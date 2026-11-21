/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.Sweep

/-!
# Two classical Gram–Schmidt passes as one total operation

The same coefficient scratch is reused for the two passes and released on return. Their
actual coefficient words and local error witnesses remain in the mathematical output, even
though the program discards the coefficients. This is the orthogonalization order of the
existing reorthogonalized Lanczos algorithm.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.cgs2Routine_meets`: total two-pass execution with rounded witnesses.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- Two classical passes, with one shared coefficient buffer of length `k`. -/
def cgs2 : Stmt Op Tst :=
  .alloc (.var 1) (.seq
    (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨1, .var 3⟩, ⟨3, .const 0⟩] cgsPass)
    (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨1, .var 3⟩, ⟨3, .const 0⟩] cgsPass))

/-- Both classical passes are fully charged. -/
noncomputable def cgs2Count (n k : ℕ) : Count Op Tst := 2 • cgsPassCount n k

/-- Shared coefficient storage plus the single-pass workspace. -/
def cgs2Peak (W : Op → List ℕ → ℕ) (n k : ℕ) : ℕ := k + cgsPassPeak W n

/-- Static accounting includes all coefficients and projection updates of both passes. -/
theorem stmtCost_cgs2 (n k q w w' : ℕ) :
    stmtCost (cgs2 (Op := Op) (Tst := Tst)) [n, k, q, w, w'] = cgs2Count n k := by
  simp [cgs2, stmtCost, stmtCost_cgsPass, cgs2Count, two_nsmul]

/-- The second pass reuses coefficient and scalar scratch from the first pass. -/
theorem stmtPeak_cgs2_le (W : Op → List ℕ → ℕ) (n k q w w' : ℕ) :
    stmtPeak W (cgs2 (Op := Op) (Tst := Tst)) [n, k, q, w, w'] ≤ cgs2Peak W n k := by
  have h := stmtPeak_cgsPass_le (Op := Op) (Tst := Tst) W n k q w w 0
  simpa [cgs2, stmtPeak, cgs2Peak] using Nat.add_le_add_left h k

variable [Inhabited K]

/-- The intermediate vector and both sets of computed coefficients witness two rounded passes. -/
def TwoPassOut (dec : K → ℝ) (ed ea : ℝ) (n k : ℕ) (qs ws ws' : List K) : Prop :=
  ∃ mid h₁ h₂, PassOut dec ed ea n k qs ws mid h₁ ∧ PassOut dec ed ea n k qs mid ws' h₂

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- The discarded coefficients of both passes still give an actual representation witness.
The bound adds the two independently certified axpy chains, without assuming orthogonality. -/
theorem TwoPassOut.exists_abs_sub_le {dec : K → ℝ} {ed ea : ℝ} {n k : ℕ}
    {qs ws ws' : List K} (h : TwoPassOut dec ed ea n k qs ws ws') (ha : 0 ≤ ea) :
    ∃ mid h₁ h₂ : List K, PassOut dec ed ea n k qs ws mid h₁ ∧
      PassOut dec ed ea n k qs mid ws' h₂ ∧ ∀ i : Fin n,
      |dec (vec ws' i) - (dec (vec ws i) - ∑ j ∈ Finset.range k,
          (dec (vec h₁ j) + dec (vec h₂ j)) * dec (vec qs (j * n + i)))| ≤
        ((1 + ea) ^ k - 1) * (|dec (vec ws i)| +
          ∑ j ∈ Finset.range k, |dec (vec h₁ j) * dec (vec qs (j * n + i))|) +
        ((1 + ea) ^ k - 1) * (|dec (vec mid i)| +
          ∑ j ∈ Finset.range k, |dec (vec h₂ j) * dec (vec qs (j * n + i))|) := by
  obtain ⟨mid, h₁, h₂, hp₁, hp₂⟩ := h
  refine ⟨mid, h₁, h₂, hp₁, hp₂, fun i => ?_⟩
  have hid : dec (vec ws' i) - (dec (vec ws i) - ∑ j ∈ Finset.range k,
      (dec (vec h₁ j) + dec (vec h₂ j)) * dec (vec qs (j * n + i))) =
      (dec (vec mid i) - (dec (vec ws i) - ∑ j ∈ Finset.range k,
        dec (vec h₁ j) * dec (vec qs (j * n + i)))) +
      (dec (vec ws' i) - (dec (vec mid i) - ∑ j ∈ Finset.range k,
        dec (vec h₂ j) * dec (vec qs (j * n + i)))) := by
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add (hp₁.abs_sub_le ha i) (hp₂.abs_sub_le ha i))

/-- The two-pass operation as a routine: the basis `Q` is read and the vector `w` updated in
place. -/
def cgs2Routine : Routine Op Tst :=
  routine% [n, k] (Q : k * n, w : n) → (w) := cgs2

/-- The two-pass local-error specification, at admitted dimensions. -/
def cgs2Spec (dec : K → ℝ) (ed : ℕ → ℝ) (ea : ℝ) (ok : ℕ → Prop) : Routine.Spec K :=
  spec% [n, k] (qs, ws) → (ws') requires ok n ensures TwoPassOut dec (ed n) ea n k qs ws ws'

/-- Two passes succeed at every admitted dimension and basis rank, with actual error witnesses.
Each pass is a call of the classical pass on the shared coefficient scratch. -/
theorem cgs2Routine_meets {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {ok : ℕ → Prop} {I : Interp Op Tst K} (hS : IsScalar M I)
    (hD : I.Satisfies .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok)))
    (hA : I.Satisfies .total (Has.inj Blas1Op.axpy) ((axpyRel dec ea).spec (InPlace ok)))
    (hneg : ∀ a, dec (M.neg a) = -dec a) :
    (cgs2Routine (Op := Op) (Tst := Tst)).Meets I (cgs2Spec dec ed ea ok) := by
  routine_intro [n, k] (Q, w) reads (qs, ws)
  have hok : ok n := hpre
  have hpass := cgsPassRoutine_meets (Op := Op) (Tst := Tst) hS hD hA hneg (ok := ok)
  have hQL : Q.1 ≠ m.store.length := by omega
  have hwL : w.1 ≠ m.store.length := by omega
  refine writes_alloc rfl fun s₁ hs₁ hH hBelow => ?_
  call hpass [n, k] (Q, w, (m.store.length, 0)) (pre := hok) as μ₁ hfr₁ hpos₁ (mid, cs₁) hfirst
  call hpass [n, k] (Q, w, (m.store.length, 0)) (pre := hok) as μ₂ hfr₂ hpos₂ (ws', cs₂) hsecond
  intro s₂ hs₂ hBelow₂
  exact ⟨by simp [hpos₂, hpos₁], [ws'], Mem.readBlocks_of_cons (by kept) rfl,
    show TwoPassOut dec (ed n) ea n k qs ws ws' from ⟨mid, cs₁, cs₂, hfirst, hsecond⟩⟩

/-- Readable inputs and output room suffice for total execution and the declared budget: the
counted form of `cgs2Routine_meets`. -/
theorem runs_cgs2 {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {ok : ℕ → Prop} {I : Interp Op Tst K} (hS : IsScalar M I)
    (hD : I.Satisfies .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok)))
    (hA : I.Satisfies .total (Has.inj Blas1Op.axpy) ((axpyRel dec ea).spec (InPlace ok)))
    (hneg : ∀ a, dec (M.neg a) = -dec a)
    (W : Op → List ℕ → ℕ) {n k : ℕ} {τ : Tape K} {μ : Mem K}
    {Q w : ℕ × ℕ} {qs ws : List K} (hok : ok n) (hQw : Q.1 ≠ w.1)
    (hl : μ.Live [Q, w]) (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hws : μ.store.readBlock w.1 w.2 n = some ws) (hz : μ.Room [w] [n]) :
    ConditionalRuns I W τ cgs2 (Env.frame [n, k] [Q, w, w]) μ (cgs2Count n k) (cgs2Peak W n k)
      (fun μ' => ∃ ws', ws'.length = n ∧ TwoPassOut dec (ed n) ea n k qs ws ws' ∧
        μ' = μ.updBlocks [w] [ws']) := by
  have hread : μ.readBlocks [Q, w] [k * n, n] = some [qs, ws] :=
    Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hws rfl)
  obtain ⟨μ', hrun, hfr, hpos, Y, hout, hrel⟩ :=
    (cgs2Routine_meets hS hD hA hneg [n, k] [Q, w] τ μ _ rfl rfl hl (by routine_sep) hread hok
      hz).wp (Q := fun m' => μ.store.EqOff (Fp.blocks [w] [n]) m'.store ∧ m'.pos = μ.pos ∧
        ∃ Y, m'.readBlocks [w] [n] = some Y ∧
          (cgs2Spec dec ed ea ok).post [n, k] (τ.shift μ.pos) [qs, ws] Y)
      fun _ hfr h => ⟨hfr, h⟩
  split_reads hout as (ws')
  refine (ConditionalRuns.of_run hrun ⟨ws', Store.length_of_readBlock hws', hrel, ?_⟩ W).mono
    (le_of_eq (stmtCost_cgs2 ..)) (stmtPeak_cgs2_le ..) (fun _ h => h)
  exact Mem.eq_updBlocks_of_eqOff (m := μ) hfr (Mem.readBlocks_of_cons hws' rfl) hpos

end NLAlib.Krylov.Lanczos.Reorth
