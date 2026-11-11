/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.SweepInterface

/-!
# Two classical Gram–Schmidt passes as one total operation

The same coefficient scratch is reused for the two passes and released on return. Their
actual coefficient words and local error witnesses remain in the mathematical output, even
though the program discards the coefficients. This is the orthogonalization order of the
existing reorthogonalized Lanczos algorithm.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.cgs2_spec`: total two-pass execution with rounded witnesses.
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

/-- The two-pass operation reads the basis and vector, and updates the vector in place. -/
def cgs2Impl : Impl Op Tst := ⟨2, 2, 1, cgs2⟩

/-- Both classical passes are fully charged. -/
noncomputable def cgs2Count (n k : ℕ) : Count Op Tst := 2 • cgsPassCount n k

/-- Shared coefficient storage plus the single-pass workspace. -/
def cgs2Peak (W : Op → List ℕ → ℕ) (n k : ℕ) : ℕ := k + cgsPassPeak W n

/-- Static accounting includes all coefficients and projection updates of both passes. -/
theorem staticCost_cgs2 (n k q w w' : ℕ) :
    staticCost (cgs2 (Op := Op) (Tst := Tst)) [n, k, q, w, w'] = cgs2Count n k := by
  simp [cgs2, staticCost, staticCost_cgsPass, cgs2Count, two_nsmul]

/-- The second pass reuses coefficient and scalar scratch from the first pass. -/
theorem staticPeak_cgs2_le (W : Op → List ℕ → ℕ) (n k q w w' : ℕ) :
    staticPeak W (cgs2 (Op := Op) (Tst := Tst)) [n, k, q, w, w'] ≤ cgs2Peak W n k := by
  have h := staticPeak_cgsPass_le (Op := Op) (Tst := Tst) W n k q w w 0
  simpa [cgs2, staticPeak, cgs2Peak] using Nat.add_le_add_left h k

variable [Inhabited K]

/-- The intermediate vector and both sets of computed coefficients witness two rounded passes. -/
def TwoPassOut (dec : K → ℝ) (ed ea : ℝ) (n k : ℕ) (qs ws ws' : List K) : Prop :=
  ∃ mid h₁ h₂, PassOut dec ed ea n k qs ws mid h₁ ∧ PassOut dec ed ea n k qs mid ws' h₂

/-- The vector is updated in place in a buffer distinct from the read-only basis. -/
@[admNF] def TwoPassOperands (ok : ℕ → Prop) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => ok (d.headD 0) ∧ ∃ Q w, ins = [Q, w] ∧ outs = [w] ∧ Q.1 ≠ w.1

/-- The two-pass local-error contract. -/
@[simps (attr := storeNF)]
def twoPassRel (dec : K → ℝ) (ed : ℕ → ℝ) (ea : ℝ) : BlockRel K where
  nd := 2
  inLens d := [d.getD 1 0 * d.headD 0, d.headD 0]
  outLens d := [d.headD 0]
  rel d X _ Y := match X, Y with
    | [qs, ws], [ws'] => TwoPassOut dec (ed (d.headD 0)) ea (d.headD 0) (d.getD 1 0) qs ws ws'
    | _, _ => False

/-- Two passes succeed at every admitted dimension and basis rank, with actual error witnesses. -/
theorem cgs2_spec {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {ok : ℕ → Prop} {I : Interp Op Tst K} (hS : IsScalar M I)
    (hD : I.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok)))
    (hA : I.Meets .total (Has.inj Blas1Op.axpy) ((axpyRel dec ea).spec (InPlace ok)))
    (hneg : ∀ a, dec (M.neg a) = -dec a) :
    (cgs2Impl (Op := Op) (Tst := Tst)).Meets I .total
      ((twoPassRel dec ed ea).spec (TwoPassOperands ok)) := by
  cert_intro [n, k] (Q, w) → (w') reads (qs, ws)
  obtain ⟨hok, hw, hQw⟩ := hadm
  subst w'
  simp only [twoPassRel, List.headD_cons, List.getD_cons_zero, List.getD_cons_succ] at *
  have hQL := hl.1
  have hwL := hl.2.1
  refine writes_alloc rfl fun s₁ hs₁ hH hBelow => ?_
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (cgsPass_writes (qs := qs) (ws := ws) hS hD hA hneg hok hQw (by omega) (by omega)
      (by simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
      (by kept) (by kept) (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add, hH]
        exact ⟨by simpa only [(hBelow w.1 hwL).1] using hz, le_rfl⟩))) (by fp_sub)
    fun μ₁ hfr₁ ⟨hpos₁, mid, hs₁', hmid, hh₁, hfirst⟩ => ?_
  refine Writes.mono (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₁.length_eq]; omega)
    (cgsPass_writes (qs := qs) (ws := mid) hS hD hA hneg hok hQw (by omega) (by omega)
      (by simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₁.length_eq]; omega)
      (by kept) hmid (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add, hfr₁.len_eq, hH]
        exact ⟨by simpa only [(hBelow w.1 hwL).1] using hz, le_rfl⟩))) (by fp_sub) ?_
  rintro μ₂ hfr₂ ⟨hpos₂, ws', hs₂', hws', hh₂, hsecond⟩ s₂ hs₂ hBelow₂
  exact ⟨by simp [hpos₂, hpos₁], [ws'], Mem.readBlocks_of_cons (by kept) rfl,
    mid, hs₁', hs₂', hfirst, hsecond⟩

end NLAlib.Krylov.Lanczos.Reorth
