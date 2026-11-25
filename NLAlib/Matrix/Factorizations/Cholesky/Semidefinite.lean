/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.SemidefiniteSteps
public import NLAlib.Matrix.Factorizations.Cholesky.Initialize
public import NLAlib.Ops.Logic.Allocation

/-!
# Zero-safe right-looking Cholesky on positive semidefinite matrices

The source is copied into scoped residual storage and the output is initialized once.
Each zero pivot writes a zero factor suffix without division; each positive pivot uses the
ordinary right-looking scalar column and saved-pivot update. The specification includes
singular and empty matrices and does not use the strict-positive-diagonal `IsCholesky` predicate.

## Main results

* `NLAlib.Cholesky.semidefiniteRightLooking_meets`: the actual canonical semidefinite factor,
  its nonnegative diagonal, exact Gram identity and literal upper zeros.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Copy, initialize and run the zero-safe column loop on caller-owned scratch. -/
def semidefiniteRightWithScratch : Stmt Op Tst := ops% [n] (A, L, R) → () {
  run initializeLower [n] (A, R, L);
  run rightLoopTotal [n] (R, L)
}

/-- Full zero-safe scalar Cholesky with scoped residual scratch. A zero pivot is guarded
before every possible division, and an empty matrix executes no pivot step. -/
def semidefiniteRightLooking : Routine Op Tst := routine% [n] (A : n * n) → (L : n * n) {
  ifPos n {
    let R ← alloc (n * n);
    run semidefiniteRightWithScratch [n] (A, L, R)
  }
}

/-- At order zero the raw scalar body reads no operands and leaves the complete memory
unchanged, for arbitrary handles, offsets, aliases and even an empty caller store. -/
theorem eval_semidefiniteRightLooking_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (semidefiniteRightLooking (Op := Op) (Tst := Tst)).body
      (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The actual decoded factor is canonical, lower triangular with nonnegative diagonal,
and has the exact Gram identity. Its stored upper words are the initialization zero literal.
The positive semidefinite input domain includes singular and order-zero matrices. -/
def semidefiniteRightLookingSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls) requires (decodeMatrix dec n n as).PosSemidef ensures
    decodeMatrix dec n n ls = choleskyLower (decodeMatrix dec n n as) ∧
      (decodeMatrix dec n n ls).IsLowerTriangular ∧
      (∀ i : Fin n, 0 ≤ decodeMatrix dec n n ls i i) ∧
      decodeMatrix dec n n as = decodeMatrix dec n n ls * (decodeMatrix dec n n ls)ᴴ ∧
      (∀ i j : Fin n, i < j → vec ls (j.val * n + i.val) = M.lit 0)

/-- The numerical postcondition at order zero holds for the actual empty output words.
No matrix entries or strict diagonal values exist at this order. -/
theorem semidefiniteRightLookingSpec_empty (M : Machine K) (dec : K → ℝ) (as : List K)
    (τ : Tape K) :
    (semidefiniteRightLookingSpec M dec).post [0] τ [as] [[]] := by
  refine ⟨?_, ?_, fun i => Fin.elim0 i, ?_, fun i => Fin.elim0 i⟩
  · ext i j
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · ext i j
    exact Fin.elim0 i

/-- The common initializer and actual guarded loop compute the full canonical factor.
Only scratch is required apart; source and output may overlap because copying comes first. -/
theorem semidefiniteRightWithScratch_writes {M : Machine K} {I : Interp Op Tst K}
    {dec : K → ℝ} (hI : IsScalar M I) (hM : ExactModel dec M) (hcmp : IsCmp dec I) {N : ℕ}
    {τ : Tape K} {m : Mem K} {A L R : ℕ × ℕ} {as : List K}
    (hl : m.Live [A, L, R]) (hRA : R.1 ≠ A.1) (hRL : R.1 ≠ L.1)
    (has : m.store.readBlock A.1 A.2 (N * N) = some as)
    (hA : (decodeMatrix dec N N as).PosSemidef)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) :
    Writes .total I τ (semidefiniteRightWithScratch (Op := Op) (Tst := Tst))
      (Env.frame [N] [A, L, R])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ ∃ ls : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some ls ∧
        decodeMatrix dec N N ls = choleskyLower (decodeMatrix dec N N as) ∧
        (∀ i j : Fin N, i < j → vec ls (j.val * N + i.val) = M.lit 0)) m := by
  have hlARL : m.Live [A, R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl A (by simp), hl R (by simp), hl L (by simp), trivial⟩
  unfold semidefiniteRightWithScratch
  refine ((initializeLower_writes_of_scratch_apart hI hlARL hRA hRL has hRroom hLroom).in_frame
    rfl rfl hlARL).seq_le le_rfl ?_
  intro m₁ hfr₁ ⟨hpos₁, hR₁, hL₁⟩
  have hpref := IsRightPrefix.initial hM hR₁ hL₁
  have hlRL : m.Live [R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl R (by simp), hl L (by simp), trivial⟩
  have hlRL₁ := hlRL.congr hfr₁.length_eq
  refine ((rightLoopTotal_writes hI hM hcmp hA hlRL₁ hRL
    (by simpa only [hfr₁.len_eq] using hRroom)
    (by simpa only [hfr₁.len_eq] using hLroom) hpref).in_frame
      rfl rfl hlRL₁).mono le_rfl ?_
  intro m₂ hfr₂ ⟨hpos₂, hfinal⟩
  obtain ⟨ls, hls, hnum, hupper⟩ := hfinal.read_factor
  exact ⟨by omega, ls, hls, hnum, hupper⟩

/-- The scoped scalar body at arbitrary source/output operands. The copy occurs before
output initialization, so this common body also admits coincident operands. Only the factor
block can change; scoped residual storage and the tape position are restored. -/
theorem semidefiniteRightLooking_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) (hcmp : IsCmp dec I) {n : ℕ}
    {τ : Tape K} {m : Mem K} {A L : ℕ × ℕ} {as : List K}
    (hlive : m.Live [A, L])
    (has : m.store.readBlock A.1 A.2 (n * n) = some as)
    (hpre : (decodeMatrix dec n n as).PosSemidef)
    (hroom : L.2 + n * n ≤ m.store.len L.1) :
    Writes .total I τ (semidefiniteRightLooking (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [A, L]) (Store.inBlock L.1 L.2 (n * n))
      (fun m' => m'.pos = m.pos ∧ ∃ ls : List K,
        m'.store.readBlock L.1 L.2 (n * n) = some ls ∧
        decodeMatrix dec n n ls = choleskyLower (decodeMatrix dec n n as) ∧
        (∀ i j : Fin n, i < j → vec ls (j.val * n + i.val) = M.lit 0)) m := by
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have hlA : A.1 < m.store.length := hlive A (by simp)
    have hlL : L.1 < m.store.length := hlive L (by simp)
    apply writes_allocs_preserving_post (lens := [.var 0 * .var 0]) (ns := [n * n]) rfl
    · intro s s' p hBelow hp
      obtain ⟨hpos, ls, hls, hnum, hupper⟩ := hp
      exact ⟨hpos, ls, (hBelow.readBlock hlL L.2 (n * n)).trans hls, hnum, hupper⟩
    · intro store hlength hlens hBelow
      have hRlen : store.len m.store.length = n * n := by simpa using hlens 0 (by simp)
      have hRlive : m.store.length < store.length := by
        simp only [List.length_singleton] at hlength
        omega
      have hLive : (Mem.mk store m.pos).Live [A, L, (m.store.length, 0)] := by
        simp only [Mem.live_cons, Mem.live_nil]
        exact ⟨by omega, by omega, hRlive, trivial⟩
      refine ((semidefiniteRightWithScratch_writes hI hM hcmp hLive (by omega) (by omega)
        (by kept) hpre (by simpa using hRlen.ge)
        (by simpa only [(hBelow L.1 hlL).1] using hroom)).in_frame
          rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    obtain ⟨hnum, -, -, -, hupper⟩ := semidefiniteRightLookingSpec_empty M dec as (τ.shift m.pos)
    exact ⟨rfl, [], rfl, hnum, hupper⟩

/-- The full scalar zero-safe routine meets its exact semidefinite specification, including
singular and empty inputs, scoped scratch and the off-output frame. No pivot-nonzero or
successful-run assumption is needed. -/
theorem semidefiniteRightLooking_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) (hcmp : IsCmp dec I) :
    (semidefiniteRightLooking (Op := Op) (Tst := Tst)).Meets I
      (semidefiniteRightLookingSpec M dec) := by
  routine_intro [n] (A, L) reads (as)
  refine (semidefiniteRightLooking_writes hI hM hcmp hlive has hpre hroom).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, ls, hls, hnum, hupper⟩
  refine ⟨by omega, [ls], Mem.readBlocks_of_cons hls rfl, hnum, ?_, ?_, ?_, hupper⟩
  · rw [hnum]
    exact isLowerTriangular_choleskyLower _
  · intro i
    rw [hnum]
    exact hpre.isHermitian.choleskyLower_apply_self_nonneg i
  · rw [hnum]
    exact hpre.eq_choleskyLower_mul_conjTranspose

end NLAlib.Cholesky
