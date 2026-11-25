/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightSteps
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Catalog.Compare

/-!
# Zero-safe stored steps of semidefinite Cholesky

A zero residual pivot writes a literal-zero lower column suffix and leaves the residual
unchanged, executing no division. Otherwise the existing right-looking step is used. Positive
semidefiniteness supplies the exact positivity of every nonzero residual pivot.

## Main results

* `NLAlib.Cholesky.rightStepTotal_writes`: an actual guarded step advances the stored prefix.
* `NLAlib.Cholesky.rightLoopTotal_writes`: the entire zero-safe loop completes the factor.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- The guarded column step of `semidefiniteRightLooking`. A zero pivot fills the factor
suffix with zero literals and skips the Schur update; no zero-pivot division is executed. -/
def rightStepTotal : Stmt Op Tst := ops% [n, k] (R, L) → () {
  if (Has.inj CmpTst.isZero) [] (R[k * n + k]) {
    run (fillRoutine (Has.inj (ScalarOp.lit 0))) [n - k] (L[k * n + k])
  } else {
    run rightStep [n, k] (R, L)
  }
}

/-- The full guarded column loop of `semidefiniteRightLooking`. -/
def rightLoopTotal : Stmt Op Tst := ops% [n] (R, L) → () {
  for k < n {
    run rightStepTotal [n, k] (R, L)
  }
}

variable [Inhabited K]

/-- An actual zero-safe step advances the canonical stored prefix on every positive
semidefinite input, including a zero pivot. Exact comparisons choose the executed branch. -/
theorem rightStepTotal_writes_suffix {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) (hcmp : IsCmp dec I) {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef) (k : Fin N)
    {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsRightPrefix dec (M.lit 0) A k.val R L m.store) :
    Writes .total I τ (rightStepTotal (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 (L.2 + k.val * N + k.val) (N - k.val))
      (fun m' => m'.pos = m.pos ∧
        IsRightPrefix dec (M.lit 0) A (k.val + 1) R L m'.store) m := by
  have hlR : R.1 < m.store.length := hl R (by simp)
  have hlL : L.1 < m.store.length := hl L (by simp)
  obtain ⟨rw, lw, hR, hL, hres, hfac, hupper⟩ := hpref
  have hdiag := hR k.val k.isLt k.val k.isLt
  have hend : k.val * N + k.val + (N - k.val) ≤ N * N := by
    have hm := Nat.mul_le_mul_right N (Nat.succ_le_of_lt k.isLt)
    rw [Nat.succ_mul] at hm
    omega
  unfold rightStepTotal
  refine writes_ite rfl rfl (hcmp.test_isZero hdiag) ?_
  by_cases hz : dec (rw k k) = 0
  · simp only [hz, decide_true, ite_true]
    call (fillRoutine_meets (hI (.lit 0))) [N - k.val]
      ((L.1, L.2 + k.val * N + k.val)) as m₁ hfr₁ hpos₁ (ys) hfill
    have hfrL : m.store.EqOff
        (Store.inBlock L.1 (L.2 + k.val * N + k.val) (N - k.val)) m₁.store := by
      simpa [Fp.blocks_cons, Fp.blocks_nil] using hfr₁
    have hL₁ := hL.update_column_suffix_of_frame (by exact le_rfl) k.val k.val k.isLt.le hfrL hys
    have hR₁ : m₁.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw := by keep
    have hpivot : gaussState A k.val k k = 0 := by simpa only [hres k k] using hz
    have hnext : gaussState A (k.val + 1) = gaussState A k.val := by
      rw [gaussState_succ A k.isLt, eliminationStep_eq_self_of_apply_self_eq_zero hpivot]
    refine ⟨by omega, IsRightPrefix.succ k rw lw ys hR₁ hL₁ ?_ hfac hupper ?_⟩
    · intro i j
      rw [hnext]
      exact hres i j
    · intro i hki
      have hi : i.val - k.val < N - k.val := by omega
      have hzero : dec (M.lit 0) = 0 := by simpa using hM.lit 0
      have hfill_eq : ys = List.replicate (N - k.val) (M.lit 0) := hfill
      rw [hfill_eq]
      simp only [vec, List.getD_replicate (α := K) (x := M.lit 0) (h := hi), hzero,
        choleskyLower, Matrix.of_apply,
        if_pos hki, hpivot, RCLike.re_to_real, RCLike.ofReal_real_eq_id, id_eq,
        Real.sqrt_zero, div_zero]
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
    have hpivot : 0 < gaussState A k.val k k := by
      have hn := (hA.gaussState k.val).diag_nonneg (i := k)
      have hne : gaussState A k.val k k ≠ 0 := by simpa only [hres k k] using hz
      exact lt_of_le_of_ne hn (Ne.symm hne)
    exact (rightStep_writes_suffix hI hM hA.isHermitian k hpivot hl hRL hRroom hLroom
      ⟨rw, lw, hR, hL, hres, hfac, hupper⟩).in_frame rfl rfl hl

/-- The complete matrix-block frame follows from the actual current-column suffix frame.
The numerical postcondition is unchanged, allowing full-loop consumers to use ordinary blocks. -/
theorem rightStepTotal_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) (hcmp : IsCmp dec I) {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef) (k : Fin N)
    {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsRightPrefix dec (M.lit 0) A k.val R L m.store) :
    Writes .total I τ (rightStepTotal (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧
        IsRightPrefix dec (M.lit 0) A (k.val + 1) R L m'.store) m := by
  refine (rightStepTotal_writes_suffix hI hM hcmp hA k hl hRL hRroom hLroom hpref).mono
    (sup_le_sup le_rfl (Fp.inBlock_le_inBlock (by omega) ?_)) (fun _ _ h => h)
  have hm := Nat.mul_le_mul_right N (Nat.succ_le_of_lt k.isLt)
  rw [Nat.succ_mul] at hm
  omega

/-- The actual guarded column loop completes the canonical semidefinite factor, retaining
literal upper zeros and requiring no nonzero-pivot premise. -/
theorem rightLoopTotal_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) (hcmp : IsCmp dec I) {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef)
    {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsRightPrefix dec (M.lit 0) A 0 R L m.store) :
    Writes .total I τ (rightLoopTotal (Op := Op) (Tst := Tst)) (Env.frame [N] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ IsRightPrefix dec (M.lit 0) A N R L m'.store) m := by
  unfold rightLoopTotal
  refine (writes_loop rfl
    (fun _ => Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
    (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ IsRightPrefix dec (M.lit 0) A k R L m'.store)
    ⟨rfl, hpref⟩ ?_).mono le_rfl (fun _ _ h => h)
  intro k hk m' hfr ⟨hpos, hpref'⟩
  have hl' := hl.congr hfr.length_eq
  refine ((rightStepTotal_writes hI hM hcmp hA ⟨k, hk⟩ hl' hRL
    (by simpa only [hfr.len_eq] using hRroom)
    (by simpa only [hfr.len_eq] using hLroom) hpref').in_frame rfl rfl hl').mono le_rfl ?_
  intro m'' hfr' ⟨hpos', hpref''⟩
  exact ⟨hpos'.trans hpos, hpref''⟩

end NLAlib.Cholesky
