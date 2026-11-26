/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightColumnValues
public import NLAlib.Matrix.Factorizations.LU.Schur
public import NLAlib.Ops.Logic.ColumnSuffix

/-!
# One stored right-looking Cholesky step

The step commits the current lower column suffix and then updates the copied Gaussian
residual. The stored prefix advances from these two actual routine calls. The upper factor
words remain the initialization literal; no residual-row cancellation is used for their shape.

## Main results

* `NLAlib.Cholesky.rightStep_writes`: actual column normalization and elimination advance
  the canonical stored prefix on positive definite input.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- The column-normalization and saved-pivot update fragment of `rightLooking`.
Both buffers are already initialized; only the lower suffix of the factor is written. -/
def rightStep : Stmt Op Tst := ops% [n, k] (R, L) → () {
  run rightColumn [n - k - 1] (R[k * n + k], R[k * n + k + 1], L[k * n + k]);
  run LU.schurStep [n, k] (R)
}

/-- The column loop of `rightLooking`, on its copied residual and initialized factor. -/
def rightLoop : Stmt Op Tst := ops% [n] (R, L) → () {
  for k < n {
    run rightStep [n, k] (R, L)
  }
}

variable [Inhabited K]

/-- On Hermitian input with a positive current pivot, actual normalization and the full Schur
update advance the
stored canonical factor prefix at a positive current pivot. The conclusion retains actual
initialized word blocks and
literal upper zeros, and its frame covers only the residual and factor operands. -/
theorem rightStep_writes_suffix {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (k : Fin N)
    (hpivot : 0 < gaussState A k.val k k) {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsRightPrefix dec (M.lit 0) A k.val R L m.store) :
    Writes .total I τ (rightStep (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 (L.2 + k.val * N + k.val) (N - k.val))
      (fun m' => m'.pos = m.pos ∧
        IsRightPrefix dec (M.lit 0) A (k.val + 1) R L m'.store) m := by
  have hlR : R.1 < m.store.length := hl R (by simp)
  have hlL : L.1 < m.store.length := hl L (by simp)
  obtain ⟨rw, lw, hR, hL, hres, hfac, hupper⟩ := hpref
  have hdiag := Store.readBlock_one_of_get (hR k.val k.isLt k.val k.isLt)
  have htail : m.store.readBlock R.1 (R.2 + k.val * N + k.val + 1) (N - k.val - 1) =
      some ((List.range (N - k.val - 1)).map fun i => rw (k.val + 1 + i) k.val) := by
    simpa only [Nat.sub_sub, Nat.add_assoc] using
      hR.readBlock_column_suffix k.val k.isLt (k.val + 1) (Nat.succ_le_of_lt k.isLt)
  have hs : N - k.val - 1 + 1 = N - k.val := by omega
  have hend : k.val * N + k.val + (N - k.val - 1 + 1) ≤ N * N := by
    have hmul := Nat.mul_le_mul_right N (Nat.succ_le_of_lt k.isLt)
    rw [Nat.succ_mul] at hmul
    omega
  unfold rightStep
  call (rightColumn_meets hI) [N - k.val - 1]
    ((R.1, R.2 + k.val * N + k.val), (R.1, R.2 + k.val * N + k.val + 1),
      (L.1, L.2 + k.val * N + k.val))
    as m₁ hfr₁ hpos₁ (ys) hcol
  have hfrL : m.store.EqOff
      (Store.inBlock L.1 (L.2 + k.val * N + k.val) (N - k.val)) m₁.store := by
    simpa [hs, Fp.blocks_cons, Fp.blocks_nil] using hfr₁
  have hys : m₁.store.readBlock L.1 (L.2 + k.val * N + k.val) (N - k.val) = some ys := by
    simpa only [hs] using hys
  let lw' : ℕ → ℕ → K := fun i j =>
    if j = k.val ∧ k.val ≤ i then vec ys (i - k.val) else lw i j
  have hL₁ : m₁.store.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw' :=
    hL.update_column_suffix_of_frame (by exact le_rfl) k.val k.val k.isLt.le hfrL hys
  have hR₁ : m₁.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw := by keep
  have hycol : ∀ i : Fin N, k ≤ i → dec (vec ys (i.val - k.val)) = choleskyLower A i k :=
    rightColumnSpec_decode_choleskyLower hM hA k hpivot rw hres
      (by intro i hi; simp [vec, List.getD_eq_getElem?_getD, hi]) hcol
  obtain ⟨rs, hrs, -, hdata⟩ := hR₁.readBlock rfl
  have hdecodeR : decodeMatrix dec N N rs = gaussState A k.val := by
    ext i j
    rw [decodeMatrix_apply, hdata i i.isLt j j.isLt, hres i j]
  call (LU.schurStep_meets hI) [N, k.val] (R) (pre := k.isLt)
    as m₂ hfr₂ hpos₂ (bs) hschur
  have hL₂ : m₂.store.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw' := by keep
  have hb := LU.schurStepSpec_decode hM k hschur
    (by rw [hdecodeR]; exact hpivot.ne')
  rw [hdecodeR, ← gaussState_succ A k.isLt] at hb
  refine ⟨by omega, IsRightPrefix.succ k (fun i j => vec bs (j * N + i)) lw ys
    (Store.holdsMat_of_readBlock rfl hbs) hL₂ ?_ hfac hupper hycol⟩
  intro i j
  simpa only [decodeMatrix_apply] using congrFun (congrFun hb i) j

/-- The complete matrix-block frame follows from the actual current-column suffix frame.
The numerical postcondition is unchanged, allowing full-loop consumers to use ordinary blocks. -/
theorem rightStep_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (k : Fin N)
    (hpivot : 0 < gaussState A k.val k k) {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsRightPrefix dec (M.lit 0) A k.val R L m.store) :
    Writes .total I τ (rightStep (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧
        IsRightPrefix dec (M.lit 0) A (k.val + 1) R L m'.store) m := by
  refine (rightStep_writes_suffix hI hM hA k hpivot hl hRL hRroom hLroom hpref).mono
    (sup_le_sup le_rfl (Fp.inBlock_le_inBlock (by omega) ?_)) (fun _ _ h => h)
  have hm := Nat.mul_le_mul_right N (Nat.succ_le_of_lt k.isLt)
  rw [Nat.succ_mul] at hm
  omega

/-- The actual stored column loop completes the canonical factor prefix. Its arithmetic
nonbreakdown follows from the positive definite input, rather than a run premise. -/
theorem rightLoop_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsRightPrefix dec (M.lit 0) A 0 R L m.store) :
    Writes .total I τ (rightLoop (Op := Op) (Tst := Tst)) (Env.frame [N] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ IsRightPrefix dec (M.lit 0) A N R L m'.store) m := by
  unfold rightLoop
  refine (writes_loop rfl
    (fun _ => Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
    (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ IsRightPrefix dec (M.lit 0) A k R L m'.store)
    ⟨rfl, hpref⟩ ?_).mono le_rfl (fun _ _ h => h)
  intro k hk m' hfr ⟨hpos, hpref'⟩
  have hl' := hl.congr hfr.length_eq
  refine ((rightStep_writes hI hM hA.isHermitian ⟨k, hk⟩
    (hA.gaussState_apply_self_pos ⟨k, hk⟩) hl' hRL
    (by simpa only [hfr.len_eq] using hRroom)
    (by simpa only [hfr.len_eq] using hLroom) hpref').in_frame rfl rfl hl').mono le_rfl ?_
  intro m'' hfr' ⟨hpos', hpref''⟩
  exact ⟨hpos'.trans hpos, hpref''⟩

end NLAlib.Cholesky
