/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.PivotPrefix
public import NLAlib.Matrix.Factorizations.Cholesky.SemidefiniteSteps
public import NLAlib.Ops.Logic.IndexLog

/-!
# Committing a stored symmetric Cholesky pivot

The scalar exchange, actual dimension-literal log write and zero-safe column step advance
the stored factor prefix. The full driver supplies the selected row through its executed
scan and bounded query. The invariant retains earlier log words and actual future zero words.

## Main results

* `NLAlib.Cholesky.pivotedAdvance_writes`: commit one actual selected symmetric pivot.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Apply and record an already read current-position pivot, then materialize the zero-safe
factor column. The complete driver supplies this index through its actual bounded query. -/
def pivotedAdvance : Stmt Op Tst := ops% [n, k, row] (R, L, H) → () {
  run symmetricPivot [n, k, row] (R, L);
  call (Has.inj IndexOp.lit) [row] () → (H[k]);
  run rightStepTotal [n, k] (R, L)
}

variable [Inhabited K]

/-- The actual exchange, literal write and column instructions advance the stored prefix.
The input's semidefiniteness proves positivity of every nonzero residual pivot. -/
theorem pivotedAdvance_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hlit : IsIndexLit M I) (hcmp : IsCmp dec I)
    (hM : ExactModel dec M) {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef)
    {p : Fin N → Fin N} (k r : Fin N)
    (hchoice : HasDiagonalPivotPrefix A (Function.update p k r) (k.val + 1))
    {τ : Tape K} {m : Mem K} {R L H : ℕ × ℕ} (hlive : m.Live [R, L, H])
    (hRL : R.1 ≠ L.1) (hRH : R.1 ≠ H.1) (hLH : L.1 ≠ H.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hHroom : H.2 + N ≤ m.store.len H.1)
    (hstate : IsDiagonalPrefix dec (M.lit 0) A p k.val R L H m.store) :
    Writes .total I τ (pivotedAdvance (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val, r.val] [R, L, H])
      ((Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N)) ⊔
        Store.inBlock H.1 H.2 N)
      (fun m' => m'.pos = m.pos ∧ IsDiagonalPrefix dec (M.lit 0) A
        (Function.update p k r) (k.val + 1) R L H m'.store) m := by
  have hlR : R.1 < m.store.length := hlive R (by simp)
  have hlL : L.1 < m.store.length := hlive L (by simp)
  have hlH : H.1 < m.store.length := hlive H (by simp)
  have hkr : k ≤ r := by
    simpa only [Function.update_self] using (hchoice k (by omega)).1
  obtain ⟨hpre, hfuture, hlog, -⟩ := hstate
  obtain ⟨rs, ls, hrs, hls, hres, hfac, hupper⟩ := hpre.read_blocks
  let B := A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
    (luPivotPermutation (Function.update p k r) (k.val + 1))
  have heB : (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val)).submatrix
      (Equiv.swap k r) (Equiv.swap k r) = B := by
    dsimp only [B]
    rw [luPivotPermutation_update]
    rfl
  unfold pivotedAdvance
  call (symmetricPivot_meets hI) [N, k.val, r.val] (R, L) (pre := ⟨hkr, r.isLt⟩)
    as m₁ hfr₁ hpos₁ (rs', ls') hswap
  obtain ⟨hpre₁, hfuture₁⟩ := IsRightPrefix.symmetricPivot k r hkr hls hrs' hls'
    hres hfac hupper hfuture hswap
  rw [heB] at hpre₁
  have hlog₁ := hfr₁.keep (Store.readsOnly_indexPrefix dec p k.val H) (by
    simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq, Fp.disj_sup_left] using
      And.intro (Fp.disj_inBlock_of_ne hRH) (Fp.disj_inBlock_of_ne hLH)) hlog
  refine (writes_indexLit hlit (n := r.val) rfl rfl (by
    change H.2 + k.val < m₁.store.len H.1
    rw [hfr₁.len_eq]
    have := k.isLt
    omega)).seq_le
    (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hpos₂, hget⟩
  have hpre₂ := hfr₂.keep (IsRightPrefix.readsOnly dec (M.lit 0) B k.val R L)
    (Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne hRH.symm,
      Fp.disj_inBlock_of_ne hLH.symm⟩) hpre₁
  have hfuture₂ := hfr₂.keep (HasFutureZeroColumns.readsOnly (M.lit 0) N k.val L)
    (Fp.disj_inBlock_of_ne hLH.symm) hfuture₁
  have hlog₂ := Store.indexPrefix_update k r hlog₁ hfr₂ hget
    (show dec (M.lit (r.val : ℚ)) = (r.val : ℝ) from by simpa using hM.lit (r.val : ℚ))
  have hlRL : m₂.Live [R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by rw [hfr₂.length_eq, hfr₁.length_eq]; exact hlR,
      by rw [hfr₂.length_eq, hfr₁.length_eq]; exact hlL, trivial⟩
  have hbound : L.2 + k.val * N + k.val + (N - k.val) ≤ L.2 + N * N := by
    have hb := Nat.mul_le_mul_right N (Nat.succ_le_of_lt k.isLt)
    rw [Nat.succ_mul] at hb
    omega
  refine ((rightStepTotal_writes_suffix hI hM hcmp (hA.submatrix _) k hlRL hRL
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hRroom)
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hLroom) hpre₂).in_frame
      rfl rfl hlRL).mono
        ((sup_le_sup le_rfl (Fp.inBlock_le_inBlock (by omega) hbound)).trans le_sup_left) ?_
  intro m₃ hfr₃ ⟨hpos₃, hpre₃⟩
  refine ⟨hpos₃.trans (hpos₂.trans hpos₁), hpre₃, hfuture₂.step k hRL hfr₃, ?_, hchoice⟩
  exact hfr₃.keep (Store.readsOnly_indexPrefix dec (Function.update p k r) (k.val + 1) H)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hRH, Fp.disj_inBlock_of_ne hLH⟩) hlog₂

end NLAlib.Cholesky
