/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedRectangles
public import NLAlib.Matrix.Factorizations.LU.BlockedPrepare
public import NLAlib.Matrix.Factorizations.LU.ColumnCorrect
public import NLAlib.Matrix.Factorizations.LUBlocked
public import NLAlib.Ops.Logic.MatrixViewUpdate

/-!
# Actual deferred panel elimination

One pivot saves its complete source column and row before updating either rectangle.
The first rectangle covers the remaining panel columns and all active rows; the second
covers the panel rows and trailing columns. The bottom-right block is retained for one
later scalar matrix-product correction. Both rectangle kernels reuse the same packed scratch.

## Main results

* `NLAlib.LU.panelSchurStep_writes`: actual exact saved-pivot elimination and scratch cleanup.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Save the pivot operands once, form the scalar coefficient, and update exactly the two
panel rectangles. The trailing square is untouched and every scratch buffer is scoped. -/
def panelSchurStep : Stmt Op Tst :=
  ops% [n, k, stop] (R) → () {
    let c ← alloc n;
    let r ← alloc n;
    let a ← alloc 1;
    let P ← alloc (n * n);
    run preparePanelPivot [n, k] (R, c, r, a);
    run panelRectangles [n, k, stop] (a, c, r, R, P)
  }

omit [Has CmpTst Tst] in
/-- The scoped saved-pivot rectangle tree performs one exact panel step. Only the residual
buffer may change; every vector, coefficient and packed workspace is released on return. -/
theorem panelSchurStep_writes [Inhabited K] {M : Machine K} {I : Interp Op Tst K}
    {dec : K → ℝ} (hI : IsScalar M I) (hM : ExactModel dec M) {N : ℕ}
    (k : Fin N) (stop : ℕ) (hks : k.val < stop) (hstop : stop ≤ N)
    {τ : Tape K} {m : Mem K} {R : ℕ × ℕ} {As : List K}
    (hl : R.1 < m.store.length) (hAs : m.store.readBlock R.1 R.2 (N * N) = some As)
    (hpivot : decodeMatrix dec N N As k k ≠ 0) :
    Writes .total I τ (panelSchurStep (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val, stop] [R]) (Store.inBuf R.1)
      (fun m' => m'.pos = m.pos ∧ ∃ W : ℕ → ℕ → K,
        m'.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ W ∧
          (fun i j : Fin N => dec (W i j)) = luPanelStep (decodeMatrix dec N N As) k stop) m := by
  alloc as c r a P
  have hRc : R.1 ≠ c := by change R.1 ≠ m.store.length + 0; omega
  have hRr : R.1 ≠ r := by change R.1 ≠ m.store.length + 1; omega
  have hRa : R.1 ≠ a := by change R.1 ≠ m.store.length + 2; omega
  have hRP : R.1 ≠ P := by change R.1 ≠ m.store.length + 3; omega
  have hca : c ≠ a := by change m.store.length + 0 ≠ m.store.length + 2; omega
  have hra : r ≠ a := by change m.store.length + 1 ≠ m.store.length + 2; omega
  have hcr : c ≠ r := by change m.store.length + 0 ≠ m.store.length + 1; omega
  have hcP : c ≠ P := by change m.store.length + 0 ≠ m.store.length + 3; omega
  have hrP : r ≠ P := by change m.store.length + 1 ≠ m.store.length + 3; omega
  have haP : a ≠ P := by change m.store.length + 2 ≠ m.store.length + 3; omega
  have hAs₀ := Store.Below.readBlock_of hbelow_c hl hAs
  call (preparePanelPivot_meets hI) [N, k.val] (R, (c, 0), (r, 0), (a, 0))
    (pre := k.isLt) as m₁ hfr₁ hpos₁ (cs, rs, coeff) hprep
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change R.1 < s_c.length ∧ m.store.length < s_c.length ∧
      m.store.length + 1 < s_c.length ∧ m.store.length + 2 < s_c.length
    simp only [List.length_cons, List.length_nil] at hlen_c
    exact ⟨by omega, by omega, by omega, by omega⟩
  case' hroom =>
    change (0 + N ≤ s_c.len c) ∧ (0 + N ≤ s_c.len r) ∧ (0 + 1 ≤ s_c.len a) ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hc.ge,
      by simpa only [Nat.zero_add] using hr.ge,
      by simpa only [Nat.zero_add] using ha.ge, trivial⟩
  obtain ⟨rfl, rfl, rfl⟩ := hprep
  have hlen₁ : m₁.store.length = s_c.length := hfr₁.length_eq
  have hAs₁ : m₁.store.readBlock R.1 R.2 (N * N) = some As := by keep
  have hStore := Store.holdsMat_of_readBlock (L := ⟨R.1, R.2, N, N, N⟩) rfl hAs₁
  have hLive : m₁.Live [(a, 0), (c, 0), (r, 0), R, (P, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change m.store.length + 2 < m₁.store.length ∧ m.store.length < m₁.store.length ∧
      m.store.length + 1 < m₁.store.length ∧ R.1 < m₁.store.length ∧
      m.store.length + 3 < m₁.store.length
    simp only [List.length_cons, List.length_nil] at hlen_c
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hpRoom : 0 + N * N ≤ m₁.store.len P := by
    rw [hfr₁.len_eq]; simpa only [Nat.zero_add] using hP.ge
  have hp : dec (vec As (k.val * N + k.val)) ≠ 0 := by
    simpa only [decodeMatrix_apply] using hpivot
  have hcoef : dec (M.div (M.lit (-1)) (vec As (k.val * N + k.val))) =
      -1 / decodeMatrix dec N N As k k := by
    rw [hM.div _ _ hp, hM.lit, decodeMatrix_apply]
    norm_num
  have hpair := panelRectangles_writes (τ := τ) hI hM (decodeMatrix dec N N As) k stop
    hks.le hstop hStore (fun i j => (decodeMatrix_apply dec N N As i j).symm)
    hcoeff hcs hrs hLive hRa.symm haP hRc.symm hcP hRr.symm hrP hRP hpRoom hcoef
    (by intro i; rw [pivotColumnWords, vec_map_range _ i.isLt, decodeMatrix_apply])
    (by intro j; rw [pivotRowWords, vec_map_range _ j.isLt, decodeMatrix_apply])
  refine (hpair.in_frame rfl rfl hLive).mono (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, W, hW, hdec⟩ s₂ hs₂ hB₂
  refine ⟨hp₂.trans hpos₁, W, ?_, hdec⟩
  intro i hi j hj
  exact Store.Below.get_of hB₂ hl (hW i hi j hj)

end NLAlib.LU
