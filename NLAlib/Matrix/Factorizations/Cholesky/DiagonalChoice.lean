/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PartialPivot
public import NLAlib.Ops.Blas.DiagonalCopy
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Actual first-maximum diagonal selection

The active diagonal is gathered by the scalar strided-copy loop. The ordinary absolute
maximum scan writes a relative index; the actual bounded conversion reads that word, and a
dimension-literal instruction records the absolute selected index. Positive semidefinite
residuals have nonnegative diagonals, so this absolute comparison selects a maximal diagonal.

## Main results

* `NLAlib.Cholesky.diagonalChoice_meets`: actual selection and exact absolute index output.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Gather and scan the active diagonal, read the actual relative index, then store the
absolute selected position as a dimension literal. -/
def diagonalChoice : Routine Op Tst := routine% [n, k] (R : n * n) → (p : 1) {
  let diagonal ← alloc (n - k);
  let relative ← alloc 1;
  run copyDiagonal [n, k, n - k] (R, diagonal);
  run LU.argmaxAbs [n - k] (diagonal, relative);
  let row ← index (Has.inj IdxTst.toNat) (relative) ≤ n - k - 1;
  call (Has.inj IndexOp.lit) [k + row] () → (p)
}

variable [Inhabited K]

/-- The actual output identifies the first largest-magnitude diagonal in the active suffix.
The explicit dimension bound is the allowance for exact stored natural literals. -/
def diagonalChoiceSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] (rs) → ([w]) requires k < n ∧ n ≤ bound ensures
    ∃ r : Fin n, k ≤ r.val ∧ dec w = r.val ∧
      (∀ i : Fin n, k ≤ i.val →
        |dec (vec rs (i.val * n + i.val))| ≤ |dec (vec rs (r.val * n + r.val))|) ∧
      (∀ i : Fin n, k ≤ i.val → i < r →
        |dec (vec rs (i.val * n + i.val))| < |dec (vec rs (r.val * n + r.val))|)

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] [Has IdxTst Tst] in
private theorem diagonalChoice_post {M : Machine K} {dec : K → ℝ} {N k bound : ℕ}
    {rs ds : List K} {τ : Tape K} (hN : N ≤ bound)
    (hNat : IsExactNatLit dec M bound) (row : Fin (N - k))
    (hd : ds = (List.range (N - k)).map fun i => vec rs ((k + i) * N + (k + i)))
    (hmax : ∀ i : Fin (N - k), |dec (vec ds i)| ≤ |dec (vec ds row)|)
    (hfirst : ∀ i : Fin (N - k), i < row → |dec (vec ds i)| < |dec (vec ds row)|) :
    (diagonalChoiceSpec dec bound).post [N, k] τ [rs] [[M.lit (k + row.val : ℕ)]] := by
  let r : Fin N := ⟨k + row.val, by have := row.isLt; omega⟩
  have hr : k ≤ r.val := by dsimp only [r]; omega
  have hword (i : Fin N) (hi : k ≤ i.val) :
      vec ds (i.val - k) = vec rs (i.val * N + i.val) := by
    have ht : i.val - k < N - k := by omega
    rw [hd]
    simp only [vec, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range ht, Option.map_some, Option.getD_some,
      show k + (i.val - k) = i.val by omega]
  have hrow : vec ds row.val = vec rs (r.val * N + r.val) := by
    simpa only [r, Nat.add_sub_cancel_left] using hword r hr
  refine ⟨r, hr, hNat (k + row.val) (by have := row.isLt; omega), ?_, ?_⟩
  · intro i hi
    have ht : i.val - k < N - k := by omega
    have h := hmax ⟨i.val - k, ht⟩
    change |dec (vec ds (i.val - k))| ≤ |dec (vec ds row.val)| at h
    simpa only [hword i hi, hrow] using h
  · intro i hi hir
    have ht : i.val - k < N - k := by omega
    have hlt : (⟨i.val - k, ht⟩ : Fin (N - k)) < row := by
      have hi' : i.val < r.val := hir
      change i.val < k + row.val at hi'
      change i.val - k < row.val
      omega
    have h := hfirst ⟨i.val - k, ht⟩ hlt
    change |dec (vec ds (i.val - k))| < |dec (vec ds row.val)| at h
    simpa only [hword i hi, hrow] using h

/-- All selection instructions succeed under local scalar, comparison, dimension-literal and
conversion contracts. The selected row is read from the actual scan output, never guessed. -/
theorem diagonalChoice_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (diagonalChoice (Op := Op) (Tst := Tst)).Meets I (diagonalChoiceSpec dec bound) := by
  routine_intro [n, k] (R, p) reads (rs)
  change Writes .total I τ _ (Env.frame [n, k] [R, p]) (Fp.blocks [p] [1]) _ m
  obtain ⟨hkn, hnb⟩ := hpre
  obtain ⟨hlR, hlp⟩ := hl
  alloc as diagonal relative
  have hdEq : diagonal = m.store.length := by change m.store.length = m.store.length; rfl
  have hrEq : relative = m.store.length + 1 := by rfl
  have hlen : s_diagonal.length = m.store.length + 2 := by simpa using hlen_diagonal
  have hld : diagonal < s_diagonal.length := by rw [hdEq]; omega
  have hlr : relative < s_diagonal.length := by rw [hrEq]; omega
  have hRd : R.1 ≠ diagonal := by rw [hdEq]; omega
  have hdr : diagonal ≠ relative := by rw [hdEq, hrEq]; omega
  call (copyDiagonal_meets hI) [n, k, n - k] (R, (diagonal, 0))
    (pre := by change k + (n - k) ≤ n; omega)
    as m₁ hfr₁ hpos₁ (ds) hcopy
  case' hroom =>
    change (0 + (n - k) ≤ s_diagonal.len diagonal) ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hdiagonal.ge, trivial⟩
  call (LU.argmaxAbs_meets hI hcmp hlit hM hNat) [n - k] ((diagonal, 0), (relative, 0))
    (pre := ⟨by omega, by omega⟩) as m₂ hfr₂ hpos₂ (js) hscan
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hjs
  obtain ⟨row, hrow, hmax, hfirst⟩ : ∃ row : Fin (n - k), dec w = row.val ∧
      (∀ i : Fin (n - k), |dec (vec ds i)| ≤ |dec (vec ds row)|) ∧
      (∀ i : Fin (n - k), i < row → |dec (vec ds i)| < |dec (vec ds row)|) := hscan
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hrow (by have := row.isLt; omega) ?_
  refine (writes_indexLit hlit (n := k + row.val) rfl rfl (by
    change p.2 < m₂.store.len p.1
    rw [hfr₂.len_eq, hfr₁.len_eq, (hbelow_diagonal p.1 hlp).1]
    omega)).mono (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨hpos₃, hout⟩ s₃ hs₃ hB
  refine ⟨by simpa only [Nat.add_zero] using hpos₃.trans (hpos₂.trans hpos₁),
    [[M.lit (k + row.val : ℕ)]], Mem.readBlocks_of_cons ?_ rfl, ?_⟩
  · exact Store.Below.readBlock_of hB hlp (Store.readBlock_one_of_get hout)
  · exact diagonalChoice_post hnb hNat row (by exact hcopy)
      hmax hfirst

end NLAlib.Cholesky
