/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PartialPivot
public import NLAlib.Ops.Blas.StridedCopy
public import NLAlib.Ops.Logic.ViewBlock
public import NLAlib.Ops.Logic.MatrixView
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Actual first-maximum selection on a stored matrix line

A bounded strided line is gathered by scalar copies from the declared square matrix.
The shared absolute-value scan stores a relative index. The actual bounded conversion
reads that word, and a dimension-literal instruction records the absolute line position.
This one selector serves active rows, columns and diagonal lines without a matrix oracle.

## Main results

* `NLAlib.LU.lineChoice_meets`: actual bounded scan and exact absolute selected-index output.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Gather and scan a bounded stored line, read the actual relative index, then write its
absolute position. The source matrix is read only and both temporary vectors are scoped. -/
def lineChoice : Routine Op Tst := routine% [n, start, base, stride] (R : n * n) → (p : 1) {
  let line ← alloc (n - start);
  let relative ← alloc 1;
  run copyStridedRoutine [n - start, stride, 1] (R[base], line);
  run argmaxAbs [n - start] (line, relative);
  let row ← index (Has.inj IdxTst.toNat) (relative) ≤ n - start - 1;
  call (Has.inj IndexOp.lit) [start + row] () → (p)
}

variable [Inhabited K]

/-- The selected absolute line position is bounded and exactly decoded. Its original stored
magnitude is maximal, with strict inequality at every earlier eligible position. -/
def lineChoiceSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, start, base, stride] (rs) → ([w]) requires
    start < n ∧ n ≤ bound ∧ (∀ i < n - start, base + stride * i < n * n) ensures
    ∃ r : Fin n, start ≤ r.val ∧ dec w = r.val ∧
      (∀ i : Fin n, start ≤ i.val →
        |dec (vec rs (base + stride * (i.val - start)))| ≤
          |dec (vec rs (base + stride * (r.val - start)))|) ∧
      (∀ i : Fin n, start ≤ i.val → i < r →
        |dec (vec rs (base + stride * (i.val - start)))| <
          |dec (vec rs (base + stride * (r.val - start)))|)

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] [Has IdxTst Tst] in
private theorem lineChoice_post {M : Machine K} {dec : K → ℝ} {N start base stride bound : ℕ}
    {rs ds : List K} {τ : Tape K} (hN : N ≤ bound)
    (hNat : IsExactNatLit dec M bound) (row : Fin (N - start))
    (hd : ds = (List.range (N - start)).map fun i => vec rs (base + stride * i))
    (hmax : ∀ i : Fin (N - start), |dec (vec ds i)| ≤ |dec (vec ds row)|)
    (hfirst : ∀ i : Fin (N - start), i < row → |dec (vec ds i)| < |dec (vec ds row)|) :
    (lineChoiceSpec dec bound).post [N, start, base, stride] τ [rs]
      [[M.lit (start + row.val : ℕ)]] := by
  let r : Fin N := ⟨start + row.val, by have := row.isLt; omega⟩
  have hr : start ≤ r.val := by dsimp only [r]; omega
  have hword (i : Fin N) (hi : start ≤ i.val) :
      vec ds (i.val - start) = vec rs (base + stride * (i.val - start)) := by
    have ht : i.val - start < N - start := by omega
    rw [hd]
    simp only [vec, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range ht, Option.map_some, Option.getD_some]
  have hrow : vec ds row.val = vec rs (base + stride * (r.val - start)) := by
    simpa only [r, Nat.add_sub_cancel_left] using hword r hr
  refine ⟨r, hr, hNat (start + row.val) (by have := row.isLt; omega), ?_, ?_⟩
  · intro i hi
    have ht : i.val - start < N - start := by omega
    have h := hmax ⟨i.val - start, ht⟩
    change |dec (vec ds (i.val - start))| ≤ |dec (vec ds row.val)| at h
    simpa only [hword i hi, hrow] using h
  · intro i hi hir
    have ht : i.val - start < N - start := by omega
    have hlt : (⟨i.val - start, ht⟩ : Fin (N - start)) < row := by
      have hi' : i.val < r.val := hir
      change i.val < start + row.val at hi'
      change i.val - start < row.val
      omega
    have h := hfirst ⟨i.val - start, ht⟩ hlt
    change |dec (vec ds (i.val - start))| < |dec (vec ds row.val)| at h
    simpa only [hword i hi, hrow] using h

/-- Every actual line copy, scan, stored-index conversion and absolute literal succeeds
under the local primitive contracts and the explicit bounded line geometry. No run is assumed. -/
theorem lineChoice_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (lineChoice (Op := Op) (Tst := Tst)).Meets I (lineChoiceSpec dec bound) := by
  routine_intro [n, start, base, stride] (R, p) reads (rs)
  change Writes .total I τ _ (Env.frame [n, start, base, stride] [R, p]) (Fp.blocks [p] [1]) _ m
  obtain ⟨hsn, hnb, hcells⟩ := hpre
  obtain ⟨hlR, hlp⟩ := hl
  let words := (List.range (n - start)).map fun i => vec rs (base + stride * i)
  have hview : m.store.readView R.1 (R.2 + base) ⟨1, some (n - start, stride)⟩ =
      some words := by
    apply Store.readView_of_readBlock hrs (by simp [words, View.cells_runs])
    intro i hi
    have hi' : i < n - start := by simpa only [View.cells_runs, Nat.mul_one] using hi
    refine ⟨by simpa only [View.offset_runs_one] using hcells i hi', ?_⟩
    have hn : base + stride * i < rs.length := by
      rw [Store.length_of_readBlock hrs]
      exact hcells i hi'
    simp only [words, View.offset_runs_one, List.getElem?_map, List.getElem?_range hi',
      Option.map_some, vec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
      Option.getD_some]
  change Writes .total I τ _ (Env.frame [n, start, base, stride] [R, p]) (Fp.blocks [p] [1]) _ m
  alloc as line relative
  have hlEq : line = m.store.length := by change m.store.length = m.store.length; rfl
  have hrEq : relative = m.store.length + 1 := by rfl
  have hlen : s_line.length = m.store.length + 2 := by simpa using hlen_line
  have hll : line < s_line.length := by rw [hlEq]; omega
  have hlr : relative < s_line.length := by rw [hrEq]; omega
  have hRl : R.1 ≠ line := by rw [hlEq]; omega
  have hlrel : line ≠ relative := by rw [hlEq, hrEq]; omega
  have hview' : s_line.readView R.1 (R.2 + base) ⟨1, some (n - start, stride)⟩ =
      some words := Store.Below.readView_of hbelow_line hlR hview
  call (copyStridedRoutine_meets hI) [n - start, stride, 1] ((R.1, R.2 + base), (line, 0))
    as m₁ hfr₁ hpos₁ (ds) hcopy
  case' hcall => exact [words]
  case' hr => exact Mem.readViews_of_cons hview' rfl
  case' hpre => exact fun _ => Nat.zero_lt_one
  case' hroom =>
    change (∀ i < (n - start) * 1, 0 + (⟨1, some (n - start, 1)⟩ : View).offset i <
      s_line.len line) ∧ True
    simp only [Nat.mul_one, View.offset_runs_one, Nat.one_mul, Nat.zero_add, and_true]
    intro i hi
    rw [hline]
    exact hi
  rw [Store.readView_unitStride] at hds
  call (argmaxAbs_meets hI hcmp hlit hM hNat) [n - start] ((line, 0), (relative, 0))
    (pre := ⟨by omega, by omega⟩) as m₂ hfr₂ hpos₂ (js) hscan
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hjs
  obtain ⟨row, hrow, hmax, hfirst⟩ : ∃ row : Fin (n - start), dec w = row.val ∧
      (∀ i : Fin (n - start), |dec (vec ds i)| ≤ |dec (vec ds row)|) ∧
      (∀ i : Fin (n - start), i < row → |dec (vec ds i)| < |dec (vec ds row)|) := hscan
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hrow (by have := row.isLt; omega) ?_
  refine (writes_indexLit hlit (n := start + row.val) rfl rfl (by
    change p.2 < m₂.store.len p.1
    rw [hfr₂.len_eq, hfr₁.len_eq, (hbelow_line p.1 hlp).1]
    omega)).mono (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨hpos₃, hout⟩ s₃ hs₃ hB
  refine ⟨by simpa only [Nat.add_zero] using hpos₃.trans (hpos₂.trans hpos₁),
    [[M.lit (start + row.val : ℕ)]], Mem.readBlocks_of_cons ?_ rfl, ?_⟩
  · exact Store.Below.readBlock_of hB hlp (Store.readBlock_one_of_get hout)
  · exact lineChoice_post hnb hNat row (by exact hcopy) hmax hfirst

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] [Has IdxTst Tst] in
/-- A unit-stride active column has its usual packed matrix-entry score and first-row tie rule. -/
theorem lineChoiceSpec_column {dec : K → ℝ} {N bound : ℕ} (k c : Fin N)
    {rs : List K} {w : K} {τ : Tape K}
    (h : (lineChoiceSpec dec bound).post [N, k.val, c.val * N + k.val, 1] τ [rs] [[w]]) :
    ∃ r : Fin N, k ≤ r ∧ dec w = r.val ∧
      (∀ i : Fin N, k ≤ i → |dec (vec rs (c.val * N + i.val))| ≤
        |dec (vec rs (c.val * N + r.val))|) ∧
      (∀ i : Fin N, k ≤ i → i < r → |dec (vec rs (c.val * N + i.val))| <
        |dec (vec rs (c.val * N + r.val))|) := by
  obtain ⟨r, hkr, hd, hmax, hfirst⟩ := h
  have haddr (i : Fin N) (hi : k ≤ i) :
      c.val * N + k.val + 1 * (i.val - k.val) = c.val * N + i.val := by omega
  refine ⟨r, hkr, hd, ?_, ?_⟩
  · intro i hi
    simpa only [haddr i hi, haddr r hkr] using hmax i hi
  · intro i hi hir
    simpa only [haddr i hi, haddr r hkr] using hfirst i hi hir

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] [Has IdxTst Tst] in
/-- A leading-dimension-stride active row has the usual packed entries and first-column ties. -/
theorem lineChoiceSpec_row {dec : K → ℝ} {N bound : ℕ} (k i : Fin N)
    {rs : List K} {w : K} {τ : Tape K}
    (h : (lineChoiceSpec dec bound).post [N, k.val, k.val * N + i.val, N] τ [rs] [[w]]) :
    ∃ c : Fin N, k ≤ c ∧ dec w = c.val ∧
      (∀ j : Fin N, k ≤ j → |dec (vec rs (j.val * N + i.val))| ≤
        |dec (vec rs (c.val * N + i.val))|) ∧
      (∀ j : Fin N, k ≤ j → j < c → |dec (vec rs (j.val * N + i.val))| <
        |dec (vec rs (c.val * N + i.val))|) := by
  obtain ⟨c, hkc, hd, hmax, hfirst⟩ := h
  have haddr (j : Fin N) (hj : k ≤ j) :
      k.val * N + i.val + N * (j.val - k.val) = j.val * N + i.val := by
    have he : k.val + (j.val - k.val) = j.val := by omega
    have hm := congrArg (fun t : ℕ => t * N) he
    rw [Nat.add_mul] at hm
    rw [Nat.mul_comm N (j.val - k.val)]
    omega
  refine ⟨c, hkc, hd, ?_, ?_⟩
  · intro j hj
    simpa only [haddr j hj, haddr c hkc] using hmax j hj
  · intro j hj hjc
    simpa only [haddr j hj, haddr c hkc] using hfirst j hj hjc

end NLAlib.LU
