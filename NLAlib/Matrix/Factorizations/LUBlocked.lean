/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Deferred trailing updates for blocked LU

Inside a panel, Gaussian elimination updates its columns and block rows while retaining the
trailing block from panel entry. A single rectangular factor product supplies the deferred
trailing correction after the panel is complete. The states use the existing canonical total
elimination and factor functions.

## Main definitions

* `NLAlib.luPanelState`: canonical panel entries with an unchanged trailing block.
* `NLAlib.luPanelStep`: one pivot updates the two panel rectangles.
* `NLAlib.luPanelRectangle`: a rectangle update using saved original operands.

## Main results

* `NLAlib.luPanelStep_luPanelState`: panel execution advances the canonical invariant.
* `NLAlib.gaussState_sub_luLower_mul_luUpper`: one active canonical factor product.
* `NLAlib.gaussState_eq_add_panel_sum`: the product deferred during a panel.
* `NLAlib.luPanelState_sub_panel_sum`: the trailing product restores the exit residual.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {K : Type*} [Field K] {N : ℕ}

/-- The panel and its block rows agree with elimination after $k$ steps; only the trailing
square beginning at `stop` retains its state from panel entry `start`. This is a residual
matrix, not a new factorization predicate. [GolubVanLoan2013, §3.2]. -/
def luPanelState (A : Matrix (Fin N) (Fin N) K) (start stop k : ℕ) :
    Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => if stop ≤ i.val ∧ stop ≤ j.val then
    gaussState A start i j else gaussState A k i j

/-- Before its first elimination step a panel is exactly the complete entry residual. -/
theorem luPanelState_start (A : Matrix (Fin N) (Fin N) K) (start stop : ℕ) :
    luPanelState A start stop start = gaussState A start := by
  ext i j
  simp only [luPanelState, Matrix.of_apply, ite_self]

/-- Every pivot column inside the panel agrees with canonical elimination, including all rows
below it. No nonzero-pivot assumption is required for this stored-state identity. -/
theorem luPanelState_apply_column (A : Matrix (Fin N) (Fin N) K) (start stop : ℕ)
    (k i : Fin N) (hk : k.val < stop) :
    luPanelState A start stop k.val i k = gaussState A k.val i k := by
  simp only [luPanelState, Matrix.of_apply, not_le.mpr hk, and_false, if_false]

/-- Every pivot row inside the panel agrees with canonical elimination, including all trailing
columns. No nonzero-pivot assumption is required. -/
theorem luPanelState_apply_row (A : Matrix (Fin N) (Fin N) K) (start stop : ℕ)
    (k j : Fin N) (hk : k.val < stop) :
    luPanelState A start stop k.val k j = gaussState A k.val k j := by
  simp only [luPanelState, Matrix.of_apply, not_le.mpr hk, false_and, if_false]

/-- Update one rectangle using the saved row and column from `source`. Entries of `current`
outside the rectangle are retained. The two panel calls use disjoint column intervals, so
later writes cannot change the saved operands of either update. -/
def luPanelRectangle (source current : Matrix (Fin N) (Fin N) K) (r : Fin N)
    (row col m n : ℕ) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j =>
    if row ≤ i.val ∧ i.val < row + m ∧ col ≤ j.val ∧ j.val < col + n then
      current i j - source i r / source r r * source r j else current i j

/-- Rectangle coordinates and unchanged exterior entries determine the saved-operand update.
The embedding uses the existing finite-index operations and the supplied rectangle bounds. -/
theorem eq_luPanelRectangle_of_coordinates
    (source current result : Matrix (Fin N) (Fin N) K) (r : Fin N)
    (row col m n : ℕ) (hr : row + m ≤ N) (hc : col + n ≤ N)
    (hin : ∀ i j, result (Fin.castLE hr (Fin.natAdd row i))
      (Fin.castLE hc (Fin.natAdd col j)) =
        current (Fin.castLE hr (Fin.natAdd row i)) (Fin.castLE hc (Fin.natAdd col j)) -
          source (Fin.castLE hr (Fin.natAdd row i)) r / source r r *
            source r (Fin.castLE hc (Fin.natAdd col j)))
    (hout : ∀ i j, (i.val < row ∨ row + m ≤ i.val ∨ j.val < col ∨ col + n ≤ j.val) →
      result i j = current i j) :
    result = luPanelRectangle source current r row col m n := by
  ext i j
  by_cases h : row ≤ i.val ∧ i.val < row + m ∧ col ≤ j.val ∧ j.val < col + n
  · let ii : Fin m := ⟨i.val - row, by omega⟩
    let jj : Fin n := ⟨j.val - col, by omega⟩
    have hi : Fin.castLE hr (Fin.natAdd row ii) = i := Fin.ext (by dsimp [ii]; omega)
    have hj : Fin.castLE hc (Fin.natAdd col jj) = j := Fin.ext (by dsimp [jj]; omega)
    rw [luPanelRectangle, Matrix.of_apply, if_pos h]
    simpa only [hi, hj] using hin ii jj
  · rw [luPanelRectangle, Matrix.of_apply, if_neg h]
    exact hout i j (by omega)

/-- One panel pivot updates its remaining panel columns and its trailing block rows. The
bottom-right square beginning at `stop` is deferred to a later matrix multiplication.
The operands are the saved original pivot row and column. [GolubVanLoan2013, §3.2]. -/
def luPanelStep (M : Matrix (Fin N) (Fin N) K) (r : Fin N) (stop : ℕ) :
    Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => if r ≤ i ∧ r ≤ j ∧ (i.val < stop ∨ j.val < stop) then
    M i j - M i r / M r r * M r j else M i j

/-- The two packed rank-one rectangles cover precisely the panel update, with no overlap.
Both calls use the original saved pivot row and column. -/
theorem luPanelRectangle_twice (M : Matrix (Fin N) (Fin N) K) (r : Fin N)
    (stop : ℕ) (hr : r.val ≤ stop) (hstop : stop ≤ N) :
    luPanelRectangle M (luPanelRectangle M M r r.val r.val (N - r.val) (stop - r.val))
      r r.val stop (stop - r.val) (N - stop) = luPanelStep M r stop := by
  ext i j
  simp only [luPanelRectangle, luPanelStep, Matrix.of_apply]
  split_ifs <;> try rfl
  all_goals omega

/-- Under the original nonzero-pivot premise, the two panel rectangles advance the canonical
panel state while leaving the deferred trailing square unchanged. Already retired rows and
columns remain zero by the existing Gaussian-elimination lemmas. -/
theorem luPanelStep_luPanelState (A : Matrix (Fin N) (Fin N) K) (start stop : ℕ)
    (r : Fin N) (hr : r.val < stop)
    (hp : ∀ l : Fin N, gaussState A l.val l l ≠ 0) :
    luPanelStep (luPanelState A start stop r.val) r stop =
      luPanelState A start stop (r.val + 1) := by
  ext i j
  by_cases ht : stop ≤ i.val ∧ stop ≤ j.val
  · have hm : ¬(r ≤ i ∧ r ≤ j ∧ (i.val < stop ∨ j.val < stop)) := by omega
    simp only [luPanelStep, luPanelState, Matrix.of_apply, hm, ht, true_and, if_false, if_true]
  · have he : luPanelState A start stop r.val i j = gaussState A r.val i j := by
      simp only [luPanelState, Matrix.of_apply, ht, if_false]
    have he' : luPanelState A start stop (r.val + 1) i j =
        gaussState A (r.val + 1) i j := by
      simp only [luPanelState, Matrix.of_apply, ht, if_false]
    by_cases hi : r ≤ i
    · by_cases hj : r ≤ j
      · have hm : r ≤ i ∧ r ≤ j ∧ (i.val < stop ∨ j.val < stop) := by omega
        rw [luPanelStep, Matrix.of_apply, if_pos hm, he, he',
          luPanelState_apply_column A start stop r i hr,
          luPanelState_apply_row A start stop r r hr,
          luPanelState_apply_row A start stop r j hr, gaussState_succ A r.isLt,
          eliminationStep_apply]
        rw [div_eq_mul_inv]
        ring
      · have hjr : j.val < r.val := lt_of_not_ge hj
        have hm : ¬(r ≤ i ∧ r ≤ j ∧ (i.val < stop ∨ j.val < stop)) := by tauto
        rw [luPanelStep, Matrix.of_apply, if_neg hm, he, he',
          gaussState_apply_eq_zero_of_lt_right A (fun l _ => hp l) i hjr,
          gaussState_apply_eq_zero_of_lt_right A (fun l _ => hp l) i (by omega)]
    · have hir : i.val < r.val := lt_of_not_ge hi
      have hm : ¬(r ≤ i ∧ r ≤ j ∧ (i.val < stop ∨ j.val < stop)) := by tauto
      rw [luPanelStep, Matrix.of_apply, if_neg hm, he, he',
        gaussState_apply_eq_zero_of_lt_left A (fun l _ => hp l) hir j,
        gaussState_apply_eq_zero_of_lt_left A (fun l _ => hp l) (by omega) j]

/-- On entries strictly below and right of a pivot, the next total Gaussian residual removes
exactly the product of the canonical lower and upper entries. Total division handles zero
pivots as well; a blocked driver may impose nonzero pivots for its panel execution. -/
theorem gaussState_sub_luLower_mul_luUpper (A : Matrix (Fin N) (Fin N) K)
    (r i j : Fin N) (hri : r < i) (hrj : r < j) :
    gaussState A r.val i j - luLower A i r * luUpper A r j =
      gaussState A (r.val + 1) i j := by
  rw [gaussState_succ A r.isLt]
  simp only [luLower, luUpper, Matrix.of_apply, hri, hrj.le, if_true,
    eliminationStep_apply, div_eq_mul_inv]
  ring

/-- The trailing entries at panel entry equal the completed trailing residual plus the factor
product accumulated over that panel. The sum uses the actual packed panel width, so it is
exactly the inner dimension of the eventual matrix multiplication. The bound hypothesis
supplies the canonical `Fin.castLE` embedding and no new matrix encoding is introduced.
[GolubVanLoan2013, §3.2]. -/
theorem gaussState_eq_add_panel_sum (A : Matrix (Fin N) (Fin N) K) (start width : ℕ)
    (h : start + width ≤ N) (i j : Fin N)
    (hi : start + width ≤ i.val) (hj : start + width ≤ j.val) :
    gaussState A start i j = gaussState A (start + width) i j +
      ∑ t : Fin width,
        luLower A i (Fin.castLE h (Fin.natAdd start t)) *
          luUpper A (Fin.castLE h (Fin.natAdd start t)) j := by
  induction width with
  | zero => simp
  | succ width ih =>
    have h' : start + width ≤ N := by omega
    have hi' : start + width ≤ i.val := by omega
    have hj' : start + width ≤ j.val := by omega
    have he := ih h' hi' hj'
    rw [Fin.sum_univ_castSucc]
    have hsum : (∑ t : Fin width,
        luLower A i (Fin.castLE h (Fin.natAdd start t.castSucc)) *
          luUpper A (Fin.castLE h (Fin.natAdd start t.castSucc)) j) =
        ∑ t : Fin width, luLower A i (Fin.castLE h' (Fin.natAdd start t)) *
          luUpper A (Fin.castLE h' (Fin.natAdd start t)) j := by
      apply Finset.sum_congr rfl
      intro t _
      congr 2
    rw [hsum]
    let r : Fin N := Fin.castLE h (Fin.natAdd start (Fin.last width))
    have hr : r.val = start + width := rfl
    have hstep := gaussState_sub_luLower_mul_luUpper A r i j
      (by change r.val < i.val; omega) (by change r.val < j.val; omega)
    change gaussState A start i j = gaussState A (start + (width + 1)) i j +
      ((∑ t : Fin width, luLower A i (Fin.castLE h' (Fin.natAdd start t)) *
        luUpper A (Fin.castLE h' (Fin.natAdd start t)) j) + luLower A i r * luUpper A r j)
    rw [hr] at hstep
    rw [he]
    rw [show start + (width + 1) = start + width + 1 by omega]
    linear_combination hstep

/-- Applying the deferred panel product only to the trailing square restores the full
canonical residual at panel exit. This is the matrix identity consumed by the eventual
GEMM-backed update; entries outside the trailing square retain their panel values. -/
theorem luPanelState_sub_panel_sum (A : Matrix (Fin N) (Fin N) K) (start width : ℕ)
    (h : start + width ≤ N) :
    Matrix.of (fun i j : Fin N =>
      if start + width ≤ i.val ∧ start + width ≤ j.val then
        luPanelState A start (start + width) (start + width) i j -
          ∑ t : Fin width, luLower A i (Fin.castLE h (Fin.natAdd start t)) *
            luUpper A (Fin.castLE h (Fin.natAdd start t)) j
      else luPanelState A start (start + width) (start + width) i j) =
      gaussState A (start + width) := by
  ext i j
  by_cases ht : start + width ≤ i.val ∧ start + width ≤ j.val
  · simp only [Matrix.of_apply, ht, if_true, luPanelState, true_and]
    have he := gaussState_eq_add_panel_sum A start width h i j ht.1 ht.2
    linear_combination he
  · simp only [Matrix.of_apply, ht, if_false, luPanelState]


/-- A trailing update formed from completed stored factor prefixes restores the canonical
exit residual. The entrywise hypotheses are exactly the raw product and exterior guarantees
of the gathered BLAS3 update; factor entries outside the committed prefix are irrelevant. -/
theorem eq_gaussState_of_panel_products (A F G result : Matrix (Fin N) (Fin N) K)
    (start width : ℕ) (h : start + width ≤ N)
    (hF : ∀ i j : Fin N, j.val < start + width → F i j = luLower A i j)
    (hG : ∀ i j : Fin N, i.val < start + width → G i j = luUpper A i j)
    (hin : ∀ i j : Fin N, start + width ≤ i.val → start + width ≤ j.val →
      result i j = luPanelState A start (start + width) (start + width) i j -
        ∑ t : Fin width, F i (Fin.castLE h (Fin.natAdd start t)) *
          G (Fin.castLE h (Fin.natAdd start t)) j)
    (hout : ∀ i j : Fin N, (i.val < start + width ∨ j.val < start + width) →
      result i j = luPanelState A start (start + width) (start + width) i j) :
    result = gaussState A (start + width) := by
  rw [← luPanelState_sub_panel_sum A start width h]
  ext i j
  by_cases ht : start + width ≤ i.val ∧ start + width ≤ j.val
  · rw [Matrix.of_apply, if_pos ht, hin i j ht.1 ht.2]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    have hidx : (Fin.castLE h (Fin.natAdd start t)).val < start + width := by
      simp only [Fin.val_castLE, Fin.val_natAdd]
      omega
    rw [hF i _ hidx, hG _ j hidx]
  · rw [Matrix.of_apply, if_neg ht]
    exact hout i j (by omega)

end NLAlib
