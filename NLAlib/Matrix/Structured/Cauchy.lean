/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.Matrix.Order
public import NLAlib.Matrix.Factorizations.Elimination

/-!
# Cauchy and Hilbert matrices

The Cauchy matrix of two families `x`, `y` has entries `1 / (x i + y j)`. Its determinant is
Cauchy's double product, which is positive for increasing positive families; the Hilbert matrix
is the case `x i = i + 1`, `y j = j`.

## Main definitions

* `NLAlib.cauchyMatrix`, `NLAlib.hilbertMatrix`.

## Main results

* `NLAlib.det_cauchyMatrix`: Cauchy's determinant formula.
* `NLAlib.det_cauchyMatrix_pos`, `NLAlib.det_hilbertMatrix_pos`.
* `NLAlib.posDef_cauchyMatrix_self`: a symmetric Cauchy matrix of distinct positive numbers is
  positive definite.
* `NLAlib.posDef_hilbertMatrix`: the Hilbert matrix is positive definite.
-/

@[expose] public section

open scoped Matrix MatrixOrder

universe u

namespace NLAlib

variable {K : Type*} [Field K] {m n : Type*}

/-- The **Cauchy matrix** of two families: entries `1 / (x i + y j)`.
Port of `NLAlib.cauchyMatrix`, there over `ℝ`. -/
def cauchyMatrix (x : m → K) (y : n → K) : Matrix m n K :=
  Matrix.of fun i j => (x i + y j)⁻¹

/-- Entries of a Cauchy matrix. -/
@[simp]
theorem cauchyMatrix_apply (x : m → K) (y : n → K) (i : m) (j : n) :
    cauchyMatrix x y i j = (x i + y j)⁻¹ :=
  rfl

/-- The transpose of a Cauchy matrix is the Cauchy matrix of the swapped families. -/
theorem transpose_cauchyMatrix (x : m → K) (y : n → K) :
    (cauchyMatrix x y)ᵀ = cauchyMatrix y x := by
  ext i j
  rw [Matrix.transpose_apply, cauchyMatrix_apply, cauchyMatrix_apply, add_comm]

/-- One elimination step on a Cauchy matrix: the Schur complement of the first pivot is a
Cauchy matrix scaled by diagonal matrices on both sides. -/
private theorem det_cauchyMatrix_succ {n : ℕ} (x y : Fin (n + 1) → K)
    (h : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det = (x 0 + y 0)⁻¹ *
      (∏ i : Fin n, (x i.succ - x 0) / (x i.succ + y 0)) *
      (∏ j : Fin n, (y j.succ - y 0) / (x 0 + y j.succ)) *
      (cauchyMatrix (fun i : Fin n => x i.succ) fun j : Fin n => y j.succ).det := by
  let c : Fin (n + 1) → K := Fin.cons 0 fun i => -((x 0 + y 0) / (x i.succ + y 0))
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    Matrix.of fun i j => cauchyMatrix x y i j + c i * cauchyMatrix x y 0 j
  have hB : B.det = (cauchyMatrix x y).det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (Fin.cons_zero _ _) fun i j => rfl
  have h00 := h 0 0
  have h0 : B 0 0 = (x 0 + y 0)⁻¹ := by
    simp only [B, c, Matrix.of_apply, cauchyMatrix_apply, Fin.cons_zero, zero_mul, add_zero]
  have hcol : ∀ i : Fin n, B i.succ 0 = 0 := by
    intro i
    have hi := h i.succ 0
    simp only [B, c, Matrix.of_apply, cauchyMatrix_apply, Fin.cons_succ]
    field_simp
    ring
  have hsub : B.submatrix Fin.succ Fin.succ =
      Matrix.diagonal (fun i : Fin n => (x i.succ - x 0) / (x i.succ + y 0)) *
        cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ) *
        Matrix.diagonal fun j : Fin n => (y j.succ - y 0) / (x 0 + y j.succ) := by
    ext i j
    have hij := h i.succ j.succ
    have hi := h i.succ 0
    have hj := h 0 j.succ
    simp only [B, c, Matrix.submatrix_apply, Matrix.of_apply, cauchyMatrix_apply, Fin.cons_succ,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    field_simp
    ring
  rw [← hB, Matrix.det_succ_column_zero, Fin.sum_univ_succ,
    Finset.sum_eq_zero fun i _ => by rw [hcol, mul_zero, zero_mul], add_zero, Fin.succAbove_zero,
    hsub, h0, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Fin.val_zero, pow_zero, one_mul]
  ring

/-- The product of the differences splits off the differences from the first index. -/
private theorem prod_Ioi_sub_succ {n : ℕ} (x : Fin (n + 1) → K) :
    ∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i) =
      (∏ i : Fin n, (x i.succ - x 0)) * ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j.succ - x i.succ) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.Ioi_zero_eq_map, Finset.prod_map, Fin.coe_succEmb, Fin.prod_Ioi_succ]

/-- Cauchy's determinant as a quotient of the two products of differences by the product of the
denominators. -/
private theorem det_cauchyMatrix_aux {n : ℕ} (x y : Fin n → K) (h : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det =
      (∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i)) * (∏ i, ∏ j ∈ Finset.Ioi i, (y j - y i)) /
        ∏ i, ∏ j, (x i + y j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrow : ∏ i : Fin n, (x i.succ + y 0) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => h i.succ 0
    have hcol : ∏ j : Fin n, (x 0 + y j.succ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => h 0 j.succ
    have hdiag : ∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ =>
        h i.succ j.succ
    have h00 := h 0 0
    have hden : ∏ i : Fin (n + 1), ∏ j : Fin (n + 1), (x i + y j) =
        (x 0 + y 0) * (∏ i : Fin n, (x i.succ + y 0)) * (∏ j : Fin n, (x 0 + y j.succ)) *
          ∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ) := by
      rw [Fin.prod_univ_succ]
      simp only [Fin.prod_univ_succ, Finset.prod_mul_distrib]
      ring
    rw [det_cauchyMatrix_succ x y h, ih _ _ fun i j => h i.succ j.succ, prod_Ioi_sub_succ x,
      prod_Ioi_sub_succ y, hden, Finset.prod_div_distrib, Finset.prod_div_distrib]
    field_simp

/-- **Cauchy's determinant.** For families with nonvanishing denominators,
`det = ∏_{i < j} (x j - x i)(y j - y i) / ∏_{i, j} (x i + y j)`.
[HornJohnson2013, §0.9.12]. Port of `NLAlib.det_cauchyMatrix_eq_prod_differences`. -/
theorem det_cauchyMatrix {n : ℕ} (x y : Fin n → K) (h : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det =
      (∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i) * (y j - y i)) / ∏ i, ∏ j, (x i + y j) := by
  rw [det_cauchyMatrix_aux x y h]
  simp only [Finset.prod_mul_distrib]

/-- The determinant of a Cauchy matrix of strictly increasing families with positive denominators
is positive. Port of `NLAlib.det_cauchyMatrix_pos_of_strictMono`. -/
theorem det_cauchyMatrix_pos {n : ℕ} {x y : Fin n → ℝ} (hx : StrictMono x) (hy : StrictMono y)
    (h : ∀ i j, 0 < x i + y j) : 0 < (cauchyMatrix x y).det := by
  rw [det_cauchyMatrix x y fun i j => (h i j).ne']
  exact div_pos
    (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      mul_pos (sub_pos.mpr (hx (Finset.mem_Ioi.mp hj))) (sub_pos.mpr (hy (Finset.mem_Ioi.mp hj))))
    (Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => h i j)

/-- The **Hilbert matrix** of order `n`: entries `1 / (i + j + 1)`.
Port of `NLAlib.hilbertMatrix`. -/
noncomputable def hilbertMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ((i : ℝ) + j + 1)⁻¹

/-- The Hilbert matrix is a Cauchy matrix. Port of `NLAlib.hilbertMatrix_eq_cauchyMatrix`. -/
theorem hilbertMatrix_eq_cauchyMatrix (n : ℕ) :
    hilbertMatrix n = cauchyMatrix (fun i : Fin n => (i : ℝ) + 1) fun j : Fin n => (j : ℝ) := by
  ext i j
  rw [cauchyMatrix_apply, hilbertMatrix, Matrix.of_apply, add_right_comm]

/-- The determinant of the Hilbert matrix is positive. Port of `NLAlib.det_hilbertMatrix_pos`. -/
theorem det_hilbertMatrix_pos (n : ℕ) : 0 < (hilbertMatrix n).det := by
  rw [hilbertMatrix_eq_cauchyMatrix]
  refine det_cauchyMatrix_pos (fun i j hij => ?_) (fun i j hij => ?_) fun i j => by positivity
  · exact add_lt_add_left (Nat.cast_lt.mpr hij) 1
  · exact Nat.cast_lt.mpr hij

/-- A symmetric Cauchy matrix of distinct positive numbers is positive definite: the Schur
complement of a pivot is a symmetric Cauchy matrix scaled by an invertible diagonal matrix on both
sides. -/
private theorem posDef_cauchyMatrix_self_aux (k : ℕ) :
    ∀ (ι : Type u) [Fintype ι], Fintype.card ι = k → ∀ a : ι → ℝ, (∀ i, 0 < a i) →
      Function.Injective a → (cauchyMatrix a a).PosDef := by
  induction k with
  | zero =>
    intro ι _ hι a _ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hι
    exact ⟨Matrix.ext fun i => isEmptyElim i, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩
  | succ k ih =>
    intro ι _ hι a ha hinj
    classical
    have : Nonempty ι := Fintype.card_pos_iff.mp (hι ▸ k.succ_pos)
    obtain ⟨t⟩ := this
    have hherm : (cauchyMatrix a a).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, transpose_cauchyMatrix]
    have hcard : Fintype.card {i // i ≠ t} = k := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hι, Nat.add_sub_cancel]
    have hstep : (eliminationStep (cauchyMatrix a a) t).submatrix
        (Subtype.val : {i // i ≠ t} → ι) Subtype.val =
        (Matrix.diagonal fun i : {i // i ≠ t} => (a i - a t) / (a i + a t))ᴴ *
          cauchyMatrix (fun i : {i // i ≠ t} => a i) (fun i : {i // i ≠ t} => a i) *
          Matrix.diagonal fun i : {i // i ≠ t} => (a i - a t) / (a i + a t) := by
      ext i j
      have hi := ha i
      have hj := ha j
      have ht := ha t
      rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.submatrix_apply, eliminationStep_apply, cauchyMatrix_apply, Pi.star_apply,
        star_trivial]
      field_simp
      ring
    rw [hherm.posDef_iff_eliminationStep t, hstep]
    refine ⟨inv_pos.mpr (add_pos (ha t) (ha t)), ?_⟩
    refine (ih {i // i ≠ t} hcard _ (fun i => ha i) (hinj.comp Subtype.val_injective))
      |>.conjTranspose_mul_mul_same ?_
    refine Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_diagonal).mpr ?_)
    refine Pi.isUnit_iff.mpr fun i => IsUnit.mk0 _ (div_ne_zero ?_ (add_pos (ha i) (ha t)).ne')
    exact sub_ne_zero.mpr fun h => i.2 (hinj h)

/-- **A symmetric Cauchy matrix of distinct positive numbers is positive definite**: for an
injective family `a` of positive reals on any finite index type, the matrix with entries
`1 / (a i + a j)` is positive definite. [HornJohnson2013, §7.1.P19 context]. -/
theorem posDef_cauchyMatrix_self {ι : Type*} [Finite ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) : (cauchyMatrix a a).PosDef := by
  cases nonempty_fintype ι
  exact posDef_cauchyMatrix_self_aux _ ι rfl a ha hinj

/-- **The Hilbert matrix is positive definite.** [HornJohnson2013, §7.1.P19 context]. -/
theorem posDef_hilbertMatrix (n : ℕ) : (hilbertMatrix n).PosDef := by
  have h : hilbertMatrix n =
      cauchyMatrix (fun i : Fin n => (i : ℝ) + 1 / 2) fun i : Fin n => (i : ℝ) + 1 / 2 := by
    ext i j
    rw [cauchyMatrix_apply, hilbertMatrix, Matrix.of_apply]
    congr 1
    ring
  rw [h]
  exact posDef_cauchyMatrix_self (fun i => by positivity) fun i j hij =>
    Fin.ext (Nat.cast_injective (add_right_cancel hij))

end NLAlib
