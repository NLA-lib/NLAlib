/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Polynomial
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Rational matrix functions and their block differences

The upper off-diagonal blocks of rational functions of triangular block matrices give ordered
first and second differences. The finite-difference rules hold without assumptions on spectral
separation or diagonalizability.

## Main results

* `NLAlib.sub_rationalMatrixEval`: exact first difference.
* `NLAlib.rationalSecondBlockDifference_resolvent`: the ordered three-resolvent product.
-/

@[expose] public section

namespace NLAlib

section
open Polynomial
open scoped Matrix

variable {𝕜 m n o : Type*} [CommRing 𝕜]
variable [Fintype m] [Fintype n] [Fintype o]
variable [DecidableEq m] [DecidableEq n] [DecidableEq o]

/-- The finite one-insertion sum for a monomial. [Tropp2026, §§4.2–4.4]. -/
def monomialBlockDifference (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  ∑ j ∈ Finset.range k, A ^ (k.pred - j) * H * B ^ j

private theorem monomialBlockDifference_succ (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) (k : ℕ) :
    monomialBlockDifference A B H (k + 1) =
      A ^ k * H + monomialBlockDifference A B H k * B := by
  simp only [monomialBlockDifference, Nat.pred_succ]
  rw [Finset.sum_range_succ', add_comm]
  simp only [tsub_zero, pow_zero, Matrix.mul_one, Matrix.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have he : k - (j + 1) = k.pred - j := by
    simp [Nat.pred_eq_sub_one, Nat.sub_sub, Nat.add_comm]
  rw [he, pow_succ]
  simp only [Matrix.mul_assoc]

/-- Actual powers of triangular matrices have the insertion sum as their upper block. -/
private theorem upperBlockTwo_pow (A : Matrix m m 𝕜) (H : Matrix m n 𝕜)
    (B : Matrix n n 𝕜) (k : ℕ) :
    Matrix.fromBlocks A H 0 B ^ k =
      Matrix.fromBlocks (A ^ k) (monomialBlockDifference A B H k) 0 (B ^ k) := by
  induction k with
  | zero => simp [monomialBlockDifference, Matrix.fromBlocks_one]
  | succ k hk =>
    rw [pow_succ, hk, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← pow_succ,
      monomialBlockDifference_succ]

/-- The first polynomial block difference, written as a finite insertion sum. -/
def polynomialBlockDifference (p : 𝕜[X]) (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • monomialBlockDifference A B H k

/-- Polynomial evaluation on an actual triangular matrix. -/
private theorem aeval_upperBlockTwo (p : 𝕜[X]) (A : Matrix m m 𝕜) (H : Matrix m n 𝕜)
    (B : Matrix n n 𝕜) :
    aeval (Matrix.fromBlocks A H 0 B) p =
      Matrix.fromBlocks (aeval A p) (polynomialBlockDifference p A B H) 0 (aeval B p) := by
  simp only [aeval_eq_sum_range, upperBlockTwo_pow, polynomialBlockDifference]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.sum_apply, Matrix.smul_apply]

/-- The ordered second polynomial difference: two insertions in their given order. -/
def polynomialSecondBlockDifference (p : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜) :
    Matrix m o 𝕜 :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k •
    ∑ j ∈ Finset.range k, monomialBlockDifference A B G (k.pred - j) * H * C ^ j

/-- A three-block triangular matrix with a zero direct first-to-third block. -/
private abbrev upperBlockThree (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) : Matrix ((m ⊕ n) ⊕ o) ((m ⊕ n) ⊕ o) 𝕜 :=
  Matrix.fromBlocks (Matrix.fromBlocks A G 0 B) (Matrix.fromRows 0 H) 0 C

private theorem polynomialBlockDifference_upperBlockTwo (p : 𝕜[X])
    (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) :
    polynomialBlockDifference p (Matrix.fromBlocks A G 0 B) C (Matrix.fromRows 0 H) =
      Matrix.fromRows (polynomialSecondBlockDifference p A B C G H)
        (polynomialBlockDifference p B C H) := by
  simp only [polynomialBlockDifference, monomialBlockDifference, upperBlockTwo_pow,
    Matrix.fromBlocks_mul_fromRows, Matrix.mul_zero, zero_add,
    Matrix.fromRows_mul]
  ext i j
  rcases i with i | i <;>
    simp only [polynomialSecondBlockDifference, monomialBlockDifference,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, smul_eq_mul]

/-- The ordered second difference is the actual first-to-third block of the
polynomial of a three-block triangular matrix. -/
private theorem aeval_upperBlockThree (p : 𝕜[X])
    (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) :
    aeval (upperBlockThree A G B H C) p =
      Matrix.fromBlocks
        (Matrix.fromBlocks (aeval A p) (polynomialBlockDifference p A B G) 0 (aeval B p))
        (Matrix.fromRows (polynomialSecondBlockDifference p A B C G H)
          (polynomialBlockDifference p B C H)) 0 (aeval C p) := by
  simp only [upperBlockThree, aeval_upperBlockTwo, polynomialBlockDifference_upperBlockTwo]

end

section
open Polynomial
open scoped Matrix

variable {𝕜 m n o : Type*} [Field 𝕜]
variable [Fintype m] [Fintype n] [Fintype o]
variable [DecidableEq m] [DecidableEq n] [DecidableEq o]

/-- Rational functional calculus by a polynomial pair. A singular denominator evaluation gives
zero by the matrix inverse convention. [Higham2008, §1.2]. -/
noncomputable def rationalMatrixEval (P Q : 𝕜[X]) (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  aeval A P * (aeval A Q)⁻¹

/-- The first rational block difference, with its explicit finite formula. [Tropp2026, §§4.2–4.4].
-/
noncomputable def rationalBlockDifference (P Q : 𝕜[X]) (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  (polynomialBlockDifference P A B H -
    rationalMatrixEval P Q A * polynomialBlockDifference Q A B H) * (aeval B Q)⁻¹

/-- The ordered second rational block difference, obtained by triangular inversion. [Tropp2026,
§§4.2–4.4]. -/
noncomputable def rationalSecondBlockDifference (P Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜) :
    Matrix m o 𝕜 :=
  (polynomialSecondBlockDifference P A B C G H -
    rationalMatrixEval P Q A * polynomialSecondBlockDifference Q A B C G H -
    rationalBlockDifference P Q A B G * polynomialBlockDifference Q B C H) * (aeval C Q)⁻¹

private theorem isUnit_aeval_upperBlockTwo (Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (H : Matrix m n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    IsUnit (aeval (Matrix.fromBlocks A H 0 B) Q) := by
  rw [aeval_upperBlockTwo]
  exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA, hB⟩

private theorem isUnit_aeval_upperBlockThree (Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    IsUnit (aeval (upperBlockThree A G B H C) Q) :=
  isUnit_aeval_upperBlockTwo Q _ _ _ (isUnit_aeval_upperBlockTwo Q A B G hA hB) hC

/-- The first difference is exactly the upper block of the rational function of the actual
triangular matrix. [Tropp2026, §§4.2–4.4]. -/
theorem rationalMatrixEval_fromBlocks (P Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (H : Matrix m n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    rationalMatrixEval P Q (Matrix.fromBlocks A H 0 B) =
      Matrix.fromBlocks (rationalMatrixEval P Q A) (rationalBlockDifference P Q A B H)
        0 (rationalMatrixEval P Q B) := by
  unfold rationalMatrixEval
  rw [aeval_upperBlockTwo, aeval_upperBlockTwo,
    Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ ⟨fun _ => hB, fun _ => hA⟩,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  simp [rationalBlockDifference, rationalMatrixEval, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- **The ordered second difference is exactly the first-to-third block.** Only the three diagonal
denominator evaluations need be invertible. [Tropp2026, §§4.2–4.4].
Result: matrix-function-block-divided-differences -/
theorem rationalMatrixEval_fromBlocks_fromBlocks (P Q : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    rationalMatrixEval P Q (Matrix.fromBlocks (Matrix.fromBlocks A G 0 B)
      (Matrix.fromRows 0 H) 0 C) =
      Matrix.fromBlocks
        (Matrix.fromBlocks (rationalMatrixEval P Q A) (rationalBlockDifference P Q A B G)
          0 (rationalMatrixEval P Q B))
        (Matrix.fromRows (rationalSecondBlockDifference P Q A B C G H)
          (rationalBlockDifference P Q B C H)) 0 (rationalMatrixEval P Q C) := by
  rw [rationalMatrixEval_fromBlocks P Q _ _ _
    (isUnit_aeval_upperBlockTwo Q A B G hA hB) hC,
    rationalMatrixEval_fromBlocks P Q A B G hA hB]
  congr 1
  unfold rationalBlockDifference
  rw [polynomialBlockDifference_upperBlockTwo, polynomialBlockDifference_upperBlockTwo,
    rationalMatrixEval_fromBlocks P Q A B G hA hB,
    Matrix.fromBlocks_mul_fromRows, Matrix.zero_mul, zero_add]
  have hsub (D₁ D₂ : Matrix m o 𝕜) (E₁ E₂ : Matrix n o 𝕜) :
      Matrix.fromRows D₁ E₁ - Matrix.fromRows D₂ E₂ =
        Matrix.fromRows (D₁ - D₂) (E₁ - E₂) := by
    ext (i | i) j <;> simp
  rw [hsub, Matrix.fromRows_mul]
  congr 1
  simp only [rationalSecondBlockDifference, sub_sub]

/-- Rational evaluation preserves rectangular intertwining, provided the two denominators are
invertible. [Tropp2026, §§4.2–4.4]. -/
theorem rationalMatrixEval_mul_eq_mul_rationalMatrixEval (P Q : 𝕜[X])
    {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} {S : Matrix m n 𝕜}
    (h : A * S = S * B) (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    rationalMatrixEval P Q A * S = S * rationalMatrixEval P Q B := by
  have hQ := aeval_mul_eq_mul_aeval_of_mul_eq_mul h Q
  have hP := aeval_mul_eq_mul_aeval_of_mul_eq_mul h P
  have hAd := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hBd := (Matrix.isUnit_iff_isUnit_det _).mp hB
  have hi : (aeval A Q)⁻¹ * S = S * (aeval B Q)⁻¹ := by
    calc
      _ = (aeval A Q)⁻¹ * S * (aeval B Q) * (aeval B Q)⁻¹ := by
        simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBd]
      _ = (aeval A Q)⁻¹ * (aeval A Q * S) * (aeval B Q)⁻¹ := by
        rw [hQ]; simp only [Matrix.mul_assoc]
      _ = S * (aeval B Q)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAd, Matrix.one_mul]
  simp only [rationalMatrixEval, Matrix.mul_assoc]
  rw [hi, ← Matrix.mul_assoc, hP, Matrix.mul_assoc]

end

section
open Polynomial
open scoped Matrix
variable {𝕜 n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

/-- **The exact first finite-difference formula for a rational matrix function.** [Tropp2026,
§§4.2–4.4].
Result: matrix-function-block-divided-differences -/
theorem sub_rationalMatrixEval (P Q : 𝕜[X]) (A B : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    rationalMatrixEval P Q A - rationalMatrixEval P Q B =
      rationalBlockDifference P Q A B (A - B) := by
  let M := Matrix.fromBlocks A (A - B) 0 B
  let S : Matrix n (n ⊕ n) 𝕜 := Matrix.fromCols 1 1
  have hi : A * S = S * M := by
    simp [S, M, Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols]
  have hf := rationalMatrixEval_mul_eq_mul_rationalMatrixEval P Q hi hA
    (isUnit_aeval_upperBlockTwo Q A B (A - B) hA hB)
  rw [show M = Matrix.fromBlocks A (A - B) 0 B from rfl,
    rationalMatrixEval_fromBlocks P Q A B (A - B) hA hB] at hf
  have he := congrArg Matrix.toCols₂ hf
  simp only [Matrix.mul_fromCols, mul_one, Matrix.toCols₂_fromCols, Matrix.fromCols_mul_fromBlocks,
    one_mul, mul_zero, add_zero, S] at he
  exact (sub_eq_iff_eq_add).mpr he

/-- Changing the right base point produces the ordered second block difference. [Tropp2026,
§§4.2–4.4]. -/
theorem sub_rationalBlockDifference_right (P Q : 𝕜[X]) (A B C H : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    rationalBlockDifference P Q A B H - rationalBlockDifference P Q A C H =
      rationalSecondBlockDifference P Q A B C H (B - C) := by
  let M := upperBlockThree A H B (B - C) C
  let S : Matrix ((n ⊕ n) ⊕ n) (n ⊕ n) 𝕜 :=
    Matrix.fromRows 1 (Matrix.fromCols 0 (-1))
  have hi : M * S = S * Matrix.fromBlocks A H 0 C := by
    simp only [M, S, upperBlockThree, Matrix.fromBlocks_mul_fromRows,
      Matrix.fromRows_mul, Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols,
      Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul]
    ext ((i | i) | i) (j | j) <;> simp
  have hf := rationalMatrixEval_mul_eq_mul_rationalMatrixEval P Q hi
    (isUnit_aeval_upperBlockThree Q A B C H (B - C) hA hB hC)
    (isUnit_aeval_upperBlockTwo Q A C H hA hC)
  rw [show M = upperBlockThree A H B (B - C) C from rfl,
    rationalMatrixEval_fromBlocks_fromBlocks P Q A B C H (B - C) hA hB hC,
    rationalMatrixEval_fromBlocks P Q A C H hA hC] at hf
  simp only [S, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul,
    Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.mul_one,
    Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul] at hf
  ext i j
  have he := congrArg (fun D => D (Sum.inl (Sum.inl i)) (Sum.inr j)) hf
  simp only [Matrix.fromRows_neg, Matrix.fromRows_apply_inl, Matrix.add_apply,
    Matrix.fromBlocks_apply₁₂, Matrix.fromCols_apply_inr, Matrix.neg_apply] at he
  simp only [Matrix.sub_apply]
  have he' : rationalBlockDifference P Q A B H i j -
      rationalSecondBlockDifference P Q A B C H (B - C) i j =
      rationalBlockDifference P Q A C H i j := by simpa only [sub_eq_add_neg] using he
  exact sub_eq_of_eq_add (by simpa only [add_comm] using sub_eq_iff_eq_add.mp he')

/-- Changing the left base point produces the other ordered second difference. [Tropp2026,
§§4.2–4.4]. -/
theorem sub_rationalBlockDifference_left (P Q : 𝕜[X]) (A B C H : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    rationalBlockDifference P Q A C H - rationalBlockDifference P Q B C H =
      rationalSecondBlockDifference P Q A B C (A - B) H := by
  let M := upperBlockThree A (A - B) B H C
  let S : Matrix (n ⊕ n) ((n ⊕ n) ⊕ n) 𝕜 :=
    Matrix.fromCols (Matrix.fromRows (Matrix.fromCols 1 1) 0)
      (Matrix.fromRows 0 1)
  have hi : Matrix.fromBlocks A H 0 C * S = S * M := by
    simp only [M, S, upperBlockThree, Matrix.fromBlocks_mul_fromRows,
      Matrix.fromRows_mul, Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols,
      Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero]
    ext (i | i) ((j | j) | j) <;> simp
  have hf := rationalMatrixEval_mul_eq_mul_rationalMatrixEval P Q hi
    (isUnit_aeval_upperBlockTwo Q A C H hA hC)
    (isUnit_aeval_upperBlockThree Q A B C (A - B) H hA hB hC)
  rw [show M = upperBlockThree A (A - B) B H C from rfl,
    rationalMatrixEval_fromBlocks_fromBlocks P Q A B C (A - B) H hA hB hC,
    rationalMatrixEval_fromBlocks P Q A C H hA hC] at hf
  simp only [S, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul,
    Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows] at hf
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero] at hf
  ext i j
  have he := congrArg (fun D => D (Sum.inl i) (Sum.inr j)) hf
  simp only [Matrix.fromCols_zero, Matrix.fromCols_apply_inr, Matrix.fromRows_apply_inl,
    Matrix.fromRows_zero, add_zero, Matrix.add_apply, Matrix.zero_apply] at he
  simp only [Matrix.sub_apply]
  exact (sub_eq_iff_eq_add).mpr he

end

section
open Polynomial
open scoped Matrix
variable {𝕜 n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

@[simp] private theorem polynomialBlockDifference_C (c : 𝕜) (A B H : Matrix n n 𝕜) :
    polynomialBlockDifference (C c) A B H = 0 := by
  simp [polynomialBlockDifference, monomialBlockDifference]

@[simp] private theorem polynomialSecondBlockDifference_C (c : 𝕜) (A B D G H : Matrix n n 𝕜) :
    polynomialSecondBlockDifference (C c) A B D G H = 0 := by
  simp [polynomialSecondBlockDifference]

@[simp] private theorem polynomialBlockDifference_one (A B H : Matrix n n 𝕜) :
    polynomialBlockDifference 1 A B H = 0 := polynomialBlockDifference_C 1 A B H

@[simp] private theorem polynomialSecondBlockDifference_one (A B C G H : Matrix n n 𝕜) :
    polynomialSecondBlockDifference 1 A B C G H = 0 :=
  polynomialSecondBlockDifference_C 1 A B C G H

@[simp] private theorem polynomialBlockDifference_X (A B H : Matrix n n 𝕜) :
    polynomialBlockDifference X A B H = H := by
  simp [polynomialBlockDifference, monomialBlockDifference, Finset.sum_range_succ]

@[simp] private theorem polynomialSecondBlockDifference_X (A B C G H : Matrix n n 𝕜) :
    polynomialSecondBlockDifference X A B C G H = 0 := by
  simp [polynomialSecondBlockDifference, monomialBlockDifference, Finset.sum_range_succ]

private theorem polynomialBlockDifference_sub (P Q : 𝕜[X]) (A B H : Matrix n n 𝕜) :
    polynomialBlockDifference (P - Q) A B H =
      polynomialBlockDifference P A B H - polynomialBlockDifference Q A B H := by
  ext i j
  have h := congrArg (fun D : Matrix (n ⊕ n) (n ⊕ n) 𝕜 => D (Sum.inl i) (Sum.inr j))
    (map_sub (aeval (Matrix.fromBlocks A H 0 B)) P Q)
  simpa only [aeval_upperBlockTwo, Matrix.sub_apply, Matrix.fromBlocks_apply₁₂] using h

private theorem polynomialSecondBlockDifference_sub (P Q : 𝕜[X]) (A B C G H : Matrix n n 𝕜) :
    polynomialSecondBlockDifference (P - Q) A B C G H =
      polynomialSecondBlockDifference P A B C G H -
        polynomialSecondBlockDifference Q A B C G H := by
  ext i j
  have h := congrArg (fun D : Matrix ((n ⊕ n) ⊕ n) ((n ⊕ n) ⊕ n) 𝕜 =>
    D (Sum.inl (Sum.inl i)) (Sum.inr j)) (map_sub (aeval (upperBlockThree A G B H C)) P Q)
  simpa only [aeval_upperBlockThree, Matrix.sub_apply, Matrix.fromBlocks_apply₁₂,
    Matrix.fromRows_apply_inl] using h

/-- Rational evaluation respects multiplication of scalar rational expressions. [Tropp2026,
§§4.2–4.4]. -/
theorem rationalMatrixEval_mul (P Q R S : 𝕜[X]) (A : Matrix n n 𝕜) :
    rationalMatrixEval (P * R) (Q * S) A =
      rationalMatrixEval P Q A * rationalMatrixEval R S A := by
  have hc : Commute (aeval A R) (aeval A Q)⁻¹ :=
    by
      have h : Commute (aeval A R) (aeval A Q) := (Commute.all R Q).map (aeval A).toRingHom
      rw [Matrix.nonsing_inv_eq_ringInverse]
      by_cases hu : IsUnit (aeval A Q)
      · obtain ⟨u, hu⟩ := hu
        rw [← hu, Ring.inverse_unit]
        rw [← hu] at h
        exact h.units_inv_right
      · rw [Ring.inverse_non_unit _ hu]
        exact Commute.zero_right _
  rw [show Q * S = S * Q from mul_comm Q S]
  simp only [rationalMatrixEval, map_mul, Matrix.mul_inv_rev]
  calc
    _ = aeval A P * (aeval A R * (aeval A Q)⁻¹) * (aeval A S)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc.eq]; simp only [Matrix.mul_assoc]

/-- First block product rule, proved by multiplication of the actual evaluated blocks. [Tropp2026,
§§4.2–4.4]. -/
theorem rationalBlockDifference_mul (P Q R S : 𝕜[X]) (A B H : Matrix n n 𝕜)
    (hQA : IsUnit (aeval A Q)) (hQB : IsUnit (aeval B Q))
    (hSA : IsUnit (aeval A S)) (hSB : IsUnit (aeval B S)) :
    rationalBlockDifference (P * R) (Q * S) A B H =
      rationalMatrixEval P Q A * rationalBlockDifference R S A B H +
        rationalBlockDifference P Q A B H * rationalMatrixEval R S B := by
  have h := rationalMatrixEval_mul P Q R S (Matrix.fromBlocks A H 0 B)
  rw [rationalMatrixEval_fromBlocks P Q A B H hQA hQB,
    rationalMatrixEval_fromBlocks R S A B H hSA hSB,
    rationalMatrixEval_fromBlocks (P * R) (Q * S) A B H
      (by simpa only [map_mul] using hQA.mul hSA) (by simpa only [map_mul] using hQB.mul hSB),
    Matrix.fromBlocks_multiply] at h
  exact congrArg Matrix.toBlocks₁₂ h

/-- Ordered second block product rule, including the cross insertion in its specified order.
[Tropp2026, §§4.2–4.4]. -/
theorem rationalSecondBlockDifference_mul (P Q R S : 𝕜[X]) (A B C G H : Matrix n n 𝕜)
    (hQA : IsUnit (aeval A Q)) (hQB : IsUnit (aeval B Q)) (hQC : IsUnit (aeval C Q))
    (hSA : IsUnit (aeval A S)) (hSB : IsUnit (aeval B S)) (hSC : IsUnit (aeval C S)) :
    rationalSecondBlockDifference (P * R) (Q * S) A B C G H =
      rationalMatrixEval P Q A * rationalSecondBlockDifference R S A B C G H +
      rationalBlockDifference P Q A B G * rationalBlockDifference R S B C H +
      rationalSecondBlockDifference P Q A B C G H * rationalMatrixEval R S C := by
  have h := rationalMatrixEval_mul P Q R S (upperBlockThree A G B H C)
  rw [rationalMatrixEval_fromBlocks_fromBlocks P Q A B C G H hQA hQB hQC,
    rationalMatrixEval_fromBlocks_fromBlocks R S A B C G H hSA hSB hSC,
    rationalMatrixEval_fromBlocks_fromBlocks (P * R) (Q * S) A B C G H
      (by simpa only [map_mul] using hQA.mul hSA) (by simpa only [map_mul] using hQB.mul hSB)
      (by simpa only [map_mul] using hQC.mul hSC), Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul] at h
  ext i j
  have he := congrArg (fun D => D (Sum.inl (Sum.inl i)) (Sum.inr j)) h
  simpa using he

/-- First block inverse rule. [Tropp2026, §§4.2–4.4]. -/
theorem rationalBlockDifference_one (Q : 𝕜[X]) (A B H : Matrix n n 𝕜) :
    rationalBlockDifference 1 Q A B H =
      -((aeval A Q)⁻¹ * polynomialBlockDifference Q A B H * (aeval B Q)⁻¹) := by
  simp [rationalBlockDifference, rationalMatrixEval,
    Matrix.mul_assoc]

/-- Ordered second inverse rule. [Tropp2026, §§4.2–4.4]. -/
theorem rationalSecondBlockDifference_one (Q : 𝕜[X]) (A B C G H : Matrix n n 𝕜) :
    rationalSecondBlockDifference 1 Q A B C G H =
      (aeval A Q)⁻¹ * polynomialBlockDifference Q A B G * (aeval B Q)⁻¹ *
        polynomialBlockDifference Q B C H * (aeval C Q)⁻¹ -
      (aeval A Q)⁻¹ * polynomialSecondBlockDifference Q A B C G H * (aeval C Q)⁻¹ := by
  simp [rationalSecondBlockDifference, rationalBlockDifference_one, rationalMatrixEval,
    Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- The ordered second resolvent difference contains precisely one insertion of each direction in
its prescribed order. [Tropp2026, §§4.2–4.4]. -/
theorem rationalSecondBlockDifference_resolvent (ζ : 𝕜) (A B C G H : Matrix n n 𝕜) :
    rationalSecondBlockDifference 1 (Polynomial.C ζ - X) A B C G H =
      (ζ • (1 : Matrix n n 𝕜) - A)⁻¹ * G * (ζ • (1 : Matrix n n 𝕜) - B)⁻¹ * H *
        (ζ • (1 : Matrix n n 𝕜) - C)⁻¹ := by
  rw [rationalSecondBlockDifference_one]
  simp [polynomialBlockDifference_sub, polynomialSecondBlockDifference_sub,
    Algebra.algebraMap_eq_smul_one]

end

end NLAlib
