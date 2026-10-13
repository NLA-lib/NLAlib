/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.FieldTheory.Separable
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Functions.Complexification

/-!
# Schur triangularisation

Every square complex matrix is unitarily similar to an upper triangular matrix, with its
eigenvalues on the diagonal in any prescribed order. Over a general `RCLike` field the same holds
when the characteristic polynomial splits, in particular for a real matrix all of whose complex
eigenvalues are real.

The eigenvalues of a matrix that need not be Hermitian are given by a listing:
`NLAlib.IsEigenvalueListing A d` says that the family `d` lists the roots of the characteristic
polynomial of `A` with multiplicity.

## Main definitions

* `NLAlib.IsEigenvalueListing`: `A.charpoly = ∏ i, (X - C (d i))`.

## Main results

* `NLAlib.IsEigenvalueListing.exists_hasOrthonormalCols_isUpperTriangular`: Schur's theorem with
  a prescribed diagonal.
* `NLAlib.exists_hasOrthonormalCols_isUpperTriangular`: Schur's theorem over `ℂ`.
* `NLAlib.IsEigenvalueListing.sum_norm_sq_le_frobNorm_sq`: Schur's inequality.
* `NLAlib.IsEigenvalueListing.sum_norm_sq_eq_frobNorm_sq_iff`: equality exactly for normal
  matrices.
* `NLAlib.exists_isEigenvalueListing_add_mul_of_commute`: eigenvalues of commuting matrices add.
* `NLAlib.dense_setOf_separable_charpoly`: matrices with distinct eigenvalues are dense.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {K : Type*} [Field K] {ι κ n : Type*} [Fintype ι] [Fintype κ]
  [Fintype n] [DecidableEq n]

/-! ### Listings of the eigenvalues -/

/-- `IsEigenvalueListing A d`: the family `d` **lists the eigenvalues** of `A` with algebraic
multiplicity, `A.charpoly = ∏ i, (X - C (d i))`. Over `ℂ` every matrix has a listing; over a
general field the existence of one says that the characteristic polynomial splits. For a
Hermitian matrix the sorted `eigenvalue A` is a listing. -/
def IsEigenvalueListing (A : Matrix n n K) (d : ι → K) : Prop :=
  A.charpoly = ∏ i, (X - C (d i))

/-- `IsEigenvalueListing` unfolded. -/
theorem isEigenvalueListing_iff {A : Matrix n n K} {d : ι → K} :
    IsEigenvalueListing A d ↔ A.charpoly = ∏ i, (X - C (d i)) :=
  Iff.rfl

/-- A listing has as many entries as the matrix has rows. -/
theorem IsEigenvalueListing.card_eq {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : Fintype.card ι = Fintype.card n := by
  sorry

/-- A complex matrix has a listing of its eigenvalues. -/
theorem exists_isEigenvalueListing (A : Matrix n n ℂ) : ∃ d : n → ℂ, IsEigenvalueListing A d := by
  sorry

/-- **Two listings of the eigenvalues differ by a relabelling.**
Port of `NLAlib.exists_perm_eq_of_prod_X_sub_C_eq`, there over `ℂ` on one index type. -/
theorem IsEigenvalueListing.exists_equiv_eq {A : Matrix n n K} {a : ι → K} {b : κ → K}
    (ha : IsEigenvalueListing A a) (hb : IsEigenvalueListing A b) :
    ∃ e : ι ≃ κ, a = b ∘ e := by
  sorry

/-- A relabelling of a listing is a listing. -/
theorem IsEigenvalueListing.comp_equiv {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) (e : κ ≃ ι) : IsEigenvalueListing A (d ∘ e) := by
  sorry

/-- The spectrum is the set of listed eigenvalues. -/
theorem IsEigenvalueListing.spectrum_eq_range {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : spectrum K A = Set.range d := by
  sorry

/-- The trace is the sum of the listed eigenvalues.
Port of `NLAlib.trace_eq_sum_of_charpoly_eq_prod`. -/
theorem IsEigenvalueListing.trace_eq_sum {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : A.trace = ∑ i, d i := by
  sorry

/-- The determinant is the product of the listed eigenvalues. -/
theorem IsEigenvalueListing.det_eq_prod {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : A.det = ∏ i, d i := by
  sorry

/-- The eigenvalues of a power are the powers of the eigenvalues. -/
theorem IsEigenvalueListing.pow {A : Matrix n n K} {d : ι → K} (h : IsEigenvalueListing A d)
    (k : ℕ) : IsEigenvalueListing (A ^ k) (fun i => d i ^ k) := by
  sorry

/-- The diagonal of an upper triangular matrix lists its eigenvalues. -/
theorem _root_.Matrix.IsUpperTriangular.isEigenvalueListing_diag [LinearOrder n]
    {T : Matrix n n K} (hT : T.IsUpperTriangular) : IsEigenvalueListing T fun i => T i i := by
  sorry

/-- A real matrix all of whose complex eigenvalues are real has a real listing of its
eigenvalues. Port of `NLAlib.exists_real_charpoly_factors_of_complex_spectrum_real`. -/
theorem exists_isEigenvalueListing_of_forall_im_eq_zero {A : Matrix n n ℝ}
    (h : ∀ μ ∈ spectrum ℂ (complexify A), μ.im = 0) :
    ∃ d : n → ℝ, IsEigenvalueListing A d := by
  sorry

/-! ### Schur's theorem -/

/-- **Schur triangularisation with a prescribed diagonal.** If `d` lists the eigenvalues of `A`,
there is a unitary `U` with `Uᴴ A U` upper triangular with diagonal `d`, in the given order.
Over `ℝ` this is orthogonal triangularisation of a matrix with real eigenvalues.
[HornJohnson2013, Theorem 2.3.1].
Port of `NLAlib.exists_unitary_schur_triangularization_with_charpoly`.
Result: schur-triangularization -/
theorem IsEigenvalueListing.exists_hasOrthonormalCols_isUpperTriangular [LinearOrder n]
    {A : Matrix n n 𝕜} {d : n → 𝕜} (hd : IsEigenvalueListing A d) :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ (Uᴴ * A * U).IsUpperTriangular ∧
      ∀ i, (Uᴴ * A * U) i i = d i := by
  sorry

/-- **Schur's theorem.** Every square complex matrix is unitarily similar to an upper triangular
matrix. [HornJohnson2013, Theorem 2.3.1]; [GolubVanLoan2013, Theorem 7.1.3].
Port of `NLAlib.exists_unitary_schur_triangularization`. -/
theorem exists_hasOrthonormalCols_isUpperTriangular [LinearOrder n] (A : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧ (Uᴴ * A * U).IsUpperTriangular := by
  sorry

/-- The diagonal of a triangular matrix unitarily similar to `A` lists the eigenvalues of `A`. -/
theorem isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul [LinearOrder n]
    {A U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) (hT : (Uᴴ * A * U).IsUpperTriangular) :
    IsEigenvalueListing A fun i => (Uᴴ * A * U) i i := by
  sorry

/-- **Triangularisation with small off-diagonal part.** For every `ε > 0` a complex matrix is
similar to an upper triangular matrix whose off-diagonal entries are smaller than `ε`. This is
the step from the spectral radius to a norm in which the matrix is almost as small.
[HornJohnson2013, Lemma 5.6.10].
Port of `NLAlib.exists_similarity_upper_triangular_small_entries`. -/
theorem exists_isUpperTriangular_inv_mul_mul_norm_apply_lt [LinearOrder n] (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ (S⁻¹ * A * S).IsUpperTriangular ∧
      ∀ i j, i ≠ j → ‖(S⁻¹ * A * S) i j‖ < ε := by
  sorry

/-! ### Schur's inequality -/

/-- **Schur's inequality**: the sum of the squared moduli of the eigenvalues is at most the
squared Frobenius norm. [HornJohnson2013, §2.3].
Port of `NLAlib.sum_norm_sq_schur_diagonal_le_frobSq`. -/
theorem IsEigenvalueListing.sum_norm_sq_le_frobNorm_sq {A : Matrix n n 𝕜} {d : ι → 𝕜}
    (hd : IsEigenvalueListing A d) : ∑ i, ‖d i‖ ^ 2 ≤ frobNorm A ^ 2 := by
  sorry

/-- **Equality in Schur's inequality holds exactly for normal matrices.**
[HornJohnson2013, Theorem 2.5.3].
Port of `NLAlib.sum_norm_sq_characteristic_eq_frobSq_iff_normal`. -/
theorem IsEigenvalueListing.sum_norm_sq_eq_frobNorm_sq_iff {A : Matrix n n 𝕜} {d : ι → 𝕜}
    (hd : IsEigenvalueListing A d) : ∑ i, ‖d i‖ ^ 2 = frobNorm A ^ 2 ↔ IsStarNormal A := by
  sorry

/-! ### Commuting matrices and density -/

/-- **Eigenvalues of commuting matrices pair up**: commuting complex matrices have listings of
their eigenvalues whose sums and products list the eigenvalues of `A + B` and `A * B`.
[HornJohnson2013, Theorem 2.4.8.1].
Port of `NLAlib.exists_paired_charpoly_factors_add_mul_of_commute`. -/
theorem exists_isEigenvalueListing_add_mul_of_commute {A B : Matrix n n ℂ} (h : Commute A B) :
    ∃ a b : n → ℂ, IsEigenvalueListing A a ∧ IsEigenvalueListing B b ∧
      IsEigenvalueListing (A + B) (fun i => a i + b i) ∧
      IsEigenvalueListing (A * B) (fun i => a i * b i) := by
  sorry

/-- **Matrices with distinct eigenvalues are dense.**
[HornJohnson2013, Theorem 2.4.7.1]. Port of `NLAlib.dense_separable_charpoly`. -/
theorem dense_setOf_separable_charpoly : Dense {A : Matrix n n 𝕜 | A.charpoly.Separable} := by
  sorry

end NLAlib
