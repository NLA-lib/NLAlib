/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Spectral.EigenvalueListing

/-!
# Schur triangularisation

Every square complex matrix is unitarily similar to an upper triangular matrix, with its
eigenvalues on the diagonal in any prescribed order. Over a general `RCLike` field the same holds
when the characteristic polynomial splits, in particular for a real matrix all of whose complex
eigenvalues are real.

The eigenvalues of a matrix that need not be Hermitian are given by a listing,
`NLAlib.IsEigenvalueListing A d`, defined in `NLAlib.Matrix.Spectral.EigenvalueListing`.

## Main results

* `NLAlib.IsEigenvalueListing.exists_hasOrthonormalCols_isUpperTriangular`: Schur's theorem with
  a prescribed diagonal.
* `NLAlib.exists_hasOrthonormalCols_isUpperTriangular`: Schur's theorem over `ℂ`.
* `NLAlib.IsEigenvalueListing.sum_norm_sq_le_frobNorm_sq`: Schur's inequality.
* `NLAlib.IsEigenvalueListing.sum_norm_sq_eq_frobNorm_sq_iff`: equality exactly for normal
  matrices.
* `NLAlib.exists_isEigenvalueListing_add_mul_of_commute`: eigenvalues of commuting matrices add.
* `NLAlib.dense_setOf_separable_charpoly`: matrices with distinct eigenvalues are dense.

## Implementation notes

The similarity of `NLAlib.IsEigenvalueListing.exists_isUpperTriangular_inv_mul_mul_of_commute`,
which triangularises a commuting pair over any field, is made unitary by a QR factorization. For
a normal matrix `A` the pair `A`, `Aᴴ` gives a diagonal form.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {K : Type*} [Field K] {ι n : Type*} [Fintype ι] [Fintype n]
  [DecidableEq n]

/-! ### Schur's theorem -/

/-- Conjugation by a pair of mutually inverse matrices preserves the characteristic polynomial. -/
private theorem charpoly_mul_mul_of_mul_eq_one {S S' : Matrix n n K} (hS : S' * S = 1)
    (M : Matrix n n K) : (S' * M * S).charpoly = M.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, mul_eq_one_comm.mp hS, Matrix.one_mul]

open scoped ComplexOrder in
/-- Simultaneous unitary triangularisation of a commuting pair: a QR factorization turns the
similarity of `IsEigenvalueListing.exists_isUpperTriangular_inv_mul_mul_of_commute` into a
unitary one and keeps the diagonals. -/
private theorem exists_schur_pair [LinearOrder n] {A B : Matrix n n 𝕜} {a : n → 𝕜}
    (hAB : Commute A B) (ha : IsEigenvalueListing A a) (hB : B.charpoly.Splits) :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ (Uᴴ * A * U).IsUpperTriangular ∧
      (∀ i, (Uᴴ * A * U) i i = a i) ∧ (Uᴴ * B * U).IsUpperTriangular := by
  obtain ⟨S, hdet, hTA, hdA, hTB⟩ := ha.exists_isUpperTriangular_inv_mul_mul_of_commute hAB hB
  have hS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hdet
  have hS' : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinj : Function.Injective S.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (IsUnit.of_mul_eq_one _ hS')
  obtain ⟨Q, R, hQR, hR⟩ := exists_isQR_of_injective hinj
  have hRne : ∀ i, R i i ≠ 0 := fun i => (hR i).ne'
  have hRinv : R⁻¹ = S⁻¹ * Q := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, ← hQR.eq_mul, hS]
  have hQH : Qᴴ = R * S⁻¹ := by
    rw [← hQR.conjTranspose_mul_eq, Matrix.mul_assoc, hS', Matrix.mul_one]
  have key : ∀ M : Matrix n n 𝕜, Qᴴ * M * Q = R * (S⁻¹ * M * S) * R⁻¹ := by
    intro M
    rw [hQH, hRinv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S S⁻¹, hS', Matrix.one_mul]
  have hRtri := hQR.isUpperTriangular
  refine ⟨Q, hQR.hasOrthonormalCols, ?_, fun i => ?_, ?_⟩
  · rw [key]
    exact (hRtri.mul hTA).mul hRtri.inv
  · rw [key, Matrix.IsUpperTriangular.mul_apply_self (hRtri.mul hTA) hRtri.inv,
      hRtri.mul_apply_self hTA, hdA, hRtri.inv_apply_self hRne, mul_right_comm,
      mul_inv_cancel₀ (hRne i), one_mul]
  · rw [key]
    exact (hRtri.mul hTB).mul hRtri.inv

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
  obtain ⟨U, hU, hT, hdiag, -⟩ := exists_schur_pair (Commute.refl A) hd hd.splits_charpoly
  exact ⟨U, hU, hT, hdiag⟩

/-- **Schur's theorem.** Every square complex matrix is unitarily similar to an upper triangular
matrix. [HornJohnson2013, Theorem 2.3.1]; [GolubVanLoan2013, Theorem 7.1.3].
Port of `NLAlib.exists_unitary_schur_triangularization`. -/
theorem exists_hasOrthonormalCols_isUpperTriangular [LinearOrder n] (A : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧ (Uᴴ * A * U).IsUpperTriangular := by
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing A
  obtain ⟨U, hU, hT, -⟩ := hd.exists_hasOrthonormalCols_isUpperTriangular
  exact ⟨U, hU, hT⟩

/-- The diagonal of a triangular matrix unitarily similar to `A` lists the eigenvalues of `A`. -/
theorem isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul [LinearOrder n]
    {A U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) (hT : (Uᴴ * A * U).IsUpperTriangular) :
    IsEigenvalueListing A fun i => (Uᴴ * A * U) i i := by
  rw [isEigenvalueListing_iff, ← Matrix.charpoly_of_isUpperTriangular _ hT,
    charpoly_mul_mul_of_mul_eq_one hU.conjTranspose_mul_self]

/-- **Triangularisation with small off-diagonal part.** For every `ε > 0` a complex matrix is
similar to an upper triangular matrix whose off-diagonal entries are smaller than `ε`. This is
the step from the spectral radius to a norm in which the matrix is almost as small.
[HornJohnson2013, Lemma 5.6.10].
Port of `NLAlib.exists_similarity_upper_triangular_small_entries`. -/
theorem exists_isUpperTriangular_inv_mul_mul_norm_apply_lt [LinearOrder n] (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ (S⁻¹ * A * S).IsUpperTriangular ∧
      ∀ i j, i ≠ j → ‖(S⁻¹ * A * S) i j‖ < ε := by
  obtain ⟨U, hU, hT⟩ := exists_hasOrthonormalCols_isUpperTriangular A
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = frobNorm (Uᴴ * A * U) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ frobNorm_nonneg _
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (1 + M + ε) := ⟨_, rfl⟩
  have hden : 0 < 1 + M + ε := by positivity
  have hδ : 0 < δ := hδdef ▸ div_pos hε hden
  have hδ1 : δ ≤ 1 := hδdef ▸ (div_le_one hden).mpr (by linarith)
  have hMδ : M * δ < ε := by
    rw [hδdef, ← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith
  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  let r : n → ℕ := fun i => (Finset.univ.filter (· < i)).card
  have hr : ∀ i j, i < j → r i < r j := fun i j hij =>
    Finset.card_lt_card (Finset.ssubset_iff_of_subset
      (Finset.monotone_filter_right _ fun k _ hk => hk.trans hij) |>.mpr
      ⟨i, by simpa using hij, by simp⟩)
  have hHS : Matrix.diagonal (fun i => ((δ : ℂ) ^ r i)⁻¹) * Uᴴ *
      (U * Matrix.diagonal fun i => (δ : ℂ) ^ r i) = 1 := by
    rw [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left, Matrix.diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (pow_ne_zero _ hδC), Matrix.diagonal_one]
  have hentry : ∀ i j, ((U * Matrix.diagonal fun i => (δ : ℂ) ^ r i)⁻¹ * A *
      (U * Matrix.diagonal fun i => (δ : ℂ) ^ r i)) i j =
        ((δ : ℂ) ^ r i)⁻¹ * (Uᴴ * A * U) i j * (δ : ℂ) ^ r j := by
    intro i j
    have hmat : (U * Matrix.diagonal fun i => (δ : ℂ) ^ r i)⁻¹ * A *
        (U * Matrix.diagonal fun i => (δ : ℂ) ^ r i) =
        Matrix.diagonal (fun i => ((δ : ℂ) ^ r i)⁻¹) * (Uᴴ * A * U) *
          Matrix.diagonal fun i => (δ : ℂ) ^ r i := by
      rw [Matrix.inv_eq_left_inv hHS]
      simp only [Matrix.mul_assoc]
    rw [hmat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨U * Matrix.diagonal fun i => (δ : ℂ) ^ r i, Matrix.isUnit_det_of_left_inverse hHS,
    fun i j hji => ?_, fun i j hij => ?_⟩
  · rw [hentry, hT hji, mul_zero, zero_mul]
  · rw [hentry]
    rcases lt_or_gt_of_ne hij with h | h
    · have hnorm : ‖((δ : ℂ) ^ r i)⁻¹ * (Uᴴ * A * U) i j * (δ : ℂ) ^ r j‖ =
          ‖(Uᴴ * A * U) i j‖ * δ ^ (r j - r i) := by
        rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg hδ.le, pow_sub₀ δ hδ.ne' (hr i j h).le]
        ring
      rw [hnorm]
      calc ‖(Uᴴ * A * U) i j‖ * δ ^ (r j - r i) ≤ ‖(Uᴴ * A * U) i j‖ * δ :=
            mul_le_mul_of_nonneg_left
              (pow_le_of_le_one hδ.le hδ1 (Nat.sub_ne_zero_of_lt (hr i j h))) (norm_nonneg _)
        _ ≤ M * δ :=
            mul_le_mul_of_nonneg_right (hM ▸ norm_apply_le_frobNorm (Uᴴ * A * U) i j) hδ.le
        _ < ε := hMδ
    · rw [hT h, mul_zero, zero_mul, norm_zero]
      exact hε

/-! ### Schur's inequality -/

/-- The squared Frobenius norm is the diagonal part plus the off-diagonal part. -/
private theorem frobNorm_sq_eq_sum_diag_add (T : Matrix n n 𝕜) :
    frobNorm T ^ 2 = ∑ i, ‖T i i‖ ^ 2 + ∑ i, ∑ j ∈ Finset.univ.erase i, ‖T i j‖ ^ 2 := by
  rw [frobNorm_sq_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    (Finset.add_sum_erase _ (fun j => ‖T i j‖ ^ 2) (Finset.mem_univ i)).symm

/-- A unitary similarity that puts a listing of the eigenvalues on the diagonal, and that
diagonalises the matrix if it is normal. -/
private theorem exists_hasOrthonormalCols_diag_eq {A : Matrix n n 𝕜} {d : ι → 𝕜}
    (hd : IsEigenvalueListing A d) :
    ∃ (U : Matrix n n 𝕜) (e : n ≃ ι), HasOrthonormalCols U ∧
      (∀ i, (Uᴴ * A * U) i i = d (e i)) ∧
      (IsStarNormal A → ∀ i j, i ≠ j → (Uᴴ * A * U) i j = 0) := by
  classical
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  let e : n ≃ ι := Fintype.equivOfCardEq hd.card_eq.symm
  by_cases hN : IsStarNormal A
  · have hsplit : Aᴴ.charpoly.Splits := by
      have h : Aᴴ.charpoly = A.charpoly.map (starRingEnd 𝕜) := by
        rw [← Matrix.charpoly_transpose A, ← Matrix.charpoly_map]
        rfl
      rw [h]
      exact hd.splits_charpoly.map _
    obtain ⟨U, hU, hT, hdiag, hT'⟩ := exists_schur_pair
      (show Commute A Aᴴ from (hN.star_comm_self).symm) (hd.comp_equiv e) hsplit
    refine ⟨U, e, hU, hdiag, fun _ i j hij => ?_⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have h0 : (Uᴴ * Aᴴ * U) j i = 0 := hT' h
      have h1 : Uᴴ * Aᴴ * U = (Uᴴ * A * U)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      rwa [h1, Matrix.conjTranspose_apply, star_eq_zero] at h0
    · exact hT h
  · obtain ⟨U, hU, -, hdiag⟩ := (hd.comp_equiv e).exists_hasOrthonormalCols_isUpperTriangular
    exact ⟨U, e, hU, hdiag, fun h => absurd h hN⟩

/-- **Schur's inequality**: the sum of the squared moduli of the eigenvalues is at most the
squared Frobenius norm. [HornJohnson2013, §2.3].
Port of `NLAlib.sum_norm_sq_schur_diagonal_le_frobSq`. -/
theorem IsEigenvalueListing.sum_norm_sq_le_frobNorm_sq {A : Matrix n n 𝕜} {d : ι → 𝕜}
    (hd : IsEigenvalueListing A d) : ∑ i, ‖d i‖ ^ 2 ≤ frobNorm A ^ 2 := by
  obtain ⟨U, e, hU, hdiag, -⟩ := exists_hasOrthonormalCols_diag_eq hd
  rw [← hU.conjTranspose.frobNorm_mul_left A, ← hU.frobNorm_mul_right (Uᴴ * A),
    frobNorm_sq_eq_sum_diag_add, ← e.sum_comp]
  simp only [hdiag]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- **Equality in Schur's inequality holds exactly for normal matrices.**
[HornJohnson2013, Theorem 2.5.3].
Port of `NLAlib.sum_norm_sq_characteristic_eq_frobSq_iff_normal`. -/
theorem IsEigenvalueListing.sum_norm_sq_eq_frobNorm_sq_iff {A : Matrix n n 𝕜} {d : ι → 𝕜}
    (hd : IsEigenvalueListing A d) : ∑ i, ‖d i‖ ^ 2 = frobNorm A ^ 2 ↔ IsStarNormal A := by
  obtain ⟨U, e, hU, hdiag, hnormal⟩ := exists_hasOrthonormalCols_diag_eq hd
  have hsum : ∑ i, ‖d i‖ ^ 2 = ∑ i, ‖(Uᴴ * A * U) i i‖ ^ 2 := by
    rw [← e.sum_comp]
    simp only [hdiag]
  rw [← hU.conjTranspose.frobNorm_mul_left A, ← hU.frobNorm_mul_right (Uᴴ * A),
    frobNorm_sq_eq_sum_diag_add, hsum, left_eq_add]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hoff : ∀ i j, i ≠ j → (Uᴴ * A * U) i j = 0 := by
      intro i j hij
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg ‖(Uᴴ * A * U) i j‖).mp h i (Finset.mem_univ i)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        sq_nonneg ‖(Uᴴ * A * U) i j‖).mp h1 j (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    obtain ⟨t, hT⟩ : ∃ t : n → 𝕜, Uᴴ * A * U = Matrix.diagonal t := by
      refine ⟨fun i => (Uᴴ * A * U) i i, Matrix.ext fun i j => ?_⟩
      by_cases hij : i = j
      · rw [hij, Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
    have hA : A = U * Matrix.diagonal t * Uᴴ := by
      rw [← hT]
      simp only [Matrix.mul_assoc, hU.mul_conjTranspose_self, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hU.mul_conjTranspose_self, Matrix.one_mul]
    refine ⟨?_⟩
    rw [Commute, SemiconjBy, Matrix.star_eq_conjTranspose, hA]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    rw [hU.conjTranspose_mul_cancel_left, hU.conjTranspose_mul_cancel_left,
      ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
      ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]
  · exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => by
      rw [hnormal h i j (Finset.ne_of_mem_erase hj).symm, norm_zero, zero_pow two_ne_zero]

/-! ### Commuting matrices and density -/

/-- **Eigenvalues of commuting matrices pair up**: commuting complex matrices have listings of
their eigenvalues whose sums and products list the eigenvalues of `A + B` and `A * B`.
[HornJohnson2013, Theorem 2.4.8.1].
Port of `NLAlib.exists_paired_charpoly_factors_add_mul_of_commute`. -/
theorem exists_isEigenvalueListing_add_mul_of_commute {A B : Matrix n n ℂ} (h : Commute A B) :
    ∃ a b : n → ℂ, IsEigenvalueListing A a ∧ IsEigenvalueListing B b ∧
      IsEigenvalueListing (A + B) (fun i => a i + b i) ∧
      IsEigenvalueListing (A * B) (fun i => a i * b i) := by
  classical
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨a, ha⟩ := exists_isEigenvalueListing A
  obtain ⟨S, hdet, hTA, hdA, hTB⟩ :=
    ha.exists_isUpperTriangular_inv_mul_mul_of_commute h (IsAlgClosed.splits _)
  have hS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hdet
  refine ⟨a, fun i => (S⁻¹ * B * S) i i, ha, ?_, ?_, ?_⟩
  · rw [isEigenvalueListing_iff, ← charpoly_mul_mul_of_mul_eq_one hS,
      Matrix.charpoly_of_isUpperTriangular _ hTB]
  · have hadd : S⁻¹ * (A + B) * S = S⁻¹ * A * S + S⁻¹ * B * S := by
      rw [Matrix.mul_add, Matrix.add_mul]
    rw [isEigenvalueListing_iff, ← charpoly_mul_mul_of_mul_eq_one hS, hadd,
      Matrix.charpoly_of_isUpperTriangular _ (hTA.add hTB)]
    simp only [Matrix.add_apply, hdA]
  · have hmul : S⁻¹ * (A * B) * S = S⁻¹ * A * S * (S⁻¹ * B * S) := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
    rw [isEigenvalueListing_iff, ← charpoly_mul_mul_of_mul_eq_one hS, hmul,
      Matrix.charpoly_of_isUpperTriangular _ (hTA.mul hTB)]
    simp only [Matrix.IsUpperTriangular.mul_apply_self hTA hTB, hdA]

/-- Along the segment from `A` to a matrix `D` with separable characteristic polynomial, the
characteristic polynomial is separable for all but finitely many parameters: the resultant of the
characteristic polynomial and its derivative is a nonzero polynomial in the parameter. -/
private theorem finite_setOf_not_separable_charpoly (A D : Matrix n n 𝕜)
    (hD : D.charpoly.Separable) : {t : 𝕜 | ¬(A + t • (D - A)).charpoly.Separable}.Finite := by
  let P : 𝕜[X][X] := (A.map C + (X : 𝕜[X]) • (D - A).map C).charpoly
  let r : 𝕜[X] := P.resultant P.derivative (Fintype.card n) (Fintype.card n - 1)
  have hmap : ∀ t : 𝕜, P.map (Polynomial.evalRingHom t) = (A + t • (D - A)).charpoly := by
    intro t
    rw [← Matrix.charpoly_map]
    congr 1
    ext i j
    simp [Matrix.map_apply]
  have hsep : ∀ t : 𝕜, (A + t • (D - A)).charpoly.Separable ↔ r.eval t ≠ 0 := by
    intro t
    have h := Polynomial.resultant_map_map P P.derivative (Fintype.card n) (Fintype.card n - 1)
      (Polynomial.evalRingHom t)
    rw [← Polynomial.derivative_map, hmap] at h
    have h' : r.eval t = (A + t • (D - A)).charpoly.resultant
        (A + t • (D - A)).charpoly.derivative := by
      simpa only [r, Polynomial.coe_evalRingHom, Polynomial.natDegree_derivative,
        Matrix.charpoly_natDegree_eq_dim] using h.symm
    rw [h', Polynomial.separable_def,
      ← Polynomial.isUnit_resultant_iff_isCoprime (A + t • (D - A)).charpoly_monic,
      isUnit_iff_ne_zero]
  have hr : r ≠ 0 := by
    intro h0
    have h1 := (hsep 1).mp (by simpa using hD)
    rw [h0, Polynomial.eval_zero] at h1
    exact h1 rfl
  exact (Polynomial.finite_setOfPred_isRoot hr).subset fun t ht =>
    not_ne_iff.mp ((hsep t).not.mp ht)

/-- **Matrices with distinct eigenvalues are dense.**
[HornJohnson2013, Theorem 2.4.7.1]. Port of `NLAlib.dense_separable_charpoly`. -/
theorem dense_setOf_separable_charpoly : Dense {A : Matrix n n 𝕜 | A.charpoly.Separable} := by
  have hD : (Matrix.diagonal fun i : n => ((Fintype.equivFin n i : ℕ) : 𝕜)).charpoly.Separable := by
    rw [Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr fun i j hij =>
      (Fintype.equivFin n).injective (Fin.ext (Nat.cast_injective hij))
  intro A
  refine mem_closure_iff.mpr fun V hV hAV => ?_
  have hg : Continuous fun t : 𝕜 =>
      A + t • (Matrix.diagonal (fun i : n => ((Fintype.equivFin n i : ℕ) : 𝕜)) - A) := by
    fun_prop
  have hpre : (fun t : 𝕜 =>
      A + t • (Matrix.diagonal (fun i : n => ((Fintype.equivFin n i : ℕ) : 𝕜)) - A)) ⁻¹' V ∈
      nhds (0 : 𝕜) :=
    hg.continuousAt.preimage_mem_nhds (hV.mem_nhds (by simpa using hAV))
  obtain ⟨t, ht, hgood⟩ := (infinite_of_mem_nhds (0 : 𝕜) hpre).exists_notMem_finite
    (finite_setOf_not_separable_charpoly A _ hD)
  exact ⟨_, ht, not_not.mp hgood⟩

end NLAlib
