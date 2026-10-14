/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import NLAlib.Matrix.Spectral.EigenvectorPairing
public import NLAlib.Matrix.Spectral.Schur
public import NLAlib.Matrix.Majorization.Schur

/-!
# The Hermitian part and the real parts of the eigenvalues

The Hermitian part of a square matrix is `NLAlib.hermitianPart A = (A + Aᴴ) / 2`, Mathlib's
`selfAdjointPart ℝ A` as a matrix. The real parts of the eigenvalues of a complex matrix are
majorized by the eigenvalues of its Hermitian part (Ky Fan), so they lie between its extreme
eigenvalues (Bendixson).

## Main definitions

* `NLAlib.hermitianPart`: `(2⁻¹ : ℝ) • (A + Aᴴ)`.

## Main results

* `NLAlib.majorized_re_of_isEigenvalueListing`: Ky Fan's majorization.
* `NLAlib.re_le_eigenvalue_zero_hermitianPart`, `NLAlib.eigenvalue_hermitianPart_le_re`:
  Bendixson's bounds.
* `NLAlib.det_ne_zero_of_posDef_hermitianPart`: a matrix with positive definite Hermitian part is
  invertible.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-- The **Hermitian part** of a square matrix, `(A + Aᴴ) / 2`.
[HornJohnson2013, §4.1.2]. -/
noncomputable def hermitianPart (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (2⁻¹ : ℝ) • (A + Aᴴ)

/-- The Hermitian part is Mathlib's `selfAdjointPart`. -/
theorem hermitianPart_eq_selfAdjointPart (A : Matrix n n 𝕜) :
    hermitianPart A = (selfAdjointPart ℝ A : Matrix n n 𝕜) := by
  rw [selfAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose, hermitianPart]

/-- The Hermitian part is Hermitian. -/
theorem isHermitian_hermitianPart (A : Matrix n n 𝕜) : (hermitianPart A).IsHermitian := by
  rw [Matrix.IsHermitian, hermitianPart, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

/-- A Hermitian matrix is its own Hermitian part. -/
theorem _root_.Matrix.IsHermitian.hermitianPart_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hermitianPart A = A := by
  rw [hermitianPart, hA.eq, ← two_smul ℝ A, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

variable [Fintype n]

/-- The quadratic form of the Hermitian part is the real part of the quadratic form. -/
theorem re_quadForm_hermitianPart (A : Matrix n n 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm (hermitianPart A) x) = RCLike.re (quadForm A x) := by
  rw [hermitianPart, RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left,
    quadForm_add_left, ← star_quadForm, RCLike.re_ofReal_mul, map_add, RCLike.star_def,
    RCLike.conj_re]
  ring

/-- The Hermitian part commutes with unitary conjugation.
Port of `NLAlib.selfAdjointPart_mul_mul_conjTranspose`. -/
theorem hermitianPart_mul_mul_conjTranspose (U A : Matrix n n 𝕜) :
    hermitianPart (U * A * Uᴴ) = U * hermitianPart A * Uᴴ := by
  simp only [hermitianPart, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

variable [DecidableEq n]

/-- **The real parts of the eigenvalues are majorized by the eigenvalues of the Hermitian
part** (Ky Fan). [HornJohnson1991, §3.3]; [Bhatia1997, Proposition III.5.3].
Port of `NLAlib.majorized_real_parts_eigenvalues_selfAdjointPart`.
Result: real-part-majorization -/
theorem majorized_re_of_isEigenvalueListing {A : Matrix n n ℂ} {z : n → ℂ} {x : n → ℝ}
    (hz : IsEigenvalueListing A z)
    (hx : IsEigenvalueListing (hermitianPart A) fun i => ((x i : ℝ) : ℂ)) :
    Majorized (fun i => (z i).re) x := by
  classical
  let _ : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨U, hU, -, hdiag⟩ := hz.exists_hasOrthonormalCols_isUpperTriangular
  have hH : hermitianPart (Uᴴ * A * U) = Uᴴ * hermitianPart A * U := by
    have h := hermitianPart_mul_mul_conjTranspose Uᴴ A
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hherm := isHermitian_hermitianPart (Uᴴ * A * U)
  have hre : ∀ i, RCLike.re (hermitianPart (Uᴴ * A * U) i i) = (z i).re := by
    intro i
    rw [hermitianPart, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, hdiag,
      RCLike.re_to_complex, Complex.real_smul, Complex.re_ofReal_mul, Complex.add_re,
      Complex.star_def, Complex.conj_re]
    ring
  have hmaj := hherm.majorized_re_diag_eigenvalues
  simp only [hre] at hmaj
  have hlist : IsEigenvalueListing (hermitianPart A) fun i => ((hherm.eigenvalues i : ℝ) : ℂ) := by
    have hchar : (hermitianPart (Uᴴ * A * U)).charpoly = (hermitianPart A).charpoly := by
      rw [hH, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU.mul_conjTranspose_self,
        Matrix.one_mul]
    exact hchar.symm.trans hherm.charpoly_eq
  obtain ⟨e, he⟩ := hlist.exists_equiv_eq hx
  have heq : hherm.eigenvalues = x ∘ e := funext fun i => Complex.ofReal_injective (congrFun he i)
  rw [heq] at hmaj
  exact hmaj.trans (majorized_comp_equiv x e)

/-- An eigenvalue is the value of the quadratic form at a unit eigenvector. -/
private theorem exists_re_quadForm_eq_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ v : n → 𝕜, 0 < ‖WithLp.toLp 2 v‖ ^ 2 ∧
      RCLike.re (quadForm A v) = RCLike.re μ * ‖WithLp.toLp 2 v‖ ^ 2 := by
  obtain ⟨v, hv, hAv⟩ := exists_mulVec_eq_smul_of_mem_spectrum hμ
  refine ⟨v, pow_pos (norm_pos_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hv)) 2, ?_⟩
  rw [quadForm, hAv, dotProduct_smul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
    smul_eq_mul, RCLike.re_mul_ofReal]

/-- **Bendixson's upper bound**: the real part of every eigenvalue is at most the largest
eigenvalue of the Hermitian part. [HornJohnson2013, §5.6].
Port of `NLAlib.real_part_eigenvalue_mem_Icc_selfAdjointPart`, upper half. -/
theorem re_le_eigenvalue_zero_hermitianPart {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : RCLike.re μ ≤ eigenvalue (hermitianPart A) 0 := by
  obtain ⟨v, hv, hq⟩ := exists_re_quadForm_eq_of_mem_spectrum hμ
  have h := (isHermitian_hermitianPart A).re_quadForm_le_eigenvalue_zero_mul v
  rw [re_quadForm_hermitianPart, hq] at h
  exact le_of_mul_le_mul_right h hv

/-- **Bendixson's lower bound**: the real part of every eigenvalue is at least the smallest
eigenvalue of the Hermitian part.
Port of `NLAlib.real_part_eigenvalue_mem_Icc_selfAdjointPart`, lower half. -/
theorem eigenvalue_hermitianPart_le_re {A : Matrix n n 𝕜} {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A)
    {j : ℕ} (hj : j + 1 = Fintype.card n) : eigenvalue (hermitianPart A) j ≤ RCLike.re μ := by
  obtain ⟨v, hv, hq⟩ := exists_re_quadForm_eq_of_mem_spectrum hμ
  have h := (isHermitian_hermitianPart A).eigenvalue_last_mul_le_re_quadForm hj v
  rw [re_quadForm_hermitianPart, hq] at h
  exact le_of_mul_le_mul_right h hv

open scoped ComplexOrder in
/-- **A matrix with positive definite Hermitian part is invertible.** A null vector `v` of `A`
would have `re (v* A v) = 0`, which is the quadratic form of the Hermitian part.
[HornJohnson2013, §7.1 context]. -/
theorem det_ne_zero_of_posDef_hermitianPart {A : Matrix n n 𝕜} (h : (hermitianPart A).PosDef) :
    A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hpos := h.re_quadForm_pos hv
  rw [re_quadForm_hermitianPart, quadForm, hAv, dotProduct_zero, map_zero] at hpos
  exact lt_irrefl 0 hpos

end NLAlib
