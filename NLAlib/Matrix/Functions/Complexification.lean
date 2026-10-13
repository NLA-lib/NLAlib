/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.RCLike.ToComplex
public import NLAlib.Matrix.Functions.Exponential

/-!
# Transfer from `𝕜` to `ℂ`

Many results on functions of Hermitian matrices are theorems about complex C⋆-algebras. To state
them over an arbitrary `RCLike` field (in particular over `ℝ`), a matrix over `𝕜` is sent to the
complex matrix with the same real and imaginary parts, `NLAlib.complexify A`. The map is an
injective star algebra homomorphism over `ℝ` compatible with traces, the Loewner order, the
functional calculus and the exponential, so a statement about Hermitian matrices that holds over
`ℂ` holds over `𝕜`.

## Main definitions

* `NLAlib.complexify`: entrywise embedding of `Matrix m n 𝕜` into `Matrix m n ℂ`.

## Main results

* `NLAlib.complexify_mul`, `NLAlib.complexify_conjTranspose`: it is a star-ring homomorphism.
* `NLAlib.re_trace_complexify`, `NLAlib.complexify_le_complexify_iff`.
* `NLAlib.complexify_cfc`, `NLAlib.complexify_exp`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*}

/-- The **complexification** of a matrix over an `RCLike` field: the complex matrix with the same
real and imaginary parts. Over `ℂ` it is the identity, over `ℝ` the inclusion.
Port of `NLAlib.realMatrixComplexification`, there for real matrices. -/
noncomputable def complexify (A : Matrix m n 𝕜) : Matrix m n ℂ :=
  A.map RCLike.toComplex

/-- Entries of the complexification. -/
@[simp]
theorem complexify_apply (A : Matrix m n 𝕜) (i : m) (j : n) :
    complexify A i j = RCLike.toComplex (A i j) :=
  rfl

/-- On square matrices the complexification is the star algebra homomorphism induced by
`RCLike.toComplex`. -/
theorem complexify_eq_mapMatrix [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) :
    complexify A = (RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toAlgHom.mapMatrix A := by
  rfl

/-- The complexification is injective. -/
theorem complexify_injective : Function.Injective (complexify : Matrix m n 𝕜 → Matrix m n ℂ) := by
  exact Matrix.map_injective RCLike.toComplex_injective

/-- The complexification is additive. -/
@[simp]
theorem complexify_add (A B : Matrix m n 𝕜) : complexify (A + B) = complexify A + complexify B := by
  exact Matrix.map_add _ (map_add _) A B

/-- The complexification commutes with subtraction. -/
@[simp]
theorem complexify_sub (A B : Matrix m n 𝕜) : complexify (A - B) = complexify A - complexify B := by
  exact Matrix.map_sub _ (map_sub _) A B

/-- The complexification commutes with real scalar multiplication. -/
@[simp]
theorem complexify_real_smul (c : ℝ) (A : Matrix m n 𝕜) :
    complexify (c • A) = c • complexify A := by
  ext i j
  rw [Matrix.smul_apply, complexify_apply, complexify_apply, Matrix.smul_apply]
  exact (RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toAlgHom.map_smul_of_tower c (A i j)

/-- The complexification of zero. -/
@[simp]
theorem complexify_zero : complexify (0 : Matrix m n 𝕜) = 0 := by
  exact Matrix.map_zero _ (map_zero _)

/-- The complexification of the identity. -/
@[simp]
theorem complexify_one [DecidableEq n] : complexify (1 : Matrix n n 𝕜) = 1 := by
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- The complexification is multiplicative. -/
@[simp]
theorem complexify_mul [Fintype m] (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j
  simp only [complexify_apply, Matrix.mul_apply, map_sum, map_mul]

/-- The complexification commutes with natural powers. -/
@[simp]
theorem complexify_pow [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k := by
  rw [complexify_eq_mapMatrix, complexify_eq_mapMatrix, map_pow]

/-- The complexification commutes with the conjugate transpose. -/
@[simp]
theorem complexify_conjTranspose (A : Matrix m n 𝕜) : complexify Aᴴ = (complexify A)ᴴ := by
  ext i j
  rw [complexify_apply, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, complexify_apply,
    map_star]

/-- The complexification of a diagonal matrix. -/
@[simp]
theorem complexify_diagonal [DecidableEq n] (d : n → 𝕜) :
    complexify (Matrix.diagonal d) = Matrix.diagonal fun i => RCLike.toComplex (d i) := by
  exact Matrix.diagonal_map (map_zero _)

/-- The complexification of a matrix with orthonormal columns has orthonormal columns. -/
theorem HasOrthonormalCols.complexify [Fintype m] [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) : HasOrthonormalCols (complexify Q) := by
  rw [HasOrthonormalCols, ← complexify_conjTranspose, ← complexify_mul, hQ.conjTranspose_mul_self,
    complexify_one]

/-- The complexification of a Hermitian matrix is Hermitian, and conversely. -/
@[simp]
theorem isHermitian_complexify_iff {A : Matrix n n 𝕜} :
    (complexify A).IsHermitian ↔ A.IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_conjTranspose, complexify_injective.eq_iff]
  exact Iff.rfl

/-- The complexification preserves the real part of the trace. -/
@[simp]
theorem re_trace_complexify [Fintype n] (A : Matrix n n 𝕜) :
    (complexify A).trace.re = RCLike.re A.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, complexify_apply, Complex.re_sum, map_sum,
    RCLike.re_toComplex]

/-- The complexification of a unitary diagonalisation with real diagonal. -/
private theorem complexify_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r]
    [DecidableEq r] (U : Matrix n r 𝕜) (d : r → ℝ) :
    complexify (U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) =
      complexify U * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * (complexify U)ᴴ := by
  simp only [complexify_mul, complexify_conjTranspose, complexify_diagonal,
    RCLike.toComplex_ofReal]

/-- The sorted eigenvalues of the complexification of a Hermitian matrix. -/
private theorem eigenvalue_complexify_of_isHermitian [Fintype n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) : eigenvalue (complexify A) k = eigenvalue A k := by
  classical
  rcases le_or_gt (Fintype.card n) k with hk | hk
  · rw [eigenvalue_of_card_le _ hk, eigenvalue_of_card_le _ hk]
  · obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
    have hc : complexify A = complexify U *
        (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : ℂ)) *
          (complexify U)ᴴ := by
      conv_lhs => rw [hAU]
      exact complexify_mul_diagonal_mul_conjTranspose U _
    exact eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU.complexify rfl
      hA.antitone_eigenvalue_coe hc ⟨k, hk⟩

/-- The complexification preserves and reflects positive semidefiniteness. -/
@[simp]
theorem posSemidef_complexify_iff [Finite n] {A : Matrix n n 𝕜} :
    (complexify A).PosSemidef ↔ A.PosSemidef := by
  cases nonempty_fintype n
  by_cases hA : A.IsHermitian
  · rw [(isHermitian_complexify_iff.mpr hA).posSemidef_iff_eigenvalue_nonneg,
      hA.posSemidef_iff_eigenvalue_nonneg]
    simp only [eigenvalue_complexify_of_isHermitian hA]
  · exact ⟨fun h => absurd (isHermitian_complexify_iff.mp h.isHermitian) hA,
      fun h => absurd h.isHermitian hA⟩

/-- The complexification preserves and reflects positive definiteness. -/
@[simp]
theorem posDef_complexify_iff [Finite n] {A : Matrix n n 𝕜} :
    (complexify A).PosDef ↔ A.PosDef := by
  cases nonempty_fintype n
  by_cases hA : A.IsHermitian
  · rw [(isHermitian_complexify_iff.mpr hA).posDef_iff_eigenvalue_pos,
      hA.posDef_iff_eigenvalue_pos]
    simp only [eigenvalue_complexify_of_isHermitian hA]
  · exact ⟨fun h => absurd (isHermitian_complexify_iff.mp h.isHermitian) hA,
      fun h => absurd h.isHermitian hA⟩

/-- **The complexification preserves and reflects the Loewner order.** -/
@[simp]
theorem complexify_le_complexify_iff [Finite n] {A B : Matrix n n 𝕜} :
    complexify A ≤ complexify B ↔ A ≤ B := by
  rw [Matrix.le_iff, Matrix.le_iff, ← complexify_sub, posSemidef_complexify_iff]

/-- The complexification preserves the real spectrum. -/
@[simp]
theorem spectrum_complexify [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) :
    spectrum ℝ (complexify A) = spectrum ℝ A := by
  have hunit : ∀ M : Matrix n n 𝕜, IsUnit (complexify M) ↔ IsUnit M := by
    intro M
    have hdet : (complexify M).det = RCLike.toComplex M.det :=
      (RingHom.map_det (RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toRingHom M).symm
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      isUnit_iff_ne_zero, hdet, ne_eq, ne_eq, map_eq_zero_iff _ RCLike.toComplex_injective]
  ext r
  rw [spectrum.mem_iff, spectrum.mem_iff, ← hunit, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, complexify_sub, complexify_real_smul, complexify_one]

/-- The complexification preserves the sorted eigenvalues. -/
@[simp]
theorem eigenvalue_complexify [Fintype n] (A : Matrix n n 𝕜) (k : ℕ) :
    eigenvalue (complexify A) k = eigenvalue A k := by
  by_cases hA : A.IsHermitian
  · exact eigenvalue_complexify_of_isHermitian hA k
  · rw [eigenvalue_of_not_isHermitian hA,
      eigenvalue_of_not_isHermitian (mt isHermitian_complexify_iff.mp hA)]

/-- The complexification preserves the spectral norm. -/
@[simp]
theorem specNorm_complexify [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    specNorm (complexify A) = specNorm A := by
  classical
  refine (sq_eq_sq₀ (specNorm_nonneg _) (specNorm_nonneg _)).mp ?_
  have hP := Matrix.posSemidef_conjTranspose_mul_self A
  rw [← specNorm_conjTranspose_mul_self, ← specNorm_conjTranspose_mul_self,
    ← complexify_conjTranspose, ← complexify_mul,
    (posSemidef_complexify_iff.mpr hP).specNorm_eq_eigenvalue_zero,
    hP.specNorm_eq_eigenvalue_zero, eigenvalue_complexify]

/-- **The complexification commutes with the functional calculus** of a Hermitian matrix. -/
theorem complexify_cfc [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : complexify (cfc f A) = cfc f (complexify A) := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  have hc : complexify A = complexify U *
      (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : ℂ)) *
        (complexify U)ᴴ := by
    conv_lhs => rw [hAU]
    exact complexify_mul_diagonal_mul_conjTranspose U _
  rw [cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAU f,
    cfc_eq_mul_diagonal_mul_conjTranspose hU.complexify hr hc f]
  exact complexify_mul_diagonal_mul_conjTranspose U _

open scoped Classical in
/-- The complexification commutes with the square root. -/
theorem complexify_sqrt [Fintype n] (A : Matrix n n 𝕜) :
    complexify (CFC.sqrt A) = CFC.sqrt (complexify A) := by
  by_cases hA : A.PosSemidef
  · have h0 : (0 : Matrix n n 𝕜) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
    refine (CFC.sqrt_unique ?_ ?_).symm
    · rw [← complexify_mul, CFC.sqrt_mul_sqrt_self A h0]
    · exact Matrix.nonneg_iff_posSemidef.mpr
        (posSemidef_complexify_iff.mpr (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)))
  · have hA' : ¬ (0 : Matrix n n 𝕜) ≤ A := mt Matrix.nonneg_iff_posSemidef.mp hA
    have hc : ¬ (0 : Matrix n n ℂ) ≤ complexify A :=
      mt (fun h => posSemidef_complexify_iff.mp (Matrix.nonneg_iff_posSemidef.mp h)) hA
    rw [CFC.sqrt_of_not_nonneg hA', CFC.sqrt_of_not_nonneg hc, complexify_zero]

/-- The complexification commutes with real powers. -/
theorem complexify_rpow [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) (r : ℝ) :
    complexify (A ^ r) = complexify A ^ r := by
  by_cases hA : A.PosSemidef
  · rw [CFC.rpow_eq_cfc_real (Matrix.nonneg_iff_posSemidef.mpr hA),
      CFC.rpow_eq_cfc_real
        (Matrix.nonneg_iff_posSemidef.mpr (posSemidef_complexify_iff.mpr hA))]
    exact complexify_cfc hA.isHermitian _
  · have hA' : ¬ (0 : Matrix n n 𝕜) ≤ A := mt Matrix.nonneg_iff_posSemidef.mp hA
    have hc : ¬ (0 : Matrix n n ℂ) ≤ complexify A :=
      mt (fun h => posSemidef_complexify_iff.mp (Matrix.nonneg_iff_posSemidef.mp h)) hA
    rw [CFC.rpow_def, CFC.rpow_def, cfc_apply_of_not_predicate A hA',
      cfc_apply_of_not_predicate (complexify A) hc, complexify_zero]

/-- The complexification commutes with the exponential. -/
theorem complexify_exp [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) :
    complexify (exp A) = exp (complexify A) := by
  have hf : Continuous ((RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toRingHom.mapMatrix :
      Matrix n n 𝕜 →+* Matrix n n ℂ) :=
    continuous_id.matrix_map RCLike.continuous_toComplex
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp ((RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toRingHom.mapMatrix) hf A

end NLAlib
