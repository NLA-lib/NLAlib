/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.OperatorConvex

/-!
# The matrix perspective

The perspective of `f : ℝ → ℝ` at a pair of positive definite matrices is
`A^{1/2} f(A^{-1/2} H A^{-1/2}) A^{1/2}`. The perspective of an operator convex function is
jointly operator convex (Effros; Ebadian, Nikoufar and Eshaghi Gordji), which is the source of
the joint convexity of the matrix relative entropy.

## Main definitions

* `NLAlib.matrixPerspective`: the matrix perspective of a function.

## Main results

* `NLAlib.matrixPerspective_mul_diagonal_mul_conjTranspose`: for two matrices diagonalised by
  the same frame it is the scalar perspective `a f(h / a)` of the eigenvalues.
* `NLAlib.matrixPerspective_smul_one`: the case of multiples of the identity.
* `NLAlib.matrixPerspective_smul_smul`: positive homogeneity.
* `NLAlib.OperatorConvexOn.matrixPerspective_smul_add_smul_le`: joint operator convexity.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **matrix perspective** `A^{1/2} f(A^{-1/2} H A^{-1/2}) A^{1/2}` of a function `f` at a
positive definite `A` and a Hermitian `H`; the square root and the inverse give junk values when
`A` is not positive definite. [Tropp2015, Definition 8.6.1]. Port of `NLAlib.matrixPerspective`. -/
noncomputable def matrixPerspective (f : ℝ → ℝ) (A H : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  CFC.sqrt A * cfc f ((CFC.sqrt A)⁻¹ * H * (CFC.sqrt A)⁻¹) * CFC.sqrt A

/-- The matrix perspective is Hermitian. -/
theorem isHermitian_matrixPerspective (f : ℝ → ℝ) (A H : Matrix n n 𝕜) :
    (matrixPerspective f A H).IsHermitian := by
  have hS : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hC : (cfc f ((CFC.sqrt A)⁻¹ * H * (CFC.sqrt A)⁻¹)).IsHermitian :=
    (cfc_predicate f _ : IsSelfAdjoint _)
  have h := Matrix.isHermitian_mul_mul_conjTranspose (CFC.sqrt A) hC
  rwa [hS.eq] at h

/-- The perspective at the identity is the function itself. -/
theorem matrixPerspective_one (f : ℝ → ℝ) (H : Matrix n n 𝕜) :
    matrixPerspective f 1 H = cfc f H := by
  rw [matrixPerspective, CFC.sqrt_one, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one]

omit [DecidableEq n] in
/-- A unitary conjugate of a positive diagonal matrix is positive definite. -/
private theorem posDef_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n)
    {a : r → ℝ} (ha : ∀ i, 0 < a i) :
    (U * Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * Uᴴ).PosDef := by
  classical
  have hD : (Matrix.diagonal fun i => ((a i : ℝ) : 𝕜)).PosDef :=
    Matrix.PosDef.diagonal fun i => RCLike.ofReal_pos.mpr (ha i)
  have h := hD.conjTranspose_mul_mul_same (hU.conjTranspose_of_card_eq hr.symm).mulVec_injective
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- **The perspective of two simultaneously diagonalised matrices** is the scalar perspective
`a f(h / a)` of the eigenvalues: for a frame `U` with orthonormal columns and `card r = card n`,
`ψ_f(U diag(a) Uᴴ, U diag(h) Uᴴ) = U diag(a f(h / a)) Uᴴ` when the `a i` are positive. -/
theorem matrixPerspective_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n)
    (f : ℝ → ℝ) {a : r → ℝ} (ha : ∀ i, 0 < a i) (h : r → ℝ) :
    matrixPerspective f (U * Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * Uᴴ)
        (U * Matrix.diagonal (fun i => ((h i : ℝ) : 𝕜)) * Uᴴ) =
      U * Matrix.diagonal (fun i => ((a i * f (h i / a i) : ℝ) : 𝕜)) * Uᴴ := by
  have hA := posDef_mul_diagonal_mul_conjTranspose hU hr ha
  have hmul : ∀ x y : r → ℝ, (U * Matrix.diagonal (fun i => ((x i : ℝ) : 𝕜)) * Uᴴ) *
      (U * Matrix.diagonal (fun i => ((y i : ℝ) : 𝕜)) * Uᴴ) =
        U * Matrix.diagonal (fun i => ((x i * y i : ℝ) : 𝕜)) * Uᴴ := fun x y => by
    rw [Matrix.mul_assoc _ Uᴴ, ← Matrix.mul_assoc Uᴴ, ← Matrix.mul_assoc Uᴴ,
      hU.conjTranspose_mul_self, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U,
      Matrix.diagonal_mul_diagonal]
    simp only [RCLike.ofReal_mul]
  have hsqrt : CFC.sqrt (U * Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * Uᴴ) =
      U * Matrix.diagonal (fun i => ((√(a i) : ℝ) : 𝕜)) * Uᴴ := by
    refine CFC.sqrt_unique ?_ (posDef_mul_diagonal_mul_conjTranspose hU hr fun i =>
      Real.sqrt_pos.mpr (ha i)).posSemidef.nonneg
    rw [hmul]
    simp only [Real.mul_self_sqrt (ha _).le]
  rw [matrixPerspective, hA.inv_sqrt_eq_cfc, hsqrt,
    cfc_eq_mul_diagonal_mul_conjTranspose hU hr rfl, hmul, hmul,
    cfc_eq_mul_diagonal_mul_conjTranspose hU hr rfl, hmul, hmul]
  congr 3
  funext i
  have hs := Real.mul_self_sqrt (ha i).le
  have hs0 : √(a i) ≠ 0 := (Real.sqrt_pos.mpr (ha i)).ne'
  have e : (√(a i))⁻¹ * h i * (√(a i))⁻¹ = h i / a i := by
    nth_rewrite 3 [← hs]
    field_simp
  rw [e, mul_right_comm, hs]

/-- The perspective of two multiples of the identity is the scalar perspective `a f(h / a)`. -/
theorem matrixPerspective_smul_one (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (h : ℝ) :
    matrixPerspective f (a • (1 : Matrix n n 𝕜)) (h • (1 : Matrix n n 𝕜)) =
      (a * f (h / a)) • (1 : Matrix n n 𝕜) := by
  have key : ∀ c : ℝ, c • (1 : Matrix n n 𝕜) =
      1 * Matrix.diagonal (fun _ : n => ((c : ℝ) : 𝕜)) * (1 : Matrix n n 𝕜)ᴴ := fun c => by
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.smul_one_eq_diagonal,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  rw [key a, key h, key]
  exact matrixPerspective_mul_diagonal_mul_conjTranspose hasOrthonormalCols_one rfl f
    (fun _ => ha) fun _ => h

/-- The inverse of a nonzero real multiple of a matrix, singular or not. -/
private theorem inv_real_smul {c : ℝ} (hc : c ≠ 0) (M : Matrix n n 𝕜) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul,
      Matrix.mul_nonsing_inv _ h]
  · have h' : ¬IsUnit (c • M).det := fun h' => h <| by
      refine Matrix.isUnit_det_of_right_inverse (B := c • (c • M)⁻¹) ?_
      rw [Matrix.mul_smul, ← Matrix.smul_mul, Matrix.mul_nonsing_inv _ h']
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      smul_zero]

/-- The perspective is positively homogeneous: `ψ_f(t A, t H) = t ψ_f(A, H)` for `t > 0`. -/
theorem matrixPerspective_smul_smul (f : ℝ → ℝ) (A H : Matrix n n 𝕜) {t : ℝ} (ht : 0 < t) :
    matrixPerspective f (t • A) (t • H) = t • matrixPerspective f A H := by
  have hsqrt : CFC.sqrt (t • A) = √t • CFC.sqrt A := by
    by_cases hA : 0 ≤ A
    · refine CFC.sqrt_unique ?_ (smul_nonneg (Real.sqrt_nonneg t) (CFC.sqrt_nonneg A))
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt ht.le,
        CFC.sqrt_mul_sqrt_self A hA]
    · have hA' : ¬0 ≤ t • A := fun h => hA <| by
        have h' := smul_nonneg (inv_nonneg.mpr ht.le) h
        rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h'
      rw [CFC.sqrt_of_not_nonneg hA, CFC.sqrt_of_not_nonneg hA', smul_zero]
  have hs := Real.mul_self_sqrt ht.le
  have hs0 : √t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  rw [matrixPerspective, matrixPerspective, hsqrt, inv_real_smul hs0]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have e : (√t)⁻¹ * (t * (√t)⁻¹) = 1 := by
    rw [mul_comm t, ← mul_assoc, ← mul_inv, hs, inv_mul_cancel₀ ht.ne']
  rw [e, one_smul, hs]

omit [Fintype n] [DecidableEq n] in
/-- Convex combinations of positive definite matrices are positive definite. -/
private theorem posDef_smul_add_smul {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : (a • A + b • B).PosDef := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    rwa [hab, zero_smul, zero_add, one_smul]
  · exact (hA.smul ha').add_posSemidef (hB.posSemidef.smul hb)

/-- The square root of a positive definite matrix and its inverse: both Hermitian, the square
root squares to the matrix, and they are inverse to each other. -/
private theorem sqrt_and_inv {A : Matrix n n 𝕜} (hA : A.PosDef) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A ∧ ((CFC.sqrt A)⁻¹)ᴴ = (CFC.sqrt A)⁻¹ ∧
      CFC.sqrt A * CFC.sqrt A = A ∧ CFC.sqrt A * (CFC.sqrt A)⁻¹ = 1 ∧
        (CFC.sqrt A)⁻¹ * CFC.sqrt A = 1 := by
  have hS : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hdet : IsUnit (CFC.sqrt A).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit_sqrt
  exact ⟨hS, by rw [Matrix.conjTranspose_nonsing_inv, hS.eq],
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg, Matrix.mul_nonsing_inv _ hdet,
    Matrix.nonsing_inv_mul _ hdet⟩

omit [DecidableEq n] in
/-- The congruence by `√c • (S * R)` in terms of the congruence by `R`. -/
private theorem conjTranspose_smul_mul_mul_smul {c : ℝ} (hc : 0 ≤ c) {S R : Matrix n n 𝕜}
    (hS : Sᴴ = S) (hR : Rᴴ = R) (N : Matrix n n 𝕜) :
    (√c • (S * R))ᴴ * N * (√c • (S * R)) = c • (R * (S * N * S) * R) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hR, hS, star_trivial]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hc,
    Matrix.mul_assoc]

/-- The operator Jensen inequality for the two-term family `K₁ = √a • S₁ R`, `K₂ = √b • S₂ R`
with `R (a S₁² + b S₂²) R = 1`. -/
private theorem OperatorConvexOn.cfc_mul_smul_add_smul_mul_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorConvexOn s f) {S₁ S₂ R B₁ B₂ : Matrix n n 𝕜} (hS₁ : S₁ᴴ = S₁) (hS₂ : S₂ᴴ = S₂)
    (hR : Rᴴ = R) (hB₁ : B₁.IsHermitian) (hB₂ : B₂.IsHermitian) (hB₁s : spectrum ℝ B₁ ⊆ s)
    (hB₂s : spectrum ℝ B₂ ⊆ s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : R * (a • (S₁ * S₁) + b • (S₂ * S₂)) * R = 1) :
    cfc f (R * (a • (S₁ * B₁ * S₁) + b • (S₂ * B₂ * S₂)) * R) ≤
      R * (a • (S₁ * cfc f B₁ * S₁) + b • (S₂ * cfc f B₂ * S₂)) * R := by
  have e : ∀ (c : ℝ) (Y : Matrix n n 𝕜), c • (R * Y * R) = R * (c • Y) * R := fun c Y => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hsum : ∀ N₁ N₂ : Matrix n n 𝕜,
      ∑ i : Fin 2, ((![√a • (S₁ * R), √b • (S₂ * R)] : Fin 2 → Matrix n n 𝕜) i)ᴴ *
        (![N₁, N₂] : Fin 2 → Matrix n n 𝕜) i *
          (![√a • (S₁ * R), √b • (S₂ * R)] : Fin 2 → Matrix n n 𝕜) i =
        R * (a • (S₁ * N₁ * S₁) + b • (S₂ * N₂ * S₂)) * R := fun N₁ N₂ => by
    rw [Fin.sum_univ_two]
    change (√a • (S₁ * R))ᴴ * N₁ * (√a • (S₁ * R)) + (√b • (S₂ * R))ᴴ * N₂ * (√b • (S₂ * R)) = _
    rw [conjTranspose_smul_mul_mul_smul ha hS₁ hR, conjTranspose_smul_mul_mul_smul hb hS₂ hR, e,
      e, ← Matrix.add_mul, ← Matrix.mul_add]
  have hK' : ∑ i : Fin 2, ((![√a • (S₁ * R), √b • (S₂ * R)] : Fin 2 → Matrix n n 𝕜) i)ᴴ *
      (![√a • (S₁ * R), √b • (S₂ * R)] : Fin 2 → Matrix n n 𝕜) i = 1 := by
    have h1 := conjTranspose_smul_mul_mul_smul ha hS₁ hR 1
    have h2 := conjTranspose_smul_mul_mul_smul hb hS₂ hR 1
    simp only [Matrix.mul_one] at h1 h2
    rw [Fin.sum_univ_two]
    change (√a • (S₁ * R))ᴴ * (√a • (S₁ * R)) + (√b • (S₂ * R))ᴴ * (√b • (S₂ * R)) = 1
    rw [h1, h2, e, e, ← Matrix.add_mul, ← Matrix.mul_add]
    exact hK
  have hJ := hf.cfc_sum_conjTranspose_mul_mul_le (A := ![B₁, B₂])
    (Fin.forall_fin_two.mpr ⟨hB₁, hB₂⟩) (Fin.forall_fin_two.mpr ⟨hB₁s, hB₂s⟩) hK'
  have hc : (fun i => cfc f ((![B₁, B₂] : Fin 2 → Matrix n n 𝕜) i)) = ![cfc f B₁, cfc f B₂] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hsum] at hJ
  refine hJ.trans (le_of_eq ?_)
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ => by rw [← hc]

/-- Joint convexity of the perspective, with the square roots and their inverses abstracted. -/
private theorem OperatorConvexOn.mul_cfc_mul_le {f : ℝ → ℝ} (hf : OperatorConvexOn (Set.Ioi 0) f)
    {S R S₁ R₁ S₂ R₂ H₁ H₂ : Matrix n n 𝕜} (hS : Sᴴ = S) (hR : Rᴴ = R) (hSR : S * R = 1)
    (hRS : R * S = 1) (hS₁ : S₁ᴴ = S₁) (hR₁ : R₁ᴴ = R₁) (hSR₁ : S₁ * R₁ = 1) (hRS₁ : R₁ * S₁ = 1)
    (hS₂ : S₂ᴴ = S₂) (hR₂ : R₂ᴴ = R₂) (hSR₂ : S₂ * R₂ = 1) (hRS₂ : R₂ * S₂ = 1)
    (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : a • (S₁ * S₁) + b • (S₂ * S₂) = S * S) :
    S * cfc f (R * (a • H₁ + b • H₂) * R) * S ≤
      a • (S₁ * cfc f (R₁ * H₁ * R₁) * S₁) + b • (S₂ * cfc f (R₂ * H₂ * R₂) * S₂) := by
  have hB : ∀ {T Q N : Matrix n n 𝕜}, Qᴴ = Q → T * Q = 1 → N.PosDef → (Q * N * Q).PosDef :=
    fun {T Q N} hQ hTQ hN => by
      have h := hN.conjTranspose_mul_mul_same (B := Q)
        (Function.LeftInverse.injective (g := T.mulVec) fun x => by
          rw [Matrix.mulVec_mulVec, hTQ, Matrix.one_mulVec])
      rwa [hQ] at h
  have hB₁ := hB hR₁ hSR₁ hH₁
  have hB₂ := hB hR₂ hSR₂ hH₂
  have hc : ∀ {T Q : Matrix n n 𝕜}, T * Q = 1 → Q * T = 1 → ∀ N : Matrix n n 𝕜,
      T * (Q * N * Q) * T = N := fun {T Q} hTQ hQT N => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hTQ, Matrix.one_mul, Matrix.mul_assoc, hQT,
      Matrix.mul_one]
  have hK' : R * (a • (S₁ * S₁) + b • (S₂ * S₂)) * R = 1 := by
    rw [hK, ← Matrix.mul_assoc, hRS, Matrix.one_mul, hSR]
  have h := hf.cfc_mul_smul_add_smul_mul_le hS₁ hS₂ hR hB₁.isHermitian hB₂.isHermitian
    hB₁.spectrum_subset_Ioi hB₂.spectrum_subset_Ioi ha hb hK'
  rw [hc hSR₁ hRS₁, hc hSR₂ hRS₂] at h
  have h2 := star_left_conjugate_le_conjugate h S
  rwa [Matrix.star_eq_conjTranspose, hS, hc hSR hRS] at h2

/-- **The perspective of an operator convex function is jointly operator convex**: for positive
definite `A₁`, `A₂`, `H₁`, `H₂` and weights `a + b = 1`,
`ψ_f(a A₁ + b A₂, a H₁ + b H₂) ≤ a ψ_f(A₁, H₁) + b ψ_f(A₂, H₂)`.
[Tropp2015, Theorem 8.6.2].
Port of `NLAlib.matrixPerspective_jointly_operatorConvex`, there over `ℂ` on `Fin d`.
Result: perspective-convexity -/
theorem OperatorConvexOn.matrixPerspective_smul_add_smul_le {f : ℝ → ℝ}
    (hf : OperatorConvexOn (Set.Ioi 0) f) {A₁ A₂ H₁ H₂ : Matrix n n 𝕜} (hA₁ : A₁.PosDef)
    (hA₂ : A₂.PosDef) (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    matrixPerspective f (a • A₁ + b • A₂) (a • H₁ + b • H₂) ≤
      a • matrixPerspective f A₁ H₁ + b • matrixPerspective f A₂ H₂ := by
  obtain ⟨hS, hR, hSS, hSR, hRS⟩ := sqrt_and_inv (posDef_smul_add_smul hA₁ hA₂ ha hb hab)
  obtain ⟨hS₁, hR₁, hSS₁, hSR₁, hRS₁⟩ := sqrt_and_inv hA₁
  obtain ⟨hS₂, hR₂, hSS₂, hSR₂, hRS₂⟩ := sqrt_and_inv hA₂
  exact hf.mul_cfc_mul_le hS hR hSR hRS hS₁ hR₁ hSR₁ hRS₁ hS₂ hR₂ hSR₂ hRS₂ hH₁ hH₂ ha hb
    (by rw [hSS₁, hSS₂, hSS])

end NLAlib
