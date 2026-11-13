/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.PositiveCone
public import NLAlib.Matrix.Functions.KTransform

/-!
# Positive-matrix certificates for K-transform stability

Strict positivity of the derivative on Hermitian directions is equivalent to a norm bound and to
two positive-matrix certificates. Under the norm bound the inverse preserves the cone.

## Main results

* `NLAlib.forall_frobInner_matrixKTransformDeriv_pos_iff_norm_lt_one`: the stability certificates.
* `NLAlib.norm_matrixKStabilityFrobenius_lt_one_iff_exists_posDef_sub`: the order certificate.
-/

@[expose] public section

open MeasureTheory

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Square-root congruence undoes inverse-square-root congruence. -/
private theorem sqrt_invSqrt_congruence (S : Matrix n n ℂ) (hS : S.PosDef) (X : Matrix n n ℂ) :
    CFC.sqrt S * ((CFC.sqrt S)⁻¹ * X *
      (CFC.sqrt S)⁻¹) * CFC.sqrt S = X := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_sqrt
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

/-- Inverse-square-root congruence undoes square-root congruence. -/
private theorem invSqrt_sqrt_congruence (S : Matrix n n ℂ) (hS : S.PosDef) (X : Matrix n n ℂ) :
    (CFC.sqrt S)⁻¹ * (CFC.sqrt S * X * CFC.sqrt S) *
      (CFC.sqrt S)⁻¹ = X := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_sqrt
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

/-- Strict matrix positivity is unchanged by inverse-square-root congruence. -/
private theorem posDef_invSqrt_congruence_iff (S : Matrix n n ℂ) (hS : S.PosDef)
    (X : Matrix n n ℂ) :
    ((CFC.sqrt S)⁻¹ * X * (CFC.sqrt S)⁻¹).PosDef ↔ X.PosDef := by
  have hR : ((CFC.sqrt S)⁻¹).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv,
      (show (CFC.sqrt S).IsHermitian from (CFC.sqrt_nonneg S).isSelfAdjoint).eq]
  simpa only [Matrix.star_eq_conjTranspose, hR.eq] using
    Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Matrix.isUnit_nonsing_inv_iff.mpr hS.isUnit_sqrt) (x := X)

omit [Fintype n] [DecidableEq n] in
/-- Positive scalar multiplication preserves and reflects strict positivity. -/
private theorem posDef_real_smul_iff (a : ℝ) (ha : 0 < a) (X : Matrix n n ℂ) :
    (a • X).PosDef ↔ X.PosDef := by
  constructor
  · intro h
    have hh := h.smul (inv_pos.mpr ha)
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul] using hh
  · exact fun h => h.smul ha

/-- The derivative's strict-positive output condition is exactly the strict supersolution gap
after invertible whitening. -/
private theorem posDef_matrixKTransformDeriv_iff
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) (Δ : Matrix n n ℂ) :
    (matrixKTransformDeriv ν α S Δ).PosDef ↔
      ((CFC.sqrt S)⁻¹ * Δ * (CFC.sqrt S)⁻¹ -
        matrixKStabilityMap ν α S ((CFC.sqrt S)⁻¹ * Δ *
          (CFC.sqrt S)⁻¹)).PosDef := by
  rw [matrixKTransformDeriv_eq_congruence ν hν α (ne_of_gt hα) S hS hgap Δ]
  rw [posDef_real_smul_iff _ (inv_pos.mpr hα), posDef_invSqrt_congruence_iff S hS]

/-- The Hermitian compression of the stability map in the Frobenius norm. At admissible
points the map itself preserves the Hermitian subspace. -/
noncomputable def matrixKStabilityFrobenius
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ) (S : Matrix n n ℂ) :
    hermitianFrobenius ℂ n →L[ℝ] hermitianFrobenius ℂ n :=
  let project := (hermitianFrobeniusEquiv ℂ n).symm.toLinearMap.comp
    (selfAdjointPart ℝ : Matrix n n ℂ →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
  (project.comp ((matrixKStabilityMap ν α S).toLinearMap.comp
    hermitianFrobeniusMatrixLinear)).toContinuousLinearMap

/-- Evaluation on a Hermitian input recovers the integral operator on matrices. -/
theorem hermitianFrobeniusMatrix_matrixKStabilityFrobenius
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) (x : hermitianFrobenius ℂ n) :
    hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν α S x) =
      matrixKStabilityMap ν α S (hermitianFrobeniusMatrix ℂ n x) := by
  exact (isHermitian_matrixKStabilityMap ν hν α hα S hS hgap
    (isHermitian_hermitianFrobeniusMatrix x)).isSelfAdjoint.coe_selfAdjointPart_apply ℝ

/-- The stability operator is symmetric in the Frobenius inner product. -/
theorem isSymmetric_matrixKStabilityFrobenius
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) :
    (matrixKStabilityFrobenius ν α S).IsSymmetric := by
  intro x y
  change frobInner (hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν α S x))
    (hermitianFrobeniusMatrix ℂ n y) = frobInner (hermitianFrobeniusMatrix ℂ n x)
      (hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν α S y))
  rw [hermitianFrobeniusMatrix_matrixKStabilityFrobenius ν hν α hα S hS hgap x,
    hermitianFrobeniusMatrix_matrixKStabilityFrobenius ν hν α hα S hS hgap y]
  exact (frobInner_matrixKStabilityMap_comm ν hν α S hS hgap _ _).symm

/-- The Frobenius realization of the stability operator preserves the positive semidefinite
cone. -/
theorem posSemidef_matrixKStabilityFrobenius
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S)
    (x : hermitianFrobenius ℂ n) (hx : (hermitianFrobeniusMatrix ℂ n x).PosSemidef) :
    (hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν α S x)).PosSemidef := by
  rw [hermitianFrobeniusMatrix_matrixKStabilityFrobenius ν hν α hα S hS hgap]
  exact posSemidef_matrixKStabilityMap ν hν α hα S hS hgap hx

/-- Whitening identifies the positive derivative quadratic form with strict positivity of the
identity minus the stability operator. -/
private theorem matrixKTransform_quadratic_iff
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) :
    (∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ ≠ 0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α S Δ)) ↔
    (∀ x : hermitianFrobenius ℂ n, x ≠ 0 →
      0 < inner ℝ x (x - matrixKStabilityFrobenius ν α S x)) := by
  let Q := CFC.sqrt S
  let R := (CFC.sqrt S)⁻¹
  have hQ : Q.IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hR : R.IsHermitian := by
    change Matrix.conjTranspose ((CFC.sqrt S)⁻¹) = (CFC.sqrt S)⁻¹
    rw [Matrix.conjTranspose_nonsing_inv, (show (CFC.sqrt S).IsHermitian from hQ).eq]
  have hquad (x : hermitianFrobenius ℂ n) :
      inner ℝ x (x - matrixKStabilityFrobenius ν α S x) =
        frobInner (hermitianFrobeniusMatrix ℂ n x) (hermitianFrobeniusMatrix ℂ n x -
          matrixKStabilityMap ν α S (hermitianFrobeniusMatrix ℂ n x)) := by
    change frobInner (hermitianFrobeniusMatrix ℂ n x) (hermitianFrobeniusMatrix ℂ n x -
      hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν α S x)) = _
    rw [hermitianFrobeniusMatrix_matrixKStabilityFrobenius ν hν α hα.le S hS hgap]
  simp only [hquad]
  constructor
  · intro h x hx
    let H := hermitianFrobeniusMatrix ℂ n x
    let Δ := Q * H * Q
    have hΔ : Δ.IsHermitian := by
      simpa only [hQ.eq] using Matrix.isHermitian_mul_mul_conjTranspose Q
        (isHermitian_hermitianFrobeniusMatrix x)
    have hΔ0 : Δ ≠ 0 := by
      intro hz
      have he : R * Δ * R = H := invSqrt_sqrt_congruence S hS H
      rw [hz, Matrix.mul_zero, Matrix.zero_mul] at he
      apply hx
      apply (hermitianFrobeniusEquiv ℂ n).injective
      exact Subtype.ext he.symm
    have hp := h Δ hΔ hΔ0
    have he := frobInner_matrixKTransformDeriv ν hν α (ne_of_gt hα) S hS hgap Δ
    dsimp only at he
    rw [invSqrt_sqrt_congruence S hS H] at he
    rw [he] at hp
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hα)).mp hp
  · intro h Δ hΔ hΔ0
    let H := R * Δ * R
    have hH : H.IsHermitian := by
      simpa only [hR.eq] using Matrix.isHermitian_mul_mul_conjTranspose R hΔ
    let x := toHermitianFrobenius hH
    have hx : x ≠ 0 := by
      intro hz
      have hh := congrArg (hermitianFrobeniusMatrix ℂ n) hz
      change H = 0 at hh
      have he : Q * H * Q = Δ := sqrt_invSqrt_congruence S hS Δ
      rw [hh, Matrix.mul_zero, Matrix.zero_mul] at he
      exact hΔ0 he.symm
    have hp := h x hx
    rw [frobInner_matrixKTransformDeriv ν hν α (ne_of_gt hα) S hS hgap Δ]
    exact mul_pos (inv_pos.mpr hα) hp

/-- **K-transform quadratic stability.** For $n$ nonempty, the derivative is strictly positive
on nonzero Hermitian directions exactly when the stability map contracts in Frobenius norm.
[MontanariSaeed2026, Lemma 6].
Result: matrix-k-transform-stability -/
theorem forall_frobInner_matrixKTransformDeriv_pos_iff_norm_lt_one [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) :
    (∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ ≠ 0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α S Δ)) ↔
    ‖matrixKStabilityFrobenius ν α S‖ < 1 := by
  rw [matrixKTransform_quadratic_iff ν hν α hα S hS hgap]
  exact inner_sub_map_pos_iff_norm_lt_one _
    (isSymmetric_matrixKStabilityFrobenius ν hν α hα.le S hS hgap)
    (posSemidef_matrixKStabilityFrobenius ν hν α hα.le S hS hgap)

/-- **K-transform supersolution criterion.** For $n$ nonempty, the stability map contracts in
Frobenius norm exactly when it admits a positive definite strict supersolution.
[MontanariSaeed2026, Lemma 6].
Result: matrix-k-transform-stability -/
theorem norm_matrixKStabilityFrobenius_lt_one_iff_exists_posDef_sub [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) :
    ‖matrixKStabilityFrobenius ν α S‖ < 1 ↔
    ∃ Y : Matrix n n ℂ, Y.PosDef ∧ (Y - matrixKStabilityMap ν α S Y).PosDef := by
  have he := (norm_lt_one_iff_exists_posDef_sub_map
    (matrixKStabilityFrobenius ν α S)
    (isSymmetric_matrixKStabilityFrobenius ν hν α hα.le S hS hgap)
    (posSemidef_matrixKStabilityFrobenius ν hν α hα.le S hS hgap))
  rw [he]
  constructor
  · rintro ⟨Y, hY, hg⟩
    refine ⟨hermitianFrobeniusMatrix ℂ n Y, hY, ?_⟩
    change (_ - hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν α S Y)).PosDef at hg
    rwa [hermitianFrobeniusMatrix_matrixKStabilityFrobenius ν hν α hα.le S hS hgap] at hg
  · rintro ⟨Y, hY, hg⟩
    let y := toHermitianFrobenius hY.isHermitian
    refine ⟨y, hY, ?_⟩
    change (Y - hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν α S y)).PosDef
    rwa [hermitianFrobeniusMatrix_matrixKStabilityFrobenius ν hν α hα.le S hS hgap]

/-- **K-transform derivative witness.** A positive definite strict supersolution exists exactly
when the derivative sends some positive definite direction to a positive definite matrix.
[MontanariSaeed2026, Lemma 6].
Result: matrix-k-transform-stability -/
theorem exists_posDef_sub_matrixKStabilityMap_iff_exists_posDef_matrixKTransformDeriv
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) :
    (∃ Y : Matrix n n ℂ, Y.PosDef ∧ (Y - matrixKStabilityMap ν α S Y).PosDef) ↔
    ∃ B : Matrix n n ℂ, B.PosDef ∧ (matrixKTransformDeriv ν α S B).PosDef := by
  constructor
  · rintro ⟨Y, hY, hg⟩
    have hQ : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
    have hQY := (Matrix.IsUnit.posDef_star_right_conjugate_iff hS.isUnit_sqrt).mpr hY
    refine ⟨CFC.sqrt S * Y * CFC.sqrt S, ?_, ?_⟩
    · simpa only [Matrix.star_eq_conjTranspose, hQ.eq] using hQY
    · rw [posDef_matrixKTransformDeriv_iff ν hν α hα S hS hgap,
        invSqrt_sqrt_congruence S hS Y]
      exact hg
  · rintro ⟨B, hB, hg⟩
    exact ⟨_, (posDef_invSqrt_congruence_iff S hS B).mpr hB,
      (posDef_matrixKTransformDeriv_iff ν hν α hα S hS hgap B).mp hg⟩

end NLAlib
