/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import NLAlib.ForMathlib.Analysis.Calculus.ParametricIntegral
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Matrix.Functions.Perspective
public import NLAlib.Matrix.Norms.Frobenius

/-!
# The matrix K-transform and its derivative

A matrix-valued resolvent integral on compactly supported Hermitian data has a Fréchet
derivative on the admissible domain. Square-root congruence identifies the derivative quadratic
form with a self-adjoint map preserving the positive cone.

## Main results

* `NLAlib.hasFDerivAt_matrixKTransform_of_posDef`: differentiation on the support.
-/

@[expose] public section

open MeasureTheory Set Filter

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix K-transform denominator is positive at every sample in the support. -/
def IsKTransformAdmissible (ν : Measure (selfAdjoint (Matrix n n ℂ))) (S : Matrix n n ℂ) : Prop :=
  ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef

/-- The resolvent kernel
$\mathbf{T}(\mathbf{I}+\mathbf{S}\mathbf{T})^{-1}$ of the matrix K-transform. -/
noncomputable def matrixKResolvent (S T : Matrix n n ℂ) : Matrix n n ℂ := T * (1 + S * T)⁻¹

/-- The real continuous linear derivative of a resolvent kernel. -/
noncomputable def matrixKResolventDeriv (S T : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  -ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (matrixKResolvent S T) (matrixKResolvent S T)

/-- The matrix K-transform of a measure on Hermitian matrices, at parameter $\alpha$. -/
noncomputable def matrixKTransform (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  (∫ T, matrixKResolvent S T.val ∂ν) - α⁻¹ • S⁻¹

/-- The resolvent integral formula for the real derivative of the matrix K-transform. -/
noncomputable def matrixKTransformDeriv (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (∫ T, matrixKResolventDeriv S T.val ∂ν) +
    α⁻¹ • ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) S⁻¹ S⁻¹

/-- Fréchet derivative of nonsingular matrix inversion. -/
private theorem hasFDerivAt_matrixInverse (S : Matrix n n ℂ) (hS : IsUnit S) :
    HasFDerivAt (fun X : Matrix n n ℂ => X⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) S⁻¹ S⁻¹) S := by
  obtain ⟨u, hu⟩ := hS
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at h
  convert! h using 1
  · funext X
    exact Matrix.nonsing_inv_eq_ringInverse X
  · rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]

/-- Fréchet derivative of the resolvent at an invertible denominator. -/
private theorem hasFDerivAt_matrixKResolvent (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    HasFDerivAt (fun X => matrixKResolvent X T) (matrixKResolventDeriv S T) S := by
  have hlin := ((hasFDerivAt_id (𝕜 := ℝ) S).mul_const' T).const_add 1
  have hi := (hasFDerivAt_matrixInverse (1 + S * T) h).comp S hlin
  have hk := hi.const_mul T
  convert! hk using 1
  apply ContinuousLinearMap.ext
  intro X
  simp only [matrixKResolventDeriv, neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, matrixKResolvent, Matrix.mul_assoc, Matrix.mul_neg]

/-- The resolvent is jointly continuous at invertible denominators. -/
private theorem continuousAt_matrixKResolvent (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => matrixKResolvent p.1 p.2) (S, T) := by
  have hi := (hasFDerivAt_matrixInverse (1 + S * T) h).continuousAt
  have harg : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => 1 + p.1 * p.2) (S, T) := by
    fun_prop
  have hi' : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => (1 + p.1 * p.2)⁻¹) (S, T) :=
    hi.comp (f := fun p : Matrix n n ℂ × Matrix n n ℂ => 1 + p.1 * p.2) harg
  have hmul : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ =>
      p.2 * (1 + p.1 * p.2)⁻¹) (S, T) :=
    continuous_snd.continuousAt.mul hi'
  simpa only [matrixKResolvent] using hmul

/-- The derivative kernel is jointly continuous at invertible denominators. -/
private theorem continuousAt_matrixKResolventDeriv (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ =>
      matrixKResolventDeriv p.1 p.2) (S, T) := by
  have hr := continuousAt_matrixKResolvent S T h
  have hleft := (ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)).continuous.continuousAt.comp hr
  exact (hleft.clm_apply hr).neg

/-- Differentiation of the K-transform when all denominators on the support are invertible. -/
theorem hasFDerivAt_matrixKTransform (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : IsUnit S) (hden : ∀ T ∈ ν.support, IsUnit (1 + S * T.val)) :
    HasFDerivAt (matrixKTransform ν α) (matrixKTransformDeriv ν α S) S := by
  let U : Set (Matrix n n ℂ × selfAdjoint (Matrix n n ℂ)) := {p | IsUnit (1 + p.1 * p.2.val)}
  have hproj : Continuous (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (p.1, p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hU : IsOpen U := Units.isOpen.preimage
    (continuous_const.add (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  have hF : ContinuousOn (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) =>
      matrixKResolvent p.1 p.2.val) U := by
    intro p hp
    exact ((continuousAt_matrixKResolvent p.1 p.2.val hp).comp
      (f := fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (q.1, q.2.val))
      hproj.continuousAt).continuousWithinAt
  have hD : ContinuousOn (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) =>
      matrixKResolventDeriv p.1 p.2.val) U := by
    intro p hp
    exact ((continuousAt_matrixKResolventDeriv p.1 p.2.val hp).comp
      (f := fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (q.1, q.2.val))
      hproj.continuousAt).continuousWithinAt
  have hI := hasFDerivAt_integral_of_compact_support ν hν
    (fun X T => matrixKResolvent X T.val) (fun X T => matrixKResolventDeriv X T.val)
    U hU hF hD (fun p hp => hasFDerivAt_matrixKResolvent p.1 p.2.val hp) S hden
  have hInv := (hasFDerivAt_matrixInverse S hS).const_smul α⁻¹
  convert! hI.sub hInv using 1
  simp only [matrixKTransformDeriv, smul_neg, sub_neg_eq_add]

/-- The Hermitian sample after congruence by the square root of the evaluation point. -/
noncomputable def matrixKWhitened (S T : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt S * T * CFC.sqrt S

/-- The rational coefficient $\mathbf{Z}(\mathbf{I}+\mathbf{Z})^{-1}$ of a whitened sample. -/
noncomputable def matrixKCoefficient (S T : Matrix n n ℂ) : Matrix n n ℂ :=
  matrixKWhitened S T * (1 + matrixKWhitened S T)⁻¹

/-- The positive denominator condition implies invertibility of the resolvent denominator. -/
private theorem isUnit_matrixKDenominator (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : (S⁻¹ + T).PosDef) : IsUnit (1 + S * T) := by
  have he : 1 + S * T = S * (S⁻¹ + T) := by
    rw [Matrix.mul_add, Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)]
  rw [he]
  exact hS.isUnit.mul hgap.isUnit

/-- Whitening preserves the strict denominator condition. -/
private theorem posDef_one_add_matrixKWhitened (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : (S⁻¹ + T).PosDef) : (1 + matrixKWhitened S T).PosDef := by
  let Q := CFC.sqrt S
  let R := (CFC.sqrt S)⁻¹
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_sqrt
  have hQR : Q * R = 1 := Matrix.mul_nonsing_inv _ hd
  have hRQ : R * Q = 1 := Matrix.nonsing_inv_mul _ hd
  have hQi : IsUnit Q := ⟨⟨Q, R, hQR, hRQ⟩, rfl⟩
  have hQ : Q.IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hInv : S⁻¹ = R * R := hS.inv_eq_inv_sqrt_mul_inv_sqrt
  have he : 1 + matrixKWhitened S T = Q * (S⁻¹ + T) * Qᴴ := by
    rw [hQ.eq, Matrix.mul_add, Matrix.add_mul, hInv]
    change 1 + Q * T * Q = Q * (R * R) * Q + Q * T * Q
    rw [← Matrix.mul_assoc, hQR, Matrix.one_mul, hRQ]
  rw [he]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hQi).mpr hgap

/-- The rational coefficient of a Hermitian sample is Hermitian on the admissible domain. -/
private theorem isHermitian_matrixKCoefficient (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hT : T.IsHermitian) (hgap : (S⁻¹ + T).PosDef) : (matrixKCoefficient S T).IsHermitian := by
  have hZ : (matrixKWhitened S T).IsHermitian := by
    have hQ : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
    simp only [matrixKWhitened, Matrix.IsHermitian, Matrix.conjTranspose_mul, hQ.eq, hT.eq,
      Matrix.mul_assoc]
  have hP := posDef_one_add_matrixKWhitened S T hS hgap
  have he : matrixKCoefficient S T = 1 - (1 + matrixKWhitened S T)⁻¹ := by
    unfold matrixKCoefficient
    have hZeq : matrixKWhitened S T = (1 + matrixKWhitened S T) - 1 := by abel
    calc
      _ = ((1 + matrixKWhitened S T) - 1) * (1 + matrixKWhitened S T)⁻¹ := by rw [← hZeq]
      _ = _ := by
        rw [Matrix.sub_mul,
          Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit),
          Matrix.one_mul]
  rw [he]
  exact Matrix.isHermitian_one.sub hP.inv.isHermitian

/-- The resolvent is the inverse-square-root congruence of the whitened coefficient. -/
private theorem matrixKResolvent_eq_inv_sqrt_congruence (S T : Matrix n n ℂ) (hS : S.PosDef) :
    matrixKResolvent S T = (CFC.sqrt S)⁻¹ * matrixKCoefficient S T *
      (CFC.sqrt S)⁻¹ := by
  let Q := CFC.sqrt S
  let R := (CFC.sqrt S)⁻¹
  let Z := matrixKWhitened S T
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_sqrt
  have hQR : Q * R = 1 := Matrix.mul_nonsing_inv _ hd
  have hRQ : R * Q = 1 := Matrix.nonsing_inv_mul _ hd
  have hQQ : Q * Q = S := CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hden : 1 + S * T = Q * (1 + Z) * R := by
    dsimp only [Z, matrixKWhitened]
    change 1 + S * T = Q * (1 + Q * T * Q) * R
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    have hz : Q * (Q * T * Q) * R = S * T := by
      calc
        _ = (Q * Q) * T * (Q * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQQ, hQR, Matrix.mul_one]
    rw [hQR, hz]
  have hQi : Q⁻¹ = R := Matrix.inv_eq_right_inv hQR
  have hRi : R⁻¹ = Q := Matrix.inv_eq_right_inv hRQ
  unfold matrixKResolvent
  rw [hden, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hQi, hRi]
  change T * (Q * ((1 + Z)⁻¹ * R)) = R * (Z * (1 + Z)⁻¹) * R
  have hRZ : R * Z = T * Q := by
    change R * (Q * T * Q) = T * Q
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRQ, Matrix.one_mul]
  rw [← Matrix.mul_assoc R Z, hRZ]
  simp only [Matrix.mul_assoc]

/-- The resolvent is Hermitian at an admissible Hermitian sample. -/
private theorem isHermitian_matrixKResolvent (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hT : T.IsHermitian) (hgap : (S⁻¹ + T).PosDef) : (matrixKResolvent S T).IsHermitian := by
  rw [matrixKResolvent_eq_inv_sqrt_congruence S T hS]
  have hR : ((CFC.sqrt S)⁻¹).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv,
      (show (CFC.sqrt S).IsHermitian from (CFC.sqrt_nonneg S).isSelfAdjoint).eq]
  have hC := isHermitian_matrixKCoefficient S T hS hT hgap
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, hR.eq, hC.eq, Matrix.mul_assoc]

/-- Push-through identity for the left and right resolvents. -/
private theorem matrixKResolvent_eq_right (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hT : T.IsHermitian) (hgap : (S⁻¹ + T).PosDef) :
    matrixKResolvent S T = (1 + T * S)⁻¹ * T := by
  have hR := (isHermitian_matrixKResolvent S T hS hT hgap).eq
  simpa only [matrixKResolvent, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_add, Matrix.conjTranspose_one, hT.eq, hS.isHermitian.eq] using hR.symm

/-- **K-transform derivative.** The K-transform is Fréchet differentiable at a positive definite
matrix with positive denominators throughout the support. [MontanariSaeed2026, Eq. (21)].
Result: matrix-k-transform-stability -/
theorem hasFDerivAt_matrixKTransform_of_posDef
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : S.PosDef) (hgap : IsKTransformAdmissible ν S) :
    HasFDerivAt (matrixKTransform ν α) (matrixKTransformDeriv ν α S) S :=
  hasFDerivAt_matrixKTransform ν hν α S hS.isUnit
    (fun T hT => isUnit_matrixKDenominator S T.val hS (hgap T hT))

/-- The averaged conjugation by the whitened resolvent coefficient, scaled by $\alpha$. -/
noncomputable def matrixKStabilityMap (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  α • ∫ T, ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)
    (matrixKCoefficient S T.val) (matrixKCoefficient S T.val) ∂ν

/-- The whitened coefficient is the square-root congruence of the resolvent. -/
private theorem matrixKCoefficient_eq_sqrt_congruence (S T : Matrix n n ℂ) (hS : S.PosDef) :
    matrixKCoefficient S T = CFC.sqrt S * matrixKResolvent S T * CFC.sqrt S := by
  let Q := CFC.sqrt S
  let R := (CFC.sqrt S)⁻¹
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_sqrt
  have hQR : Q * R = 1 := Matrix.mul_nonsing_inv _ hd
  have hRQ : R * Q = 1 := Matrix.nonsing_inv_mul _ hd
  rw [matrixKResolvent_eq_inv_sqrt_congruence S T hS]
  change _ = Q * (R * matrixKCoefficient S T * R) * Q
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, Matrix.one_mul,
    Matrix.mul_assoc, hRQ, Matrix.mul_one]
private theorem continuousOn_kResolvent_support (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    (S : Matrix n n ℂ) (hden : ∀ T ∈ ν.support, IsUnit (1 + S * T.val)) :
    ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) => matrixKResolvent S T.val) ν.support := by
  intro T hT
  have hc : ContinuousAt (fun T : selfAdjoint (Matrix n n ℂ) => matrixKResolvent S T.val) T :=
    (continuousAt_matrixKResolvent S T.val (hden T hT)).comp
      (f := fun T : selfAdjoint (Matrix n n ℂ) => (S, T.val))
      (continuous_const.prodMk continuous_subtype_val).continuousAt
  exact hc.continuousWithinAt

/-- Integrability of the derivative and stability operator kernels on the support. -/
private theorem integrable_matrixK_kernels (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) :
    Integrable (fun T => matrixKResolventDeriv S T.val) ν ∧
    Integrable (fun T => ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)
      (matrixKCoefficient S T.val) (matrixKCoefficient S T.val)) ν := by
  have hden := fun T hT => isUnit_matrixKDenominator S T.val hS (hgap T hT)
  have hR := continuousOn_kResolvent_support ν S hden
  have hC : ContinuousOn
      (fun T : selfAdjoint (Matrix n n ℂ) => matrixKCoefficient S T.val) ν.support := by
    simp_rw [matrixKCoefficient_eq_sqrt_congruence S _ hS]
    exact (continuous_const.continuousOn.mul hR).mul continuous_const.continuousOn
  have hm := (ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)).continuous
  have hRC := (hm.comp_continuousOn hR).clm_apply hR
  have hCC := (hm.comp_continuousOn hC).clm_apply hC
  have hiR := hRC.neg.integrableOn_compact (μ := ν) hν
  have hiC := hCC.integrableOn_compact (μ := ν) hν
  have heq : ν.restrict ν.support = ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rw [IntegrableOn, heq] at hiR hiC
  exact ⟨hiR, hiC⟩

/-- Evaluation of the derivative as an integral of left and right resolvents.
[MontanariSaeed2026, Eq. (21)]. -/
theorem matrixKTransformDeriv_apply (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : S.PosDef) (hgap : IsKTransformAdmissible ν S) (Δ : Matrix n n ℂ) :
    matrixKTransformDeriv ν α S Δ = α⁻¹ • (S⁻¹ * Δ * S⁻¹) -
      ∫ T, T.val * (1 + S * T.val)⁻¹ * Δ * (1 + T.val * S)⁻¹ * T.val ∂ν := by
  have hi := (integrable_matrixK_kernels ν hν S hS hgap).1
  unfold matrixKTransformDeriv
  rw [add_apply, smul_apply, ContinuousLinearMap.integral_apply hi Δ]
  simp only [matrixKResolventDeriv, neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  rw [integral_neg]
  have he : (∫ T, matrixKResolvent S T.val * Δ * matrixKResolvent S T.val ∂ν) =
      ∫ T, T.val * (1 + S * T.val)⁻¹ * Δ * (1 + T.val * S)⁻¹ * T.val ∂ν := by
    apply integral_congr_ae
    filter_upwards [ν.support_mem_ae] with T hT
    have hHerm : T.val.IsHermitian := T.property
    nth_rw 2 [matrixKResolvent_eq_right S T.val hS hHerm (hgap T hT)]
    unfold matrixKResolvent
    simp only [Matrix.mul_assoc]
  rw [he]
  abel

private theorem matrixKTransformDeriv_apply_resolvent
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S) (Δ : Matrix n n ℂ) :
    matrixKTransformDeriv ν α S Δ = α⁻¹ • (S⁻¹ * Δ * S⁻¹) -
      ∫ T, matrixKResolvent S T.val * Δ * matrixKResolvent S T.val ∂ν := by
  have hi := (integrable_matrixK_kernels ν hν S hS hgap).1
  unfold matrixKTransformDeriv
  rw [add_apply, smul_apply, ContinuousLinearMap.integral_apply hi Δ]
  simp only [matrixKResolventDeriv, neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  rw [integral_neg]
  abel

/-- Evaluation of the stability map as an integral of matrix products. -/
theorem matrixKStabilityMap_apply (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : S.PosDef) (hgap : IsKTransformAdmissible ν S) (H : Matrix n n ℂ) :
    matrixKStabilityMap ν α S H =
      α • ∫ T, matrixKCoefficient S T.val * H * matrixKCoefficient S T.val ∂ν := by
  unfold matrixKStabilityMap
  rw [smul_apply, ContinuousLinearMap.integral_apply
    (integrable_matrixK_kernels ν hν S hS hgap).2 H]
  rfl

/-- Whitening carries the derivative to the identity minus the averaged stability operator. -/
theorem matrixKTransformDeriv_eq_congruence (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (hα : α ≠ 0)
    (S : Matrix n n ℂ) (hS : S.PosDef) (hgap : IsKTransformAdmissible ν S)
    (Δ : Matrix n n ℂ) :
    matrixKTransformDeriv ν α S Δ =
      let R := (CFC.sqrt S)⁻¹
      let H := R * Δ * R
      α⁻¹ • (R * (H - matrixKStabilityMap ν α S H) * R) := by
  let R := (CFC.sqrt S)⁻¹
  let H := R * Δ * R
  change matrixKTransformDeriv ν α S Δ = α⁻¹ • (R * (H - matrixKStabilityMap ν α S H) * R)
  have hi0 := (integrable_matrixK_kernels ν hν S hS hgap).2
  have hi : Integrable
      (fun T => matrixKCoefficient S T.val * H * matrixKCoefficient S T.val) ν := by
    simpa only [ContinuousLinearMap.mulLeftRight_apply] using hi0.apply_continuousLinearMap H
  let F := ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) R R
  have htransport := F.integral_comp_comm hi
  change (∫ T, R * (matrixKCoefficient S T.val * H * matrixKCoefficient S T.val) * R ∂ν) =
    R * (∫ T, matrixKCoefficient S T.val * H * matrixKCoefficient S T.val ∂ν) * R at htransport
  have hkernel : (∫ T, matrixKResolvent S T.val * Δ * matrixKResolvent S T.val ∂ν) =
      R * (∫ T, matrixKCoefficient S T.val * H * matrixKCoefficient S T.val ∂ν) * R := by
    rw [← htransport]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun T => by
      dsimp only
      rw [matrixKResolvent_eq_inv_sqrt_congruence S T.val hS]
      simp only [H, R, Matrix.mul_assoc]
  have hfirst : S⁻¹ * Δ * S⁻¹ = R * H * R := by
    rw [hS.inv_eq_inv_sqrt_mul_inv_sqrt]
    simp only [R, H, Matrix.mul_assoc]
  rw [matrixKTransformDeriv_apply_resolvent ν hν α S hS hgap Δ, hkernel, hfirst,
    matrixKStabilityMap_apply ν hν α S hS hgap H]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_sub, smul_smul, inv_mul_cancel₀ hα, one_smul]

omit [DecidableEq n] in
/-- Hermitian congruence is self-adjoint for the real Frobenius pairing. -/
private theorem frobInner_hermitian_congruence (R A B : Matrix n n ℂ) (hR : R.IsHermitian) :
    frobInner A (R * B * R) = frobInner (R * A * R) B := by
  rw [frobInner, frobInner, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hR.eq]
  congr 1
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (Aᴴ * R * B) R

/-- The derivative quadratic form equals the quadratic form of the whitened stability operator
up to a positive scalar for positive $\alpha$. -/
theorem frobInner_matrixKTransformDeriv (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (hα : α ≠ 0)
    (S : Matrix n n ℂ) (hS : S.PosDef) (hgap : IsKTransformAdmissible ν S)
    (Δ : Matrix n n ℂ) :
    frobInner Δ (matrixKTransformDeriv ν α S Δ) =
      let R := (CFC.sqrt S)⁻¹
      let H := R * Δ * R
      α⁻¹ * frobInner H (H - matrixKStabilityMap ν α S H) := by
  rw [matrixKTransformDeriv_eq_congruence ν hν α hα S hS hgap Δ, frobInner_smul_right,
    frobInner_hermitian_congruence]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv,
    (show (CFC.sqrt S).IsHermitian from (CFC.sqrt_nonneg S).isSelfAdjoint).eq]

/-- The real Frobenius pairing, bundled in its second argument. -/
private noncomputable def frobInnerCLM (A : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  (show Matrix n n ℂ →ₗ[ℝ] ℝ from
    { toFun := frobInner A
      map_add' := frobInner_add_right A
      map_smul' := fun r B => frobInner_smul_right r A B }).toContinuousLinearMap

/-- The stability operator sends positive semidefinite matrices to positive semidefinite
matrices. -/
theorem posSemidef_matrixKStabilityMap
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    (matrixKStabilityMap ν α S P).PosSemidef := by
  rw [matrixKStabilityMap_apply ν hν α S hS hgap P]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply smul_nonneg hα
  apply integral_nonneg_of_ae
  filter_upwards [ν.support_mem_ae] with T hT
  have hC := isHermitian_matrixKCoefficient S T.val hS T.property (hgap T hT)
  change (matrixKCoefficient S T.val * P * matrixKCoefficient S T.val -
    (0 : Matrix n n ℂ)).PosSemidef
  rw [sub_zero]
  simpa only [hC.eq] using hP.mul_mul_conjTranspose_same (matrixKCoefficient S T.val)

/-- The stability operator preserves Hermitian matrices. -/
theorem isHermitian_matrixKStabilityMap
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (matrixKStabilityMap ν α S H).IsHermitian := by
  have hp := posSemidef_matrixKStabilityMap ν hν α hα S hS hgap
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)))
  have hn := posSemidef_matrixKStabilityMap ν hν α hα S hS hgap
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)))
  have he := hp.isHermitian.sub hn.isHermitian
  rwa [← map_sub, CFC.posPart_sub_negPart H hH.isSelfAdjoint] at he

/-- The stability operator is symmetric for the real Frobenius pairing. -/
theorem frobInner_matrixKStabilityMap_comm
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : IsKTransformAdmissible ν S)
    (A B : Matrix n n ℂ) :
    frobInner A (matrixKStabilityMap ν α S B) =
      frobInner (matrixKStabilityMap ν α S A) B := by
  have hi0 := (integrable_matrixK_kernels ν hν S hS hgap).2
  have hi (H : Matrix n n ℂ) : Integrable
      (fun T => matrixKCoefficient S T.val * H * matrixKCoefficient S T.val) ν := by
    simpa only [ContinuousLinearMap.mulLeftRight_apply] using hi0.apply_continuousLinearMap H
  rw [matrixKStabilityMap_apply ν hν α S hS hgap B,
    matrixKStabilityMap_apply ν hν α S hS hgap A,
    frobInner_smul_right, frobInner_smul_left]
  congr 1
  have hleft := (frobInnerCLM A).integral_comp_comm (hi B)
  have hright := (frobInnerCLM B).integral_comp_comm (hi A)
  change (∫ T, frobInner A (matrixKCoefficient S T.val * B * matrixKCoefficient S T.val) ∂ν) =
    frobInner A (∫ T, matrixKCoefficient S T.val * B * matrixKCoefficient S T.val ∂ν) at hleft
  change (∫ T, frobInner B (matrixKCoefficient S T.val * A * matrixKCoefficient S T.val) ∂ν) =
    frobInner B (∫ T, matrixKCoefficient S T.val * A * matrixKCoefficient S T.val ∂ν) at hright
  rw [← hleft, frobInner_comm _ B, ← hright]
  apply integral_congr_ae
  filter_upwards [ν.support_mem_ae] with T hT
  rw [frobInner_hermitian_congruence _ A B
    (isHermitian_matrixKCoefficient S T.val hS T.property (hgap T hT)), frobInner_comm]

end NLAlib
