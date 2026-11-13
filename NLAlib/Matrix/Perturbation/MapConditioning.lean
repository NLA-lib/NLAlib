/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Conditioning of a differentiable map

The operator norm of the Fréchet derivative measures absolute sensitivity. Normwise
relative conditioning uses the norms of the input and output. Componentwise conditioning
uses their individual coordinates and measures the resulting perturbations in Euclidean norm.

## Main results

* `NLAlib.specNorm_euclideanJacobian`: absolute sensitivity in coordinates.
* `NLAlib.hasFDerivAt_componentwisePerturbation`: the relative-coordinate derivative.
* `NLAlib.specNorm_componentwiseJacobian_le`: the diagonal scaling bound.
* `NLAlib.normwiseRelativeCondition_toEuclideanCLM_le`: the linear condition bound.
-/

@[expose] public section

open Matrix

namespace NLAlib

section Normwise

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {U W : Type*}
  [NormedAddCommGroup U] [NormedSpace 𝕜 U] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Normwise relative conditioning of a map, with the norm of the Fréchet derivative scaled
by the reference norms. The relative interpretation takes a differentiable map and nonzero
input and output. The total formula uses zero for division by zero. [Gautschi2004, Def 2.4]. -/
noncomputable def normwiseRelativeCondition (f : U → W) (x : U) : ℝ :=
  ‖fderiv 𝕜 f x‖ * ‖x‖ / ‖f x‖

/-- For scalar data the normwise relative condition is the norm of the logarithmic
derivative times the input. [Gautschi2004, Def 2.6]. -/
theorem normwiseRelativeCondition_eq_norm_mul_deriv_div (f : 𝕜 → 𝕜) (x : 𝕜) :
    normwiseRelativeCondition 𝕜 f x = ‖x * deriv f x / f x‖ := by
  rw [normwiseRelativeCondition, ← norm_deriv_eq_norm_fderiv, norm_div, norm_mul, mul_comm]

end Normwise

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq m]

/-- The coordinate matrix of the Fréchet derivative in the Euclidean coordinate bases.
[Gautschi2004, Def 2.3]. -/
noncomputable def euclideanJacobian (f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n)
    (x : EuclideanSpace 𝕜 m) : Matrix n m 𝕜 :=
  Matrix.toEuclideanLin.symm (fderiv 𝕜 f x).toLinearMap

omit [Fintype n] in
/-- Returning to the Euclidean linear map recovers the Fréchet derivative.
[Gautschi2004, Def 2.3]. -/
theorem toEuclideanLin_euclideanJacobian (f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n)
    (x : EuclideanSpace 𝕜 m) :
    (euclideanJacobian f x).toEuclideanLin = (fderiv 𝕜 f x).toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

omit [Fintype n] in
/-- Each entry is obtained by applying the derivative to a coordinate vector.
[Gautschi2004, Def 2.3]. -/
theorem euclideanJacobian_apply (f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n)
    (x : EuclideanSpace 𝕜 m) (i : n) (j : m) :
    euclideanJacobian f x i j = (fderiv 𝕜 f x (EuclideanSpace.single j 1)) i := rfl

/-- **Absolute conditioning in coordinates.** The spectral norm of the Euclidean Jacobian
is the operator norm of the Fréchet derivative. [Gautschi2004, Def 2.3].
Result: condition-number-of-map-def -/
theorem specNorm_euclideanJacobian (f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n)
    (x : EuclideanSpace 𝕜 m) : specNorm (euclideanJacobian f x) = ‖fderiv 𝕜 f x‖ := by
  open scoped Matrix.Norms.L2Operator in
    rw [specNorm_eq_norm, Matrix.l2_opNorm_def]
  simp only [LinearEquiv.trans_apply, toEuclideanLin_euclideanJacobian]
  congr 1

variable [DecidableEq n]

/-- The Jacobian in relative input and output coordinates. Its spectral norm gives
componentwise relative conditioning at a differentiability point with nonzero reference
coordinates. With a zero coordinate the formula still uses the total inverse.
[Gautschi2004, Def 2.4]. -/
noncomputable def componentwiseJacobian (f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n)
    (x : EuclideanSpace 𝕜 m) : Matrix n m 𝕜 :=
  diagonal (fun i => (f x i)⁻¹) * euclideanJacobian f x * diagonal (fun j => x j)

/-- The entries of the componentwise Jacobian are scaled partial derivatives.
[Gautschi2004, Def 2.4]. -/
theorem componentwiseJacobian_apply (f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n)
    (x : EuclideanSpace 𝕜 m) (i : n) (j : m) :
    componentwiseJacobian f x i j =
      x j * (fderiv 𝕜 f x (EuclideanSpace.single j 1)) i / f x i := by
  simp only [componentwiseJacobian, Matrix.mul_diagonal, Matrix.diagonal_mul,
    euclideanJacobian_apply, div_eq_mul_inv]
  ring

/-- A relative input perturbation is scaled into physical coordinates and the output
difference is divided by the reference coordinates. [Gautschi2004, Def 2.4]. -/
noncomputable def componentwisePerturbation (f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n)
    (x u : EuclideanSpace 𝕜 m) : EuclideanSpace 𝕜 n :=
  Matrix.toEuclideanCLM (𝕜 := 𝕜) (diagonal (fun i => (f x i)⁻¹))
    (f (x + Matrix.toEuclideanCLM (𝕜 := 𝕜) (diagonal (fun j => x j)) u) - f x)

/-- **Derivative in relative coordinates.** At a differentiability point the componentwise
Jacobian represents the derivative of the relative perturbation map at zero.
[Gautschi2004, Def 2.4].
Result: componentwise-perturbation-derivative -/
theorem hasFDerivAt_componentwisePerturbation
    {f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n} {x : EuclideanSpace 𝕜 m}
    (hf : DifferentiableAt 𝕜 f x) :
    HasFDerivAt (componentwisePerturbation f x)
      ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
        (componentwiseJacobian f x)) 0 := by
  let dx := Matrix.toEuclideanCLM (𝕜 := 𝕜) (diagonal (fun j => x j))
  let dy := Matrix.toEuclideanCLM (𝕜 := 𝕜) (diagonal (fun i => (f x i)⁻¹))
  have hin : HasFDerivAt (fun u => x + dx u) dx 0 := dx.hasFDerivAt.const_add x
  have hf₀ : HasFDerivAt f (fderiv 𝕜 f x) (x + dx 0) := by
    simpa only [map_zero, add_zero] using hf.hasFDerivAt
  have h := dy.hasFDerivAt.comp 0 ((hf₀.comp 0 hin).sub_const (f x))
  have heq : dy.comp ((fderiv 𝕜 f x).comp dx) =
      (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
        (componentwiseJacobian f x) := by
    apply ContinuousLinearMap.coe_injective
    change dy.toLinearMap.comp ((fderiv 𝕜 f x).toLinearMap.comp dx.toLinearMap) =
      (componentwiseJacobian f x).toEuclideanLin
    change _ = Matrix.toLpLin 2 2
      (diagonal (fun i => (f x i)⁻¹) * euclideanJacobian f x * diagonal (fun j => x j))
    rw [Matrix.toLpLin_mul 2 2 2, Matrix.toLpLin_mul 2 2 2, toEuclideanLin_euclideanJacobian]
    rfl
  rw [heq] at h
  exact h

/-- The norm of the derivative of the relative perturbation map is the spectral norm of
the componentwise Jacobian. [Gautschi2004, Def 2.4]. -/
theorem specNorm_componentwiseJacobian {f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n}
    {x : EuclideanSpace 𝕜 m} (hf : DifferentiableAt 𝕜 f x) :
    specNorm (componentwiseJacobian f x) = ‖fderiv 𝕜 (componentwisePerturbation f x) 0‖ := by
  rw [(hasFDerivAt_componentwisePerturbation hf).fderiv]
  rfl

/-- **Componentwise relative conditioning.** The spectral norm of the componentwise Jacobian
is at most the product of the output scaling norm, the absolute condition of the map, and
the input scaling norm. [Gautschi2004, Def 2.4].
Result: componentwise-condition-bound -/
theorem specNorm_componentwiseJacobian_le (f : EuclideanSpace 𝕜 m → EuclideanSpace 𝕜 n)
    (x : EuclideanSpace 𝕜 m) :
    specNorm (componentwiseJacobian f x) ≤
      specNorm (diagonal (fun i => (f x i)⁻¹)) * ‖fderiv 𝕜 f x‖ *
        specNorm (diagonal (fun j => x j)) := by
  unfold componentwiseJacobian
  refine (specNorm_mul_le _ _).trans ?_
  rw [← specNorm_euclideanJacobian f x]
  exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)

/-- **Normwise conditioning of a linear system.** At every input the normwise relative
condition of an invertible Euclidean linear map is at most its matrix condition number.
[TrefethenBau1997, Lecture 12].
Result: linear-map-relative-condition-bound -/
theorem normwiseRelativeCondition_toEuclideanCLM_le {A : Matrix n n 𝕜} (hA : IsUnit A)
    (x : EuclideanSpace 𝕜 n) :
    normwiseRelativeCondition 𝕜 (Matrix.toEuclideanCLM (𝕜 := 𝕜) A) x ≤
      pseudoConditionNumber A := by
  let T := Matrix.toEuclideanCLM (𝕜 := 𝕜) A
  let S := Matrix.toEuclideanCLM (𝕜 := 𝕜) A⁻¹
  have hx : S (T x) = x := by
    have h := congrArg (fun M : Matrix n n 𝕜 => Matrix.toEuclideanCLM (𝕜 := 𝕜) M x)
      (Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA))
    simpa only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] using h
  have hbound : ‖x‖ ≤ specNorm A⁻¹ * ‖T x‖ :=
    calc ‖x‖ = ‖S (T x)‖ := congrArg norm hx.symm
         _ ≤ _ := S.le_opNorm (T x)
  rw [normwiseRelativeCondition, ContinuousLinearMap.fderiv, pseudoConditionNumber_of_isUnit hA]
  change specNorm A * ‖x‖ / ‖T x‖ ≤ _
  by_cases hz : T x = 0
  · simp only [hz, norm_zero, div_zero]
    exact mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hbound (specNorm_nonneg _)

end NLAlib
