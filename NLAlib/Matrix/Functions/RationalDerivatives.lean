/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.RationalDifferences
public import NLAlib.ForMathlib.Analysis.Calculus.FDeriv.Polynomial
public import NLAlib.ForMathlib.Analysis.Calculus.FDeriv.Secant
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# First and second derivatives of rational matrix functions

On the open denominator domain, evaluating the two-block difference at equal arguments
gives the derivative. The Hessian adds both orders of the three-block insertion.

## Main results

* `NLAlib.fderiv_rationalMatrixEval_apply`: the first derivative.
* `NLAlib.fderiv_fderiv_rationalMatrixEval_apply`: the Hessian in two directions.
-/

@[expose] public section

namespace NLAlib

section
open Polynomial ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Topology
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n 𝕜

@[fun_prop] private theorem continuous_flip_matrixBilinear :
    Continuous (fun L : M →L[𝕜] M →L[𝕜] M => L.flip) :=
  (flipₗᵢ 𝕜 M M M).continuous

/-- The monomial insertion sum as a continuous linear map. [Tropp2026, §§4.2–4.4]. -/
private noncomputable def monomialBlockMap (A B : M) (k : ℕ) : M →L[𝕜] M :=
  ∑ j ∈ Finset.range k, mulLeftRight 𝕜 M (A ^ (k.pred - j)) (B ^ j)

@[simp] private theorem monomialBlockMap_apply (A B H : M) (k : ℕ) :
    monomialBlockMap A B k H = monomialBlockDifference A B H k := by
  simp [monomialBlockMap, monomialBlockDifference]

/-- The first polynomial block difference as a continuous linear map. [Tropp2026, §§4.2–4.4]. -/
private noncomputable def polynomialBlockMap (p : 𝕜[X]) (A B : M) : M →L[𝕜] M :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • monomialBlockMap A B k

@[simp] private theorem polynomialBlockMap_apply (p : 𝕜[X]) (A B H : M) :
    polynomialBlockMap p A B H = polynomialBlockDifference p A B H := by
  simp [polynomialBlockMap, polynomialBlockDifference]

/-- The ordered second polynomial block difference as a continuous bilinear map. [Tropp2026,
§§4.2–4.4]. -/
private noncomputable def polynomialSecondBlockMap (p : 𝕜[X]) (A B C : M) : M →L[𝕜] M →L[𝕜] M :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k •
    ∑ j ∈ Finset.range k,
      (compL 𝕜 M M M (mulLeftRight 𝕜 M 1 (C ^ j))).comp
        ((mul 𝕜 M).comp (monomialBlockMap A B (k.pred - j)))

@[simp] private theorem polynomialSecondBlockMap_apply (p : 𝕜[X]) (A B C G H : M) :
    polynomialSecondBlockMap p A B C G H = polynomialSecondBlockDifference p A B C G H := by
  simp [polynomialSecondBlockMap, polynomialSecondBlockDifference]

/-- The first rational difference as a continuous linear map. [Tropp2026, §§4.2–4.4]. -/
private noncomputable def firstLinear (P Q : 𝕜[X]) (A B : M) : M →L[𝕜] M :=
  (mulLeftRight 𝕜 M 1 (aeval B Q)⁻¹).comp
    (polynomialBlockMap P A B -
      (mulLeftRight 𝕜 M (rationalMatrixEval P Q A) 1).comp (polynomialBlockMap Q A B))

/-- Applying the continuous first-difference map gives the algebraic block difference. [Tropp2026,
§§4.2–4.4]. -/
@[simp] private theorem firstLinear_apply (P Q : 𝕜[X]) (A B H : M) :
    firstLinear P Q A B H = rationalBlockDifference P Q A B H := by
  simp [firstLinear, rationalBlockDifference, Matrix.sub_mul]

/-- The continuous linear map acting by the first rational block difference. [Tropp2026, §4.2]. -/
noncomputable def rationalBlockMap (P Q : 𝕜[X]) (A B : M) : M →L[𝕜] M :=
  LinearMap.toContinuousLinearMap
    { toFun := rationalBlockDifference P Q A B
      map_add' x y := by simp only [← firstLinear_apply, map_add]
      map_smul' c x := by simp only [← firstLinear_apply, map_smul, RingHom.id_apply] }

/-- Applying the linear map in a direction gives its first block difference. -/
@[simp] theorem rationalBlockMap_apply (P Q : 𝕜[X]) (A B H : M) :
    rationalBlockMap P Q A B H = rationalBlockDifference P Q A B H := rfl

private theorem rationalBlockMap_eq (P Q : 𝕜[X]) (A B : M) :
    rationalBlockMap P Q A B = firstLinear P Q A B := by
  ext H i j
  simp


/-- The ordered second rational difference as a continuous bilinear map. [Tropp2026, §§4.2–4.4].
-/
private noncomputable def secondBilinear (P Q : 𝕜[X]) (A B C : M) : M →L[𝕜] M →L[𝕜] M :=
  (compL 𝕜 M M M (mulLeftRight 𝕜 M 1 (aeval C Q)⁻¹)).comp
    (polynomialSecondBlockMap P A B C -
      (compL 𝕜 M M M (mulLeftRight 𝕜 M (rationalMatrixEval P Q A) 1)).comp
        (polynomialSecondBlockMap Q A B C) -
      bilinearComp (mul 𝕜 M) (rationalBlockMap P Q A B) (polynomialBlockMap Q B C))

/-- Evaluation in two directions gives the ordered algebraic second difference. [Tropp2026,
§§4.2–4.4]. -/
@[simp] private theorem secondBilinear_apply (P Q : 𝕜[X]) (A B C G H : M) :
    secondBilinear P Q A B C G H = rationalSecondBlockDifference P Q A B C G H := by
  simp [secondBilinear, rationalSecondBlockDifference, Matrix.sub_mul]

/-- The continuous bilinear map acting by the ordered second difference. [Tropp2026, §4.3]. -/
noncomputable def rationalSecondBlockMap (P Q : 𝕜[X]) (A B C : M) : M →L[𝕜] M →L[𝕜] M :=
  LinearMap.toContinuousLinearMap <| LinearMap.toContinuousLinearMap.toLinearMap.comp
    (LinearMap.mk₂ 𝕜 (rationalSecondBlockDifference P Q A B C)
      (fun x y h => by simp only [← secondBilinear_apply, map_add, _root_.add_apply])
      (fun c x h => by simp only [← secondBilinear_apply, map_smul, _root_.smul_apply])
      (fun x h k => by simp only [← secondBilinear_apply, map_add])
      (fun c x h => by simp only [← secondBilinear_apply, map_smul]))

/-- Evaluation in two direction matrices gives their ordered block difference. -/
@[simp] theorem rationalSecondBlockMap_apply (P Q : 𝕜[X]) (A B C G H : M) :
    rationalSecondBlockMap P Q A B C G H = rationalSecondBlockDifference P Q A B C G H := rfl

private theorem rationalSecondBlockMap_eq (P Q : 𝕜[X]) (A B C : M) :
    rationalSecondBlockMap P Q A B C = secondBilinear P Q A B C := by
  ext G H i j
  simp


@[fun_prop] private theorem continuous_monomialBlockMap (k : ℕ) :
    Continuous (fun Z : M × M => monomialBlockMap Z.1 Z.2 k) := by
  unfold monomialBlockMap
  fun_prop

@[fun_prop] private theorem continuous_polynomialBlockMap (p : 𝕜[X]) :
    Continuous (fun Z : M × M => polynomialBlockMap p Z.1 Z.2) := by
  unfold polynomialBlockMap monomialBlockMap
  fun_prop

@[fun_prop] private theorem continuous_polynomialSecondBlockMap (p : 𝕜[X]) :
    Continuous (fun Z : M × M × M => polynomialSecondBlockMap p Z.1 Z.2.1 Z.2.2) := by
  unfold polynomialSecondBlockMap monomialBlockMap
  refine continuous_finsetSum _ fun k _ => ?_
  have hc : Continuous (fun Z : M × M × M => ∑ j ∈ Finset.range k,
      (compL 𝕜 M M M (mulLeftRight 𝕜 M 1 (Z.2.2 ^ j))).comp
        ((mul 𝕜 M).comp (∑ i ∈ Finset.range (k.pred - j),
          mulLeftRight 𝕜 M (Z.1 ^ ((k.pred - j).pred - i)) (Z.2.1 ^ i)))) := by
    refine continuous_finsetSum _ fun j _ => ?_
    apply Continuous.clm_comp
    · fun_prop
    · fun_prop
  convert! hc.const_smul (p.coeff k) using 1

/-- Rational matrix evaluation is continuous at each point with nonsingular denominator.
[Tropp2026, §§4.2–4.4]. -/
theorem continuousAt_rationalMatrixEval (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) : ContinuousAt (rationalMatrixEval P Q) A := by
  unfold rationalMatrixEval
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  exact (P.hasFDerivAt_aevalFDeriv A).continuousAt.mul
    ((differentiableAt_inverse (𝕜 := 𝕜) (R := M) hA).continuousAt.comp
      (f := fun X : M => aeval X Q)
      (Q.hasFDerivAt_aevalFDeriv A).continuousAt)

/-- The continuous linear first difference varies continuously on its denominator domain.
[Tropp2026, §§4.2–4.4]. -/
theorem continuousAt_rationalBlockMap (P Q : 𝕜[X]) (A B : M)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    ContinuousAt (fun Z : M × M => rationalBlockMap P Q Z.1 Z.2) (A, B) := by
  have hfa : ContinuousAt (fun Z : M × M => rationalMatrixEval P Q Z.1) (A,B) :=
    by simpa only [Function.comp_def] using
      (continuousAt_rationalMatrixEval P Q A hA).comp
        (f := fun Z : M × M => Z.1) continuous_fst.continuousAt
  have hinvB : ContinuousAt (fun X : M => Ring.inverse (aeval X Q)) B :=
    (differentiableAt_inverse (𝕜 := 𝕜) (R := M) hB).continuousAt.comp
      (f := fun X : M => aeval X Q)
      (Q.hasFDerivAt_aevalFDeriv B).continuousAt
  have hqb : ContinuousAt (fun Z : M × M => Ring.inverse (aeval Z.2 Q)) (A,B) := by
    simpa only [Function.comp_def] using hinvB.comp
      (x := (A,B)) (f := fun Z : M × M => Z.2) continuous_snd.continuousAt
  simp only [← Matrix.nonsing_inv_eq_ringInverse] at hqb
  simp_rw [rationalBlockMap_eq]
  unfold firstLinear
  fun_prop

/-- The bilinear second difference varies continuously where all three denominators are units.
[Tropp2026, §§4.2–4.4]. -/
theorem continuousAt_rationalSecondBlockMap (P Q : 𝕜[X]) (A B C : M)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    ContinuousAt (fun Z : M × M × M => rationalSecondBlockMap P Q Z.1 Z.2.1 Z.2.2)
      (A, B, C) := by
  have hfa : ContinuousAt (fun Z : M × M × M => rationalMatrixEval P Q Z.1) (A,B,C) :=
    by simpa only [Function.comp_def] using
      (continuousAt_rationalMatrixEval P Q A hA).comp
        (f := fun Z : M × M × M => Z.1) continuous_fst.continuousAt
  have hinvC : ContinuousAt (fun X : M => Ring.inverse (aeval X Q)) C :=
    (differentiableAt_inverse (𝕜 := 𝕜) (R := M) hC).continuousAt.comp
      (f := fun X : M => aeval X Q)
      (Q.hasFDerivAt_aevalFDeriv C).continuousAt
  have hqc : ContinuousAt (fun Z : M × M × M => Ring.inverse (aeval Z.2.2 Q)) (A,B,C) := by
    simpa only [Function.comp_def] using hinvC.comp
      (x := (A, B, C)) (f := fun Z : M × M × M => Z.2.2)
        (continuous_snd.comp continuous_snd).continuousAt
  simp only [← Matrix.nonsing_inv_eq_ringInverse] at hqc
  have hfirst : ContinuousAt (fun Z : M × M × M => rationalBlockMap P Q Z.1 Z.2.1)
      (A,B,C) := by
    simpa only [Function.comp_def] using
      (continuousAt_rationalBlockMap P Q A B hA hB).comp
        (x := (A,B,C)) (f := fun Z : M × M × M => (Z.1,Z.2.1))
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousAt
  simp_rw [rationalSecondBlockMap_eq]
  unfold secondBilinear bilinearComp
  fun_prop

end

section
open Polynomial Filter ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Topology
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n 𝕜

/-- Rational matrix functions have an open denominator domain. [Tropp2026, §§4.2–4.4]. -/
private theorem isOpen_rationalMatrixDomain (Q : 𝕜[X]) :
    IsOpen {A : M | IsUnit (aeval A Q)} :=
  Units.isOpen.preimage (continuous_iff_continuousAt.mpr
    (fun A => (Q.hasFDerivAt_aevalFDeriv A).continuousAt))

private theorem eventually_isUnit_aeval (Q : 𝕜[X]) (A : M) (hA : IsUnit (aeval A Q)) :
    ∀ᶠ B in 𝓝 A, IsUnit (aeval B Q) :=
  (isOpen_rationalMatrixDomain (n := n) Q).mem_nhds hA

/-- The full Fréchet derivative is the first block difference on the diagonal. [Tropp2026,
§§4.2–4.4]. -/
theorem hasFDerivAt_rationalMatrixEval (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (rationalMatrixEval P Q) (rationalBlockMap P Q A A) A := by
  apply hasFDerivAt_of_continuous_secant (L := fun B => rationalBlockMap P Q B A)
  · simpa only [Function.comp_def] using
      (continuousAt_rationalBlockMap P Q A A hA hA).comp
        (x := A) (f := fun B : M => (B,A)) (continuous_id.prodMk continuous_const).continuousAt
  · filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
    simpa only [rationalBlockMap_apply] using sub_rationalMatrixEval P Q B A hB hA

/-- Differentiating the first difference on its diagonal gives both ordered second differences, as
an operator-norm Fréchet derivative. [Tropp2026, §§4.2–4.4]. -/
theorem hasFDerivAt_rationalBlockMap_diagonal (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (fun B : M => rationalBlockMap P Q B B)
      (rationalSecondBlockMap P Q A A A + (rationalSecondBlockMap P Q A A A).flip) A := by
  let L : M → M →L[𝕜] M →L[𝕜] M := fun B =>
    rationalSecondBlockMap P Q B A B + (rationalSecondBlockMap P Q A B A).flip
  change HasFDerivAt _ (L A) A
  apply hasFDerivAt_of_continuous_secant
  · have h₁ : ContinuousAt (fun B : M => rationalSecondBlockMap P Q B A B) A := by
      simpa only [Function.comp_def] using
        (continuousAt_rationalSecondBlockMap P Q A A A hA hA hA).comp
          (x := A) (f := fun B : M => (B,A,B))
          (continuous_id.prodMk (continuous_const.prodMk continuous_id)).continuousAt
    have h₂ : ContinuousAt (fun B : M => rationalSecondBlockMap P Q A B A) A := by
      simpa only [Function.comp_def] using
        (continuousAt_rationalSecondBlockMap P Q A A A hA hA hA).comp
          (x := A) (f := fun B : M => (A,B,A))
          (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousAt
    exact h₁.add (continuous_flip_matrixBilinear.continuousAt.comp h₂)
  · filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
    ext H i j
    have h₁ := congrArg (fun D : M => D i j)
      (sub_rationalBlockDifference_left P Q B A B H hB hA hB)
    have h₂ := congrArg (fun D : M => D i j)
      (sub_rationalBlockDifference_right P Q A B A H hA hB hA)
    simp only [Matrix.sub_apply] at h₁ h₂
    simp only [sub_apply, rationalBlockMap_apply, L, add_apply, flip_apply,
      rationalSecondBlockMap_apply, Matrix.add_apply, Matrix.sub_apply]
    calc
      _ = (rationalBlockDifference P Q B B H i j - rationalBlockDifference P Q A B H i j) +
          (rationalBlockDifference P Q A B H i j - rationalBlockDifference P Q A A H i j) := by abel
      _ = _ := by rw [h₁, h₂]

/-- The actual Fréchet derivative of the rational calculus is differentiable, with Hessian the
symmetrized ordered second difference. [Tropp2026, §§4.2–4.4]. -/
theorem hasFDerivAt_fderiv_rationalMatrixEval (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (fun B : M => fderiv 𝕜 (rationalMatrixEval P Q) B)
      (rationalSecondBlockMap P Q A A A + (rationalSecondBlockMap P Q A A A).flip) A := by
  apply (hasFDerivAt_rationalBlockMap_diagonal P Q A hA).congr_of_eventuallyEq
  filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
  exact (hasFDerivAt_rationalMatrixEval P Q B hB).fderiv

/-- **Applying the actual first Fréchet derivative gives the triangular block difference.**
[Tropp2026, §§4.2–4.4].
Result: matrix-function-block-divided-differences -/
theorem fderiv_rationalMatrixEval_apply (P Q : 𝕜[X]) (A H : M)
    (hA : IsUnit (aeval A Q)) :
    fderiv 𝕜 (rationalMatrixEval P Q) A H = rationalBlockDifference P Q A A H := by
  rw [(hasFDerivAt_rationalMatrixEval P Q A hA).fderiv, rationalBlockMap_apply]

/-- **The actual second Fréchet derivative is the sum of the two ordered second block
differences.** [Tropp2026, §§4.2–4.4].
Result: matrix-function-block-divided-differences -/
theorem fderiv_fderiv_rationalMatrixEval_apply (P Q : 𝕜[X]) (A G H : M)
    (hA : IsUnit (aeval A Q)) :
    fderiv 𝕜 (fun B : M => fderiv 𝕜 (rationalMatrixEval P Q) B) A G H =
      rationalSecondBlockDifference P Q A A A G H +
        rationalSecondBlockDifference P Q A A A H G := by
  rw [(hasFDerivAt_fderiv_rationalMatrixEval P Q A hA).fderiv,
    _root_.add_apply, _root_.add_apply, ContinuousLinearMap.flip_apply,
    rationalSecondBlockMap_apply, rationalSecondBlockMap_apply]

end

end NLAlib
