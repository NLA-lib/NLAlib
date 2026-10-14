/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.Probability.Independence.Integration
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Probability.MatrixIntegral

/-!
# The variance of a sum of independent random matrices

For independent random matrices the cross terms of the second moment of a sum vanish once one
factor is centred: `E (∑ f (X k)) (∑ g (X k)) = ∑ E f (X k) g (X k)` when `E f (X k) = 0`. In
particular the matrix variance is additive, `E (∑ X k)² = ∑ E (X k)²` for independent centred
square-integrable `X k` (Tropp 2015, (2.2.5)), the identity that makes the variance statistic
`‖∑ E (X k)²‖` of the matrix Bernstein inequality the variance of the sum. Expectations are
Bochner integrals under `open scoped Matrix.Norms.L2Operator`
(`NLAlib/Probability/MatrixIntegral.lean`); square integrability is `MemLp _ 2 μ`, which does
not depend on the norm chosen.

## Main results

* `NLAlib.integral_sum_mul_sum_of_iIndepFun`: the cross terms vanish.
* `NLAlib.integral_sum_sq_of_iIndepFun`: `E (∑ X k)² = ∑ E (X k)²` for centred summands.
* `NLAlib.integral_sum_sub_integral_sq_of_iIndepFun`: the variance of the sum is the sum of the
  variances.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], §2.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {ι : Type*} [Fintype ι]

section Product

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Matrix multiplication as a continuous real-bilinear map. -/
private noncomputable def mulCLM : Matrix l m 𝕜 →L[ℝ] Matrix m n 𝕜 →L[ℝ] Matrix l n 𝕜 :=
  LinearMap.mkContinuous₂ (mulLinearMap ℝ) 1 fun A B => by
    rw [one_mul]
    exact Matrix.l2_opNorm_mul A B

private theorem mulCLM_apply (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) : mulCLM A B = A * B := rfl

variable {Y : Ω → Matrix l m 𝕜} {Z : Ω → Matrix m n 𝕜}

/-- The product of two square-integrable random matrices is integrable. -/
private theorem integrable_mul_of_memLp (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    Integrable (fun ω => Y ω * Z ω) μ := by
  have hm : AEStronglyMeasurable (fun ω => Y ω * Z ω) μ := by
    simpa only [mulCLM_apply] using
      (mulCLM (𝕜 := 𝕜) (l := l) (m := m) (n := n)).continuous₂.comp_aestronglyMeasurable₂ hY.1
        hZ.1
  have h := MemLp.of_bilin (p := 2) (q := 2) (r := 1)
    (fun (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) => A * B) 1 hY hZ hm
    (Filter.Eventually.of_forall fun ω => by
      simpa only [one_mul] using Matrix.l2_opNNNorm_mul (Y ω) (Z ω))
  exact memLp_one_iff_integrable.1 h

variable [IsProbabilityMeasure μ] {α : Type*} {mα : MeasurableSpace α}

/-- **The cross terms of an independent sum vanish.** For independent random variables `X k`
and measurable matrix-valued `f`, `g` with `f (X k)` and `g (X k)` square integrable and
`E f (X k) = 0`, `E (∑ f (X k)) (∑ g (X k)) = ∑ E f (X k) g (X k)`. [Tropp2015, (2.2.5)], where
`f = g = id`, for Hermitian summands; here rectangular and over any `RCLike` field.
Port of `NLAlib.integral_sum_mul_sum_eq_sum_integral_mul`, there over `ℂ` and `Fin`. -/
theorem integral_sum_mul_sum_of_iIndepFun {X : ι → Ω → α} (hind : iIndepFun X μ)
    {f : α → Matrix l m 𝕜} {g : α → Matrix m n 𝕜} (hf : Measurable f) (hg : Measurable g)
    (hfX : ∀ k, MemLp (fun ω => f (X k ω)) 2 μ) (hgX : ∀ k, MemLp (fun ω => g (X k ω)) 2 μ)
    (hf0 : ∀ k, ∫ ω, f (X k ω) ∂μ = 0) :
    ∫ ω, (∑ k, f (X k ω)) * ∑ k, g (X k ω) ∂μ = ∑ k, ∫ ω, f (X k ω) * g (X k ω) ∂μ := by
  have hint (j k : ι) : Integrable (fun ω => f (X j ω) * g (X k ω)) μ :=
    integrable_mul_of_memLp (hfX j) (hgX k)
  have hcross (j k : ι) (hjk : j ≠ k) : ∫ ω, f (X j ω) * g (X k ω) ∂μ = 0 := by
    have hind' : IndepFun (fun ω => f (X j ω)) (fun ω => g (X k ω)) μ :=
      (hind.indepFun hjk).comp hf hg
    have h := hind'.integral_bilin ((hfX j).integrable one_le_two)
      ((hgX k).integrable one_le_two) (mulCLM (𝕜 := 𝕜) (l := l) (m := m) (n := n))
    simp only [mulCLM_apply] at h
    rw [h, hf0 j, Matrix.zero_mul]
  simp only [Matrix.sum_mul, Matrix.mul_sum]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun j _ => hint j k,
    Finset.sum_eq_single k (fun j _ hjk => hcross j k hjk)
      (fun h => absurd (Finset.mem_univ k) h)]

end Product

variable [IsProbabilityMeasure μ] {n : Type*} [Fintype n] [DecidableEq n]
  {X : ι → Ω → Matrix n n 𝕜}

/-- **Additivity of the matrix variance.** For independent, centred, square-integrable random
matrices, `E (∑ X k)² = ∑ E (X k)²`. [Tropp2015, (2.2.5)], there for Hermitian summands; the
Hermitian hypothesis is not needed. -/
theorem integral_sum_sq_of_iIndepFun (hind : iIndepFun X μ) (hX : ∀ k, MemLp (X k) 2 μ)
    (hX0 : ∀ k, ∫ ω, X k ω ∂μ = 0) :
    ∫ ω, (∑ k, X k ω) ^ 2 ∂μ = ∑ k, ∫ ω, X k ω ^ 2 ∂μ := by
  simp only [sq]
  exact integral_sum_mul_sum_of_iIndepFun hind measurable_id measurable_id hX hX hX0

/-- **The variance of an independent sum is the sum of the variances**, for square-integrable
random matrices: `E (∑ X k - E ∑ X k)² = ∑ E (X k - E X k)²`. [Tropp2015, (2.2.5)], there for
Hermitian summands; the Hermitian hypothesis is not needed.
Port of `NLAlib.variance_additivity`, there over `ℂ` and `Fin`. -/
theorem integral_sum_sub_integral_sq_of_iIndepFun (hind : iIndepFun X μ)
    (hX : ∀ k, MemLp (X k) 2 μ) :
    ∫ ω, ((∑ k, X k ω) - ∫ ω', ∑ k, X k ω' ∂μ) ^ 2 ∂μ =
      ∑ k, ∫ ω, (X k ω - ∫ ω', X k ω' ∂μ) ^ 2 ∂μ := by
  set c : ι → Matrix n n 𝕜 := fun k => ∫ ω', X k ω' ∂μ
  have hXint (k : ι) : Integrable (X k) μ := (hX k).integrable one_le_two
  have hsum (ω : Ω) : (∑ k, X k ω) - ∫ ω', ∑ k, X k ω' ∂μ = ∑ k, (X k ω - c k) := by
    rw [integral_finsetSum _ fun k _ => hXint k, ← Finset.sum_sub_distrib]
  simp only [hsum]
  refine integral_sum_sq_of_iIndepFun (X := fun k ω => X k ω - c k)
    (hind.comp (fun k x => x - c k) fun k => measurable_id.sub_const _)
    (fun k => (hX k).sub (memLp_const (c k))) fun k => ?_
  rw [integral_sub (hXint k) (integrable_const _), integral_const, probReal_univ, one_smul,
    sub_self]

end NLAlib
