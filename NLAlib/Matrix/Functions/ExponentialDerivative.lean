/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.ForMathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The exponential insertion integral

Perturbations of the exponential of a general matrix need not commute with its argument.
Left and right exponential factors propagate the perturbation through the time interval.

## Main results

* `NLAlib.exp_sub_exp_eq_integral`: the finite difference.
* `NLAlib.fderiv_exp_apply`: the Fréchet derivative in any matrix direction.
-/

@[expose] public section

open Matrix Filter MeasureTheory NormedSpace
open scoped Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable local instance : NormedAlgebra ℝ (Matrix n n 𝕜) :=
  Matrix.l2OpNormedAlgebraReal

private noncomputable local instance : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ ℝ _

/-- The exact exponential difference as a noncommutative insertion integral.
[Higham2008, Chapter 10]. -/
theorem exp_sub_exp_eq_integral (A B : Matrix n n 𝕜) :
    exp A - exp B =
      ∫ t : ℝ in 0..1, exp ((1 - t) • A) * (A - B) * exp (t • B) := by
  let F (t : ℝ) := exp ((1 - t) • A) * exp (t • B)
  let G (t : ℝ) := exp ((1 - t) • A) * (A - B) * exp (t • B)
  have hder (t : ℝ) : HasDerivAt F (-G t) t := by
    have hleft := (hasDerivAt_exp_smul_const A (1 - t)).scomp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
    have hright := hasDerivAt_exp_smul_const' B t
    convert! hleft.mul hright using 1
    change -G t = _
    simp only [G, neg_smul, one_smul, zero_sub]
    noncomm_ring
  have hcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hder t) (hcont.neg.intervalIntegrable 0 1)
  simp only [F, zero_smul, sub_zero, one_smul, sub_self,
    NormedSpace.exp_zero, one_mul, mul_one, intervalIntegral.integral_neg] at hi
  change NormedSpace.exp A - NormedSpace.exp B = _
  exact neg_injective (by simpa only [neg_sub] using hi.symm)

/-- **Fréchet derivative of the exponential.** For arbitrary real or complex square matrices the
derivative in a direction is its integral between left and right exponential factors.
[Higham2008, Chapter 10].
Result: matrix-exponential-frechet-integral -/
theorem fderiv_exp_apply (A E : Matrix n n 𝕜) :
    fderiv 𝕜 exp A E =
      ∫ s : ℝ in 0..1, exp ((1 - s) • A) * E * exp (s • A) := by
  let J (t : ℝ) := ∫ s : ℝ in 0..1,
    exp ((1 - s) • (A + t • E)) * E * exp (s • A)
  have hc : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (a₀ := 0) (b₀ := 1)
    fun_prop
  have hpath : HasDerivAt (fun t : ℝ => A + t • E) E 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const E).const_add A
  have hd : HasDerivAt (fun t : ℝ => exp (A + t • E))
      (fderiv 𝕜 exp A E) 0 := by
    have h := (NormedSpace.exp_analytic (𝕂 := 𝕜) A).differentiableAt.hasFDerivAt
    exact (h.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hpath (by simp)
  have heq : (fun t : ℝ => t⁻¹ • (exp (A + (0 + t) • E) - exp (A + (0 : ℝ) • E)))
      =ᶠ[𝓝[>] 0] J := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [zero_add, zero_smul, add_zero]
    rw [exp_sub_exp_eq_integral]
    have he : A + t • E - A = t • E := by abel
    rw [he]
    have hint : (∫ s : ℝ in 0..1, exp ((1 - s) • (A + t • E)) *
        (t • E) * exp (s • A)) = t • J t := by
      simp only [J, Matrix.mul_smul, Matrix.smul_mul, intervalIntegral.integral_smul]
    rw [hint, inv_smul_smul₀ ht0]
  have hj : Tendsto J (𝓝[>] 0) (𝓝 (J 0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := hd.tendsto_slope_zero_right.congr' heq
  have he := tendsto_nhds_unique hlim hj
  simpa [J] using he

end NLAlib
