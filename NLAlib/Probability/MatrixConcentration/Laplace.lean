/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.Probability.Measurability.Matrix

/-!
# The matrix Laplace transform method

For a random Hermitian matrix `Y`, the tail of its largest eigenvalue is bounded by the trace of
its matrix moment generating function, `P(t ≤ λ_max Y) ≤ e^{-θ t} E tr exp (θ Y)` for `θ > 0`, and
its mean by `θ⁻¹ log E tr exp (θ Y)` (Tropp 2015, Proposition 3.2.1). The smallest eigenvalue,
`eigenvalue Y k` with `k + 1 = card n`, is handled with `θ < 0`. The eigenvalue and spectral norm of
an integrable random matrix are integrable, so the means here are not junk values.

## Main results

* `NLAlib.measureReal_eigenvalue_zero_ge_le`, `NLAlib.measureReal_eigenvalue_le_le`: the tails.
* `NLAlib.integral_eigenvalue_zero_le`, `NLAlib.le_integral_eigenvalue`: the means.
* `NLAlib.integrable_eigenvalue`, `NLAlib.integrable_specNorm`.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], §3.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {Y : Ω → Matrix n n 𝕜}

/-- An eigenvalue of an integrable random matrix is integrable. -/
theorem integrable_eigenvalue (hY : Integrable Y μ) (k : ℕ) :
    Integrable (fun ω => eigenvalue (Y ω) k) μ := by
  refine Integrable.mono' hY.norm
    ((measurable_eigenvalue k).comp_aemeasurable hY.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, ← specNorm_eq_norm]
  by_cases h : (Y ω).IsHermitian
  · exact h.abs_eigenvalue_le_specNorm k
  · rw [eigenvalue_of_not_isHermitian h, abs_zero]
    exact specNorm_nonneg _

/-- The spectral norm of an integrable random matrix is integrable. -/
theorem integrable_specNorm {m : Type*} [Fintype m] {S : Ω → Matrix m n 𝕜} (hS : Integrable S μ) :
    Integrable (fun ω => specNorm (S ω)) μ := by
  simp only [specNorm_eq_norm]
  exact hS.norm

/-- `exp (θ λ_j(A)) ≤ tr exp (θ A)` for a Hermitian `A`, any real `θ` and any valid index `j`. -/
private theorem exp_mul_eigenvalue_le_re_trace_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (θ : ℝ) {j : ℕ} (hj : j < Fintype.card n) :
    Real.exp (θ * eigenvalue A j) ≤ RCLike.re (exp (θ • A)).trace := by
  have hθA : (θ • A).IsHermitian := (IsSelfAdjoint.all θ).smul hA
  rw [hθA.exp_eq_cfc, ← cfc_comp_smul θ Real.exp A, hA.re_trace_cfc]
  exact Finset.single_le_sum (f := fun i => Real.exp (θ • eigenvalue A i))
    (fun i _ => (Real.exp_pos _).le) (Finset.mem_range.mpr hj)

/-- `tr exp (θ A)` is positive for a Hermitian `A` with an eigenvalue index `j`. -/
private theorem re_trace_exp_smul_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) (θ : ℝ)
    {j : ℕ} (hj : j < Fintype.card n) : 0 ≤ RCLike.re (exp (θ • A)).trace :=
  (Real.exp_pos _).le.trans (exp_mul_eigenvalue_le_re_trace_exp hA θ hj)

variable [IsProbabilityMeasure μ]

/-- Markov's inequality in the form `P(s) ≤ e^{-c} E f` when `e^c ≤ f` on `s`. -/
private theorem measureReal_le_exp_neg_mul_integral {f : Ω → ℝ} {s : Set Ω} (hnn : 0 ≤ᵐ[μ] f)
    (hf : Integrable f μ) {c : ℝ} (hs : ∀ᵐ ω ∂μ, ω ∈ s → Real.exp c ≤ f ω) :
    μ.real s ≤ Real.exp (-c) * ∫ ω, f ω ∂μ := by
  have hM := mul_meas_ge_le_integral_of_nonneg hnn hf (Real.exp c)
  have hmono : μ.real s ≤ μ.real {ω | Real.exp c ≤ f ω} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
  calc μ.real s ≤ μ.real {ω | Real.exp c ≤ f ω} := hmono
    _ = Real.exp (-c) * (Real.exp c * μ.real {ω | Real.exp c ≤ f ω}) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-c) * ∫ ω, f ω ∂μ := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le

/-- Jensen's inequality for the exponential: `exp (E Z) ≤ E f` when `exp Z ≤ f`. -/
private theorem exp_integral_le {Z f : Ω → ℝ} (hZ : Integrable Z μ) (hf : Integrable f μ)
    (hle : ∀ᵐ ω ∂μ, Real.exp (Z ω) ≤ f ω) : Real.exp (∫ ω, Z ω ∂μ) ≤ ∫ ω, f ω ∂μ := by
  have hgi : Integrable (Real.exp ∘ Z) μ := by
    refine hf.mono' (Real.continuous_exp.comp_aestronglyMeasurable hZ.aestronglyMeasurable) ?_
    filter_upwards [hle] with ω hω
    rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hω
  refine (ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hZ hgi).trans ?_
  exact integral_mono_ae hgi hf hle

/-- **The matrix Laplace transform bound** for the largest eigenvalue ([Tropp2015],
Proposition 3.2.1). -/
theorem measureReal_eigenvalue_zero_ge_le [Nonempty n] (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (t : ℝ) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤
      Real.exp (-θ * t) * ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ := by
  rw [neg_mul]
  refine measureReal_le_exp_neg_mul_integral
    (hY.mono fun ω hω => re_trace_exp_smul_nonneg hω θ Fintype.card_pos) hint ?_
  filter_upwards [hY] with ω hω ht
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hθ.le)).trans
    (exp_mul_eigenvalue_le_re_trace_exp hω θ Fintype.card_pos)

/-- The matrix Laplace transform bound for the smallest eigenvalue, with `θ < 0`. -/
theorem measureReal_eigenvalue_le_le (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {k : ℕ}
    (hk : k + 1 = Fintype.card n) {θ : ℝ} (hθ : θ < 0)
    (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ) (t : ℝ) :
    μ.real {ω | eigenvalue (Y ω) k ≤ t} ≤
      Real.exp (-θ * t) * ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ := by
  have hkn : k < Fintype.card n := by omega
  rw [neg_mul]
  refine measureReal_le_exp_neg_mul_integral
    (hY.mono fun ω hω => re_trace_exp_smul_nonneg hω θ hkn) hint ?_
  filter_upwards [hY] with ω hω ht
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht hθ.le)).trans
    (exp_mul_eigenvalue_le_re_trace_exp hω θ hkn)

/-- The matrix Laplace transform bound for the mean of the largest eigenvalue. -/
theorem integral_eigenvalue_zero_le [Nonempty n] (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hYi : Integrable Y μ) {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ) :
    ∫ ω, eigenvalue (Y ω) 0 ∂μ ≤ θ⁻¹ * Real.log (∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ) := by
  have h := exp_integral_le ((integrable_eigenvalue hYi 0).const_mul θ) hint
    (hY.mono fun ω hω => exp_mul_eigenvalue_le_re_trace_exp hω θ Fintype.card_pos)
  rw [integral_const_mul] at h
  rw [le_inv_mul_iff₀ hθ, Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le h)]
  exact h

/-- The matrix Laplace transform bound for the mean of the smallest eigenvalue, with `θ < 0`. -/
theorem le_integral_eigenvalue (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hYi : Integrable Y μ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {θ : ℝ} (hθ : θ < 0)
    (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ) :
    θ⁻¹ * Real.log (∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ) ≤ ∫ ω, eigenvalue (Y ω) k ∂μ := by
  have hkn : k < Fintype.card n := by omega
  have h := exp_integral_le ((integrable_eigenvalue hYi k).const_mul θ) hint
    (hY.mono fun ω hω => exp_mul_eigenvalue_le_re_trace_exp hω θ hkn)
  rw [integral_const_mul] at h
  have hlog : θ * ∫ ω, eigenvalue (Y ω) k ∂μ ≤
      Real.log (∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ) :=
    (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le h)).mpr h
  calc θ⁻¹ * Real.log (∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ)
      ≤ θ⁻¹ * (θ * ∫ ω, eigenvalue (Y ω) k ∂μ) :=
        mul_le_mul_of_nonpos_left hlog (inv_nonpos.mpr hθ.le)
    _ = ∫ ω, eigenvalue (Y ω) k ∂μ := by rw [← mul_assoc, inv_mul_cancel₀ hθ.ne, one_mul]

end NLAlib
