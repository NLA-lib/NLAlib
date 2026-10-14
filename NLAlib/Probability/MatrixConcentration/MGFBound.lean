/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.Subadditivity

/-!
# Matrix moment generating function bounds and the master bounds

`NLAlib.HasMatrixMGFBound X g A s μ` says that the random matrix `X` is almost surely Hermitian
and that `E exp (θ X) ≤ exp (g θ • A)` in the Loewner order for every `θ ∈ s`, with `A` Hermitian.
Bounded positive semidefinite summands (Chernoff), bounded centred summands (Bernstein) and a
sub-Gaussian scalar times a fixed Hermitian matrix (series) all have such bounds. For independent
summands with these bounds, the trace of the matrix moment generating function of the sum is at
most `tr exp (g θ ∑ A k)` (through the subadditivity of matrix cumulant generating functions and
the operator monotonicity of the logarithm), which gives the master tail and mean bounds.

The bound is not monotone in `A`: the matrix exponential is not operator monotone. Monotonicity
in `A` holds after the trace (`NLAlib.re_trace_exp_le_re_trace_exp_of_le`), which is where the
consumers use it.

## Main definitions

* `NLAlib.HasMatrixMGFBound X g A s μ`.

## Main results

* `NLAlib.HasMatrixMGFBound.integral_re_trace_exp_sum_le`: the trace-level master bound.
* `NLAlib.HasMatrixMGFBound.measure_eigenvalue_zero_sum_ge_le`: the master tail bound.
* `NLAlib.HasMatrixMGFBound.integral_eigenvalue_zero_sum_le`: the master bound for the mean.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], §3.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The random matrix `X` is almost surely Hermitian and its matrix moment generating function is
bounded by `exp (g θ • A)` in the Loewner order for every `θ ∈ s`, with `A` Hermitian. -/
structure HasMatrixMGFBound (X : Ω → Matrix n n 𝕜) (g : ℝ → ℝ) (A : Matrix n n 𝕜) (s : Set ℝ)
    (μ : Measure Ω) : Prop where
  /-- `X` is almost surely Hermitian. -/
  ae_isHermitian : ∀ᵐ ω ∂μ, (X ω).IsHermitian
  /-- The bounding matrix is Hermitian. -/
  isHermitian_bound : A.IsHermitian
  /-- `exp (θ X)` is integrable for `θ ∈ s`. -/
  integrable_exp : ∀ θ ∈ s, Integrable (fun ω => exp (θ • X ω)) μ
  /-- The bound on the matrix moment generating function. -/
  integral_exp_le : ∀ θ ∈ s, ∫ ω, exp (θ • X ω) ∂μ ≤ exp (g θ • A)

namespace HasMatrixMGFBound

variable {X : Ω → Matrix n n 𝕜} {g : ℝ → ℝ} {A : Matrix n n 𝕜} {s : Set ℝ}

/-- A random matrix with a matrix MGF bound at some `θ ≠ 0` is almost everywhere measurable. -/
theorem aemeasurable (h : HasMatrixMGFBound X g A s μ) (hs : ∃ θ ∈ s, θ ≠ 0) :
    AEMeasurable X μ := by
  obtain ⟨θ, hθs, hθ⟩ := hs
  have hY : AEMeasurable (fun ω => θ • X ω) μ :=
    aemeasurable_of_integrable_exp
      (h.ae_isHermitian.mono fun ω hω => (IsSelfAdjoint.all θ).smul hω) (h.integrable_exp θ hθs)
  refine (hY.const_smul θ⁻¹).congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hθ, one_smul]

/-- The bound depends only on the almost-everywhere class of `X`. -/
theorem congr {Y : Ω → Matrix n n 𝕜} (h : HasMatrixMGFBound X g A s μ) (hXY : X =ᵐ[μ] Y) :
    HasMatrixMGFBound Y g A s μ := by
  have he : ∀ θ : ℝ, (fun ω => exp (θ • X ω)) =ᵐ[μ] fun ω => exp (θ • Y ω) := fun θ =>
    hXY.mono fun ω hω => by simp only [hω]
  refine ⟨?_, h.isHermitian_bound, fun θ hθ => (h.integrable_exp θ hθ).congr (he θ),
    fun θ hθ => ?_⟩
  · filter_upwards [h.ae_isHermitian, hXY] with ω h1 h2
    rwa [← h2]
  · rw [← integral_congr_ae (he θ)]
    exact h.integral_exp_le θ hθ

/-- A bound on a set holds on every subset. -/
theorem mono_set (h : HasMatrixMGFBound X g A s μ) {s' : Set ℝ} (hs : s' ⊆ s) :
    HasMatrixMGFBound X g A s' μ :=
  ⟨h.ae_isHermitian, h.isHermitian_bound, fun θ hθ => h.integrable_exp θ (hs hθ),
    fun θ hθ => h.integral_exp_le θ (hs hθ)⟩

/-- The bound for `-X`, which gives the lower tails. -/
theorem neg (h : HasMatrixMGFBound X g A s μ) :
    HasMatrixMGFBound (fun ω => -X ω) (fun θ => g (-θ)) A (-s) μ := by
  have he : ∀ (θ : ℝ) (ω : Ω), θ • -X ω = (-θ) • X ω := fun θ ω => by rw [smul_neg, neg_smul]
  refine ⟨h.ae_isHermitian.mono fun ω hω => hω.neg, h.isHermitian_bound, fun θ hθ => ?_,
    fun θ hθ => ?_⟩
  · simp only [he]
    exact h.integrable_exp (-θ) hθ
  · simp only [he]
    exact h.integral_exp_le (-θ) hθ

variable {ι : Type*} {X : ι → Ω → Matrix n n 𝕜} {A : ι → Matrix n n 𝕜}

/-- The summands `θ • X k` are independent, almost surely Hermitian, with integrable
exponentials. -/
private theorem smul_family (hind : iIndepFun X μ) (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ)
    {θ : ℝ} (hθ : θ ∈ s) :
    iIndepFun (fun k ω => θ • X k ω) μ ∧ (∀ k, ∀ᵐ ω ∂μ, (θ • X k ω).IsHermitian) ∧
      ∀ k, Integrable (fun ω => exp (θ • X k ω)) μ :=
  ⟨hind.comp (fun _ M => θ • M) fun _ => (continuous_const_smul θ).measurable,
    fun k => (h k).ae_isHermitian.mono fun _ hω => (IsSelfAdjoint.all θ).smul hω,
    fun k => (h k).integrable_exp θ hθ⟩

variable [Fintype ι]

/-- The trace exponential of `θ` times a sum of independent summands with matrix MGF bounds is
integrable. -/
theorem integrable_re_trace_exp_sum (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθ : θ ∈ s) :
    Integrable (fun ω => RCLike.re (exp (θ • ∑ k, X k ω)).trace) μ := by
  obtain ⟨h1, h2, h3⟩ := smul_family hind h hθ
  simpa only [Finset.smul_sum] using NLAlib.integrable_re_trace_exp_sum h1 h2 h3

/-- **The trace-level master bound**: `E tr exp (θ ∑ X k) ≤ tr exp (g θ • ∑ A k)` for independent
summands with matrix MGF bounds and `θ ∈ s` ([Tropp2015], §3.6). -/
theorem integral_re_trace_exp_sum_le (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθ : θ ∈ s) :
    ∫ ω, RCLike.re (exp (θ • ∑ k, X k ω)).trace ∂μ ≤ RCLike.re (exp (g θ • ∑ k, A k)).trace := by
  have := hind.isProbabilityMeasure
  obtain ⟨h1, h2, h3⟩ := smul_family hind h hθ
  have hsub := NLAlib.integral_re_trace_exp_sum_le h1 h2 h3
  simp only [← Finset.smul_sum] at hsub
  refine hsub.trans ?_
  have hlog : ∀ k, cfc Real.log (∫ ω, exp (θ • X k ω) ∂μ) ≤ g θ • A k := fun k => by
    have hpd : (∫ ω, exp (θ • X k ω) ∂μ).PosDef :=
      Matrix.posDef_integral (h3 k) ((h2 k).mono fun ω hω => hω.posDef_exp)
    have hgA : (g θ • A k).IsHermitian := (IsSelfAdjoint.all _).smul (h k).isHermitian_bound
    rw [← hgA.cfc_log_exp]
    exact hpd.cfc_log_le_cfc_log ((h k).integral_exp_le θ hθ)
  rw [Finset.smul_sum]
  exact re_trace_exp_le_re_trace_exp_of_le
    (isSelfAdjoint_sum _ fun k _ => cfc_predicate Real.log _)
    (Finset.sum_le_sum fun k _ => hlog k)

/-- The sum is almost surely Hermitian. -/
private theorem ae_isHermitian_sum (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) :
    ∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian := by
  filter_upwards [ae_all_iff.2 fun k => (h k).ae_isHermitian] with ω hω
  exact isSelfAdjoint_sum _ fun k _ => hω k

/-- **The master tail bound** ([Tropp2015], Theorem 3.6.1):
`P(t ≤ λ_max (∑ X k)) ≤ e^{-θt} tr exp (g θ • ∑ A k)` for `θ ∈ s`, `θ > 0`. -/
theorem measure_eigenvalue_zero_sum_ge_le [Nonempty n] (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθs : θ ∈ s) (hθ : 0 < θ) (t : ℝ) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Real.exp (-θ * t) * RCLike.re (exp (g θ • ∑ k, A k)).trace := by
  have := hind.isProbabilityMeasure
  exact (measureReal_eigenvalue_zero_ge_le (ae_isHermitian_sum h) hθ
    (integrable_re_trace_exp_sum hind h hθs) t).trans
    (mul_le_mul_of_nonneg_left (integral_re_trace_exp_sum_le hind h hθs) (Real.exp_pos _).le)

/-- The master tail bound in the dimension form: `≤ d e^{-θt + g θ λ_max (∑ A k)}`. -/
theorem measure_eigenvalue_zero_sum_ge_le_card_mul_exp [Nonempty n] (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθs : θ ∈ s) (hθ : 0 < θ)
    (hg : 0 ≤ g θ) (t : ℝ) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * Real.exp (-θ * t + g θ * eigenvalue (∑ k, A k) 0) := by
  have hA : (g θ • ∑ k, A k).IsHermitian :=
    (IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun k _ => (h k).isHermitian_bound)
  have htr := hA.re_trace_exp_le_card_mul_exp
  rw [eigenvalue_real_smul _ hg] at htr
  refine (measure_eigenvalue_zero_sum_ge_le hind h hθs hθ t).trans ?_
  calc Real.exp (-θ * t) * RCLike.re (exp (g θ • ∑ k, A k)).trace
      ≤ Real.exp (-θ * t) * (Fintype.card n * Real.exp (g θ * eigenvalue (∑ k, A k) 0)) :=
        mul_le_mul_of_nonneg_left htr (Real.exp_pos _).le
    _ = Fintype.card n * Real.exp (-θ * t + g θ * eigenvalue (∑ k, A k) 0) := by
        rw [Real.exp_add]
        ring

/-- An almost surely positive integrable function has a positive mean. -/
private theorem integral_pos_of_ae_pos [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    (hpos : ∀ᵐ ω ∂μ, 0 < f ω) : 0 < ∫ ω, f ω ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le) hf,
    measure_congr (Filter.eventuallyEq_univ.2 (hpos.mono fun _ h => h.ne') :
      Function.support f =ᵐ[μ] Set.univ), measure_univ]
  exact one_pos

/-- **The master bound for the mean** ([Tropp2015], Theorem 3.6.1). -/
theorem integral_eigenvalue_zero_sum_le [Nonempty n] (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) (hX : ∀ k, Integrable (X k) μ) {θ : ℝ}
    (hθs : θ ∈ s) (hθ : 0 < θ) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      θ⁻¹ * Real.log (RCLike.re (exp (g θ • ∑ k, A k)).trace) := by
  have := hind.isProbabilityMeasure
  have hint := integrable_re_trace_exp_sum hind h hθs
  have hpos : 0 < ∫ ω, RCLike.re (exp (θ • ∑ k, X k ω)).trace ∂μ :=
    integral_pos_of_ae_pos hint ((ae_isHermitian_sum h).mono fun ω hω =>
      (show (θ • ∑ k, X k ω).IsHermitian from (IsSelfAdjoint.all θ).smul hω).re_trace_exp_pos)
  refine (integral_eigenvalue_zero_le (ae_isHermitian_sum h)
    (integrable_finsetSum _ fun k _ => hX k) hθ hint).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log hpos (integral_re_trace_exp_sum_le hind h hθs)) (inv_nonneg.mpr hθ.le)

end HasMatrixMGFBound

end NLAlib
