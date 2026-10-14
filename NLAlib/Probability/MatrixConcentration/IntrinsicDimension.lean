/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import NLAlib.Matrix.Basic.SchurComplement
public import NLAlib.Matrix.Functions.TraceFunctions
public import NLAlib.Probability.MatrixConcentration.Bernstein
public import NLAlib.Probability.MatrixConcentration.ChernoffSum
public import NLAlib.Probability.MatrixConcentration.LaplaceGeneral
public import NLAlib.Probability.Tail

/-!
# Matrix concentration in the intrinsic dimension

The matrix Chernoff and Bernstein inequalities with the ambient dimension `d` replaced by the
intrinsic dimension `intrinsicDimension V = tr V / ‖V‖ ≤ rank V` of a variance proxy `V` (Tropp
2015, chapter 7). The proxy is any deterministic `V` above the variance statistic in Loewner
order (`∑ E X k ≤ M` for Chernoff, `∑ E X k² ≤ V` for Bernstein), entering after the trace, so a
user trades `‖V‖` against `intrinsicDimension V`. The trace forms take a single random matrix with
a trace MGF bound, as `NLAlib/Probability/MatrixConcentration/Chernoff.lean` does; the
independent-sum forms are corollaries.

The bounds are better than the dimensional ones (`ChernoffSum.lean`, `Bernstein.lean`) when
`2 intdim M < d`, respectively `4 intdim V < d`, and the Bernstein tails hold only above the
threshold `t ≥ √‖V‖ + L / 3`.

## Main results

* `NLAlib.measureReal_eigenvalue_zero_ge_le_chernoff_intrinsicDim_of_integral_le`,
  `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_chernoff_intrinsicDim`,
  `NLAlib.integral_eigenvalue_zero_sum_le_chernoff_intrinsicDim`: intrinsic Chernoff.
* `NLAlib.measureReal_eigenvalue_zero_ge_le_bernstein_intrinsicDim_of_integral_le`,
  `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein_intrinsicDim`,
  `NLAlib.measureReal_specNorm_sum_ge_le_bernstein_intrinsicDim`: intrinsic Bernstein tails.
* `NLAlib.integral_eigenvalue_zero_sum_le_bernstein_intrinsicDim`,
  `NLAlib.integral_specNorm_sum_le_bernstein_intrinsicDim`: the means, with the constant
  `NLAlib.intrinsicBernsteinMeanConstant`.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι] {L : ℝ}

/-! ### Preliminaries -/

/-- The Chernoff tail base in exponential form:
`(e^s / (1 + s)^{1+s})^a = e^{(s - (1 + s) log (1 + s)) a}`. -/
private theorem chernoff_base_rpow_eq_exp {s : ℝ} (hs : 0 < 1 + s) (a : ℝ) :
    (Real.exp s / (1 + s) ^ (1 + s)) ^ a = Real.exp ((s - (1 + s) * Real.log (1 + s)) * a) := by
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hs _)),
    Real.log_div (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hs _).ne', Real.log_exp,
    Real.log_rpow hs]

/-- `δ ≤ (1 + δ) log (1 + δ)` for `δ > -1`. -/
private theorem le_one_add_mul_log_one_add {δ : ℝ} (hδ : 0 < 1 + δ) :
    δ ≤ (1 + δ) * Real.log (1 + δ) := by
  have h := Real.add_one_le_exp (-Real.log (1 + δ))
  rw [Real.exp_neg, Real.exp_log hδ] at h
  have h2 : (1 + δ) * (-Real.log (1 + δ) + 1) ≤ (1 + δ) * (1 + δ)⁻¹ :=
    mul_le_mul_of_nonneg_left h hδ.le
  rw [mul_inv_cancel₀ hδ.ne'] at h2
  linarith

/-- `e^u ≤ 4 (e^u - u - 1)` for `u ≥ 1`. -/
private theorem exp_le_four_mul_exp_sub_sub_one {u : ℝ} (hu : 1 ≤ u) :
    Real.exp u ≤ 4 * (Real.exp u - u - 1) := by
  have h1 : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have h2 : Real.exp u = Real.exp (u - 1) * Real.exp 1 := by
    rw [← Real.exp_add, sub_add_cancel]
  have h3 : u * Real.exp 1 ≤ Real.exp u := by
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos 1).le
  have he := Real.exp_one_gt_d9
  have h4 := mul_le_mul_of_nonneg_left he.le (by linarith : (0 : ℝ) ≤ u)
  linarith

/-- `r (E - 1) / (X - 1) ≤ 2 r E / X` for `r, E ≥ 0` and `X ≥ 2`. -/
private theorem mul_sub_one_div_sub_one_le {r E X : ℝ} (hr : 0 ≤ r) (hE : 0 ≤ E) (hX : 2 ≤ X) :
    r * (E - 1) / (X - 1) ≤ 2 * r * E / X := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg hr hE) (by linarith : (0 : ℝ) ≤ X - 2)]

/-- `r (E - 1) / (e^u - u - 1) ≤ 4 r E / e^u` for `r, E ≥ 0` and `u ≥ 1`. -/
private theorem mul_sub_one_div_exp_sub_le {r E u : ℝ} (hr : 0 ≤ r) (hE : 0 ≤ E) (hu : 1 ≤ u) :
    r * (E - 1) / (Real.exp u - u - 1) ≤ 4 * r * E / Real.exp u := by
  have h4 := exp_le_four_mul_exp_sub_sub_one hu
  have hX : 0 < Real.exp u - u - 1 := by linarith [Real.exp_pos u]
  rw [div_le_div_iff₀ hX (Real.exp_pos u)]
  nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hr hE),
    mul_nonneg hr (Real.exp_pos u).le]

/-- `e^{c x} - 1` is convex. -/
private theorem convexOn_exp_mul_sub_one (c : ℝ) :
    ConvexOn ℝ (Set.Ici 0) fun x : ℝ => Real.exp (c * x) - 1 := by
  refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  have h := convexOn_exp.2 (Set.mem_univ (c * x)) (Set.mem_univ (c * y)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : c * (a * x + b * y) = a * (c * x) + b * (c * y) := by ring
  rw [e]
  linear_combination h + hab

/-- Jensen's inequality for the exponential: `exp (E Z) ≤ E f` when `exp Z ≤ f`. -/
private theorem exp_integral_le_integral [IsProbabilityMeasure μ] {Z f : Ω → ℝ}
    (hZ : Integrable Z μ) (hf : Integrable f μ) (hle : ∀ᵐ ω ∂μ, Real.exp (Z ω) ≤ f ω) :
    Real.exp (∫ ω, Z ω ∂μ) ≤ ∫ ω, f ω ∂μ := by
  have hgi : Integrable (Real.exp ∘ Z) μ := by
    refine hf.mono' (Real.continuous_exp.comp_aestronglyMeasurable hZ.aestronglyMeasurable) ?_
    filter_upwards [hle] with ω hω
    rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hω
  refine (ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hZ hgi).trans ?_
  exact integral_mono_ae hgi hf hle

omit [DecidableEq n] in
/-- The intrinsic dimension of a positive semidefinite matrix is nonnegative. -/
private theorem intrinsicDimension_nonneg_of_posSemidef {V : Matrix n n 𝕜} (hV : V.PosSemidef) :
    0 ≤ intrinsicDimension V :=
  div_nonneg ((specNorm_nonneg V).trans hV.specNorm_le_re_trace) (specNorm_nonneg V)

/-- `tr exp (c A) = ∑ e^{c λ_i}` for Hermitian `A`. -/
private theorem re_trace_exp_smul_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (c : ℝ) :
    RCLike.re (exp (c • A)).trace =
      ∑ i ∈ Finset.range (Fintype.card n), Real.exp (c * eigenvalue A i) := by
  have hcA : (c • A).IsHermitian := (IsSelfAdjoint.all c).smul hA
  rw [hcA.exp_eq_cfc, ← cfc_comp_smul c Real.exp A, hA.re_trace_cfc]
  simp only [smul_eq_mul]

/-- `tr (e^{cA} - 1) = tr e^{cA} - d` for Hermitian `A`. -/
private theorem re_trace_cfc_exp_sub_one {A : Matrix n n 𝕜} (hA : A.IsHermitian) (c : ℝ) :
    RCLike.re (cfc (fun x => Real.exp (c * x) - 1) A).trace =
      RCLike.re (exp (c • A)).trace - Fintype.card n := by
  rw [hA.re_trace_cfc, re_trace_exp_smul_eq_sum hA, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]

/-- `tr (e^{cA} - cA - 1) = tr e^{cA} - c tr A - d` for Hermitian `A`. -/
private theorem re_trace_cfc_exp_sub_mul_sub_one {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (c : ℝ) :
    RCLike.re (cfc (fun x => Real.exp (c * x) - c * x - 1) A).trace =
      RCLike.re (exp (c • A)).trace - c * RCLike.re A.trace - Fintype.card n := by
  rw [hA.re_trace_cfc, re_trace_exp_smul_eq_sum hA, hA.re_trace_eq_sum_range_eigenvalue,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Finset.mul_sum]

/-- The intrinsic dimension lemma for the trace exponential:
`tr e^{cV} - d ≤ intdim V (e^{c ‖V‖} - 1)`. -/
private theorem re_trace_exp_smul_sub_card_le {V : Matrix n n 𝕜} (hV : V.PosSemidef) (c : ℝ) :
    RCLike.re (exp (c • V)).trace - Fintype.card n ≤
      intrinsicDimension V * (Real.exp (c * specNorm V) - 1) := by
  rw [← re_trace_cfc_exp_sub_one hV.isHermitian c]
  exact hV.re_trace_cfc_le_intrinsicDimension_mul (convexOn_exp_mul_sub_one c)
    (by simp only [mul_zero, Real.exp_zero, sub_self])

/-- `e^{c λ_max A} - 1 ≤ tr e^{cA} - d` for positive semidefinite `A` and `c ≥ 0`. -/
private theorem exp_mul_eigenvalue_zero_sub_one_le {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    Real.exp (c * eigenvalue A 0) - 1 ≤ RCLike.re (exp (c • A)).trace - Fintype.card n := by
  rw [← re_trace_cfc_exp_sub_one hA.isHermitian c]
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [eigenvalue_of_card_le _ (by simp), mul_zero, Real.exp_zero, sub_self,
      hA.isHermitian.re_trace_cfc]
    simp
  · exact hA.isHermitian.apply_eigenvalue_zero_le_re_trace_cfc
      (φ := fun x => Real.exp (c * x) - 1) fun x hx =>
        sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc (hA.spectrum_subset_Ici hx)))

/-! ### Chernoff -/

section Chernoff

/-- **Intrinsic-dimension matrix Chernoff, trace form**: for an almost surely positive
semidefinite `Y` with `E tr exp (θ Y) ≤ tr exp ((e^{θL} - 1)/L • V)` for every `θ > 0`, a nonzero
positive semidefinite `V` and `δ ≥ L / λ_max V`,
`P((1 + δ) λ_max V ≤ λ_max Y) ≤ 2 intdim V (e^δ / (1 + δ)^{1+δ})^{λ_max V / L}`.
[Tropp2015, Theorem 7.2.1]; there for independent sums, here from the trace bound alone, so any
`Y` with that bound (sampling without replacement) gets the tail. `V ≠ 0` is needed: at `V = 0`
the event is everything and the bound `0`. -/
theorem measureReal_eigenvalue_zero_ge_le_chernoff_intrinsicDim_of_integral_le
    [IsProbabilityMeasure μ] {Y : Ω → Matrix n n 𝕜} {V : Matrix n n 𝕜}
    (hY : ∀ᵐ ω ∂μ, (Y ω).PosSemidef) (hV : V.PosSemidef) (hV0 : V ≠ 0) (hL : 0 < L)
    (hint : ∀ θ : ℝ, 0 < θ → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ : ℝ, 0 < θ → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace)
    {δ : ℝ} (hδ : L / eigenvalue V 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue V 0 ≤ eigenvalue (Y ω) 0} ≤
      2 * intrinsicDimension V * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue V 0 / L) := by
  have hne : Nonempty n := by
    by_contra h
    exact hV0 (Matrix.ext fun i _ => (h ⟨i⟩).elim)
  have hna : specNorm V = eigenvalue V 0 := hV.specNorm_eq_eigenvalue_zero
  have hapos : 0 < eigenvalue V 0 := hna ▸
    lt_of_le_of_ne (specNorm_nonneg V) (Ne.symm (mt specNorm_eq_zero_iff.mp hV0))
  have hδa : L ≤ δ * eigenvalue V 0 := by rwa [div_le_iff₀ hapos] at hδ
  have hδ0 : 0 < δ := by
    by_contra h
    push Not at h
    nlinarith
  have h1δ : 0 < 1 + δ := by linarith
  set θ := Real.log (1 + δ) / L with hθdef
  have hθ : 0 < θ := div_pos (Real.log_pos (by linarith)) hL
  have hθL : Real.exp (θ * L) = 1 + δ := by
    rw [hθdef, div_mul_cancel₀ _ hL.ne', Real.exp_log h1δ]
  set t := (1 + δ) * eigenvalue V 0 with htdef
  have hθt : 1 ≤ θ * t := by
    have e : θ * t = (1 + δ) * Real.log (1 + δ) * eigenvalue V 0 / L := by
      rw [hθdef, htdef]
      ring
    rw [e, le_div_iff₀ hL, one_mul]
    exact hδa.trans (mul_le_mul_of_nonneg_right (le_one_add_mul_log_one_add h1δ) hapos.le)
  have hX2 : 2 ≤ Real.exp (θ * t) := by linarith [Real.add_one_le_exp (θ * t)]
  have hψY : ∀ᵐ ω ∂μ, RCLike.re (cfc (fun x => max (Real.exp (θ * x) - 1) 0) (Y ω)).trace =
      RCLike.re (exp (θ • Y ω)).trace - Fintype.card n := by
    filter_upwards [hY] with ω hω
    rw [← re_trace_cfc_exp_sub_one hω.isHermitian θ]
    congr 2
    refine cfc_congr fun x hx => max_eq_left ?_
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hθ.le (hω.spectrum_subset_Ici hx)))
  have hψint : Integrable
      (fun ω => RCLike.re (cfc (fun x => max (Real.exp (θ * x) - 1) 0) (Y ω)).trace) μ :=
    ((hint θ hθ).sub (integrable_const _)).congr (hψY.mono fun ω h => h.symm)
  have hE : ∫ ω, RCLike.re (cfc (fun x => max (Real.exp (θ * x) - 1) 0) (Y ω)).trace ∂μ ≤
      intrinsicDimension V * (Real.exp (δ / L * eigenvalue V 0) - 1) := by
    rw [integral_congr_ae hψY, integral_sub (hint θ hθ) (integrable_const _), integral_const,
      probReal_univ, one_smul]
    have h := re_trace_exp_smul_sub_card_le hV (δ / L)
    rw [hna] at h
    refine (sub_le_sub_right (htr θ hθ) _).trans ?_
    rwa [hθL, add_sub_cancel_left]
  have hlap := measureReal_eigenvalue_zero_ge_le_integral_re_trace_cfc_div
    (hY.mono fun ω h => h.isHermitian) (fun x => le_max_right _ _)
    (fun x _ y _ hxy => max_le_max (sub_le_sub_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hθ.le)) 1) le_rfl)
    hψint (by positivity : (0 : ℝ) ≤ t)
    (by rw [max_eq_left (by linarith)]; linarith : 0 < max (Real.exp (θ * t) - 1) 0)
  rw [max_eq_left (by linarith)] at hlap
  refine hlap.trans ((div_le_div_of_nonneg_right hE (by linarith)).trans ?_)
  refine (mul_sub_one_div_sub_one_le (intrinsicDimension_nonneg_of_posSemidef hV)
    (Real.exp_pos _).le hX2).trans_eq ?_
  rw [chernoff_base_rpow_eq_exp h1δ, mul_div_assoc, ← Real.exp_sub]
  congr 2
  rw [htdef, hθdef]
  field_simp

variable {X : ι → Ω → Matrix n n 𝕜}

/-- The hypotheses of the trace-form intrinsic Chernoff bound for `Y = ∑ X k` and the proxy
`M`. -/
private theorem chernoff_intrinsic_hyps [IsProbabilityMeasure μ] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {M : Matrix n n 𝕜}
    (hM : ∑ k, ∫ ω, X k ω ∂μ ≤ M) :
    (∀ᵐ ω ∂μ, (∑ k, X k ω).PosSemidef) ∧ M.PosSemidef ∧
      (∀ θ : ℝ, Integrable (fun ω => RCLike.re (exp (θ • ∑ k, X k ω)).trace) μ) ∧
      ∀ θ : ℝ, 0 ≤ θ → ∫ ω, RCLike.re (exp (θ • ∑ k, X k ω)).trace ∂μ ≤
        RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • M)).trace := by
  have h := fun k => hasMatrixMGFBound_of_posSemidef_of_le (hXm k) hL (hpsd k) (hle k)
  have hS : (∑ k, ∫ ω, X k ω ∂μ).PosSemidef :=
    Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_integral (hpsd k)
  have hMpsd : M.PosSemidef := by
    have h' := (Matrix.le_iff.mp hM).add hS
    rwa [sub_add_cancel] at h'
  refine ⟨?_, hMpsd, fun θ => HasMatrixMGFBound.integrable_re_trace_exp_sum hind h
    (Set.mem_univ θ), fun θ hθ => ?_⟩
  · filter_upwards [ae_all_iff.2 hpsd] with ω hω
    exact Matrix.posSemidef_sum _ fun k _ => hω k
  · refine (HasMatrixMGFBound.integral_re_trace_exp_sum_le hind h (Set.mem_univ θ)).trans ?_
    have hc : 0 ≤ (Real.exp (θ * L) - 1) / L :=
      div_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hθ hL.le))) hL.le
    exact re_trace_exp_le_re_trace_exp_of_le ((IsSelfAdjoint.all _).smul hS.isHermitian)
      (Matrix.le_iff.mpr (by rw [← smul_sub]; exact (Matrix.le_iff.mp hM).smul hc))

/-- **Intrinsic-dimension matrix Chernoff**: for independent random positive semidefinite
`0 ≤ X k ≤ L • 1`, a matrix `M ≠ 0` above `∑ E X k` and `δ ≥ L / λ_max M`,
`P((1 + δ) λ_max M ≤ λ_max (∑ X k)) ≤ 2 intdim M (e^δ / (1 + δ)^{1+δ})^{λ_max M / L}`.
[Tropp2015, Theorem 7.2.1]; here with any upper bound `M` in Loewner order in place of
`∑ E X k`. Better than `measureReal_eigenvalue_zero_sum_ge_le_chernoff` when
`2 intdim M < card n`, but only for `δ ≥ L / λ_max M`.
Result: intrinsic-matrix-chernoff -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff_intrinsicDim (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {M : Matrix n n 𝕜}
    (hM : ∑ k, ∫ ω, X k ω ∂μ ≤ M) (hM0 : M ≠ 0) {δ : ℝ} (hδ : L / eigenvalue M 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue M 0 ≤ eigenvalue (∑ k, X k ω) 0} ≤
      2 * intrinsicDimension M * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue M 0 / L) := by
  have := hind.isProbabilityMeasure
  obtain ⟨hY, hMpsd, hint, htr⟩ := chernoff_intrinsic_hyps hind hXm hL hpsd hle hM
  exact measureReal_eigenvalue_zero_ge_le_chernoff_intrinsicDim_of_integral_le
    (Y := fun ω => ∑ k, X k ω) hY hMpsd hM0 hL (fun θ _ => hint θ) (fun θ hθ => htr θ hθ.le) hδ

/-- **Intrinsic-dimension matrix Chernoff for the mean**: for independent random positive
semidefinite `0 ≤ X k ≤ L • 1`, a matrix `M` above `∑ E X k` and every `θ > 0`,
`E λ_max (∑ X k) ≤ (e^θ - 1)/θ · λ_max M + L/θ · log (2 intdim M)`.
[Tropp2015, Theorem 7.2.1]; here with any upper bound `M` in Loewner order and a free `θ`. No
`M ≠ 0`: at `M = 0` both sides are `0` (`Real.log 0 = 0`). Proof: for positive semidefinite `Y`,
`e^{s λ_max Y} - 1 ≤ tr (e^{s Y} - 1)`; Jensen; the trace bound at `s = θ / L` and monotonicity
after the trace; the intrinsic dimension lemma
(`Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul`); then
`1 + d (e^a - 1) ≤ 2 d e^a` from `Matrix.PosSemidef.one_le_intrinsicDimension` (case split on
`M = 0`).
Result: intrinsic-matrix-chernoff -/
theorem integral_eigenvalue_zero_sum_le_chernoff_intrinsicDim (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {M : Matrix n n 𝕜}
    (hM : ∑ k, ∫ ω, X k ω ∂μ ≤ M) {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      (Real.exp θ - 1) / θ * eigenvalue M 0 + L / θ * Real.log (2 * intrinsicDimension M) := by
  have := hind.isProbabilityMeasure
  obtain ⟨hY, hMpsd, hint, htr⟩ := chernoff_intrinsic_hyps hind hXm hL hpsd hle hM
  have hYi : Integrable (fun ω => ∑ k, X k ω) μ :=
    integrable_finsetSum _ fun k _ => integrable_of_posSemidef_of_le (hXm k) (hpsd k) (hle k)
  have hna : specNorm M = eigenvalue M 0 := hMpsd.specNorm_eq_eigenvalue_zero
  have hs : 0 < θ / L := div_pos hθ hL
  have hsL : θ / L * L = θ := div_mul_cancel₀ θ hL.ne'
  have hJ : Real.exp (θ / L * ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ) ≤
      1 + intrinsicDimension M * (Real.exp ((Real.exp θ - 1) / L * eigenvalue M 0) - 1) := by
    have hW : Integrable (fun ω => RCLike.re (exp ((θ / L) • ∑ k, X k ω)).trace -
        (Fintype.card n : ℝ)) μ := (hint _).sub (integrable_const _)
    have hf : Integrable (fun ω => 1 + (RCLike.re (exp ((θ / L) • ∑ k, X k ω)).trace -
        (Fintype.card n : ℝ))) μ := (integrable_const 1).add hW
    have h1 := exp_integral_le_integral ((integrable_eigenvalue hYi 0).const_mul (θ / L)) hf
      (hY.mono fun ω hω => by linarith [exp_mul_eigenvalue_zero_sub_one_le hω hs.le])
    rw [integral_const_mul] at h1
    refine h1.trans ?_
    rw [integral_add (integrable_const _) hW, integral_sub (hint _) (integrable_const _),
      integral_const, integral_const, probReal_univ, one_smul, one_smul]
    have h2 := re_trace_exp_smul_sub_card_le hMpsd ((Real.exp θ - 1) / L)
    have h3 := htr (θ / L) hs.le
    rw [hsL] at h3
    rw [hna] at h2
    linarith
  rcases eq_or_ne M 0 with rfl | hM0
  · have hr0 : intrinsicDimension (0 : Matrix n n 𝕜) = 0 := by
      rw [intrinsicDimension, specNorm_zero, div_zero]
    rw [hr0, zero_mul, add_zero, Real.exp_le_one_iff] at hJ
    rw [eigenvalue_zero, hr0, mul_zero, mul_zero, Real.log_zero, mul_zero, add_zero]
    nlinarith
  · have hr1 : 1 ≤ intrinsicDimension M := hMpsd.one_le_intrinsicDimension hM0
    have hga : 0 ≤ (Real.exp θ - 1) / L * eigenvalue M 0 :=
      mul_nonneg (div_nonneg (sub_nonneg.mpr (Real.one_le_exp hθ.le)) hL.le)
        (hMpsd.eigenvalue_nonneg 0)
    have h2 : 1 + intrinsicDimension M * (Real.exp ((Real.exp θ - 1) / L * eigenvalue M 0) - 1) ≤
        2 * intrinsicDimension M * Real.exp ((Real.exp θ - 1) / L * eigenvalue M 0) := by
      nlinarith [Real.one_le_exp hga]
    have hlog := Real.log_le_log (Real.exp_pos _) (hJ.trans h2)
    rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
    calc ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ
        = L / θ * (θ / L * ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ) := by
          field_simp
      _ ≤ L / θ * (Real.log (2 * intrinsicDimension M) +
          (Real.exp θ - 1) / L * eigenvalue M 0) :=
          mul_le_mul_of_nonneg_left hlog (div_nonneg hL.le hθ.le)
      _ = (Real.exp θ - 1) / θ * eigenvalue M 0 + L / θ * Real.log (2 * intrinsicDimension M) := by
          field_simp
          ring

end Chernoff

/-! ### Bernstein -/

section Bernstein

/-- The generalised Laplace bound with `ψ a = e^{θa} - θa - 1` for a centred `Y` with a trace
bound `E tr e^{θY} ≤ tr e^{cV}`. -/
private theorem bernstein_intrinsic_core [IsProbabilityMeasure μ] {Y : Ω → Matrix n n 𝕜}
    {V : Matrix n n 𝕜} (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hYi : Integrable Y μ)
    (hmean : ∫ ω, Y ω ∂μ = 0) (hV : V.PosSemidef) {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ) {c : ℝ}
    (htr : ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤ RCLike.re (exp (c • V)).trace)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤
      intrinsicDimension V * (Real.exp (c * specNorm V) - 1) /
        (Real.exp (θ * t) - θ * t - 1) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : ∀ A : Matrix n n 𝕜, eigenvalue A 0 = 0 := fun A =>
      eigenvalue_of_card_le A (by simp)
    have hempty : {ω | t ≤ eigenvalue (Y ω) 0} = ∅ := by
      ext ω
      simp only [h0, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact ht
    have hr : intrinsicDimension V = 0 := by
      rw [intrinsicDimension, Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty, map_zero,
        zero_div]
    rw [hempty, measureReal_empty, hr, zero_mul, zero_div]
  have hψ0 : ∀ x, 0 ≤ Real.exp (θ * x) - θ * x - 1 := fun x => by
    linarith [Real.add_one_le_exp (θ * x)]
  have hψm : MonotoneOn (fun x => Real.exp (θ * x) - θ * x - 1) (Set.Ici 0) :=
    fun x hx y _ hxy => by
      have h1 : Real.exp (θ * y) = Real.exp (θ * x) * Real.exp (θ * (y - x)) := by
        rw [← Real.exp_add]
        ring_nf
      have h2 := Real.add_one_le_exp (θ * (y - x))
      have h3 : 1 ≤ Real.exp (θ * x) := Real.one_le_exp (mul_nonneg hθ.le hx)
      have h4 : 0 ≤ θ * (y - x) := mul_nonneg hθ.le (sub_nonneg.mpr hxy)
      simp only
      rw [h1]
      nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (θ * x)).le,
        mul_nonneg (sub_nonneg.mpr h3) h4]
  have hψY : ∀ᵐ ω ∂μ, RCLike.re (cfc (fun x => Real.exp (θ * x) - θ * x - 1) (Y ω)).trace =
      RCLike.re (exp (θ • Y ω)).trace - θ * RCLike.re (Y ω).trace - Fintype.card n := by
    filter_upwards [hY] with ω hω
    exact re_trace_cfc_exp_sub_mul_sub_one hω θ
  have hYtr : Integrable (fun ω => (Y ω).trace) μ :=
    (Matrix.traceLinearMap n ℝ 𝕜).toContinuousLinearMap.integrable_comp hYi
  have htrI : Integrable (fun ω => RCLike.re (Y ω).trace) μ := hYtr.re
  have htr0 : ∫ ω, RCLike.re (Y ω).trace ∂μ = 0 := by
    rw [integral_re hYtr, Matrix.integral_trace hYi, hmean, Matrix.trace_zero, map_zero]
  have hA : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace -
      θ * RCLike.re (Y ω).trace) μ := hint.sub (htrI.const_mul θ)
  have hψint : Integrable
      (fun ω => RCLike.re (cfc (fun x => Real.exp (θ * x) - θ * x - 1) (Y ω)).trace) μ :=
    (hA.sub (integrable_const _)).congr (hψY.mono fun ω h => h.symm)
  have hE : ∫ ω, RCLike.re (cfc (fun x => Real.exp (θ * x) - θ * x - 1) (Y ω)).trace ∂μ ≤
      intrinsicDimension V * (Real.exp (c * specNorm V) - 1) := by
    rw [integral_congr_ae hψY, integral_sub hA (integrable_const _),
      integral_sub hint (htrI.const_mul θ), integral_const_mul, htr0, mul_zero, sub_zero,
      integral_const, probReal_univ, one_smul]
    exact (sub_le_sub_right htr _).trans (re_trace_exp_smul_sub_card_le hV c)
  have hψt : 0 < Real.exp (θ * t) - θ * t - 1 := by
    linarith [Real.add_one_lt_exp (mul_pos hθ ht).ne']
  exact (measureReal_eigenvalue_zero_ge_le_integral_re_trace_cfc_div hY hψ0 hψm hψint ht.le
    hψt).trans (div_le_div_of_nonneg_right hE hψt.le)

/-- **Intrinsic-dimension matrix Bernstein, trace form**: for a centred, integrable, almost
surely Hermitian `Y` with `E tr exp (θ Y) ≤ tr exp (θ²/2/(1 - Lθ/3) • V)` for `θ ∈ (0, 3/L)`, a
positive semidefinite `V`, and `t ≥ √‖V‖ + L/3`,
`P(t ≤ λ_max Y) ≤ 4 intdim V exp (-(t²/2) / (‖V‖ + L t / 3))`.
[Tropp2015, Theorem 7.7.1]; here from the trace bound alone. No `V ≠ 0`: at `V = 0` the bound
`0` holds because `E tr (e^{θY} - θY - 1) ≤ 0` forces `Y = 0` almost surely. -/
theorem measureReal_eigenvalue_zero_ge_le_bernstein_intrinsicDim_of_integral_le
    [IsProbabilityMeasure μ] {Y : Ω → Matrix n n 𝕜} {V : Matrix n n 𝕜}
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hYi : Integrable Y μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (hV : V.PosSemidef) (hL : 0 < L)
    (hint : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) →
      Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • V)).trace)
    {t : ℝ} (ht : √(specNorm V) + L / 3 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤
      4 * intrinsicDimension V * Real.exp (-(t ^ 2 / 2) / (specNorm V + L * t / 3)) := by
  have hv : 0 ≤ specNorm V := specNorm_nonneg V
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  rcases hv.eq_or_lt with hv0 | hvpos
  · have hr : intrinsicDimension V = 0 := by rw [intrinsicDimension, ← hv0, div_zero]
    have hθ : 3 / (2 * L) ∈ Set.Ioo 0 (3 / L) :=
      ⟨by positivity, by rw [div_lt_div_iff₀ (by positivity) hL]; nlinarith⟩
    refine (bernstein_intrinsic_core hY hYi hmean hV hθ.1 (hint _ hθ) (htr _ hθ) ht0).trans ?_
    rw [hr, zero_mul, zero_div, mul_zero, zero_mul]
  generalize hD : specNorm V + L * t / 3 = D
  have hD0 : 0 < D := by rw [← hD]; positivity
  have hθ : t / D ∈ Set.Ioo 0 (3 / L) :=
    ⟨div_pos ht0 hD0, by rw [div_lt_div_iff₀ hD0 hL, ← hD]; linarith⟩
  have hq : 1 - L * (t / D) / 3 = specNorm V / D := by
    rw [eq_div_iff hD0.ne', sub_mul, one_mul, ← hD]
    field_simp
    ring
  have hsq : √(specNorm V) ≤ t := le_trans (by linarith) ht
  have htD : D ≤ t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left ht ht0.le
    have h2 := mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg (specNorm V))
    have h3 := Real.mul_self_sqrt hv
    rw [← hD]
    nlinarith
  have hu : 1 ≤ t / D * t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hD0, one_mul]
    nlinarith
  refine (bernstein_intrinsic_core hY hYi hmean hV hθ.1 (hint _ hθ) (htr _ hθ) ht0).trans ?_
  refine (mul_sub_one_div_exp_sub_le (intrinsicDimension_nonneg_of_posSemidef hV)
    (Real.exp_pos _).le hu).trans_eq ?_
  rw [mul_div_assoc, ← Real.exp_sub, hq]
  congr 2
  field_simp
  ring

/-- The hypotheses of the trace-form intrinsic Bernstein bound for `Y = ∑ X k`. -/
private theorem bernstein_intrinsic_hyps [IsProbabilityMeasure μ] {X : ι → Ω → Matrix n n 𝕜}
    (hind : iIndepFun X μ) (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ)
    (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0) (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜))
    {V : Matrix n n 𝕜} (hV : ∑ k, ∫ ω, X k ω ^ 2 ∂μ ≤ V) :
    (∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian) ∧ Integrable (fun ω => ∑ k, X k ω) μ ∧
      ∫ ω, ∑ k, X k ω ∂μ = 0 ∧ V.PosSemidef ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) →
        Integrable (fun ω => RCLike.re (exp (θ • ∑ k, X k ω)).trace) μ) ∧
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) → ∫ ω, RCLike.re (exp (θ • ∑ k, X k ω)).trace ∂μ ≤
        RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • V)).trace := by
  have h := fun k => hasMatrixMGFBound_of_integral_eq_zero_of_le hL (hX2 k) (hmean k) (hle k)
  have hXi := fun k => (hX2 k).integrable one_le_two
  have hS : (∑ k, ∫ ω, X k ω ^ 2 ∂μ).PosSemidef :=
    Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_integral
      ((h k).ae_isHermitian.mono fun ω hω => by
        rw [sq]
        nth_rewrite 1 [← hω.eq]
        exact Matrix.posSemidef_conjTranspose_mul_self _)
  have hVpsd : V.PosSemidef := by
    have h' := (Matrix.le_iff.mp hV).add hS
    rwa [sub_add_cancel] at h'
  refine ⟨?_, integrable_finsetSum _ fun k _ => hXi k, ?_, hVpsd,
    fun θ hθ => HasMatrixMGFBound.integrable_re_trace_exp_sum hind h hθ, fun θ hθ => ?_⟩
  · filter_upwards [ae_all_iff.2 fun k => (h k).ae_isHermitian] with ω hω
    exact isSelfAdjoint_sum _ fun k _ => hω k
  · rw [integral_finsetSum _ fun k _ => hXi k]
    exact Finset.sum_eq_zero fun k _ => hmean k
  · refine (HasMatrixMGFBound.integral_re_trace_exp_sum_le hind h hθ).trans ?_
    have hLθ : L * θ < 3 := by
      have := hθ.2
      rw [lt_div_iff₀ hL] at this
      linarith
    have hc : 0 ≤ θ ^ 2 / 2 / (1 - L * θ / 3) := div_nonneg (by positivity) (by linarith)
    exact re_trace_exp_le_re_trace_exp_of_le ((IsSelfAdjoint.all _).smul hS.isHermitian)
      (Matrix.le_iff.mpr (by rw [← smul_sub]; exact (Matrix.le_iff.mp hV).smul hc))

section Hermitian

variable {X : ι → Ω → Matrix n n 𝕜}

/-- **Intrinsic-dimension matrix Bernstein**, Hermitian summands: for independent centred
`X k ≤ L • 1` in `L²`, a matrix `V` above `∑ E X k²` and `t ≥ √‖V‖ + L/3`,
`P(t ≤ λ_max (∑ X k)) ≤ 4 intdim V exp (-(t²/2) / (‖V‖ + L t / 3))`.
[Tropp2015, Corollary 7.3.2; Theorem 7.7.1]; here with any upper bound `V` in Loewner order and a
one-sided bound on the summands. Better than `measureReal_eigenvalue_zero_sum_ge_le_bernstein`
when `4 intdim V < card n`, and only for `t` above the threshold.
Result: intrinsic-matrix-bernstein -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein_intrinsicDim (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {V : Matrix n n 𝕜}
    (hV : ∑ k, ∫ ω, X k ω ^ 2 ∂μ ≤ V) {t : ℝ} (ht : √(specNorm V) + L / 3 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      4 * intrinsicDimension V * Real.exp (-(t ^ 2 / 2) / (specNorm V + L * t / 3)) := by
  have := hind.isProbabilityMeasure
  obtain ⟨hY, hYi, hm, hVpsd, hint, htr⟩ := bernstein_intrinsic_hyps hind hL hX2 hmean hle hV
  exact measureReal_eigenvalue_zero_ge_le_bernstein_intrinsicDim_of_integral_le
    (Y := fun ω => ∑ k, X k ω) hY hYi hm hVpsd hL hint htr ht

end Hermitian

section Rectangular

variable {m : Type*} [Fintype m] [DecidableEq m] {S : ι → Ω → Matrix m n 𝕜}

/-- The Hermitian dilation as a continuous real-linear map. -/
private noncomputable def dilationRealCLM (m : Type*) [Fintype m] :
    Matrix m n 𝕜 →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := dilation
      map_add' := dilation_add
      map_smul' := dilation_smul_real }

omit [Fintype ι] in
/-- The dilations of bounded centred independent summands satisfy the hypotheses of the
Hermitian theorems. -/
private theorem dilation_intrinsic_hyps (hind : iIndepFun S μ) (hS2 : ∀ k, MemLp (S k) 2 μ)
    (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0) (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) :
    iIndepFun (fun k ω => dilation (S k ω)) μ ∧
      (∀ k, MemLp (fun ω => dilation (S k ω)) 2 μ) ∧ (∀ k, ∫ ω, dilation (S k ω) ∂μ = 0) ∧
      ∀ k, ∀ᵐ ω ∂μ, dilation (S k ω) ≤ L • (1 : Matrix (m ⊕ n) (m ⊕ n) 𝕜) := by
  have := hind.isProbabilityMeasure
  have hmeas : Measurable (fun A : Matrix m n 𝕜 => dilation A) :=
    (Continuous.matrix_fromBlocks continuous_const continuous_id
      continuous_id.matrix_conjTranspose continuous_const).measurable
  refine ⟨hind.comp (fun _ A => dilation A) fun _ => hmeas,
    fun k => (dilationRealCLM (𝕜 := 𝕜) (n := n) m).comp_memLp' (hS2 k),
    fun k => ?_, fun k => (hle k).mono fun ω h =>
      (isHermitian_dilation _).le_smul_one_of_specNorm_le (by rwa [specNorm_dilation])⟩
  rw [integral_dilation ((hS2 k).integrable one_le_two), hmean k, dilation_zero]

/-- The second moments of the dilations are bounded by the block diagonal proxy. -/
private theorem sum_integral_dilation_sq_le (hS2 : ∀ k, MemLp (S k) 2 μ) {V₁ : Matrix m m 𝕜}
    {V₂ : Matrix n n 𝕜} (hV₁ : ∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ ≤ V₁)
    (hV₂ : ∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ ≤ V₂) :
    ∑ k, ∫ ω, dilation (S k ω) ^ 2 ∂μ ≤ Matrix.fromBlocks V₁ 0 0 V₂ := by
  have hsq : ∀ k, ∫ ω, dilation (S k ω) ^ 2 ∂μ =
      Matrix.fromBlocks (∫ ω, S k ω * (S k ω)ᴴ ∂μ) 0 0 (∫ ω, (S k ω)ᴴ * S k ω ∂μ) := fun k =>
    integral_dilation_sq (hS2 k)
  have hsum : ∑ k, Matrix.fromBlocks (∫ ω, S k ω * (S k ω)ᴴ ∂μ) 0 0
      (∫ ω, (S k ω)ᴴ * S k ω ∂μ) = Matrix.fromBlocks (∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ) 0 0
      (∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        Finset.sum_const_zero]
  simp only [hsq]
  rw [hsum, Matrix.le_iff]
  have hdiff : Matrix.fromBlocks V₁ 0 0 V₂ - Matrix.fromBlocks (∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ) 0 0
      (∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ) = Matrix.fromBlocks (V₁ - ∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ)
      0 0ᴴ (V₂ - ∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ) := by
    rw [Matrix.conjTranspose_zero, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp only [neg_zero, add_zero, sub_eq_add_neg]
  rw [hdiff]
  exact posSemidef_fromBlocks_iff_exists.mpr ⟨Matrix.le_iff.mp hV₁, 0, Matrix.mul_zero _,
    by simpa only [Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero] using
      Matrix.le_iff.mp hV₂⟩

/-- **Intrinsic-dimension matrix Bernstein**, rectangular summands: for independent centred
`S k` in `L²` with `‖S k‖ ≤ L`, matrices `V₁ ≥ ∑ E S Sᴴ`, `V₂ ≥ ∑ E Sᴴ S`, `v = max ‖V₁‖ ‖V₂‖`
and `t ≥ √v + L/3`, `P(t ≤ ‖∑ S k‖) ≤ 4 intdim (V₁ ⊕ V₂) exp (-(t²/2) / (v + L t / 3))`.
[Tropp2015, Theorem 7.3.1]; through the Hermitian dilation, with any upper bounds `V₁`, `V₂`.
Better than `measureReal_specNorm_sum_ge_le_bernstein` when
`4 intdim (V₁ ⊕ V₂) < card m + card n`.
Result: intrinsic-matrix-bernstein -/
theorem measureReal_specNorm_sum_ge_le_bernstein_intrinsicDim (hind : iIndepFun S μ)
    (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) {V₁ : Matrix m m 𝕜} {V₂ : Matrix n n 𝕜}
    (hV₁ : ∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ ≤ V₁) (hV₂ : ∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ ≤ V₂)
    {t : ℝ} (ht : √(max (specNorm V₁) (specNorm V₂)) + L / 3 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, S k ω)} ≤
      4 * intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂) *
        Real.exp (-(t ^ 2 / 2) / (max (specNorm V₁) (specNorm V₂) + L * t / 3)) := by
  obtain ⟨h1, h2, h3, h4⟩ := dilation_intrinsic_hyps hind hS2 hmean hle
  have h := measureReal_eigenvalue_zero_sum_ge_le_bernstein_intrinsicDim h1 hL h2 h3 h4
    (sum_integral_dilation_sq_le hS2 hV₁ hV₂) (t := t)
    (by rwa [specNorm_fromBlocks_zero₁₂_zero₂₁])
  simp only [← dilation_sum, eigenvalue_zero_dilation, specNorm_fromBlocks_zero₁₂_zero₂₁] at h
  exact h

end Rectangular

/-- The absolute constant of the intrinsic-dimension Bernstein means. [Tropp2015, Theorem 7.3.1]
leaves it unspecified; the prototype's proof reached `20`, the proof here `8`, the value here.
A smaller value is a better bound. Use only `intrinsicBernsteinMeanConstant_pos` and
`intrinsicBernsteinMeanConstant_le`. -/
noncomputable irreducible_def intrinsicBernsteinMeanConstant : ℝ := 8

/-- The intrinsic Bernstein mean constant is positive. -/
theorem intrinsicBernsteinMeanConstant_pos : 0 < intrinsicBernsteinMeanConstant := by
  rw [intrinsicBernsteinMeanConstant_def]
  norm_num

/-- An explicit upper bound on `intrinsicBernsteinMeanConstant`. -/
theorem intrinsicBernsteinMeanConstant_le : intrinsicBernsteinMeanConstant ≤ 8 := by
  exact intrinsicBernsteinMeanConstant_def.le

/-- The Bernstein exponent beyond `μ₀` dominates a linear one:
`-(t²/2)/(v + Lt/3) ≤ -c t` with `c = (μ₀/2)/(v + Lμ₀/3)`, for `t ≥ μ₀ > 0`. -/
private theorem bernstein_exponent_le_linear {v L μ₀ t : ℝ} (hv : 0 ≤ v) (hL : 0 < L)
    (hμ : 0 < μ₀) (ht : μ₀ ≤ t) :
    -(t ^ 2 / 2) / (v + L * t / 3) ≤ -(μ₀ / 2 / (v + L * μ₀ / 3)) * t := by
  have hA : 0 < v + L * μ₀ / 3 := by positivity
  have ht0 : 0 < t := hμ.trans_le ht
  have hB : 0 < v + L * t / 3 := by positivity
  rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_div_iff₀ hA hB]
  nlinarith [mul_le_mul_of_nonneg_left ht (mul_nonneg ht0.le hv)]

/-- The scalar bookkeeping of the intrinsic Bernstein mean: with `μ₀ = 2 √(v ℓ) + 2 ℓ L` and
`c = (μ₀/2)/(v + Lμ₀/3)`, `μ₀` is above the threshold and
`μ₀ + 4 r e^{-c μ₀} / c ≤ 8 (√(v ℓ) + L ℓ)` when `e^{-ℓ} = 1/(1 + r)` and `ℓ ≥ 2/3`. -/
private theorem bernstein_mean_scalar {v L ℓ r : ℝ} (hv : 0 < v) (hL : 0 < L) (hℓ : 2 / 3 ≤ ℓ)
    (hr : 0 ≤ r) (hexp : Real.exp (-ℓ) = 1 / (1 + r)) {μ₀ c : ℝ}
    (hμ : μ₀ = 2 * √(v * ℓ) + 2 * ℓ * L) (hc : c = μ₀ / 2 / (v + L * μ₀ / 3)) :
    √v + L / 3 ≤ μ₀ ∧ 0 < μ₀ ∧ 0 < c ∧
      μ₀ + 4 * r * Real.exp (-c * μ₀) / c ≤ 8 * (√(v * ℓ) + L * ℓ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hs0 : 0 < √(v * ℓ) := Real.sqrt_pos.mpr (by positivity)
  have hss : √(v * ℓ) * √(v * ℓ) = v * ℓ := Real.mul_self_sqrt (by positivity)
  have hμ0 : 0 < μ₀ := by rw [hμ]; positivity
  have hA : 0 < v + L * μ₀ / 3 := by positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have h2s : 2 * √(v * ℓ) ≤ μ₀ := by rw [hμ]; nlinarith
  refine ⟨?_, hμ0, hc0, ?_⟩
  · have h1 : √v ≤ 2 * √(v * ℓ) :=
      calc √v ≤ √((2 * √(v * ℓ)) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hv.le (by linarith : (0 : ℝ) ≤ 4 * ℓ - 1)])
        _ = 2 * √(v * ℓ) := Real.sqrt_sq (by positivity)
    have h2 : L / 3 ≤ 2 * ℓ * L := by nlinarith
    rw [hμ]
    linarith
  have hcμ : ℓ ≤ c * μ₀ := by
    rw [hc, div_mul_eq_mul_div, le_div_iff₀ hA]
    have hμμ : μ₀ * μ₀ = 2 * √(v * ℓ) * μ₀ + 2 * ℓ * L * μ₀ := by
      nth_rewrite 1 [hμ]
      ring
    nlinarith [mul_le_mul_of_nonneg_left h2s (by positivity : (0 : ℝ) ≤ 2 * √(v * ℓ)),
      mul_pos (mul_pos hℓ0 hL) hμ0, mul_pos hv hℓ0]
  have he : Real.exp (-c * μ₀) ≤ 1 / (1 + r) := by
    rw [← hexp]
    exact Real.exp_le_exp.mpr (by linarith)
  have h4 : 4 * r * Real.exp (-c * μ₀) ≤ 4 := by
    calc 4 * r * Real.exp (-c * μ₀) ≤ 4 * r * (1 / (1 + r)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ 4 := by
          rw [mul_one_div, div_le_iff₀ (by linarith)]
          linarith
  have hinvc : 1 / c = 2 * v / μ₀ + 2 * L / 3 := by
    rw [hc]
    field_simp
  have h2v : 2 * v / μ₀ ≤ 3 / 2 * √(v * ℓ) := by
    rw [div_le_iff₀ hμ0]
    nlinarith [mul_le_mul_of_nonneg_left h2s (by positivity : (0 : ℝ) ≤ 3 / 2 * √(v * ℓ)),
      mul_nonneg (sub_nonneg.mpr hℓ) hv.le]
  have hterm : 4 * r * Real.exp (-c * μ₀) / c ≤ 4 * (3 / 2 * √(v * ℓ) + 2 * L / 3) := by
    rw [div_eq_mul_one_div, hinvc]
    calc 4 * r * Real.exp (-c * μ₀) * (2 * v / μ₀ + 2 * L / 3)
        ≤ 4 * (2 * v / μ₀ + 2 * L / 3) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ ≤ 4 * (3 / 2 * √(v * ℓ) + 2 * L / 3) := by linarith
  have hLℓ : 2 * L / 3 ≤ L * ℓ := by nlinarith
  linarith [mul_pos hℓ0 hL]

section Hermitian

variable {X : ι → Ω → Matrix n n 𝕜}

/-- **Intrinsic-dimension matrix Bernstein for the mean**, Hermitian summands: for independent
centred `X k ≤ L • 1` in `L²` and a matrix `V` above `∑ E X k²`,
`E λ_max (∑ X k) ≤ C (√(‖V‖ log (1 + intdim V)) + L log (1 + intdim V))` with
`C = intrinsicBernsteinMeanConstant`. [Tropp2015, Corollary 7.3.2]; here with any upper bound `V`
in Loewner order. Better than `integral_eigenvalue_zero_sum_le_bernstein` when `intdim V` is
much smaller than `card n`; its constant is worse. Proof: integrate the tail above the
threshold.
Result: intrinsic-matrix-bernstein -/
theorem integral_eigenvalue_zero_sum_le_bernstein_intrinsicDim (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {V : Matrix n n 𝕜}
    (hV : ∑ k, ∫ ω, X k ω ^ 2 ∂μ ≤ V) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤ intrinsicBernsteinMeanConstant *
      (√(specNorm V * Real.log (1 + intrinsicDimension V)) +
        L * Real.log (1 + intrinsicDimension V)) := by
  have := hind.isProbabilityMeasure
  obtain ⟨hY, hYi, hm, hVpsd, hint, htr⟩ := bernstein_intrinsic_hyps hind hL hX2 hmean hle hV
  have hfi : Integrable (fun ω => eigenvalue (∑ k, X k ω) 0) μ := integrable_eigenvalue hYi 0
  have hfpos := hfi.pos_part
  have hset : ∀ t : ℝ, 0 < t → {ω | t ≤ max (eigenvalue (∑ k, X k ω) 0) 0} =
      {ω | t ≤ eigenvalue (∑ k, X k ω) 0} := fun t ht => by
    ext ω
    simp only [Set.mem_ofPred_eq, le_max_iff, or_iff_left_iff_imp]
    intro h
    linarith
  have hmeas := hfpos.aemeasurable
  have hnn : 0 ≤ᵐ[μ] fun ω => max (eigenvalue (∑ k, X k ω) 0) 0 :=
    ae_of_all _ fun ω => le_max_right _ _
  refine (integral_mono hfi hfpos fun ω => le_max_left _ _).trans ?_
  rw [intrinsicBernsteinMeanConstant_def]
  rcases (specNorm_nonneg V).eq_or_lt with hv0 | hvpos
  · have hr : intrinsicDimension V = 0 := by rw [intrinsicDimension, ← hv0, div_zero]
    rw [hr, add_zero, Real.log_one, mul_zero, mul_zero, Real.sqrt_zero, add_zero, mul_zero]
    have hθ : 3 / (2 * L) ∈ Set.Ioo 0 (3 / L) :=
      ⟨by positivity, by rw [div_lt_div_iff₀ (by positivity) hL]; nlinarith⟩
    have h := integral_le_of_measureReal_ge_le hmeas hnn (a := 0) (F := fun _ => 0)
      integrableOn_zero fun t ht => by
        rw [hset t ht]
        refine (bernstein_intrinsic_core (Y := fun ω => ∑ k, X k ω) hY hYi hm hVpsd hθ.1
          (hint _ hθ) (htr _ hθ) ht).trans ?_
        rw [hr, zero_mul, zero_div]
    simpa only [integral_zero, add_zero] using h
  have hV0 : V ≠ 0 := fun h => hvpos.ne' (by rw [h, specNorm_zero])
  have hr1 : 1 ≤ intrinsicDimension V := hVpsd.one_le_intrinsicDimension hV0
  have hℓ : 2 / 3 ≤ Real.log (1 + intrinsicDimension V) := by
    have h2 : Real.log 2 ≤ Real.log (1 + intrinsicDimension V) :=
      Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hexp : Real.exp (-Real.log (1 + intrinsicDimension V)) =
      1 / (1 + intrinsicDimension V) := by
    rw [Real.exp_neg, Real.exp_log (by linarith), one_div]
  obtain ⟨hthr, hμ0, hc0, hfin⟩ := bernstein_mean_scalar hvpos hL hℓ (by linarith) hexp rfl rfl
  set μ₀ := 2 * √(specNorm V * Real.log (1 + intrinsicDimension V)) +
    2 * Real.log (1 + intrinsicDimension V) * L with hμ₀
  set c := μ₀ / 2 / (specNorm V + L * μ₀ / 3) with hc
  have h := integral_le_of_measureReal_ge_le hmeas hnn (a := μ₀)
    (F := fun t => 4 * intrinsicDimension V * Real.exp (-c * t))
    ((exp_neg_integrableOn_Ioi μ₀ hc0).const_mul _) fun t ht => by
      rw [hset t (hμ0.trans ht)]
      refine (measureReal_eigenvalue_zero_sum_ge_le_bernstein_intrinsicDim hind hL hX2 hmean hle
        hV (hthr.trans ht.le)).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (bernstein_exponent_le_linear (specNorm_nonneg V) hL hμ0 ht.le)) (by positivity)
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hc0), neg_div_neg_eq,
    ← mul_div_assoc] at h
  exact h.trans hfin

end Hermitian

section Rectangular

variable {m : Type*} [Fintype m] [DecidableEq m] {S : ι → Ω → Matrix m n 𝕜}

/-- **Intrinsic-dimension matrix Bernstein for the mean**, rectangular summands: for independent
centred `S k` in `L²` with `‖S k‖ ≤ L` and matrices `V₁ ≥ ∑ E S Sᴴ`, `V₂ ≥ ∑ E Sᴴ S`, with
`v = max ‖V₁‖ ‖V₂‖` and `D = intdim (V₁ ⊕ V₂)`, `E ‖∑ S k‖ ≤ C (√(v log (1 + D)) + L log (1 + D))`
with `C = intrinsicBernsteinMeanConstant`. [Tropp2015, Theorem 7.3.1]; here with any upper
bounds `V₁`, `V₂`. Better than `integral_specNorm_sum_le_bernstein` when `D` is much smaller than
`card m + card n`.
Result: intrinsic-matrix-bernstein -/
theorem integral_specNorm_sum_le_bernstein_intrinsicDim (hind : iIndepFun S μ)
    (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) {V₁ : Matrix m m 𝕜} {V₂ : Matrix n n 𝕜}
    (hV₁ : ∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ ≤ V₁) (hV₂ : ∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ ≤ V₂) :
    ∫ ω, specNorm (∑ k, S k ω) ∂μ ≤ intrinsicBernsteinMeanConstant *
      (√(max (specNorm V₁) (specNorm V₂) *
          Real.log (1 + intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂))) +
        L * Real.log (1 + intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂))) := by
  obtain ⟨h1, h2, h3, h4⟩ := dilation_intrinsic_hyps hind hS2 hmean hle
  have h := integral_eigenvalue_zero_sum_le_bernstein_intrinsicDim h1 hL h2 h3 h4
    (sum_integral_dilation_sq_le hS2 hV₁ hV₂)
  simp only [← dilation_sum, eigenvalue_zero_dilation, specNorm_fromBlocks_zero₁₂_zero₂₁] at h
  exact h

end Rectangular

end Bernstein

end NLAlib
