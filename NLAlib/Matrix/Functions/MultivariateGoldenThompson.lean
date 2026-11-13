/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.ExponentialInterpolation
public import NLAlib.Matrix.Perturbation.Continuity

/-!
# The multivariate Golden–Thompson inequality

The ordered product of matrix exponentials on the right boundary of the complex strip controls
the exponential of a Hermitian sum. Its log Schatten norm is integrable against the limiting
Poisson density. The limit of the finite-parameter bound gives the inequality for each finite
Schatten exponent at least one [SutterBertaTomamichel2017, Corollary 3.3].

## Main results

* `NLAlib.integrable_stripPoissonDensityZero_mul_log_schattenNorm_orderedMatrixExp`.
* `NLAlib.log_schattenNorm_exp_sum_le_integral`.
-/

@[expose] public section

open Matrix Complex Set Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator MatrixOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Golden–Thompson boundary integrand is absolutely integrable. The ordered product and
its inverse bound the positive and negative parts of the logarithm. -/
theorem integrable_stripPoissonDensityZero_mul_log_schattenNorm_orderedMatrixExp
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 0 < p) :
    Integrable (fun t : ℝ => Real.stripPoissonDensityZero t *
      Real.log (schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I)))) := by
  by_cases hn : Nonempty n
  · let := hn
    apply Real.integrable_stripPoissonDensityZero.mul_bdd
      (continuous_log_schattenNorm_orderedMatrixExp H hH hp).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using
      abs_log_schattenNorm_orderedMatrixExp_le H hH hp t)
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz (A : Matrix n n ℂ) : A = 0 := Subsingleton.elim _ _
    simp only [hz _, schattenNorm_zero, Real.log_zero, mul_zero]
    exact integrable_zero _ _ _

/-- The Schatten norm of the exponential of a Hermitian sum is bounded by the exponential of
the strip average of the boundary log norms. This form also applies in dimension zero.
[SutterBertaTomamichel2017, Corollary 3.3]. -/
theorem schattenNorm_exp_sum_le_exp_integral
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 1 ≤ p) :
    schattenNorm (ENNReal.ofReal p) (NormedSpace.exp H.sum) ≤
      Real.exp (∫ t : ℝ, Real.stripPoissonDensityZero t *
        Real.log (schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I)))) := by
  by_cases hn : Nonempty n
  · let := hn
    let f : ℝ → ℝ := fun t =>
      Real.log (schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I)))
    have hp0 := zero_lt_one.trans_le hp
    have hf : Continuous f := continuous_log_schattenNorm_orderedMatrixExp H hH hp0
    have hb : ∀ᵐ t, ‖f t‖ ≤
        (H.map specNorm).sum + |Real.log ((Fintype.card n : ℝ) ^ (1 / p))| :=
      ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using
        abs_log_schattenNorm_orderedMatrixExp_le H hH hp0 t)
    have hparam : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝[>] 0) :=
      tendsto_inv_atTop_nhdsGT_zero.comp tendsto_natCast_atTop_atTop
    have hi :=
      (Real.tendsto_integral_stripPoissonDensity_smul_zero hf.aestronglyMeasurable hb).comp hparam
    simp only [smul_eq_mul, Function.comp_def] at hi
    have hright := Real.continuous_exp.continuousAt.tendsto.comp hi
    have hleft := (continuous_schattenNorm (𝕜 := ℂ) (m := n) (n := n)
      (ENNReal.one_le_ofReal.mpr hp)).continuousAt.tendsto.comp
        (tendsto_abs_orderedMatrixExp_pow H hH)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
    have hr : (k : ℝ)⁻¹ ∈ Ioo (0 : ℝ) 1 :=
      ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hk1⟩
    have h := schattenNorm_rpow_abs_orderedMatrixExp_le_exp_integral H hH hp hr
    have hco : (((k : ℝ)⁻¹ : ℝ) : ℂ) = (k : ℂ)⁻¹ := by
      simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [Real.integral_stripHarmonicMeasure hr, hco] at h
    simp only [one_div, inv_inv] at h
    rw [CFC.rpow_natCast (CFC.abs (orderedMatrixExp H (k : ℂ)⁻¹)) k (CFC.abs_nonneg _)] at h
    exact h
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz : NormedSpace.exp H.sum = 0 := Subsingleton.elim _ _
    rw [hz, schattenNorm_zero]
    exact (Real.exp_pos _).le

/-- **Multivariate Golden–Thompson.** For Hermitian matrices $\mathbf H_j$ and $1\le p<\infty$,
$$\log\Big\|\exp\Big(\sum_j\mathbf H_j\Big)\Big\|_{S_p}
  \le \int_{\mathbb R}\!\beta_0(t)\log\Big\|\prod_j\exp((1+it)\mathbf H_j)\Big\|_{S_p}\,dt,$$
where $\beta_0(t)=\pi/(2(\cosh(\pi t)+1))$ and multiplication follows the order of the list.
[SutterBertaTomamichel2017, Corollary 3.3].
The formal proof adapts `tchen-research/NLAlib@77514ce`.
Result: multivariate-golden-thompson -/
theorem log_schattenNorm_exp_sum_le_integral
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 1 ≤ p) :
    Real.log (schattenNorm (ENNReal.ofReal p) (NormedSpace.exp H.sum)) ≤
      ∫ t : ℝ, Real.stripPoissonDensityZero t *
        Real.log (schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I))) := by
  by_cases hn : Nonempty n
  · let := hn
    have hun : IsUnit (NormedSpace.exp H.sum) := by
      let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
      exact NormedSpace.isUnit_exp H.sum
    have hnorm : 0 < schattenNorm (ENNReal.ofReal p) (NormedSpace.exp H.sum) :=
      lt_of_le_of_ne (schattenNorm_nonneg _ _) (Ne.symm (fun h => hun.ne_zero
        ((schattenNorm_eq_zero_iff _).mp h)))
    exact (Real.log_le_iff_le_exp hnorm).mpr
      (schattenNorm_exp_sum_le_exp_integral H hH hp)
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz (A : Matrix n n ℂ) : A = 0 := Subsingleton.elim _ _
    simp only [hz _, schattenNorm_zero, Real.log_zero, mul_zero, integral_zero, le_rfl]

end NLAlib
