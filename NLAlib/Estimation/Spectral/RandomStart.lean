/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Eigenvalues.PowerIteration
public import NLAlib.Krylov.Eigenvalues.Ritz
public import NLAlib.Probability.Distributions.GaussianLogOverlap
public import NLAlib.Probability.Measurability.Krylov
public import NLAlib.Probability.Measurability.Matrix

/-!
# Estimating the largest eigenvalue from a random start

For a positive semidefinite real $\mathbf{A}$ and a standard Gaussian start $\mathbf{g}$, the
power method and the Lanczos method estimate $\lambda_0 = \lambda_0(\mathbf{A})$ with an expected
error that depends on the dimension $N = \lvert n\rvert$ only through $\log N$, with no gap:
after $q$ multiplications the power method's Rayleigh quotient is within
$\lambda_0(\log(2N) + 2)/(2q + 1)$ of $\lambda_0$ on average, and the largest Ritz value of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$ within $O(\lambda_0\log(N)^2/q^2)$. The bounds hold
for every dimension, repeated top eigenvalues and $\mathbf{A} = \mathbf{0}$.

The proofs compose, pointwise in the sample, the deterministic gap-free steps of
`NLAlib.Krylov.Eigenvalues` with the logarithmic moments of the overlap of a Gaussian vector with
a unit eigenvector (`NLAlib.Probability.Distributions.GaussianLogOverlap`): the weight of the top
eigenvalue in the spectral measure dominates the squared overlap, which is almost surely nonzero.
The Ritz value is written in projector form,
$\lambda_0(\mathbf{P}\mathbf{A}\mathbf{P})$ with $\mathbf{P}$ the orthogonal projector onto
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$, which is a measurable function of $\mathbf{g}$.

The constants are named bounds whose values are those the proof gives.

## Main definitions

* `NLAlib.randomStartPowerBound`: the power factor, <!-- value randomStartPowerBound N q -->
  $(\log(2N) + 2)/(2q + 1)$.
* `NLAlib.randomStartLanczosBound`: the Lanczos factor, <!-- value randomStartLanczosBound N q -->
  $4((\log(2N) + 2 + \log 2)^2 + 4)/((\log 2)^2 q^2)$.

## Main results

* `NLAlib.integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector`: the
  power method.
* `NLAlib.integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector`:
  the Lanczos method.
* Their asymptotic forms, $O(\log(N)/\varepsilon)$ and $O(\log(N)/\sqrt{\varepsilon})$
  multiplications.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n] {g : Ω → n → ℝ} {A : Matrix n n ℝ}

/-! ### The named bounds -/

/-- The random-start power-method factor <!-- value randomStartPowerBound N q -->
$(\log(2N) + 2)/(2q + 1)$, for dimension $N$ and $q$ multiplications: the mean logarithmic
overlap of a Gaussian vector with a unit vector, $\log(2N) + 2$, over the $2q + 1$ of the
deterministic step. Source:
[MartinssonTropp2020, Theorem 6.1], whose printed constant is to be
compared with this one; the value here is the one the proof gives and is not optimised (the exact
mean overlap is $\log(2N) + \gamma + o(1)$). -/
noncomputable irreducible_def randomStartPowerBound (N q : ℕ) : ℝ :=
  (Real.log (2 * N) + 2) / (2 * q + 1)

/-- The random-start Lanczos factor <!-- value randomStartLanczosBound N q -->
$4((\log(2N) + 2 + \log 2)^2 + 4)/((\log 2)^2 q^2)$, for dimension $N$ and $q$
multiplications: $4/q^2$ times the bound $((\log(2N) + 2 + \log 2)^2 + 4)/(\log 2)^2$ on
$\mathbb{E}(1 + L/\log 2)^2$, $L$ the logarithmic overlap of a Gaussian vector with a unit
vector. Source: [MartinssonTropp2020, Theorem 6.2], whose printed
constant is to be compared with this one; the value here is the one the proof gives and is not
optimised. -/
noncomputable irreducible_def randomStartLanczosBound (N q : ℕ) : ℝ :=
  4 * ((Real.log (2 * N) + 2 + Real.log 2) ^ 2 + 4) / (Real.log 2 ^ 2 * q ^ 2)

/-- The random-start power-method factor is nonnegative: <!-- value randomStartPowerBound N q -->
$0 \le (\log(2N) + 2)/(2q + 1)$. -/
theorem randomStartPowerBound_nonneg (N q : ℕ) : 0 ≤ randomStartPowerBound N q := by
  rw [randomStartPowerBound_def]
  have h : 0 ≤ Real.log (2 * N) := by
    have := Real.log_natCast_nonneg (2 * N)
    rwa [Nat.cast_mul, Nat.cast_ofNat] at this
  positivity

/-- The random-start Lanczos factor is nonnegative: <!-- value randomStartLanczosBound N q -->
$0 \le 4((\log(2N) + 2 + \log 2)^2 + 4)/((\log 2)^2 q^2)$.
-/
theorem randomStartLanczosBound_nonneg (N q : ℕ) : 0 ≤ randomStartLanczosBound N q := by
  rw [randomStartLanczosBound_def]
  positivity

/-- A coarse form of the random-start power-method factor: for $N \ge 2$ and
$q \ge 1$, <!-- value randomStartPowerBound N q -->
$(\log(2N) + 2)/(2q + 1) \le 3\log(N)/q$. -/
theorem randomStartPowerBound_le {N q : ℕ} (hN : 2 ≤ N) (hq : 1 ≤ q) :
    randomStartPowerBound N q ≤ 3 * Real.log N / q := by
  rw [randomStartPowerBound_def]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hsplit : Real.log (2 * N) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) (by positivity)
  rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ q)]

/-! ### Expected errors -/

/-- The pointwise random-start step: if a unit eigenvector $\mathbf{u}$ of $c$ has
$\langle \mathbf{u}, \mathbf{x} \rangle \ne 0$, then $\mathbf{x}$ has positive weight at $c$
and $\log(1 + \tan^2\angle(\mathbf{x}, E_c)) \le
\log(\|\mathbf{x}\|^2 / \langle \mathbf{u}, \mathbf{x} \rangle^2)$. -/
private theorem log_one_add_spectralTangentSq_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {u x : n → ℝ} {c : ℝ} (hu : A *ᵥ u = c • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1)
    (hux : u ⬝ᵥ x ≠ 0) :
    0 < (spectralMeasure A x).real {c} ∧
      Real.log (1 + spectralTangentSq A x c) ≤
        Real.log (‖WithLp.toLp 2 x‖ ^ 2 / (u ⬝ᵥ x) ^ 2) := by
  have hw : (u ⬝ᵥ x) ^ 2 ≤ (spectralMeasure A x).real {c} := by
    have h := hA.norm_star_dotProduct_sq_le_spectralMeasure_real (c := c) hu hu1 x
    rwa [star_trivial, Real.norm_eq_abs, sq_abs] at h
  have hpos : 0 < (u ⬝ᵥ x) ^ 2 := by positivity
  have hb : 0 < (spectralMeasure A x).real {c} := hpos.trans_le hw
  refine ⟨hb, ?_⟩
  have h1 : 0 < 1 + spectralTangentSq A x c := by
    linarith [spectralTangentSq_nonneg A x c]
  refine Real.log_le_log h1 ?_
  rw [hA.one_add_spectralTangentSq hb]
  exact div_le_div_of_nonneg_left (by positivity) hpos hw

omit [DecidableEq n] in
/-- The Ritz value in projector form is the frame form: for $\mathbf{Q}$ with orthonormal columns
and the column space of $\mathbf{K}$, $\lambda_0(\mathbf{P}_{\mathbf{K}}\mathbf{A}
\mathbf{P}_{\mathbf{K}}) = \lambda_0(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})$. -/
private theorem eigenvalue_rangeProjector_mul_mul_eq {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {r m : Type*} [Fintype r] [DecidableEq r] [Fintype m] {Q : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) {K : Matrix n m ℝ}
    (hK : LinearMap.range Q.mulVecLin = LinearMap.range K.mulVecLin) :
    eigenvalue (rangeProjector K * A * rangeProjector K) 0 = eigenvalue (Qᴴ * A * Q) 0 := by
  rw [← rangeProjector_inj.2 hK, hQ.rangeProjector_eq,
    show Q * Qᴴ * A * (Q * Qᴴ) = Q * (Qᴴ * A * Q) * Qᴴ by simp only [Matrix.mul_assoc]]
  exact hQ.eigenvalue_mul_mul_conjTranspose (hA.conjTranspose_mul_mul_same Q) 0

/-- The power-method error $\lambda_0(\mathbf{A}) - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{g})$ of
a standard Gaussian start $\mathbf{g}$, $\rho_{\mathbf{A}}$ the Rayleigh quotient, is integrable
for every real square $\mathbf{A}$: it is measurable and bounded. -/
theorem integrable_eigenvalue_sub_rayleighQuotient_pow_mulVec_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix n n ℝ) (q : ℕ) :
    Integrable (fun ω => eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) μ := by
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure
  have hm : AEStronglyMeasurable (fun ω => rayleighQuotient A (A ^ q *ᵥ g ω)) μ :=
    ((measurable_rayleighQuotient A).comp_aemeasurable
      ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp_aemeasurable
        hg.aemeasurable)).aestronglyMeasurable
  refine (integrable_const _).sub (Integrable.of_bound hm (specNorm A) (ae_of_all _ fun ω => ?_))
  rw [Real.norm_eq_abs, rayleighQuotient_def, abs_div, abs_pow, abs_norm]
  exact div_le_of_le_mul₀ (by positivity) (specNorm_nonneg A) (abs_re_quadForm_le A _)

/-- The Lanczos error $\lambda_0(\mathbf{A}) - \lambda_0(\mathbf{P}\mathbf{A}\mathbf{P})$ of a
standard Gaussian start $\mathbf{g}$, $\mathbf{P}$ the orthogonal projector onto
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$, is integrable for every real square $\mathbf{A}$: it
is measurable and bounded. -/
theorem integrable_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix n n ℝ) (q : ℕ) :
    Integrable (fun ω => eigenvalue A 0 -
      eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) * A *
        rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) μ := by
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure
  have hm : AEStronglyMeasurable (fun ω => eigenvalue (rangeProjector (krylovMatrix A (g ω)
      (q + 1)) * A * rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) μ := by
    have hP : Measurable fun b : n → ℝ => rangeProjector (krylovMatrix A b (q + 1)) :=
      measurable_rangeProjector.comp (measurable_krylovMatrix A (q + 1))
    exact ((measurable_eigenvalue 0).comp ((hP.matrix_mul measurable_const).matrix_mul
      hP)).comp_aemeasurable hg.aemeasurable |>.aestronglyMeasurable
  refine (integrable_const _).sub (Integrable.of_bound hm (specNorm A) (ae_of_all _ fun ω => ?_))
  set P := rangeProjector (krylovMatrix A (g ω) (q + 1))
  have hP := isStarProjection_rangeProjector (krylovMatrix A (g ω) (q + 1))
  rw [Real.norm_eq_abs]
  by_cases hH : (P * A * P).IsHermitian
  · refine (hH.abs_eigenvalue_le_specNorm 0).trans ?_
    rw [Matrix.mul_assoc]
    exact (hP.specNorm_mul_le _).trans (hP.specNorm_mul_right_le A)
  · rw [eigenvalue_of_not_isHermitian hH, abs_zero]
    exact specNorm_nonneg A

-- A backticked declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Random-start power method**: for positive semidefinite real $\mathbf{A}$ and a standard
Gaussian start $\mathbf{g}$ (law $\mathcal{N}(\mathbf{0}, \mathbf{I})$ on $\mathbb{R}^n$), after
$q$ multiplications, <!-- value randomStartPowerBound {\lvert n \rvert} q -->
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{g})\bigr] \le
\frac{\log(2\lvert n \rvert) + 2}{2q + 1}\,\lambda_0(\mathbf{A})\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient, for every $q$ (including $0$), every dimension,
repeated top eigenvalues and $\mathbf{A} = \mathbf{0}$; no gap. The factor is
`randomStartPowerBound`. Asymptotic form:
`NLAlib.exists_forall_integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector`.
[MartinssonTropp2020, Theorem 6.1]; there as
a relative error with a different constant; constants composed here.
Result: random-start-power -/
theorem integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hA : A.PosSemidef) (q : ℕ) :
    ∫ ω, (eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) ∂μ ≤
      randomStartPowerBound (Fintype.card n) q * eigenvalue A 0 := by
  have h0 := hA.eigenvalue_nonneg 0
  rcases isEmpty_or_nonempty n with hn | hn
  · have h : ∀ ω, eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω) = 0 := fun ω => by
      rw [eigenvalue_of_card_le A (by simp), Subsingleton.elim (A ^ q *ᵥ g ω) 0,
        rayleighQuotient_zero_right, sub_zero]
    simp only [h, integral_zero]
    exact mul_nonneg (randomStartPowerBound_nonneg _ _) h0
  obtain ⟨u, hu1, hu⟩ := hA.isHermitian.exists_norm_eq_one_and_mulVec_eq Fintype.card_pos
  have hc : 0 ≤ eigenvalue A 0 / (2 * q + 1) := div_nonneg h0 (by positivity)
  have hpt : ∀ᵐ ω ∂μ, eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω) ≤
      eigenvalue A 0 / (2 * q + 1) * Real.log (‖WithLp.toLp 2 (g ω)‖ ^ 2 / (u ⬝ᵥ g ω) ^ 2) := by
    filter_upwards [ae_dotProduct_ne_zero_of_hasLaw_gaussianVector hg hu1] with ω hω
    obtain ⟨hb, hlog⟩ := log_one_add_spectralTangentSq_le hA.isHermitian hu hu1 hω
    refine (hA.eigenvalue_sub_rayleighQuotient_pow_mulVec_le (g ω) hb q).trans ?_
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hlog hc
  refine (integral_mono_ae
    (integrable_eigenvalue_sub_rayleighQuotient_pow_mulVec_of_hasLaw_gaussianVector hg A q)
    ((integrable_log_norm_sq_div_sq_of_hasLaw_gaussianVector hg hu1).const_mul _) hpt).trans ?_
  rw [integral_const_mul, randomStartPowerBound_def]
  refine (mul_le_mul_of_nonneg_left
    (integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector hg hu1) hc).trans_eq ?_
  ring

-- A backticked declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Random-start Lanczos**: for positive semidefinite real $\mathbf{A}$, a standard Gaussian
start $\mathbf{g}$ (law $\mathcal{N}(\mathbf{0}, \mathbf{I})$ on $\mathbb{R}^n$) and $q \ge 1$,
the largest Ritz value $\theta_0$ of $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$ ($q$
multiplications), written as $\lambda_0(\mathbf{P}\mathbf{A}\mathbf{P})$ with $\mathbf{P}$ the
orthogonal projector onto it, satisfies <!-- value randomStartLanczosBound {\lvert n \rvert} q -->
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \theta_0\bigr] \le
\frac{4((\log(2\lvert n \rvert) + 2 + \log 2)^2 + 4)}{(\log 2)^2 q^2}\,\lambda_0(\mathbf{A})\,,$$
for every dimension, repeated top eigenvalues and $\mathbf{A} = \mathbf{0}$; no gap. The factor
is `randomStartLanczosBound`. Asymptotic form:
`NLAlib.exists_forall_integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector`.
[MartinssonTropp2020, Theorem 6.2]; there as a relative error with a
different constant; constants composed here.
Result: random-start-lanczos -/
theorem integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hA : A.PosSemidef) {q : ℕ} (hq : 1 ≤ q) :
    ∫ ω, (eigenvalue A 0 -
        eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) * A *
          rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) ∂μ ≤
      randomStartLanczosBound (Fintype.card n) q * eigenvalue A 0 := by
  have h0 := hA.eigenvalue_nonneg 0
  rcases isEmpty_or_nonempty n with hn | hn
  · have h : ∀ ω, eigenvalue A 0 - eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) *
        A * rangeProjector (krylovMatrix A (g ω) (q + 1))) 0 = 0 := fun ω => by
      rw [eigenvalue_of_card_le A (by simp), eigenvalue_of_card_le _ (by simp), sub_zero]
    simp only [h, integral_zero]
    exact mul_nonneg (randomStartLanczosBound_nonneg _ _) h0
  obtain ⟨u, hu1, hu⟩ := hA.isHermitian.exists_norm_eq_one_and_mulVec_eq Fintype.card_pos
  let L : Ω → ℝ := fun ω => Real.log (‖WithLp.toLp 2 (g ω)‖ ^ 2 / (u ⬝ᵥ g ω) ^ 2)
  have hc : 0 ≤ 4 * eigenvalue A 0 / q ^ 2 := by positivity
  have hpt : ∀ᵐ ω ∂μ, eigenvalue A 0 - eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) *
      A * rangeProjector (krylovMatrix A (g ω) (q + 1))) 0 ≤
        4 * eigenvalue A 0 / q ^ 2 * (1 + L ω / Real.log 2) ^ 2 := by
    filter_upwards [ae_dotProduct_ne_zero_of_hasLaw_gaussianVector hg hu1] with ω hω
    obtain ⟨hb, hlog⟩ := log_one_add_spectralTangentSq_le hA.isHermitian hu hu1 hω
    obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A (g ω) (q + 1)
    rw [eigenvalue_rangeProjector_mul_mul_eq hA hQ hK]
    refine (hA.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq hb hQ hq hK).trans ?_
    rw [mul_div_right_comm]
    refine mul_le_mul_of_nonneg_left ?_ hc
    have hl0 : 0 ≤ Real.log (1 + spectralTangentSq A (g ω) (eigenvalue A 0)) :=
      Real.log_nonneg (by linarith [spectralTangentSq_nonneg A (g ω) (eigenvalue A 0)])
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have h1 : 0 ≤ 1 + Real.log (1 + spectralTangentSq A (g ω) (eigenvalue A 0)) / Real.log 2 := by
      positivity
    exact pow_le_pow_left₀ h1 (by gcongr) 2
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hint1 : Integrable L μ := integrable_log_norm_sq_div_sq_of_hasLaw_gaussianVector hg hu1
  have hint2 : Integrable (fun ω => L ω ^ 2) μ :=
    integrable_log_norm_sq_div_sq_sq_of_hasLaw_gaussianVector hg hu1
  have hexp : (fun ω => (1 + L ω / Real.log 2) ^ 2) =
      fun ω => 1 + (2 / Real.log 2 * L ω + 1 / Real.log 2 ^ 2 * L ω ^ 2) := by
    funext ω
    field_simp
    ring
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure
  have hint : Integrable (fun ω => (1 + L ω / Real.log 2) ^ 2) μ := by
    rw [hexp]
    exact (integrable_const _).add ((hint1.const_mul _).add (hint2.const_mul _))
  have hint0 :=
    integrable_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_of_hasLaw_gaussianVector hg A q
  refine (integral_mono_ae hint0 (hint.const_mul _) hpt).trans ?_
  have hsum : ∫ ω, (1 + L ω / Real.log 2) ^ 2 ∂μ =
      1 + (2 / Real.log 2 * ∫ ω, L ω ∂μ + 1 / Real.log 2 ^ 2 * ∫ ω, L ω ^ 2 ∂μ) := by
    rw [hexp, integral_add (f := fun _ => (1 : ℝ))
      (g := fun ω => 2 / Real.log 2 * L ω + 1 / Real.log 2 ^ 2 * L ω ^ 2) (integrable_const _)
      ((hint1.const_mul _).add (hint2.const_mul _)),
      integral_add (f := fun ω => 2 / Real.log 2 * L ω)
      (g := fun ω => 1 / Real.log 2 ^ 2 * L ω ^ 2) (hint1.const_mul _) (hint2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const, smul_eq_mul, probReal_univ,
      one_mul]
  rw [integral_const_mul, hsum]
  have hE1 : ∫ ω, L ω ∂μ ≤ Real.log (2 * Fintype.card n) + 2 :=
    integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector hg hu1
  have hE2 : ∫ ω, L ω ^ 2 ∂μ ≤
      Real.log (2 * Fintype.card n) ^ 2 + 4 * Real.log (2 * Fintype.card n) + 8 :=
    integral_log_norm_sq_div_sq_sq_le_of_hasLaw_gaussianVector hg hu1
  set T := Real.log (2 * Fintype.card n)
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc 4 * eigenvalue A 0 / q ^ 2 * (1 + (2 / Real.log 2 * ∫ ω, L ω ∂μ +
          1 / Real.log 2 ^ 2 * ∫ ω, L ω ^ 2 ∂μ))
      ≤ 4 * eigenvalue A 0 / q ^ 2 * (1 + (2 / Real.log 2 * (T + 2) +
          1 / Real.log 2 ^ 2 * (T ^ 2 + 4 * T + 8))) := by
        gcongr
    _ = randomStartLanczosBound (Fintype.card n) q * eigenvalue A 0 := by
        rw [randomStartLanczosBound_def]
        field_simp
        ring

/-! ### Asymptotic forms -/

/-- **$O(\log(N)/\varepsilon)$ multiplications suffice for the random-start power method**:
there is an absolute constant $C > 0$ such that for every positive semidefinite real
$\mathbf{A}$ of size $N = \lvert n\rvert$, a standard Gaussian start $\mathbf{g}$ (law
$\mathcal{N}(\mathbf{0}, \mathbf{I})$ on $\mathbb{R}^n$), $\varepsilon > 0$ and
$q \ge C\log(2N)/\varepsilon$ multiplications,
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{g})\bigr] \le
\varepsilon\,\lambda_0(\mathbf{A})\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient. The asymptotic form of
`NLAlib.integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector`.
[MartinssonTropp2020, Theorem 6.1].
Asymptotic:
NLAlib.integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector
Result: random-start-power -/
theorem
exists_forall_integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {n : Type} [Fintype n]
      [DecidableEq n] {g : Ω → n → ℝ}, HasLaw g (gaussianVector n) μ →
      ∀ {A : Matrix n n ℝ}, A.PosSemidef → ∀ (ε : ℝ) (q : ℕ), 0 < ε →
        C * Real.log (2 * Fintype.card n) / ε ≤ q →
          ∫ ω, (eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) ∂μ ≤ ε * eigenvalue A 0 := by
  refine ⟨3, by norm_num, fun {Ω _ μ n _ _ g} hg {A} hA ε q hε hq => ?_⟩
  refine (integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector hg hA
    q).trans ?_
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · rw [eigenvalue_of_card_le A hn.le, mul_zero, mul_zero]
  refine mul_le_mul_of_nonneg_right ?_ (hA.eigenvalue_nonneg 0)
  have hl : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hT : Real.log 2 ≤ Real.log (2 * Fintype.card n) :=
    Real.log_le_log two_pos (by have : (1 : ℝ) ≤ Fintype.card n := (by exact_mod_cast hn); linarith)
  rw [div_le_iff₀ hε] at hq
  rw [randomStartPowerBound_def, div_le_iff₀ (by positivity)]
  nlinarith

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(N)/\sqrt{\varepsilon})$ multiplications suffice for random-start Lanczos**: there
is an absolute constant $C > 0$ such that for every positive semidefinite real $\mathbf{A}$ of
size $N = \lvert n\rvert$, a standard Gaussian start $\mathbf{g}$ (law
$\mathcal{N}(\mathbf{0}, \mathbf{I})$ on $\mathbb{R}^n$), $\varepsilon > 0$ and
$q \ge C\log(2N)/\sqrt{\varepsilon}$ multiplications, the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$, written as $\lambda_0(\mathbf{P}\mathbf{A}\mathbf{P})$
with $\mathbf{P}$ the orthogonal projector onto it, satisfies
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \theta_0\bigr] \le \varepsilon\,\lambda_0(\mathbf{A})\,.$$
The asymptotic form of
`NLAlib.integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector`.
[MartinssonTropp2020, Theorem 6.2].
Asymptotic:
NLAlib.integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector
Result: random-start-lanczos -/
theorem
exists_forall_integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {n : Type} [Fintype n]
      [DecidableEq n] {g : Ω → n → ℝ}, HasLaw g (gaussianVector n) μ →
      ∀ {A : Matrix n n ℝ}, A.PosSemidef → ∀ (ε : ℝ) (q : ℕ), 0 < ε →
        C * Real.log (2 * Fintype.card n) / √ε ≤ q →
          ∫ ω, (eigenvalue A 0 -
              eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) * A *
                rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) ∂μ ≤ ε * eigenvalue A 0 := by
  refine ⟨30, by norm_num, fun {Ω _ μ n _ _ g} hg {A} hA ε q hε hq => ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · have h : ∀ ω, eigenvalue A 0 - eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) *
        A * rangeProjector (krylovMatrix A (g ω) (q + 1))) 0 = 0 := fun ω => by
      rw [eigenvalue_of_card_le A hn.le, eigenvalue_of_card_le _ hn.le, sub_zero]
    simp only [h, integral_zero]
    rw [eigenvalue_of_card_le A hn.le, mul_zero]
  have hl : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  set T := Real.log (2 * Fintype.card n)
  have hT : Real.log 2 ≤ T :=
    Real.log_le_log two_pos (by have : (1 : ℝ) ≤ Fintype.card n := (by exact_mod_cast hn); linarith)
  have hsε := Real.sqrt_pos.2 hε
  rw [div_le_iff₀ hsε] at hq
  have hq0 : (0 : ℝ) < q := by
    by_contra h
    nlinarith
  have hq1 : 1 ≤ q := by exact_mod_cast hq0
  refine (integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector hg
    hA hq1).trans (mul_le_mul_of_nonneg_right ?_ (hA.eigenvalue_nonneg 0))
  have hq2 : 900 * T ^ 2 ≤ q ^ 2 * ε := by
    have h := pow_le_pow_left₀ (by linarith) hq 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hε.le] at h
    linarith
  rw [randomStartLanczosBound_def, div_le_iff₀ (by positivity)]
  have h6 : T + 2 + Real.log 2 ≤ 6 * T := by linarith
  have hX : (T + 2 + Real.log 2) ^ 2 + 4 ≤ 52 * T ^ 2 := by
    nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ T + 2 + Real.log 2) h6 2]
  have hl2 : 1 / 4 ≤ Real.log 2 ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ Real.log 2 ^ 2),
    mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ T ^ 2)]

end NLAlib
