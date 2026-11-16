/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import NLAlib.Probability.Tail
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.InverseMoments.Spectral

/-!
# Clipped inverse moments of the smallest singular value of a Gaussian matrix

For a standard Gaussian $m \times n$ matrix $\mathbf{G}$ with $100n \le m$ and $900 \le m$, the
smallest eigenvalue of $\mathbf{G}^{\mathsf{H}}\mathbf{G}/m$, clipped at $1$,
$\bar\lambda = \min\{1, \sigma_{\min}(\mathbf{G})^2/m\}$, has inverse moments within $O(m^{-1/2})$
of those of its mean-field value $(1 - \sqrt{n/m})^2$, for $q \le 4$. These are the moments of
the head constant in the structural bound of early truncation
(`NLAlib.IsSubspaceInjection.frobNorm_sub_mul_sq_le`), which an expectation bound integrates.

The proof splits $\bar\lambda^{-q}$ at $\sigma_{\min} = 5$. Above, the layer-cake formula on the
deviation $(\sqrt{m} - \sqrt{n} - \sigma_{\min})^+$, whose tail is Gordon's
(`NLAlib.measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix`), gives the leading term and
a Gaussian integral of order $m^{-1/2}$; below, Cauchy–Schwarz with the second moment (from the
spectral moments of the pseudoinverse,
`NLAlib.integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`) and the same tail at
$\sqrt{m} - \sqrt{n} - 5$ give at most $m^{-1/2}$.

The extreme singular values themselves (Gordon's bounds and their tails) are in
`NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues`, the unclipped inverse moments in
`NLAlib.RandomMatrix.Gaussian.InverseMoments.Spectral`.


## Main results

* `NLAlib.integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix`: the
  clipped inverse moments.
* `NLAlib.gaussianClippedInvMomentConstant q`: the constant, at
  present <!-- value gaussianClippedInvMomentConstant q -->
  $2q (0.9)^{-(2q + 1)} e^{(2q + 1)^2/50}\sqrt{2\pi} + 1$, with
  `NLAlib.gaussianClippedInvMomentConstant_one_le_10` and
  `NLAlib.gaussianClippedInvMomentConstant_four_le_263`.
* `NLAlib.integrable_min_one_singularValues_sq_div_inv_pow_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped Matrix ENNReal

namespace NLAlib

/-- **The clipped inverse-moment constant**, at
present <!-- value gaussianClippedInvMomentConstant q -->
$$2q (0.9)^{-(2q + 1)} e^{(2q + 1)^2/50}\sqrt{2\pi} + 1\,,$$
the constant of
`NLAlib.integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix`: its first
term is the Gaussian integral of the layer-cake formula, the $1$ the small-ball piece. Source
value: none; proved without a literature source. Value proved: as displayed. Consumers use
`NLAlib.gaussianClippedInvMomentConstant_one_le_10` and
`NLAlib.gaussianClippedInvMomentConstant_four_le_263`. -/
noncomputable irreducible_def gaussianClippedInvMomentConstant (q : ℕ) : ℝ :=
  2 * q * 0.9 ^ (-(2 * q + 1 : ℤ)) * Real.exp ((2 * q + 1) ^ 2 / 50) * √(2 * π) + 1

/-- The explicit value the documentation displays: the clipped inverse-moment constant is at
most <!-- value gaussianClippedInvMomentConstant q -->
$2q (0.9)^{-(2q + 1)} e^{(2q + 1)^2/50}\sqrt{2\pi} + 1$ (at present an equality). -/
theorem gaussianClippedInvMomentConstant_le (q : ℕ) :
    gaussianClippedInvMomentConstant q ≤
      2 * q * 0.9 ^ (-(2 * q + 1 : ℤ)) * Real.exp ((2 * q + 1) ^ 2 / 50) * √(2 * π) + 1 := by
  rw [gaussianClippedInvMomentConstant_def]

private theorem sqrt_two_mul_pi_le : √(2 * π) ≤ 2.5067 := by
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [Real.pi_lt_d6]

private theorem exp_nine_div_fifty_le : Real.exp (9 / 50) ≤ 1.1973 := by
  have h := Real.exp_bound' (x := 9 / 50) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem exp_eighty_one_div_fifty_le : Real.exp (81 / 50) ≤ 5.0532 := by
  have h := Real.exp_bound' (x := 81 / 100) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  have e : Real.exp (81 / 50) = Real.exp (81 / 100) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 : 0 ≤ Real.exp (81 / 100) := (Real.exp_pos _).le
  have h2 : Real.exp (81 / 100) ≤ 2.24792 := h.trans (by
    norm_num [Finset.sum_range_succ, Nat.factorial])
  nlinarith

/-- The clipped inverse-moment constant at $q = 1$ is at most $10$: the
value <!-- value gaussianClippedInvMomentConstant q -->
$2q (0.9)^{-(2q + 1)} e^{(2q + 1)^2/50}\sqrt{2\pi} + 1$ at $q = 1$ is $9.234$ to three
decimals (`gaussianClippedInvMomentConstant 1`). -/
theorem gaussianClippedInvMomentConstant_one_le_10 : gaussianClippedInvMomentConstant 1 ≤ 10 := by
  rw [gaussianClippedInvMomentConstant_def]
  have h1 := sqrt_two_mul_pi_le
  have h2 := exp_nine_div_fifty_le
  have h3 : (0.9 : ℝ) ^ (-(2 * ((1 : ℕ) : ℤ) + 1 : ℤ)) = 1000 / 729 := by norm_num
  have h4 : Real.exp ((2 * ((1 : ℕ) : ℝ) + 1) ^ 2 / 50) = Real.exp (9 / 50) := by norm_num
  push_cast at h3 h4 ⊢
  rw [h3, h4]
  have h5 : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  have h6 : 0 ≤ Real.exp (9 / 50) := (Real.exp_pos _).le
  nlinarith [mul_le_mul h2 h1 h5 (by norm_num)]

/-- The clipped inverse-moment constant at $q = 4$ is at most $263$: the
value <!-- value gaussianClippedInvMomentConstant q -->
$2q (0.9)^{-(2q + 1)} e^{(2q + 1)^2/50}\sqrt{2\pi} + 1$ at $q = 4$ is $262.55$ to two decimals
(`gaussianClippedInvMomentConstant 4`). -/
theorem gaussianClippedInvMomentConstant_four_le_263 :
    gaussianClippedInvMomentConstant 4 ≤ 263 := by
  rw [gaussianClippedInvMomentConstant_def]
  have h1 := sqrt_two_mul_pi_le
  have h2 := exp_eighty_one_div_fifty_le
  have h3 : (0.9 : ℝ) ^ (-(2 * ((4 : ℕ) : ℤ) + 1 : ℤ)) = 1000000000 / 387420489 := by norm_num
  have h4 : Real.exp ((2 * ((4 : ℕ) : ℝ) + 1) ^ 2 / 50) = Real.exp (81 / 50) := by norm_num
  push_cast at h3 h4 ⊢
  rw [h3, h4]
  have h5 : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  have h6 : 0 ≤ Real.exp (81 / 50) := (Real.exp_pos _).le
  nlinarith [mul_le_mul h2 h1 h5 (by norm_num)]

/-! ### Pointwise facts -/

/-- The clipped inverse power of $s^2/M$ is at most $\max(1, M^q s^{-2q})$. -/
private theorem min_one_sq_div_inv_pow_le_max (s M : ℝ) (q : ℕ) :
    (min 1 (s ^ 2 / M))⁻¹ ^ q ≤ max 1 (M ^ q * s⁻¹ ^ (2 * q)) := by
  rcases le_total 1 (s ^ 2 / M) with h | h
  · rw [min_eq_left h, inv_one, one_pow]
    exact le_max_left _ _
  · rw [min_eq_right h, inv_div, div_eq_mul_inv, mul_pow, ← inv_pow, ← pow_mul, mul_comm 2 q]
    exact le_max_right _ _

/-- The clipped inverse power is nonnegative for $M \ge 0$. -/
private theorem min_one_sq_div_inv_pow_nonneg (s : ℝ) {M : ℝ} (hM : 0 ≤ M) (q : ℕ) :
    0 ≤ (min 1 (s ^ 2 / M))⁻¹ ^ q :=
  pow_nonneg (inv_nonneg.2 (le_min zero_le_one (div_nonneg (sq_nonneg s) hM))) q

/-- The clipped inverse power is a measurable function of $s$. -/
private theorem measurable_min_one_sq_div_inv_pow (M : ℝ) (q : ℕ) :
    Measurable fun s : ℝ => (min 1 (s ^ 2 / M))⁻¹ ^ q := by
  fun_prop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- For a tall standard Gaussian matrix the inverse smallest singular value is almost surely the
spectral norm of the pseudoinverse of the (wide, standard Gaussian) transpose. -/
private theorem ae_inv_singularValues_eq (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ}
    (hk : k + 1 = Fintype.card n) (hnm : Fintype.card n ≤ Fintype.card m) :
    ∀ᵐ ω ∂μ, (singularValues (X ω) k)⁻¹ = specNorm (pinv (X ω)ᴴ) := by
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hX] with ω hω
  rw [pinv_conjTranspose, specNorm_conjTranspose, specNorm_pinv _ (hk.trans (by omega))]

/-- The clipped inverse power is at most $\max(1, M^q\|\mathbf{G}^{\mathsf{H}+}\|_2^{2q})$ almost
surely. -/
private theorem ae_min_one_sq_div_inv_pow_le (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ}
    (hk : k + 1 = Fintype.card n) (hnm : Fintype.card n ≤ Fintype.card m) (q : ℕ) :
    ∀ᵐ ω ∂μ, (min 1 (singularValues (X ω) k ^ 2 / Fintype.card m))⁻¹ ^ q ≤
      max 1 ((Fintype.card m : ℝ) ^ q * specNorm (pinv (X ω)ᴴ) ^ (2 * q)) := by
  filter_upwards [ae_inv_singularValues_eq hX hk hnm] with ω hω
  rw [← hω]
  exact min_one_sq_div_inv_pow_le_max _ _ q

/-- The integrable majorant $1 + M^q\|\mathbf{G}^{\mathsf{H}+}\|_2^{2q}$, for $2q \le m - n$. -/
private theorem integrable_one_add_pow_mul_specNorm_pinv_pow
    (hX : HasLaw X (gaussianMatrix m n) μ) {q : ℕ}
    (hq : 2 * q + Fintype.card n ≤ Fintype.card m) (c : ℝ) :
    Integrable (fun ω => 1 + c * specNorm (pinv (X ω)ᴴ) ^ (2 * q)) μ := by
  have := hX.isProbabilityMeasure
  have hY := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simp only [mul_zero, pow_zero, mul_one]
    exact integrable_const _
  have hq' : ((2 * q : ℕ) : ℝ) ≤ (Fintype.card m : ℝ) - Fintype.card n := by
    have : ((2 * q + Fintype.card n : ℕ) : ℝ) ≤ Fintype.card m := by exact_mod_cast hq
    push_cast at this ⊢
    linarith
  have h := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hY
    (q := ((2 * q : ℕ) : ℝ)) (by positivity) hq'
  simp only [Real.rpow_natCast] at h
  exact (integrable_const 1).add (h.const_mul c)

/-! ### Integrability -/

/-- Integrability of the clipped inverse moment: for a standard Gaussian $m \times n$ matrix
$\mathbf{G}$ and $2q + n \le m$, $\min\{1, \sigma_{\min}(\mathbf{G})^2/m\}^{-q}$ is integrable. -/
theorem integrable_min_one_singularValues_sq_div_inv_pow_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ} (hk : k + 1 = Fintype.card n) {q : ℕ}
    (hq : 2 * q + Fintype.card n ≤ Fintype.card m) :
    Integrable (fun ω => (min 1 (singularValues (X ω) k ^ 2 / Fintype.card m))⁻¹ ^ q) μ := by
  have hm : Measurable fun ω' : Matrix m n ℝ =>
      (min 1 (singularValues ω' k ^ 2 / Fintype.card m))⁻¹ ^ q :=
    (measurable_min_one_sq_div_inv_pow _ q).comp (measurable_singularValues k)
  refine (integrable_one_add_pow_mul_specNorm_pinv_pow hX hq ((Fintype.card m : ℝ) ^ q)).mono'
    (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable ?_
  filter_upwards [ae_min_one_sq_div_inv_pow_le hX hk (by omega) q] with ω hω
  rw [Real.norm_of_nonneg (min_one_sq_div_inv_pow_nonneg _ (Nat.cast_nonneg _) q)]
  refine hω.trans (max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left
    zero_le_one))


/-! ### The layer-cake integrand -/

/-- The Gaussian integral of the layer-cake integrand:
$\int_0^\infty e^{cv} e^{-v^2/2}\,dv \le e^{c^2/2}\sqrt{2\pi}$. -/
private theorem setLIntegral_exp_mul_mul_exp_neg_sq_le (c : ℝ) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Real.exp (c * t) * Real.exp (-t ^ 2 / 2)) ≤
      ENNReal.ofReal (Real.exp (c ^ 2 / 2) * √(2 * π)) := by
  have e (t : ℝ) : Real.exp (c * t) * Real.exp (-t ^ 2 / 2) =
      Real.exp (c ^ 2 / 2) * Real.exp (-(1 / 2) * (t - c) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hint : Integrable (fun t : ℝ => Real.exp (c ^ 2 / 2) * Real.exp (-(1 / 2) * (t - c) ^ 2)) :=
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right c).const_mul _
  calc _ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (c * t) * Real.exp (-t ^ 2 / 2)) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ t, Real.exp (c ^ 2 / 2) * Real.exp (-(1 / 2) * (t - c) ^ 2)) := by
        simp_rw [e]
        rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
    _ = ENNReal.ofReal (Real.exp (c ^ 2 / 2) * √(2 * π)) := by
        rw [integral_const_mul,
          integral_sub_right_eq_self (μ := volume) (fun t => Real.exp (-(1 / 2) * t ^ 2)) c,
          integral_gaussian]
        congr 3
        ring

/-- The layer-cake integrand against $e^{cv}$: for $a > 0$, $v \ge 0$, with
$w = \max(a - v, 5)$, $w^{-j} \le a^{-j} e^{jv/5}$. -/
private theorem inv_max_sub_pow_le {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) (j : ℕ) :
    ((max (a - v) 5) ^ j)⁻¹ ≤ (a ^ j)⁻¹ * Real.exp (j / 5 * v) := by
  set w := max (a - v) 5 with hw
  have hw5 : 5 ≤ w := le_max_right _ _
  have hwa : a - v ≤ w := le_max_left _ _
  have hw0 : 0 < w := by linarith
  have h1 : a ≤ w * (1 + v / 5) := by nlinarith
  have h2 : 1 + v / 5 ≤ Real.exp (v / 5) := by linarith [Real.add_one_le_exp (v / 5)]
  have h3 : a ≤ w * Real.exp (v / 5) := h1.trans (mul_le_mul_of_nonneg_left h2 hw0.le)
  have key : a ^ j ≤ w ^ j * Real.exp (j / 5 * v) := by
    have := pow_le_pow_left₀ ha.le h3 j
    rwa [mul_pow, ← Real.exp_nat_mul, show (j : ℝ) * (v / 5) = j / 5 * v by ring] at this
  have hwj : 0 < w ^ j := pow_pos hw0 j
  have haj : 0 < a ^ j := pow_pos ha j
  calc (w ^ j)⁻¹ = (a ^ j)⁻¹ * (a ^ j / w ^ j) := by field_simp
    _ ≤ (a ^ j)⁻¹ * Real.exp (j / 5 * v) := by
        gcongr
        rw [div_le_iff₀ hwj]
        linarith [mul_comm (w ^ j) (Real.exp (j / 5 * v))]

/-- The layer-cake integrand $g(v) = 2q M^q \max(a - v, 5)^{-(2q+1)}$ is continuous. -/
private theorem continuous_layerCake (M a : ℝ) (q : ℕ) :
    Continuous fun v : ℝ => 2 * q * M ^ q * ((max (a - v) 5) ^ (2 * q + 1))⁻¹ := by
  have hc : Continuous fun v : ℝ => max (a - v) 5 := by fun_prop
  exact continuous_const.mul ((hc.pow _).inv₀ fun v =>
    pow_ne_zero _ (by linarith [le_max_right (a - v) 5] : (0 : ℝ) < max (a - v) 5).ne')

/-- The layer-cake integrand is nonnegative for $M \ge 0$. -/
private theorem layerCake_nonneg {M : ℝ} (hM : 0 ≤ M) (a : ℝ) (q : ℕ) (v : ℝ) :
    0 ≤ 2 * q * M ^ q * ((max (a - v) 5) ^ (2 * q + 1))⁻¹ := by
  have : 0 < max (a - v) 5 := by linarith [le_max_right (a - v) 5]
  positivity

/-- **The pointwise split of the clipped inverse power**: for $5 \le a$ and
$a^2 \le M$, with $g$ the layer-cake integrand,
$\min\{1, s^2/M\}^{-q} \le M^q a^{-2q} + \int_0^{(a - s)^+} g + \mathbf{1}_{s < 5}\min\{1,
s^2/M\}^{-q}$. -/
private theorem min_one_sq_div_inv_pow_le_add {s M a : ℝ} (ha5 : 5 ≤ a)
    (haM : a ^ 2 ≤ M) (q : ℕ) :
    (min 1 (s ^ 2 / M))⁻¹ ^ q ≤ M ^ q * (a ^ (2 * q))⁻¹ +
      (∫ v in (0)..max (a - s) 0, 2 * q * M ^ q * ((max (a - v) 5) ^ (2 * q + 1))⁻¹) +
        (Set.Iio 5).indicator (fun s => (min 1 (s ^ 2 / M))⁻¹ ^ q) s := by
  have ha0 : 0 < a := by linarith
  have hM : 0 < M := lt_of_lt_of_le (by positivity) haM
  have hI : 0 ≤ ∫ v in (0)..max (a - s) 0, 2 * q * M ^ q * ((max (a - v) 5) ^ (2 * q + 1))⁻¹ :=
    intervalIntegral.integral_nonneg (le_max_right _ _) fun v _ => layerCake_nonneg hM.le a q v
  have hA : 0 ≤ M ^ q * (a ^ (2 * q))⁻¹ := by positivity
  by_cases h5 : s < 5
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 h5)]
    linarith
  rw [Set.indicator_of_notMem (by simpa using h5), add_zero]
  push Not at h5
  have hs0 : 0 < s := by linarith
  by_cases hsa : a ≤ s
  · rw [max_eq_right (by linarith), intervalIntegral.integral_same, add_zero]
    have h1 : a ^ 2 / M ≤ min 1 (s ^ 2 / M) :=
      le_min ((div_le_one hM).2 haM) (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ ha0.le hsa 2) hM.le)
    have h2 : (min 1 (s ^ 2 / M))⁻¹ ≤ (a ^ 2 / M)⁻¹ := inv_anti₀ (by positivity) h1
    rw [inv_div] at h2
    calc (min 1 (s ^ 2 / M))⁻¹ ^ q ≤ (M / a ^ 2) ^ q :=
          pow_le_pow_left₀ (inv_nonneg.2 (le_min zero_le_one (by positivity))) h2 q
      _ = M ^ q * (a ^ (2 * q))⁻¹ := by rw [div_pow, ← pow_mul, div_eq_mul_inv]
  push Not at hsa
  rw [max_eq_left (by linarith)]
  have hsM : s ^ 2 / M ≤ 1 := (div_le_one hM).2 (le_trans
    (pow_le_pow_left₀ hs0.le hsa.le 2) haM)
  -- the fundamental theorem of calculus for $v \mapsto M^q (a - v)^{-2q}$
  have hderiv : ∀ v ∈ Set.uIcc 0 (a - s), HasDerivAt
      (fun v => M ^ q * (a - v) ^ (-(2 * q : ℤ)))
      (2 * q * M ^ q * ((max (a - v) 5) ^ (2 * q + 1))⁻¹) v := by
    intro v hv
    rw [Set.uIcc_of_le (by linarith)] at hv
    have hav : s ≤ a - v := by linarith [hv.2]
    have hne : a - v ≠ 0 := by linarith
    have h : HasDerivAt (fun v => M ^ q * (a - v) ^ (-(2 * q : ℤ)))
        (M ^ q * (((-(2 * q : ℤ) : ℤ) : ℝ) * (a - v) ^ (-(2 * q : ℤ) - 1) * -1)) v :=
      ((hasDerivAt_zpow (-(2 * q : ℤ)) (a - v) (Or.inl hne)).comp v
        ((hasDerivAt_id v).const_sub a)).const_mul (M ^ q)
    refine h.congr_deriv ?_
    rw [max_eq_left (by linarith), show (-(2 * q : ℤ) - 1) = -((2 * q + 1 : ℕ) : ℤ) by
      push_cast; ring, zpow_neg, zpow_natCast]
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_layerCake M a q).intervalIntegrable _ _)]
  simp only [sub_sub_cancel, sub_zero, zpow_neg]
  rw [min_eq_right hsM, inv_div, div_pow, ← pow_mul, div_eq_mul_inv]
  have : (2 * q : ℤ) = ((2 * q : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_natCast, zpow_natCast]
  linarith


/-! ### Numerical facts -/

/-- The small-ball piece is negligible: for $M \ge 900$ and $a \ge 0.9\sqrt{M}$,
$45400\,M \le e^{(a - 5)^2/2}$. -/
private theorem mul_le_exp_sub_five_sq {M a : ℝ} (hM : 900 ≤ M) (ha : 0.9 * √M ≤ a) :
    45400 * M ≤ Real.exp ((a - 5) ^ 2 / 2) := by
  have hx : 30 ≤ √M := Real.le_sqrt_of_sq_le (by linarith)
  have hxx : √M ^ 2 = M := Real.sq_sqrt (by linarith)
  have h1 : 11 / 15 * √M ≤ a - 5 := by linarith
  have h2 : (121 / 450) * M ≤ (a - 5) ^ 2 / 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, hxx] at this
    linarith
  have h3 := Real.pow_div_factorial_le_exp (x := (121 / 450) * M) (by positivity) 4
  have h4 : (900 : ℝ) ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (by norm_num) hM 3
  have h5 : 45400 * M ≤ ((121 / 450) * M) ^ 4 / (Nat.factorial 4 : ℝ) := by
    norm_num [Nat.factorial]
    nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ M)]
  exact h5.trans (h3.trans (Real.exp_le_exp.2 h2))

/-- The inverse-moment constant of the transpose: for $100n \le m$,
$m\beta(n, m)^2 \le 3.82$ with $\beta(n, m) = (e/(m - n))\sqrt{(m + n - 1)/2}$. -/
private theorem mul_sq_le {M N : ℝ} (hN : 0 ≤ N) (hNM : 100 * N ≤ M) (hM : 900 ≤ M) :
    M * (Real.exp 1 / (M - N) * √((M + N - 1) / 2)) ^ 2 ≤ 3.82 := by
  have he : Real.exp 1 ^ 2 ≤ 7.3891 := by
    have := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos 1]
  have hMN : 0 < M - N := by linarith
  rw [mul_pow, div_pow, Real.sq_sqrt (by linarith)]
  have h1 : (M + N - 1) / 2 ≤ 1.01 * M / 2 := by linarith
  have h2 : 0.9801 * M ^ 2 ≤ (M - N) ^ 2 := by nlinarith
  have key : M * (Real.exp 1 ^ 2 * ((M + N - 1) / 2)) ≤ 3.82 * (M - N) ^ 2 :=
    calc M * (Real.exp 1 ^ 2 * ((M + N - 1) / 2)) ≤ M * (7.3891 * (1.01 * M / 2)) := by
          gcongr
          linarith
      _ ≤ 3.82 * (M - N) ^ 2 := by nlinarith
  calc M * (Real.exp 1 ^ 2 / (M - N) ^ 2 * ((M + N - 1) / 2)) =
        M * (Real.exp 1 ^ 2 * ((M + N - 1) / 2)) / (M - N) ^ 2 := by ring
    _ ≤ 3.82 := by rw [div_le_iff₀ (by positivity)]; exact key

/-! ### The main estimate -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- The second moment of the clipped inverse power is at most $45400$, for $q \le 4$,
$100n \le m$ and $900 \le m$. -/
private theorem integral_min_one_sq_div_inv_pow_sq_le (hX : HasLaw X (gaussianMatrix m n) μ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) (hnm : 100 * Fintype.card n ≤ Fintype.card m)
    (hm : 900 ≤ Fintype.card m) {q : ℕ} (hq4 : q ≤ 4) :
    Integrable (fun ω => ((min 1 (singularValues (X ω) k ^ 2 / Fintype.card m))⁻¹ ^ q) ^ 2) μ ∧
      ∫ ω, ((min 1 (singularValues (X ω) k ^ 2 / Fintype.card m))⁻¹ ^ q) ^ 2 ∂μ ≤ 45400 := by
  have := hX.isProbabilityMeasure
  set M := (Fintype.card m : ℝ) with hMdef
  set N := (Fintype.card n : ℝ) with hNdef
  have hM : (900 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hm
  have hNM : 100 * N ≤ M := by rw [hMdef, hNdef]; exact_mod_cast hnm
  have hq4' : 2 * (2 * q) + Fintype.card n ≤ Fintype.card m := by omega
  have hY := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX
  have hmaj := integrable_one_add_pow_mul_specNorm_pinv_pow hX hq4' (M ^ (2 * q))
  have hm' : Measurable fun ω' : Matrix m n ℝ =>
      ((min 1 (singularValues ω' k ^ 2 / M))⁻¹ ^ q) ^ 2 :=
    ((measurable_min_one_sq_div_inv_pow _ q).comp (measurable_singularValues k)).pow_const 2
  have hle : ∀ᵐ ω ∂μ, ((min 1 (singularValues (X ω) k ^ 2 / M))⁻¹ ^ q) ^ 2 ≤
      1 + M ^ (2 * q) * specNorm (pinv (X ω)ᴴ) ^ (2 * (2 * q)) := by
    filter_upwards [ae_min_one_sq_div_inv_pow_le hX hk (by omega) q] with ω hω
    have h0 := min_one_sq_div_inv_pow_nonneg (singularValues (X ω) k) (Nat.cast_nonneg
      (Fintype.card m)) q
    have hx : 0 ≤ M ^ q * specNorm (pinv (X ω)ᴴ) ^ (2 * q) := by positivity
    have e : M ^ (2 * q) * specNorm (pinv (X ω)ᴴ) ^ (2 * (2 * q)) =
        (M ^ q * specNorm (pinv (X ω)ᴴ) ^ (2 * q)) ^ 2 := by ring
    rw [e]
    calc _ ≤ (max 1 (M ^ q * specNorm (pinv (X ω)ᴴ) ^ (2 * q))) ^ 2 :=
          pow_le_pow_left₀ h0 hω 2
      _ ≤ _ := by
          rcases le_total 1 (M ^ q * specNorm (pinv (X ω)ᴴ) ^ (2 * q)) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; nlinarith
  have hint : Integrable (fun ω => ((min 1 (singularValues (X ω) k ^ 2 / M))⁻¹ ^ q) ^ 2) μ :=
    hmaj.mono' (hm'.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
      (hle.mono fun ω hω => by rwa [Real.norm_of_nonneg (by positivity)])
  refine ⟨hint, (integral_mono_ae hint hmaj hle).trans ?_⟩
  rw [integral_add (integrable_const _) (hmaj.sub (integrable_const 1) |>.congr
    (ae_of_all _ fun ω => by simp)), integral_const, probReal_univ, one_smul, integral_const_mul]
  -- the spectral moment of the pseudoinverse
  have hβ : M ^ (2 * q) * ∫ ω, specNorm (pinv (X ω)ᴴ) ^ (2 * (2 * q)) ∂μ ≤ 3.82 ^ 8 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · norm_num
    have hr : ((2 * (2 * q) : ℕ) : ℝ) ≤ (Fintype.card m : ℝ) - Fintype.card n := by
      have : ((2 * (2 * q) + Fintype.card n : ℕ) : ℝ) ≤ Fintype.card m := by exact_mod_cast hq4'
      push_cast at this ⊢
      linarith
    have h := integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix hY
      (q := ((2 * (2 * q) : ℕ) : ℝ)) (by positivity) hr
    simp only [Real.rpow_natCast] at h
    have hB := mul_sq_le (Nat.cast_nonneg _) hNM hM
    set β := Real.exp 1 / (M - N) * √((M + N - 1) / 2)
    calc M ^ (2 * q) * ∫ ω, specNorm (pinv (X ω)ᴴ) ^ (2 * (2 * q)) ∂μ ≤ M ^ (2 * q) *
          β ^ (2 * (2 * q)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = (M * β ^ 2) ^ (2 * q) := by ring
      _ ≤ 3.82 ^ (2 * q) := pow_le_pow_left₀ (by positivity) hB _
      _ ≤ 3.82 ^ 8 := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hβ ⊢
  linarith


/-- The layer-cake part: with $a = \sqrt{m} - \sqrt{n} \ge 5$ and $V = (a - \sigma_{\min})^+$,
$\mathbb{E}\int_0^V g \le 2q m^q a^{-(2q+1)} e^{c^2/2}\sqrt{2\pi}$, $c = (2q+1)/5$, together with
the integrability of $\int_0^V g$. -/
private theorem integral_layerCake_le (hX : HasLaw X (gaussianMatrix m n) μ) (hXm : Measurable X)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {a : ℝ}
    (ha : a = √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) (ha5 : 5 ≤ a) (q : ℕ) :
    Integrable (fun ω => ∫ v in (0)..max (a - singularValues (X ω) k) 0,
      2 * q * (Fintype.card m : ℝ) ^ q * ((max (a - v) 5) ^ (2 * q + 1))⁻¹) μ ∧
    ∫ ω, (∫ v in (0)..max (a - singularValues (X ω) k) 0,
      2 * q * (Fintype.card m : ℝ) ^ q * ((max (a - v) 5) ^ (2 * q + 1))⁻¹) ∂μ ≤
      2 * q * (Fintype.card m : ℝ) ^ q * (a ^ (2 * q + 1))⁻¹ *
        (Real.exp (((2 * q + 1) / 5) ^ 2 / 2) * √(2 * π)) := by
  have := hX.isProbabilityMeasure
  set M := (Fintype.card m : ℝ)
  set g : ℝ → ℝ := fun v => 2 * q * M ^ q * ((max (a - v) 5) ^ (2 * q + 1))⁻¹ with hgdef
  have hg : Continuous g := continuous_layerCake M a q
  have hg0 (v : ℝ) : 0 ≤ g v := layerCake_nonneg (Nat.cast_nonneg _) a q v
  have ha0 : 0 < a := by linarith
  set C := 2 * q * M ^ q * (a ^ (2 * q + 1))⁻¹ with hCdef
  have hC0 : 0 ≤ C := by positivity
  set c := ((2 * q + 1 : ℝ) / 5)
  set V : Ω → ℝ := fun ω => max (a - singularValues (X ω) k) 0
  have hVm : Measurable V :=
    (measurable_const.sub ((measurable_singularValues k).comp hXm)).max measurable_const
  have hΦ : Continuous fun x => ∫ v in (0)..x, g v :=
    intervalIntegral.continuous_primitive (fun _ _ => hg.intervalIntegrable _ _) 0
  have hΦ0 (ω : Ω) : 0 ≤ ∫ v in (0)..V ω, g v :=
    intervalIntegral.integral_nonneg (le_max_right _ _) fun v _ => hg0 v
  -- the tail of the deviation
  have htail (t : ℝ) (ht : t ∈ Set.Ioi 0) :
      μ {ω | t < V ω} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
    have hsub : {ω | t < V ω} ⊆ {ω | singularValues (X ω) k ≤
        √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, V] at hω ⊢
      rw [← ha]
      rcases le_total (a - singularValues (X ω) k) 0 with h | h
      · rw [max_eq_right h] at hω; exact absurd hω (not_lt.2 (le_of_lt ht))
      · rw [max_eq_left h] at hω; linarith
    calc μ {ω | t < V ω} ≤ μ {ω | singularValues (X ω) k ≤
          √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {ω | singularValues (X ω) k ≤
          √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := ENNReal.ofReal_le_ofReal
          (measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix hX hk (le_of_lt ht))
  -- the layer-cake formula
  have hlc : ∫⁻ ω, ENNReal.ofReal (∫ v in (0)..V ω, g v) ∂μ ≤
      ENNReal.ofReal (C * (Real.exp (c ^ 2 / 2) * √(2 * π))) := by
    rw [lintegral_comp_eq_lintegral_meas_lt_mul (f := V) μ (ae_of_all _ fun ω => le_max_right _ _)
      hVm.aemeasurable (fun t _ => hg.intervalIntegrable _ _) (ae_of_all _ fun v => hg0 v)]
    calc ∫⁻ t in Set.Ioi 0, μ {ω | t < V ω} * ENNReal.ofReal (g t) ≤
          ∫⁻ t in Set.Ioi 0, ENNReal.ofReal C *
            ENNReal.ofReal (Real.exp (c * t) * Real.exp (-t ^ 2 / 2)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have hgt : g t ≤ C * Real.exp (c * t) := by
            have h := inv_max_sub_pow_le ha0 (le_of_lt ht) (2 * q + 1)
            simp only [hgdef, hCdef, c]
            push_cast at h ⊢
            calc 2 * q * M ^ q * ((max (a - t) 5) ^ (2 * q + 1))⁻¹ ≤
                2 * q * M ^ q * ((a ^ (2 * q + 1))⁻¹ * Real.exp ((2 * q + 1) / 5 * t)) :=
                  mul_le_mul_of_nonneg_left h (by positivity)
              _ = _ := by ring
          calc μ {ω | t < V ω} * ENNReal.ofReal (g t) ≤
                ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) * ENNReal.ofReal (g t) := by
                gcongr
                exact htail t ht
            _ = ENNReal.ofReal (g t * Real.exp (-t ^ 2 / 2)) := by
                rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
            _ ≤ ENNReal.ofReal (C * (Real.exp (c * t) * Real.exp (-t ^ 2 / 2))) := by
                refine ENNReal.ofReal_le_ofReal ?_
                calc g t * Real.exp (-t ^ 2 / 2) ≤
                    C * Real.exp (c * t) * Real.exp (-t ^ 2 / 2) :=
                      mul_le_mul_of_nonneg_right hgt (Real.exp_pos _).le
                  _ = C * (Real.exp (c * t) * Real.exp (-t ^ 2 / 2)) := by ring
            _ = _ := ENNReal.ofReal_mul hC0
      _ = ENNReal.ofReal C * ∫⁻ t in Set.Ioi 0,
            ENNReal.ofReal (Real.exp (c * t) * Real.exp (-t ^ 2 / 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.exp (c ^ 2 / 2) * √(2 * π)) :=
          by gcongr; exact setLIntegral_exp_mul_mul_exp_neg_sq_le c
      _ = ENNReal.ofReal (C * (Real.exp (c ^ 2 / 2) * √(2 * π))) :=
          (ENNReal.ofReal_mul hC0).symm
  have hK0 : 0 ≤ C * (Real.exp (c ^ 2 / 2) * √(2 * π)) := by positivity
  have hint : Integrable (fun ω => ∫ v in (0)..V ω, g v) μ :=
    ⟨(hΦ.measurable.comp hVm).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hΦ0)).2 (hlc.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hΦ0) hint.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hK0 hlc

/-- The small-ball part:
$\mathbb{E}[\min\{1, \sigma_{\min}^2/m\}^{-q}\mathbf{1}_{\sigma_{\min} < 5}] \le m^{-1/2}$, by
$xy \le (x^2/T + Ty^2)/2$, the second moment and the lower tail of $\sigma_{\min}$ at $a - 5$. -/
private theorem integral_indicator_min_one_sq_div_inv_pow_le
    (hX : HasLaw X (gaussianMatrix m n) μ) (hXm : Measurable X) {k : ℕ}
    (hk : k + 1 = Fintype.card n) (hnm : 100 * Fintype.card n ≤ Fintype.card m)
    (hm : 900 ≤ Fintype.card m) {q : ℕ} (hq4 : q ≤ 4) {a : ℝ}
    (ha : a = √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ))
    (ha9 : 0.9 * √(Fintype.card m : ℝ) ≤ a) :
    Integrable (fun ω => (Set.Iio 5).indicator
      (fun s : ℝ => (min 1 (s ^ 2 / (Fintype.card m : ℝ)))⁻¹ ^ q) (singularValues (X ω) k)) μ ∧
    ∫ ω, (Set.Iio 5).indicator (fun s : ℝ => (min 1 (s ^ 2 / (Fintype.card m : ℝ)))⁻¹ ^ q)
      (singularValues (X ω) k) ∂μ ≤ 1 / √(Fintype.card m : ℝ) := by
  have := hX.isProbabilityMeasure
  set M := (Fintype.card m : ℝ) with hMdef
  have hM : (900 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hm
  have hsM : 0 < √M := Real.sqrt_pos.2 (by linarith)
  set φ : ℝ → ℝ := fun s => (min 1 (s ^ 2 / M))⁻¹ ^ q
  have hφ0 (s : ℝ) : 0 ≤ φ s := min_one_sq_div_inv_pow_nonneg s (by linarith) q
  set σ : Ω → ℝ := fun ω => singularValues (X ω) k
  have hσm : Measurable σ := (measurable_singularValues k).comp hXm
  set B := {ω | σ ω < 5}
  have hB : MeasurableSet B := measurableSet_lt hσm measurable_const
  have hind : (fun ω => (Set.Iio 5).indicator φ (σ ω)) = B.indicator fun ω => φ (σ ω) := by
    funext ω
    by_cases h : σ ω < 5
    · rw [Set.indicator_of_mem (Set.mem_Iio.2 h), Set.indicator_of_mem (show ω ∈ B from h)]
    · rw [Set.indicator_of_notMem (by simpa using h), Set.indicator_of_notMem
        (show ω ∉ B from h)]
  have hf := integrable_min_one_singularValues_sq_div_inv_pow_of_hasLaw_gaussianMatrix hX hk
    (q := q) (by omega)
  obtain ⟨hf2, hf2le⟩ := integral_min_one_sq_div_inv_pow_sq_le hX hk hnm hm hq4
  have hint : Integrable (fun ω => (Set.Iio 5).indicator φ (σ ω)) μ := by
    rw [hind]; exact hf.indicator hB
  refine ⟨hint, ?_⟩
  -- the tail at `a - 5`
  have hPB : μ.real B ≤ Real.exp (-(a - 5) ^ 2 / 2) := by
    have hsub : B ⊆ {ω | singularValues (X ω) k ≤
        √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - (a - 5)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, B, σ] at hω ⊢
      rw [← ha]
      linarith
    refine (measureReal_mono hsub).trans ?_
    have h30 : 30 ≤ √M := Real.le_sqrt_of_sq_le (by linarith)
    exact measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix hX hk (by linarith)
  set T := 45400 * √M with hT
  have hT0 : 0 < T := by positivity
  have hpt (ω : Ω) : B.indicator (fun ω => φ (σ ω)) ω ≤
      (φ (σ ω) ^ 2 / T + T * B.indicator 1 ω) / 2 := by
    by_cases h : ω ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, mul_one,
        le_div_iff₀ two_pos, div_add' _ _ _ hT0.ne', le_div_iff₀ hT0]
      nlinarith [sq_nonneg (φ (σ ω) - T)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero, add_zero]
      positivity
  have hI1 : Integrable (B.indicator (1 : Ω → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hB
  have hf2' : Integrable (fun ω => φ (σ ω) ^ 2 / T) μ := hf2.div_const T
  have hRint : Integrable (fun ω => (φ (σ ω) ^ 2 / T + T * B.indicator 1 ω) / 2) μ :=
    (hf2'.add (hI1.const_mul T)).div_const 2
  rw [hind]
  refine (integral_mono (hf.indicator hB) hRint hpt).trans ?_
  rw [integral_div, integral_add hf2' (hI1.const_mul T), integral_div, integral_const_mul,
    integral_indicator_one hB]
  have hnum := mul_le_exp_sub_five_sq hM ha9
  have h1 : (∫ ω, φ (σ ω) ^ 2 ∂μ) / T ≤ 1 / √M := by
    rw [div_le_div_iff₀ hT0 hsM, hT]
    nlinarith
  have h2 : T * μ.real B ≤ 1 / √M := by
    have hE : Real.exp (-(a - 5) ^ 2 / 2) * Real.exp ((a - 5) ^ 2 / 2) = 1 := by
      rw [← Real.exp_add, show -(a - 5) ^ 2 / 2 + (a - 5) ^ 2 / 2 = 0 by ring, Real.exp_zero]
    have hsq : √M * √M = M := Real.mul_self_sqrt (by linarith)
    rw [le_div_iff₀ hsM, hT]
    have hPB' : μ.real B * (45400 * M) ≤ 1 := by
      calc μ.real B * (45400 * M) ≤ Real.exp (-(a - 5) ^ 2 / 2) * Real.exp ((a - 5) ^ 2 / 2) :=
            mul_le_mul hPB hnum (by positivity) (Real.exp_pos _).le
        _ = 1 := hE
    nlinarith
  linarith


/-- The sizes: for $100n \le m$ and $900 \le m$, $a = \sqrt{m} - \sqrt{n}$ satisfies
$0.9\sqrt{m} \le a$, $5 \le a$ and $a^2 \le m$. -/
private theorem sqrt_sub_sqrt_bounds {M N : ℝ} (hNM : 100 * N ≤ M)
    (hM : 900 ≤ M) :
    0.9 * √M ≤ √M - √N ∧ 5 ≤ √M - √N ∧ (√M - √N) ^ 2 ≤ M := by
  have h10 : 10 * √N ≤ √M := by
    have h := Real.sqrt_le_sqrt hNM
    rwa [Real.sqrt_mul (by norm_num), show √(100 : ℝ) = 10 by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have h30 : 30 ≤ √M := Real.le_sqrt_of_sq_le (by linarith)
  have hN0 := Real.sqrt_nonneg N
  refine ⟨by linarith, by linarith, ?_⟩
  calc (√M - √N) ^ 2 ≤ √M ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    _ = M := Real.sq_sqrt (by linarith)

/-- The main estimate for a measurable Gaussian matrix, before the constants are collected:
with $a = \sqrt{m} - \sqrt{n}$,
$\mathbb{E}\bar\lambda^{-q} \le m^q a^{-2q} + 2q m^q a^{-(2q+1)} e^{c^2/2}\sqrt{2\pi} +
m^{-1/2}$, $c = (2q + 1)/5$. -/
private theorem integral_min_one_sq_div_inv_pow_le_aux (hX : HasLaw X (gaussianMatrix m n) μ)
    (hXm : Measurable X) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (hnm : 100 * Fintype.card n ≤ Fintype.card m) (hm : 900 ≤ Fintype.card m) {q : ℕ}
    (hq4 : q ≤ 4) :
    ∫ ω, (min 1 (singularValues (X ω) k ^ 2 / Fintype.card m))⁻¹ ^ q ∂μ ≤
      (Fintype.card m : ℝ) ^ q *
          ((√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) ^ (2 * q))⁻¹ +
        2 * q * (Fintype.card m : ℝ) ^ q *
            ((√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) ^ (2 * q + 1))⁻¹ *
          (Real.exp (((2 * q + 1) / 5) ^ 2 / 2) * √(2 * π)) +
        1 / √(Fintype.card m : ℝ) := by
  have := hX.isProbabilityMeasure
  have hM : (900 : ℝ) ≤ Fintype.card m := by exact_mod_cast hm
  have hNM : 100 * (Fintype.card n : ℝ) ≤ Fintype.card m := by exact_mod_cast hnm
  obtain ⟨ha9, ha5, haM⟩ := sqrt_sub_sqrt_bounds hNM hM
  obtain ⟨hΦi, hΦle⟩ := integral_layerCake_le hX hXm hk rfl ha5 q
  obtain ⟨hIi, hIle⟩ :=
    integral_indicator_min_one_sq_div_inv_pow_le hX hXm hk hnm hm hq4 rfl ha9
  have hf := integrable_min_one_singularValues_sq_div_inv_pow_of_hasLaw_gaussianMatrix hX hk
    (q := q) (by omega)
  have hpt (ω : Ω) := min_one_sq_div_inv_pow_le_add (s := singularValues (X ω) k) ha5 haM q
  refine (integral_mono hf (((integrable_const _).add hΦi).add hIi) hpt).trans ?_
  rw [integral_add' ((integrable_const _).add hΦi) hIi, integral_add' (integrable_const _) hΦi,
    integral_const, probReal_univ, one_smul]
  linarith

/-- **Clipped inverse moments of the smallest singular value**: for a standard Gaussian
$m \times n$ matrix $\mathbf{G}$, $\bar\lambda = \min\{1, \sigma_{\min}(\mathbf{G})^2/m\}$,
$100n \le m$, $900 \le m$ and $q \le 4$, <!-- value gaussianClippedInvMomentConstant q -->
$$\mathbb{E}\,\bar\lambda^{-q} \le \bigl(1 - \sqrt{n/m}\bigr)^{-2q} +
\frac{2q (0.9)^{-(2q + 1)} e^{(2q + 1)^2/50}\sqrt{2\pi} + 1}{\sqrt{m}}\,,$$
the constant being `gaussianClippedInvMomentConstant q`: the inverse moments of the smallest
eigenvalue of $\mathbf{G}^{\mathsf{H}}\mathbf{G}/m$, clipped at $1$, are those of its mean-field
value $(1 - \sqrt{n/m})^2$ up to $O(m^{-1/2})$. Proved without a literature source, by the
layer-cake formula on the deviation of $\sigma_{\min}$ below $\sqrt{m} - \sqrt{n}$ and
Cauchy–Schwarz on $\{\sigma_{\min} < 5\}$; inputs [Vershynin2018, Exercise 7.3.4, Corollary 7.3.3]
and [HalkoMartinssonTropp2011, Proposition 10.4] (in the forms of this library). -/
theorem integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (hnm : 100 * Fintype.card n ≤ Fintype.card m) (hm : 900 ≤ Fintype.card m)
    {q : ℕ} (hq4 : q ≤ 4) :
    ∫ ω, (min 1 (singularValues (X ω) k ^ 2 / Fintype.card m))⁻¹ ^ q ∂μ ≤
      ((1 - √((Fintype.card n : ℝ) / Fintype.card m)) ^ (2 * q))⁻¹ +
        gaussianClippedInvMomentConstant q / √(Fintype.card m) := by
  have hF : Measurable fun x : Matrix m n ℝ =>
      (min 1 (singularValues x k ^ 2 / Fintype.card m))⁻¹ ^ q :=
    (measurable_min_one_sq_div_inv_pow _ q).comp (measurable_singularValues k)
  have h := hX.integral_comp hF.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  refine (integral_min_one_sq_div_inv_pow_le_aux (X := id) HasLaw.id measurable_id hk hnm hm
    hq4).trans ?_
  have hM : (900 : ℝ) ≤ Fintype.card m := by exact_mod_cast hm
  have hNM : 100 * (Fintype.card n : ℝ) ≤ Fintype.card m := by exact_mod_cast hnm
  set M := (Fintype.card m : ℝ)
  set N := (Fintype.card n : ℝ)
  obtain ⟨ha9, ha5, -⟩ := sqrt_sub_sqrt_bounds hNM hM
  set a := √M - √N with ha
  have hsM : 0 < √M := Real.sqrt_pos.2 (by linarith)
  have ha0 : 0 < a := by linarith
  have hMq : M ^ q = √M ^ (2 * q) := by rw [pow_mul, Real.sq_sqrt (by linarith)]
  -- the leading term
  have hlead : M ^ q * (a ^ (2 * q))⁻¹ = ((1 - √(N / M)) ^ (2 * q))⁻¹ := by
    rw [Real.sqrt_div (Nat.cast_nonneg _), show 1 - √N / √M = a / √M by
      rw [ha]; field_simp, div_pow, inv_div, hMq, div_eq_mul_inv]
  -- the middle term
  have hmid : 2 * q * M ^ q * (a ^ (2 * q + 1))⁻¹ *
      (Real.exp (((2 * q + 1) / 5) ^ 2 / 2) * √(2 * π)) ≤
      (gaussianClippedInvMomentConstant q - 1) / √M := by
    rw [gaussianClippedInvMomentConstant_def, add_sub_cancel_right,
      show (-(2 * q + 1 : ℤ)) = -((2 * q + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, show (((2 * q + 1 : ℝ) / 5) ^ 2 / 2) = (2 * q + 1) ^ 2 / 50 by ring]
    have hpow : (0.9 : ℝ) ^ (2 * q + 1) * √M ^ (2 * q + 1) ≤ a ^ (2 * q + 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) ha9 _
    have hkey : M ^ q * (a ^ (2 * q + 1))⁻¹ ≤ ((0.9 : ℝ) ^ (2 * q + 1))⁻¹ / √M := by
      rw [hMq, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hsM, inv_mul_eq_div,
        le_div_iff₀ (by positivity)]
      calc √M ^ (2 * q) * √M * (0.9 : ℝ) ^ (2 * q + 1) =
            (0.9 : ℝ) ^ (2 * q + 1) * √M ^ (2 * q + 1) := by ring
        _ ≤ a ^ (2 * q + 1) := hpow
    have hE : 0 ≤ Real.exp ((2 * q + 1) ^ 2 / 50) * √(2 * π) := by positivity
    calc 2 * q * M ^ q * (a ^ (2 * q + 1))⁻¹ *
          (Real.exp ((2 * q + 1) ^ 2 / 50) * √(2 * π)) =
          2 * q * (M ^ q * (a ^ (2 * q + 1))⁻¹) *
            (Real.exp ((2 * q + 1) ^ 2 / 50) * √(2 * π)) := by ring
      _ ≤ 2 * q * (((0.9 : ℝ) ^ (2 * q + 1))⁻¹ / √M) *
            (Real.exp ((2 * q + 1) ^ 2 / 50) * √(2 * π)) := by gcongr
      _ = _ := by ring
  rw [hlead, add_assoc]
  gcongr
  calc _ ≤ (gaussianClippedInvMomentConstant q - 1) / √M + 1 / √M := by gcongr
    _ = gaussianClippedInvMomentConstant q / √M := by ring

end NLAlib
