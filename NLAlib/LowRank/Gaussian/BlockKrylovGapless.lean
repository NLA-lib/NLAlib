/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.Convex.Integral
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.LowRank.Gaussian.BlockKrylov
public import NLAlib.Matrix.Functions.TraceFunctions
import NLAlib.ForMathlib.RingTheory.Polynomial.Chebyshev

/-!
# Gapless bounds for randomized block Krylov and subspace iteration

Expected spectral errors of randomized block Krylov iteration $\mathsf{rbki}(\mathbf{A},
\mathbf{X}, q)$ and of randomized subspace iteration with $p$ power steps, for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$ and a target rank $r$ with $r + 2 \le \ell$, that need no
gap in the spectrum of $\mathbf{A}$. Two incomparable forms.

**The $(1 + \varepsilon)$ form** (Musco and Musco's case split, applied to the gapped bounds of
`NLAlib.LowRank.Gaussian.BlockKrylov`): for every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
4e^{-8(q-1)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,,$$
for the truncated and the untruncated output, so that depth
$q = O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\varepsilon})$ gives relative error
$1 + \varepsilon$.
The case split is on the number of singular values at least $(1 + \varepsilon)\sigma_r$; it is
deterministic and uses only the gapped bound, `NLAlib.singularValues_sub_truncatedSVD_rsvd_le_of_le`
and reverse Eckart–Young.

**Tropp and Webber's form**, with the exact constants of their Theorem 9.1 at an even number of
products: $\sigma_r(\mathbf{A})^2$ times a factor tending to $1$ at the rate $1/(q-1)^2$ for RBKI
and $1/(2p + 1)$ for RSI, through the range-finder tail ratio `NLAlib.rangeFinderTailRatio`
<!-- mention rangeFinderTailRatio --> and the almost-convex Jensen inequality
(`HasSupportingLineOn.le_integral_comp`).

## Main results

* `NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`: the
  $(1 + \varepsilon)$ form for RBKI, truncated and untruncated, and its asymptotic form
  `NLAlib.exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix`.
* the same for RSI, truncated and untruncated:
  `integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix`: Tropp and
  Webber's form.
* the asymptotic forms of Tropp and Webber's form, depth
  $O(\log(\lvert n \rvert + 1)/\sqrt{\varepsilon})$ for RBKI and
  $O(\log(\lvert n \rvert + 1)/\varepsilon)$ power steps for RSI, with no positivity hypothesis:
  `NLAlib.exists_forall_integral_specNorm_sub_rbki_sq_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.exists_forall_integral_specNorm_sub_rsvd_pow_mul_sq_le_of_hasLaw_gaussianMatrix`; and of
  the truncated RSI $(1 + \varepsilon)$ form, $O(\log(\lvert n \rvert/\varepsilon)/\varepsilon)$
  power steps:
`exists_forall_integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_of_hasLaw_gaussianMatrix`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l ℝ}


omit [DecidableEq n] in
/-- Musco and Musco's case split: for $\varepsilon > 0$, either
$\|\mathbf{A}\|_2 = \sigma_0 \le (1 + \varepsilon)\sigma_r$, or there is a head $h + 1 \le r$
with $\sigma_{h+1} \le (1 + \varepsilon)\sigma_r \le \sigma_h$, so that the relative gap
$(\sigma_h - \sigma_r)/(\sigma_h + \sigma_r)$ is at least $\varepsilon/(2 + \varepsilon)$ unless
$\sigma_r = 0$. Here $h + 1$ is the number of singular values at least
$(1 + \varepsilon)\sigma_r$. -/
theorem singularValues_zero_le_or_exists_singularGapRatio (A : Matrix m n ℝ) (r : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    singularValues A 0 ≤ (1 + ε) * singularValues A r ∨
      ∃ h, h + 1 ≤ r ∧ singularValues A (h + 1) ≤ (1 + ε) * singularValues A r ∧
        (singularValues A r = 0 ∨ ε / (2 + ε) ≤ singularGapRatio A h r) := by
  classical
  set s := singularValues A r with hsdef
  have hs : 0 ≤ s := singularValues_nonneg A r
  by_cases h0 : singularValues A 0 ≤ (1 + ε) * s
  · exact Or.inl h0
  right
  replace h0 := not_le.mp h0
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · rw [hsdef, hr] at h0
      nlinarith [singularValues_nonneg A 0]
    · exact hr
  have hex : ∃ k, singularValues A (k + 1) ≤ (1 + ε) * s :=
    ⟨r - 1, by rw [Nat.sub_add_cancel hr]; nlinarith⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · have := Nat.find_min' hex (show singularValues A (r - 1 + 1) ≤ (1 + ε) * s by
      rw [Nat.sub_add_cancel hr]; nlinarith)
    omega
  have hlow : (1 + ε) * s ≤ singularValues A (Nat.find hex) := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk | hk
    · rw [hk]
      exact h0.le
    · have h := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel hk] at h
      exact (not_le.mp h).le
  rcases hs.eq_or_lt with hz | hpos
  · exact Or.inl hz.symm
  right
  rw [singularGapRatio, div_le_div_iff₀ (by linarith)
    (by linarith [singularValues_nonneg A (Nat.find hex)])]
  nlinarith

omit [DecidableEq n] in
/-- The tail term of the gapped bounds at the gap of the case split is at most the tail term at
$\varepsilon/(2 + \varepsilon)$, for any non-increasing function $e$ of the gap: when
$\sigma_r = 0$ both are zero. -/
theorem mul_frobNorm_sub_truncatedSVD_sq_le (A : Matrix m n ℝ) {e : ℝ → ℝ}
    (he : Antitone e) {h r : ℕ} {ε κ : ℝ} (hκ : 0 ≤ κ)
    (hgap : singularValues A r = 0 ∨ ε / (2 + ε) ≤ singularGapRatio A h r) :
    e (singularGapRatio A h r) * κ * frobNorm (A - truncatedSVD A r) ^ 2 ≤
      e (ε / (2 + ε)) * κ * frobNorm (A - truncatedSVD A r) ^ 2 := by
  rcases hgap with hz | hγ
  · have hrk : A.rank ≤ r := (singularValues_eq_zero_iff A).mp hz
    rw [truncatedSVD_of_rank_le A hrk, sub_self, frobNorm_zero]
    simp
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he hγ) hκ) (sq_nonneg _)

omit [DecidableEq n] in
/-- The case split in expectation: if an error $Y \le \|\mathbf{A}\|_2^2$ obeys, at every head
$h + 1 \le r$, the gapped bound $\sigma_{h+1}^2 + e(\gamma_h)\kappa
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$ with $e$ non-increasing and
$e(\varepsilon/(2 + \varepsilon)), \kappa \ge 0$, then
$\mathbb{E}Y \le (1 + \varepsilon)^2\sigma_r^2 + e(\varepsilon/(2 + \varepsilon))\kappa
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$. -/
private theorem integral_le_one_add_sq_mul_of_gapped [IsProbabilityMeasure μ] (A : Matrix m n ℝ)
    {r : ℕ} {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 ≤ κ) {e : ℝ → ℝ} (he : Antitone e)
    (he₀ : 0 ≤ e (ε / (2 + ε))) {Y : Ω → ℝ} (hY₀ : ∀ ω, 0 ≤ Y ω)
    (hYA : ∀ ω, Y ω ≤ specNorm A ^ 2)
    (hgapped : ∀ h, h + 1 ≤ r → ∫ ω, Y ω ∂μ ≤ singularValues A (h + 1) ^ 2 +
      e (singularGapRatio A h r) * κ * frobNorm (A - truncatedSVD A r) ^ 2) :
    ∫ ω, Y ω ∂μ ≤ (1 + ε) ^ 2 * singularValues A r ^ 2 +
      e (ε / (2 + ε)) * κ * frobNorm (A - truncatedSVD A r) ^ 2 := by
  have hT : 0 ≤ e (ε / (2 + ε)) * κ * frobNorm (A - truncatedSVD A r) ^ 2 :=
    mul_nonneg (mul_nonneg he₀ hκ) (sq_nonneg _)
  rcases singularValues_zero_le_or_exists_singularGapRatio A r hε with h0 | ⟨h, hhr, hσ, hgap⟩
  · rw [singularValues_zero_eq_specNorm] at h0
    have hA : specNorm A ^ 2 ≤ (1 + ε) ^ 2 * singularValues A r ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (specNorm_nonneg _) h0 2
    have h := integral_mono_of_nonneg (Filter.Eventually.of_forall hY₀)
      (integrable_const (μ := μ) (specNorm A ^ 2)) (Filter.Eventually.of_forall hYA)
    rw [integral_const, probReal_univ, one_smul] at h
    linarith
  · have h1 := hgapped h hhr
    have h2 := mul_frobNorm_sub_truncatedSVD_sq_le A he hκ hgap
    have h3 : singularValues A (h + 1) ^ 2 ≤ (1 + ε) ^ 2 * singularValues A r ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (singularValues_nonneg _ _) hσ 2
    linarith

/-- The RBKI factor $4e^{-8(q-1)\sqrt{\gamma}}$ is non-increasing in $\gamma$ for $q \ge 1$. -/
private theorem antitone_four_mul_exp_sqrt {q : ℕ} (hq : 1 ≤ q) :
    Antitone fun γ : ℝ => 4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt γ) := by
  have hq' : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  intro a b hab
  have := Real.sqrt_le_sqrt hab
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by norm_num)

/-- The RSI factor $e^{-8p\gamma}$ is non-increasing in $\gamma$. -/
private theorem antitone_exp_mul (p : ℕ) :
    Antitone fun γ : ℝ => Real.exp (-8 * (p : ℝ) * γ) := by
  intro a b hab
  exact Real.exp_le_exp.2 (by nlinarith)

/-- **The gapless bound for truncated randomized block Krylov iteration, $(1 + \varepsilon)$
form**: for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a
target rank $r$ with $r + 2 \le \ell$, and every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
4e^{-8(q-1)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
No gap is assumed: with $h$ the number of singular values at least
$(1 + \varepsilon)\sigma_r(\mathbf{A})$, either $h = 0$ and the error is at most
$\|\mathbf{A}\|_2 < (1 + \varepsilon)\sigma_r$, or the gapped bound at head $h$ and tail index $r$
applies with gap at least $\varepsilon/(2 + \varepsilon)$. The constants are composed here, not
printed in either source: $4$ and $8$ from TW Theorem 9.2 at $m = 2q$, the gap from MM's case
split with $1 + \varepsilon$ in place of their $1 + \varepsilon/2$. Better than Tropp and Webber's
gapless form (`NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix`) for a
fixed relative accuracy $\varepsilon$; that one is better as $q \to \infty$ at fixed $\mathbf{A}$.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix`.
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2]; there with probability
$99/100$ (MM) or untruncated and gapped (TW); here in expectation.
Result: rbki-gapless-error -/
theorem integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  have := hX.isProbabilityMeasure
  refine integral_le_one_add_sq_mul_of_gapped A hε (natCast_div_sub_sub_one_nonneg hr)
    (antitone_four_mul_exp_sqrt hq) (by positivity) (fun ω => sq_nonneg _) (fun ω => ?_)
    (fun h hhr => ?_)
  · have h := singularValues_sub_truncatedSVD_rsvd_le_of_le A
      (blockKrylovMatrix (Aᴴ * A) (X ω) q) (Nat.zero_le r) 0
    rw [truncatedSVD_zero, sub_zero, singularValues_zero_eq_specNorm,
      singularValues_zero_eq_specNorm, ← rbki_def] at h
    exact pow_le_pow_left₀ (specNorm_nonneg _) h 2
  · have hX' := hX.aemeasurable
    refine (integral_mono (integrable_specNorm_sub_truncatedSVD_rbki_sq A hX' q r)
      (integrable_specNorm_sub_truncatedSVD_rbki_sq A hX' q (h + 1)) fun ω => ?_).trans
      (integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A
        hX rfl hhr hr hq)
    have h := singularValues_sub_truncatedSVD_rsvd_le_of_le A
      (blockKrylovMatrix (Aᴴ * A) (X ω) q) hhr 0
    rw [singularValues_zero_eq_specNorm, singularValues_zero_eq_specNorm, ← rbki_def] at h
    exact pow_le_pow_left₀ (specNorm_nonneg _) h 2

/-- **The gapless bound for randomized block Krylov iteration, $(1 + \varepsilon)$ form**: for a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a target rank $r$ with
$r + 2 \le \ell$, and every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
4e^{-8(q-1)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
The same bound as the truncated form
(`NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`).
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2]; constants composed here.
Result: rbki-gapless-error -/
theorem integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  refine integral_le_one_add_sq_mul_of_gapped A hε (natCast_div_sub_sub_one_nonneg hr)
    (antitone_four_mul_exp_sqrt hq) (by positivity) (fun ω => sq_nonneg _) (fun ω => ?_)
    (fun h hhr =>
      integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A hX rfl hhr hr
        hq)
  rw [rbki_def, sub_rsvd]
  exact pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_one_sub_rangeProjector_mul_le _ _) 2

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapless bound for truncated randomized subspace iteration, $(1 + \varepsilon)$ form**:
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a target rank
$r$ with $r + 2 \le \ell$, and every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
e^{-8p\varepsilon/(2 + \varepsilon)}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_of_hasLaw_gaussianMatrix`.
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2 (RSI)]; there for block Krylov
iteration (MM) or gapped (TW); constants composed here.
Result: rsi-gapless-error -/
theorem
integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        Real.exp (-8 * (p : ℝ) * (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  have := hX.isProbabilityMeasure
  refine integral_le_one_add_sq_mul_of_gapped A hε (natCast_div_sub_sub_one_nonneg hr)
    (antitone_exp_mul p) (by positivity) (fun ω => sq_nonneg _) (fun ω => ?_)
    (fun h hhr => ?_)
  · have h := singularValues_sub_truncatedSVD_rsvd_le_of_le A ((Aᴴ * A) ^ p * X ω)
      (Nat.zero_le r) 0
    rw [truncatedSVD_zero, sub_zero, singularValues_zero_eq_specNorm,
      singularValues_zero_eq_specNorm] at h
    exact pow_le_pow_left₀ (specNorm_nonneg _) h 2
  · have hX' : AEMeasurable (fun ω => (Aᴴ * A) ^ p * X ω) μ :=
      (measurable_const.matrix_mul measurable_id).comp_aemeasurable hX.aemeasurable
    refine (integral_mono (integrable_specNorm_sub_truncatedSVD_rsvd_sq A hX' r)
      (integrable_specNorm_sub_truncatedSVD_rsvd_sq A hX' (h + 1)) fun ω => ?_).trans
      (integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
        A hX rfl hhr hr p)
    have h := singularValues_sub_truncatedSVD_rsvd_le_of_le A ((Aᴴ * A) ^ p * X ω) hhr 0
    rw [singularValues_zero_eq_specNorm, singularValues_zero_eq_specNorm] at h
    exact pow_le_pow_left₀ (specNorm_nonneg _) h 2

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapless bound for randomized subspace iteration, $(1 + \varepsilon)$ form**: for a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a target rank $r$ with
$r + 2 \le \ell$, and every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
e^{-8p\varepsilon/(2 + \varepsilon)}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
The same bound as the truncated form
(`NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`).
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2 (RSI)]; constants composed
here.
Result: rsi-gapless-error -/
theorem integral_specNorm_sub_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        Real.exp (-8 * (p : ℝ) * (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  refine integral_le_one_add_sq_mul_of_gapped A hε (natCast_div_sub_sub_one_nonneg hr)
    (antitone_exp_mul p) (by positivity) (fun ω => sq_nonneg _) (fun ω => ?_)
    (fun h hhr =>
      integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A hX rfl
        hhr hr p)
  rw [sub_rsvd]
  exact pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_one_sub_rangeProjector_mul_le _ _) 2

/-- The depth step of the depth bound for RBKI: for $N \ge 1$, $0 < \varepsilon \le 1/2$ and
$6\log(N/\varepsilon) \le q\sqrt\varepsilon$, $16N^2e^{-8(q-1)s} \le \varepsilon$ with
$s = \sqrt{(\varepsilon/3)/(2 + \varepsilon/3)} \ge \sqrt\varepsilon/3$. -/
private theorem sixteen_mul_sq_mul_exp_le {N ε : ℝ} {q : ℕ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hε₀ : ε ≤ 1 / 2) (hq1 : 1 ≤ q) (hqε : 6 * Real.log (N / ε) ≤ q * Real.sqrt ε) :
    16 * N ^ 2 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (ε / 3 / (2 + ε / 3))) ≤ ε := by
  have hN0 : 0 < N := by linarith
  have hlogε : Real.log ε ≤ -Real.log 2 := by
    rw [← Real.log_inv]
    exact Real.log_le_log hε (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hL : Real.log (N / ε) = Real.log N - Real.log ε := Real.log_div hN0.ne' hε.ne'
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at h ⊢
    linarith
  have hsε1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hq' : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith
  set s := Real.sqrt (ε / 3 / (2 + ε / 3)) with hsdef
  have hs : Real.sqrt ε / 3 ≤ s := by
    have h9 : Real.sqrt ε / 3 = Real.sqrt (ε / 9) := by
      rw [Real.sqrt_div' ε (by norm_num : (0 : ℝ) ≤ 9), show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h9, hsdef]
    refine Real.sqrt_le_sqrt ?_
    rw [div_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have harg : Real.log 16 + 2 * Real.log N - Real.log ε ≤ 8 * ((q : ℝ) - 1) * s := by
    have h1 : 8 * ((q : ℝ) - 1) * (Real.sqrt ε / 3) ≤ 8 * ((q : ℝ) - 1) * s :=
      mul_le_mul_of_nonneg_left hs (by linarith)
    linarith
  have h : 16 * (N : ℝ) ^ 2 = Real.exp (Real.log 16 + 2 * Real.log N) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), two_mul, Real.exp_add,
      Real.exp_log hN0]
    ring
  rw [h, ← Real.exp_add]
  calc Real.exp (Real.log 16 + 2 * Real.log N + -8 * ((q : ℝ) - 1) * s)
      ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 (by linarith)
    _ = ε := Real.exp_log hε

/-- **Depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\varepsilon})$ suffices for randomized
block Krylov iteration**, spectral norm, truncated output: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$,
a target rank $r$ with $r + 2 \le \ell$, $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\varepsilon}$ blocks,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2
\le (1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of
`NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`, at
$\varepsilon/3$, with $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 \le
\lvert n \rvert\,\sigma_r(\mathbf{A})^2$ and $r/(\ell - r - 1) \le \lvert n \rvert$ when
$r < \lvert n \rvert$ (for $r \ge \lvert n \rvert$ the tail term vanishes); the proof takes
$C = 6$ and $\varepsilon_0 = 1/2$. At $\lvert n \rvert = 0$ every depth is allowed (Lean's
$\log 0 = 0$), harmlessly, since then $\mathbf{A} = \mathbf{0}$.
[MuscoMusco2015, Theorem 10]; [MartinssonTropp2020, Theorem 11.11]; there with probability $99/100$
and $q = \Theta(\log(d/\varepsilon)/\sqrt{\varepsilon})$ (MM), or stated without proof (MT).
Asymptotic:
NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
Result: rbki-gapless-error -/
theorem exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (r q : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → r + 2 ≤ Fintype.card l → 0 < ε →
      ε ≤ ε₀ → C * Real.log (Fintype.card n / ε) / Real.sqrt ε ≤ q →
      ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
        (1 + ε) * singularValues A r ^ 2 := by
  refine ⟨6, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X r q ε hX hr hε hε₀ hq
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hN0 | hNpos
  · -- No columns: $\mathbf{A} = \mathbf{0}$.
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hN0
    have h0 : ∀ ω, A - truncatedSVD (rbki A (X ω) q) r = 0 := fun ω => Subsingleton.elim _ _
    simp only [h0, specNorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
    positivity
  set N := Fintype.card n
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hlogε : Real.log ε ≤ -Real.log 2 := by
    rw [← Real.log_inv]
    exact Real.log_le_log hε (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hL : Real.log (N / ε) = Real.log N - Real.log ε := Real.log_div (by positivity) hε.ne'
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at h ⊢
    linarith
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hqε : 6 * Real.log (N / ε) ≤ q * Real.sqrt ε := by rwa [div_le_iff₀ hsε] at hq
  have hq1 : 1 ≤ q := by
    have hLpos : 0 < Real.log (N / ε) := by rw [hL]; linarith
    have h : (0 : ℝ) < q := lt_of_lt_of_le (div_pos (mul_pos (by norm_num) hLpos) hsε) hq
    exact_mod_cast h
  have hexp :=
    integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix A hX hr
      hq1 (ε := ε / 3) (by positivity)
  set σ := singularValues A r
  set κ := (r : ℝ) / ((Fintype.card l : ℝ) - r - 1)
  set F := frobNorm (A - truncatedSVD A r)
  set s := Real.sqrt (ε / 3 / (2 + ε / 3))
  set E := Real.exp (-8 * ((q : ℝ) - 1) * s)
  -- $\kappa\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 \le N^2\sigma_r^2$.
  have hκF : κ * F ^ 2 ≤ (N : ℝ) ^ 2 * σ ^ 2 :=
    natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq A
      le_rfl hr
  -- $16N^2 e^{-8(q-1)s} \le \varepsilon$, from $s \ge \sqrt{\varepsilon}/3$.
  have hEε : 16 * (N : ℝ) ^ 2 * E ≤ ε := sixteen_mul_sq_mul_exp_le hNR hε hε₀ hq1 hqε
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg _
  have h13 : (1 + ε / 3) ^ 2 ≤ 1 + 3 / 4 * ε := by nlinarith
  have htail : 4 * E * κ * F ^ 2 ≤ ε / 4 * σ ^ 2 :=
    calc 4 * E * κ * F ^ 2 = 4 * E * (κ * F ^ 2) := by ring
      _ ≤ 4 * E * ((N : ℝ) ^ 2 * σ ^ 2) :=
          mul_le_mul_of_nonneg_left hκF (by positivity)
      _ = 16 * (N : ℝ) ^ 2 * E / 4 * σ ^ 2 := by ring
      _ ≤ ε / 4 * σ ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hσ2
  calc ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ
      ≤ (1 + ε / 3) ^ 2 * σ ^ 2 + 4 * E * κ * F ^ 2 := hexp
    _ ≤ (1 + 3 / 4 * ε) * σ ^ 2 + ε / 4 * σ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right h13 hσ2) htail
    _ = (1 + ε) * σ ^ 2 := by ring


open Polynomial.Chebyshev in
/-- The rescaled Chebyshev filter $\varphi(y) = y\,T_j(2y/s - 1)^2$ has a supporting line on
$[0, \infty)$ at every $x \ge s > 0$: it is $s\,\psi(y/s)$ for the filter $\psi$ of
`Polynomial.Chebyshev.hasSupportingLineOn_mul_eval_T_sq`. -/
private theorem hasSupportingLineOn_mul_eval_T_div_sq (j : ℕ) {s x : ℝ} (hs : 0 < s)
    (hx : s ≤ x) :
    HasSupportingLineOn (fun y => y * ((T ℝ (j : ℤ)).eval (2 * (y / s) - 1)) ^ 2)
      (Set.Ici 0) x := by
  obtain ⟨c, hc⟩ := hasSupportingLineOn_mul_eval_T_sq j ((one_le_div hs).2 hx)
  refine ⟨c, fun y hy => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hc (y / s) (div_nonneg hy hs.le)) hs.le
  beta_reduce at h ⊢
  have e₁ : s * (x / s * ((T ℝ (j : ℤ)).eval (2 * (x / s) - 1)) ^ 2 + c * (y / s - x / s)) =
      x * ((T ℝ (j : ℤ)).eval (2 * (x / s) - 1)) ^ 2 + c * (y - x) := by
    field_simp
  have e₂ : s * (y / s * ((T ℝ (j : ℤ)).eval (2 * (y / s) - 1)) ^ 2) =
      y * ((T ℝ (j : ℤ)).eval (2 * (y / s) - 1)) ^ 2 := by
    field_simp
  linarith

open Polynomial.Chebyshev in
/-- The scalar inversion closing Tropp and Webber's proof for RBKI: for $j \ge 1$ and
$x \ge s > 0$, if $x\,T_j(2x/s - 1)^2 \le sR$ then
$$x \le s\exp\Bigl(\frac{\log^2(4R)}{16j^2}\Bigr)\,,$$
through $T_j(2u^2 - 1) = T_{2j}(u)$ at $u = \sqrt{x/s}$ and the inverse growth bound
`Polynomial.Chebyshev.le_exp_of_eval_T_real_le`. -/
private theorem le_mul_exp_of_mul_eval_T_sq_le {j : ℕ} (hj : 0 < j) {s x R : ℝ} (hs : 0 < s)
    (hx : s ≤ x) (h : x * ((T ℝ (j : ℤ)).eval (2 * (x / s) - 1)) ^ 2 ≤ s * R) :
    x ≤ s * Real.exp (Real.log (4 * R) ^ 2 / (16 * (j : ℝ) ^ 2)) := by
  have hxs : 1 ≤ x / s := (one_le_div hs).2 hx
  set u := Real.sqrt (x / s)
  have hu1 : 1 ≤ u := Real.one_le_sqrt.mpr hxs
  have hu2 : u ^ 2 = x / s := Real.sq_sqrt (by linarith)
  set τ := (T ℝ (j : ℤ)).eval (2 * (x / s) - 1)
  have hT : (T ℝ ((2 * j : ℕ) : ℤ)).eval u = τ := by
    rw [Nat.cast_mul, Nat.cast_ofNat, eval_T_two_mul, hu2]
  have hτ2 : τ ^ 2 ≤ R := by
    have h1 : x / s * τ ^ 2 ≤ R := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hs]
      linarith
    nlinarith [sq_nonneg τ]
  have hR : 0 ≤ R := (sq_nonneg τ).trans hτ2
  have h4 := le_exp_of_eval_T_real_le (q := 2 * j) (by omega) hu1
    (hT.trans_le ((le_abs_self τ).trans (Real.abs_le_sqrt hτ2)))
  have hsq : Real.sqrt (4 * R) = 2 * Real.sqrt R := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [← hsq, Real.log_sqrt (by positivity)] at h4
  have hxs' : x / s ≤ Real.exp (Real.log (4 * R) ^ 2 / (16 * (j : ℝ) ^ 2)) := by
    rw [← hu2]
    calc u ^ 2 ≤ Real.exp ((Real.log (4 * R) / 2 / ((2 * j : ℕ) : ℝ)) ^ 2 / 2) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h4 2
      _ = Real.exp (Real.log (4 * R) ^ 2 / (16 * (j : ℝ) ^ 2)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
          ring
  rwa [div_le_iff₀' hs] at hxs'

/-- The rank-$r$ competitor of Tropp and Webber's proof of Theorem 9.1, in expectation: for
$r \le \lvert n \rvert$, a real polynomial $f$ with $\lvert f \rvert \le a$ on
$[0, \sigma_r(\mathbf{A})^2]$ and $\mathbf{B} = \mathbf{A}f(\mathbf{A}^{\mathsf{H}}\mathbf{A})$,
there is a top-$r$ right singular frame $\mathbf{W}$ such that the randomized SVD of $\mathbf{B}$
at the test matrix $\mathbf{X}(\mathbf{W}^{\mathsf{H}}\mathbf{X})^{+}$, of $r$ columns, has
$$\mathbb{E}\|\mathbf{B} - \mathsf{rsvd}(\mathbf{B},
\mathbf{X}(\mathbf{W}^{\mathsf{H}}\mathbf{X})^{+})\|_2^2 \le
a^2\Bigl(\sigma_r(\mathbf{A})^2 + \frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\Bigr)\,.$$
The competitor-projector bound `NLAlib.HasOrthonormalCols.specNorm_sub_rsvd_mul_pinv_sq_le`
holds almost surely, and the Gaussian block moment integrates its sketch residual. -/
private theorem exists_integral_specNorm_sub_rsvd_mul_pinv_sq_le (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (f : Polynomial ℝ) {r : ℕ}
    (hrn : r ≤ Fintype.card n) (hr : r + 2 ≤ Fintype.card l) {a : ℝ}
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A r ^ 2), |f.eval x| ≤ a) :
    ∃ W : Matrix n (Fin r) ℝ,
      ∫ ω, specNorm (A * Polynomial.aeval (Aᴴ * A) f -
          rsvd (A * Polynomial.aeval (Aᴴ * A) f) (X ω * pinv (Wᴴ * X ω))) ^ 2 ∂μ ≤
        a ^ 2 * (singularValues A r ^ 2 +
          (r : ℝ) / ((Fintype.card l : ℝ) - r - 1) * frobNorm (A - truncatedSVD A r) ^ 2) := by
  have := hX.isProbabilityMeasure
  obtain ⟨Z, V, hZ, hV, hZV, hZZ, -, hAV, hpre⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A hrn
  set G := Polynomial.aeval (Aᴴ * A) f
  set B := A * G
  have hG : cfc (fun x => f.eval x) (Aᴴ * A) = G :=
    cfc_polynomial f (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self A)
  have hVV : V * Vᴴ = 1 - Z * Zᴴ := by rw [← hZZ, add_sub_cancel_left]
  have hEr : A - truncatedSVD A r = A * V * Vᴴ := by
    have h := hpre r le_rfl
    rw [Fin.castLE_rfl, Matrix.submatrix_id_id] at h
    rw [← h, Matrix.mul_assoc A V, hVV, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hBE : B - B * Z * Zᴴ = B * V * Vᴴ := by
    rw [Matrix.mul_assoc B V Vᴴ, hVV, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc B Z Zᴴ]
  have ha : 0 ≤ a := (abs_nonneg _).trans (htail 0 ⟨le_rfl, sq_nonneg _⟩)
  -- $\mathbf{B}\mathbf{V} = \mathbf{A}\mathbf{V}f(\mathbf{D})$, with $\lvert f \rvert \le a$ on
  -- the tail.
  have hGV := (Matrix.isHermitian_conjTranspose_mul_self A).cfc_mul_eq_mul_diagonal_of_mul_eq
    hAV (fun x => f.eval x)
  rw [hG] at hGV
  have hD : specNorm (Matrix.diagonal fun j : Fin (Fintype.card n - r) =>
      (((fun x => f.eval x) (singularValues A (r + j) ^ 2) : ℝ) : ℝ)) ≤ a :=
    specNorm_diagonal_le ha fun j => by
      rw [Real.norm_eq_abs]
      exact htail _ ⟨sq_nonneg _, pow_le_pow_left₀ (singularValues_nonneg _ _)
        (singularValues_antitone A (Nat.le_add_right r j)) 2⟩
  have hAVs : specNorm (A * V) = singularValues A r := by
    rw [← hV.specNorm_mul_conjTranspose_right, ← hEr, specNorm_sub_truncatedSVD]
  have hAVf : frobNorm (A * V) = frobNorm (A - truncatedSVD A r) := by
    rw [hEr, hV.frobNorm_mul_conjTranspose_right]
  have hS : specNorm (B * V) ≤ a * singularValues A r := by
    rw [Matrix.mul_assoc, hGV, ← Matrix.mul_assoc, ← hAVs, mul_comm a]
    exact (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hD (specNorm_nonneg _))
  have hSF : frobNorm (B * V) ≤ a * frobNorm (A - truncatedSVD A r) := by
    rw [Matrix.mul_assoc, hGV, ← Matrix.mul_assoc, ← hAVf, mul_comm a]
    exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (mul_le_mul_of_nonneg_left hD (frobNorm_nonneg _))
  have hk' : Fintype.card (Fin r) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
  refine ⟨Z, ?_⟩
  have hmeas : AEMeasurable (fun ω => X ω * pinv (Zᴴ * X ω)) μ :=
    (measurable_id.matrix_mul (measurable_pinv.comp
      (measurable_const.matrix_mul measurable_id))).comp_aemeasurable hX.aemeasurable
  have hMi := integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
    (B * V)
  have hI : Integrable (fun ω => specNorm (B * V) ^ 2 +
      frobNorm (B * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2) μ :=
    (integrable_const _).add hMi
  refine (integral_mono_ae (integrable_specNorm_sub_rsvd_sq B hmeas) hI ?_).trans ?_
  · filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
      (by rw [hZ.rank_eq, Fintype.card_fin]; omega)] with ω hω
    have h := hZ.specNorm_sub_rsvd_mul_pinv_sq_le hω B
    rw [hBE, hV.specNorm_mul_conjTranspose_right, Matrix.mul_assoc (B * V) Vᴴ (X ω)] at h
    exact h.trans (add_le_add le_rfl
      (pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm _) 2))
  · rw [integral_add (integrable_const _) hMi, integral_const, probReal_univ, one_smul,
      integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk',
      Fintype.card_fin]
    have hk : 0 ≤ (r : ℝ) / ((Fintype.card l : ℝ) - r - 1) := by
      have : (r : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hr
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    have h1 : specNorm (B * V) ^ 2 ≤ a ^ 2 * singularValues A r ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (specNorm_nonneg _) hS 2
    have h2 : frobNorm (B * V) ^ 2 ≤ a ^ 2 * frobNorm (A - truncatedSVD A r) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (frobNorm_nonneg _) hSF 2
    calc specNorm (B * V) ^ 2 + frobNorm (B * V) ^ 2 * r / ((Fintype.card l : ℝ) - r - 1)
        = specNorm (B * V) ^ 2 +
            (r : ℝ) / ((Fintype.card l : ℝ) - r - 1) * frobNorm (B * V) ^ 2 := by ring
      _ ≤ a ^ 2 * singularValues A r ^ 2 + (r : ℝ) / ((Fintype.card l : ℝ) - r - 1) *
            (a ^ 2 * frobNorm (A - truncatedSVD A r) ^ 2) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 hk)
      _ = _ := by ring

omit [DecidableEq n] in
/-- The rescaled Chebyshev filter evaluates as
$T_j(2x/s - 1) = T_j(2(x/s) - 1)$. -/
private theorem eval_T_comp_C_mul_X_sub_one (j : ℕ) (s y : ℝ) :
    ((Polynomial.Chebyshev.T ℝ (j : ℤ)).comp (Polynomial.C (2 / s) * Polynomial.X - 1)).eval y =
      (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (2 * (y / s) - 1) := by
  simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  ring_nf

/-- The Gram matrix of $\mathbf{A}f(\mathbf{A}^{\mathsf{H}}\mathbf{A})$ is
$\varphi(\mathbf{A}\mathbf{A}^{\mathsf{H}})$ with $\varphi(y) = f(y)\,y\,f(y)$. -/
private theorem mul_aeval_mul_conjTranspose_eq_cfc [DecidableEq m] (A : Matrix m n ℝ)
    (f : Polynomial ℝ) :
    A * Polynomial.aeval (Aᴴ * A) f * (A * Polynomial.aeval (Aᴴ * A) f)ᴴ =
      cfc (fun y => f.eval y * (y * f.eval y)) (A * Aᴴ) := by
  have hH : IsSelfAdjoint (A * Aᴴ) := Matrix.isHermitian_mul_conjTranspose_self A
  have hc : Continuous fun y => f.eval y := f.continuous
  have hF : cfc (fun y => f.eval y) (A * Aᴴ) * A = A * Polynomial.aeval (Aᴴ * A) f := by
    rw [cfc_polynomial f (A * Aᴴ) hH, aeval_mul_conjTranspose_self_mul]
  have hFH : (cfc (fun y => f.eval y) (A * Aᴴ))ᴴ = cfc (fun y => f.eval y) (A * Aᴴ) :=
    (cfc_predicate (fun y => f.eval y) (A * Aᴴ)).star_eq
  rw [← hF, Matrix.conjTranspose_mul, hFH,
    cfc_mul (fun y => f.eval y) (fun y => y * f.eval y) (A * Aᴴ) hc.continuousOn
      (continuous_id.mul hc).continuousOn,
    cfc_mul (fun y => y) (fun y => f.eval y) (A * Aᴴ) continuous_id.continuousOn
      hc.continuousOn, cfc_id' ℝ (A * Aᴴ) hH]
  simp only [Matrix.mul_assoc]

/-- A filter of degree below $q$ gives a competitor in the Krylov range: the error of RBKI is at
most that of the projector onto the range of $\mathbf{A}f(\mathbf{A}^{\mathsf{H}}\mathbf{A})
\mathbf{X}\mathbf{P}$, for every $\mathbf{P}$. -/
private theorem specNorm_sub_rbki_sq_le_of_degree_lt [DecidableEq m] {k : Type*} [Fintype k]
    (A : Matrix m n ℝ) {f : Polynomial ℝ} {q : ℕ} (hf : f.degree < q) (Y : Matrix n l ℝ)
    (P : Matrix l k ℝ) :
    specNorm (A - rbki A Y q) ^ 2 ≤
      specNorm ((1 - rangeProjector (A * Polynomial.aeval (Aᴴ * A) f * (Y * P))) * A) ^ 2 := by
  have hrange : LinearMap.range (A * Polynomial.aeval (Aᴴ * A) f * (Y * P)).mulVecLin ≤
      LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) Y q).mulVecLin :=
    (range_le_iff_exists_mul.mpr ⟨P, (Matrix.mul_assoc _ Y P).symm⟩).trans
      (range_mul_aeval_mul_le_range_mul_blockKrylovMatrix A (Aᴴ * A) Y hf)
  rw [rbki, sub_rsvd]
  exact pow_le_pow_left₀ (specNorm_nonneg _)
    (specNorm_one_sub_rangeProjector_mul_le_of_range_le hrange A) 2

omit [DecidableEq n] in
/-- A target rank with $\sigma_r(\mathbf{A}) > 0$ is below the number of columns. -/
private theorem le_card_of_singularValues_pos (A : Matrix m n ℝ) {r : ℕ}
    (hσ : 0 < singularValues A r) : r ≤ Fintype.card n := by
  by_contra h
  exact hσ.ne' (singularValues_of_card_cols_le A (by omega))

/-- **Tropp and Webber's gapless bound for randomized block Krylov iteration**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 2$ blocks, a target rank $r$ with
$r + 2 \le \ell$ and $\sigma_r(\mathbf{A}) > 0$,
the bound <!-- value rangeFinderTailRatio \mathbf{A} r \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 \le
\sigma_r(\mathbf{A})^2\exp\biggl(\frac{1}{16(q-1)^2}\log^2\biggl(4\Bigl(1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2}{\sigma_r(\mathbf{A})^2}
\Bigr)\biggr)\biggr)\,,$$
the argument of the logarithm being four times the range-finder tail ratio
`NLAlib.rangeFinderTailRatio`. The hypothesis $q \ge 2$ is needed: at $q = 1$ the right side is
$\sigma_r(\mathbf{A})^2$, below the error of the randomized SVD. The hypothesis
$\sigma_r(\mathbf{A}) > 0$ normalises the ratio; the bound would hold without it. Incomparable
with the $(1 + \varepsilon)$ form
(`NLAlib.integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`): this one
tends to $\sigma_r(\mathbf{A})^2$ as $q \to \infty$.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_rbki_sq_le_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, Theorem 9.1 (RBKI)]; there in logarithmic form with $m$ products and the rate
$1/(4(m-2)^2)$, indices from $1$; here $m = 2q$ (odd $m$ is not covered).
Result: rbki-gapless-error -/
theorem integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ} (hr : r + 2 ≤ Fintype.card l) (hq : 2 ≤ q)
    (hσ : 0 < singularValues A r) :
    ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      singularValues A r ^ 2 *
        Real.exp (Real.log (4 * rangeFinderTailRatio A r (Fintype.card l)) ^ 2 /
          (16 * ((q : ℝ) - 1) ^ 2)) := by
  classical
  have := hX.isProbabilityMeasure
  set σ := singularValues A r
  set R := rangeFinderTailRatio A r (Fintype.card l)
  have hσ2 : 0 < σ ^ 2 := pow_pos hσ 2
  set j := q - 1 with hj
  have hj1 : 0 < j := by omega
  have hjq : (q : ℝ) - 1 = j := by rw [hj, Nat.cast_sub (by omega), Nat.cast_one]
  -- The filter $f(y) = T_j(2y/\sigma_r^2 - 1)$: degree $j < q$, at most $1$ on the tail.
  set f : Polynomial ℝ := (Polynomial.Chebyshev.T ℝ (j : ℤ)).comp
    (Polynomial.C (2 / σ ^ 2) * Polynomial.X - 1)
  have hfe (y : ℝ) :
      f.eval y = (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (2 * (y / σ ^ 2) - 1) :=
    eval_T_comp_C_mul_X_sub_one j (σ ^ 2) y
  have hfdeg : f.degree < q := (Polynomial.degree_le_of_natDegree_le
    (Polynomial.Chebyshev.natDegree_T_comp_le (j : ℤ) (by compute_degree))).trans_lt
      (by rw [Int.natAbs_natCast]; exact_mod_cast (by omega : j < q))
  have htail : ∀ x ∈ Set.Icc 0 (σ ^ 2), |f.eval x| ≤ 1 := fun x hx =>
    Polynomial.Chebyshev.abs_eval_T_comp_C_mul_X_sub_one_le j hσ2 hx
  obtain ⟨W, hW⟩ := exists_integral_specNorm_sub_rsvd_mul_pinv_sq_le A hX f
    (le_card_of_singularValues_pos A hσ) hr htail
  rw [one_pow, one_mul, ← singularValues_sq_mul_rangeFinderTailRatio A _ hσ] at hW
  set G := Polynomial.aeval (Aᴴ * A) f
  set B := A * G
  set Ω' : Ω → Matrix n (Fin r) ℝ := fun ω => X ω * pinv (Wᴴ * X ω)
  set x : Ω → ℝ := fun ω => specNorm ((1 - rangeProjector (B * Ω' ω)) * A) ^ 2
  set φ : ℝ → ℝ := fun y => y * ((Polynomial.Chebyshev.T ℝ (j : ℤ)).eval
    (2 * (y / σ ^ 2) - 1)) ^ 2 with hφ
  -- $\mathbf{B}\mathbf{B}^{\mathsf{H}} = \varphi(\mathbf{A}\mathbf{A}^{\mathsf{H}})$.
  have hBB : B * Bᴴ = cfc φ (A * Aᴴ) := by
    have hφ' : φ = fun y => f.eval y * (y * f.eval y) := by
      funext y
      rw [hφ, hfe]
      ring
    rw [hφ']
    exact mul_aeval_mul_conjTranspose_eq_cfc A f
  -- Each competitor projector has rank at most $r$, so $\sigma_r^2 \le x$.
  have hlow (ω : Ω) : σ ≤ specNorm ((1 - rangeProjector (B * Ω' ω)) * A) := by
    have hrk : (rangeProjector (B * Ω' ω) * A).rank ≤ r :=
      (Matrix.rank_mul_le_left _ _).trans ((rank_rangeProjector _).le.trans
        ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin r)))
    have h := singularValues_le_specNorm_sub_of_rank_le A hrk
    rwa [Matrix.sub_mul, Matrix.one_mul]
  have hlow2 (ω : Ω) : σ ^ 2 ≤ x ω := pow_le_pow_left₀ hσ.le (hlow ω) 2
  -- The competitor lies in the Krylov range, so RBKI does at least as well.
  have hup (ω : Ω) : specNorm (A - rbki A (X ω) q) ^ 2 ≤ x ω :=
    specNorm_sub_rbki_sq_le_of_degree_lt A hfdeg (X ω) (pinv (Wᴴ * X ω))
  -- The projection half of the almost-convex Jensen inequality, pointwise.
  have hjen (ω : Ω) : φ (x ω) ≤ specNorm (B - rsvd B (Ω' ω)) ^ 2 := by
    rw [sub_rsvd]
    exact apply_specNorm_mul_sq_le_specNorm_mul_sq_of_hasSupportingLineOn hBB
      (isStarProjection_one_sub_rangeProjector _) (hσ.trans_le (hlow ω))
      (hasSupportingLineOn_mul_eval_T_div_sq j hσ2 (hlow2 ω))
  -- Integrability.
  have hΩ'm : AEMeasurable Ω' μ :=
    (measurable_id.matrix_mul (measurable_pinv.comp
      (measurable_const.matrix_mul measurable_id))).comp_aemeasurable hX.aemeasurable
  have hxi : Integrable x μ := integrable_specNorm_one_sub_rangeProjector_mul_sq B A hΩ'm
  have hBi := integrable_specNorm_sub_rsvd_sq B hΩ'm
  have hφc : Continuous φ :=
    continuous_id.mul (((Polynomial.Chebyshev.T ℝ (j : ℤ)).continuous.comp
      ((continuous_const.mul (continuous_id.div_const _)).sub continuous_const)).pow 2)
  have hφi : Integrable (φ ∘ x) μ :=
    hBi.mono' (hφc.comp_aestronglyMeasurable hxi.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by
        have h0 : 0 ≤ φ (x ω) := mul_nonneg ((sq_nonneg _).trans (hlow2 ω)) (sq_nonneg _)
        rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg h0]
        exact hjen ω)
  -- The scalar half, then the inversion.
  have hx0 : σ ^ 2 ≤ ∫ ω, x ω ∂μ := by
    have h := integral_mono (integrable_const (σ ^ 2)) hxi hlow2
    rwa [integral_const, probReal_univ, one_smul] at h
  have hJ := (hasSupportingLineOn_mul_eval_T_div_sq j hσ2 hx0).le_integral_comp
    (Filter.Eventually.of_forall fun ω => Set.mem_Ici.mpr (sq_nonneg _)) hxi hφi
  have hchain : φ (∫ ω, x ω ∂μ) ≤ σ ^ 2 * R := hJ.trans ((integral_mono hφi hBi hjen).trans hW)
  rw [hjq]
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hxi
    (Filter.Eventually.of_forall hup)).trans ?_
  exact le_mul_exp_of_mul_eval_T_sq_le hj1 hσ2 hx0 hchain

/-- **Tropp and Webber's gapless bound for randomized subspace iteration**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a target rank $r$ with
$r + 2 \le \ell$ and $\sigma_r(\mathbf{A}) > 0$,
the bound <!-- value rangeFinderTailRatio \mathbf{A} r \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\|_2^2 \le
\sigma_r(\mathbf{A})^2\Bigl(1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2}{\sigma_r(\mathbf{A})^2}
\Bigr)^{1/(2p+1)}\,,$$
the range-finder tail ratio `NLAlib.rangeFinderTailRatio` to the power $1/(2p + 1)$. At $p = 0$
it is the bound of the randomized SVD (TW Theorem 8.1). The proof uses the power lemma
(`IsStarProjection.specNorm_mul_pow_le`) in place of the almost-convex Jensen inequality.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_rsvd_pow_mul_sq_le_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, Theorem 9.1 (RSI)]; there in logarithmic form with $m$ products and the rate
$1/(m - 1)$; here $m = 2p + 2$. The power lemma is [HalkoMartinssonTropp2011, Proposition 8.6].
Result: rsi-gapless-error -/
theorem integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (p : ℕ) (hσ : 0 < singularValues A r) :
    ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      singularValues A r ^ 2 *
        rangeFinderTailRatio A r (Fintype.card l) ^ (1 / (2 * (p : ℝ) + 1)) := by
  classical
  have := hX.isProbabilityMeasure
  set σ := singularValues A r
  set R := rangeFinderTailRatio A r (Fintype.card l)
  have htail : ∀ x ∈ Set.Icc 0 (σ ^ 2),
      |(Polynomial.X ^ p : Polynomial ℝ).eval x| ≤ (σ ^ 2) ^ p := fun x hx => by
    rw [Polynomial.eval_pow, Polynomial.eval_X, abs_of_nonneg (pow_nonneg hx.1 p)]
    exact pow_le_pow_left₀ hx.1 hx.2 p
  obtain ⟨W, hW⟩ := exists_integral_specNorm_sub_rsvd_mul_pinv_sq_le A hX (Polynomial.X ^ p)
    (le_card_of_singularValues_pos A hσ) hr htail
  rw [← singularValues_sq_mul_rangeFinderTailRatio A _ hσ, Polynomial.aeval_X_pow] at hW
  set B := A * (Aᴴ * A) ^ p with hBdef
  set Ω' : Ω → Matrix n (Fin r) ℝ := fun ω => X ω * pinv (Wᴴ * X ω) with hΩ'
  set y : Ω → ℝ := fun ω => specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 with hy
  have hBA : (A * Aᴴ) ^ p * A = B := by
    simpa only [Polynomial.aeval_X_pow] using aeval_mul_conjTranspose_self_mul A (Polynomial.X ^ p)
  -- The power lemma, then the competitor inside the range of the sketch.
  have hpt (ω : Ω) : y ω ^ (2 * p + 1) ≤ specNorm (B - rsvd B (Ω' ω)) ^ 2 := by
    have h := (isStarProjection_one_sub_rangeProjector
      (A * ((Aᴴ * A) ^ p * X ω))).specNorm_mul_pow_le A p
    rw [hBA] at h
    have h2 := specNorm_one_sub_rangeProjector_mul_le_of_range_le
      (B := A * ((Aᴴ * A) ^ p * X ω)) (Y := B * Ω' ω)
      (range_le_iff_exists_mul.mpr ⟨pinv (Wᴴ * X ω), by
        simp only [hBdef, hΩ', Matrix.mul_assoc]⟩) B
    rw [← sub_rsvd B (Ω' ω)] at h2
    simp only [hy]
    rw [sub_rsvd A ((Aᴴ * A) ^ p * X ω), ← pow_mul,
      show 2 * (2 * p + 1) = (2 * p + 1) * 2 by ring, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (specNorm_nonneg _) _) (h.trans h2) 2
  have hΩ'm : AEMeasurable Ω' μ :=
    (measurable_id.matrix_mul (measurable_pinv.comp
      (measurable_const.matrix_mul measurable_id))).comp_aemeasurable hX.aemeasurable
  have hBi := integrable_specNorm_sub_rsvd_sq B hΩ'm
  have hyi : Integrable y μ := integrable_specNorm_sub_rsvd_sq A
    ((measurable_const.matrix_mul measurable_id).comp_aemeasurable hX.aemeasurable)
  have hyk : Integrable (fun ω => y ω ^ (2 * p + 1)) μ :=
    hBi.mono' (hyi.aestronglyMeasurable.pow _) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
      exact hpt ω)
  have hy0 : 0 ≤ ∫ ω, y ω ∂μ := integral_nonneg fun ω => sq_nonneg _
  -- Jensen for the convex power, then the $(2p + 1)$-th root.
  have hJ := ((convexOn_pow (2 * p + 1)).hasSupportingLineOn (Set.mem_Ici.mpr hy0)
    (differentiableAt_pow _)).le_integral_comp
    (Filter.Eventually.of_forall fun ω => Set.mem_Ici.mpr (sq_nonneg _)) hyi hyk
  beta_reduce at hJ
  have hk : (∫ ω, y ω ∂μ) ^ (2 * p + 1) ≤ (σ ^ 2) ^ (2 * p + 1) * R :=
    hJ.trans ((integral_mono hyk hBi hpt).trans (hW.trans_eq (by ring)))
  have hR : 0 ≤ R := zero_le_one.trans (one_le_rangeFinderTailRatio A hr)
  have hn : 2 * p + 1 ≠ 0 := by omega
  calc ∫ ω, y ω ∂μ = ((∫ ω, y ω ∂μ) ^ (2 * p + 1)) ^ ((2 * p + 1 : ℕ) : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast hy0 hn).symm
    _ ≤ ((σ ^ 2) ^ (2 * p + 1) * R) ^ ((2 * p + 1 : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg hy0 _) hk (by positivity)
    _ = σ ^ 2 * R ^ (1 / (2 * (p : ℝ) + 1)) := by
        rw [Real.mul_rpow (by positivity) hR, Real.pow_rpow_inv_natCast (sq_nonneg σ) hn,
          one_div]
        push_cast
        rfl

/-! ### Asymptotic forms -/

/-- **Depth $O(\log(\lvert n \rvert + 1)/\sqrt{\varepsilon})$ suffices for randomized block Krylov
iteration**, spectral norm, no gap: there are absolute constants $C, \varepsilon_0 > 0$ such that
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a target rank $r$ with
$r + 2 \le \ell$, $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\log(\lvert n \rvert + 1)/\sqrt{\varepsilon}$ blocks,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 \le
(1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of Tropp and Webber's gapless bound
`NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix`, with the tail ratio at
most $1 + \lvert n \rvert^2$ (`NLAlib.rangeFinderTailRatio_le_one_add_card_sq`); no factor
$\log(1/\varepsilon)$ enters. When $\sigma_r(\mathbf{A}) = 0$ the $(1 + \varepsilon)$ form
(`NLAlib.integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`) gives error
$0$, so no positivity hypothesis is needed. The proof takes $C = 4$ and $\varepsilon_0 = 1$.
[TroppWebber2023, Theorem 9.1 (RBKI)]; there in logarithmic form with $m = 2q$ products.
Asymptotic:
NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix
Result: rbki-gapless-error -/
theorem exists_forall_integral_specNorm_sub_rbki_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (r q : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → r + 2 ≤ Fintype.card l → 0 < ε →
      ε ≤ ε₀ → C * Real.log (Fintype.card n + 1) / Real.sqrt ε ≤ q →
      ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤ (1 + ε) * singularValues A r ^ 2 := by
  refine ⟨4, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X r q ε hX hr hε hε₁ hq
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hN0 | hNpos
  · -- No columns: $\mathbf{A} = \mathbf{0}$.
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hN0
    have h0 : ∀ ω, A - rbki A (X ω) q = 0 := fun ω => Subsingleton.elim _ _
    simp only [h0, specNorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
    positivity
  have hN : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast hNpos
  obtain ⟨hq2, hexp⟩ := Real.two_le_and_exp_log_four_mul_sq_div_le_one_add hN hε hε₁ hq
  rcases (singularValues_nonneg A r).eq_or_lt with hσ0 | hσ
  · -- $\sigma_r(\mathbf{A}) = 0$: the $(1 + \varepsilon)$ form bounds the error by $0$.
    have hA : A - truncatedSVD A r = 0 := by
      rw [truncatedSVD_of_singularValues_eq_zero A hσ0.symm, sub_self]
    have h := integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix A hX hr
      (q := q) (by omega) hε
    rw [hA, frobNorm_zero, ← hσ0] at h
    rw [← hσ0]
    simpa using h
  refine (integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix A hX hr hq2
    hσ).trans ?_
  rw [mul_comm (1 + ε)]
  exact mul_le_mul_of_nonneg_left (hexp _ (one_le_rangeFinderTailRatio A hr)
    (rangeFinderTailRatio_le_one_add_card_sq A hr hσ)) (sq_nonneg _)

/-- **$O(\log(\lvert n \rvert + 1)/\varepsilon)$ power steps suffice for randomized subspace
iteration**, spectral norm, no gap: there are absolute constants $C, \varepsilon_0 > 0$ such that
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a target rank $r$ with
$r + 2 \le \ell$, $0 < \varepsilon \le \varepsilon_0$ and
$p \ge C\log(\lvert n \rvert + 1)/\varepsilon$ power steps,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p
\mathbf{X})\|_2^2 \le (1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of Tropp and Webber's gapless bound
`NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix`, with the tail
ratio at most $1 + \lvert n \rvert^2$ (`NLAlib.rangeFinderTailRatio_le_one_add_card_sq`). When
$\sigma_r(\mathbf{A}) = 0$ the $(1 + \varepsilon)$ form
(`NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`) gives
error $0$, so no positivity hypothesis is needed. The proof takes $C = 2$ and $\varepsilon_0 = 1$.
[TroppWebber2023, Theorem 9.1 (RSI)]; there in logarithmic form with $m = 2p + 2$ products.
Asymptotic:
NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix
Result: rsi-gapless-error -/
theorem exists_forall_integral_specNorm_sub_rsvd_pow_mul_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (r p : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → r + 2 ≤ Fintype.card l → 0 < ε →
      ε ≤ ε₀ → C * Real.log (Fintype.card n + 1) / ε ≤ p →
      ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
        (1 + ε) * singularValues A r ^ 2 := by
  refine ⟨2, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X r p ε hX hr hε hε₁ hp
  rcases (singularValues_nonneg A r).eq_or_lt with hσ0 | hσ
  · -- $\sigma_r(\mathbf{A}) = 0$: the $(1 + \varepsilon)$ form bounds the error by $0$.
    have hA : A - truncatedSVD A r = 0 := by
      rw [truncatedSVD_of_singularValues_eq_zero A hσ0.symm, sub_self]
    have h := integral_specNorm_sub_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix A hX
      hr p hε
    rw [hA, frobNorm_zero, ← hσ0] at h
    rw [← hσ0]
    simpa using h
  refine (integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix A hX hr p
    hσ).trans ?_
  rw [mul_comm (1 + ε)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_one_div_two_mul_add_one_le_one_add (Nat.cast_nonneg _)
    (one_le_rangeFinderTailRatio A hr) (rangeFinderTailRatio_le_one_add_card_sq A hr hσ) hε hε₁
    hp) (sq_nonneg _)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n \rvert/\varepsilon)/\varepsilon)$ power steps suffice for truncated
randomized subspace iteration**, spectral norm, no gap: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$,
a target rank $r$ with $r + 2 \le \ell$, $0 < \varepsilon \le \varepsilon_0$ and
$p \ge C\log(\lvert n \rvert/\varepsilon)/\varepsilon$ power steps,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_2^2 \le
(1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of
`NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`,
at $\varepsilon/3$, with the tail term at most
$\lvert n \rvert^2e^{-8p\varepsilon/(6 + \varepsilon)}\sigma_r(\mathbf{A})^2$; the proof takes
$C = 11$ and $\varepsilon_0 = 1/2$. At $\lvert n \rvert = 0$ every $p$ is allowed (Lean's
$\log 0 = 0$), harmlessly, since then $\mathbf{A} = \mathbf{0}$.
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2 (RSI)]; there for block
Krylov iteration (MM) or gapped (TW).
Asymptotic:
NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
Result: rsi-gapless-error -/
theorem
exists_forall_integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (r p : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → r + 2 ≤ Fintype.card l → 0 < ε →
      ε ≤ ε₀ → C * Real.log (Fintype.card n / ε) / ε ≤ p →
      ∫ ω, specNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
        (1 + ε) * singularValues A r ^ 2 := by
  refine ⟨11, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X r p ε hX hr hε hε₀ hp
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hN0 | hNpos
  · -- No columns: $\mathbf{A} = \mathbf{0}$.
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hN0
    have h0 : ∀ ω, A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r = 0 := fun ω =>
      Subsingleton.elim _ _
    simp only [h0, specNorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
    positivity
  have hN : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast hNpos
  set N : ℝ := (Fintype.card n : ℝ)
  set L := Real.log (N / ε) with hLdef
  have hpε : 11 * L ≤ p * ε := by rwa [div_le_iff₀ hε] at hp
  have hlog2 : Real.log 2 ≤ L :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have hlog4 : Real.log (N / (ε / 4)) = Real.log 4 + L := by
    rw [hLdef, ← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hfrac : ε / 7 ≤ ε / 3 / (2 + ε / 3) := by
    rw [div_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hy : -8 * (p : ℝ) * (ε / 3 / (2 + ε / 3)) ≤ -(4 * Real.log (N / (ε / 4))) := by
    rw [hlog4]
    nlinarith [mul_le_mul_of_nonneg_left hfrac hp0]
  have hexp :=
    integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
      A hX hr p (ε := ε / 3) (by positivity)
  rw [← one_mul (Real.exp _)] at hexp
  have h := Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) zero_le_one (by norm_num)
    (natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq A
      le_rfl hr) hN (by positivity) (by linarith) hy
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  nlinarith

end NLAlib
