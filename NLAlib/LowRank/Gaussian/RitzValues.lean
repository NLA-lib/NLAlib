/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.BlockKrylovSum
public import NLAlib.LowRank.Structural.FilteredResidual
public import NLAlib.Probability.Tail

/-!
# Weighted Gaussian block Krylov singular-value deficits

Power-weighted polynomial filters bound the individual squared singular-value deficits of
randomized block Krylov iteration in expectation. The filtered residual energy is controlled
by a Schatten power of the tail, with no factor of the dimension.

## Main results

* The expected weighted singular-value deficit with a spectral gap.
* The expected positive part of a gapless singular-value deficit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

section Gaussian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l m n : Type*}
  [Fintype l] [Fintype m] [Fintype n] [DecidableEq n] {X : Ω → Matrix n l ℝ}

/-- A power-weighted filter measures tail energy in the requested Schatten power. -/
private theorem weighted_power_le {x s a v P : ℝ} {r : ℕ} (hx : 0 ≤ x) (hxs : x ≤ s)
    (hP : 0 < P) (hr : P ≤ 4 * r + 2) (hv : |v| ≤ a * (x ^ 2) ^ r) :
    x ^ 2 * v ^ 2 ≤ a ^ 2 * s ^ (4 * r + 2 - P) * x ^ P := by
  rcases hx.eq_or_lt with h0 | hx
  · rw [← h0]
    simp only [zero_pow two_ne_zero, zero_mul, Real.zero_rpow hP.ne', mul_zero, le_refl]
  have hN : x ^ 2 * ((x ^ 2) ^ r) ^ 2 = x ^ (4 * r + 2) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hpow : x ^ (4 * r + 2) = x ^ P * x ^ (4 * r + 2 - P) := by
    rw [← Real.rpow_add hx]
    have he : P + (4 * (r : ℝ) + 2 - P) = (4 * r + 2 : ℕ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
  have hbound := pow_le_pow_left₀ (abs_nonneg v) hv 2
  rw [sq_abs, mul_pow] at hbound
  have hstep := mul_le_mul_of_nonneg_left hbound (sq_nonneg x)
  have hm := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hx.le hxs (by linarith : 0 ≤ 4 * (r : ℝ) + 2 - P))
    (show 0 ≤ a ^ 2 * x ^ P by positivity)
  nlinarith [hN, hpow]

/-- The head weight cancels the Schatten deficit weight, leaving a ratio at most one. -/
private theorem weighted_scale_le {x s c a P : ℝ} {r : ℕ} (hx : 0 < x) (hs : 0 ≤ s)
    (hxs : s ≤ x) (hc : 0 < c) (hr : P ≤ 4 * r + 2) :
    x ^ (P - 2) * (c * (x ^ 2) ^ r)⁻¹ ^ 2 *
      (a ^ 2 * s ^ (4 * r + 2 - P)) ≤ (a / c) ^ 2 := by
  have hw : ((x ^ 2) ^ r) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hx.ne'))
  have hpow : x ^ (P - 2) * x ^ (4 * r + 2 - P) = ((x ^ 2) ^ r) ^ 2 := by
    rw [← Real.rpow_add hx, ← pow_mul, ← pow_mul]
    have he : P - 2 + (4 * (r : ℝ) + 2 - P) = (2 * (r * 2) : ℕ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
  have hm : x ^ (P - 2) * s ^ (4 * r + 2 - P) ≤ ((x ^ 2) ^ r) ^ 2 := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hs hxs (by linarith)) (Real.rpow_nonneg hx.le _)
  calc _ = ((a / c) ^ 2 / ((x ^ 2) ^ r) ^ 2) *
        (x ^ (P - 2) * s ^ (4 * r + 2 - P)) := by field_simp
    _ ≤ ((a / c) ^ 2 / ((x ^ 2) ^ r) ^ 2) * ((x ^ 2) ^ r) ^ 2 :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (a / c) ^ 2 := div_mul_cancel₀ _ hw

/-- A squared spectral gap controls the Chebyshev relative gap. -/
private theorem gap_rate_bound {s τ γ : ℝ} (hs : 0 < s) (hτ : 0 ≤ τ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hgap : (1 + γ) * τ ^ 2 ≤ s ^ 2) :
    γ * (s + τ) ^ 2 ≤ 8 * (s ^ 2 - τ ^ 2) := by
  rcases le_or_gt (9 * τ) (7 * s) with h | h
  · nlinarith
  · have hsum : s + τ ≤ 16 / 7 * τ := by linarith
    have hsq : (s + τ) ^ 2 ≤ 8 * τ ^ 2 := by
      nlinarith [mul_le_mul hsum hsum (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hγ]

/-- The filter cut is capped at the tail level so that both regimes have the gapless rate. -/
private theorem cut_rate_bound {s b τ γ : ℝ} (hs : 0 < s) (hb : 0 ≤ b) (hbs : b ≤ s)
    (hτ : 0 ≤ τ) (hτ2 : τ ^ 2 = s ^ 2 - γ * b ^ 2) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    γ * (s + min b τ) ^ 2 ≤ 8 * (s ^ 2 - min b τ ^ 2) := by
  rcases le_total b τ with h | h
  · rw [min_eq_left h]
    apply gap_rate_bound hs hb hγ.le hγ1
    nlinarith [pow_le_pow_left₀ hb h 2]
  · rw [min_eq_right h]
    have hτs : τ ≤ s := by nlinarith
    have hsq : (s + τ) ^ 2 ≤ 4 * s ^ 2 := by nlinarith [sq_nonneg (s - τ)]
    have hsmall : s ^ 2 ≤ 2 * b ^ 2 := by nlinarith [pow_le_pow_left₀ hτ h 2]
    nlinarith [mul_le_mul_of_nonneg_left hsq hγ.le]

/-- The inverse head weight leaves exactly the reciprocal Schatten weight of the tail level. -/
private theorem weighted_unscaled_eq {x c a P : ℝ} {r : ℕ} (hx : 0 < x) (hc : 0 < c) :
    (c * (x ^ 2) ^ r)⁻¹ ^ 2 * (a ^ 2 * x ^ (4 * r + 2 - P)) =
      (a / c) ^ 2 * x ^ (2 - P) := by
  have hpow : x ^ (4 * r + 2 - P) = ((x ^ 2) ^ r) ^ 2 * x ^ (2 - P) := by
    rw [← pow_mul, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hx]
    congr 1
    push_cast
    ring
  rw [hpow]
  field_simp [hc.ne', pow_ne_zero _ (pow_ne_zero _ hx.ne')]

/-- Integrate a polynomial-filter deficit using the Gaussian residual moment. -/
private theorem integral_deficit_le_of_filter {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {t q i : ℕ}
    (hl : t + 2 ≤ Fintype.card l) (hit : i < t) (f : Polynomial ℝ) (hf : f.degree < q)
    {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) {w : ℝ} (hw0 : 0 ≤ w)
    (hhead : ∀ j ≤ i, c ≤ |f.eval (singularValues A j ^ 2)|)
    (hw : ∀ j, t ≤ j → singularValues A j ^ 2 * f.eval (singularValues A j ^ 2) ^ 2 ≤
      b * singularValues A j ^ p.toReal) :
    ∫ ω, w *
      (singularValues A i ^ 2 - singularValues (rbki A (X ω) q) i ^ 2) ∂μ ≤
      w * c⁻¹ ^ 2 *
        ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * b *
        schattenNorm p (A - truncatedSVD A t) ^ p.toReal := by
  classical
  have hO0 := Real.rpow_nonneg (schattenNorm_nonneg p (A - truncatedSVD A t)) p.toReal
  have := hX.isProbabilityMeasure
  obtain ⟨Z, hZ, hAZ, hrk, -, -⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix A hX hl
  set B := A * cfc (fun x => f.eval x) (Aᴴ * A)
  have hs : Fintype.card (Fin (min t (Fintype.card n))) + 2 ≤ Fintype.card l := by
    rw [Fintype.card_fin]
    omega
  have hi := integrable_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix B hX hZ hs
  have hiD := ((integrable_const (singularValues A i ^ 2)).sub
    (integrable_singularValues_rbki_sq A hX.aemeasurable q i)).const_mul
      (w)
  have hmoment := integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix B hX hZ hs
  have henergy := frobNorm_sub_mul_cfc_mul_sq_le_mul_schattenNorm_rpow
    (fun x => f.eval x) hAZ hp0 hp hw
  have hbound : ∀ᵐ ω ∂μ, w *
      (singularValues A i ^ 2 - singularValues (rbki A (X ω) q) i ^ 2) ≤
      w * c⁻¹ ^ 2 *
        frobNorm ((B - B * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2 := by
    filter_upwards [hrk] with ω hω
    have h := hZ.singularValues_sq_sub_inv_sq_mul_le_singularValues_rsvd_cfc_sq
      (fun x => f.eval x) hω hAZ hit hc hhead
    have hcomp := pow_le_pow_left₀ (singularValues_nonneg _ _)
      (singularValues_rsvd_cfc_le_singularValues_rbki A (X ω) hf i) 2
    have hn := pow_le_pow_left₀ (specNorm_nonneg _)
      (specNorm_le_frobNorm ((B - B * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω))) 2
    have hdef : singularValues A i ^ 2 - singularValues (rbki A (X ω) q) i ^ 2 ≤
        c⁻¹ ^ 2 * frobNorm ((B - B * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg c⁻¹)]
    nlinarith [mul_le_mul_of_nonneg_left hdef
      hw0]
  refine (integral_mono_ae hiD (hi.const_mul _) hbound).trans ?_
  rw [integral_const_mul, hmoment, Fintype.card_fin, mul_div_assoc]
  have htl : (t : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hl
  have hst : ((min t (Fintype.card n) : ℕ) : ℝ) ≤ t := Nat.cast_le.mpr (min_le_left _ _)
  have hratio := div_le_div₀ (Nat.cast_nonneg t) hst
    (show (0 : ℝ) < Fintype.card l - t - 1 by linarith)
    (show (Fintype.card l : ℝ) - t - 1 ≤ Fintype.card l - min t (Fintype.card n) - 1 by linarith)
  have hmul := mul_le_mul henergy hratio
    (div_nonneg (Nat.cast_nonneg _) (by linarith))
    (show 0 ≤ b * schattenNorm p (A - truncatedSVD A t) ^ p.toReal by positivity)
  have hfinal := mul_le_mul_of_nonneg_left hmul
    (show 0 ≤ w * c⁻¹ ^ 2 by positivity)
  nlinarith

/-- Integrate the positive part of a cut deficit using the filtered Gaussian residual. -/
private theorem integral_max_deficit_le_of_filter {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {t q i : ℕ}
    (hl : t + 2 ≤ Fintype.card l) (hit : i < t) (f : Polynomial ℝ) (hf : f.degree < q)
    {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) {w : ℝ} (hw0 : 0 ≤ w) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτi : τ ≤ singularValues A i)
    (hhead : ∀ j ≤ i, c ≤ |f.eval (singularValues A j ^ 2)|)
    (hw : ∀ j, t ≤ j → singularValues A j ^ 2 *
      (Set.indicator (Set.Iio (τ ^ 2)) (fun x => f.eval x) (singularValues A j ^ 2)) ^ 2 ≤
      b * singularValues A j ^ p.toReal) :
    ∫ ω, w *
      (max 0 (τ ^ 2 - singularValues (rbki A (X ω) q) i ^ 2)) ∂μ ≤
      w * c⁻¹ ^ 2 *
        ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * b *
        schattenNorm p (A - truncatedSVD A t) ^ p.toReal := by
  classical
  have hO0 := Real.rpow_nonneg (schattenNorm_nonneg p (A - truncatedSVD A t)) p.toReal
  have := hX.isProbabilityMeasure
  obtain ⟨Z, hZ, hAZ, hrk, -, -⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix A hX hl
  set B := A * cfc (Set.indicator (Set.Iio (τ ^ 2)) (fun x => f.eval x)) (Aᴴ * A)
  have hs : Fintype.card (Fin (min t (Fintype.card n))) + 2 ≤ Fintype.card l := by
    rw [Fintype.card_fin]
    omega
  have hi := integrable_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix B hX hZ hs
  have hiD := ((integrable_const (0 : ℝ)).sup
    ((integrable_const (τ ^ 2)).sub
      (integrable_singularValues_rbki_sq A hX.aemeasurable q i))).const_mul w
  have hmoment := integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix B hX hZ hs
  have henergy := frobNorm_sub_mul_cfc_mul_sq_le_mul_schattenNorm_rpow
    (Set.indicator (Set.Iio (τ ^ 2)) (fun x => f.eval x)) hAZ hp0 hp hw
  have hbound : ∀ᵐ ω ∂μ, w *
      (max 0 (τ ^ 2 - singularValues (rbki A (X ω) q) i ^ 2)) ≤
      w * c⁻¹ ^ 2 *
        frobNorm ((B - B * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2 := by
    filter_upwards [hrk] with ω hω
    have h := hZ.sq_sub_inv_sq_mul_le_singularValues_rsvd_cfc_sq_of_le_singularValues
      (fun x => f.eval x) hω
      (truncatedSVD_mul_mul_conjTranspose_of_le hAZ (by omega)) hc hτ hτi hhead
    have hcomp := pow_le_pow_left₀ (singularValues_nonneg _ _)
      (singularValues_rsvd_cfc_le_singularValues_rbki A (X ω) hf i) 2
    have hn := pow_le_pow_left₀ (specNorm_nonneg _)
      (specNorm_le_frobNorm ((B - B * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω))) 2
    have hdef : max 0 (τ ^ 2 -
        singularValues (rbki A (X ω) q) i ^ 2) ≤
        c⁻¹ ^ 2 * frobNorm ((B - B * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2 := by
      apply max_le (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg c⁻¹)]
    nlinarith [mul_le_mul_of_nonneg_left hdef
      hw0]
  refine (integral_mono_ae hiD (hi.const_mul _) hbound).trans ?_
  rw [integral_const_mul, hmoment, Fintype.card_fin, mul_div_assoc]
  have htl : (t : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hl
  have hst : ((min t (Fintype.card n) : ℕ) : ℝ) ≤ t := Nat.cast_le.mpr (min_le_left _ _)
  have hratio := div_le_div₀ (Nat.cast_nonneg t) hst
    (show (0 : ℝ) < Fintype.card l - t - 1 by linarith)
    (show (Fintype.card l : ℝ) - t - 1 ≤ Fintype.card l - min t (Fintype.card n) - 1 by linarith)
  have hmul := mul_le_mul henergy hratio
    (div_nonneg (Nat.cast_nonneg _) (by linarith))
    (show 0 ≤ b * schattenNorm p (A - truncatedSVD A t) ^ p.toReal by positivity)
  have hfinal := mul_le_mul_of_nonneg_left hmul
    (show 0 ≤ w * c⁻¹ ^ 2 by positivity)
  nlinarith

/-! ### Weighted deficits of one run -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **A weighted deficit of one Gaussian block Krylov run with a gap, in expectation**: let
$2 \le p < \infty$, $\mathbf{A}$ a real matrix, $\mathbf{X}$ a standard Gaussian $n \times \ell$
test matrix (independent standard normal entries), $t + 2 \le \ell$, $r$ with $p \le 4r + 2$,
$q \ge r + 1$, $i < t$ and $0 < \theta \le 1$ with
$(1 + \theta)\,\sigma_t(\mathbf{A})^2 \le \sigma_i(\mathbf{A})^2$. Then
$$\mathbb{E}\Bigl[\sigma_i(\mathbf{A})^{p-2}\Bigl(\sigma_i(\mathbf{A})^2 -
\sigma_i\bigl(\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\bigr)^2\Bigr)\Bigr] \le
4e^{-\frac{8}{3}(q-1-r)\sqrt{\theta}}\,\frac{t}{\ell - t - 1}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{S_p}^p\,.$$
The filter is a Chebyshev filter of degree $q - 1 - r$ times the weight $x^r$; the weight
measures the filtered tail in the Schatten $p$-norm, relative to $\sigma_i$ itself.
[BakshiNarayanan2023, proof of Lemma 7.6]; there for rank one and one Gaussian start vector,
here for every index of a gapped head and any block of at least $t + 2$ columns;
[BakshiClarksonWoodruff2022, Lemma 3.2]; there with a uniform bound of the filter on the tail,
here with the weighted filtered residual. -/
theorem
    integral_singularValues_rpow_mul_singularValues_sq_sub_singularValues_rbki_sq_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {t r q i : ℕ} (hl : t + 2 ≤ Fintype.card l)
    (hr : p.toReal ≤ 4 * r + 2) (hq : r + 1 ≤ q) (hit : i < t) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hgap : (1 + θ) * singularValues A t ^ 2 ≤ singularValues A i ^ 2) :
    ∫ ω, singularValues A i ^ (p.toReal - 2) *
        (singularValues A i ^ 2 - singularValues (rbki A (X ω) q) i ^ 2) ∂μ ≤
      4 * Real.exp (-(8 / 3) * ((q : ℝ) - 1 - r) * Real.sqrt θ) *
        ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
        schattenNorm p (A - truncatedSVD A t) ^ p.toReal := by
  classical
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp2).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hden : (0 : ℝ) < Fintype.card l - t - 1 := by
    have htl : (t : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hl
    linarith
  rcases (singularValues_nonneg A i).eq_or_lt with hσ | hσ
  · have hz (ω : Ω) : singularValues (rbki A (X ω) q) i = 0 := by
      have h := (isStarProjection_rangeProjector
        (A * blockKrylovMatrix (Aᴴ * A) (X ω) q)).singularValues_mul_le A i
      change singularValues (rbki A (X ω) q) i ≤ singularValues A i at h
      exact le_antisymm (h.trans_eq hσ.symm) (singularValues_nonneg _ _)
    simp only [hz, ← hσ, zero_pow two_ne_zero, sub_self, mul_zero, integral_zero]
    positivity
  let d := q - 1 - r
  have hdq : d + r + 1 = q := by dsimp [d]; omega
  have hd : (d : ℝ) = (q : ℝ) - 1 - r := by
    have h : (d : ℝ) + r + 1 = q := by exact_mod_cast hdq
    linarith
  have ht0 := singularValues_nonneg A t
  have hti : singularValues A t ≤ singularValues A i := singularValues_antitone A hit.le
  obtain ⟨f, hf, c, a, hc, hhead, htail, hac⟩ :=
    Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_mul_pow
      (singularValues_nonneg A t) hti hσ d r
  have hC : 0 < c * (singularValues A i ^ 2) ^ r := by positivity
  have hbound := integral_deficit_le_of_filter hp0 hp A hX hl hit f (by rwa [hdq] at hf)
    hC (by positivity : 0 ≤ a ^ 2 * singularValues A t ^ (4 * r + 2 - p.toReal))
    (Real.rpow_nonneg (singularValues_nonneg A i) (p.toReal - 2))
    (fun j hj => (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _)
      (pow_le_pow_left₀ (singularValues_nonneg _ _)
        (singularValues_antitone A hj) 2) r) hc.le).trans
      (hhead _ (pow_le_pow_left₀ (singularValues_nonneg _ _) (singularValues_antitone A hj) 2)))
    (fun j hj => weighted_power_le (singularValues_nonneg A j) (singularValues_antitone A hj)
      hpr hr (htail _ ⟨sq_nonneg _, pow_le_pow_left₀ (singularValues_nonneg _ _)
        (singularValues_antitone A hj) 2⟩))
  have hscale := weighted_scale_le hσ (singularValues_nonneg A t) hti hc hr
    (a := a)
  have hrate := gap_rate_bound hσ ht0 hθ.le hθ1 hgap
  have he := four_mul_exp_le_four_mul_exp hσ (singularValues_nonneg A t)
    (Nat.cast_nonneg d) hrate
  have hconst : (8 / 3 : ℝ) ≤ 2 * Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hrate' : (a / c) ^ 2 ≤
      4 * Real.exp (-(8 / 3) * ((q : ℝ) - 1 - r) * Real.sqrt θ) := by
    refine (hac.trans he).trans ?_
    rw [hd]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      have hd0 : (0 : ℝ) ≤ q - 1 - r := by rw [← hd]; positivity
      nlinarith [mul_le_mul_of_nonneg_right hconst (mul_nonneg hd0 (Real.sqrt_nonneg θ))]))
      (by norm_num)
  have htl : (t : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hl
  have hnon : 0 ≤ ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
      schattenNorm p (A - truncatedSVD A t) ^ p.toReal := by
    apply mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith))
    positivity
  have hfinal := mul_le_mul_of_nonneg_right (hscale.trans hrate') hnon
  exact hbound.trans (by nlinarith)


/-- A zero spectral tail makes the centered gapless deficit vanish almost surely. -/
private theorem ae_max_deficit_eq_zero_of_singularValues_eq_zero
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k q i : ℕ}
    (hl : k + 2 ≤ Fintype.card l) (hq : 1 ≤ q) (hik : i < k) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hk0 : singularValues A k = 0) :
    (fun ω => max 0 (singularValues A i ^ 2 - γ * singularValues A k ^ 2 -
      singularValues (rbki A (X ω) q) i ^ 2)) =ᵐ[μ] 0 := by
  obtain ⟨Z, hZ, hAZ, hrk, -, -⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix A hX hl
  have hA : truncatedSVD A k = A := truncatedSVD_of_rank_le A
    ((singularValues_eq_zero_iff A).mp hk0)
  filter_upwards [hrk] with ω hω
  have h := hZ.singularValues_sq_sub_le_singularValues_rbki_sq hω hAZ hq hγ hγ1 hik
  rw [hA, sub_self, Matrix.zero_mul, Matrix.zero_mul, specNorm_zero, zero_pow two_ne_zero,
    mul_zero, sub_zero] at h
  exact max_eq_left (by linarith)

/-- **A deficit of one Gaussian block Krylov run without a gap, in expectation, Schatten
form**: let $2 \le p < \infty$, $\mathbf{A}$ a real matrix, $\mathbf{X}$ a standard Gaussian
$n \times \ell$ test matrix (independent standard normal entries), $k + 2 \le \ell$, $r$ with
$p \le 4r + 2$, $q \ge r + 1$, $i < k$ and $0 < \gamma \le 1$. Then
$$\begin{aligned}
&\mathbb{E}\max\Bigl(0, \sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 -
\sigma_i\bigl(\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\bigr)^2\Bigr) \\
&\quad \le 4e^{-2\sqrt{2}(q-1-r)\sqrt{\gamma}}\,\frac{k}{\ell - k - 1}\,
\sigma_k(\mathbf{A})^{2-p}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.
\end{aligned}$$
No gap in the spectrum is assumed. The positive part is what Markov's inequality needs in the
tail bound. [BakshiClarksonWoodruff2022, Lemma 3.1]; there for a Gaussian block of $k$ columns
with probability $99/100$, a uniform bound of the filter on the tail and unspecified constants,
here in expectation, with the weighted filtered residual of [BakshiNarayanan2023, proof of
Lemma 7.6] and the Schatten $p$-norm of the tail. -/
theorem integral_max_singularValues_sq_sub_sub_singularValues_rbki_sq_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k r q i : ℕ} (hl : k + 2 ≤ Fintype.card l)
    (hr : p.toReal ≤ 4 * r + 2) (hq : r + 1 ≤ q) (hik : i < k) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) :
    ∫ ω, max 0 (singularValues A i ^ 2 - γ * singularValues A k ^ 2 -
        singularValues (rbki A (X ω) q) i ^ 2) ∂μ ≤
      4 * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1 - r) * Real.sqrt γ) *
        ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) * singularValues A k ^ (2 - p.toReal) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  classical
  have := hX.isProbabilityMeasure
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp2).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hden : (0 : ℝ) < Fintype.card l - k - 1 := by
    have hkl : (k : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hl
    linarith
  rcases (singularValues_nonneg A k).eq_or_lt with hk0 | hk0
  · have heq := ae_max_deficit_eq_zero_of_singularValues_eq_zero A hX hl
      (show 1 ≤ q by omega) hik hγ hγ1 hk0.symm
    rw [integral_congr_ae heq]
    simp only [Pi.zero_apply, integral_zero]
    have hs0 := singularValues_nonneg A k
    have hO0 := Real.rpow_nonneg (schattenNorm_nonneg p (A - truncatedSVD A k)) p.toReal
    positivity
  have hi0 : 0 < singularValues A i := hk0.trans_le (singularValues_antitone A hik.le)
  let τ := Real.sqrt (singularValues A i ^ 2 - γ * singularValues A k ^ 2)
  have hτ2 : τ ^ 2 = singularValues A i ^ 2 - γ * singularValues A k ^ 2 :=
    Real.sq_sqrt (by
      have hsq := pow_le_pow_left₀ (singularValues_nonneg A k)
        (singularValues_antitone A hik.le) 2
      nlinarith [mul_le_mul_of_nonneg_right hγ1 (sq_nonneg (singularValues A k))])
  have hτ : 0 ≤ τ := Real.sqrt_nonneg _
  have hτi : τ ≤ singularValues A i := by nlinarith
  let d := q - 1 - r
  have hdq : d + r + 1 = q := by dsimp [d]; omega
  have hd : (d : ℝ) = (q : ℝ) - 1 - r := by
    have h : (d : ℝ) + r + 1 = q := by exact_mod_cast hdq
    linarith
  obtain ⟨f, hf, c, a, hc, hhead, htail, hac⟩ :=
    Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_mul_pow
      (le_min hk0.le hτ) ((min_le_right _ _).trans hτi) hi0 d r
  have hC : 0 < c * (singularValues A k ^ 2) ^ r := by positivity
  have htail' (j : ℕ) (hjk : k ≤ j) : singularValues A j ^ 2 *
      (Set.indicator (Set.Iio (τ ^ 2)) (fun x => f.eval x) (singularValues A j ^ 2)) ^ 2 ≤
      (a ^ 2 * singularValues A k ^ (4 * r + 2 - p.toReal)) * singularValues A j ^ p.toReal := by
    by_cases hjτ : singularValues A j ^ 2 < τ ^ 2
    · rw [Set.indicator_of_mem (s := Set.Iio (τ ^ 2)) hjτ]
      have hj : singularValues A j ≤ τ := by nlinarith [singularValues_nonneg A j]
      exact weighted_power_le (singularValues_nonneg A j) (singularValues_antitone A hjk)
        hpr hr (htail _ ⟨sq_nonneg _, pow_le_pow_left₀ (singularValues_nonneg A j)
          (le_min (singularValues_antitone A hjk) hj) 2⟩)
    · rw [Set.indicator_of_notMem (s := Set.Iio (τ ^ 2)) hjτ, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hk0.le _))
        (Real.rpow_nonneg (singularValues_nonneg A j) _)
  have hbound := integral_max_deficit_le_of_filter hp0 hp A hX hl hik f (by rwa [hdq] at hf)
    hC (by positivity : 0 ≤ a ^ 2 * singularValues A k ^ (4 * r + 2 - p.toReal))
    (w := 1) zero_le_one hτ hτi
    (fun j hj => (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _)
      (pow_le_pow_left₀ hk0.le ((singularValues_antitone A hik.le).trans
        (singularValues_antitone A hj)) 2) r) hc.le).trans
      (hhead _ (pow_le_pow_left₀ hi0.le (singularValues_antitone A hj) 2))) htail'
  have he := four_mul_exp_le_four_mul_exp hi0 (le_min hk0.le hτ) (Nat.cast_nonneg d)
    (cut_rate_bound hi0 hk0.le (singularValues_antitone A hik.le) hτ hτ2 hγ hγ1)
  have hscale := weighted_unscaled_eq hk0 hc (a := a) (P := p.toReal) (r := r)
  have hnon : 0 ≤ ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
      singularValues A k ^ (2 - p.toReal) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
    exact mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hden.le)
      (Real.rpow_nonneg hk0.le _)) (Real.rpow_nonneg (schattenNorm_nonneg _ _) _)
  have hfinal := mul_le_mul_of_nonneg_right (hac.trans he) hnon
  rw [hd] at hfinal
  simp only [one_mul, hτ2] at hbound
  have hmul : (c * (singularValues A k ^ 2) ^ r)⁻¹ ^ 2 *
      ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
      (a ^ 2 * singularValues A k ^ (4 * r + 2 - p.toReal)) *
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal =
      (a / c) ^ 2 * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
        singularValues A k ^ (2 - p.toReal) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
    calc _ = ((c * (singularValues A k ^ 2) ^ r)⁻¹ ^ 2 *
          (a ^ 2 * singularValues A k ^ (4 * r + 2 - p.toReal))) *
          (((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
            schattenNorm p (A - truncatedSVD A k) ^ p.toReal) := by ring
      _ = _ := by rw [hscale]; ring
  rw [hmul] at hbound
  exact hbound.trans (by nlinarith)


end Gaussian

end NLAlib
