/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import NLAlib.RandomMatrix.Shattering.GinibreClass

/-!
# The parameters of the small-eigenvalue solver

The parameters of [BanksGarzaVargasSrivastava2025, Theorem 1.1] as closed forms of the order bound
$n_{\max}$, the norm bound $\Sigma$ (`S`), the backward error $\delta$, the failure probability
$\varphi$ and the two tail records of the random-matrix hypotheses: the perturbation scale
$\gamma$, the class it produces (separation $t_1$, condition $t_2^{-1}$, from the inverted tails,
`NLAlib.SmallEig.ginibreClass_spec`), the coupling threshold $\omega$ of the decoupler and the
accuracy $\beta' = \omega/20$ of `OneEig`, the radii $\eta_1, \eta_2$ of the regularized net, the
degree $m = 2^q$ of `DistSpec`, the round cap $t$ of `OneEig` and the step cap $m_2$ of
`Decouple`, and the scan thresholds. The words are fixed at the outer bound $n_{\max}$ and serve
every order $d \le n_{\max}$: the program computes the scale $\gamma/\sqrt d$ itself. Logarithms
are in base $2$ (the paper's erratum P7); the corrections of the paper's choices of $t$ (P6) and
$\eta_2$ (P5) are in `NLAlib.SmallEig.oneEigRounds_spec` and `NLAlib.SmallEig.oneEigRadii_spec`.

## Main definitions

* `NLAlib.SmallEig.distSpecDegree`, `NLAlib.SmallEig.oneEigRounds`,
  `NLAlib.SmallEig.oneEigOuterRadius`, `NLAlib.SmallEig.oneEigInnerRadius`: the choices of
  `DistSpec` and `OneEig`.
* `NLAlib.SmallEig.ginibreGapThreshold`, `NLAlib.SmallEig.ginibreConditionThreshold`: the class
  of the perturbation.
* `NLAlib.SmallEig.smallEigParams`, `NLAlib.SmallEig.smallEigCap`, `NLAlib.SmallEig.SmallEigCaps`:
  the twelve parameter words, the cap dimension and the validity of the cap words.

## Main results

* `NLAlib.SmallEig.distSpecDegree_spec`, `NLAlib.SmallEig.oneEigRounds_spec`,
  `NLAlib.SmallEig.oneEigRadii_spec`, `NLAlib.SmallEig.ginibreClass_spec`: the scalar facts.
* `NLAlib.SmallEig.length_smallEigParams`, `NLAlib.SmallEig.smallEigParams_spec`,
  `NLAlib.SmallEig.smallEigParams_pos`, `NLAlib.SmallEig.smallEigCaps_smallEigParams`: the words.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Real

/-! ### The choices of `DistSpec` and `OneEig` -/

/-- The degree $m_1 = \lceil 12\log_2\kappa + 6\log_2(1/p)\rceil$ of `DistSpec` for the condition
$\kappa$ and the weight $p$ ([BanksGarzaVargasSrivastava2025, Proposition 3.5], line 1 of
`OneEig`, with $\log = \log_2$). -/
noncomputable def distSpecDegree (κ p : ℝ) : ℕ := ⌈12 * logb 2 κ + 6 * logb 2 p⁻¹⌉₊

/-- $2^{1/12} \le 1.09$: the factor by which a degree $m \ge 12\log_2 x$ lets $x^{1/m}$ exceed
$1$. -/
private theorem two_rpow_inv_twelve_le : (2 : ℝ) ^ ((12 : ℝ)⁻¹) ≤ 1.09 := by
  have h : (2 : ℝ) ≤ 1.09 ^ (12 : ℕ) := by norm_num
  calc (2 : ℝ) ^ ((12 : ℝ)⁻¹) ≤ ((1.09 : ℝ) ^ (12 : ℕ)) ^ ((12 : ℝ)⁻¹) := by gcongr
    _ = 1.09 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- **The degree of `DistSpec` is large enough** ([BanksGarzaVargasSrivastava2025,
Observation 3.3], "$m$ is large enough", with $\log = \log_2$): for $\kappa \ge 1$,
$0 < p \le 1$ and $m \ge 1$ at least `NLAlib.SmallEig.distSpecDegree` $\kappa$ $p$,
$$0.9 \le 0.998\,\kappa^{-1/m} \quad\text{and}\quad 1.003\,\kappa^{1/m}p^{-1/(2m)} \le 1.1\,,$$
the two factors by which the estimate of `DistSpec` may miss the distance to the spectrum. -/
theorem distSpecDegree_spec {κ p : ℝ} (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) {m : ℕ}
    (hm0 : 0 < m) (hm : distSpecDegree κ p ≤ m) :
    0.9 ≤ 0.998 * κ ^ (-(m : ℝ)⁻¹) ∧ 1.003 * κ ^ ((m : ℝ)⁻¹) * p ^ (-(2 * (m : ℝ))⁻¹) ≤ 1.1 := by
  have hm' : 12 * logb 2 κ + 6 * logb 2 p⁻¹ ≤ m := Nat.ceil_le.mp hm
  have hmR : (0:ℝ) < m := by exact_mod_cast hm0
  have ha : 0 ≤ logb 2 κ := logb_nonneg (by norm_num) hκ
  have hb : 0 ≤ logb 2 p⁻¹ := logb_nonneg (by norm_num) (one_le_inv₀ hp |>.mpr hp1)
  have hκ0 : 0 < κ := by linarith
  have key : κ ^ ((m : ℝ)⁻¹) * p ^ (-(2 * (m : ℝ))⁻¹) ≤ 2 ^ ((12:ℝ)⁻¹) := by
    have e1 : κ = 2 ^ logb 2 κ := (rpow_logb (by norm_num) (by norm_num) hκ0).symm
    have e2 : p = 2 ^ (-logb 2 p⁻¹) := by
      rw [logb_inv, neg_neg, rpow_logb (by norm_num) (by norm_num) hp]
    rw [e1, e2, ← rpow_mul (by norm_num), ← rpow_mul (by norm_num), ← rpow_add (by norm_num)]
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    rw [← sub_nonneg]
    have : (12:ℝ)⁻¹ - (logb 2 κ * (m:ℝ)⁻¹ + -logb 2 p⁻¹ * -(2 * (m:ℝ))⁻¹) =
        (m - (12 * logb 2 κ + 6 * logb 2 p⁻¹)) / (12 * m) := by field_simp; ring
    rw [this]; apply div_nonneg <;> linarith
  have h2 := two_rpow_inv_twelve_le
  have hpos1 : 0 < κ ^ ((m : ℝ)⁻¹) := rpow_pos_of_pos hκ0 _
  have hκ1 : 1 ≤ κ ^ ((m : ℝ)⁻¹) := one_le_rpow hκ (by positivity)
  have hp2 : 1 ≤ p ^ (-(2 * (m : ℝ))⁻¹) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos hp hp1 (by rw [neg_nonpos]; positivity)
  constructor
  · rw [rpow_neg hκ0.le]
    have : κ ^ ((m : ℝ)⁻¹) ≤ 1.09 := by nlinarith
    rw [← div_eq_mul_inv, le_div_iff₀ hpos1]; nlinarith
  · nlinarith

/-- The round cap $t = \lceil 2\log_2(5.2\,\Sigma/\beta)\rceil$ of `OneEig` (the paper's
$\lceil 2\log(\Sigma/(5\beta))\rceil$ corrected, its erratum P6). -/
noncomputable def oneEigRounds (S β : ℝ) : ℕ := ⌈2 * logb 2 (5.2 * S / β)⌉₊

/-- The contraction of the round cap: for $0 < \beta \le \Sigma$ and $t$ =
`NLAlib.SmallEig.oneEigRounds` $\Sigma$ $\beta$, $0.66^t \le \beta/(5.2\,\Sigma)$. -/
theorem pow_oneEigRounds_le {S β : ℝ} (hβ : 0 < β) (hβS : β ≤ S) :
    (0.66 : ℝ) ^ oneEigRounds S β ≤ β / (5.2 * S) := by
  set y := logb 2 (5.2 * S / β) with hy
  have hr : 1 ≤ 5.2 * S / β := by rw [le_div_iff₀ hβ]; linarith
  have hy0 : 0 ≤ y := logb_nonneg (by norm_num) hr
  have ht : 2 * y ≤ oneEigRounds S β := Nat.le_ceil _
  have h1 : (0.66:ℝ) ^ oneEigRounds S β ≤ (0.66:ℝ) ^ (2 * y) := by
    rw [← rpow_natCast]; exact rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht
  refine h1.trans ?_
  rw [rpow_mul (by norm_num)]
  calc ((0.66:ℝ) ^ (2:ℝ)) ^ y ≤ (2⁻¹ : ℝ) ^ y := by
        gcongr; rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, rpow_natCast]; norm_num
    _ = β / (5.2 * S) := by
        rw [inv_rpow (by norm_num), hy, rpow_logb (by norm_num) (by norm_num) (by linarith)]
        field_simp

/-- **The round cap of `OneEig` suffices** ([BanksGarzaVargasSrivastava2025, Proposition 3.5],
the choice of $t$ corrected): for $0 < \beta \le \Sigma$ and $t$ =
`NLAlib.SmallEig.oneEigRounds` $\Sigma$ $\beta$,
$$\frac{4.6 \cdot 0.66^t}{0.9} \le \frac{\beta}{\Sigma} \quad\text{and}\quad
  6t + 1 \le 12\log_2\frac{7.8\,\Sigma}{\beta}\,.$$
The paper's $t$ fails the first for $\Sigma/\beta < 6 \cdot 10^7$. -/
theorem oneEigRounds_spec {S β : ℝ} (hβ : 0 < β) (hβS : β ≤ S) :
    4.6 * 0.66 ^ oneEigRounds S β / 0.9 ≤ β / S ∧
      6 * (oneEigRounds S β : ℝ) + 1 ≤ 12 * logb 2 (7.8 * S / β) := by
  have hS : 0 < S := hβ.trans_le hβS
  set y := logb 2 (5.2 * S / β) with hy
  have hr : 1 ≤ 5.2 * S / β := by rw [le_div_iff₀ hβ]; linarith
  have hy0 : 0 ≤ y := logb_nonneg (by norm_num) hr
  have ht' : (oneEigRounds S β : ℝ) < 2 * y + 1 := Nat.ceil_lt_add_one (by positivity)
  constructor
  · have h2 := pow_oneEigRounds_le hβ hβS
    have h3 : β / (5.2 * S) * 5.2 = β / S := by field_simp
    have : 0 ≤ (0.66:ℝ) ^ oneEigRounds S β := by positivity
    rw [div_le_iff₀ (by norm_num)]
    nlinarith [div_pos hβ hS]
  · have e : logb 2 (7.8 * S / β) = y + logb 2 1.5 := by
      rw [hy, ← logb_mul (by positivity) (by norm_num)]; congr 1; ring
    have h15 : 7 ≤ 12 * logb 2 1.5 := by
      rw [← logb_rpow_eq_mul_logb_of_pos (by norm_num),
        le_logb_iff_rpow_le (by norm_num) (by positivity)]
      rw [show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, rpow_natCast,
        show (7:ℝ) = ((7:ℕ):ℝ) by norm_num, rpow_natCast]; norm_num
    rw [e]; linarith

/-- The radius $\eta_2 = \min(\beta/40, g/3)$ of the disk samples of `OneEig` (the paper's
$\beta/5$ corrected, its erratum P5). -/
noncomputable def oneEigOuterRadius (β g : ℝ) : ℝ := min (β / 40) (g / 3)

/-- The radius $\eta_1 = \eta_2\sqrt{\varphi/(12\log_2(8\Sigma/\beta))}$ that the accepted point of
`OneEig` keeps from the spectrum. -/
noncomputable def oneEigInnerRadius (S β g φ : ℝ) : ℝ :=
  oneEigOuterRadius β g * √(φ / (12 * logb 2 (8 * S / β)))

/-- **The radii of `OneEig`** ([BanksGarzaVargasSrivastava2025, Observation 3.4], with
$\eta_2 = \min(\beta/40, g/3)$, its errata P5 and N6): for $0 < \beta \le 0.8\,\Sigma$, $g > 0$
and $0 < \varphi \le 1$, with $\eta_1, \eta_2$ = `NLAlib.SmallEig.oneEigInnerRadius`,
`NLAlib.SmallEig.oneEigOuterRadius` and $t$ = `NLAlib.SmallEig.oneEigRounds` $\Sigma$ $\beta$:
$\eta_1 > 0$, $\eta_1 + \eta_2 \le g/2$, $\eta_2 \le 0.02\,\Sigma$ and
$(6t + 1)(\eta_1/\eta_2)^2 \le \varphi$. -/
theorem oneEigRadii_spec {S β g φ : ℝ} (hβ : 0 < β) (hβS : β ≤ 0.8 * S) (hg : 0 < g)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < oneEigInnerRadius S β g φ ∧ oneEigInnerRadius S β g φ + oneEigOuterRadius β g ≤ g / 2 ∧
      oneEigOuterRadius β g ≤ 0.02 * S ∧
      (6 * (oneEigRounds S β : ℝ) + 1) * (oneEigInnerRadius S β g φ / oneEigOuterRadius β g) ^ 2
        ≤ φ := by
  have hS : 0 < S := by linarith
  have h2 : 0 < oneEigOuterRadius β g := lt_min (by positivity) (by positivity)
  have h2g : oneEigOuterRadius β g ≤ g / 3 := min_le_right _ _
  have h2β : oneEigOuterRadius β g ≤ β / 40 := min_le_left _ _
  set L := logb 2 (8 * S / β) with hL
  have hL3 : 3 ≤ L := by
    rw [hL, le_logb_iff_rpow_le (by norm_num) (by positivity), le_div_iff₀ hβ,
      show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, rpow_natCast]; linarith
  have hq : φ / (12 * L) ≤ 1 / 36 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsq : √(φ / (12 * L)) ≤ 1 / 6 := by
    rw [sqrt_le_left (by norm_num)]; linarith
  have hsq0 : 0 < √(φ / (12 * L)) := sqrt_pos.mpr (by positivity)
  have hr := (oneEigRounds_spec (S := S) hβ (by linarith)).2
  have hlog : logb 2 (7.8 * S / β) ≤ L :=
    logb_le_logb_of_le (by norm_num) (by positivity) (by gcongr; norm_num)
  refine ⟨mul_pos h2 hsq0, ?_, by linarith, ?_⟩
  · unfold oneEigInnerRadius; nlinarith
  · unfold oneEigInnerRadius
    rw [mul_div_cancel_left₀ _ h2.ne', sq_sqrt (by positivity), ← mul_div_assoc,
      div_le_iff₀ (by positivity)]
    nlinarith

/-- $\log_2(40/39) \ge 1/30$. -/
private theorem one_div_thirty_le_logb : (1 : ℝ) / 30 ≤ logb 2 (40 / 39) := by
  rw [le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  have h : (2 : ℝ) ≤ (40 / 39) ^ (30 : ℕ) := by norm_num
  calc (2 : ℝ) ^ ((1 : ℝ) / 30) ≤ ((40 / 39 : ℝ) ^ (30 : ℕ)) ^ ((1 : ℝ) / 30) := by gcongr
    _ = 40 / 39 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- **The radii of `OneEig` leave room for rounding** ([BanksGarzaVargasSrivastava2025,
Observation 3.4], with $\eta_2 = \min(\beta/40, g/3)$): for $0 < \beta \le 0.8\,\Sigma$, $g > 0$,
$\varphi > 0$ and $0 \le \varepsilon$ with
$100\,\varepsilon\log_2(8\Sigma/\beta) \le \eta_1$, where $\eta_1, \eta_2$ =
`NLAlib.SmallEig.oneEigInnerRadius`, `NLAlib.SmallEig.oneEigOuterRadius` and $t$ =
`NLAlib.SmallEig.oneEigRounds` $\Sigma$ $\beta$: $(6t + 1)((\eta_1 + \varepsilon)/\eta_2)^2 \le
\varphi$. -/
theorem oneEigRadii_add_sq_le {S β g φ ε : ℝ} (hβ : 0 < β) (hβS : β ≤ 0.8 * S) (hg : 0 < g)
    (hφ : 0 < φ) (hε : 0 ≤ ε)
    (hεL : 100 * ε * logb 2 (8 * S / β) ≤ oneEigInnerRadius S β g φ) :
    (6 * (oneEigRounds S β : ℝ) + 1) *
      ((oneEigInnerRadius S β g φ + ε) / oneEigOuterRadius β g) ^ 2 ≤ φ := by
  have hS : 0 < S := by linarith
  have h2 : 0 < oneEigOuterRadius β g := lt_min (by positivity) (by positivity)
  set η₂ := oneEigOuterRadius β g
  set L := logb 2 (8 * S / β) with hL
  have hL3 : 3 ≤ L := by
    rw [hL, le_logb_iff_rpow_le (by norm_num) (by positivity), le_div_iff₀ hβ,
      show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, rpow_natCast]; linarith
  have hr := (oneEigRounds_spec (S := S) hβ (by linarith)).2
  have e : L = logb 2 (7.8 * S / β) + logb 2 (40 / 39) := by
    rw [hL, ← logb_mul (by positivity) (by norm_num)]; congr 1; field_simp; norm_num
  have hlog := one_div_thirty_le_logb
  have ht : 6 * (oneEigRounds S β : ℝ) + 1 ≤ 12 * L - 0.4 := by linarith
  set η₁ := oneEigInnerRadius S β g φ with hη₁
  have hq0 : 0 ≤ φ / (12 * L) := by positivity
  have hsq : η₁ ^ 2 * (12 * L) = φ * η₂ ^ 2 := by
    rw [hη₁, oneEigInnerRadius, mul_pow, sq_sqrt hq0]; field_simp; rfl
  have hη₁0 : 0 ≤ η₁ := mul_nonneg h2.le (sqrt_nonneg _)
  have hεη : ε ≤ η₁ := by nlinarith
  have hA : 0 ≤ 6 * (oneEigRounds S β : ℝ) + 1 := by positivity
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have hb : (η₁ + ε) ^ 2 ≤ η₁ ^ 2 + 3 * η₁ * ε := by nlinarith
  have hc : 36 * L * η₁ * ε ≤ 0.36 * η₁ ^ 2 := by nlinarith
  calc (6 * (oneEigRounds S β : ℝ) + 1) * (η₁ + ε) ^ 2
      ≤ (12 * L - 0.4) * (η₁ ^ 2 + 3 * η₁ * ε) := by
        apply mul_le_mul ht hb (by positivity) (by linarith)
    _ ≤ η₁ ^ 2 * (12 * L) := by nlinarith
    _ = φ * η₂ ^ 2 := hsq

/-- The inner radius of `OneEig` is at most a sixth of the outer one: for
$0 < \beta \le 0.8\,\Sigma$, $g > 0$ and $\varphi \le 1$,
`NLAlib.SmallEig.oneEigInnerRadius` $\Sigma$ $\beta$ $g$ $\varphi$ is at most
`NLAlib.SmallEig.oneEigOuterRadius` $\beta$ $g$ divided by $6$. -/
theorem oneEigInnerRadius_le {S β g φ : ℝ} (hβ : 0 < β) (hβS : β ≤ 0.8 * S) (hg : 0 < g)
    (hφ1 : φ ≤ 1) : oneEigInnerRadius S β g φ ≤ oneEigOuterRadius β g / 6 := by
  have hS : 0 < S := by linarith
  have h2 : 0 < oneEigOuterRadius β g := lt_min (by positivity) (by positivity)
  have hL3 : 3 ≤ Real.logb 2 (8 * S / β) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), le_div_iff₀ hβ,
      show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; linarith
  have hq : φ / (12 * Real.logb 2 (8 * S / β)) ≤ 1 / 36 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsq : √(φ / (12 * Real.logb 2 (8 * S / β))) ≤ 1 / 6 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  unfold oneEigInnerRadius
  nlinarith

/-- $\log_2 y \le 2y$ for $y > 0$. -/
theorem logb_two_le_two_mul {y : ℝ} (hy : 0 < y) : Real.logb 2 y ≤ 2 * y := by
  have h2 := Real.log_two_gt_d9
  have hl := Real.log_le_sub_one_of_pos hy
  rw [Real.logb, div_le_iff₀ (by linarith)]
  rcases le_or_gt 0 (Real.log y) with h | h <;> nlinarith

/-- The degree of `DistSpec` is at least $2$ when the weight bound is at most $1/2$: for
$\kappa \ge 1$, $0 < p \le 1/2$ and $m$ at least `NLAlib.SmallEig.distSpecDegree` $\kappa$ $p$,
$m \ge 2$. -/
theorem two_le_of_distSpecDegree_le {κ p : ℝ} {m : ℕ} (hκ : 1 ≤ κ) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (hm : distSpecDegree κ p ≤ m) : 2 ≤ m := by
  have h1 : 0 ≤ Real.logb 2 κ := Real.logb_nonneg (by norm_num) hκ
  have h2 : 1 ≤ Real.logb 2 p⁻¹ := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one,
      le_inv_comm₀ (by norm_num) hp]
    linarith
  have h4 : (2 : ℝ) ≤ (distSpecDegree κ p : ℝ) := by
    unfold distSpecDegree; exact (by linarith : (2 : ℝ) ≤ _).trans (Nat.le_ceil _)
  have : 2 ≤ distSpecDegree κ p := by exact_mod_cast h4
  omega

/-- The step cap $m_2 = \lceil\log_2(\kappa/\sqrt p)\rceil + 1$ of `Decouple` for the condition
$\kappa$ and the weight $p$: $\kappa \le 2^{m_2}\sqrt p$. -/
noncomputable def decoupleSteps (κ p : ℝ) : ℕ := ⌈logb 2 (κ / √p)⌉₊ + 1

/-! ### The class of the perturbation -/

/-- The separation $t_1 = \gamma\tau_1$ of the eigenvalues of a Ginibre perturbation of scale
$\gamma$ of a matrix of norm at most $\Sigma$ and order at most $n_{\max}$, at the failure
probability $\varphi$, for the gap tail $c_1$: $\tau_1$ inverts the normalized tail at the norm
ratio $K = (\Sigma + 4\gamma)/\gamma$ (`NLAlib.polyLogTailInverse`). -/
noncomputable def ginibreGapThreshold (nmax : ℕ) (S γ φ : ℝ) (c₁ : PolyLogTail) : ℝ :=
  γ * polyLogTailInverse c₁.normalize nmax ((S + 4 * γ) / γ) φ

/-- The condition bound $t_2^{-1}$ of the eigenvectors of a Ginibre perturbation, as
`NLAlib.SmallEig.ginibreGapThreshold`, for the condition tail $c_2$. -/
noncomputable def ginibreConditionThreshold (nmax : ℕ) (S γ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  polyLogTailInverse c₂.normalize nmax ((S + 4 * γ) / γ) φ

/-- **The inverted tails** ([BanksGarzaVargasSrivastava2025, Lemma 6.5], replaced by the class):
for tail records with $b_1, b_2 > 0$, $n_{\max} \ge 1$, $\Sigma \ge 0$, $\gamma > 0$ and
$0 < \varphi \le 1$, with $K = (\Sigma + 4\gamma)/\gamma$ and $t_1, t_2$ =
`NLAlib.SmallEig.ginibreGapThreshold`, `NLAlib.SmallEig.ginibreConditionThreshold`: $0 < t_1 \le
\gamma$, $0 < t_2 \le 1$, at every order $1 \le N \le n_{\max}$ the two normalized tails
$$\bar C_1 N^{\bar a_1}(t_1/\gamma)^{\bar b_1}(K + \log(\gamma/t_1))^{\bar c_1}, \qquad
  \bar C_2 N^{\bar a_2}t_2^{\bar b_2}(K + \log(1/t_2))^{\bar c_2}$$
are at most $\varphi$, and $\log_2(\gamma/t_1)$, $\log_2(1/t_2)$ are at most $2/b_i$ times
$\log_2(s_i/\varphi)$, $s_i$ the scale `NLAlib.polyLogTailScale` of the normalized record at
$n_{\max}$ and $K$. -/
theorem ginibreClass_spec {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S γ φ : ℝ} (hS : 0 ≤ S) (hγ : 0 < γ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < ginibreGapThreshold nmax S γ φ c₁ ∧ ginibreGapThreshold nmax S γ φ c₁ ≤ γ ∧
      0 < ginibreConditionThreshold nmax S γ φ c₂ ∧ ginibreConditionThreshold nmax S γ φ c₂ ≤ 1 ∧
      (∀ N : ℕ, 1 ≤ N → N ≤ nmax →
        c₁.normalize.C * (N : ℝ) ^ c₁.normalize.a *
            (ginibreGapThreshold nmax S γ φ c₁ / γ) ^ c₁.normalize.b *
            ((S + 4 * γ) / γ + log (γ / ginibreGapThreshold nmax S γ φ c₁)) ^ c₁.normalize.c ≤ φ ∧
        c₂.normalize.C * (N : ℝ) ^ c₂.normalize.a *
            ginibreConditionThreshold nmax S γ φ c₂ ^ c₂.normalize.b *
            ((S + 4 * γ) / γ + log (ginibreConditionThreshold nmax S γ φ c₂)⁻¹) ^ c₂.normalize.c
          ≤ φ) ∧
      logb 2 (γ / ginibreGapThreshold nmax S γ φ c₁) ≤
        2 / c₁.b * logb 2 (polyLogTailScale c₁.normalize nmax ((S + 4 * γ) / γ) / φ) ∧
      logb 2 (ginibreConditionThreshold nmax S γ φ c₂)⁻¹ ≤
        2 / c₂.b * logb 2 (polyLogTailScale c₂.normalize nmax ((S + 4 * γ) / γ) / φ) := by
  have hK : 0 ≤ (S + 4 * γ) / γ := div_nonneg (by linarith) hγ.le
  have hN : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
  obtain ⟨h1p, h1le, h1t, h1l⟩ := polyLogTailInverse_spec (c := c₁) hb₁ hN hK hφ hφ1
  obtain ⟨h2p, h2le, h2t, h2l⟩ := polyLogTailInverse_spec (c := c₂) hb₂ hN hK hφ hφ1
  have e1 : ginibreGapThreshold nmax S γ φ c₁ / γ =
      polyLogTailInverse c₁.normalize nmax ((S + 4 * γ) / γ) φ := by
    rw [ginibreGapThreshold, mul_div_cancel_left₀ _ hγ.ne']
  have e2 : γ / ginibreGapThreshold nmax S γ φ c₁ =
      (polyLogTailInverse c₁.normalize nmax ((S + 4 * γ) / γ) φ)⁻¹ := by
    rw [ginibreGapThreshold, div_mul_cancel_left₀ hγ.ne']
  refine ⟨mul_pos hγ h1p, ?_, h2p, h2le, fun N hN1 hNn => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [ginibreGapThreshold]
    nlinarith
  · rw [e1, e2]
    exact h1t N (by exact_mod_cast hN1) (by exact_mod_cast hNn)
  · exact h2t N (by exact_mod_cast hN1) (by exact_mod_cast hNn)
  · rw [e2, logb, logb, h1l, mul_div_assoc]
  · rw [logb, logb, ginibreConditionThreshold, h2l, mul_div_assoc]

/-! ### The parameter words -/

/-- The noise level $W = 3 + \sqrt{\log(4/\varphi)}$: the norm of $\gamma n^{-1/2}\mathbf{G}$ is
at most $\gamma W$ except with probability $\varphi/4$, at every order. -/
noncomputable def smallEigNoiseLevel (φ : ℝ) : ℝ := 3 + √(log (4 / φ))

/-- The perturbation scale $\gamma = \delta/(4W)$, $W$ = `NLAlib.SmallEig.smallEigNoiseLevel`. -/
noncomputable def smallEigScale (δ φ : ℝ) : ℝ := δ / (4 * smallEigNoiseLevel φ)

/-- The separation $t_1$ of the perturbed matrix: the gap threshold at the scale $\gamma/2$ and the
failure $\varphi/(4 \cdot 2^{\bar c_1})$, so that the tail at any scale in
$[\gamma/2, 2\gamma]$ (the rounded scale of the program) is at most $\varphi/4$. -/
noncomputable def smallEigGap (nmax : ℕ) (S δ φ : ℝ) (c₁ : PolyLogTail) : ℝ :=
  ginibreGapThreshold nmax S (smallEigScale δ φ / 2) (φ / (4 * 2 ^ c₁.normalize.c)) c₁

/-- The condition parameter $t_2$ of the perturbed matrix: the condition threshold at the scale
$\gamma/2$ and the failure $\varphi/4$. -/
noncomputable def smallEigCond (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  ginibreConditionThreshold nmax S (smallEigScale δ φ / 2) (φ / 4) c₂

/-- The condition bound $B_c = 4/t_2$ of the matrix the core receives (one doubling for the
rounding of the perturbation, one for the reduction). -/
noncomputable def smallEigCondition (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  4 / smallEigCond nmax S δ φ c₂

/-- The separation $g_c = t_1/4$ of the matrix the core receives. -/
noncomputable def smallEigSeparation (nmax : ℕ) (S δ φ : ℝ) (c₁ : PolyLogTail) : ℝ :=
  smallEigGap nmax S δ φ c₁ / 4

/-- The coupling threshold
$\omega = \min(\delta/4, g_c/(16n_{\max}B_c))/(12n_{\max})$ of the decoupler. -/
noncomputable def smallEigOmega (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (δ / 4) (smallEigSeparation nmax S δ φ c₁ / (16 * nmax * smallEigCondition nmax S δ φ c₂)) /
    (12 * nmax)

/-- The accuracy $\beta' = \omega/20$ of `OneEig`. -/
noncomputable def smallEigAccuracy (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  smallEigOmega nmax S δ φ c₁ c₂ / 20

/-- The failure $\varphi_D = \varphi/(16n_{\max})$ allowed to one decoupler call; half of it to
`RHess`, half to `OneEig`. -/
noncomputable def smallEigDecouplerFailure (nmax : ℕ) (φ : ℝ) : ℝ := φ / (16 * nmax)

/-- The norm bound $R = \sqrt2\,(3\sqrt{n_{\max}} + \sqrt{2\log(4/\varphi_D)})$ of the window of
$2N$ standard real Gaussian draws of `RHess` (its direction before normalization), the radius that
`NLAlib.SmallEig.rhess_pwrites` takes at the failure $\varphi_D/4$. -/
noncomputable def smallEigVectorRadius (nmax : ℕ) (φ : ℝ) : ℝ :=
  √2 * (3 * √nmax + √(2 * log (4 / smallEigDecouplerFailure nmax φ)))

/-- The lower bound $p = s^2/(64R^2(2B_c)^2)$, $s^2 = \varphi_D/(8n_{\max})$, of the last-row
weights after `RHess` at the condition $2B_c$ and the radius $R$ =
`NLAlib.SmallEig.smallEigVectorRadius`: the weight bound of `NLAlib.SmallEig.rhess_pwrites`. -/
noncomputable def smallEigWeight (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  smallEigDecouplerFailure nmax φ / (8 * nmax) /
    (64 * smallEigVectorRadius nmax φ ^ 2 * (2 * smallEigCondition nmax S δ φ c₂) ^ 2)

/-- The exponent $q$ of the degree $m = 2^q$ of `DistSpec`:
$q = \lceil\log_2 m_1\rceil$ for $m_1$ = `NLAlib.SmallEig.distSpecDegree` at the condition
$8B_c$ and the weight $p$. -/
noncomputable def smallEigDegreeLog (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℕ :=
  Nat.clog 2 (distSpecDegree (8 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂))

/-- The round cap $t$ of `OneEig` at the block norm $2\Sigma$ and the accuracy $\beta'$. -/
noncomputable def smallEigRounds (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  oneEigRounds (2 * S) (smallEigAccuracy nmax S δ φ c₁ c₂)

/-- The step cap $m_2$ of `Decouple` at the condition $8B_c$ and the weight $p$. -/
noncomputable def smallEigDecoupleSteps (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℕ :=
  decoupleSteps (8 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂)

/-- The radius $\eta_2$ of the disk samples of `OneEig`, at the separation $g_c/4$ inside the
decoupler. -/
noncomputable def smallEigOuterRadius (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  oneEigOuterRadius (smallEigAccuracy nmax S δ φ c₁ c₂) (smallEigSeparation nmax S δ φ c₁ / 4)

/-- The radius $\eta_1$ of `OneEig`, at the failure $\varphi_D/2$. -/
noncomputable def smallEigInnerRadius (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  oneEigInnerRadius (2 * S) (smallEigAccuracy nmax S δ φ c₁ c₂)
    (smallEigSeparation nmax S δ φ c₁ / 4) (smallEigDecouplerFailure nmax φ / 2)

/-- **The twelve parameter words of the small-eigenvalue program**
([BanksGarzaVargasSrivastava2025, Theorem 1.1]): in this order, the scale $\gamma$, the coupling
threshold $\omega$, the accuracy $\beta' = \omega/20$, the radii $\eta_1$ and $\eta_2$ of
`OneEig`, its exit threshold $0.9\beta'$, the worklist's scan threshold $2(1.5\,\omega)^2$, the
scan threshold $t_L = 2\omega^2$ of `Decouple`, and the cap words $m = 2^q$, $q$, $t$, $m_2$. The
program reads them at these offsets. -/
noncomputable def smallEigParams (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℝ :=
  [smallEigScale δ φ, smallEigOmega nmax S δ φ c₁ c₂, smallEigAccuracy nmax S δ φ c₁ c₂,
    smallEigInnerRadius nmax S δ φ c₁ c₂, smallEigOuterRadius nmax S δ φ c₁ c₂,
    0.9 * smallEigAccuracy nmax S δ φ c₁ c₂, 2 * (1.5 * smallEigOmega nmax S δ φ c₁ c₂) ^ 2,
    2 * smallEigOmega nmax S δ φ c₁ c₂ ^ 2, ((2 ^ smallEigDegreeLog nmax S δ φ c₂ : ℕ) : ℝ),
    (smallEigDegreeLog nmax S δ φ c₂ : ℝ), (smallEigRounds nmax S δ φ c₁ c₂ : ℝ),
    (smallEigDecoupleSteps nmax S δ φ c₂ : ℝ)]

/-- The cap dimension $T = \max(m, t, m_2)$ of the program. -/
noncomputable def smallEigCap (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  max (2 ^ smallEigDegreeLog nmax S δ φ c₂)
    (max (smallEigRounds nmax S δ φ c₁ c₂) (smallEigDecoupleSteps nmax S δ φ c₂))

/-- **Valid cap words** for the cap dimension $T$: the words $8$ to $11$ of `qs` are exact
naturals $m, q, t, m_2$ with $m = 2^q$ and $m, t, m_2 \le T$. The program reads them with bounded
index reads, which fail on a negative or too large word. -/
def SmallEigCaps (T : ℕ) (qs : List ℝ) : Prop :=
  ∃ m q t m₂ : ℕ, qs.getD 8 0 = m ∧ qs.getD 9 0 = q ∧ qs.getD 10 0 = t ∧ qs.getD 11 0 = m₂ ∧
    m = 2 ^ q ∧ m ≤ T ∧ t ≤ T ∧ m₂ ≤ T

/-- The program has twelve parameter words. -/
theorem length_smallEigParams (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) :
    (smallEigParams nmax S δ φ c₁ c₂).length = 12 := by
  simp [smallEigParams]

/-- The noise level is positive. -/
theorem smallEigNoiseLevel_pos (φ : ℝ) : 0 < smallEigNoiseLevel φ := by
  unfold smallEigNoiseLevel; positivity

/-- The perturbation scale $\gamma$ is positive for $\delta > 0$. -/
theorem smallEigScale_pos {δ φ : ℝ} (hδ : 0 < δ) : 0 < smallEigScale δ φ := by
  have := smallEigNoiseLevel_pos φ
  unfold smallEigScale; positivity

/-- The noise budget: $\gamma W = \delta/4$. -/
theorem smallEigScale_mul_noiseLevel (δ φ : ℝ) :
    smallEigScale δ φ * smallEigNoiseLevel φ = δ / 4 := by
  have := (smallEigNoiseLevel_pos φ).ne'
  unfold smallEigScale; field_simp

/-- The separation $t_1$ is in $(0, \gamma/2]$ (`NLAlib.SmallEig.ginibreClass_spec` at the scale
$\gamma/2$). -/
theorem smallEigGap_pos_le {c₁ : PolyLogTail} (hb₁ : 0 < c₁.b) {nmax : ℕ} (hn : 1 ≤ nmax)
    {S δ φ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < smallEigGap nmax S δ φ c₁ ∧ smallEigGap nmax S δ φ c₁ ≤ smallEigScale δ φ / 2 := by
  have hc : (1 : ℝ) ≤ 2 ^ c₁.normalize.c := one_le_rpow (by norm_num) (le_max_right _ _)
  have hγ : 0 < smallEigScale δ φ / 2 := by have := smallEigScale_pos (φ := φ) hδ; positivity
  obtain ⟨h1, h2, -⟩ := ginibreClass_spec (c₂ := c₁) hb₁ hb₁ hn hS hγ
    (φ := φ / (4 * 2 ^ c₁.normalize.c)) (by positivity)
    (by rw [div_le_one (by positivity)]; nlinarith)
  exact ⟨h1, h2⟩

/-- The condition parameter $t_2$ is in $(0, 1]$. -/
theorem smallEigCond_pos_le {c₂ : PolyLogTail} (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : 1 ≤ nmax)
    {S δ φ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < smallEigCond nmax S δ φ c₂ ∧ smallEigCond nmax S δ φ c₂ ≤ 1 := by
  have hγ : 0 < smallEigScale δ φ / 2 := by have := smallEigScale_pos (φ := φ) hδ; positivity
  obtain ⟨-, -, h1, h2, -⟩ := ginibreClass_spec (c₁ := c₂) hb₂ hb₂ hn hS hγ
    (φ := φ / 4) (by positivity) (by linarith)
  exact ⟨h1, h2⟩

/-- The condition bound $B_c = 4/t_2$ is at least $4$. -/
theorem smallEigCondition_ge {c₂ : PolyLogTail} (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : 1 ≤ nmax)
    {S δ φ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    4 ≤ smallEigCondition nmax S δ φ c₂ := by
  obtain ⟨h1, h2⟩ := smallEigCond_pos_le hb₂ hn hS hδ hφ hφ1
  unfold smallEigCondition
  rw [le_div_iff₀ h1]; linarith

/-- The separation $g_c = t_1/4$ is positive. -/
theorem smallEigSeparation_pos {c₁ : PolyLogTail} (hb₁ : 0 < c₁.b) {nmax : ℕ} (hn : 1 ≤ nmax)
    {S δ φ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < smallEigSeparation nmax S δ φ c₁ := by
  have := (smallEigGap_pos_le hb₁ hn hS hδ hφ hφ1).1
  unfold smallEigSeparation; positivity

/-- The coupling threshold $\omega$ is positive. -/
theorem smallEigOmega_pos {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < smallEigOmega nmax S δ φ c₁ c₂ := by
  have h1 := smallEigSeparation_pos hb₁ hn hS hδ hφ hφ1
  have h2 := smallEigCondition_ge hb₂ hn hS hδ hφ hφ1
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
  unfold smallEigOmega
  apply div_pos (lt_min (by positivity) (div_pos h1 (by positivity))) (by positivity)

/-- $2n_{\max}\cdot 2.25\,\omega = \tfrac38\min(\delta/4, g_c/(16n_{\max}B_c))$. -/
theorem two_mul_mul_smallEigOmega {c₁ c₂ : PolyLogTail} {nmax : ℕ} (hn : 1 ≤ nmax)
    (S δ φ : ℝ) :
    2 * nmax * (2.25 * smallEigOmega nmax S δ φ c₁ c₂) = 3 / 8 *
      min (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
        (16 * nmax * smallEigCondition nmax S δ φ c₂)) := by
  have hn' : (0 : ℝ) < nmax := by exact_mod_cast hn
  unfold smallEigOmega
  field_simp
  ring

/-- The weight bound $p$ is in $(0, 1]$: $R \ge 3$, $B_c \ge 4$ and $\varphi_D \le 1$. -/
theorem smallEigWeight_pos_le {c₂ : PolyLogTail} (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : 1 ≤ nmax)
    {S δ φ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < smallEigWeight nmax S δ φ c₂ ∧ smallEigWeight nmax S δ φ c₂ ≤ 1 := by
  have hB := smallEigCondition_ge hb₂ hn hS hδ hφ hφ1
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
  have hR : 3 ≤ smallEigVectorRadius nmax φ := by
    unfold smallEigVectorRadius
    have : 1 ≤ √(nmax : ℝ) := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt hn'
    have := sqrt_nonneg (2 * log (4 / smallEigDecouplerFailure nmax φ))
    have h2 : (1 : ℝ) ≤ √2 := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt (by norm_num)
    nlinarith
  have hD : 0 < smallEigDecouplerFailure nmax φ := by unfold smallEigDecouplerFailure; positivity
  have hD1 : smallEigDecouplerFailure nmax φ ≤ 1 := by
    unfold smallEigDecouplerFailure; rw [div_le_one (by positivity)]; linarith
  unfold smallEigWeight
  constructor
  · have : 0 < smallEigVectorRadius nmax φ := by linarith
    have : 0 < smallEigCondition nmax S δ φ c₂ := by linarith
    positivity
  · rw [div_le_one (by positivity), div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ 64 * smallEigVectorRadius nmax φ ^ 2 *
        (2 * smallEigCondition nmax S δ φ c₂) ^ 2 := by
      have : (1:ℝ) ≤ smallEigVectorRadius nmax φ ^ 2 := by nlinarith
      have : (1:ℝ) ≤ (2 * smallEigCondition nmax S δ φ c₂) ^ 2 := by nlinarith
      nlinarith
    nlinarith

/-- The degree $m = 2^q$ is at least `NLAlib.SmallEig.distSpecDegree` at $8B_c$ and $p$. -/
theorem distSpecDegree_le_two_pow_smallEigDegreeLog (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) :
    distSpecDegree (8 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂) ≤
      2 ^ smallEigDegreeLog nmax S δ φ c₂ :=
  Nat.le_pow_clog (by norm_num) _

/-- The step cap suffices: $\kappa \le 2^{m_2}\sqrt p$ for $m_2$ =
`NLAlib.SmallEig.decoupleSteps` $\kappa$ $p$ and $\kappa, p > 0$. -/
theorem le_two_pow_decoupleSteps_mul_sqrt {κ p : ℝ} (hκ : 0 < κ) (hp : 0 < p) :
    κ ≤ 2 ^ decoupleSteps κ p * √p := by
  have hsp : 0 < √p := sqrt_pos.mpr hp
  have h : logb 2 (κ / √p) ≤ (decoupleSteps κ p : ℝ) := by
    unfold decoupleSteps; push_cast
    linarith [Nat.le_ceil (logb 2 (κ / √p))]
  rw [← div_le_iff₀ hsp, ← rpow_natCast]
  calc κ / √p = 2 ^ logb 2 (κ / √p) := (rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
    _ ≤ 2 ^ (decoupleSteps κ p : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) h

/-- **The degree of `DistSpec` is at most twelve step caps**: for $\kappa, p > 0$,
`NLAlib.SmallEig.distSpecDegree` $\kappa$ $p \le 12m_2$, $m_2$ = `NLAlib.SmallEig.decoupleSteps`
$\kappa$ $p$, since $12\log_2\kappa + 6\log_2(1/p) = 12\log_2(\kappa/\sqrt p)$ and
$\kappa \le 2^{m_2}\sqrt p$. -/
theorem distSpecDegree_le_decoupleSteps {κ p : ℝ} (hκ : 0 < κ) (hp : 0 < p) :
    distSpecDegree κ p ≤ 12 * decoupleSteps κ p := by
  have hsp : 0 < √p := sqrt_pos.mpr hp
  have hl : logb 2 κ ≤ decoupleSteps κ p + logb 2 √p := by
    calc logb 2 κ ≤ logb 2 (2 ^ decoupleSteps κ p * √p) :=
          logb_le_logb_of_le (by norm_num) hκ (le_two_pow_decoupleSteps_mul_sqrt hκ hp)
      _ = _ := by
          rw [logb_mul (by positivity) hsp.ne', logb_pow, logb_self_eq_one (by norm_num),
            mul_one]
  have hs : logb 2 p = 2 * logb 2 √p := by
    rw [← sq_sqrt hp.le, logb_pow, sqrt_sq hsp.le]; norm_num
  unfold distSpecDegree
  refine Nat.ceil_le.mpr ?_
  rw [logb_inv]
  push_cast
  linarith

/-- The accuracy $\beta' = \omega/20$ is in $(0, 0.8 \cdot 2\Sigma]$. -/
theorem smallEigAccuracy_le {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < smallEigAccuracy nmax S δ φ c₁ c₂ ∧ smallEigAccuracy nmax S δ φ c₁ c₂ ≤ 0.8 * (2 * S) := by
  have hS : 0 ≤ S := by linarith
  have hω := smallEigOmega_pos hb₁ hb₂ hn hS hδ hφ hφ1
  have h := two_mul_mul_smallEigOmega (c₁ := c₁) (c₂ := c₂) hn S δ φ
  have hm := min_le_left (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
    (16 * nmax * smallEigCondition nmax S δ φ c₂))
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
  unfold smallEigAccuracy
  constructor
  · positivity
  · nlinarith

/-- **The side conditions of the parameter words** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], the parameter choices, corrected): for tail records with $b_1, b_2 > 0$,
$n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$, with $\gamma, t_1, t_2, B_c,
g_c, \omega, \beta', \eta_1, \eta_2, p, m = 2^q, t, m_2$ the choices of this file: the noise is
within budget, $\gamma W \le \delta/4$; the class tails hold at every order $N \le n_{\max}$ with
$\varphi/4$ each (`NLAlib.SmallEig.ginibreClass_spec`); the worklist's cut level
$2.25\,\omega$ over $2n_{\max}$ rounds is within $\delta/4$ and the class bound
$g_c/(16n_{\max}B_c)$; the choices of `OneEig` hold at the block norm $2\Sigma$
(`NLAlib.SmallEig.oneEigRadii_spec` at $\beta'$, $g_c/4$, $\varphi_D/2$), the degree $m$ is at
least `NLAlib.SmallEig.distSpecDegree` $8B_c$ $p$, and $8B_c \le 2^{m_2}\sqrt p$. -/
theorem smallEigParams_spec {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < smallEigScale δ φ ∧ smallEigScale δ φ * smallEigNoiseLevel φ ≤ δ / 4 ∧
      0 < smallEigGap nmax S δ φ c₁ ∧ smallEigGap nmax S δ φ c₁ ≤ smallEigScale δ φ ∧
      0 < smallEigCond nmax S δ φ c₂ ∧ smallEigCond nmax S δ φ c₂ ≤ 1 ∧
      0 < smallEigOmega nmax S δ φ c₁ c₂ ∧
      2 * nmax * (2.25 * smallEigOmega nmax S δ φ c₁ c₂) ≤ δ / 4 ∧
      2 * nmax * (2.25 * smallEigOmega nmax S δ φ c₁ c₂) ≤
        smallEigSeparation nmax S δ φ c₁ / (16 * nmax * smallEigCondition nmax S δ φ c₂) ∧
      smallEigAccuracy nmax S δ φ c₁ c₂ ≤ 0.8 * (2 * S) ∧
      0 < smallEigWeight nmax S δ φ c₂ ∧ smallEigWeight nmax S δ φ c₂ ≤ 1 ∧
      distSpecDegree (8 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂) ≤
        2 ^ smallEigDegreeLog nmax S δ φ c₂ ∧
      8 * smallEigCondition nmax S δ φ c₂ ≤
        2 ^ smallEigDecoupleSteps nmax S δ φ c₂ * √(smallEigWeight nmax S δ φ c₂) := by
  have hS : 0 ≤ S := by linarith
  have hγ := smallEigScale_pos (φ := φ) hδ
  obtain ⟨hg0, hg⟩ := smallEigGap_pos_le hb₁ hn hS hδ hφ hφ1
  obtain ⟨hc0, hc1⟩ := smallEigCond_pos_le hb₂ hn hS hδ hφ hφ1
  have hB := smallEigCondition_ge hb₂ hn hS hδ hφ hφ1
  have hsep := smallEigSeparation_pos hb₁ hn hS hδ hφ hφ1
  have hn' : (0 : ℝ) < nmax := by exact_mod_cast hn
  have hm0 : 0 < min (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
      (16 * nmax * smallEigCondition nmax S δ φ c₂)) := lt_min (by positivity) (by positivity)
  have hΩ := two_mul_mul_smallEigOmega (c₁ := c₁) (c₂ := c₂) hn S δ φ
  obtain ⟨hp0, hp1⟩ := smallEigWeight_pos_le hb₂ hn hS hδ hφ hφ1
  refine ⟨hγ, (smallEigScale_mul_noiseLevel δ φ).le, hg0, by linarith, hc0, hc1,
    smallEigOmega_pos hb₁ hb₂ hn hS hδ hφ hφ1, ?_, ?_,
    (smallEigAccuracy_le hb₁ hb₂ hn hδ hδS hφ hφ1).2, hp0, hp1,
    distSpecDegree_le_two_pow_smallEigDegreeLog nmax S δ φ c₂,
    le_two_pow_decoupleSteps_mul_sqrt (by linarith) hp0⟩
  · rw [hΩ]; nlinarith [min_le_left (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
      (16 * nmax * smallEigCondition nmax S δ φ c₂))]
  · rw [hΩ]; nlinarith [min_le_right (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
      (16 * nmax * smallEigCondition nmax S δ φ c₂))]

/-- The radius $\eta_1$ of `OneEig` is positive (`NLAlib.SmallEig.oneEigRadii_spec` at $\beta'$,
$g_c/4$ and $\varphi_D/2$). -/
theorem smallEigInnerRadius_pos {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) : 0 < smallEigInnerRadius nmax S δ φ c₁ c₂ := by
  obtain ⟨hβ, hβS⟩ := smallEigAccuracy_le hb₁ hb₂ hn hδ hδS hφ hφ1
  have hsep := smallEigSeparation_pos hb₁ hn (hδ.le.trans hδS) hδ hφ hφ1
  have hn1 : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
  have hD : 0 < smallEigDecouplerFailure nmax φ / 2 := by
    unfold smallEigDecouplerFailure; positivity
  have hD1 : smallEigDecouplerFailure nmax φ / 2 ≤ 1 := by
    unfold smallEigDecouplerFailure
    rw [div_div, div_le_one (by positivity)]; nlinarith
  exact (oneEigRadii_spec hβ hβS (by positivity : 0 < smallEigSeparation nmax S δ φ c₁ / 4)
    hD hD1).1

/-- **The parameter words are positive** ([BanksGarzaVargasSrivastava2025, Theorem 1.1]): for
tail records with $b_1, b_2 > 0$, $n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and
$0 < \varphi \le 1$, the first eight words of `NLAlib.SmallEig.smallEigParams` (the scale, the
thresholds and the radii) are positive. Without it a headline under
$0 \le \boldsymbol{u} \le \boldsymbol{u}_0$ could be vacuous. -/
theorem smallEigParams_pos {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    ∀ i < 8, 0 < (smallEigParams nmax S δ φ c₁ c₂).getD i 0 := by
  have hS : 0 ≤ S := by linarith
  have hγ := smallEigScale_pos (φ := φ) hδ
  have hω := smallEigOmega_pos hb₁ hb₂ hn hS hδ hφ hφ1
  have hβ := (smallEigAccuracy_le hb₁ hb₂ hn hδ hδS hφ hφ1).1
  have hsep := smallEigSeparation_pos hb₁ hn hS hδ hφ hφ1
  have hη1 := smallEigInnerRadius_pos hb₁ hb₂ hn hδ hδS hφ hφ1
  have hη2 : 0 < smallEigOuterRadius nmax S δ φ c₁ c₂ :=
    lt_min (by positivity) (by positivity)
  intro i hi
  interval_cases i <;> simp only [smallEigParams, List.getD_cons_zero, List.getD_cons_succ]
  · exact hγ
  · exact hω
  · exact hβ
  · exact hη1
  · exact hη2
  · positivity
  · positivity
  · positivity

/-- **The cap words are valid** for the cap `NLAlib.SmallEig.smallEigCap`: the words $8$ to $11$
of `NLAlib.SmallEig.smallEigParams` are the exact naturals $m = 2^q$, $q$, $t$, $m_2$, all at
most the cap, for any arguments. -/
theorem smallEigCaps_smallEigParams (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) :
    SmallEigCaps (smallEigCap nmax S δ φ c₁ c₂) (smallEigParams nmax S δ φ c₁ c₂) :=
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩

end NLAlib.SmallEig
