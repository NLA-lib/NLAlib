/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import NLAlib.Matrix.QRIteration.EigenvectorWeights
public import NLAlib.Matrix.QRIteration.ShiftedQR
public import NLAlib.Matrix.Spectral.Diagonalizable

/-!
# Inverse iteration estimates of the distance to the spectrum

For a diagonalizable $\mathbf{H} = \mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ and a
shift $s$ off the spectrum, the last row of $(s\mathbf{I} - \mathbf{H})^{-m}$ measures the
distance from $s$ to the spectrum: its norm is at most $\kappa(\mathbf{V})$ times the $m$-th power
of the inverse distance, and at least the weighted inverse distance to every eigenvalue, divided
by $\kappa(\mathbf{V})$ (the row form of [BanksGarzaVargasSrivastava2025, Proposition 3.1]). Its
consequence for the exact shifted QR iteration with one repeated shift
[BanksGarzaVargasSrivastava2025, Lemma 4.1]: one of the first $m$ iterates has its last
subdiagonal entry at most the distance to a weighted eigenvalue, up to the factor
$(\kappa(\mathbf{V})/\sqrt{w_i})^{1/m}$. The six-point net of an annulus
([BanksGarzaVargasSrivastava2025, Observation 3.2], with the radii as parameters) is the geometry
of the search for a point near the spectrum.

## Main definitions

* `NLAlib.hexDir`: the sixth roots of unity $e^{i\pi j/3}$.
* `NLAlib.hexNetRadius`: the covering radius of the six-point net of an annulus.

## Main results

* `NLAlib.norm_lastRow_inv_pow_le`, `NLAlib.sqrt_lastRowWeights_mul_le_norm_lastRow_inv_pow`: the
  two sides of the row form of Proposition 3.1.
* `NLAlib.exists_le_norm_subdiag_shiftedQR_pow`: Lemma 4.1.
* `NLAlib.exists_norm_hexNet_add_sub_le`, `NLAlib.hexNetRadius_le`: the six-point net.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-! ### The distance to the spectrum from the last row of a resolvent power -/

/-- **The last row of a resolvent power is at most $\kappa(\mathbf{V})$ times the inverse
distance to the spectrum, to the power $m$** ([BanksGarzaVargasSrivastava2025, Proposition 3.1],
the lower bound on $\tau$, in row form): for
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
a shift $s \ne d_i$ for every $i$ and $m \ge 1$,
$$\|\mathbf{e}_n^{\mathsf{T}}(s\mathbf{I} - \mathbf{H})^{-m}\| \le
  \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\,\bigl(\min_i \lvert s - d_i\rvert\bigr)^{-m}.$$ -/
theorem norm_lastRow_inv_pow_le {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {s : ℂ} {m : ℕ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hs : ∀ i, s ≠ d i) (hm : 1 ≤ m) :
    ‖WithLp.toLp 2 (((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - H)⁻¹ ^ m) (Fin.last n))‖ ≤
      pseudoConditionNumber V * (⨅ i, ‖s - d i‖)⁻¹ ^ m := by
  set g : Fin (n + 1) → ℂ := fun i => (s - d i)⁻¹ ^ m
  have h := norm_mul_diagonal_mul_inv_last_sq_le hV g
  rw [← inv_smul_one_sub_pow_eq_mul_diagonal_mul_inv hV hHV hs m] at h
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := fun i => ‖s - d i‖)
  have hpos : 0 < ⨅ i, ‖s - d i‖ := by rw [← hi₀]; exact norm_pos_iff.mpr (sub_ne_zero.mpr (hs i₀))
  have hg : ∀ i, ‖g i‖ ≤ (⨅ i, ‖s - d i‖)⁻¹ ^ m := fun i => by
    rw [norm_pow, norm_inv]
    gcongr
    exact ciInf_le (Finite.bddBelow_range _) i
  have hsum : ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 ≤ ((⨅ i, ‖s - d i‖)⁻¹ ^ m) ^ 2 := by
    calc ∑ i, lastRowWeights V i * ‖g i‖ ^ 2
        ≤ ∑ i, lastRowWeights V i * ((⨅ i, ‖s - d i‖)⁻¹ ^ m) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            gcongr
            · exact lastRowWeights_nonneg V i
            · exact hg i
      _ = ((⨅ i, ‖s - d i‖)⁻¹ ^ m) ^ 2 := by rw [← Finset.sum_mul, sum_lastRowWeights hV, one_mul]
  have hκ : 0 ≤ pseudoConditionNumber V := pseudoConditionNumber_nonneg V
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow]
  exact h.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))

/-- **The last row of a resolvent power is at least every weighted inverse distance, divided by
$\kappa(\mathbf{V})$** ([BanksGarzaVargasSrivastava2025, Proposition 3.1], the upper bound on
$\tau$, in row form): for $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\mathbf{V}$ invertible, a shift $s \ne d_i$ for every $i$, $m \ge 1$ and the last-row weights
$w_i$ of $\mathbf{V}$, for every $i$
$$\sqrt{w_i}\,\lvert s - d_i\rvert^{-m} \le \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2
  \|\mathbf{e}_n^{\mathsf{T}}(s\mathbf{I} - \mathbf{H})^{-m}\|.$$ -/
theorem sqrt_lastRowWeights_mul_le_norm_lastRow_inv_pow
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {s : ℂ} {m : ℕ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) (hs : ∀ i, s ≠ d i) (hm : 1 ≤ m)
    (i : Fin (n + 1)) :
    √(lastRowWeights V i) * ‖s - d i‖⁻¹ ^ m ≤
      pseudoConditionNumber V *
        ‖WithLp.toLp 2 (((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - H)⁻¹ ^ m)
          (Fin.last n))‖ := by
  set g : Fin (n + 1) → ℂ := fun i => (s - d i)⁻¹ ^ m
  have h := sum_lastRowWeights_mul_sq_le hV g
  rw [← inv_smul_one_sub_pow_eq_mul_diagonal_mul_inv hV hHV hs m] at h
  have hi : lastRowWeights V i * ‖g i‖ ^ 2 ≤ ∑ j, lastRowWeights V j * ‖g j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => lastRowWeights V j * ‖g j‖ ^ 2)
      (fun j _ => mul_nonneg (lastRowWeights_nonneg V j) (sq_nonneg _)) (Finset.mem_univ i)
  have hgi : ‖g i‖ = ‖s - d i‖⁻¹ ^ m := by rw [norm_pow, norm_inv]
  have hκ : 0 ≤ pseudoConditionNumber V := pseudoConditionNumber_nonneg V
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, mul_pow, mul_pow,
    Real.sq_sqrt (lastRowWeights_nonneg V i), ← hgi]
  exact hi.trans h

/-- **Exact decoupling by a repeated shift** ([BanksGarzaVargasSrivastava2025, Lemma 4.1]): let
$\mathbf{H}$ of order $n + 2$ be upper Hessenberg, $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and last-row weights $w$,
$s \ne d_i$ for every $i$, and $m \ge 1$. Then for every $i$ some $\ell$ with
$1 \le \ell \le m$ has the last subdiagonal entry $h_\ell$ of the $\ell$-th exact shifted QR
iterate with the shift $s$ satisfying
$$\lvert h_\ell\rvert^m\sqrt{w_i} \le \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\,
  \lvert s - d_i\rvert^m.$$
Stated with powers, so that a zero weight makes it vacuous instead of dividing by zero. -/
theorem exists_le_norm_subdiag_shiftedQR_pow {H V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    {d : Fin (n + 2) → ℂ} {s : ℂ} {m : ℕ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hs : ∀ i, s ≠ d i) (hm : 1 ≤ m) (i : Fin (n + 2)) :
    ∃ ℓ ∈ Finset.Icc 1 m,
      ‖multiShiftedQRStep H (List.replicate ℓ s) (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ m *
          √(lastRowWeights V i) ≤
        pseudoConditionNumber V * ‖s - d i‖ ^ m := by
  sorry

/-! ### The six-point net of an annulus -/

/-- The sixth roots of unity $e^{i\pi j/3}$, $j < 6$: the directions of the six-point net. -/
noncomputable def hexDir (j : Fin 6) : ℂ := Complex.exp (((Real.pi * j / 3 : ℝ) : ℂ) * Complex.I)

/-- The covering radius of the six-point net $\{s + r e^{i\pi j/3}\}$ on the annulus
$r_1 \le \lvert z - s\rvert \le r_2$:
$\max\bigl(\sqrt{r_1^2 + r^2 - \sqrt3\,r_1 r}, \sqrt{r_2^2 + r^2 - \sqrt3\,r_2 r}\bigr)$, the
distance at the angle $\pi/6$ from the nearest net point, largest on one of the two circles. -/
noncomputable def hexNetRadius (r₁ r₂ r : ℝ) : ℝ :=
  max (√(r₁ ^ 2 + r ^ 2 - √3 * r₁ * r)) (√(r₂ ^ 2 + r ^ 2 - √3 * r₂ * r))

/-- The six directions have unit modulus. -/
theorem norm_hexDir (j : Fin 6) : ‖hexDir j‖ = 1 := by
  rw [hexDir, Complex.norm_exp_ofReal_mul_I]

private theorem hexDir_re_im (j : Fin 6) :
    (hexDir j).re = Real.cos (Real.pi * j / 3) ∧ (hexDir j).im = Real.sin (Real.pi * j / 3) :=
  ⟨Complex.exp_ofReal_mul_I_re _, Complex.exp_ofReal_mul_I_im _⟩

/-- One of the six directions is within $\pi/6$ of every complex number: for every
$u \in \mathbb{C}$ some $j < 6$ has
$\sqrt3\,\lvert u\rvert \le 2\operatorname{Re}(\overline{e^{i\pi j/3}}\,u)$. -/
theorem exists_sqrt_three_mul_norm_le_re_conj_hexDir_mul (u : ℂ) :
    ∃ j : Fin 6, √3 * ‖u‖ ≤ 2 * (starRingEnd ℂ (hexDir j) * u).re := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hcos2 : Real.cos (Real.pi * 2 / 3) = -(1 / 2) := by
    rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  have hsin2 : Real.sin (Real.pi * 2 / 3) = √3 / 2 := by
    rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]
  have hcos4 : Real.cos (Real.pi * 4 / 3) = -(1 / 2) := by
    rw [show Real.pi * 4 / 3 = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_three]
  have hsin4 : Real.sin (Real.pi * 4 / 3) = -(√3 / 2) := by
    rw [show Real.pi * 4 / 3 = Real.pi / 3 + Real.pi by ring, Real.sin_add_pi,
      Real.sin_pi_div_three]
  have hcos5 : Real.cos (Real.pi * 5 / 3) = 1 / 2 := by
    rw [show Real.pi * 5 / 3 = -(Real.pi / 3) + 2 * Real.pi by ring, Real.cos_add_two_pi,
      Real.cos_neg, Real.cos_pi_div_three]
  have hsin5 : Real.sin (Real.pi * 5 / 3) = -(√3 / 2) := by
    rw [show Real.pi * 5 / 3 = -(Real.pi / 3) + 2 * Real.pi by ring, Real.sin_add_two_pi,
      Real.sin_neg, Real.sin_pi_div_three]
  set a := u.re
  set b := u.im
  have hu : ‖u‖ ^ 2 = a ^ 2 + b ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  -- `√3 ‖u‖ ≤ 2 p` follows from `0 ≤ p` and `3 (a² + b²) ≤ 4 p²`
  have key : ∀ p : ℝ, 0 ≤ p → 3 * (a ^ 2 + b ^ 2) ≤ 4 * p ^ 2 → √3 * ‖u‖ ≤ 2 * p := by
    intro p hp h
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, h3, hu]; linarith
  have hre : ∀ j : Fin 6, (starRingEnd ℂ (hexDir j) * u).re =
      Real.cos (Real.pi * j / 3) * a + Real.sin (Real.pi * j / 3) * b := fun j => by
    obtain ⟨h1, h2⟩ := hexDir_re_im j
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, h1, h2, a, b]; ring
  rcases le_or_gt (√3 * |b|) |a| with hab | hab
  · rcases le_or_gt 0 a with ha | ha
    · refine ⟨0, key _ ?_ ?_⟩ <;> simp only [hre, Fin.val_zero, Nat.cast_zero, mul_zero,
        zero_div, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero]
      · exact ha
      · rw [abs_of_nonneg ha] at hab
        nlinarith [sq_abs b, mul_self_le_mul_self (by positivity) hab]
    · refine ⟨3, key _ ?_ ?_⟩ <;> simp only [hre, show ((3 : Fin 6) : ℕ) = 3 from rfl,
        Nat.cast_ofNat, show Real.pi * 3 / 3 = Real.pi by ring, Real.cos_pi, Real.sin_pi,
        zero_mul, add_zero]
      · linarith
      · rw [abs_of_neg ha] at hab
        nlinarith [sq_abs b, mul_self_le_mul_self (by positivity) hab]
  · rcases le_or_gt 0 b with hb0 | hb0 <;> rcases le_or_gt 0 a with ha | ha
    · refine ⟨1, key _ ?_ ?_⟩ <;> simp only [hre, Fin.val_one, Nat.cast_one, mul_one,
        Real.cos_pi_div_three, Real.sin_pi_div_three]
      · positivity
      · rw [abs_of_nonneg ha, abs_of_nonneg hb0] at hab
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hab.le)]
    · refine ⟨2, key _ ?_ ?_⟩ <;> simp only [hre, show ((2 : Fin 6) : ℕ) = 2 from rfl,
        Nat.cast_ofNat, hcos2, hsin2]
      · nlinarith
      · rw [abs_of_neg ha, abs_of_nonneg hb0] at hab
        nlinarith [mul_nonneg (neg_nonneg.mpr ha.le) (sub_nonneg.mpr hab.le)]
    · refine ⟨5, key _ ?_ ?_⟩ <;> simp only [hre, show ((5 : Fin 6) : ℕ) = 5 from rfl,
        Nat.cast_ofNat, hcos5, hsin5]
      · nlinarith
      · rw [abs_of_nonneg ha, abs_of_neg hb0] at hab
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hab.le)]
    · refine ⟨4, key _ ?_ ?_⟩ <;> simp only [hre, show ((4 : Fin 6) : ℕ) = 4 from rfl,
        Nat.cast_ofNat, hcos4, hsin4]
      · nlinarith
      · rw [abs_of_neg ha, abs_of_neg hb0] at hab
        nlinarith [mul_nonneg (neg_nonneg.mpr ha.le) (sub_nonneg.mpr hab.le)]

/-- **The perturbed six-point net covers an annulus**
([BanksGarzaVargasSrivastava2025, Observation 3.2], with the radii as parameters): for
$0 < r_1 \le r \le r_2$, every $z$ with $r_1 \le \lvert z - s\rvert \le r_2$ and every
$\lvert w\rvert \le \eta$, some $j < 6$ has
$\lvert s + r e^{i\pi j/3} + w - z\rvert \le \rho + \eta$, where $\rho$ is
`NLAlib.hexNetRadius` $r_1$ $r_2$ $r$. -/
theorem exists_norm_hexNet_add_sub_le {r₁ r r₂ η : ℝ} (h₁ : 0 < r₁) (h₁r : r₁ ≤ r)
    (hr₂ : r ≤ r₂) {s z w : ℂ} (hz₁ : r₁ ≤ ‖z - s‖) (hz₂ : ‖z - s‖ ≤ r₂) (hw : ‖w‖ ≤ η) :
    ∃ j : Fin 6, ‖s + r * hexDir j + w - z‖ ≤ hexNetRadius r₁ r₂ r + η := by
  obtain ⟨j, hj⟩ := exists_sqrt_three_mul_norm_le_re_conj_hexDir_mul (z - s)
  refine ⟨j, ?_⟩
  set u := z - s
  set t := ‖u‖
  have hr : 0 ≤ r := h₁.le.trans h₁r
  -- `‖r e - u‖² = r² + t² - 2 r Re(ē u) ≤ r² + t² - √3 r t`
  have hsq : ‖(r : ℂ) * hexDir j - u‖ ^ 2 ≤ t ^ 2 + r ^ 2 - √3 * t * r := by
    have he : (hexDir j).re * (hexDir j).re + (hexDir j).im * (hexDir j).im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, norm_hexDir, one_pow]
    have ht : t ^ 2 = u.re * u.re + u.im * u.im := by rw [Complex.sq_norm, Complex.normSq_apply]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, Complex.conj_re, Complex.conj_im] at hj ⊢
    nlinarith [mul_le_mul_of_nonneg_left hj hr]
  -- the quadratic in `t` is largest at an end of `[r₁, r₂]`
  have hend : ‖(r : ℂ) * hexDir j - u‖ ≤ hexNetRadius r₁ r₂ r := by
    unfold hexNetRadius
    rcases le_or_gt (t + r₁) (√3 * r) with h | h
    · refine le_max_of_le_left (Real.le_sqrt_of_sq_le ?_)
      nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hz₁)]
    · refine le_max_of_le_right (Real.le_sqrt_of_sq_le ?_)
      nlinarith [mul_le_mul_of_nonneg_left (by linarith : √3 * r ≤ t + r₂) (sub_nonneg.mpr hz₂)]
  calc ‖s + r * hexDir j + w - z‖ = ‖((r : ℂ) * hexDir j - u) + w‖ := by congr 1; ring
    _ ≤ ‖(r : ℂ) * hexDir j - u‖ + ‖w‖ := norm_add_le _ _
    _ ≤ hexNetRadius r₁ r₂ r + η := add_le_add hend hw

/-- **The covering radius on the annulus of a $10\%$ distance estimate**
([BanksGarzaVargasSrivastava2025, Observation 3.2], corrected): on
$\tau/1.1 \le \lvert z - s\rvert \le \tau/0.9$ the six points $s + \tau e^{i\pi j/3}$ cover within
$0.561\,\tau$, for $\tau \ge 0$. The paper's $0.57\tau$ for the annulus $[0.9\tau, 1.12\tau]$ is
not the annulus a $10\%$ estimate gives. -/
theorem hexNetRadius_le {τ : ℝ} (hτ : 0 ≤ τ) : hexNetRadius (τ / 1.1) (τ / 0.9) τ ≤ 0.561 * τ := by
  have h3 : (1.73 : ℝ) ≤ √3 := Real.le_sqrt_of_sq_le (by norm_num)
  have h := mul_le_mul_of_nonneg_right h3 (sq_nonneg τ)
  unfold hexNetRadius
  refine max_le ((Real.sqrt_le_iff).mpr ⟨by positivity, ?_⟩)
    ((Real.sqrt_le_iff).mpr ⟨by positivity, ?_⟩) <;> ring_nf <;> ring_nf at h <;>
    linarith [sq_nonneg τ]

end NLAlib
