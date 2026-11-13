/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection
public import NLAlib.Probability.AdaptiveUnionBound

/-!
# Hermitian diagonalization in linear precision

The main theorem ([Shah2024, Theorem 4.2]):
randomized spectral bisection (`NLAlib.eigh`) on a floating-point machine with black-box
multiplication and QR returns, with
probability at least $1 - \theta$, an approximate diagonalization with residual
$2\varepsilon R_0$ and $\mathbf{U}$ within $\varepsilon/3$ of unitary, using
$\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ bits of
precision. The samples of the nodes are independent, each with the law `NLAlib.eighSampleLaw`;
the node bounds and the measurability of the nodes are in
`NLAlib/Eigensolvers/SpectralBisection.lean`, and the union bound over the adaptively grown
tree is `NLAlib.measureReal_exists_mem_le_of_forall_measure_le_lintegral`. The theorem for a
bounded binary format is in `NLAlib/Eigensolvers/SpectralBisection/BoundedFormat.lean`.

## Main results

* [Theorem 4.2](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw).
* [Its bit count](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

namespace NLAlib

/-- The global hypotheses of Theorem 4.2 give $u \ge 0$, $n \ge 1$, $\ell \ge 20$,
$n\beta \le \varepsilon/104$ and the contract bounds of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params`. -/
private theorem FloatMachine.IsAccurate.nonneg_and_one_le_and_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hμM : Monotone μM) (hμM₀ : 0 ≤ μM 0) {n : ℕ} {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω) :
    0 ≤ u ∧ 1 ≤ n ∧ 20 ≤ ℓ ∧ n * dec β ≤ dec ε / 104 ∧ 100 * (ℓ : ℝ) ^ 2 * u ≤ 1 ∧
      100 * τ ≤ dec ε * min (dec R₀) 1 ∧ 16 * (dec R₀ + ℓ) ≤ Ω := by
  have hl20 : 20 ≤ ℓ := by
    have h15 : (15 : ℝ) ≤ Real.logb 2 (dec ε)⁻¹ := by
      have h2 : (2 : ℝ) ^ (15 : ℕ) ≤ (dec ε)⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hε, ← inv_pow]; exact hε₁
      have := Real.logb_le_logb_of_le one_lt_two (by positivity) h2
      rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
    have : 15 ≤ ⌈Real.logb 2 (dec ε)⁻¹⌉₊ := by
      have := h15.trans (Nat.le_ceil _); exact_mod_cast this
    unfold bisectionDepth at hℓ; omega
  have hΩ1 : 1 ≤ Ω := by
    have : 0 ≤ √2 * √(n : ℝ) := by positivity
    have : (20 : ℝ) ≤ ℓ := by exact_mod_cast hl20
    linarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)), hR₀pos.le,
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hu : 0 ≤ u := by
    have h := hM.ofNat 1 (by norm_num; exact hΩ1)
    have h1 : 0 < max |((1 : ℕ) : ℝ)| τ := lt_max_of_lt_left (by norm_num)
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h1
    linarith [abs_nonneg (((1 : ℕ) : ℝ) - dec (M.ofNat 1))]
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_mul, Real.sqrt_zero, mul_zero, div_zero] at hβle
      exact absurd hβle hβ.not_ge
    exact hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : (20 : ℝ) ≤ ℓ := by exact_mod_cast hl20
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hm1 : (1 : ℝ) ≤ min (n : ℝ) (ℓ + 1) := le_min hn1 (by linarith)
  have he1 : (1 : ℝ) ≤ min (n : ℝ) (Real.exp 1) :=
    le_min hn1 (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hS : √(n : ℝ) ≤ √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) :=
    Real.sqrt_le_sqrt (by nlinarith [mul_le_mul hm1 he1 zero_le_one (by linarith)])
  have hT : 2 * √(n : ℝ) ≤
      2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)) := by
    have : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))]
  have hD : ((ℓ : ℝ) - 1) ^ 2 ≤ (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) := by nlinarith
  have hsθ : √θ ≤ 1 := Real.sqrt_le_one.mpr hθ₁
  have hnβ : n * dec β ≤ dec ε / 104 := by
    set S := √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1))
    set T := 2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))
    have hL : 0 < (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) := by nlinarith
    have hST : 2 * (n : ℝ) ≤ S * T := by
      have h1 : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt (by positivity)).symm
      have h2 := mul_le_mul hS hT (by positivity) (by positivity)
      linarith
    have hS0 : 0 < S := lt_of_lt_of_le (Real.sqrt_pos.2 (by linarith)) hS
    have hT0 : 0 < T := by linarith
    rw [le_div_iff₀ (mul_pos (mul_pos (mul_pos (by positivity) (by linarith)) hS0) hT0)] at hβle
    have h3 := mul_le_mul hD hST (by positivity) hL.le
    have h4 : ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε :=
      mul_le_of_le_one_right (by positivity) hsθ
    have h5 : 0 < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
    have h6 : 104 * ((ℓ : ℝ) - 1) ^ 2 * (n * dec β) ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε := by
      linarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 52 * dec β)]
    rw [le_div_iff₀ (by norm_num)]
    exact le_of_mul_le_mul_left (by linarith : ((ℓ : ℝ) - 1) ^ 2 * (n * dec β * 104) ≤
      ((ℓ : ℝ) - 1) ^ 2 * dec ε) h5
  have hν : 10 ≤ 4 * μM n + 10 + 10 * √(n : ℝ) := by
    nlinarith [hμM₀.trans (hμM (Nat.zero_le n)), Real.sqrt_nonneg (n : ℝ)]
  refine ⟨hu, hn, hl20, hnβ, ?_, ?_, ?_⟩
  · have hb1 : dec β ≤ 1 := by
      have := hε₁.trans (by norm_num : (2⁻¹ : ℝ) ^ 15 ≤ 1)
      have : dec β ≤ n * dec β := le_mul_of_one_le_left hβ.le hn1
      linarith
    have h0 : (ℓ : ℝ) ^ 2 ≤ n * ℓ * (ℓ + 1) := by nlinarith
    have h1 : 10 * (ℓ : ℝ) ^ 2 ≤ n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) :=
      mul_comm (10 : ℝ) _ ▸ mul_le_mul h0 hν (by norm_num) (by positivity)
    linarith [mul_le_mul_of_nonneg_right h1 hu, mul_le_of_le_one_left hβ.le hθ₁]
  · have h1 : (1 : ℝ) ≤ n * √(n : ℝ) := one_le_mul_of_one_le_of_one_le hn1 hsn
    have : 100 * τ ≤ τ * (100 * n * √(n : ℝ)) := by
      linarith [mul_le_mul_of_nonneg_left h1 hτ₀]
    exact this.trans (hτ.trans (min_le_right _ _))
  · have : 0 ≤ √2 * √(n : ℝ) := by positivity
    linarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)), hR₀pos.le, hn1]

/-- A node whose leaf test fails has a positive stored norm bound. -/
private theorem FloatMachine.IsAccurate.pos_of_le_mul_eq_false
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : u ≤ 1 / 100)
    {R e R₀ ε : F} (hint : M.le R (M.mul e R₀) = false) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1) (he : dec ε / 3 ≤ dec e) (he₁ : dec e ≤ dec ε)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1) (hR₀Ω : dec R₀ ≤ Ω) : 0 < dec R := by
  have h1 : ¬ dec R ≤ dec (M.mul e R₀) := fun h => by simp [(hM.le_iff _ _).2 h] at hint
  have ha : 0 < dec e * dec R₀ := mul_pos (by linarith) hR₀pos
  have hτa : τ ≤ dec e * dec R₀ := by
    linarith [mul_le_mul_of_nonneg_left (min_le_left (dec R₀) 1) hε.le,
      mul_le_mul_of_nonneg_right he hR₀pos.le]
  have h2 := hM.mul e R₀ (by
    rw [abs_of_pos ha]
    linarith [mul_le_mul_of_nonneg_right (he₁.trans hε₁) hR₀pos.le])
  rw [abs_of_pos ha, max_eq_left hτa] at h2
  have h3 := (abs_le.mp h2).2
  linarith [mul_le_mul_of_nonneg_right hu ha.le, lt_of_not_ge h1]

/-- The norm threshold of a node of size $k \le n$ is at most $\hat T$. -/
private theorem add_sqrt_log_le {n k : ℕ} {θ m : ℝ} (hk : 1 ≤ k) (hkn : k ≤ n) (hθ : 0 < θ)
    (hm : 0 < m) :
    2 * √2 * √(k : ℝ) + √(Real.log (16 / (θ * k / (6 * n * m)))) ≤
      2 * √2 * √(n : ℝ) + √(Real.log (96 * n * m / θ)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn : (0 : ℝ) < n := by linarith
  refine add_le_add (by gcongr) (Real.sqrt_le_sqrt ?_)
  rw [show 16 / (θ * k / (6 * n * m)) = 96 * n * m / θ / k by field_simp; ring]
  exact Real.log_le_log (by positivity) (div_le_self (by positivity) hk1)

/-- Bounds on the singular value threshold of a node of size $2 \le k \le n$: with
$S = \sqrt{nm\min(n, e)}$, $x \ge 0.39\sqrt\theta/S$, $x \ge \sqrt{\theta/(8nm)}/25$ and
$x \le 1$. -/
private theorem le_sqrt_div_min {n k : ℕ} {θ m : ℝ} (hk : 2 ≤ k) (hkn : k ≤ n) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) (hm : 1 ≤ m) :
    39 / 100 * √θ / √(n * m * min (n : ℝ) (Real.exp 1)) ≤
      √(15 * (θ * k / (6 * n * m)) / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k))) ∧
    √(θ / (8 * n * m)) / 25 ≤
      √(15 * (θ * k / (6 * n * m)) / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k))) ∧
    √(15 * (θ * k / (6 * n * m)) / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k))) ≤ 1 := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : 0 < m := by linarith
  have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hD0 : 0 < min ((k : ℝ) ^ 2) (Real.exp 1 * k) := lt_min (by positivity) (by positivity)
  have hP0 : 0 < (n : ℝ) * m * min (n : ℝ) (Real.exp 1) :=
    mul_pos (by positivity) (lt_min (by linarith) (by positivity))
  have hQ : 0 ≤ 15 * (θ * k / (6 * n * m)) / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k)) := by
    positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.le_sqrt (by positivity) hQ, div_pow, mul_pow, Real.sq_sqrt hθ.le,
      Real.sq_sqrt hP0.le]
    have hD : min ((k : ℝ) ^ 2) (Real.exp 1 * k) ≤ k * min (n : ℝ) (Real.exp 1) := by
      rw [mul_min_of_nonneg _ _ (by positivity)]
      exact min_le_min (by nlinarith) (by rw [mul_comm])
    calc (39 / 100) ^ 2 * θ / (n * m * min (n : ℝ) (Real.exp 1))
        ≤ 15 * (θ * k / (6 * n * m)) / (16 * (k * min (n : ℝ) (Real.exp 1))) := by
          rw [div_le_div_iff₀ hP0 (by positivity)]
          field_simp
          nlinarith [mul_pos hθ hP0]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  · rw [Real.le_sqrt (by positivity) hQ, div_pow, Real.sq_sqrt (by positivity)]
    calc θ / (8 * n * m) / 25 ^ 2
        ≤ 15 * (θ * k / (6 * n * m)) / (16 * (3 * k)) := by
          field_simp
          nlinarith
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by nlinarith [min_le_right ((k : ℝ) ^ 2) (Real.exp 1 * k)])
  · have hρ : θ * k / (6 * n * m) ≤ k := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [one_le_mul_of_one_le_of_one_le (by linarith : (1 : ℝ) ≤ n) hm]
    have hDk : (k : ℝ) ≤ min ((k : ℝ) ^ 2) (Real.exp 1 * k) :=
      le_min (by nlinarith) (le_mul_of_one_le_left (by positivity) he1)
    rw [Real.sqrt_le_one, div_le_one (by positivity)]
    linarith

/-- The deflation tolerance of a node: $2t\beta/x \le (1 - 1/\ell_y)\varepsilon_y/(5\ell_y)$. -/
private theorem mul_div_mul_le_of_le_div {n k L ℓ : ℕ} {e ey b θ m t x : ℝ} (hk : 2 ≤ k)
    (hkn : k ≤ n) (hL : ℓ ≤ L) (hL₂ : L ≤ 2 * ℓ) (hl20 : 20 ≤ ℓ) (he : 0 < e) (hθ : 0 < θ)
    (hm : 1 ≤ m) (hb : 0 < b)
    (hey : (1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((L : ℝ) - 1)) * e ≤ ey)
    (hble : b ≤ ((ℓ : ℝ) - 1) ^ 2 * e * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * m * min (n : ℝ) (Real.exp 1)) * (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * m / θ)))))
    (htle : t ≤ 2 * √2 * √(n : ℝ) + √(Real.log (96 * n * m / θ)))
    (hx : 39 / 100 * √θ / √(n * m * min (n : ℝ) (Real.exp 1)) ≤ x) :
    2 * t / x * b ≤ (1 - 1 / (L : ℝ)) * ey / (5 * L) := by
  set S := √(n * m * min (n : ℝ) (Real.exp 1))
  set T := 2 * √2 * √(n : ℝ) + √(Real.log (96 * n * m / θ))
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl : (20 : ℝ) ≤ ℓ := by exact_mod_cast hl20
  have hL1 : (ℓ : ℝ) ≤ L := by exact_mod_cast hL
  have hL2 : (L : ℝ) ≤ 2 * ℓ := by exact_mod_cast hL₂
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hS0 : 0 < S := Real.sqrt_pos.2 (mul_pos (by positivity) (lt_min hn0 (by positivity)))
  have hT0 : 0 < T := by
    have : 0 < 2 * √2 * √(n : ℝ) := by positivity
    linarith [Real.sqrt_nonneg (Real.log (96 * n * m / θ))]
  have hθs : 0 < √θ := Real.sqrt_pos.2 hθ
  have hx0 : 0 < 39 / 100 * √θ / S := by positivity
  have hden : 0 < 52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) := by nlinarith
  have h1 : 2 * t / x * b ≤ 2 * T / (39 / 100 * √θ / S) * b := by gcongr
  have h2 : 2 * T / (39 / 100 * √θ / S) * b = 200 / 39 * (b * (S * T)) / √θ := by
    field_simp; ring
  have h3 : b * (S * T) ≤ ((ℓ : ℝ) - 1) ^ 2 * e * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1)) := by
    rw [le_div_iff₀ hden]
    rw [le_div_iff₀ (by positivity)] at hble
    linarith
  have h4 : 200 / 39 * (((ℓ : ℝ) - 1) ^ 2 * e * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1))) / √θ ≤
      (1 - 2⁻¹ ^ 8) * ((ℓ : ℝ) - 1) * e / (20 * (ℓ : ℝ) ^ 2) := by
    rw [show 200 / 39 * (((ℓ : ℝ) - 1) ^ 2 * e * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1))) / √θ =
      200 * ((ℓ : ℝ) - 1) ^ 2 * e / (39 * (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1))) by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < ((ℓ : ℝ) - 1) * e * ℓ ^ 2 := by
      have : 0 < (ℓ : ℝ) - 1 := by linarith
      positivity
    nlinarith
  have h5 : (1 - 2⁻¹ ^ 8) * ((ℓ : ℝ) - 1) * e / (20 * (ℓ : ℝ) ^ 2) ≤
      (1 - 1 / (L : ℝ)) * ((1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((L : ℝ) - 1)) * e) / (5 * L) := by
    have hL0 : (L : ℝ) - 1 ≠ 0 := by linarith
    have hL0' : (L : ℝ) ≠ 0 := by linarith
    rw [show (1 - 1 / (L : ℝ)) * ((1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((L : ℝ) - 1)) * e) /
      (5 * L) = (1 - 2⁻¹ ^ 8) * ((ℓ : ℝ) - 1) * e / (5 * (L : ℝ) ^ 2) by field_simp]
    have : 0 ≤ (1 - 2⁻¹ ^ 8) * ((ℓ : ℝ) - 1) * e := by
      have : 0 ≤ (ℓ : ℝ) - 1 := by linarith
      positivity
    exact div_le_div_of_nonneg_left this (by positivity) (by nlinarith)
  have h6 : (1 - 1 / (L : ℝ)) * ((1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((L : ℝ) - 1)) * e) /
      (5 * L) ≤ (1 - 1 / (L : ℝ)) * ey / (5 * L) := by
    have : 0 ≤ 1 - 1 / (L : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    gcongr
  calc 2 * t / x * b ≤ 200 / 39 * (b * (S * T)) / √θ := h1.trans h2.le
    _ ≤ 200 / 39 * (((ℓ : ℝ) - 1) ^ 2 * e * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1))) / √θ := by
        gcongr
    _ ≤ _ := h4.trans (h5.trans h6)

/-- The global hypotheses of Theorem 4.2 give the node budget at every internal node within the
depth and accuracy ranges. -/
private theorem FloatMachine.IsAccurate.isEighNodeBudget_of_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hβ : 0 < dec β)
    (hnβ : n * dec β ≤ dec ε / 104)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω)
    {y : EighNode F} (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) (hkn : y.k ≤ n)
    (hℓy : ℓ ≤ y.ℓ) (hℓy₂ : y.ℓ ≤ 2 * ℓ) (hεy : dec ε / 3 ≤ dec y.ε) (hεy₁ : dec y.ε ≤ dec ε)
    (hεy' : (1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((y.ℓ : ℝ) - 1)) * dec ε ≤ dec y.ε)
    (hRy : dec y.R ≤ dec R₀) (hH : (decodeMatrix dec y.A).IsHermitian)
    (hNy : specNorm (decodeMatrix dec y.A) ≤ dec y.R) :
    M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
      (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
        (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))))) y := by
  set m := min (n : ℝ) (ℓ + 1)
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hkn' : (y.k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : (20 : ℝ) ≤ ℓ := by exact_mod_cast hl20
  have hL1 : (ℓ : ℝ) ≤ y.ℓ := by exact_mod_cast hℓy
  have hL2 : (y.ℓ : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have hm1 : 1 ≤ m := le_min hn1 (by linarith)
  have hεy0 : 0 < dec y.ε := by linarith
  have hu100 : u ≤ 1 / 100 := by
    have : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := one_le_pow₀ (by linarith)
    linarith [mul_le_mul_of_nonneg_right this hu]
  have hlog := Real.sqrt_nonneg (Real.log (96 * n * m / θ))
  have hRpos : 0 < dec y.R := hM.pos_of_le_mul_eq_false hu100 hint hR₀pos hε
    (hε₁.trans (by norm_num)) hεy hεy₁ hτ100
    (by linarith [(by positivity : (0 : ℝ) ≤ 2 * √2 * √(n : ℝ)), hR₀pos.le])
  have hD : 0 < (9 * n * ℓ * (ℓ + 1) : ℝ) := by positivity
  have h12 : (1 : ℝ) ≤ n * ℓ * (ℓ + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 (by linarith)) (by linarith)
  have hw5 : 4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)) / (5 * dec y.R) =
      4 * θ / (45 * n * ℓ * (ℓ + 1)) := by field_simp; ring
  have hw2 : 4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)) / (2 * dec y.R) =
      2 * θ / (9 * n * ℓ * (ℓ + 1)) := by field_simp; ring
  have hkβ : (y.k : ℝ) * dec β ≤ n * dec β := mul_le_mul_of_nonneg_right hkn' hβ.le
  have hNst : newtonSchulzSteps (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)) / (5 * dec y.R))
      (dec β / (16 * y.k)) ≤ Nst := by
    rw [hw5, hN]
    refine (newtonSchulzSteps_le_of_le_abs (a := θ / (12 * n * ℓ * (ℓ + 1)))
      (by positivity) ?_).trans (newtonSchulzSteps_le_of_le (by positivity) ?_ ?_)
    · rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [mul_pos hθ hD]
    · exact div_le_div_of_nonneg_left hβ.le (by positivity) (by linarith)
    · rw [div_le_iff₀ (by positivity)]
      linarith [hε₁.trans (by norm_num : (2⁻¹ : ℝ) ^ 15 ≤ 1), le_mul_of_one_le_left hβ.le hn1]
  have hNy0 : 0 ≤ newtonSchulzSteps (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)) / (5 * dec y.R))
      (dec β / (16 * y.k)) :=
    newtonSchulzSteps_nonneg (by rw [hw5]; positivity)
      (by rw [hw5, div_le_iff₀ (by positivity)]; linarith) (by positivity)
      (by rw [div_le_iff₀ (by positivity)]
          linarith [hε₁.trans (by norm_num : (2⁻¹ : ℝ) ^ 15 ≤ 1), le_mul_of_one_le_left hβ.le hn1])
  have hsk : √(y.k : ℝ) ≤ √n := Real.sqrt_le_sqrt hkn'
  have hμk := hμM₀.trans (hμM (Nat.zero_le y.k))
  have hν : 4 * μM y.k + 10 + 10 * √(y.k : ℝ) ≤ 4 * μM n + 10 + 10 * √(n : ℝ) := by
    linarith [hμM hkn]
  have hν0 : 0 ≤ 4 * μM y.k + 10 + 10 * √(y.k : ℝ) := by positivity
  have ht := add_sqrt_log_le (θ := θ) (m := m) (by omega : 1 ≤ y.k) hkn hθ (by linarith)
  have hx := le_sqrt_div_min (θ := θ) hk hkn hθ hθ₁ hm1
  refine ⟨hμk, hμQ₀.trans (hμQ (Nat.zero_le _)), hcN, hu, hH, hNy, by omega, hεy0,
    by linarith [hε₁.trans (by norm_num : (2⁻¹ : ℝ) ^ 15 ≤ 1 / 8)], hR₀pos, by positivity, ?_,
    by positivity, hx.2.2, le_add_of_nonneg_right (Real.sqrt_nonneg _), hβ,
    mul_div_mul_le_of_le_div hk hkn hℓy hℓy₂ hl20 hε hθ hm1 hβ hεy' hβle ht hx.1, ?_, ?_,
    ?_, by linarith [hε₁.trans (by norm_num : (2⁻¹ : ℝ) ^ 15 ≤ 104 / 57600)], hNst.trans hfuel,
    hτ₀, ?_, ?_⟩
  · have h9 : (4 : ℝ) ≤ 9 * n * ℓ * (ℓ + 1) := by linarith
    rw [div_le_iff₀ hD]
    linarith [mul_le_mul_of_nonneg_left hθ₁ hRpos.le, mul_le_mul_of_nonneg_left h9 hRpos.le]
  · have hX : (0 : ℝ) < n * ℓ * (ℓ + 1) := by positivity
    rw [mul_div_assoc, hw2, show (1 - 2⁻¹ ^ 7) * (2 * θ / (9 * n * ℓ * (ℓ + 1))) * dec β =
      127 * (θ * dec β) / (576 * (n * ℓ * (ℓ + 1))) by field_simp; ring,
      le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hν hu) hX.le
    have h2 : 0 ≤ (4 * μM n + 10 + 10 * √(n : ℝ)) * u * (n * ℓ * (ℓ + 1)) :=
      mul_nonneg (mul_nonneg (hν0.trans hν) hu) hX.le
    linarith
  · refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul ?_ hν hν0 ?_) hu) hustop
    · linarith
    · linarith
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hu) hudefl
    linarith [hμQ hkn, hμM hkn, mul_le_mul_of_nonneg_right hsk (by linarith : (0 : ℝ) ≤ cN + 1)]
  · have hX : τ * (4 * y.k * √(y.k : ℝ)) ≤ τ * (100 * n * √(n : ℝ)) / 25 := by
      rw [le_div_iff₀ (by norm_num)]
      have : τ * (4 * y.k * √(y.k : ℝ)) ≤ τ * (4 * n * √(n : ℝ)) := by gcongr
      linarith
    refine le_min (hX.trans ((div_le_div_of_nonneg_right (hτ.trans (min_le_left _ _))
      (by norm_num)).trans hx.2.1)) (hX.trans ?_)
    have hτ' := hτ.trans (min_le_right _ _)
    linarith [mul_le_mul_of_nonneg_left (min_le_left (dec R₀) 1) hε.le,
      mul_le_mul_of_nonneg_right hεy hR₀pos.le]
  · linarith

/-- The node budget at every internal node of the tree whose matrix is Hermitian and in its
window. -/
private theorem FloatMachine.IsAccurate.isEighNodeBudget_of_eighNodeAt_eq_some
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1)
    (hβ : 0 < dec β) (hnβ : n * dec β ≤ dec ε / 104)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1) (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω)
    (A : Matrix (Fin n) (Fin n) (F × F)) (s : List Bool → EighSample ℝ ℂ n) {a : List Bool}
    {y : EighNode F} (hy : eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false)
    (hH : (decodeMatrix dec y.A).IsHermitian) (hNy : specNorm (decodeMatrix dec y.A) ≤ dec y.R) :
    M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
      (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
        (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))))) y := by
  obtain ⟨hlen, hkn, hLy, hεy, hεy₁, hRy⟩ :=
    hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s hy
  exact hM.isEighNodeBudget_of_le hu hμM hμQ hμM₀ hμQ₀ hcN hn hR₀pos hε hε₁ hθ hθ₁ hl20 hu₁ hβ
    hnβ hβle hN husign hustop hudefl hfuel hτ₀ hτ hτ100 hΩ hk hint hkn (by omega) (by omega) hεy
    hεy₁ (hM.mul_le_dec_ε_of_eighNodeAt_eq_some hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s hy)
    hRy hH hNy

/-- Good samples at the internal nodes with a node budget are good samples at all internal nodes:
the Hermitian invariant, hence the budget, propagates down the tree. -/
private theorem FloatMachine.IsAccurate.isEighGoodSample_of_forall_isEighNodeBudget_imp
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {R₀ ε β : F} {θ : ℝ}
    (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1)
    (hβ : 0 < dec β) (hnβ : n * dec β ≤ dec ε / 104)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1) (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω)
    {s : List Bool → EighSample ℝ ℂ n}
    (hS : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel
          (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
          (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
            (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
          (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))))))
          y →
        IsEighGoodSample dec (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
          (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
            (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
          (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))))))
          y (s a)) :
    ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
          (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
            (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
          (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))))))
          y (s a) := by
  have hB := fun {a : List Bool} {y : EighNode F} hy hk hint hH hNy =>
    hM.isEighNodeBudget_of_eighNodeAt_eq_some (a := a) (y := y) hu hμM hμQ hμM₀ hμQ₀ hcN hn
      hR₀pos hε hε₁ hθ hθ₁ hℓ hl20 hu₁ hβ hnβ hβle hN husign hustop hudefl hfuel hτ₀ hτ hτ100
      hΩ16 hΩ A s hy hk hint hH hNy
  have hinv : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y →
        (decodeMatrix dec y.A).IsHermitian ∧ specNorm (decodeMatrix dec y.A) ≤ dec y.R := by
    intro a
    induction a using List.reverseRecOn with
    | nil =>
      intro y hy
      simp only [eighNodeAt, Option.some.injEq] at hy
      subst hy
      exact ⟨hA, hR₀⟩
    | append_singleton a b ih =>
      intro y hy
      rw [eighNodeAt_append_singleton] at hy
      obtain ⟨z, hz, hzy⟩ := Option.bind_eq_some_iff.1 hy
      obtain ⟨hH, hNz⟩ := ih z hz
      obtain ⟨hk, hint, -⟩ := le_eq_false_and_le_and_eq_of_eighChild_eq_some hzy
      have hBz := hB hz hk hint hH hNz
      exact hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hBz
        (fun _ _ => hS a z hz hk hint hBz) hzy
  intro a y hy hk hint
  obtain ⟨hH, hNy⟩ := hinv a y hy
  exact hS a y hy hk hint (hB hy hk hint hH hNy)

/-- A sum over paths regrouped by depth. -/
private theorem tsum_list_bool_eq_tsum_sum_ofFn (f : List Bool → ℝ≥0∞) :
    ∑' a, f a = ∑' j, ∑ v : Fin j → Bool, f (List.ofFn v) := by
  rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma']
  exact tsum_congr fun j => tsum_fintype _

/-- The sizes at depth $j$ sum to at most $n$, and to $0$ below depth $\ell$. -/
private theorem FloatMachine.IsAccurate.sum_k_eighNodeAt_ofFn_le_ite
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ}
    {signFuel : ℕ} {R₀ ε β : F} (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 2⁻¹ ^ 15) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u)
    (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω) (A : Matrix (Fin n) (Fin n) (F × F))
    (s : List Bool → EighSample ℝ ℂ n) (j : ℕ) :
    ∑ v : Fin j → Bool, (((eighNodeAt M n signFuel R₀ β (List.ofFn v) ⟨n, A, R₀, ε, ℓ⟩ s).elim 0
      EighNode.k : ℕ) : ℝ≥0∞) ≤ if j ≤ ℓ then (n : ℝ≥0∞) else 0 := by
  split_ifs with hj
  · exact_mod_cast sum_k_eighNodeAt_ofFn_le M ⟨n, A, R₀, ε, ℓ⟩ s j
  · refine le_of_eq (Finset.sum_eq_zero fun v _ => ?_)
    rcases hX : eighNodeAt M n signFuel R₀ β (List.ofFn v) ⟨n, A, R₀, ε, ℓ⟩ s with _ | y
    · simp
    · have := (hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s hX).1
      simp only [List.length_ofFn] at this
      omega

/-- The depths $0, \dots, \ell$ sum to $\ell(\ell + 1)/2$. -/
private theorem sum_range_succ_natCast_eq (L : ℕ) :
    ∑ j ∈ Finset.range (L + 1), (j : ℝ) = L * (L + 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The Event I charges along every run of the tree sum to at most $\tfrac23\theta$. -/
private theorem FloatMachine.IsAccurate.tsum_eighNodeAt_ofReal_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ} (hn : 1 ≤ n)
    {signFuel : ℕ} {R₀ ε β : F} {θ : ℝ} (hθ : 0 < θ) (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 2⁻¹ ^ 15) {ℓ : ℕ} (hl : 1 ≤ ℓ) (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u)
    (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω) (A : Matrix (Fin n) (Fin n) (F × F))
    (s : List Bool → EighSample ℝ ℂ n) :
    ∑' a, (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y =>
      ENNReal.ofReal (4 * θ / (9 * n * ℓ * (ℓ + 1)) * y.ℓ) * (y.k : ℝ≥0∞)) ≤
      ENNReal.ofReal (2 / 3 * θ) := by
  set c := 4 * θ / (9 * n * ℓ * (ℓ + 1))
  have hc : 0 ≤ c := by positivity
  rw [tsum_list_bool_eq_tsum_sum_ofFn]
  have hj : ∀ j, ∑ v : Fin j → Bool,
      (eighNodeAt M n signFuel R₀ β (List.ofFn v) ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y =>
        ENNReal.ofReal (c * y.ℓ) * (y.k : ℝ≥0∞)) ≤
      if j ≤ ℓ then ENNReal.ofReal (c * (ℓ + j)) * n else 0 := by
    intro j
    have h := hM.sum_k_eighNodeAt_ofFn_le_ite (signFuel := signFuel) (β := β) hR₀pos hε hε₁ hℓ
      hu hu₁ hτ₀ hτ100 hΩ16 A s j
    have heq : ∀ v : Fin j → Bool,
        (eighNodeAt M n signFuel R₀ β (List.ofFn v) ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y =>
          ENNReal.ofReal (c * y.ℓ) * (y.k : ℝ≥0∞)) = ENNReal.ofReal (c * (ℓ + j)) *
        (((eighNodeAt M n signFuel R₀ β (List.ofFn v) ⟨n, A, R₀, ε, ℓ⟩ s).elim 0
          EighNode.k : ℕ) : ℝ≥0∞) := by
      intro v
      rcases hX : eighNodeAt M n signFuel R₀ β (List.ofFn v) ⟨n, A, R₀, ε, ℓ⟩ s with _ | y
      · simp
      · have := (hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s
          hX).2.2.1
        simp only [List.length_ofFn] at this
        simp only [Option.elim_some, this]
        push_cast
        rfl
    rw [Finset.sum_congr rfl fun v _ => heq v, ← Finset.mul_sum]
    split_ifs at h ⊢
    · gcongr
    · exact le_of_eq (by rw [nonpos_iff_eq_zero.1 h, mul_zero])
  refine (ENNReal.tsum_le_tsum hj).trans (le_of_eq ?_)
  rw [tsum_eq_sum (s := Finset.range (ℓ + 1)) fun j hj => by
    rw [Finset.mem_range] at hj; rw [if_neg (by omega)]]
  rw [Finset.sum_congr rfl fun j hj => if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)),
    Finset.sum_congr rfl fun (j : ℕ) _ => (by rw [← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_mul (by positivity)] : ENNReal.ofReal (c * (ℓ + (j : ℝ))) * (n : ℝ≥0∞) =
        ENNReal.ofReal (c * (ℓ + (j : ℝ)) * n)),
    ← ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
  congr 1
  rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib, sum_range_succ_natCast_eq]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                           linarith
  have : (ℓ : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hl
                           linarith
  simp only [c]
  push_cast
  field_simp
  ring

/-- The sizes of the split nodes sum to at most $n\min(n, \ell + 1)$. -/
private theorem FloatMachine.IsAccurate.tsum_eighNodeAt_isSplit_k_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ}
    {signFuel : ℕ} {R₀ ε β : F} (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 2⁻¹ ^ 15) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u)
    (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω) (A : Matrix (Fin n) (Fin n) (F × F))
    (s : List Bool → EighSample ℝ ℂ n) :
    ∑' a, (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y => (y.k : ℝ≥0∞) *
      {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}.indicator 1 (s a)) ≤
      ((n * min n (ℓ + 1) : ℕ) : ℝ≥0∞) := by
  set K := fun a => (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y =>
    (y.k : ℝ≥0∞) * {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}.indicator 1 (s a))
  have h1 : ∑' a, K a ≤ ((n * (ℓ + 1) : ℕ) : ℝ≥0∞) := by
    have hK : ∀ a, K a ≤ (((eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0
        EighNode.k : ℕ) : ℝ≥0∞) := by
      intro a
      simp only [K]
      rcases eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s with _ | y
      · simp
      · simp only [Option.elim_some]
        exact mul_le_of_le_one_right zero_le (Set.indicator_le_self' (fun _ _ => zero_le) _)
    refine (ENNReal.tsum_le_tsum hK).trans ?_
    rw [tsum_list_bool_eq_tsum_sum_ofFn]
    refine (ENNReal.tsum_le_tsum fun j => hM.sum_k_eighNodeAt_ofFn_le_ite (signFuel := signFuel)
      (β := β) hR₀pos hε hε₁ hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s j).trans (le_of_eq ?_)
    rw [tsum_eq_sum (s := Finset.range (ℓ + 1)) fun j hj => by
      rw [Finset.mem_range] at hj; rw [if_neg (by omega)]]
    rw [Finset.sum_congr rfl fun j hj => if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have h2 : ∑' a, K a ≤ ((n * n : ℕ) : ℝ≥0∞) := by
    have hK : ∀ a, K a ≤ {a : List Bool | ∃ y, eighNodeAt M n signFuel R₀ β a
        ⟨n, A, R₀, ε, ℓ⟩ s = some y ∧
        (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.indicator
          (fun _ => (n : ℝ≥0∞)) a := by
      intro a
      simp only [K]
      rcases hX : eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s with _ | y
      · simp
      · simp only [Option.elim_some]
        by_cases hsp : (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit
        · have hm1 : s a ∈ {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit} := hsp
          have hm2 : a ∈ {a : List Bool | ∃ y, eighNodeAt M n signFuel R₀ β a
              ⟨n, A, R₀, ε, ℓ⟩ s = some y ∧
              (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit} := ⟨y, hX, hsp⟩
          rw [Set.indicator_of_mem hm2, Set.indicator_of_mem hm1, Pi.one_apply, mul_one]
          exact_mod_cast (hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16
            A s hX).2.1
        · have hm1 : s a ∉ {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit} := hsp
          rw [Set.indicator_of_notMem hm1, mul_zero]
          exact zero_le
    refine (ENNReal.tsum_le_tsum hK).trans ?_
    rw [← tsum_subtype, ENNReal.tsum_set_const]
    have e2 := encard_eighNodeAt_isSplit_le M (signFuel := signFuel) (R₀ := R₀) (β := β)
      ⟨n, A, R₀, ε, ℓ⟩ s
    push_cast
    gcongr
    exact_mod_cast e2
  rcases le_total n (ℓ + 1) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- The charges along every run of the tree sum to at most $\theta$: $\tfrac23\theta$ for Event I
and $\tfrac13\theta$ for the splits. -/
private theorem FloatMachine.IsAccurate.tsum_eighNodeAt_charge_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ} (hn : 1 ≤ n)
    {signFuel : ℕ} {R₀ ε β : F} {θ : ℝ} (hθ : 0 < θ) (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 2⁻¹ ^ 15) {ℓ : ℕ} (hl : 1 ≤ ℓ) (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u)
    (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω) (A : Matrix (Fin n) (Fin n) (F × F))
    (V : EighNode F → Prop) [DecidablePred V] (s : List Bool → EighSample ℝ ℂ n) :
    ∑' a, (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y => if V y then
      ENNReal.ofReal (y.k * (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1))) * y.ℓ / dec y.R) +
        ENNReal.ofReal (2 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))) *
          {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}.indicator 1 (s a)
      else 0) ≤ ENNReal.ofReal θ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (0 : ℝ) < min (n : ℝ) (ℓ + 1) := lt_min hn' (by positivity)
  set d := θ / (3 * n * min (n : ℝ) (ℓ + 1))
  have hle : ∀ a, (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y => if V y then
      ENNReal.ofReal (y.k * (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1))) * y.ℓ / dec y.R) +
        ENNReal.ofReal (2 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))) *
          {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}.indicator 1 (s a)
      else 0) ≤ (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y =>
        ENNReal.ofReal (4 * θ / (9 * n * ℓ * (ℓ + 1)) * y.ℓ) * (y.k : ℝ≥0∞)) +
      ENNReal.ofReal d * (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y =>
        (y.k : ℝ≥0∞) *
          {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}.indicator 1 (s a)) := by
    intro a
    rcases eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s with _ | y
    · simp
    simp only [Option.elim_some]
    split_ifs
    · refine add_le_add ?_ (le_of_eq ?_)
      · rw [← ENNReal.ofReal_natCast y.k, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases eq_or_ne (dec y.R) 0 with h | h
        · rw [h, div_zero]
          positivity
        · exact le_of_eq (by field_simp)
      · rw [← mul_assoc, ← ENNReal.ofReal_natCast y.k, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        simp only [d]
        field_simp
        ring
    · exact zero_le
  refine (ENNReal.tsum_le_tsum hle).trans ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
  refine (add_le_add (hM.tsum_eighNodeAt_ofReal_mul_le hn hθ hR₀pos hε hε₁ hl hℓ hu hu₁ hτ₀
    hτ100 hΩ16 A s) (mul_le_mul_right (hM.tsum_eighNodeAt_isSplit_k_le hR₀pos hε hε₁ hℓ hu hu₁
      hτ₀ hτ100 hΩ16 A s) _)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [d]
  push_cast
  field_simp
  ring

/-- The sample law is a probability measure. -/
private theorem isProbabilityMeasure_eighSampleLaw (N : ℕ) :
    IsProbabilityMeasure (eighSampleLaw N) := by
  unfold eighSampleLaw
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by simp [Real.volume_Icc])
      (by simp [Real.volume_Icc])
  infer_instance

/-- The node bound at the charge of Theorem 4.2, in integral form. -/
private theorem FloatMachine.IsAccurate.eighSampleLaw_not_isEighGoodSample_le_lintegral
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable) {n signFuel : ℕ} {R₀ β : F} {θ w : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} {y : EighNode F}
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w
      (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
        (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))))) y)
    (hk : 2 ≤ y.k) (hkn : y.k ≤ n) (hint : M.le y.R (M.mul y.ε R₀) = false) :
    eighSampleLaw n {z | ¬ IsEighGoodSample dec w
      (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
        (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))))) y z} ≤
      ∫⁻ z, (ENNReal.ofReal (y.k * w * y.ℓ / dec y.R) +
        ENNReal.ofReal (2 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))) *
          {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}.indicator 1 z)
        ∂(eighSampleLaw n) := by
  have := isProbabilityMeasure_eighSampleLaw n
  have hs := measurableSet_setOf_eighStep_isSplit hunifm hunifc n signFuel R₀ β y.A y.R y.ε y.ℓ
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ (measurable_one.indicator hs), lintegral_indicator_one hs]
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hkn' : (y.k : ℝ) ≤ n := by exact_mod_cast hkn
  have hm1 : (1 : ℝ) ≤ min (n : ℝ) (ℓ + 1) :=
    le_min (by linarith) (by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)])
  have hD : (0 : ℝ) < 6 * n * min (n : ℝ) (ℓ + 1) :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  refine hM.measure_not_isEighGoodSample_le_of_isEighNodeBudget hB hk hkn hint
    (div_pos (mul_pos hθ (by linarith)) hD) ?_
  rw [div_le_one hD]
  have := mul_le_mul hθ₁ hkn' (by positivity) zero_le_one
  nlinarith

/-- Theorem 4.2 for measurable samples. -/
private theorem FloatMachine.IsAccurate.measureReal_eigh_le_of_measurable
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hζ : ∀ a, Measurable (ζ a)) (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  classical
  obtain ⟨hu, -, hl20, hnβ, hu₁, hτ100, hΩ16⟩ := hM.nonneg_and_one_le_and_mul_le hμM hμM₀
    hR₀pos hε hε₁ hθ₁ hℓ hβ hβle husign hτ₀ hτ hΩ
  have := isProbabilityMeasure_eighSampleLaw n
  have : IsProbabilityMeasure μ := (hlaw []).isProbabilityMeasure_iff.2 this
  let W : EighNode F → ℝ := fun y => 4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1))
  let ρ : EighNode F → ℝ := fun y => θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))
  let Xt : EighNode F → ℝ := fun y =>
    √(15 * ρ y / (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k)))
  let T : EighNode F → ℝ := fun y => 2 * √2 * √(y.k : ℝ) + √(Real.log (16 / ρ y))
  let V : EighNode F → Prop := fun y => 2 ≤ y.k ∧ M.le y.R (M.mul y.ε R₀) = false ∧ y.k ≤ n ∧
    M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel (W y) (Xt y) (T y) y
  let G : EighNode F → EighSample ℝ ℂ n → Prop := fun y z =>
    IsEighGoodSample dec (W y) (Xt y) (T y) y z
  let Spl : EighNode F → Set (EighSample ℝ ℂ n) := fun y =>
    {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}
  let X : List Bool → Ω' → Option (EighNode F) := fun a ω =>
    eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ fun b => ζ b ω
  have hsub : {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ⊆ {ω | ∃ a, ζ a ω ∈ {z | ∃ y, X a ω = some y ∧ V y ∧ ¬ G y z}} := by
    intro ω hω
    by_contra hne
    apply hω
    refine hM.isApproxDiagonalization_eigh_of_forall_isEighGoodSample hu hμM hμQ hμM₀ hμQ₀ hcN
      hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN husign hustop hudefl hfuel hτ₀ hτ hΩ ?_
    refine hM.isEighGoodSample_of_forall_isEighNodeBudget_imp hu hμM hμQ hμM₀ hμQ₀ hcN hn hA hR₀
      hR₀pos hε hε₁ hθ hθ₁ hℓ hl20 hu₁ hβ hnβ hβle hN husign hustop hudefl hfuel hτ₀ hτ hτ100
      hΩ16 hΩ ?_
    intro a y hy hk hint hB
    have hkn := (hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A _ hy).2.1
    by_contra hbad
    exact hne ⟨a, y, hy, ⟨hk, hint, hkn, hB⟩, hbad⟩
  refine (measureReal_mono hsub).trans ?_
  refine measureReal_exists_mem_le_of_forall_measure_le_lintegral hlaw (X := X)
    (fun a => (countable_range_eighNodeAt hunifc hnormalc n signFuel R₀ β a _).mono
      (by rintro _ ⟨ω, rfl⟩; exact ⟨_, rfl⟩))
    (fun a y => measurableSet_eighNodeAt_eq hunifm hunifc hnormalm hnormalc hζ a _ y)
    (fun a y => indepFun_eighNodeAt_eq hunifm hunifc hnormalm hnormalc hζ hind a _ y)
    (S := fun _ oy => {z | ∃ y, oy = some y ∧ V y ∧ ¬ G y z})
    (q := fun _ oy z => oy.elim 0 fun y => if V y then
      ENNReal.ofReal (y.k * W y * y.ℓ / dec y.R) + ENNReal.ofReal (2 * ρ y) *
        (Spl y).indicator 1 z else 0)
    ?_ ?_ hθ.le ?_
  · intro a oy
    rcases oy with _ | y
    · simp only [Option.elim_none]
      exact measurable_const
    · simp only [Option.elim_some]
      split_ifs
      · exact measurable_const.add (((measurable_const : Measurable fun _ :
          EighSample ℝ ℂ n => (1 : ℝ≥0∞)).indicator
          (measurableSet_setOf_eighStep_isSplit hunifm hunifc n signFuel R₀ β y.A y.R y.ε
            y.ℓ)).const_mul _)
      · exact measurable_const
  · intro a oy
    rcases oy with _ | y
    · simp
    by_cases hV : V y
    · have hS : {z | ∃ y', some y = some y' ∧ V y' ∧ ¬ G y' z} = {z | ¬ G y z} := by
        ext z
        simp only [Set.mem_ofPred_eq, Option.some.injEq]
        constructor
        · rintro ⟨y', rfl, -, hg⟩
          exact hg
        · exact fun hg => ⟨y, rfl, hV, hg⟩
      rw [hS]
      simp only [Option.elim_some, if_pos hV]
      obtain ⟨hk, hint, hkn, hB⟩ := hV
      exact hM.eighSampleLaw_not_isEighGoodSample_le_lintegral hunifm hunifc hθ hθ₁ hB hk hkn hint
    · have hS : {z | ∃ y', some y = some y' ∧ V y' ∧ ¬ G y' z} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Option.some.injEq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, rfl, hV', -⟩
        exact hV hV'
      rw [hS, measure_empty]
      exact zero_le
  · exact fun ω => hM.tsum_eighNodeAt_charge_le hn hθ hR₀pos hε hε₁ (by omega) hℓ hu hu₁ hτ₀
      hτ100 hΩ16 A V (fun b => ζ b ω)

-- A docstring line exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Hermitian diagonalization in linear precision** (Theorem 4.2): let the machine meet
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ (constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$, $c_{\mathrm N}$), with $\mu_{\mathrm{MM}}, \mu_{\mathrm{QR}}$ monotone
and nonnegative, $c_{\mathrm N} \ge 0$, and the samplers with measurable fibres and countable
ranges. Let the stored $n \times n$ input $\mathbf{A}$, $n \ge 1$, have Hermitian decoding
with $\|\mathbf{A}\|_2 \le R_0$, for stored $R_0 > 0$, $\varepsilon$, $\beta$ (decoded values)
with $0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, a depth counter
$\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$, $m = \min(n, \ell + 1)$,
$\nu = 4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n$, and the precomputed accuracy
$$0 < \beta \le \hat\beta = \frac{(\ell - 1)^2\,\varepsilon\sqrt\theta}{52\,\ell^2(2\ell - 1)
\sqrt{n m \min(n, e)}\,\hat T} \,, \qquad \hat T = 2\sqrt2\sqrt n +
\sqrt{\log(96nm/\theta)} \,,$$
$N_* = N(\theta/(12n\ell(\ell + 1)), \beta/(16n))$ (`NLAlib.newtonSchulzSteps`). If
$146n\ell(\ell + 1)\nu u \le \theta\beta$ (the sign function), $2048(n + N_* + 1)\nu u \le \beta$
(the stopping test), $16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) +
2\mu_{\mathrm{MM}}(n) + 1)u \le \beta$ (deflation), the sign step limit is at least $N_*$,
$0 \le \tau$, $100n^{3/2}\tau \le \min(\sqrt{\theta/(8nm)}, \varepsilon\min(R_0, 1))$,
$16(2R_0 + n + 2\ell + \hat T) \le \Omega$, and the node samples $\zeta_a$ are independent, each
of law `NLAlib.eighSampleLaw` $n$, then
$$\mathbb{P}\bigl[\mathsf{eigh}(\mathbf{A}, \varepsilon, \theta) \text{ is not an approximate
diagonalization with residual } 2\varepsilon R_0 \text{ and } \mathbf{U} \text{ within }
\varepsilon/3 \text{ of unitary}\bigr] \le \theta \,,$$
$\mathsf{eigh}$ the decoded output of `NLAlib.eigh`. [Shah2024, Theorem 4.2], there with
$R_0 = \|\mathbf{A}\|_2$, node-dependent accuracies, other constants (here the Event I charge of
a node is proportional to its size and Event II uses the smallest-singular-value tail
$\min(r^2, e r)x^2$), and an operation count (not formalized); the bit count is
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw`.
Result: spectral-bisection-diagonalization -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  have hae : ∀ᵐ ω ∂μ, ∀ a, ζ a ω = (hlaw a).aemeasurable.mk (ζ a) ω :=
    ae_all_iff.2 fun a => (hlaw a).aemeasurable.ae_eq_mk
  refine le_of_eq_of_le (measureReal_congr (Filter.eventuallyEq_set.2 ?_))
    (hM.measureReal_eigh_le_of_measurable hunifm hunifc hnormalm hnormalc hμM hμQ hμM₀ hμQ₀ hcN
      hn hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN husign hustop hudefl hfuel hτ₀ hτ hΩ
      (fun a => (hlaw a).aemeasurable.measurable_mk)
      ((iIndepFun_congr fun a => (hlaw a).aemeasurable.ae_eq_mk).1 hind)
      fun a => (hlaw a).congr (hlaw a).aemeasurable.ae_eq_mk.symm)
  filter_upwards [hae] with ω hω
  have h2 : (fun a => ζ a ω) = fun a => (hlaw a).aemeasurable.mk (ζ a) ω := funext hω
  simp only [h2]

/-- Exponentiating the first bit-count condition of Theorem 4.2. -/
private theorem mul_le_mul_mul_sqrt_mul_of_logb_le {e θ P X T L Q u : ℝ} (he : 0 < e)
    (hθ : 0 < θ) (hP : 0 < P) (hX : 0 < X) (hT : 0 < T) (hL : 0 < L) (hQ : 0 < Q) (hu : 0 < u)
    (h : Real.logb 2 e⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ + Real.logb 2 P + 1 / 2 * Real.logb 2 X +
      Real.logb 2 T + Real.logb 2 L + Real.logb 2 Q + 13 ≤ Real.logb 2 u⁻¹) :
    u * (2 ^ 13 * P * √X * T * L * Q) ≤ e * (θ * √θ) := by
  have hsθ : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hsX : 0 < √X := Real.sqrt_pos.mpr hX
  have hK : 2 ^ 13 * P * √X * T * L * Q / (e * (θ * √θ)) ≤ u⁻¹ := by
    rw [← Real.logb_le_logb one_lt_two (by positivity) (by positivity), Real.logb_div
      (by positivity) (by positivity), Real.logb_mul (by positivity) hQ.ne',
      Real.logb_mul (by positivity) hL.ne', Real.logb_mul (by positivity) hT.ne',
      Real.logb_mul (by positivity) hsX.ne', Real.logb_mul (by positivity) hP.ne',
      Real.logb_mul he.ne' (by positivity), Real.logb_mul hθ.ne' hsθ.ne', Real.logb_pow,
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hθ,
      Real.logb_rpow_eq_mul_logb_of_pos hX, Real.logb_self_eq_one one_lt_two]
    rw [Real.logb_inv, Real.logb_inv] at h
    push_cast
    linarith
  rw [div_le_iff₀ (by positivity)] at hK
  calc u * (2 ^ 13 * P * √X * T * L * Q) ≤ u * (u⁻¹ * (e * (θ * √θ))) :=
        mul_le_mul_of_nonneg_left hK hu.le
    _ = e * (θ * √θ) := by rw [← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]

/-- The exponentiated first bit-count condition and the lower bound on $\beta$ give the
sign-function condition of Theorem 4.2. -/
private theorem mul_le_mul_of_mul_le_mul_sqrt {P D T L l e θ b u : ℝ} (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hl : 0 < l - 1) (hθ : 0 < θ) (hu : 0 ≤ u)
    (hc : 0 < 52 * l ^ 2 * (2 * l - 1) * D * T)
    (key : u * (2 ^ 13 * P * D * T * L * (l ^ 2 * (2 * l - 1) / (l - 1) ^ 2)) ≤ e * (θ * √θ))
    (hβge : (l - 1) ^ 2 * e * √θ / (52 * l ^ 2 * (2 * l - 1) * D * T) / (1 + 2⁻¹ ^ 6) ≤ b) :
    146 * P * L * u ≤ θ * b := by
  have hQ : l ^ 2 * (2 * l - 1) / (l - 1) ^ 2 * (l - 1) ^ 2 = l ^ 2 * (2 * l - 1) :=
    div_mul_cancel₀ _ (by positivity)
  have hl1 : 0 ≤ 2 * l - 1 := by linarith
  rw [div_div, div_le_iff₀ (by positivity)] at hβge
  refine le_of_mul_le_mul_right ?_ (mul_pos hc (by norm_num : (0 : ℝ) < 1 + 2⁻¹ ^ 6))
  have k2 := mul_le_mul_of_nonneg_right key (sq_nonneg (l - 1))
  have k3 := mul_le_mul_of_nonneg_left hβge hθ.le
  have hν : 0 ≤ P * D * T * L * (l ^ 2 * (2 * l - 1)) * u := by positivity
  calc 146 * P * L * u * (52 * l ^ 2 * (2 * l - 1) * D * T * (1 + 2⁻¹ ^ 6))
      = 146 * 52 * (1 + 2⁻¹ ^ 6) * (P * D * T * L * (l ^ 2 * (2 * l - 1)) * u) := by ring
    _ ≤ 2 ^ 13 * (P * D * T * L * (l ^ 2 * (2 * l - 1)) * u) :=
        mul_le_mul_of_nonneg_right (by norm_num) hν
    _ = u * (2 ^ 13 * P * D * T * L * (l ^ 2 * (2 * l - 1) / (l - 1) ^ 2)) * (l - 1) ^ 2 := by
        linear_combination (-(u * 2 ^ 13 * P * D * T * L)) * hQ
    _ ≤ e * (θ * √θ) * (l - 1) ^ 2 := k2
    _ = θ * ((l - 1) ^ 2 * e * √θ) := by ring
    _ ≤ _ := by linarith

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **The bit count of Hermitian diagonalization** (Theorem 4.2, in bits): let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u > 0$, monotone $\mu_{\mathrm{MM}}, \mu_{\mathrm{QR}} \ge
0$, $c_{\mathrm N} \ge 0$ and samplers with measurable fibres and countable ranges; let the stored
$n \times n$ input $\mathbf{A}$, $n \ge 1$, be Hermitian with $\|\mathbf{A}\|_2 \le R_0$, $R_0 > 0$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$ and $\ell \ge$ `NLAlib.bisectionDepth`
$\varepsilon$; let $m = \min(n, \ell + 1)$, $\nu = 4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n$,
$N_* =$ `NLAlib.newtonSchulzSteps` $(\theta/(12n\ell(\ell + 1)))\,(\beta/(16n))$ be at most the
step limit, the floor $0 \le \tau$ with $100n^{3/2}\tau \le \min(\sqrt{\theta/(8nm)},
\varepsilon\min(R_0, 1))$, the range $16(2R_0 + n + 2\ell + \hat T) \le \Omega$, the ideal samples
of the nodes independent with law `NLAlib.eighSampleLaw` $n$, the accuracy within $1 + 2^{-6}$
of its bound, $\hat\beta/(1 + 2^{-6}) \le \beta \le \hat\beta = (\ell - 1)^2\varepsilon\sqrt\theta/
(52\ell^2(2\ell - 1)\sqrt{nm\min(n, e)}\,\hat T)$, and
$$\begin{aligned}\log_2\frac1u \ge{}& \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta +
\log_2\bigl(n(4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n)\bigr) +
\tfrac12\log_2\bigl(n\min(n, \ell + 1)\min(n, e)\bigr) \\ &+ \log_2\hat T + \log_2(\ell(\ell + 1)) +
\log_2\frac{\ell^2(2\ell - 1)}{(\ell - 1)^2} + 13 \,,\end{aligned}$$
$\hat T = 2\sqrt2\sqrt n + \sqrt{\log(96n\min(n, \ell + 1)/\theta)}$, together with the
condition $\log_2(1/u) \ge \log_2(1/\beta) + \log_2(2048(n + N_* + 1)\nu +
16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1))$, the
probability that $\mathsf{eigh}(\mathbf{A}, \varepsilon, \theta)$, the decoded output of
`NLAlib.eigh`, is not an approximate diagonalization with residual $2\varepsilon R_0$ and
singular values within $\varepsilon/3$ of $1$ is at most $\theta$. This is
$\log_2(1/\varepsilon) + \tfrac32\log_2(1/\theta) + O(\log n + \log\log(1/\varepsilon))$ bits,
with the polynomial factor $n^{2.5}\max(\mu_{\mathrm{MM}}, \sqrt n)$ for $n \le \ell$; at
$\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$, $c_{\mathrm N} = \sqrt2$,
$\ell = \lceil\log_2(1/\varepsilon)\rceil + 5$, and the nontrivial failure allowance
$\theta=1/2$, the two displayed conditions ask for approximately 50.8, 54.2, 81.2 and 110.1
bits at $(n, \varepsilon) = (1, 2^{-15})$, $(2, 2^{-15})$, $(1024, 2^{-15})$,
$(1000, 2^{-40})$, choosing $\beta$ at the upper endpoint of its window. These are sufficient
rounded-black-box precision budgets; they do not establish finite-word program success.
[Shah2024, Theorem 4.2], there
$\log_2(1/\varepsilon) + \log_2\max(n^{1.5}\mu_{\mathrm{QR}}, n^2c_{\mathrm N},
n^{4.5}\mu_{\mathrm{MM}}) + 2\log_2\log_2(1/\varepsilon) + 1.5\log_2(1/\theta) +
\log_2\log_2(n\log_2(1/\varepsilon)/\theta) + 23$; the third power of $\ell$ comes from the
corrected shift-avoidance probability.
Result: spectral-bisection-diagonalization-bits -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))))
    (hβge : ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))) /
      (1 + 2⁻¹ ^ 6) ≤ dec β) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hu : 0 < u)
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n * (4 * μM n + 10 + 10 * √(n : ℝ))) +
      1 / 2 * Real.logb 2 (n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) +
      Real.logb 2 (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) +
      Real.logb 2 (ℓ * (ℓ + 1)) + Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) +
      13 ≤ Real.logb 2 u⁻¹)
    (hbits' : Real.logb 2 (dec β)⁻¹ +
      Real.logb 2 (2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) +
      16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) ≤ Real.logb 2 u⁻¹)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ5 : (5 : ℝ) ≤ ℓ := by
    have : 5 ≤ ℓ := le_trans (Nat.le_add_left 5 _) hℓ
    exact_mod_cast this
  have hμMn : 0 ≤ μM n := hμM₀.trans (hμM (Nat.zero_le n))
  have hμQn : 0 ≤ μQ n := hμQ₀.trans (hμQ (Nat.zero_le n))
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hX1 : 1 ≤ n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1) := by
    have h1 : 1 ≤ min (n : ℝ) (ℓ + 1) := le_min hn1 (by linarith)
    have h2 : 1 ≤ min (n : ℝ) (Real.exp 1) := le_min hn1 (Real.one_le_exp zero_le_one)
    nlinarith [mul_le_mul h1 h2 zero_le_one (by linarith)]
  have hD1 : 1 ≤ √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) :=
    Real.one_le_sqrt.mpr hX1
  have hT1 : 1 ≤ 2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)) := by
    have : 1 ≤ √(2 : ℝ) := Real.one_le_sqrt.mpr one_le_two
    nlinarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))]
  have hsθ : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hsθ1 : √θ ≤ 1 := Real.sqrt_le_one.mpr hθ₁
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  set D := √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) with hDdef
  set T := 2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)) with hTdef
  have hc : 0 < 52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) * D * T := by
    have : 0 < 2 * (ℓ : ℝ) - 1 := by linarith
    positivity
  have hβ1 : dec β ≤ 1 := by
    refine hβle.trans ((div_le_one hc).mpr ?_)
    have h1 : ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ ≤ (ℓ : ℝ) ^ 2 := by
      rw [mul_assoc]
      calc _ ≤ ((ℓ : ℝ) - 1) ^ 2 := mul_le_of_le_one_right (sq_nonneg _)
            (mul_le_one₀ hε1 hsθ.le hsθ1)
        _ ≤ (ℓ : ℝ) ^ 2 := by gcongr <;> linarith
    have h2 : 1 ≤ 52 * (2 * (ℓ : ℝ) - 1) * D * T :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hD1) hT1
    calc _ ≤ (ℓ : ℝ) ^ 2 := h1
      _ ≤ (ℓ : ℝ) ^ 2 * (52 * (2 * (ℓ : ℝ) - 1) * D * T) := le_mul_of_one_le_right (sq_nonneg _) h2
      _ = _ := by ring
  have hNst : 0 ≤ Nst := by
    have h12 : 1 ≤ (n : ℝ) * ℓ * (ℓ + 1) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 (by linarith))
        (by linarith)
    rw [hN]
    refine newtonSchulzSteps_nonneg (by positivity) ?_ (by positivity) ?_
    · rw [div_le_iff₀ (by positivity)]; linarith
    · rw [div_le_iff₀ (by positivity)]; linarith
  -- the second condition: `S * u ≤ β` with `S` the sum of the stopping and deflation terms
  have hS : (2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) +
      16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) * u ≤ dec β := by
    have hS0 : 0 < 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) +
        16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) := by positivity
    rw [Real.logb_inv, ← sub_eq_neg_add, ← Real.logb_div hS0.ne' hβ.ne',
      Real.logb_le_logb one_lt_two (by positivity) (by positivity), div_le_iff₀ hβ] at hbits'
    calc _ ≤ (u⁻¹ * dec β) * u := mul_le_mul_of_nonneg_right hbits' hu.le
      _ = dec β := by field_simp
  have hl1 : 0 < 2 * (ℓ : ℝ) - 1 := by linarith
  have hl2 : 0 < (ℓ : ℝ) - 1 := by linarith
  -- the first condition: `146 n ℓ (ℓ + 1) ν u ≤ θ β`
  have husign := mul_le_mul_of_mul_le_mul_sqrt (by positivity) (by positivity) (by positivity)
    (by positivity) hl2 hθ hu.le hc
    (mul_le_mul_mul_sqrt_mul_of_logb_le hε hθ (by positivity) (by linarith) (by linarith)
      (by positivity) (by positivity) hu hbits) hβge
  have ha0 : 0 ≤ 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) := by positivity
  have hb0 : 0 ≤ 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) := by positivity
  exact hM.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw
    hunifm hunifc hnormalm hnormalc hμM hμQ hμM₀ hμQ₀ hcN hn hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle
    hN (by linarith [husign]) (by linarith [mul_nonneg hb0 hu.le])
    (by linarith [mul_nonneg ha0 hu.le]) hfuel hτ₀ hτ hΩ hind hlaw

end NLAlib
