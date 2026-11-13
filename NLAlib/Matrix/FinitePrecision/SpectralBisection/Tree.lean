/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Child

/-!
# The recursion tree of spectral bisection

The tree of
`NLAlib.eighNodeAt` from a root with depth counter $\ell \ge$ `NLAlib.bisectionDepth`
$\varepsilon$ has depth at most $\ell$, its nodes have size at most the root's, depth counter
$\ell + \lvert a\rvert$, tolerance in $[\varepsilon/3, \varepsilon]$ and window at most $R_0$,
it has at most $(k + 1)(\ell + 1)$ nodes and at most $k$ of them split, and the sizes of the
nodes at one depth sum to at most $k$ ([Shah2024, proof of Theorem 4.2]).

## Main results

* `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`: the depth.
* `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params`: the parameters of the nodes.
* `NLAlib.FloatMachine.IsAccurate.mul_le_dec_ε_of_eighNodeAt_eq_some`: the tolerance at a node,
  telescoped.
* `NLAlib.FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le`,
  `NLAlib.encard_eighNodeAt_isSplit_le`: the counts.
* `NLAlib.sum_k_eighNodeAt_ofFn_le`: the sizes at one depth sum to at most the root's.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The tolerance of a node of depth $j \le \ell$ stays above $\varepsilon/3$. -/
private lemma div_three_le_of_le_depth {x j u τ ε₀ Φ : ℝ} (hx : 20 ≤ x) (hj0 : 0 ≤ j)
    (hj : j ≤ x) (hu : 0 ≤ u) (hxu : 100 * x ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : 100 * τ ≤ ε₀)
    (hε₀ : 0 < ε₀) (hΦ : 1 - 9 * (j * u) ≤ Φ) :
    ε₀ / 3 ≤ ε₀ * ((x - 1) / (x + j - 1)) * Φ - j * (u * τ) := by
  have hxu' : 20 * (x * u) ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_right hx (mul_nonneg (by linarith : (0 : ℝ) ≤ x) hu); nlinarith
  have hju : j * u ≤ x * u := mul_le_mul_of_nonneg_right hj hu
  have hρ : 2 / 5 ≤ (x - 1) / (x + j - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hΦ' : 99 / 100 ≤ Φ := by linarith
  have h1 := mul_le_mul hρ hΦ' (by norm_num) (by linarith)
  have h2 := mul_le_mul_of_nonneg_left h1 hε₀.le
  have hjuτ : j * (u * τ) ≤ ε₀ / 100 := by
    have : j * (u * τ) = (j * u) * τ := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right (hju.trans (by linarith : x * u ≤ 1)) hτ₀
    linarith
  nlinarith

/-- $(1 + 22u)^n \le 1 + 23nu$ for $nu \le 1/1000$. -/
private lemma one_add_pow_le_of_mul_le {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hnu : (n : ℝ) * u ≤ 1 / 1000) :
    (1 + 22 * u) ^ n ≤ 1 + 23 * (n * u) := by
  have h1 : (1 + 22 * u) ^ n ≤ Real.exp (n * (22 * u)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (22 * u)]) n
  have hy0 : 0 ≤ (n : ℝ) * (22 * u) := by positivity
  have hy : |(n : ℝ) * (22 * u)| ≤ 1 := by rw [abs_of_nonneg hy0]; linarith
  have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hy)).2
  have h3 : ((n : ℝ) * (22 * u)) ^ 2 ≤ (n * (22 * u)) * (22 / 1000) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) hy0
  linarith

/-- The telescoped product of the windows against the tolerance factor: for $x \ge 20$,
$$\frac{1}{32}\frac{2x(2x+1)(2x+2)(2x+3)}{x(x+1)(x+2)(x+3)} \le \frac{x-1}{2x-1} - \frac1x \,.$$ -/
private lemma div_le_sub_one_div_of_le {x : ℝ} (hx : 20 ≤ x) :
    (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3)) / 32 ≤
      (x - 1) / (x + x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  set P := (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3))
  set ρ := (x - 1) / (x + x - 1)
  have hpoly : 0 ≤ 4 * x ^ 3 - 62 * x ^ 2 - 101 * x + 48 := by
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ x - 20),
      mul_nonneg hx0.le (by linarith : 0 ≤ 18 * x - 101)]
  have h2x : x + x - 1 ≠ 0 := by linarith
  have hQ : x * (x + 1) * (x + 2) * (x + 3) ≠ 0 := by positivity
  have hρ' : ρ * (x + x - 1) = x - 1 := div_mul_cancel₀ _ h2x
  have hP' : P * (x * (x + 1) * (x + 2) * (x + 3)) =
      (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) := div_mul_cancel₀ _ hQ
  have hx' : 1 / x * x = 1 := one_div_mul_cancel hx0.ne'
  have key : (ρ - 1 / x - P / 32) * (8 * x * (x + x - 1) * (x + 2) * (x + 3) * (x + 1)) =
      (4 * x ^ 3 - 62 * x ^ 2 - 101 * x + 48) * (x + 1) := by
    linear_combination (8 * x * (x + 2) * (x + 3) * (x + 1)) * hρ' -
      (8 * (x + x - 1) * (x + 2) * (x + 3) * (x + 1)) * hx' - ((x + x - 1) / 4) * hP'
  have hD : 0 < 8 * x * (x + x - 1) * (x + 2) * (x + 3) * (x + 1) :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hx0) (by linarith))
      (by linarith)) (by linarith)) (by linarith)
  have : 0 ≤ ρ - 1 / x - P / 32 :=
    le_of_mul_le_mul_right (by rw [zero_mul, key]; exact mul_nonneg hpoly (by linarith)) hD
  linarith

/-- The real arithmetic of the leaf test at depth $\ell$. -/
private lemma le_of_le_depth_eq {x u τ R₀ ε₀ X Ψ Φ R e z : ℝ} (hx : 20 ≤ x) (hu : 0 ≤ u)
    (hxu : 100 * x ^ 2 * u ≤ 1) (hτ1 : 100 * τ ≤ ε₀ * R₀) (hτ2 : 100 * τ ≤ ε₀)
    (hR₀ : 0 < R₀) (hε₀ : 0 < ε₀) (hX : X ≤ ε₀ / 32) (hΨ0 : 0 ≤ Ψ)
    (hΨ : Ψ ≤ 1 + 23 * (x * u)) (hΦ : 1 - 9 * (x * u) ≤ Φ)
    (hR : R ≤ R₀ * (X * ((x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) /
      (x * (x + 1) * (x + 2) * (x + 3))) * Ψ) + x * (u * τ))
    (he : ε₀ * ((x - 1) / (x + x - 1)) * Φ - x * (u * τ) ≤ e)
    (hz : e * R₀ - u * (e * R₀ + τ) ≤ z) : R ≤ z := by
  have hx0 : 0 < x := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = x * u := ⟨_, rfl⟩
  have hwτ : x * (u * τ) = w * τ := by rw [hw]; ring
  rw [← hw] at hΨ hΦ
  rw [hwτ] at hR he
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwx : 100 * w * x ≤ 1 := by rw [hw]; linarith
  have hw1 : w ≤ 1 / 2000 := by
    have := mul_le_mul_of_nonneg_left hx hw0; linarith
  have huw : 20 * u ≤ w := by
    have := mul_le_mul_of_nonneg_right hx hu; rw [hw]; linarith
  set P := (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3))
  set ρ := (x - 1) / (x + x - 1)
  have hP0 : 0 ≤ P := by positivity
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hP : P / 32 ≤ ρ - 1 / x := div_le_sub_one_div_of_le hx
  have hP16 : P / 32 ≤ 1 / 2 := by have : 0 < 1 / x := by positivity
                                   linarith
  set Y := ε₀ * R₀
  have hY : 0 < Y := by positivity
  have hYx : 100 * (w * Y) ≤ Y / x := by
    rw [le_div_iff₀ hx0]
    have := mul_le_mul_of_nonneg_left hwx hY.le
    linarith
  -- the window
  have hA1 : R₀ * (X * P * Ψ) ≤ Y / 32 * P * Ψ := by
    have := mul_le_mul_of_nonneg_right hX (mul_nonneg (mul_nonneg hR₀.le hP0) hΨ0)
    simp only [Y]; linarith
  have hA2 := mul_le_mul_of_nonneg_left hΨ (mul_nonneg (by positivity : 0 ≤ Y / 32) hP0)
  have hA3 := mul_le_mul_of_nonneg_left hP hY.le
  have hA4 := mul_le_mul_of_nonneg_left hP16 (mul_nonneg hw0 hY.le)
  have hA5 : w * τ ≤ w * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ1 hw0; simp only [Y]; linarith
  -- the test
  have hB1 := mul_le_mul_of_nonneg_right he hR₀.le
  have hB2 := mul_le_mul_of_nonneg_left hΦ (mul_nonneg hY.le hρ0)
  have hB3 : w * τ * R₀ ≤ w * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ2 (mul_nonneg hw0 hR₀.le); simp only [Y]; linarith
  have hB4 := mul_le_mul_of_nonneg_left hρ1 (mul_nonneg hw0 hY.le)
  have hlow : Y * ρ * (1 - 9 * w) - w * Y / 100 ≤ e * R₀ := by
    have : ε₀ * ρ * Φ * R₀ = Y * ρ * Φ := by simp only [Y]; ring
    linarith
  have hlow2 : Y * ρ * (1 - 9 * w) - w * Y / 100 ≤ Y / 2 := by
    have := mul_le_mul_of_nonneg_left hρ1 hY.le
    have := mul_nonneg (mul_nonneg hY.le hρ0) hw0
    have := mul_nonneg hw0 hY.le
    linarith
  have hC1 := mul_le_mul_of_nonneg_right hlow (by linarith : (0 : ℝ) ≤ 1 - u)
  have hC2 := mul_le_mul_of_nonneg_left hlow2 hu
  have hC3 : u * τ ≤ u * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ1 hu; simp only [Y]; linarith
  have hC4 := mul_le_mul_of_nonneg_left huw hY.le
  have hwY := mul_nonneg hw0 hY.le
  clear_value Y P ρ
  have h1 : Y / 32 * P * (1 + 23 * w) = Y * (P / 32) + 23 * (w * Y * (P / 32)) := by ring
  have h2 : Y * (ρ - 1 / x) = Y * ρ - Y / x := by ring
  have hup : R ≤ Y * ρ - Y / x + 23 / 2 * (w * Y) + w * Y / 100 := by
    linarith only [hR, hA1, hA2, hA3, hA4, hA5, h1, h2]
  have hdown : Y * ρ - 9 / 2 * (w * Y) - w * Y / 100 - 51 / 100 * (u * Y) ≤ z := by
    linarith only [hz, hC1, hC2, hC3, hB4]
  linarith only [hup, hdown, hYx, hC4, hwY]

/-- One level of the tolerance bound: $(1 - 1/m)(\ell - 1)/(m - 1) = (\ell - 1)/m$ for
$m = \ell + j$. -/
private lemma mul_div_sub_one_pow_succ (ε u : ℝ) {ℓ j : ℕ} (hm0 : (0 : ℝ) < ℓ + j)
    (hm1 : (ℓ : ℝ) + j - 1 ≠ 0) :
    ε * (((ℓ : ℝ) - 1) / (ℓ + (j + 1) - 1)) * (1 - 9 * u) ^ (j + 1) =
      (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) * (ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) *
        (1 - 9 * u) ^ j) := by
  have : (ℓ : ℝ) + j ≠ 0 := hm0.ne'
  have h' : (ℓ : ℝ) + (j + 1) - 1 = ℓ + j := by ring
  rw [h', pow_succ]; field_simp

/-- One level of the window bound: $(1/2 + 2/m)\,m(m+1)(m+2)(m+3) =
\tfrac12(m+1)(m+2)(m+3)(m+4)$ for $m = \ell + j$. -/
private lemma mul_window_bound_eq (R u : ℝ) {ℓ j : ℕ} (hm0 : (0 : ℝ) < ℓ + j) :
    (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) * (R * (2⁻¹ ^ j *
      (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
        ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j)) =
      R * (2⁻¹ ^ (j + 1) * (((ℓ : ℝ) + (j + 1)) * (ℓ + (j + 1) + 1) * (ℓ + (j + 1) + 2) *
        (ℓ + (j + 1) + 3) / ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) *
          (1 + 22 * u) ^ (j + 1)) := by
  have : (ℓ : ℝ) + j ≠ 0 := hm0.ne'
  rw [pow_succ, pow_succ]; field_simp; ring

/-- One level of the invariants of the recursion below a node at depth $j < \ell$. -/
private lemma invariants_of_eighChild_eq_some {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {N signFuel : ℕ} {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : 20 ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ1 : 100 * τ ≤ dec ε * dec R₀) (hτ2 : 100 * τ ≤ dec ε) (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω)
    {j : ℕ} (hj : j < ℓ) {x y : EighNode F} {smp : EighSample ℝ ℂ N} {b : Bool}
    (hxy : eighChild M N signFuel R₀ β x smp b = some y) (h1 : x.ℓ = ℓ + j)
    (h2 : dec x.ε ≤ 1)
    (h3 : dec ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) * (1 - 9 * u) ^ j - j * (u * τ) ≤ dec x.ε)
    (h4 : dec x.R ≤ dec R₀)
    (h5 : dec x.R ≤ dec R₀ * (2⁻¹ ^ j * (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j) + j * (u * τ)) :
    y.ℓ = ℓ + (j + 1) ∧ dec y.ε ≤ 1 ∧
    dec ε * (((ℓ : ℝ) - 1) / (ℓ + ((j + 1 : ℕ) : ℝ) - 1)) * (1 - 9 * u) ^ (j + 1) -
      ((j + 1 : ℕ) : ℝ) * (u * τ) ≤ dec y.ε ∧ dec y.R ≤ dec R₀ ∧
    dec y.R ≤ dec R₀ * (2⁻¹ ^ (j + 1) * (((ℓ : ℝ) + ((j + 1 : ℕ) : ℝ)) *
      (ℓ + ((j + 1 : ℕ) : ℝ) + 1) * (ℓ + ((j + 1 : ℕ) : ℝ) + 2) * (ℓ + ((j + 1 : ℕ) : ℝ) + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ (j + 1)) +
      ((j + 1 : ℕ) : ℝ) * (u * τ) := by
  obtain ⟨-, hle, -, hyR, hyε, hyℓ⟩ := le_eq_false_and_le_and_eq_of_eighChild_eq_some hxy
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hjℓ : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  have hℓu : 20 * ((ℓ : ℝ) * u) ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_right hℓ' (mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ) hu)
    linarith
  have hu40 : u ≤ 1 / 40000 := by
    have := mul_le_mul_of_nonneg_right hℓ' hu; linarith
  have hτ1' : τ ≤ 1 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ1'
  have hjuτ : 0 ≤ j * (u * τ) := mul_nonneg hj0 (mul_nonneg hu hτ₀)
  have hεx : dec ε / 3 ≤ dec x.ε := by
    refine (div_three_le_of_le_depth hℓ' hj0 (by linarith) hu hu₁ hτ₀ hτ2 hε ?_).trans h3
    have := one_add_mul_le_pow (a := -(9 * u)) (by linarith) j
    rw [← sub_eq_add_neg] at this
    linarith
  -- the window is nonnegative at a node that is not a leaf
  have hxR0 : dec x.ε * dec R₀ ≤ dec R₀ := mul_le_of_le_one_left hR₀.le h2
  have hRx : 0 ≤ dec x.R := by
    have hmul := (le_and_le_of_isRoundingOf (hM.mul x.ε R₀)
      (mul_nonneg (by linarith) hR₀.le) (by linarith) hu hτ₀).1
    have hnot : ¬ dec x.R ≤ dec (M.mul x.ε R₀) := fun h => by
      rw [← hM.le_iff] at h; rw [h] at hle; exact Bool.noConfusion hle
    have h1' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hεx hR₀.le) (by linarith : (0 : ℝ) ≤ 1 - u)
    have h2' := mul_le_mul_of_nonneg_left hτ1 hu
    have h3' := mul_le_mul_of_nonneg_left hu40 (mul_nonneg hε.le hR₀.le)
    linarith
  have hm : 500 * ((x.ℓ : ℕ) : ℝ) * u ≤ 1 := by
    rw [h1]; push_cast
    linarith [mul_le_mul_of_nonneg_right (by linarith : (ℓ : ℝ) + j ≤ 2 * ℓ) hu]
  obtain ⟨s1, s2, s3⟩ := hM.dec_eighNextParams_le (R := x.R) (ε := x.ε) (m := x.ℓ) hu hm hτ₀
    hτ1' (by omega) (by rw [h1]; push_cast; linarith) hRx (by linarith) (by linarith) h2
  rw [← hyR] at s1
  rw [← hyε] at s2 s3
  rw [h1] at s1 s2 s3
  rw [hyℓ, h1]
  push_cast at s1 s2 s3 ⊢
  have hm0 : (0 : ℝ) < ℓ + j := by linarith
  have hc : (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) ≤ 61 / 100 := by
    have : 2 / ((ℓ : ℝ) + j) ≤ 1 / 10 := by rw [div_le_iff₀ hm0]; linarith
    have := mul_le_mul (by linarith : 1 / 2 + 2 / ((ℓ : ℝ) + j) ≤ 6 / 10)
      (by linarith : 1 + 22 * u ≤ 1 + 22 / 40000) (by linarith) (by norm_num)
    linarith
  have hc0 : 0 ≤ (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) := by positivity
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · have hu8 : 8 * u ≤ 1 / ((ℓ : ℝ) + j) := by
      rw [le_div_iff₀ hm0]
      linarith [mul_le_mul_of_nonneg_left (by linarith : (j : ℝ) ≤ ℓ) hu]
    have := mul_le_of_le_one_right (by rw [sub_nonneg, div_le_one hm0]; linarith :
      (0 : ℝ) ≤ 1 - 1 / ((ℓ : ℝ) + j)) h2
    have := mul_le_of_le_one_right (by linarith : (0 : ℝ) ≤ 7 * u) h2
    linarith
  · have hk0 : 0 ≤ (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) :=
      mul_nonneg (by rw [sub_nonneg, div_le_one hm0]; linarith) (by linarith)
    have hk1 : (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) ≤ 1 :=
      mul_le_one₀ (by have : 0 < 1 / ((ℓ : ℝ) + j) := by positivity
                      linarith) (by linarith) (by linarith)
    have hid := mul_div_sub_one_pow_succ (dec ε) u hm0 (by linarith : (ℓ : ℝ) + j - 1 ≠ 0)
    rw [hid]
    have := mul_le_mul_of_nonneg_left h3 hk0
    have := mul_le_of_le_one_left hjuτ hk1
    linarith
  · have := mul_le_mul_of_nonneg_left h4 hc0
    have := mul_le_mul_of_nonneg_right hc hR₀.le
    have := mul_le_of_le_one_left hτ₀ (by linarith : u ≤ 1)
    have := mul_le_of_le_one_left hR₀.le hε₁
    linarith
  · have hid := mul_window_bound_eq (dec R₀) u hm0
    have := mul_le_mul_of_nonneg_left h5 hc0
    have := mul_le_of_le_one_left hjuτ (hc.trans (by norm_num))
    linarith

/-- A node at depth $\ell$ with the invariants of the recursion is a leaf. -/
private lemma eighChild_eq_none_of_invariants {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {N signFuel : ℕ} {R₀ β ε : F} (hε : 0 < dec ε) (hR₀ : 0 < dec R₀) {ℓ : ℕ} (hℓ : 20 ≤ ℓ)
    (hhalf : (2⁻¹ : ℝ) ^ ℓ ≤ dec ε / 32) (hu : 0 ≤ u) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1)
    (hτ₀ : 0 ≤ τ) (hτ1 : 100 * τ ≤ dec ε * dec R₀) (hτ2 : 100 * τ ≤ dec ε)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {x : EighNode F} (smp : EighSample ℝ ℂ N) (b : Bool)
    (h2 : dec x.ε ≤ 1)
    (h3 : dec ε * (((ℓ : ℝ) - 1) / (ℓ + ℓ - 1)) * (1 - 9 * u) ^ ℓ - ℓ * (u * τ) ≤ dec x.ε)
    (h5 : dec x.R ≤ dec R₀ * (2⁻¹ ^ ℓ * (((ℓ : ℝ) + ℓ) * (ℓ + ℓ + 1) * (ℓ + ℓ + 2) * (ℓ + ℓ + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ ℓ) + ℓ * (u * τ)) :
    eighChild M N signFuel R₀ β x smp b = none := by
  rcases hc : eighChild M N signFuel R₀ β x smp b with _ | y
  · rfl
  exfalso
  have hle := (le_eq_false_and_le_and_eq_of_eighChild_eq_some hc).2.1
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓu : (ℓ : ℝ) * u ≤ 1 / 2000 := by
    have := mul_le_mul_of_nonneg_right hℓ' (mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ) hu)
    linarith
  have hεx : dec ε / 3 ≤ dec x.ε := by
    refine (div_three_le_of_le_depth hℓ' (by positivity) le_rfl hu hu₁ hτ₀ hτ2 hε ?_).trans h3
    have := one_add_mul_le_pow (a := -(9 * u)) (by nlinarith) ℓ
    rw [← sub_eq_add_neg] at this
    linarith
  have hmul := (le_and_le_of_isRoundingOf (hM.mul x.ε R₀)
    (mul_nonneg (by linarith) hR₀.le) (by nlinarith) hu hτ₀).1
  have hR : dec x.R ≤ dec (M.mul x.ε R₀) := by
    refine le_of_le_depth_eq hℓ' hu hu₁ hτ1 hτ2 hR₀ hε hhalf (by positivity)
      (one_add_pow_le_of_mul_le hu (hℓu.trans (by norm_num))) ?_ h5 h3 hmul
    have := one_add_mul_le_pow (a := -(9 * u)) (by nlinarith) ℓ
    rw [← sub_eq_add_neg] at this
    linarith
  rw [← hM.le_iff] at hR
  rw [hR] at hle
  exact Bool.noConfusion hle

/-- **The recursion stops by depth $\ell$**: under `NLAlib.FloatMachine.IsAccurate` with
$0 \le u$, $100\ell^2u \le 1$, $0 \le \tau$, $100\tau \le \varepsilon\min(R_0, 1)$ (an absolute
floor bound: the rounded parameters $\mathrm{fl}(2/\ell)$, $\mathrm{fl}((1 - 1/\ell)\varepsilon_j)$
have floor errors $u\tau$) and $16(R_0 + \ell) \le \Omega$, for stored $\varepsilon$, $R_0$ with $0
< \varepsilon \le 2^{-15}$, $R_0 > 0$ and a depth counter $\ell \ge \lceil \log_2(1/\varepsilon)
\rceil + 5$ (`NLAlib.bisectionDepth`), the tree of `NLAlib.eighNodeAt` from the root
$(\mathbf{A}, R_0, \varepsilon, \ell)$ has no node at a path longer than $\ell$, for every
accuracy and samples. [Shah2024, proof of Theorem 4.2], "the
depth of the tree $d$ is no more than $\ell$". -/
theorem FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} (ha : ℓ < a.length) :
    eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = none := by
  -- $2^\ell \ge 32/\varepsilon$, hence $\ell \ge 20$
  have hpow : 32 ≤ dec ε * 2 ^ ℓ := by
    have hlog : Real.logb 2 (dec ε)⁻¹ ≤ (ℓ : ℝ) - 5 := by
      have h2 : ((⌈Real.logb 2 (dec ε)⁻¹⌉₊ + 5 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
      push_cast at h2
      linarith [Nat.le_ceil (Real.logb 2 (dec ε)⁻¹)]
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hε)).mp hlog
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast] at h
    norm_num at h
    have := mul_le_mul_of_nonneg_left h hε.le
    rw [mul_inv_cancel₀ hε.ne'] at this
    linarith
  have hℓ20 : 20 ≤ ℓ := by
    have h := hpow.trans (mul_le_mul_of_nonneg_right hε₁ (by positivity))
    have h' : (2 : ℝ) ^ 20 ≤ 2 ^ ℓ := by norm_num at h ⊢; linarith
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h'
  have hhalf : (2⁻¹ : ℝ) ^ ℓ ≤ dec ε / 32 := by
    rw [inv_pow, ← one_div, div_le_iff₀ (by positivity)]; linarith
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hτ1 : 100 * τ ≤ dec ε * dec R₀ :=
    hτ.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hε.le)
  have hτ2 : 100 * τ ≤ dec ε := hτ.trans (mul_le_of_le_one_right hε.le (min_le_right _ _))
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ20
  -- induction on the path with the invariants of the recursion
  have key : ∀ (a : List Bool) (j : ℕ) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N),
      j ≤ ℓ → x.ℓ = ℓ + j → dec x.ε ≤ 1 →
      dec ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) * (1 - 9 * u) ^ j - j * (u * τ) ≤ dec x.ε →
      dec x.R ≤ dec R₀ →
      dec x.R ≤ dec R₀ * (2⁻¹ ^ j * (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
        ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j) + j * (u * τ) →
      ℓ < j + a.length → eighNodeAt M N signFuel R₀ β a x s = none := by
    intro a
    induction a with
    | nil => intro j x s hj _ _ _ _ _ hlt; simp only [List.length_nil] at hlt; omega
    | cons b a ih =>
      intro j x s hj h1 h2 h3 h4 h5 hlt
      simp only [eighNodeAt]
      rcases hc : eighChild M N signFuel R₀ β x (s []) b with _ | y
      · rfl
      rcases Nat.lt_or_ge j ℓ with hjl | hjl
      · obtain ⟨g1, g2, g3, g4, g5⟩ := invariants_of_eighChild_eq_some hM hε hε1 hR₀ hℓ20 hu
          hu₁ hτ₀ hτ1 hτ2 hΩ hjl hc h1 h2 h3 h4 h5
        exact ih (j + 1) y _ (by omega) g1 g2 g3 g4 g5
          (by simp only [List.length_cons] at hlt; omega)
      · obtain rfl : j = ℓ := by omega
        rw [eighChild_eq_none_of_invariants hM hε hR₀ hℓ20 hhalf hu hu₁ hτ₀ hτ1 hτ2 hΩ _ _ h2
          h3 h5] at hc
        exact absurd hc (by simp)
  have hQ : (ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3) ≠ 0 := by positivity
  refine key a 0 _ s (Nat.zero_le _) rfl hε1 ?_ le_rfl ?_ (by simpa using ha)
  · rw [Nat.cast_zero, add_zero, div_self (by linarith), pow_zero]; simp
  · simp only [Nat.cast_zero, add_zero, pow_zero, div_self hQ, mul_one, zero_mul]
    exact le_rfl

/-- The rounded next tolerance of a node: $\varepsilon' \le \varepsilon$ and
$\varepsilon(L - 1) - 3uL\varepsilon \le \varepsilon' L$. -/
private theorem FloatMachine.IsAccurate.dec_eighNextParams_snd_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (r e : F)
    {L : ℕ} (hu : 0 ≤ u) (huL : u * L ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 100)
    (he0 : 0 < dec e) (hτe : 30 * τ ≤ dec e) (he1 : dec e ≤ 1) (hL : 5 ≤ L)
    (hΩ : 2 + L ≤ Ω) :
    dec (eighNextParams M r e L).2 ≤ dec e ∧
      dec e * (L - 1) - 3 * u * L * dec e ≤ dec (eighNextParams M r e L).2 * L := by
  have hL' : (5 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hu5 : u ≤ 1 / 5000 := by nlinarith
  simp only [eighNextParams]
  obtain ⟨hla, hlb⟩ := le_and_le_of_isRoundingOf (hM.ofNat L) hL0.le (by linarith) hu hτ₀
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  have hdl : L - 0.002 ≤ dec (M.ofNat L) ∧ dec (M.ofNat L) ≤ L + 0.002 := by
    constructor <;> linarith
  have hdl0 : 0 < dec (M.ofNat L) := by linarith
  have hiL1 : 1 / (L : ℝ) * L = 1 := by field_simp
  have hiL5 : 1 / (L : ℝ) ≤ 1 / 5 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have huiL : u ≤ 1 / (L : ℝ) / 1000 := by
    rw [le_div_iff₀ (by norm_num), le_div_iff₀ hL0]; linarith
  -- the reciprocal of the depth counter
  have hq0 : |1 / dec (M.ofNat L) - 1 / L| ≤ u / 4 := by
    rw [div_sub_div _ _ hdl0.ne' hL0.ne', abs_div, abs_of_pos (mul_pos hdl0 hL0),
      div_le_iff₀ (mul_pos hdl0 hL0), abs_le]
    have h1 : L + τ ≤ dec (M.ofNat L) * L / 4 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ dec (M.ofNat L) - 4.99) hL0.le]
    have h2 := mul_le_mul_of_nonneg_left h1 hu
    constructor <;> linarith
  have hq0' := abs_le.mp hq0
  obtain ⟨hqa, hqb⟩ := le_and_le_of_isRoundingOf (hM.div M.one (M.ofNat L) hdl0.ne')
    (by rw [hM.dec_one]; positivity) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hqa hqb
  have hq021 : 1 / dec (M.ofNat L) ≤ 0.21 := by linarith
  have hdq : 1 / L - u / 2 ≤ dec (M.div M.one (M.ofNat L)) ∧
      dec (M.div M.one (M.ofNat L)) ≤ 1 / L + u / 2 := by
    have := mul_le_mul_of_nonneg_left hq021 hu
    constructor <;> linarith
  obtain ⟨hsa, hsb⟩ := le_and_le_of_isRoundingOf (hM.sub M.one (M.div M.one (M.ofNat L)))
    (by rw [hM.dec_one]; linarith) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hsa hsb
  have hds : 1 - 1 / L - 1.6 * u ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) ∧
      dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 - 1 / L + 1.6 * u := by
    have := mul_le_mul_of_nonneg_left (show 1 - dec (M.div M.one (M.ofNat L)) ≤ 1 by linarith) hu
    constructor <;> linarith
  have hds0 : 0 ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) := by linarith
  have hds1 : dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 := by linarith
  have hdse := mul_le_of_le_one_left he0.le hds1
  obtain ⟨hea, heb⟩ := le_and_le_of_isRoundingOf (hM.mul (M.sub M.one (M.div M.one (M.ofNat L))) e)
    (mul_nonneg hds0 he0.le) (by linarith) hu hτ₀
  have hde : (1 - 1 / L) * dec e - 3 * u * dec e ≤
      dec (M.mul (M.sub M.one (M.div M.one (M.ofNat L))) e) ∧
      dec (M.mul (M.sub M.one (M.div M.one (M.ofNat L))) e) ≤
        (1 - 1 / L) * dec e + 3 * u * dec e := by
    have h1 := mul_le_mul_of_nonneg_right hds.1 he0.le
    have h2 := mul_le_mul_of_nonneg_right hds.2 he0.le
    have h3 := mul_le_mul_of_nonneg_left hdse hu
    have h4 := mul_le_mul_of_nonneg_left hτe hu
    constructor <;> linarith
  have hue := mul_le_mul_of_nonneg_right huiL he0.le
  refine ⟨by linarith, ?_⟩
  have := mul_le_mul_of_nonneg_right hde.1 hL0.le
  linear_combination this + dec e * hiL1

/-- The rounded next window of a node that is not a leaf is at most its window. -/
private theorem FloatMachine.IsAccurate.dec_eighNextParams_fst_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R₀ r : F} (e : F)
    {L : ℕ} (hu : 0 ≤ u) (huL : u * L ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 100)
    (he0 : 0 < dec e) (hτeR : 30 * τ ≤ dec e * dec R₀) (he1 : dec e ≤ 1) (hL : 5 ≤ L)
    (hΩ : 2 + L + dec R₀ ≤ Ω) (hR₀ : 0 < dec R₀) (hr : dec r ≤ dec R₀)
    (hint : M.le r (M.mul e R₀) = false) :
    dec (eighNextParams M r e L).1 ≤ dec r := by
  have hL' : (5 : ℝ) ≤ L := by exact_mod_cast hL
  have hu5 : u ≤ 1 / 5000 := by nlinarith
  simp only [eighNextParams]
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  obtain ⟨h2a, h2b⟩ := le_and_le_of_isRoundingOf (hM.ofNat 2) (by norm_num) (by push_cast; linarith)
    hu hτ₀
  obtain ⟨hla, hlb⟩ := le_and_le_of_isRoundingOf (hM.ofNat L) (by positivity) (by linarith) hu hτ₀
  push_cast at h2a h2b
  have hd2 : 1.99 ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2.01 := by constructor <;> linarith
  have hdl : L - 0.002 ≤ dec (M.ofNat L) := by linarith
  have hdl0 : 0 < dec (M.ofNat L) := by linarith
  -- the factor is at most `0.95`
  have hh1 : 1 / dec (M.ofNat 2) ≤ 0.51 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hh2 : 0.49 ≤ 1 / dec (M.ofNat 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨hha, hhb⟩ := le_and_le_of_isRoundingOf (hM.div M.one (M.ofNat 2) (by linarith))
    (by rw [hM.dec_one]; positivity) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hha hhb
  have ht1 : dec (M.ofNat 2) / dec (M.ofNat L) ≤ 0.41 := by rw [div_le_iff₀ hdl0]; linarith
  have ht0 : 0 ≤ dec (M.ofNat 2) / dec (M.ofNat L) := div_nonneg (by linarith) hdl0.le
  obtain ⟨hta, htb⟩ := le_and_le_of_isRoundingOf (hM.div (M.ofNat 2) (M.ofNat L) hdl0.ne') ht0
    (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left hh1 hu
  have := mul_le_mul_of_nonneg_left ht1 hu
  have hdh : 0.48 ≤ dec (M.div M.one (M.ofNat 2)) ∧ dec (M.div M.one (M.ofNat 2)) ≤ 0.52 := by
    constructor <;> linarith
  have hdt : -0.01 ≤ dec (M.div (M.ofNat 2) (M.ofNat L)) ∧
      dec (M.div (M.ofNat 2) (M.ofNat L)) ≤ 0.42 := by
    constructor <;> linarith
  obtain ⟨haa, hab⟩ := le_and_le_of_isRoundingOf (hM.add (M.div M.one (M.ofNat 2))
    (M.div (M.ofNat 2) (M.ofNat L))) (by linarith) (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left (show dec (M.div M.one (M.ofNat 2)) +
    dec (M.div (M.ofNat 2) (M.ofNat L)) ≤ 0.94 by linarith) hu
  have hda : 0 ≤ dec (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ∧
      dec (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ≤ 0.95 := by
    constructor <;> linarith
  -- the window is above the floor
  have heR := mul_le_of_le_one_left hR₀.le he1
  have hm := le_and_le_of_isRoundingOf (hM.mul e R₀) (mul_pos he0 hR₀).le (by linarith) hu hτ₀
  have hrm : dec (M.mul e R₀) < dec r := by
    rw [← not_le, ← hM.le_iff]; simp [hint]
  have := mul_le_mul_of_nonneg_left heR hu
  have := mul_le_mul_of_nonneg_right hu5 (mul_pos he0 hR₀).le
  have := mul_le_mul_of_nonneg_right hu5 hτ₀
  have hr0 : 29 * τ ≤ dec r := by linarith [hm.1]
  have hdar := mul_le_of_le_one_left (by linarith : 0 ≤ dec r) (by linarith : dec (M.add
    (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ≤ 1)
  obtain ⟨hra, hrb⟩ := le_and_le_of_isRoundingOf (hM.mul (M.add (M.div M.one (M.ofNat 2))
    (M.div (M.ofNat 2) (M.ofNat L))) r) (mul_nonneg hda.1 (by linarith)) (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left hdar hu
  have := mul_le_mul_of_nonneg_right hda.2 (by linarith : 0 ≤ dec r)
  have := mul_le_mul_of_nonneg_right hu5 (by linarith : 0 ≤ dec r)
  linarith

/-- **The parameters of the nodes**: let the machine meet `NLAlib.FloatMachine.IsAccurate` with $0
\le u$, $100\ell^2u \le 1$, floor
$0 \le \tau$ with $100\tau \le \varepsilon\min(R_0, 1)$ and range $16(R_0 + \ell) \le \Omega$, and
let
the root $(k, \mathbf{A}, R_0, \varepsilon, \ell)$ have $0 < \varepsilon \le 2^{-15}$, $R_0 > 0$ and
$\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$. Then every node $y$ of the tree at a
path $a$ has $\lvert a \rvert \le \ell$, size at most the root's, depth counter $\ell +
\lvert a\rvert$, tolerance in $[\varepsilon/3, \varepsilon]$ and window at most $R_0$. (Not
$R_y \ge 0$: a rounded product can be $-u\tau$; such a node is a leaf.) [Shah2024, proof of
Theorem 4.2]. -/
theorem FloatMachine.IsAccurate.eighNodeAt_eq_some_params
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} {y : EighNode F}
    (h : eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = some y) :
    a.length ≤ ℓ ∧ y.k ≤ k ∧ y.ℓ = ℓ + a.length ∧ dec ε / 3 ≤ dec y.ε ∧ dec y.ε ≤ dec ε ∧
      dec y.R ≤ dec R₀ := by
  have hℓ20 : (20 : ℝ) ≤ ℓ := by
    have h15 : (15 : ℝ) ≤ Real.logb 2 (dec ε)⁻¹ := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), show (15 : ℝ) = (15 : ℕ) by
        norm_num, Real.rpow_natCast, ← inv_inv ((2 : ℝ) ^ 15), ← inv_pow]
      exact inv_anti₀ hε (by simpa using hε₁)
    have := (h15.trans (Nat.le_ceil _))
    have : (bisectionDepth (dec ε) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    simp only [bisectionDepth, Nat.cast_add] at this
    push_cast at this
    linarith
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hτε : 100 * τ ≤ dec ε := hτ.trans (mul_le_of_le_one_right hε.le (min_le_right _ _))
  have hτR : 100 * τ ≤ dec ε * dec R₀ := hτ.trans (by gcongr; exact min_le_left _ _)
  have huℓ : u * ℓ ≤ 1 / 2000 := by nlinarith
  -- the tolerance stays above a third of the root's
  have hlow : ∀ (x : EighNode F) (j : ℕ), j ≤ ℓ → x.ℓ = ℓ + j →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) → dec ε / 3 ≤ dec x.ε := by
    intro x j hj hxℓ hx
    have hj' : (j : ℝ) ≤ ℓ := by exact_mod_cast hj
    rw [hxℓ] at hx
    push_cast at hx
    have h1 := mul_le_mul_of_nonneg_left hj' (by positivity : 0 ≤ u * ℓ)
    have h2 := mul_le_mul_of_nonneg_right h1 hε.le
    by_contra hlt
    have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
    nlinarith [mul_lt_mul_of_pos_right (not_le.mp hlt) (by linarith : (0 : ℝ) < ℓ + j - 1)]
  have key : ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N) (j : ℕ)
      (y : EighNode F), j + a.length ≤ ℓ → x.k ≤ k → x.ℓ = ℓ + j → dec x.ε ≤ dec ε →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) → dec x.R ≤ dec R₀ →
      eighNodeAt M N signFuel R₀ β a x s = some y →
      y.k ≤ k ∧ y.ℓ = ℓ + (j + a.length) ∧ dec y.ε ≤ dec ε ∧
        dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * (j + a.length : ℕ) ≤ dec y.ε * (y.ℓ - 1) ∧
        dec y.R ≤ dec R₀ := by
    intro a
    induction a with
    | nil =>
      intro x s j y _ h1 h2 h3 h4 h5 h
      cases Option.some.inj h
      exact ⟨h1, h2, h3, by simpa using h4, h5⟩
    | cons b a ih =>
      intro x s j y hj h1 h2 h3 h4 h5 h
      simp only [eighNodeAt, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, hy⟩ := h
      obtain ⟨-, hint, hzk, hzR, hzε, hzℓ⟩ := le_eq_false_and_le_and_eq_of_eighChild_eq_some hz
      simp only [List.length_cons] at hj
      have hxε := hlow x j (by omega) h2 h4
      have hx0 : 0 < dec x.ε := by linarith
      have hxℓ : (x.ℓ : ℝ) ≤ 2 * ℓ := by
        rw [h2]; push_cast; linarith [(by exact_mod_cast (by omega : j ≤ ℓ) : (j : ℝ) ≤ ℓ)]
      have hxℓ5 : 5 ≤ x.ℓ := by
        have : (5 : ℝ) ≤ x.ℓ := by rw [h2]; push_cast; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
        exact_mod_cast this
      have huL : u * x.ℓ ≤ 1 / 1000 := by nlinarith
      have hR := mul_le_mul_of_nonneg_right hxε hR₀.le
      obtain ⟨hs1, hs2⟩ := hM.dec_eighNextParams_snd_le x.R x.ε hu huL hτ₀ (by linarith) hx0
        (by linarith) (by linarith) hxℓ5 (by linarith)
      have hf := hM.dec_eighNextParams_fst_le x.ε hu huL hτ₀ (by linarith) hx0 (by linarith)
        (by linarith) hxℓ5 (by linarith) hR₀ h5 hint
      have hloss := mul_le_mul_of_nonneg_left
        (mul_le_mul hxℓ h3 hx0.le (by positivity)) (by positivity : (0 : ℝ) ≤ 3 * u)
      obtain ⟨r1, r2, r3, r4, r5⟩ := ih z (fun a' => s (b :: a')) (j + 1) y (by omega)
        (by omega) (by omega) (by rw [hzε]; linarith) (by
          rw [hzε, hzℓ]; push_cast at hs2 ⊢; nlinarith) (by rw [hzR]; linarith) hy
      rw [show j + (b :: a).length = j + 1 + a.length by simp only [List.length_cons]; omega]
      exact ⟨r1, r2, r3, r4, r5⟩
  have hlen : a.length ≤ ℓ := by
    by_contra hlt
    rw [eighNodeAt_eq_none_of_lt_length hM hε hε₁ hR₀ hℓ hu hu₁ hτ₀ hτ hΩ A s
      (not_le.mp hlt)] at h
    cases h
  obtain ⟨r1, r2, r3, r4, r5⟩ := key a ⟨k, A, R₀, ε, ℓ⟩ s 0 y (by omega) le_rfl rfl le_rfl
    (by simp) le_rfl h
  rw [zero_add] at r2 r4
  exact ⟨hlen, r1, r2, hlow y _ hlen r2 r4, r3, r5⟩

/-- A split of `NLAlib.eighStep` has both parts nonempty. -/
private lemma pos_and_lt_of_eighStep_eq_split {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ} {s : EighSample Su Sg N} {kp : ℕ}
    {h : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (hst : eighStep M N signFuel R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ) :
    0 < kp ∧ kp < k := by
  unfold eighStep at hst
  dsimp only at hst
  split_ifs at hst with h1 h2 h3 h4
  obtain ⟨rfl, -⟩ := EighStep.split.inj hst
  omega

/-- The nodes at one depth number at most $\max(k, 1)$. -/
private lemma encard_eighNodeAt_length_eq_le {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} (j : ℕ) :
    ∀ (x : EighNode F) (s : List Bool → EighSample Su Sg N),
    {a : List Bool | a.length = j ∧ eighNodeAt M N signFuel R₀ β a x s ≠ none}.encard ≤
      (max x.k 1 : ℕ) := by
  induction j with
  | zero =>
    intro x s
    refine (Set.encard_le_encard (t := {[]}) fun a ha => ?_).trans ?_
    · exact List.eq_nil_of_length_eq_zero ha.1
    · rw [Set.encard_singleton]; exact_mod_cast le_max_right _ _
  | succ j ih =>
    intro x s
    have hmem : ∀ a ∈ {a : List Bool | a.length = j + 1 ∧
        eighNodeAt M N signFuel R₀ β a x s ≠ none},
        ∃ b a', a = b :: a' ∧ ∃ y', eighChild M N signFuel R₀ β x (s []) b = some y' ∧
          a' ∈ {a : List Bool | a.length = j ∧
            eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) ≠ none} := by
      rintro (_ | ⟨b, a'⟩) ⟨hlen, hy⟩
      · simp at hlen
      · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hy
        simp only [eighNodeAt, Option.bind_eq_some_iff] at hy
        obtain ⟨y', hy', hy⟩ := hy
        exact ⟨b, a', rfl, y', hy', by simpa using hlen, by simp [hy]⟩
    rcases hst : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (s []) with
      ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
    · refine le_of_eq_of_le (b := 0) (Set.encard_eq_zero.mpr ?_) bot_le
      refine Set.eq_empty_of_forall_notMem fun a ha => ?_
      obtain ⟨b, a', -, y', hy', -⟩ := hmem a ha
      simp [eighChild, hst] at hy'
    · set y' : EighNode F := ⟨x.k, A', (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := List.cons b '' {a : List Bool | a.length = j ∧
            eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) ≠ none})
          fun a ha => ?_).trans ?_
      · obtain ⟨b', a', rfl, z, hz, ha'⟩ := hmem a ha
        simp only [eighChild, hst] at hz
        split_ifs at hz with hb
        subst hb
        simp only [Option.some.injEq] at hz
        subst hz
        exact ⟨a', ha', rfl⟩
      · rw [(List.cons_injective).encard_image]
        exact ih y' _
    · obtain ⟨hkp0, hkpk⟩ := pos_and_lt_of_eighStep_eq_split M hst
      set yp : EighNode F := ⟨kp, Ap, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      set ym : EighNode F := ⟨x.k - kp, Am, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := List.cons true '' {a : List Bool | a.length = j ∧
            eighNodeAt M N signFuel R₀ β a yp (fun a' => s (true :: a')) ≠ none} ∪
          List.cons false '' {a : List Bool | a.length = j ∧
            eighNodeAt M N signFuel R₀ β a ym (fun a' => s (false :: a')) ≠ none})
          fun a ha => ?_).trans ?_
      · obtain ⟨b', a', rfl, z, hz, ha'⟩ := hmem a ha
        simp only [eighChild, hst] at hz
        cases b'
        · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz
          subst hz
          exact Or.inr ⟨a', ha', rfl⟩
        · simp only [↓reduceIte, Option.some.injEq] at hz
          subst hz
          exact Or.inl ⟨a', ha', rfl⟩
      · refine (Set.encard_union_le _ _).trans ?_
        rw [(List.cons_injective).encard_image, (List.cons_injective).encard_image]
        refine (add_le_add (ih yp _) (ih ym _)).trans ?_
        have hk : max yp.k 1 + max ym.k 1 ≤ max x.k 1 := by simp only [yp, ym]; omega
        exact_mod_cast hk

/-- **The recursion tree has at most $(k + 1)(\ell + 1)$ nodes**: let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $0 \le u$, $100\ell^2u \le 1$, floor
$0 \le \tau$ with $100\tau \le \varepsilon\min(R_0, 1)$ and range $16(R_0 + \ell) \le \Omega$, and
let
the root $(k, \mathbf{A}, R_0, \varepsilon, \ell)$ have $0 < \varepsilon \le 2^{-15}$, $R_0 > 0$ and
$\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$. Then the set of paths at which
`NLAlib.eighNodeAt` has a node has at most $(k + 1)(\ell + 1)$ elements, $k$ the size of the root.
[Shah2024, proof of Theorem 4.2], $\lvert X \rvert \le nd$ there. -/
theorem FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N) :
    {a : List Bool | eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}.encard ≤
      (k + 1) * (ℓ + 1) := by
  have hU : ∀ n : ℕ, {a : List Bool | a.length < n ∧
      eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}.encard ≤ (n * max k 1 : ℕ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine (Set.encard_le_encard (t := {a : List Bool | a.length < n ∧
          eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none} ∪
          {a : List Bool | a.length = n ∧
          eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}) fun a ha => ?_).trans ?_
      · rcases Nat.lt_succ_iff_lt_or_eq.mp ha.1 with h | h
        · exact Or.inl ⟨h, ha.2⟩
        · exact Or.inr ⟨h, ha.2⟩
      · refine (Set.encard_union_le _ _).trans ?_
        refine (add_le_add ih (encard_eighNodeAt_length_eq_le M n ⟨k, A, R₀, ε, ℓ⟩ s)).trans ?_
        rw [Nat.succ_mul]
        exact_mod_cast le_rfl
  refine (Set.encard_le_encard (t := {a : List Bool | a.length < ℓ + 1 ∧
      eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}) fun a ha => ?_).trans
    ((hU (ℓ + 1)).trans ?_)
  · refine ⟨Nat.lt_succ_of_le (not_lt.mp fun hlt => ha ?_), ha⟩
    exact hM.eighNodeAt_eq_none_of_lt_length hε hε₁ hR₀ hℓ hu hu₁ hτ₀ hτ hΩ A s hlt
  · have hk : (ℓ + 1) * max k 1 ≤ (k + 1) * (ℓ + 1) := by
      rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast hk

/-- The split paths of length less than `m` number at most $k - 1$. -/
private lemma encard_eighNodeAt_isSplit_length_lt_le {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} (m : ℕ) :
    ∀ (x : EighNode F) (s : List Bool → EighSample Su Sg N),
    {a : List Bool | a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
      (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.encard ≤ (x.k - 1 : ℕ) := by
  induction m with
  | zero => intro x s; simp
  | succ m ih =>
    intro x s
    have hmem : ∀ a ∈ {a : List Bool | a.length < m + 1 ∧
        ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
          (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit},
        (a = [] ∧ (eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (s [])).IsSplit) ∨
        ∃ b a', a = b :: a' ∧ ∃ y', eighChild M N signFuel R₀ β x (s []) b = some y' ∧
          a' ∈ {a : List Bool | a.length < m ∧
            ∃ y, eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (b :: a))).IsSplit} := by
      rintro (_ | ⟨b, a'⟩) ⟨hlen, y, hy, hsp⟩
      · simp only [eighNodeAt, Option.some.injEq] at hy
        subst hy
        exact Or.inl ⟨rfl, hsp⟩
      · simp only [eighNodeAt, Option.bind_eq_some_iff] at hy
        obtain ⟨y', hy', hy⟩ := hy
        exact Or.inr ⟨b, a', rfl, y', hy', by simpa using hlen, y, hy, hsp⟩
    rcases hst : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (s []) with
      ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
    · refine le_of_eq_of_le (b := 0) (Set.encard_eq_zero.mpr ?_) bot_le
      refine Set.eq_empty_of_forall_notMem fun a ha => ?_
      rcases hmem a ha with ⟨-, h⟩ | ⟨b, a', -, y', hy', -⟩
      · rw [hst] at h; exact h
      · simp [eighChild, hst] at hy'
    · set y' : EighNode F := ⟨x.k, A', (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := List.cons b '' {a : List Bool | a.length < m ∧
            ∃ y, eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (b :: a))).IsSplit})
          fun a ha => ?_).trans ?_
      · rcases hmem a ha with ⟨-, h⟩ | ⟨b', a', rfl, z, hz, ha'⟩
        · rw [hst] at h; exact h.elim
        · simp only [eighChild, hst] at hz
          split_ifs at hz with hb
          · subst hb
            simp only [Option.some.injEq] at hz
            subst hz
            exact ⟨a', ha', rfl⟩
      · rw [(List.cons_injective).encard_image]
        exact ih y' _
    · obtain ⟨hkp0, hkpk⟩ := pos_and_lt_of_eighStep_eq_split M hst
      set yp : EighNode F := ⟨kp, Ap, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      set ym : EighNode F := ⟨x.k - kp, Am, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := {[]} ∪ (List.cons true '' {a : List Bool |
            a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β a yp (fun a' => s (true :: a')) =
              some y ∧ (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (true :: a))).IsSplit} ∪
          List.cons false '' {a : List Bool | a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β
            a ym (fun a' => s (false :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (false :: a))).IsSplit}))
          fun a ha => ?_).trans ?_
      · rcases hmem a ha with ⟨rfl, -⟩ | ⟨b', a', rfl, z, hz, ha'⟩
        · exact Or.inl rfl
        · simp only [eighChild, hst] at hz
          cases b'
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz
            subst hz
            exact Or.inr (Or.inr ⟨a', ha', rfl⟩)
          · simp only [↓reduceIte, Option.some.injEq] at hz
            subst hz
            exact Or.inr (Or.inl ⟨a', ha', rfl⟩)
      · refine (Set.encard_union_le _ _).trans ?_
        refine (add_le_add le_rfl (Set.encard_union_le _ _)).trans ?_
        rw [Set.encard_singleton, (List.cons_injective).encard_image,
          (List.cons_injective).encard_image]
        refine (add_le_add le_rfl (add_le_add (ih yp _) (ih ym _))).trans ?_
        have hk : 1 + (yp.k - 1 + (ym.k - 1)) ≤ x.k - 1 := by simp only [yp, ym]; omega
        exact_mod_cast hk

/-- **At most $k$ nodes split**: for every machine, root of size $k$, accuracy and samples, the set
of paths at which `NLAlib.eighNodeAt` has a node whose step `NLAlib.eighStep` (with that path's
sample) is a split has at most $k$ elements. [Shah2024, proof of Theorem 4.2],
$\lvert X_D \rvert = n - 1$ there. -/
theorem encard_eighNodeAt_isSplit_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (s : List Bool → EighSample Su Sg N) :
    {a : List Bool | ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
      (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.encard ≤ x.k := by
  by_contra hlt
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt (not_le.mp hlt))
  have htf : t.Finite := Set.finite_of_encard_eq_coe (k := x.k + 1) (by simpa using htc)
  obtain ⟨m, hm⟩ := (htf.image List.length).bddAbove
  have hsub := Set.encard_le_encard (s := t) (t := {a : List Bool | a.length < m + 1 ∧
      ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
        (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit})
    fun a ha => ⟨Nat.lt_succ_of_le (hm ⟨a, ha, rfl⟩), hts ha⟩
  have h := hsub.trans (encard_eighNodeAt_isSplit_length_lt_le M (m + 1) x s)
  rw [htc] at h
  have h' : x.k + 1 ≤ x.k - 1 := by exact_mod_cast h
  omega

/-! ### Generic node lemmas for a precision budget -/

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
  {N signFuel : ℕ} {R₀ β : F} {w x t : ℝ} {y : EighNode F}

/-- **The tolerance at a node, telescoped**: let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $0 \le u$, $100\ell^2u \le 1$, floor $0 \le \tau$ with
$100\tau \le \varepsilon\min(R_0, 1)$ and range $16(R_0 + \ell) \le \Omega$, and let the root
$(k, \mathbf{A}, R_0, \varepsilon, \ell)$ have $0 < \varepsilon \le 2^{-15}$, $R_0 > 0$ and
$\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$. Then every node $y$ of the tree has
$$\varepsilon_y \ge (1 - 2^{-8})\,\frac{\ell - 1}{\ell_y - 1}\,\varepsilon \,,$$
in particular $\varepsilon_y \ge (1 - 2^{-8})(\ell - 1)\varepsilon/(2\ell - 1)$ since
$\ell_y \le 2\ell$. [Shah2024, proof of Theorem 4.2]. -/
theorem FloatMachine.IsAccurate.mul_le_dec_ε_of_eighNodeAt_eq_some
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15)
    (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} {y : EighNode F}
    (h : eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = some y) :
    (1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((y.ℓ : ℝ) - 1)) * dec ε ≤ dec y.ε := by
  obtain ⟨hlen, -, hyℓ, -⟩ := hM.eighNodeAt_eq_some_params hε hε₁ hR₀ hℓ hu hu₁ hτ₀ hτ hΩ A s h
  have hℓ20 : (20 : ℝ) ≤ ℓ := by
    have h15 : (15 : ℝ) ≤ Real.logb 2 (dec ε)⁻¹ := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), show (15 : ℝ) = (15 : ℕ) by
        norm_num, Real.rpow_natCast, ← inv_inv ((2 : ℝ) ^ 15), ← inv_pow]
      exact inv_anti₀ hε (by simpa using hε₁)
    have := (h15.trans (Nat.le_ceil _))
    have : (bisectionDepth (dec ε) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    simp only [bisectionDepth, Nat.cast_add] at this
    push_cast at this
    linarith
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hτε : 100 * τ ≤ dec ε := hτ.trans (mul_le_of_le_one_right hε.le (min_le_right _ _))
  have huℓ : u * ℓ ≤ 1 / 2000 := by nlinarith
  -- the tolerance stays above a third of the root's
  have hlow : ∀ (x : EighNode F) (j : ℕ), j ≤ ℓ → x.ℓ = ℓ + j →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) → dec ε / 3 ≤ dec x.ε := by
    intro x j hj hxℓ hx
    have hj' : (j : ℝ) ≤ ℓ := by exact_mod_cast hj
    rw [hxℓ] at hx
    push_cast at hx
    have h1 := mul_le_mul_of_nonneg_left hj' (by positivity : 0 ≤ u * ℓ)
    have h2 := mul_le_mul_of_nonneg_right h1 hε.le
    by_contra hlt
    have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
    nlinarith [mul_lt_mul_of_pos_right (not_le.mp hlt) (by linarith : (0 : ℝ) < ℓ + j - 1)]
  -- each level loses at most `3 u ℓ_x ε_x ≤ 6 u ℓ ε` of `ε_x (ℓ_x - 1)`
  have key : ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N) (j : ℕ)
      (y : EighNode F), j + a.length ≤ ℓ → x.ℓ = ℓ + j → dec x.ε ≤ dec ε →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) →
      eighNodeAt M N signFuel R₀ β a x s = some y →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * (j + a.length : ℕ) ≤ dec y.ε * (y.ℓ - 1) := by
    intro a
    induction a with
    | nil =>
      intro x s j y _ h2 _ h4 h
      cases Option.some.inj h
      simpa using h4
    | cons b a ih =>
      intro x s j y hj h2 h3 h4 h
      simp only [eighNodeAt, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, hy⟩ := h
      obtain ⟨-, -, -, -, hzε, hzℓ⟩ := le_eq_false_and_le_and_eq_of_eighChild_eq_some hz
      simp only [List.length_cons] at hj
      have hxε := hlow x j (by omega) h2 h4
      have hx0 : 0 < dec x.ε := by linarith
      have hxℓ : (x.ℓ : ℝ) ≤ 2 * ℓ := by
        rw [h2]; push_cast; linarith [(by exact_mod_cast (by omega : j ≤ ℓ) : (j : ℝ) ≤ ℓ)]
      have hxℓ5 : 5 ≤ x.ℓ := by
        have : (5 : ℝ) ≤ x.ℓ := by rw [h2]; push_cast; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
        exact_mod_cast this
      have huL : u * x.ℓ ≤ 1 / 1000 := by nlinarith
      obtain ⟨hs1, hs2⟩ := hM.dec_eighNextParams_snd_le x.R x.ε hu huL hτ₀ (by linarith) hx0
        (by linarith) (by linarith) hxℓ5 (by linarith)
      have hloss := mul_le_mul_of_nonneg_left
        (mul_le_mul hxℓ h3 hx0.le (by positivity)) (by positivity : (0 : ℝ) ≤ 3 * u)
      have r := ih z (fun a' => s (b :: a')) (j + 1) y (by omega) (by omega)
        (by rw [hzε]; linarith) (by
          rw [hzε, hzℓ]; push_cast at hs2 ⊢; nlinarith) hy
      rwa [show j + (b :: a).length = j + 1 + a.length by simp only [List.length_cons]; omega]
  have r := key a ⟨k, A, R₀, ε, ℓ⟩ s 0 y (by omega) rfl le_rfl (by simp) h
  rw [zero_add, hyℓ] at r
  rw [hyℓ]
  push_cast at r ⊢
  have hlen' : (a.length : ℝ) ≤ ℓ := by exact_mod_cast hlen
  have hd : (0 : ℝ) < ℓ + a.length - 1 := by linarith [(a.length.cast_nonneg : (0 : ℝ) ≤ _)]
  rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hd]
  have h1 := mul_le_mul_of_nonneg_left hlen' (by positivity : 0 ≤ 6 * u * ℓ * dec ε)
  have h2 : 6 * u * ℓ * dec ε * ℓ ≤ 6 / 100 * dec ε := by nlinarith
  nlinarith

/-- The sizes of the two children of a node sum to at most its size. -/
private lemma sum_k_eighChild_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (smp : EighSample Su Sg N) :
    (eighChild M N signFuel R₀ β x smp true).elim 0 EighNode.k +
      (eighChild M N signFuel R₀ β x smp false).elim 0 EighNode.k ≤ x.k := by
  unfold eighChild
  split
  · simp
  · rename_i b' _ _ _
    cases b' <;> simp
  · rename_i kp hkp _ _ _ _ _ _
    simp only [if_true, Option.elim_some, Bool.false_eq_true, if_false]
    omega

/-- **The sizes at one depth sum to at most the root size**: for every machine, node
$x$, tree of samples and depth $j$, the sizes of the nodes at the paths of length $j$ sum to at
most $k_x$ (a node has no child, one child of its size, or two children of sizes $k_+$ and
$k - k_+$). [Shah2024, proof of Theorem 4.2], "$\sum_{x \in X_k} n_x \le n$". -/
theorem sum_k_eighNodeAt_ofFn_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (s : List Bool → EighSample Su Sg N) (j : ℕ) :
    ∑ a : Fin j → Bool,
      ((eighNodeAt M N signFuel R₀ β (List.ofFn a) x s).elim 0 EighNode.k) ≤ x.k := by
  induction j generalizing x s with
  | zero => simp [eighNodeAt]
  | succ j ih =>
    rw [← (Fin.consEquiv fun _ : Fin (j + 1) => Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      eighNodeAt]
    have hb : ∀ b : Bool, ∑ a : Fin j → Bool,
        ((eighChild M N signFuel R₀ β x (s []) b).bind fun y =>
          eighNodeAt M N signFuel R₀ β (List.ofFn fun i => a i) y
            fun a' => s (b :: a')).elim 0 EighNode.k ≤
        (eighChild M N signFuel R₀ β x (s []) b).elim 0 EighNode.k := by
      intro b
      rcases eighChild M N signFuel R₀ β x (s []) b with _ | y
      · simp
      · exact ih y _
    exact (add_le_add (hb true) (hb false)).trans (sum_k_eighChild_le M x (s []))

end NLAlib
