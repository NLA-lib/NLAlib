/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Global
public import NLAlib.Matrix.FinitePrecision.BinaryFloat

/-!
# Hermitian diagonalization in a bounded binary format

[Shah2024, Theorem 4.2] for a machine whose numbers have a finite exponent range: with the input
scaled so that $1/2 \le R_0 \le 1$, the floor and range hypotheses of the bit count
(`NLAlib/Eigensolvers/SpectralBisection/Global.lean`) hold in a binary format with
$\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits, the claim of [Shah2024, Section 1.2].

## Main results

* [The bounded format](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw).
* [The bounded format at a machine unit roundoff](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_logb_le_of_hasLaw_eighSampleLaw).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- The exponent-bit condition bounds $L$ by $2^{2^{E-1} - 2}$. -/
private theorem le_zpow_of_logb_logb_add_two_le {L : ℝ} {E : ℕ} (hE : 2 ≤ E) (hL : 1 ≤ L)
    (h : Real.logb 2 (Real.logb 2 L + 2) + 1 ≤ E) : L ≤ (2 : ℝ) ^ ((2 : ℤ) ^ (E - 1) - 2) := by
  have h0 : 0 ≤ Real.logb 2 L := Real.logb_nonneg one_lt_two hL
  have h1 : Real.logb 2 L + 2 ≤ (2 : ℝ) ^ (E - 1) := by
    have : Real.logb 2 (Real.logb 2 L + 2) ≤ ((E - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ E)]; linarith
    rwa [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_natCast] at this
  have h2 : Real.logb 2 L ≤ (((2 : ℤ) ^ (E - 1) - 2 : ℤ) : ℝ) := by push_cast; linarith
  rwa [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_intCast] at h2

/-- $\sqrt y \le (y + 1)/2$ for $y \ge 0$. -/
private theorem sqrt_le_add_one_div_two {y : ℝ} (hy : 0 ≤ y) : √y ≤ (y + 1) / 2 := by
  nlinarith [Real.sq_sqrt hy, sq_nonneg (√y - 1)]

/-- The range hypothesis of Theorem 4.2 from the bounded-format bound on the largest number. -/
private theorem le_of_mul_le_of_le_one {n ℓ e θ R Ω : ℝ} (hn : 0 ≤ n) (hℓ : 0 ≤ ℓ) (he : 0 < e)
    (he₁ : e ≤ 1) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hR₁ : R ≤ 1)
    (hΩ : 1536 * (n + ℓ + 2) ^ 3 ≤ Ω * (e * θ)) :
    16 * (2 * R + n + 2 * ℓ + 2 * √2 * √n + √(Real.log (96 * n * min n (ℓ + 1) / θ))) ≤ Ω := by
  set m := min n (ℓ + 1)
  set M := n + ℓ + 2
  have hm0 : 0 ≤ m := le_min hn (by linarith)
  have hmM : n * m ≤ M ^ 2 := by
    have : n * m ≤ M * M :=
      mul_le_mul (by linarith) ((min_le_right _ _).trans (by linarith)) hm0 (by linarith)
    nlinarith
  have hy : 0 ≤ 96 * n * m / θ := by positivity
  have h1 : √(Real.log (96 * n * m / θ)) ≤ 96 * n * m / θ + 1 := by
    have := (Real.sqrt_le_sqrt (Real.log_le_self hy)).trans (sqrt_le_add_one_div_two hy)
    linarith
  have h2 : (96 * n * m / θ) * θ = 96 * n * m := div_mul_cancel₀ _ hθ.ne'
  have h3 : 2 * √2 * √n ≤ 3 * (n + 1) := by
    have h2 : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc 2 * √2 * √n ≤ 2 * (3 / 2) * ((n + 1) / 2) := by
          gcongr; exact sqrt_le_add_one_div_two hn
      _ ≤ 3 * (n + 1) := by linarith
  have hM2 : 2 ≤ M := by linarith
  refine le_of_mul_le_mul_right ?_ (mul_pos he hθ)
  calc 16 * (2 * R + n + 2 * ℓ + 2 * √2 * √n + √(Real.log (96 * n * m / θ))) * (e * θ)
      ≤ 16 * (2 + n + 2 * ℓ + 3 * (n + 1) + (96 * n * m / θ + 1)) * (e * θ) := by
        gcongr; linarith
    _ = 16 * (6 + 4 * n + 2 * ℓ) * (e * θ) + 1536 * (n * m) * e := by
        linear_combination 16 * e * h2
    _ ≤ 16 * (6 + 4 * n + 2 * ℓ) + 1536 * (n * m) := by
        have := mul_le_mul_of_nonneg_left (mul_le_one₀ he₁ hθ.le hθ₁)
          (by positivity : (0 : ℝ) ≤ 16 * (6 + 4 * n + 2 * ℓ))
        have := mul_le_mul_of_nonneg_left he₁ (by positivity : (0 : ℝ) ≤ 1536 * (n * m))
        linarith
    _ ≤ 1536 * M ^ 3 := by
        have hM3 : 2 * M ^ 2 ≤ M ^ 3 := by nlinarith
        have hM1 : 2 * M ≤ M ^ 2 := by nlinarith
        linarith
    _ ≤ Ω * (e * θ) := hΩ

/-- The floor and range hypotheses of Theorem 4.2 from the bounded-format bounds. -/
private theorem mul_le_min_and_le_of_mul_le {n ℓ e θ R τ Ω : ℝ} (hn : 0 ≤ n) (hℓ : 0 ≤ ℓ)
    (he : 0 < e) (he₁ : e ≤ 1) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hR : 1 / 2 ≤ R) (hR₁ : R ≤ 1)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (1536 * (n + ℓ + 2) ^ 3) ≤ e * θ)
    (hΩ : 1536 * (n + ℓ + 2) ^ 3 ≤ Ω * (e * θ)) :
    τ * (100 * n * √n) ≤ min (√(θ / (8 * n * min n (ℓ + 1)))) (e * min R 1) ∧
      16 * (2 * R + n + 2 * ℓ + 2 * √2 * √n + √(Real.log (96 * n * min n (ℓ + 1) / θ))) ≤ Ω := by
  set M := n + ℓ + 2 with hM
  set m := min n (ℓ + 1) with hm_def
  have hM2 : 2 ≤ M := by linarith
  have hm0 : 0 ≤ m := le_min hn (by linarith)
  have hmn : m ≤ n := min_le_left _ _
  have hmM : m ≤ M := by linarith
  have hc : 0 < 1536 * M ^ 3 := by positivity
  have hs : √n ^ 2 = n := Real.sq_sqrt hn
  have hsn : √n ≤ M := by nlinarith [Real.sqrt_nonneg n]
  have hnsn : n * √n ≤ M ^ 3 := by
    have : n * √n ≤ M * M := mul_le_mul (by linarith) hsn (Real.sqrt_nonneg n) (by linarith)
    nlinarith
  have heθ : e * θ ≤ θ := mul_le_of_le_one_left hθ.le he₁
  have hX0 : 0 ≤ τ * (100 * n * √n) := by positivity
  have hX : τ * (100 * n * √n) * (1536 * M ^ 3) ≤ 100 * n * √n * (e * θ) := by
    have := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ 100 * n * √n)
    linarith
  refine ⟨le_min ?_ ?_, ?_⟩
  · rcases hn.eq_or_lt with h0 | hn0
    · simp [← h0]
    have hm1 : 0 < m := lt_min hn0 (by linarith)
    rw [← Real.sqrt_sq hX0]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_right ?_ (pow_pos hc 2)
    have h1 := pow_le_pow_left₀ (by positivity) hX 2
    have h2 : (100 * n * √n * (e * θ)) ^ 2 = 10000 * n ^ 3 * (e * θ) ^ 2 := by
      linear_combination (10000 * n ^ 2 * (e * θ) ^ 2) * hs
    have h3 : n ^ 4 * m ≤ M ^ 6 := by
      have h4 : n ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ hn (by linarith) 4
      have h5 : m ≤ M ^ 2 := hmM.trans (by nlinarith)
      calc n ^ 4 * m ≤ M ^ 4 * M ^ 2 := mul_le_mul h4 h5 hm0 (by positivity)
        _ = M ^ 6 := by ring
    have h4 : (e * θ) ^ 2 ≤ θ := by nlinarith [mul_pos he hθ]
    calc (τ * (100 * n * √n)) ^ 2 * (8 * n * m) * (1536 * M ^ 3) ^ 2
        = 8 * n * m * (τ * (100 * n * √n) * (1536 * M ^ 3)) ^ 2 := by ring
      _ ≤ 8 * n * m * (10000 * n ^ 3 * (e * θ) ^ 2) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 80000 * (n ^ 4 * m) * (e * θ) ^ 2 := by ring
      _ ≤ 80000 * M ^ 6 * θ := by gcongr
      _ ≤ θ * (1536 * M ^ 3) ^ 2 := by
          have : 0 ≤ M ^ 6 * θ := by positivity
          linarith
  · have h1 : 1 / 2 ≤ min R 1 := le_min hR (by norm_num)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 he.le)
    refine le_of_mul_le_mul_right ?_ hc
    have := mul_le_mul_of_nonneg_left hnsn (by positivity : (0 : ℝ) ≤ 100 * (e * θ))
    have := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right he.le hθ₁)
      (by positivity : (0 : ℝ) ≤ M ^ 3)
    nlinarith [mul_nonneg he.le (pow_nonneg (by linarith : (0 : ℝ) ≤ M) 3)]
  · exact le_of_mul_le_of_le_one hn hℓ he he₁ hθ hθ₁ hR₁ hΩ

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **Hermitian diagonalization in a bounded binary format, at a machine unit roundoff**: let the
machine meet `NLAlib.FloatMachine.IsAccurate` with unit roundoff $u > 0$, floor
$2^{e_{\min} + p - 1}$ (the smallest normal number) and range $\Omega$ at least half the largest
finite number $\Omega_F$ ($\Omega_F \le 2\Omega$) of a binary format with $E \ge 2$ exponent
bits, precision $p$ and smallest exponent $e_{\min}$, with the other hypotheses of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw`
(the samplers, the input, $\varepsilon$, $\theta$, $\ell$, the accuracy window for $\beta$, the
step limit and the two precision conditions on $\log_2(1/u)$), the $n \times n$ input,
$n \ge 1$, scaled so that $1/2 \le R_0 \le 1$, the ideal samples of the nodes independent, each
with law `NLAlib.eighSampleLaw` $n$, and
$$\log_2\Bigl(\log_2\frac{1536\,(n + \ell + 2)^3}{\varepsilon\theta} + 2\Bigr) + 1 \le E \,.$$
Then the failure probability is at most $\theta$. A machine built on the format may round more
than once per operation (a sampler rounds a draw and a product), so its unit roundoff exceeds
$2^{-p}$, and its range is below $\Omega_F$ when its samplers must round draws of magnitude up
to $2\Omega$. [Shah2024, Section 1.2], the exponent count there, for a machine with these
constants. -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_logb_le_of_hasLaw_eighSampleLaw
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} (fmt : Float.Model.Format)
    (hE : 2 ≤ fmt.exponentBits) {u Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) Ω μM μQ cN)
    (hu : 0 < u) (hΩ : fmt.maxFinite ≤ 2 * Ω)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀)
    (hR₀half : 1 / 2 ≤ dec R₀) (hR₀one : dec R₀ ≤ 1) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))))
    (hβge : ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))) /
      (1 + 2⁻¹ ^ 6) ≤ dec β) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n * (4 * μM n + 10 + 10 * √(n : ℝ))) +
      1 / 2 * Real.logb 2 (n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) +
      Real.logb 2 (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) +
      Real.logb 2 (ℓ * (ℓ + 1)) + Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) +
      13 ≤ Real.logb 2 u⁻¹)
    (hbits' : Real.logb 2 (dec β)⁻¹ +
      Real.logb 2 (2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) +
      16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) ≤ Real.logb 2 u⁻¹)
    (hexp : Real.logb 2 (Real.logb 2 (1536 * (n + ℓ + 2) ^ 3 / (dec ε * θ)) + 2) + 1 ≤
      fmt.exponentBits)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n} (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  have hτeq : fmt.minExponent + (fmt.mantissaBits : ℤ) - 1 =
      -((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) := by
    simp only [Float.Model.Format.minExponent]; ring
  have hB : fmt.maxExponentBound = (2 : ℤ) ^ (fmt.exponentBits - 1) - fmt.mantissaBits := by
    have h1 : 1 ≤ 2 ^ (fmt.exponentBits - 1) := Nat.one_le_two_pow
    have h2 : (2 : ℤ) ^ fmt.exponentBits = 2 * 2 ^ (fmt.exponentBits - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [Float.Model.Format.maxExponentBound, Float.Model.Format.exponentBias,
      Float.Model.Format.mantissaBits]
    rw [Nat.cast_sub h1]
    push_cast
    rw [h2]
    ring
  have hp : 1 ≤ fmt.mantissaBits := by simp only [Float.Model.Format.mantissaBits]; omega
  have hmax : 2 * (2 : ℝ) ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) ≤ fmt.maxFinite := by
    rw [Float.Model.Format.maxFinite, hB]
    have h2p : (2 : ℝ) ≤ 2 ^ fmt.mantissaBits := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
    have : 2 * (2 : ℝ) ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) =
        (2 ^ fmt.mantissaBits / 2) * 2 ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - fmt.mantissaBits) := by
      rw [← zpow_natCast, div_eq_mul_inv, ← zpow_neg_one, ← zpow_add₀ two_ne_zero,
        ← zpow_add₀ two_ne_zero, mul_comm (2 : ℝ), ← zpow_add_one₀ two_ne_zero]
      congr 1; ring
    rw [this]
    gcongr
    linarith
  set m : ℝ := (n : ℝ) + ℓ + 2 with hm_def
  have hm : 2 ≤ m := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
    linarith
  have he₁ : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hL1 : 1 ≤ 1536 * m ^ 3 / (dec ε * θ) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    linarith [mul_le_one₀ he₁ hθ.le hθ₁, one_le_pow₀ (n := 3) (by linarith : (1 : ℝ) ≤ m)]
  have hL := le_zpow_of_logb_logb_add_two_le hE hL1 (by simpa only [m] using hexp)
  have hτ : (2 : ℝ) ^ (fmt.minExponent + (fmt.mantissaBits : ℤ) - 1) *
      (1536 * m ^ 3) ≤ dec ε * θ := by
    rw [hτeq, zpow_neg, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hL
    linarith
  have hΩ' : 1536 * m ^ 3 ≤ Ω * (dec ε * θ) := by
    rw [div_le_iff₀ (by positivity)] at hL
    nlinarith [mul_le_mul_of_nonneg_right (hmax.trans hΩ) (by positivity : 0 ≤ dec ε * θ)]
  obtain ⟨h₁, h₂⟩ := mul_le_min_and_le_of_mul_le (Nat.cast_nonneg n) (Nat.cast_nonneg ℓ) hε he₁
    hθ hθ₁ hR₀half hR₀one (by positivity) hτ hΩ'
  refine hM.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw
    hunifm hunifc hnormalm hnormalc hμM hμQ hμM₀ hμQ₀ hcN hn hA hR₀ (by linarith) hε hε₁ hθ hθ₁ hℓ
    hβ hβle hβge hN hu hbits hbits' hfuel (by positivity) h₁ h₂ hind hlaw

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **Hermitian diagonalization in a bounded binary format: $\log_2\log_2(n/(\varepsilon\theta)) +
O(1)$ exponent bits suffice** (Theorem 4.2 for a finite exponent range): let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u = 2^{-p}$, floor $2^{e_{\min} + p - 1}$ (the smallest
normal number) and range the largest finite number of a binary format with $E \ge 2$ exponent
bits, precision $p$ and smallest exponent $e_{\min}$ (as
`NLAlib.exists_floatMachine_isAccurate_binaryFloatRound` provides), with the other hypotheses of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw`
(the samplers, the input, $\varepsilon$, $\theta$, $\ell$, the accuracy window for $\beta$, the
step limit), the $n \times n$ input, $n \ge 1$, scaled so that $1/2 \le R_0 \le 1$ (an exact
power-of-two scaling), the two precision conditions there with $\log_2(1/u) = p$, the ideal
samples of the nodes independent, each with law `NLAlib.eighSampleLaw` $n$, and
$$\log_2\Bigl(\log_2\frac{1536\,(n + \ell + 2)^3}{\varepsilon\theta} + 2\Bigr) + 1 \le E \,.$$
Then the failure probability is at most $\theta$. With $\ell = O(\log(1/\varepsilon))$ this is
$\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits, the claim of [Shah2024, Section 1.2]
("$\lg\lg(n/\varepsilon) + O(1)$ bits to store the exponent"), with the $\theta$ it omits. -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} (fmt : Float.Model.Format)
    (hE : 2 ≤ fmt.exponentBits) {cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀)
    (hR₀half : 1 / 2 ≤ dec R₀) (hR₀one : dec R₀ ≤ 1) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))))
    (hβge : ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))) /
      (1 + 2⁻¹ ^ 6) ≤ dec β) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n * (4 * μM n + 10 + 10 * √(n : ℝ))) +
      1 / 2 * Real.logb 2 (n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) +
      Real.logb 2 (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) +
      Real.logb 2 (ℓ * (ℓ + 1)) + Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) +
      13 ≤ fmt.mantissaBits)
    (hbits' : Real.logb 2 (dec β)⁻¹ +
      Real.logb 2 (2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) +
      16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) ≤ fmt.mantissaBits)
    (hexp : Real.logb 2 (Real.logb 2 (1536 * (n + ℓ + 2) ^ 3 / (dec ε * θ)) + 2) + 1 ≤
      fmt.exponentBits)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n} (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  refine
    hM.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_logb_le_of_hasLaw_eighSampleLaw
    fmt hE (by positivity) (by linarith [fmt.maxFinite_pos]) hunifm hunifc hnormalm hnormalc hμM
    hμQ hμM₀ hμQ₀ hcN hn hA hR₀ hR₀half hR₀one hε hε₁ hθ hθ₁ hℓ hβ hβle hβge hN ?_ ?_ hexp hfuel
    hind hlaw <;>
  rwa [inv_pow, inv_inv, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

end NLAlib
