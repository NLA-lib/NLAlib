/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Accuracy
public import NLAlib.Eigensolvers.SpectralBisection.BoundedFormat
public import NLAlib.Matrix.FinitePrecision.BinaryFloatMachine
public import Mathlib.Probability.HasLawExists
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Hermitian diagonalization: an instance in binary128

The hypotheses of Theorem 4.2 ([Shah2024, Theorem 4.2]) in its two forms,
[the bit count](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw)
and [the bounded format](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw),
are **jointly satisfiable**, so the two theorems are not vacuous. The witness is a binary format
with $p = 113$ and $E = 15$ (the layout of IEEE binary128), the machine
`NLAlib.binaryFloatMachine` of that format with round-to-nearest, ties away from zero (every
operation, the black boxes and the samplers included, rounds to the format's grid, overflow not
modelled; the black boxes are correctly rounded, $\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$,
$c_{\mathrm N} = \sqrt2$), the parameters $\varepsilon = 2^{-15}$, $\theta = 1/2$, $R_0 = 1$,
$\ell = 20$, $\beta = \hat\beta$ at its bound, and every size $1 \le n \le 1024$, with
independent node samples of law `NLAlib.eighSampleLaw` on the infinite product space
`MeasureTheory.Measure.infinitePi` (`ProbabilityTheory.exists_iid`). Two examples after the
instance apply both theorems to it. A third applies
[Theorem 4.2 at fixed parameters](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_bisectionDepth_le_of_logb_le_of_hasLaw_eighSampleLaw)
to the same machine and parameters, with $\ell =$ `NLAlib.bisectionDepth` $\varepsilon = 20$,
104 sign steps and $\beta$ at the upper end of its window: there $\Lambda \le 26$ and the
precision condition takes at most 94.3 of the 113 bits. The stored type of the machine is ℝ, so
$\beta$ and the entries of the input are real parameters, not numbers of the format; the contract
holds for every real. The selector is ties away from zero, an optional IEEE 754 attribute, not
the default ties to even; the proof uses only that the selector is a nearest selector and odd,
$r(-x) = -r(x)$, which ties to even also is.

## Main results

* `NLAlib.exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw`.
* `NLAlib.exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw_of_le`: every
  $n \ge 1$, $0 < \varepsilon \le 2^{-15}$, $\theta > 0$ and $R_0 > 0$, in a format wide
  enough for them.

Three examples at the end apply the three theorems at every parameter, each in a binary format
chosen for the parameters: the bit count and the bounded format through
`NLAlib.exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw_of_le`, and Theorem 4.2 at
fixed parameters for every $n \ge 1$, $0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$ and
$R_0 > 0$, with $p$ at least its bit count, $E$ large enough for the floor
$300n^3\tau \le \varepsilon\theta\min(R_0, 1)$ and the range $64(R_0 + n + \Lambda) \le \Omega$,
$\lceil 4\Lambda\rceil$ sign steps and $\beta$ at the upper end of its window. So the hypotheses
of all three theorems are satisfiable for every $n$, $\varepsilon$, $\theta$, $R_0$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-! ### Round to nearest, ties away from zero -/

/-- Rounding to the nearest integer, ties away from zero (odd, as ties to even is too). -/
private noncomputable def roundTiesAway (x : ℝ) : ℤ :=
  if x < 0 then -⌊-x + 1 / 2⌋ else ⌊x + 1 / 2⌋

private theorem absRelErr_roundTiesAway (x : ℝ) :
    Computation.AbsRelErr 0 (1 / 2) x (roundTiesAway x : ℝ) := by
  rw [Computation.absRelErr_iff, zero_mul, zero_add, abs_le]
  unfold roundTiesAway
  split_ifs
  · have h1 := Int.floor_le (-x + 1 / 2)
    have h2 := Int.lt_floor_add_one (-x + 1 / 2)
    push_cast
    constructor <;> linarith
  · have h1 := Int.floor_le (x + 1 / 2)
    have h2 := Int.lt_floor_add_one (x + 1 / 2)
    constructor <;> linarith

private theorem roundTiesAway_neg (x : ℝ) : roundTiesAway (-x) = -roundTiesAway x := by
  unfold roundTiesAway
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [if_neg (by linarith), if_pos h, neg_neg]
  · have : ⌊(2 : ℝ)⁻¹⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by norm_num, by norm_num⟩
    simp [this]
  · rw [if_pos (by linarith), if_neg (by linarith), neg_neg]

private theorem measurable_roundTiesAway : Measurable roundTiesAway := by
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_ ?_
  · exact (Measurable.of_discrete (f := fun k : ℤ => -k)).comp
      (Int.measurable_floor.comp (measurable_id.neg.add_const _))
  · exact Int.measurable_floor.comp (measurable_id.add_const _)

/-! ### Numerical bounds -/

/-- $\log_2 y \le k$ from $0 < y \le 2^k$. -/
private theorem logb_le_of_le_two_pow {y : ℝ} {k : ℕ} (hy : 0 < y) (h : y ≤ 2 ^ k) :
    Real.logb 2 y ≤ k := by
  have := Real.logb_le_logb_of_le one_lt_two hy h
  rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this

private theorem logb_inv_two_inv_pow (k : ℕ) : Real.logb 2 ((2 : ℝ)⁻¹ ^ k)⁻¹ = k := by
  rw [inv_pow, inv_inv, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

private theorem bisectionDepth_two_inv_pow : bisectionDepth ((2 : ℝ)⁻¹ ^ 15) = 20 := by
  unfold bisectionDepth
  rw [logb_inv_two_inv_pow, Nat.ceil_natCast]

/-- The size-dependent quantities of the bounds: $1 \le \sqrt{n m \min(n, e)} \le 2^8$,
$\sqrt{\log(96nm/\theta)} \le 4$ and $1 \le \hat T \le 2^7$ for $1 \le n \le 1024$,
$1 \le m \le 21$, $\theta = 1/2$. -/
private theorem bounds_of_le {x m e : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ 1024) (hm1 : 1 ≤ m)
    (hm : m ≤ 21) (he1 : 1 ≤ e) (he : e ≤ 3) :
    1 ≤ √(x * m * e) ∧ √(x * m * e) ≤ 2 ^ 8 ∧ x * m * e ≤ 2 ^ 16 ∧
      √(Real.log (96 * x * m / (1 / 2))) ≤ 4 ∧ √x ≤ 32 ∧ √2 ≤ 3 / 2 ∧
      1 ≤ 2 * √2 * √x + √(Real.log (96 * x * m / (1 / 2))) ∧
      2 * √2 * √x + √(Real.log (96 * x * m / (1 / 2))) ≤ 2 ^ 7 := by
  have hxm : x * m ≤ 1024 * 21 := mul_le_mul hx hm (by linarith) (by norm_num)
  have hX : x * m * e ≤ 2 ^ 16 := by
    nlinarith [mul_le_mul hxm he (by linarith) (by norm_num)]
  have hX1 : 1 ≤ x * m * e := by
    have : 1 ≤ x * m := one_le_mul_of_one_le_of_one_le hx1 hm1
    exact one_le_mul_of_one_le_of_one_le this he1
  have hy : 0 < 96 * x * m / (1 / 2) := by positivity
  have hL : Real.log (96 * x * m / (1 / 2)) ≤ 16 := by
    have hy2 : 96 * x * m / (1 / 2) ≤ 2 ^ 22 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    have := Real.log_le_log hy hy2
    rw [Real.log_pow] at this
    have := Real.log_two_lt_d9
    push_cast at *
    linarith
  have hsL : √(Real.log (96 * x * m / (1 / 2))) ≤ 4 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsx : √x ≤ 32 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hs2 : √2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs21 : 1 ≤ √2 := Real.one_le_sqrt.mpr one_le_two
  have hsx1 : 1 ≤ √x := Real.one_le_sqrt.mpr hx1
  refine ⟨Real.one_le_sqrt.mpr hX1, Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩, hX, hsL, hsx,
    hs2, ?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg (Real.log (96 * x * m / (1 / 2)))]
  · nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg 2]

/-- The accuracy at its bound, for $\ell = 20$, $\varepsilon = 2^{-15}$, $\theta = 1/2$:
$2^{-43} \le \hat\beta \le 1$. -/
private theorem le_div_and_div_le {D T : ℝ} (hD1 : 1 ≤ D) (hD : D ≤ 2 ^ 8) (hT1 : 1 ≤ T)
    (hT : T ≤ 2 ^ 7) :
    (2 : ℝ)⁻¹ ^ 43 ≤ (20 - 1) ^ 2 * (2 : ℝ)⁻¹ ^ 15 * √(1 / 2) /
        (52 * 20 ^ 2 * (2 * 20 - 1) * D * T) ∧
      (20 - 1) ^ 2 * (2 : ℝ)⁻¹ ^ 15 * √(1 / 2) / (52 * 20 ^ 2 * (2 * 20 - 1) * D * T) ≤ 1 := by
  have hDT1 : 1 ≤ D * T := one_le_mul_of_one_le_of_one_le hD1 hT1
  have hDT : D * T ≤ 2 ^ 15 := by nlinarith
  have hs : 1 / 2 ≤ √(1 / 2 : ℝ) := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hs1 : √(1 / 2 : ℝ) ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  have hc : 0 < 52 * 20 ^ 2 * (2 * 20 - 1) * D * T := by positivity
  have he : (52 : ℝ) * 20 ^ 2 * (2 * 20 - 1) * D * T = 811200 * (D * T) := by ring
  constructor
  · rw [le_div_iff₀ hc, he]
    nlinarith
  · rw [div_le_one hc, he]
    nlinarith

/-- The first precision condition at $\ell = 20$, $\varepsilon = 2^{-15}$, $\theta = 1/2$,
$\mu_{\mathrm{MM}}(d) = 2d$ and $1 \le n \le 1024$, bounded here by $83.5 \le 113$ bits (its value
at $n = 1024$ is about $81.2$). -/
private theorem logb_add_le_of_le {x m e : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ 1024) (hm1 : 1 ≤ m)
    (hm : m ≤ 21) (he1 : 1 ≤ e) (he : e ≤ 3) :
    Real.logb 2 ((2 : ℝ)⁻¹ ^ 15)⁻¹ + 3 / 2 * Real.logb 2 (1 / 2)⁻¹ +
      Real.logb 2 (x * (4 * (2 * x) + 10 + 10 * √x)) +
      1 / 2 * Real.logb 2 (x * m * e) +
      Real.logb 2 (2 * √2 * √x + √(Real.log (96 * x * m / (1 / 2)))) +
      Real.logb 2 (20 * (20 + 1)) + Real.logb 2 ((20 : ℝ) ^ 2 * (2 * 20 - 1) / (20 - 1) ^ 2) +
      13 ≤ 113 := by
  obtain ⟨-, -, hX, -, hsx, -, hT1, hT⟩ := bounds_of_le hx1 hx hm1 hm he1 he
  have hX1 : 0 < x * m * e := by positivity
  have h1 := logb_inv_two_inv_pow 15
  have h2 : Real.logb 2 (1 / 2 : ℝ)⁻¹ = 1 := by norm_num
  have h3 : Real.logb 2 (x * (4 * (2 * x) + 10 + 10 * √x)) ≤ (24 : ℕ) := by
    refine logb_le_of_le_two_pow (by positivity) ?_
    nlinarith [Real.sqrt_nonneg x]
  have h4 : Real.logb 2 (x * m * e) ≤ (16 : ℕ) := logb_le_of_le_two_pow hX1 hX
  have h5 : Real.logb 2 (2 * √2 * √x + √(Real.log (96 * x * m / (1 / 2)))) ≤ (7 : ℕ) :=
    logb_le_of_le_two_pow (by linarith) hT
  have h6 : Real.logb 2 (20 * (20 + 1) : ℝ) ≤ (9 : ℕ) :=
    logb_le_of_le_two_pow (by norm_num) (by norm_num)
  have h7 : Real.logb 2 ((20 : ℝ) ^ 2 * (2 * 20 - 1) / (20 - 1) ^ 2) ≤ (6 : ℕ) :=
    logb_le_of_le_two_pow (by norm_num) (by norm_num)
  push_cast at h1 h3 h4 h5 h6 h7
  rw [h1, h2]
  calc _ ≤ (15 : ℝ) + 3 / 2 * 1 + 24 + 1 / 2 * 16 + 7 + 9 + 6 + 13 := by gcongr
    _ ≤ 113 := by norm_num

/-- The step count of the sign function at $\ell = 20$, $\theta = 1/2$ and an accuracy
$\beta \ge 2^{-43}$: $0 \le N_* \le 57$. -/
private theorem newtonSchulzSteps_nonneg_and_le {x β : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ 1024)
    (hβ : (2 : ℝ)⁻¹ ^ 43 ≤ β) (hβ1 : β ≤ 1) :
    0 ≤ newtonSchulzSteps (1 / 2 / (12 * x * 20 * (20 + 1))) (β / (16 * x)) ∧
      newtonSchulzSteps (1 / 2 / (12 * x * 20 * (20 + 1))) (β / (16 * x)) ≤ 57 := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hs : 0 < 1 / 2 / (12 * x * 20 * (20 + 1)) := by positivity
  have hs1 : 1 / 2 / (12 * x * 20 * (20 + 1)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hε : 0 < β / (16 * x) := by positivity
  have hε1 : β / (16 * x) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  refine ⟨newtonSchulzSteps_nonneg hs hs1 hε hε1, ?_⟩
  unfold newtonSchulzSteps
  rw [abs_of_pos hs, min_eq_left hs1]
  have hA : Real.logb 2 (1 / 2 / (12 * x * 20 * (20 + 1)))⁻¹ ≤ (24 : ℕ) := by
    refine logb_le_of_le_two_pow (by positivity) ?_
    rw [inv_div]
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hinv : (β / (16 * x))⁻¹ ≤ 2 ^ 57 := by
    rw [inv_div, div_le_iff₀ hβ0]
    have : (2 : ℝ) ^ 57 * (2 : ℝ)⁻¹ ^ 43 = 2 ^ 14 := by norm_num
    nlinarith
  have hinv1 : 16 ≤ (β / (16 * x))⁻¹ := by
    rw [inv_div, le_div_iff₀ hβ0]; nlinarith
  have hB : Real.logb 2 (β / (16 * x))⁻¹ ≤ (57 : ℕ) :=
    logb_le_of_le_two_pow (by positivity) hinv
  have h16 : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    norm_num
  have hB4 : 4 ≤ Real.logb 2 (β / (16 * x))⁻¹ := by
    have := Real.logb_le_logb_of_le one_lt_two (by norm_num) hinv1
    rwa [h16] at this
  have hC : Real.logb 2 (Real.logb 2 (β / (16 * x))⁻¹) ≤ (6 : ℕ) := by
    push_cast at hB
    exact logb_le_of_le_two_pow (by linarith) (hB.trans (by norm_num))
  push_cast at hA hC
  linarith

/-- The second precision condition at $\ell = 20$, $\theta = 1/2$, $\mu_{\mathrm{MM}}(d) =
\mu_{\mathrm{QR}}(d) = 2d$, $c_{\mathrm N} = \sqrt2$, $1 \le n \le 1024$ and
$2^{-43} \le \beta \le 1$, bounded here by $78 \le 113$ bits (about $75.2$ at $n = 1024$ and
$\beta = \hat\beta$). -/
private theorem logb_inv_add_logb_le {x β : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ 1024)
    (hβ : (2 : ℝ)⁻¹ ^ 43 ≤ β) (hβ1 : β ≤ 1) :
    Real.logb 2 β⁻¹ + Real.logb 2 (2048 * (x + newtonSchulzSteps (1 / 2 / (12 * x * 20 * (20 + 1)))
      (β / (16 * x)) + 1) * (4 * (2 * x) + 10 + 10 * √x) +
      16 * (4 * (2 * x) + 4 * √x * (√2 + 1) + 2 * (2 * x) + 1)) ≤ 113 := by
  obtain ⟨hN0, hN⟩ := newtonSchulzSteps_nonneg_and_le hx1 hx hβ hβ1
  set N := newtonSchulzSteps (1 / 2 / (12 * x * 20 * (20 + 1))) (β / (16 * x))
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hsx : √x ≤ 32 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hs2 : √2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h1 : Real.logb 2 β⁻¹ ≤ (43 : ℕ) := by
    refine logb_le_of_le_two_pow (by positivity) ?_
    rw [inv_le_comm₀ hβ0 (by positivity), ← inv_pow]
    exact hβ
  have h2 : Real.logb 2 (2048 * (x + N + 1) * (4 * (2 * x) + 10 + 10 * √x) +
      16 * (4 * (2 * x) + 4 * √x * (√2 + 1) + 2 * (2 * x) + 1)) ≤ (35 : ℕ) := by
    refine logb_le_of_le_two_pow (by positivity) ?_
    have ha : x + N + 1 ≤ 1082 := by linarith
    have hb : 4 * (2 * x) + 10 + 10 * √x ≤ 8522 := by linarith
    have hc : 4 * √x * (√2 + 1) ≤ 320 := by nlinarith [Real.sqrt_nonneg x]
    have hab := mul_le_mul ha hb (by positivity) (by norm_num)
    nlinarith
  push_cast at h1 h2
  linarith

/-- The floor condition: $\tau\cdot 100n^{3/2} \le \min(\sqrt{\theta/(8nm)}, \varepsilon)$ for
$\tau \le 2^{-40}$, $1 \le n \le 1024$, $1 \le m \le 21$, $\theta = 1/2$, $\varepsilon =
2^{-15}$. -/
private theorem mul_le_min_of_le {x m τ : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ 1024) (hm1 : 1 ≤ m)
    (hm : m ≤ 21) (hτ : τ ≤ (2 : ℝ)⁻¹ ^ 40) :
    τ * (100 * x * √x) ≤ min (√(1 / 2 / (8 * x * m))) ((2 : ℝ)⁻¹ ^ 15 * min 1 1) := by
  have hsx : √x ≤ 32 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : 100 * x * √x ≤ 2 ^ 22 := by nlinarith [Real.sqrt_nonneg x]
  have hl : τ * (100 * x * √x) ≤ (2 : ℝ)⁻¹ ^ 18 := by
    calc τ * (100 * x * √x) ≤ (2 : ℝ)⁻¹ ^ 40 * 2 ^ 22 :=
          mul_le_mul hτ hp (by positivity) (by positivity)
      _ = (2 : ℝ)⁻¹ ^ 18 := by norm_num
  refine le_min ?_ ?_
  · refine hl.trans ?_
    rw [Real.le_sqrt (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    have : 8 * x * m ≤ 8 * 1024 * 21 := by nlinarith
    nlinarith
  · rw [min_self, mul_one]
    exact hl.trans (by norm_num)

/-- The range condition, for $1 \le n \le 1024$, $1 \le m \le 21$, $\theta = 1/2$, $R_0 = 1$,
$\ell = 20$ and $\Omega \ge 2^{15}$. -/
private theorem mul_add_le_of_le {x m Ω : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ 1024) (hm1 : 1 ≤ m)
    (hm : m ≤ 21) (hΩ : 2 ^ 15 ≤ Ω) :
    16 * (2 * 1 + x + 2 * 20 + 2 * √2 * √x + √(Real.log (96 * x * m / (1 / 2)))) ≤ Ω := by
  obtain ⟨-, -, -, hL, -, -, -, hT⟩ := bounds_of_le (e := 1) hx1 hx hm1 hm le_rfl (by norm_num)
  linarith

/-- The exponent condition at $\ell = 20$, $\varepsilon = 2^{-15}$, $\theta = 1/2$ and
$1 \le n \le 1024$, bounded here by $7 \le 15$ exponent bits (about $6.9$ at $n = 1024$). -/
private theorem logb_logb_add_le {x : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ 1024) :
    Real.logb 2 (Real.logb 2 (1536 * (x + 20 + 2) ^ 3 / ((2 : ℝ)⁻¹ ^ 15 * (1 / 2))) + 2) + 1 ≤
      15 := by
  have hY : 1536 * (x + 20 + 2) ^ 3 / ((2 : ℝ)⁻¹ ^ 15 * (1 / 2)) ≤ 2 ^ 60 := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : (x + 20 + 2) ^ 3 ≤ (2 ^ 11) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    norm_num at h3 ⊢
    linarith
  have hY1 : 1 ≤ 1536 * (x + 20 + 2) ^ 3 / ((2 : ℝ)⁻¹ ^ 15 * (1 / 2)) := by
    rw [le_div_iff₀ (by positivity)]
    have : 1 ≤ (x + 20 + 2) ^ 3 := one_le_pow₀ (by linarith)
    norm_num
    linarith
  have h1 := logb_le_of_le_two_pow (by linarith) hY
  have h0 := Real.logb_nonneg one_lt_two hY1
  have h2 : Real.logb 2 (Real.logb 2 (1536 * (x + 20 + 2) ^ 3 / ((2 : ℝ)⁻¹ ^ 15 * (1 / 2))) +
      2) ≤ (6 : ℕ) := by
    push_cast at h1
    have h62 : (62 : ℝ) ≤ 2 ^ 6 := by norm_num
    exact logb_le_of_le_two_pow (by linarith) (by linarith)
  push_cast at h2
  linarith

/-! ### The format and the samples -/

/-- The constants of a format with $p = 113$ and $E = 15$: $u = 2^{-113}$, $\tau = 2^{-16382}
\le 2^{-40}$, $\Omega \ge 2^{15}$. -/
private theorem format_bounds {fmt : Float.Model.Format} (hp : fmt.mantissaBits = 113)
    (hE : fmt.exponentBits = 15) :
    (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) ≤ (2 : ℝ)⁻¹ ^ 40 ∧
      (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) ≤ 1 ∧ 2 ^ 15 ≤ fmt.maxFinite := by
  have hmin : fmt.minExponent + (fmt.mantissaBits : ℤ) - 1 = -16382 := by
    simp only [Float.Model.Format.minExponent, hE, hp]; norm_num
  have hw : fmt.mantissaBitsWithoutImplicit = 112 := by
    simp only [Float.Model.Format.mantissaBits] at hp; omega
  have hmax : fmt.maxExponentBound = 16271 := by
    simp only [Float.Model.Format.maxExponentBound, Float.Model.Format.exponentBias, hE, hw]
    norm_num
  have h40 : (2 : ℝ) ^ (-16382 : ℤ) ≤ (2 : ℝ)⁻¹ ^ 40 := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ one_le_two (by norm_num)
  rw [hmin]
  refine ⟨h40, h40.trans (by norm_num), ?_⟩
  rw [Float.Model.Format.maxFinite, hmax, hp]
  have h1 : (1 : ℝ) ≤ 2 ^ 113 - 1 := by norm_num
  have h2 : (2 : ℝ) ^ 15 ≤ 2 ^ (16271 : ℤ) := by
    rw [← zpow_natCast]; exact zpow_le_zpow_right₀ one_le_two (by norm_num)
  calc (2 : ℝ) ^ 15 ≤ 1 * 2 ^ (16271 : ℤ) := by rw [one_mul]; exact h2
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

/-- Independent node samples of law `NLAlib.eighSampleLaw`, on the infinite product space. -/
private theorem exists_iIndepFun_hasLaw_eighSampleLaw (n : ℕ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ : Measure Ω')
      (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
      IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ := by
  have : IsProbabilityMeasure (eighSampleLaw n) := by
    unfold eighSampleLaw
    have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)) :=
      ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by simp [Real.volume_Icc])
        (by simp [Real.volume_Icc])
    infer_instance
  obtain ⟨Ω', mΩ', μ, ζ, -, hlaw, hind, hμ⟩ := exists_iid (List Bool) (eighSampleLaw n)
  exact ⟨Ω', mΩ', μ, ζ, hμ, hind, hlaw⟩

/-! ### The instance -/

-- Docstring lines name the two theorems and exceed 100 characters.
set_option linter.style.longLine false in
/-- The hypotheses of Theorem 4.2 are satisfiable in binary128: for a binary format `fmt`
with precision $p = 113$ and $E = 15$ exponent bits (the layout of IEEE binary128) there is a
nearest selector $r$ (ties away from zero; any odd nearest selector, ties to even included,
would do) such that the machine `NLAlib.binaryFloatMachine` of `fmt` and $r$, which rounds its
arithmetic to the format's grid (overflow not modelled; negation is exact and the uniform
sampler clamps to the scale, so off-grid inputs can give off-grid results) with correctly
rounded black boxes, meets
the contract `NLAlib.FloatMachine.IsAccurate` with the identity decoding, $u = 2^{-p}$, floor
$\tau = 2^{e_{\min} + p - 1}$, range the largest finite number,
$\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$ (monotone, nonnegative) and
$c_{\mathrm N} = \sqrt2$, its samplers have measurable fibres and countable ranges, and for every
size $1 \le n \le 1024$, with $\varepsilon = 2^{-15}$, $\theta = 1/2$, $R_0 = 1$ (every Hermitian
input of spectral norm at most $1$; the stored type is ℝ, so the input and $\beta$ are real
parameters, not numbers of the format), $m = \min(n, \ell + 1)$,
$\hat T = 2\sqrt2\sqrt n + \sqrt{\log(96nm/\theta)}$ and
$N_* = N(\theta/(12n\ell(\ell + 1)), \beta/(16n))$ (`NLAlib.newtonSchulzSteps`), there are a
depth $\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$ and an accuracy
$$0 < \beta \le \hat\beta = \frac{(\ell - 1)^2\varepsilon\sqrt\theta}{52\ell^2(2\ell - 1)
\sqrt{nm\min(n, e)}\,\hat T} \,, \qquad \frac{\hat\beta}{1 + 2^{-6}} \le \beta \,,$$
meeting the two precision conditions with $p$ bits, the floor and range conditions, the
exponent condition with $E$ bits, and independent node samples $\zeta_a$, $a$ a list of
booleans, each of law `NLAlib.eighSampleLaw` $n$, on a probability space. These are the
hypotheses of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw`
and of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw`,
so neither is vacuous: the examples below apply both. The witnesses are $\ell = 20$,
$\beta = \hat\beta$ (about 81.2 and 75.2 of the 113 bits and 6.9 of the 15 exponent bits at
$n = 1024$) and the infinite
product of the sample laws. No printed source. -/
theorem exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw
    (fmt : Float.Model.Format) (hp : fmt.mantissaBits = 113) (hE : fmt.exponentBits = 15) :
    ∃ r : ℝ → ℤ, (∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) ∧
      (binaryFloatMachine fmt r).IsAccurate id ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
        ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite (fun d => 2 * d)
        (fun d => 2 * d) √2 ∧
      (∀ c z, MeasurableSet ((binaryFloatMachine fmt r).unif c ⁻¹' {z})) ∧
      (∀ c, (Set.range ((binaryFloatMachine fmt r).unif c)).Countable) ∧
      (∀ z, MeasurableSet ((binaryFloatMachine fmt r).normal ⁻¹' {z})) ∧
      (Set.range (binaryFloatMachine fmt r).normal).Countable ∧
      Monotone (fun d : ℕ => 2 * (d : ℝ)) ∧ 0 < (2 : ℝ)⁻¹ ^ fmt.mantissaBits ∧
      Real.logb 2 ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)⁻¹ = fmt.mantissaBits ∧
      2 ≤ fmt.exponentBits ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ 1024 → ∃ (ℓ : ℕ) (β : ℝ),
        bisectionDepth ((2 : ℝ)⁻¹ ^ 15) ≤ ℓ ∧ 0 < β ∧
        β ≤ ((ℓ : ℝ) - 1) ^ 2 * (2 : ℝ)⁻¹ ^ 15 * √(1 / 2) / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
          √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
          (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / (1 / 2))))) ∧
        ((ℓ : ℝ) - 1) ^ 2 * (2 : ℝ)⁻¹ ^ 15 * √(1 / 2) / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
          √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
          (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / (1 / 2))))) /
          (1 + 2⁻¹ ^ 6) ≤ β ∧
        Real.logb 2 ((2 : ℝ)⁻¹ ^ 15)⁻¹ + 3 / 2 * Real.logb 2 (1 / 2)⁻¹ +
          Real.logb 2 (n * (4 * (2 * n) + 10 + 10 * √(n : ℝ))) +
          1 / 2 * Real.logb 2 (n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) +
          Real.logb 2 (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / (1 / 2)))) +
          Real.logb 2 (ℓ * (ℓ + 1)) + Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) +
          13 ≤ fmt.mantissaBits ∧
        Real.logb 2 β⁻¹ + Real.logb 2 (2048 * (n + newtonSchulzSteps
          (1 / 2 / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n)) + 1) *
          (4 * (2 * n) + 10 + 10 * √(n : ℝ)) +
          16 * (4 * (2 * n) + 4 * √(n : ℝ) * (√2 + 1) + 2 * (2 * n) + 1)) ≤ fmt.mantissaBits ∧
        (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) * (100 * n * √(n : ℝ)) ≤
          min (√(1 / 2 / (8 * n * min (n : ℝ) (ℓ + 1)))) ((2 : ℝ)⁻¹ ^ 15 * min 1 1) ∧
        16 * (2 * 1 + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
          √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / (1 / 2)))) ≤ fmt.maxFinite ∧
        Real.logb 2 (Real.logb 2 (1536 * (n + ℓ + 2) ^ 3 / ((2 : ℝ)⁻¹ ^ 15 * (1 / 2))) + 2) + 1 ≤
          fmt.exponentBits ∧
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ : Measure Ω')
          (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
          IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ := by
  obtain ⟨hτ40, hτ1, hΩ⟩ := format_bounds hp hE
  refine ⟨roundTiesAway, absRelErr_roundTiesAway,
    isAccurate_binaryFloatMachine absRelErr_roundTiesAway roundTiesAway_neg hτ1,
    measurableSet_preimage_unif_binaryFloatMachine fmt measurable_roundTiesAway,
    countable_range_unif_binaryFloatMachine fmt _,
    measurableSet_preimage_normal_binaryFloatMachine fmt measurable_roundTiesAway,
    countable_range_normal_binaryFloatMachine fmt _,
    fun a b h => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (by norm_num), by positivity,
    logb_inv_two_inv_pow _, by omega,
    fun n hn1 hn => ?_⟩
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hx : (n : ℝ) ≤ 1024 := by exact_mod_cast hn
  have h20 : ((20 : ℕ) : ℝ) = 20 := by norm_num
  have hm1 : (1 : ℝ) ≤ min (n : ℝ) (20 + 1) := le_min hx1 (by norm_num)
  have hm : min (n : ℝ) (20 + 1) ≤ 21 := (min_le_right _ _).trans (by norm_num)
  have he1 : (1 : ℝ) ≤ min (n : ℝ) (Real.exp 1) :=
    le_min hx1 (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have he : min (n : ℝ) (Real.exp 1) ≤ 3 :=
    (min_le_right _ _).trans (by linarith [Real.exp_one_lt_d9])
  obtain ⟨hD1, hD, -, -, -, -, hT1, hT⟩ := bounds_of_le hx1 hx hm1 hm he1 he
  obtain ⟨hβ43, hβ1⟩ := le_div_and_div_le hD1 hD hT1 hT
  set β := (20 - 1) ^ 2 * (2 : ℝ)⁻¹ ^ 15 * √(1 / 2) / (52 * 20 ^ 2 * (2 * 20 - 1) *
    √(n * min (n : ℝ) (20 + 1) * min (n : ℝ) (Real.exp 1)) *
    (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (20 + 1) / (1 / 2))))) with hβdef
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ43
  refine ⟨20, β, by rw [bisectionDepth_two_inv_pow], hβ0, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    exists_iIndepFun_hasLaw_eighSampleLaw n⟩
  · rw [h20]
  · rw [h20, ← hβdef]
    exact div_le_self hβ0.le (by norm_num)
  · rw [h20, hp]
    exact logb_add_le_of_le hx1 hx hm1 hm he1 he
  · rw [h20, hp]
    exact logb_inv_add_logb_le hx1 hx hβ43 hβ1
  · rw [h20]
    exact mul_le_min_of_le hx1 hx hm1 hm hτ40
  · rw [h20]
    exact mul_add_le_of_le hx1 hx hm1 hm hΩ
  · rw [h20, hE]
    exact logb_logb_add_le hx1 hx

/-- Theorem 4.2 in bits applies to the binary128 instance: the failure probability of
`NLAlib.eigh` is at most $\theta = 1/2$ on a probability space that exists. -/
example (fmt : Float.Model.Format) (hp : fmt.mantissaBits = 113) (hE : fmt.exponentBits = 15)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 1024) {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)}
    (hA : (decodeMatrix id A).IsHermitian) (hR₀ : specNorm (decodeMatrix id A) ≤ 1) :
    ∃ (r : ℝ → ℤ) (ℓ signFuel : ℕ) (β : ℝ) (Ω' : Type) (_ : MeasurableSpace Ω')
      (μ : Measure Ω') (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
      IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ (∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) ∧
      μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix id A)
        (decodeMatrix id (eigh (binaryFloatMachine fmt r) signFuel ℓ A 1 ((2 : ℝ)⁻¹ ^ 15) β
          fun a => ζ a ω).1)
        (fun i => (eigh (binaryFloatMachine fmt r) signFuel ℓ A 1 ((2 : ℝ)⁻¹ ^ 15) β
          fun a => ζ a ω).2 i) (2 * (2 : ℝ)⁻¹ ^ 15 * 1) ((2 : ℝ)⁻¹ ^ 15 / 3)} ≤ 1 / 2 := by
  obtain ⟨r, -, hM, hunifm, hunifc, hnormalm, hnormalc, hmono, hu, hlogu, -, hall⟩ :=
    exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw fmt hp hE
  obtain ⟨ℓ, β, hℓ, hβ, hβle, hβge, hbits, hbits', hτ, hΩ, -, Ω', mΩ', μ, ζ, hμ, hind, hlaw⟩ :=
    hall n hn1 hn
  refine ⟨r, ℓ, ⌈newtonSchulzSteps (1 / 2 / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n))⌉₊, β, Ω', mΩ',
    μ, ζ, hμ, hind, hlaw, ?_⟩
  rw [← hlogu] at hbits hbits'
  exact hM.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw
    hunifm hunifc hnormalm hnormalc hmono hmono (by norm_num) (by norm_num) (Real.sqrt_nonneg 2)
    hn1 hA hR₀ one_pos (pow_pos (by norm_num) _) le_rfl (by norm_num) (by norm_num) hℓ hβ hβle
    hβge rfl hu hbits hbits' (Nat.le_ceil _) (by positivity) hτ hΩ hind hlaw

/-- Theorem 4.2 in a bounded format applies to the binary128 instance: the failure probability
of `NLAlib.eigh` is at most $\theta = 1/2$ on a probability space that exists. -/
example (fmt : Float.Model.Format) (hp : fmt.mantissaBits = 113) (hE : fmt.exponentBits = 15)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 1024) {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)}
    (hA : (decodeMatrix id A).IsHermitian) (hR₀ : specNorm (decodeMatrix id A) ≤ 1) :
    ∃ (r : ℝ → ℤ) (ℓ signFuel : ℕ) (β : ℝ) (Ω' : Type) (_ : MeasurableSpace Ω')
      (μ : Measure Ω') (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
      IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ (∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) ∧
      μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix id A)
        (decodeMatrix id (eigh (binaryFloatMachine fmt r) signFuel ℓ A 1 ((2 : ℝ)⁻¹ ^ 15) β
          fun a => ζ a ω).1)
        (fun i => (eigh (binaryFloatMachine fmt r) signFuel ℓ A 1 ((2 : ℝ)⁻¹ ^ 15) β
          fun a => ζ a ω).2 i) (2 * (2 : ℝ)⁻¹ ^ 15 * 1) ((2 : ℝ)⁻¹ ^ 15 / 3)} ≤ 1 / 2 := by
  obtain ⟨r, -, hM, hunifm, hunifc, hnormalm, hnormalc, hmono, -, -, hE2, hall⟩ :=
    exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw fmt hp hE
  obtain ⟨ℓ, β, hℓ, hβ, hβle, hβge, hbits, hbits', -, -, hexp, Ω', mΩ', μ, ζ, hμ, hind, hlaw⟩ :=
    hall n hn1 hn
  refine ⟨r, ℓ, ⌈newtonSchulzSteps (1 / 2 / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n))⌉₊, β, Ω', mΩ',
    μ, ζ, hμ, hind, hlaw, ?_⟩
  exact
    hM.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw
    fmt hE2 hunifm hunifc hnormalm hnormalc hmono hmono (by norm_num) (by norm_num)
    (Real.sqrt_nonneg 2) hn1 hA hR₀ (by norm_num) le_rfl (pow_pos (by norm_num) _) le_rfl
    (by norm_num) (by norm_num) hℓ hβ hβle hβge rfl hbits hbits' hexp (Nat.le_ceil _) hind hlaw

/-- The floor and range of a format with $p = 113$ and $E = 15$ at the fixed parameters:
$\tau = 2^{-16382} \le 2^{-60}$ and $\Omega \ge 2^{20}$. -/
private theorem format_bounds_sixty {fmt : Float.Model.Format} (hp : fmt.mantissaBits = 113)
    (hE : fmt.exponentBits = 15) :
    (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) ≤ (2 : ℝ)⁻¹ ^ 60 ∧
      2 ^ 20 ≤ fmt.maxFinite := by
  have hmin : fmt.minExponent + (fmt.mantissaBits : ℤ) - 1 = -16382 := by
    simp only [Float.Model.Format.minExponent, hE, hp]; norm_num
  have hw : fmt.mantissaBitsWithoutImplicit = 112 := by
    simp only [Float.Model.Format.mantissaBits] at hp; omega
  have hmax : fmt.maxExponentBound = 16271 := by
    simp only [Float.Model.Format.maxExponentBound, Float.Model.Format.exponentBias, hE, hw]
    norm_num
  rw [hmin]
  refine ⟨?_, ?_⟩
  · rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ one_le_two (by norm_num)
  rw [Float.Model.Format.maxFinite, hmax, hp]
  have h1 : (1 : ℝ) ≤ 2 ^ 113 - 1 := by norm_num
  have h2 : (2 : ℝ) ^ 20 ≤ 2 ^ (16271 : ℤ) := by
    rw [← zpow_natCast]; exact zpow_le_zpow_right₀ one_le_two (by norm_num)
  calc (2 : ℝ) ^ 20 ≤ 1 * 2 ^ (16271 : ℤ) := by rw [one_mul]; exact h2
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

-- The name of the theorem applied exceeds 100 characters.
set_option linter.style.longLine false in
/-- Theorem 4.2 at fixed parameters applies to the binary128 instance: with
$\varepsilon = 2^{-15}$, $\theta = 1/2$, $R_0 = 1$, $1 \le n \le 1024$ (so
$16 \le \Lambda \le 26$), the depth `NLAlib.bisectionDepth` $\varepsilon = 20$, $104$ sign steps
and $\beta$ at the upper end of its window, the precision condition asks for at most 94.3 of the
113 bits, and the failure probability of `NLAlib.eigh` is at most $1/2$. -/
example (fmt : Float.Model.Format) (hp : fmt.mantissaBits = 113) (hE : fmt.exponentBits = 15)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 1024) {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)}
    (hA : (decodeMatrix id A).IsHermitian) (hR₀ : specNorm (decodeMatrix id A) ≤ 1) :
    ∃ (r : ℝ → ℤ) (β : ℝ) (Ω' : Type) (_ : MeasurableSpace Ω')
      (μ : Measure Ω') (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
      IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ (∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) ∧
      μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix id A)
        (decodeMatrix id (eigh (binaryFloatMachine fmt r) 104
          (bisectionDepth ((2 : ℝ)⁻¹ ^ 15)) A 1 ((2 : ℝ)⁻¹ ^ 15) β fun a => ζ a ω).1)
        (fun i => (eigh (binaryFloatMachine fmt r) 104 (bisectionDepth ((2 : ℝ)⁻¹ ^ 15)) A 1
          ((2 : ℝ)⁻¹ ^ 15) β fun a => ζ a ω).2 i) (2 * (2 : ℝ)⁻¹ ^ 15 * 1)
        ((2 : ℝ)⁻¹ ^ 15 / 3)} ≤ 1 / 2 := by
  obtain ⟨r, -, hM, hunifm, hunifc, hnormalm, hnormalc, -, -, hlogu, -, hall⟩ :=
    exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw fmt hp hE
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, Ω', mΩ', μ, ζ, hμ, hind, hlaw⟩ := hall n hn1 hn
  obtain ⟨hτ60, hΩ20⟩ := format_bounds_sixty hp hE
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hx : (n : ℝ) ≤ 1024 := by exact_mod_cast hn
  have hk0 : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two hx1
  have hk : Real.logb 2 n ≤ 10 :=
    logb_le_of_le_two_pow (k := 10) (by linarith) (hx.trans (by norm_num))
  set Λ := Real.logb 2 ((2 : ℝ)⁻¹ ^ 15)⁻¹ + Real.logb 2 (1 / 2 : ℝ)⁻¹ + Real.logb 2 n with hΛ
  have hΛv : Λ = 16 + Real.logb 2 n := by
    rw [hΛ, logb_inv_two_inv_pow, one_div, inv_inv, Real.logb_self_eq_one one_lt_two]
    push_cast; ring
  have hlΛ : Real.logb 2 Λ ≤ 5 :=
    logb_le_of_le_two_pow (k := 5) (by linarith) (by norm_num; linarith)
  have hnΛ : 0 < (n : ℝ) * Λ := by nlinarith
  refine ⟨r, (2 : ℝ)⁻¹ ^ 15 * √(1 / 2) / (1024 * (n * Λ) * √(n * Λ)), Ω', mΩ', μ, ζ, hμ, hind,
    hlaw, ?_⟩
  have hn3 : (n : ℝ) ^ 3 ≤ 2 ^ 30 := by
    calc (n : ℝ) ^ 3 ≤ 1024 ^ 3 := pow_le_pow_left₀ (by linarith) hx 3
      _ = 2 ^ 30 := by norm_num
  have hτ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) := by positivity
  exact
    hM.measureReal_not_isApproxDiagonalization_eigh_bisectionDepth_le_of_logb_le_of_hasLaw_eighSampleLaw
    hunifm hunifc hnormalm hnormalc hn1 hA hR₀ one_pos (pow_pos (by norm_num) _) le_rfl
    (by norm_num) (by norm_num) hΛ
    (div_le_div_of_nonneg_left (by dsimp only [id]; positivity)
      (mul_pos (mul_pos (by norm_num) hnΛ) (Real.sqrt_pos.2 hnΛ))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hnΛ.le)
        (Real.sqrt_nonneg _))) le_rfl
    (by
      dsimp only [id]
      rw [hlogu, hp, logb_inv_two_inv_pow, one_div, inv_inv, Real.logb_self_eq_one one_lt_two]
      push_cast; nlinarith)
    (by push_cast; linarith) hτ0
    (by
      calc 300 * (n : ℝ) ^ 3 * (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)
          ≤ 300 * 2 ^ 30 * (2 : ℝ)⁻¹ ^ 60 := by gcongr
        _ ≤ (2 : ℝ)⁻¹ ^ 15 * (1 / 2) * min 1 1 := by norm_num)
    (by calc 64 * (1 + (n : ℝ) + Λ) ≤ 2 ^ 20 := by linarith
          _ ≤ fmt.maxFinite := hΩ20) hind hlaw

/-! ### Every parameter, in a wide enough format -/

/-- A format with $E \ge K + 3$ exponent bits has floor $\tau \le 2^{-K}$ and largest finite
number at least $2^K$, whatever its precision. -/
private theorem two_zpow_le_and_le_maxFinite (fmt : Float.Model.Format) {K : ℕ}
    (hK : K + 3 ≤ fmt.exponentBits) :
    (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) ≤ ((2 : ℝ) ^ K)⁻¹ ∧
      (2 : ℝ) ^ K ≤ fmt.maxFinite := by
  have hE : 2 ≤ fmt.exponentBits := by omega
  have hpowN : K + 2 ≤ 2 ^ (fmt.exponentBits - 1) :=
    (Nat.lt_two_pow_self (n := K + 2)).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hpow : (K : ℤ) + 2 ≤ (2 : ℤ) ^ (fmt.exponentBits - 1) := by exact_mod_cast hpowN
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
  rw [hτeq, ← zpow_natCast, ← zpow_neg]
  refine ⟨zpow_le_zpow_right₀ one_le_two (by linarith), ?_⟩
  have hle : (2 : ℝ) ^ (K : ℤ) ≤ 2 ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) :=
    zpow_le_zpow_right₀ one_le_two (by linarith)
  have hpos : (0 : ℝ) < 2 ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) := by positivity
  linarith

/-- **A wide enough format exists**: for reals $B_1, B_2, X, Q$ there is a binary format with
$p \ge B_1, B_2$, $E \ge \max(X, 2)$, floor $\tau \le 1$ with $\tau Q \le 1$, and largest finite
number at least $Q$. Every condition asks for more precision, more exponent bits, a smaller
floor or a larger range, so one format meets them all. -/
private theorem exists_format_le (B₁ B₂ X Q : ℝ) :
    ∃ fmt : Float.Model.Format, B₁ ≤ fmt.mantissaBits ∧ B₂ ≤ fmt.mantissaBits ∧
      X ≤ fmt.exponentBits ∧ 2 ≤ fmt.exponentBits ∧
      (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) ≤ 1 ∧
      (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) * Q ≤ 1 ∧ Q ≤ fmt.maxFinite := by
  set K := ⌈Q⌉₊
  let fmt : Float.Model.Format :=
    { mantissaBitsWithoutImplicit := ⌈max B₁ B₂⌉₊ + 1, hm := by omega,
      exponentBits := max ⌈X⌉₊ (K + 3), he := by omega }
  have hpe : (fmt.mantissaBits : ℝ) = ⌈max B₁ B₂⌉₊ + 2 := by
    simp only [fmt, Float.Model.Format.mantissaBits]; push_cast; ring
  have hEe : fmt.exponentBits = max ⌈X⌉₊ (K + 3) := rfl
  obtain ⟨hτ, hΩ⟩ := two_zpow_le_and_le_maxFinite fmt (K := K) (by rw [hEe]; omega)
  have hQK : Q ≤ (2 : ℝ) ^ K :=
    (Nat.le_ceil Q).trans (by exact_mod_cast (Nat.lt_two_pow_self (n := K)).le)
  have hτ0 : (0 : ℝ) ≤ 2 ^ (fmt.minExponent + fmt.mantissaBits - 1) := by positivity
  have hK1 : ((2 : ℝ) ^ K)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  have hm := Nat.le_ceil (max B₁ B₂)
  refine ⟨fmt, ?_, ?_, ?_, by rw [hEe]; omega, hτ.trans hK1, ?_, hQK.trans hΩ⟩
  · rw [hpe]; linarith [le_max_left B₁ B₂]
  · rw [hpe]; linarith [le_max_right B₁ B₂]
  · rw [hEe]
    exact (Nat.le_ceil X).trans (by exact_mod_cast le_max_left _ _)
  · calc _ ≤ (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) * 2 ^ K :=
          mul_le_mul_of_nonneg_left hQK hτ0
      _ ≤ ((2 : ℝ) ^ K)⁻¹ * 2 ^ K := mul_le_mul_of_nonneg_right hτ (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)

-- Docstring lines name the two theorems and exceed 100 characters.
set_option linter.style.longLine false in
/-- The hypotheses of Theorem 4.2 are satisfiable at every parameter: for every size $n \ge 1$,
tolerance $0 < \varepsilon \le 2^{-15}$, failure probability $\theta > 0$ and bound
$R_0 > 0$ there are a binary format `fmt`, a nearest selector $r$ (ties away from zero), the
depth $\ell =$ `NLAlib.bisectionDepth` $\varepsilon$ and the accuracy $\beta = \hat\beta$ at its
bound such that the machine `NLAlib.binaryFloatMachine` of `fmt` and $r$ meets the contract
`NLAlib.FloatMachine.IsAccurate` at the format's constants ($u = 2^{-p}$, floor
$\tau = 2^{e_{\min} + p - 1}$, range the largest finite number, $\mu_{\mathrm{MM}}(d) =
\mu_{\mathrm{QR}}(d) = 2d$, $c_{\mathrm N} = \sqrt2$) with samplers of measurable fibres and
countable ranges, and, with $m = \min(n, \ell + 1)$,
$\hat T = 2\sqrt2\sqrt n + \sqrt{\log(96nm/\theta)}$,
$\hat\beta = (\ell - 1)^2\varepsilon\sqrt\theta/(52\ell^2(2\ell - 1)\sqrt{nm\min(n, e)}\,\hat T)$
and $N_* = N(\theta/(12n\ell(\ell + 1)), \beta/(16n))$ (`NLAlib.newtonSchulzSteps`), the
accuracy window $\hat\beta/(1 + 2^{-6}) \le \beta \le \hat\beta$, the two precision conditions with
$p$ bits, the floor condition $100n^{3/2}\tau \le \min(\sqrt{\theta/(8nm)},
\varepsilon\min(R_0, 1))$, the range condition $16(2R_0 + n + 2\ell + \hat T) \le \Omega$, the
exponent condition with $E \ge 2$ bits, and independent node samples, each of law
`NLAlib.eighSampleLaw` $n$, on a probability space. These are the hypotheses of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw`
(any $R_0 > 0$) and of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw`
(there with $1/2 \le R_0 \le 1$) apart from $\theta \le 1$, which both theorems also assume; so
for $0 < \theta \le 1$ neither becomes vacuous as the parameters change. The construction itself
needs only $\theta > 0$. Each
condition on the format is an upper bound on $u$ or $\tau$ or a lower bound on $p$, $E$ or
$\Omega$, and in a binary format $\tau$ and $\Omega$ depend on $E$ alone (up to a factor $2$ in
$\Omega$), so the format takes $p = \lceil\max(\cdot)\rceil + 2$ and $E$ large enough for the
exponent, floor and range conditions together. The input and $\beta$ are real parameters (the
stored type is ℝ). At $n = 0$ the bound $\hat\beta$ is $0$ and no $\beta > 0$ exists. No printed
source. -/
theorem exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw_of_le {n : ℕ} (hn : 1 ≤ n)
    {ε θ R₀ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hR₀ : 0 < R₀) :
    ∃ (fmt : Float.Model.Format) (r : ℝ → ℤ) (ℓ : ℕ) (β : ℝ),
      (∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) ∧
      (binaryFloatMachine fmt r).IsAccurate id ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
        ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite (fun d => 2 * d)
        (fun d => 2 * d) √2 ∧
      (∀ c z, MeasurableSet ((binaryFloatMachine fmt r).unif c ⁻¹' {z})) ∧
      (∀ c, (Set.range ((binaryFloatMachine fmt r).unif c)).Countable) ∧
      (∀ z, MeasurableSet ((binaryFloatMachine fmt r).normal ⁻¹' {z})) ∧
      (Set.range (binaryFloatMachine fmt r).normal).Countable ∧
      Monotone (fun d : ℕ => 2 * (d : ℝ)) ∧ 0 < (2 : ℝ)⁻¹ ^ fmt.mantissaBits ∧
      Real.logb 2 ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)⁻¹ = fmt.mantissaBits ∧
      2 ≤ fmt.exponentBits ∧ bisectionDepth ε ≤ ℓ ∧ 0 < β ∧
      β ≤ ((ℓ : ℝ) - 1) ^ 2 * ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))) ∧
      ((ℓ : ℝ) - 1) ^ 2 * ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))) /
        (1 + 2⁻¹ ^ 6) ≤ β ∧
      Real.logb 2 ε⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
        Real.logb 2 (n * (4 * (2 * n) + 10 + 10 * √(n : ℝ))) +
        1 / 2 * Real.logb 2 (n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) +
        Real.logb 2 (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) +
        Real.logb 2 (ℓ * (ℓ + 1)) + Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) +
        13 ≤ fmt.mantissaBits ∧
      Real.logb 2 β⁻¹ + Real.logb 2 (2048 * (n + newtonSchulzSteps
        (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n)) + 1) *
        (4 * (2 * n) + 10 + 10 * √(n : ℝ)) +
        16 * (4 * (2 * n) + 4 * √(n : ℝ) * (√2 + 1) + 2 * (2 * n) + 1)) ≤ fmt.mantissaBits ∧
      (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) * (100 * n * √(n : ℝ)) ≤
        min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (ε * min R₀ 1) ∧
      16 * (2 * R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
        √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ fmt.maxFinite ∧
      Real.logb 2 (Real.logb 2 (1536 * (n + ℓ + 2) ^ 3 / (ε * θ)) + 2) + 1 ≤ fmt.exponentBits ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ : Measure Ω')
        (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
        IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ := by
  set ℓ := bisectionDepth ε with hℓdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ5 : (5 : ℝ) ≤ ℓ := by
    have : 5 ≤ ℓ := Nat.le_add_left 5 _
    exact_mod_cast this
  have hm0 : 0 < min (n : ℝ) (ℓ + 1) := lt_min hn0 (by linarith)
  have hD : 0 < √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) :=
    Real.sqrt_pos.mpr (mul_pos (mul_pos hn0 hm0) (lt_min hn0 (Real.exp_pos 1)))
  have hT : 0 < 2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)) := by
    have : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
    positivity
  set β := ((ℓ : ℝ) - 1) ^ 2 * ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
    √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
    (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))) with hβdef
  have hβ : 0 < β := by
    have : 0 < (ℓ : ℝ) - 1 := by linarith
    have : 0 < 2 * (ℓ : ℝ) - 1 := by linarith
    have : 0 < √θ := Real.sqrt_pos.mpr hθ
    positivity
  have hmin : 0 < min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (ε * min R₀ 1) :=
    lt_min (Real.sqrt_pos.mpr (by positivity)) (mul_pos hε (lt_min hR₀ one_pos))
  obtain ⟨fmt, hb1, hb2, hbx, hE2, hτ1, hτQ, hΩQ⟩ := exists_format_le
    (Real.logb 2 ε⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n * (4 * (2 * n) + 10 + 10 * √(n : ℝ))) +
      1 / 2 * Real.logb 2 (n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) +
      Real.logb 2 (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) +
      Real.logb 2 (ℓ * (ℓ + 1)) + Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) +
      13)
    (Real.logb 2 β⁻¹ + Real.logb 2 (2048 * (n + newtonSchulzSteps
      (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n)) + 1) *
      (4 * (2 * n) + 10 + 10 * √(n : ℝ)) +
      16 * (4 * (2 * n) + 4 * √(n : ℝ) * (√2 + 1) + 2 * (2 * n) + 1)))
    (Real.logb 2 (Real.logb 2 (1536 * (n + ℓ + 2) ^ 3 / (ε * θ)) + 2) + 1)
    (max (100 * n * √(n : ℝ) / min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (ε * min R₀ 1))
      (16 * (2 * R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
        √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))))
  have hτ0 : (0 : ℝ) ≤ 2 ^ (fmt.minExponent + fmt.mantissaBits - 1) := by positivity
  refine ⟨fmt, roundTiesAway, ℓ, β, absRelErr_roundTiesAway,
    isAccurate_binaryFloatMachine absRelErr_roundTiesAway roundTiesAway_neg hτ1,
    measurableSet_preimage_unif_binaryFloatMachine fmt measurable_roundTiesAway,
    countable_range_unif_binaryFloatMachine fmt _,
    measurableSet_preimage_normal_binaryFloatMachine fmt measurable_roundTiesAway,
    countable_range_normal_binaryFloatMachine fmt _,
    fun a b h => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (by norm_num), by positivity,
    logb_inv_two_inv_pow _, hE2, le_rfl, hβ, le_rfl, div_le_self hβ.le (by norm_num), hb1, hb2,
    ?_, (le_max_right _ _).trans hΩQ, hbx, exists_iIndepFun_hasLaw_eighSampleLaw n⟩
  set q := min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (ε * min R₀ 1)
  set τ := (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)
  have h1 : 100 * n * √(n : ℝ) / q * q = 100 * n * √(n : ℝ) := div_mul_cancel₀ _ hmin.ne'
  have h2 := mul_le_mul_of_nonneg_left (le_max_left (100 * n * √(n : ℝ) / q)
    (16 * (2 * R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) hτ0
  calc τ * (100 * n * √(n : ℝ)) = τ * (100 * n * √(n : ℝ) / q) * q := by
        rw [mul_assoc τ (100 * n * √(n : ℝ) / q) q, h1]
    _ ≤ 1 * q := mul_le_mul_of_nonneg_right (h2.trans hτQ) hmin.le
    _ = q := one_mul q

/-- Theorem 4.2 in bits applies at every parameter: for $n \ge 1$, $0 < \varepsilon \le
2^{-15}$, $0 < \theta \le 1$ and every Hermitian input with $\|\mathbf{A}\|_2 \le R_0$, the
failure probability of `NLAlib.eigh` on the wide enough binary format is at most $\theta$. -/
example {n : ℕ} (hn : 1 ≤ n) {ε θ R₀ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) (hR₀pos : 0 < R₀) {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)}
    (hA : (decodeMatrix id A).IsHermitian) (hR₀ : specNorm (decodeMatrix id A) ≤ R₀) :
    ∃ (fmt : Float.Model.Format) (r : ℝ → ℤ) (ℓ signFuel : ℕ) (β : ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω') (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
      IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ (∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) ∧
      μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix id A)
        (decodeMatrix id (eigh (binaryFloatMachine fmt r) signFuel ℓ A R₀ ε β
          fun a => ζ a ω).1)
        (fun i => (eigh (binaryFloatMachine fmt r) signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)
        (2 * ε * R₀) (ε / 3)} ≤ θ := by
  obtain ⟨fmt, r, ℓ, β, -, hM, hunifm, hunifc, hnormalm, hnormalc, hmono, hu, hlogu, -, hℓ, hβ,
    hβle, hβge, hbits, hbits', hτ, hΩ, -, Ω', mΩ', μ, ζ, hμ, hind, hlaw⟩ :=
    exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw_of_le hn hε hε₁ hθ hR₀pos
  refine ⟨fmt, r, ℓ, ⌈newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n))⌉₊, β, Ω',
    mΩ', μ, ζ, hμ, hind, hlaw, ?_⟩
  rw [← hlogu] at hbits hbits'
  exact hM.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw
    hunifm hunifc hnormalm hnormalc hmono hmono (by norm_num) (by norm_num) (Real.sqrt_nonneg 2)
    hn hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hβge rfl hu hbits hbits' (Nat.le_ceil _)
    (by positivity) hτ hΩ hind hlaw

/-- Theorem 4.2 in a bounded format applies at every parameter: for $n \ge 1$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $1/2 \le R_0 \le 1$ and every Hermitian input
with $\|\mathbf{A}\|_2 \le R_0$, the failure probability of `NLAlib.eigh` on the wide enough
binary format is at most $\theta$. -/
example {n : ℕ} (hn : 1 ≤ n) {ε θ R₀ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) (hR₀half : 1 / 2 ≤ R₀) (hR₀one : R₀ ≤ 1) {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)}
    (hA : (decodeMatrix id A).IsHermitian) (hR₀ : specNorm (decodeMatrix id A) ≤ R₀) :
    ∃ (fmt : Float.Model.Format) (r : ℝ → ℤ) (ℓ signFuel : ℕ) (β : ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω') (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
      IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ (∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) ∧
      μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix id A)
        (decodeMatrix id (eigh (binaryFloatMachine fmt r) signFuel ℓ A R₀ ε β
          fun a => ζ a ω).1)
        (fun i => (eigh (binaryFloatMachine fmt r) signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)
        (2 * ε * R₀) (ε / 3)} ≤ θ := by
  obtain ⟨fmt, r, ℓ, β, -, hM, hunifm, hunifc, hnormalm, hnormalc, hmono, -, -, hE2, hℓ, hβ,
    hβle, hβge, hbits, hbits', -, -, hexp, Ω', mΩ', μ, ζ, hμ, hind, hlaw⟩ :=
    exists_isAccurate_binaryFloatMachine_and_hasLaw_eighSampleLaw_of_le hn hε hε₁ hθ
      (R₀ := R₀) (by linarith)
  refine ⟨fmt, r, ℓ, ⌈newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n))⌉₊, β, Ω',
    mΩ', μ, ζ, hμ, hind, hlaw, ?_⟩
  exact
    hM.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw
    fmt hE2 hunifm hunifc hnormalm hnormalc hmono hmono (by norm_num) (by norm_num)
    (Real.sqrt_nonneg 2) hn hA hR₀ hR₀half hR₀one hε hε₁ hθ hθ₁ hℓ hβ hβle hβge rfl hbits hbits'
    hexp (Nat.le_ceil _) hind hlaw

-- The name of the theorem applied exceeds 100 characters.
set_option linter.style.longLine false in
/-- Theorem 4.2 at fixed parameters applies at every parameter: for $n \ge 1$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $R_0 > 0$ and every Hermitian input with
$\|\mathbf{A}\|_2 \le R_0$, a binary format with $p \ge$ the bit count and $E$ large enough for
$300n^3\tau \le \varepsilon\theta\min(R_0, 1)$ and $64(R_0 + n + \Lambda) \le \Omega$, the depth
`NLAlib.bisectionDepth` $\varepsilon$, $\lceil 4\Lambda\rceil$ sign steps and $\beta$ at the upper
end of its window give failure probability of `NLAlib.eigh` at most $\theta$. -/
example {n : ℕ} (hn : 1 ≤ n) {ε θ R₀ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) (hR₀pos : 0 < R₀) {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)}
    (hA : (decodeMatrix id A).IsHermitian) (hR₀ : specNorm (decodeMatrix id A) ≤ R₀) :
    ∃ (fmt : Float.Model.Format) (r : ℝ → ℤ) (signFuel : ℕ) (β : ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω') (ζ : List Bool → Ω' → EighSample ℝ ℂ n),
      IsProbabilityMeasure μ ∧ iIndepFun ζ μ ∧ (∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) ∧
      μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix id A)
        (decodeMatrix id (eigh (binaryFloatMachine fmt r) signFuel (bisectionDepth ε) A R₀ ε β
          fun a => ζ a ω).1)
        (fun i => (eigh (binaryFloatMachine fmt r) signFuel (bisectionDepth ε) A R₀ ε β
          fun a => ζ a ω).2 i)
        (2 * ε * R₀) (ε / 3)} ≤ θ := by
  set Λ := Real.logb 2 ε⁻¹ + Real.logb 2 θ⁻¹ + Real.logb 2 n with hΛ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hε1 : ε ≤ 1 := hε₁.trans (by norm_num)
  have hΛ0 : 0 < Λ := by
    have h1 : 0 ≤ Real.logb 2 θ⁻¹ := Real.logb_nonneg one_lt_two (one_le_inv₀ hθ |>.mpr hθ₁)
    have h2 : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
    have h3 : 15 ≤ Real.logb 2 ε⁻¹ := by
      rw [Real.le_logb_iff_rpow_le one_lt_two (inv_pos.mpr hε)]
      have : (2 : ℝ) ^ (15 : ℝ) = (2⁻¹ ^ 15)⁻¹ := by norm_num
      rw [this]; exact inv_anti₀ hε hε₁
    linarith
  have hnΛ : 0 < (n : ℝ) * Λ := mul_pos hn0 hΛ0
  have hq : 0 < ε * θ * min R₀ 1 := mul_pos (mul_pos hε hθ) (lt_min hR₀pos one_pos)
  obtain ⟨fmt, hb, -, -, -, hτ1, hτQ, hΩQ⟩ := exists_format_le
    (Real.logb 2 ε⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ + 7 / 2 * Real.logb 2 n + 4 * Real.logb 2 Λ + 24)
    0 0 (max (300 * n ^ 3 / (ε * θ * min R₀ 1)) (64 * (R₀ + n + Λ)))
  obtain ⟨Ω', mΩ', μ, ζ, hμ, hind, hlaw⟩ := exists_iIndepFun_hasLaw_eighSampleLaw n
  refine ⟨fmt, roundTiesAway, ⌈4 * Λ⌉₊, ε * √θ / (1024 * (n * Λ) * √(n * Λ)), Ω', mΩ', μ, ζ,
    hμ, hind, hlaw, ?_⟩
  set τ := (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)
  have hτ0 : 0 ≤ τ := by positivity
  have hτ : 300 * n ^ 3 * τ ≤ ε * θ * min R₀ 1 := by
    have h := mul_le_mul_of_nonneg_left (le_max_left (300 * n ^ 3 / (ε * θ * min R₀ 1))
      (64 * (R₀ + n + Λ))) hτ0
    have h1 : τ * (300 * n ^ 3 / (ε * θ * min R₀ 1)) ≤ 1 := h.trans hτQ
    rw [mul_div_assoc', div_le_one hq] at h1
    linarith
  have hM := isAccurate_binaryFloatMachine (fmt := fmt) absRelErr_roundTiesAway roundTiesAway_neg
    hτ1
  exact
    hM.measureReal_not_isApproxDiagonalization_eigh_bisectionDepth_le_of_logb_le_of_hasLaw_eighSampleLaw
    (measurableSet_preimage_unif_binaryFloatMachine fmt measurable_roundTiesAway)
    (countable_range_unif_binaryFloatMachine fmt _)
    (measurableSet_preimage_normal_binaryFloatMachine fmt measurable_roundTiesAway)
    (countable_range_normal_binaryFloatMachine fmt _) hn hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hΛ
    (div_le_div_of_nonneg_left (by positivity)
      (mul_pos (mul_pos (by norm_num) hnΛ) (Real.sqrt_pos.2 hnΛ))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hnΛ.le)
        (Real.sqrt_nonneg _))) le_rfl
    (by rw [logb_inv_two_inv_pow]; exact hb) (Nat.le_ceil _) hτ0 hτ
    ((le_max_right _ _).trans hΩQ) hind hlaw

end NLAlib
