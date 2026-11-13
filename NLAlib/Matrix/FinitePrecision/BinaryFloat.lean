/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Float
public import NLAlib.Ops.ArithmeticError
public import NLAlib.ForMathlib.Algebra.Order.Round
public import NLAlib.ForMathlib.Data.Float.Basic

/-!
# Bounded binary floating-point quantization

The binary layout is Lean core's `Float.Model.Format`. The significand exponent is clamped
below at the format's smallest exponent; spacing scales with magnitude in the normal range
and is constant only for subnormals. The upper range is the largest finite representable value.

The nearest-integer selector is a parameter. Its certificate is a half-unit absolute-error
bound, which permits every nearest tie policy, including ties to even. Mathlib's `round`
is one possible selector, with ties upward; it is not identified with IEEE's ties-to-even rule.
This is a noncomputable mathematical quantizer, not a native implementation.
[Higham2002, §2.2].

## Main results

* `NLAlib.Computation.absRelErr_binaryFloatRound`: relative error plus gradual underflow.
* `NLAlib.Computation.isBinaryRep_binaryFloatRound`: finite-range representability.
* `NLAlib.Computation.binaryFloatRound_eq_self`: exactness on represented values.
* `NLAlib.Computation.relErr_binaryFloatRound_of_minExponent_le`: normal relative error.
* `NLAlib.Computation.binaryFloatRound_two_zpow_sub_two`: strict subnormal underflow.
* `NLAlib.Computation.IsBinaryRep.abs_le`: the largest finite magnitude.
* `NLAlib.Computation.abs_sub_binaryFloatRound_le`: relative error above the smallest normal
  number, as a floor.
* `NLAlib.Computation.abs_binaryFloatRound_le_of_abs_le`: rounding stays below a larger
  represented value.
-/

@[expose] public section

namespace NLAlib.Computation

open Float.Model

/-- A represented value has magnitude at most the format's largest finite magnitude. -/
theorem IsBinaryRep.abs_le {fmt : Float.Model.Format} {x : ℝ} (hx : IsBinaryRep fmt x) :
    |x| ≤ fmt.maxFinite := by
  simp only [Format.maxFinite, Format.maxExponentBound, Nat.cast_pow, Nat.cast_ofNat]
  obtain ⟨m, e, hm, hmin, hmax, rfl⟩ := hx
  have hm' : |(m : ℝ)| ≤ (2 : ℝ) ^ fmt.mantissaBits - 1 := by
    have hi : |m| ≤ (2 : ℤ) ^ fmt.mantissaBits - 1 := by omega
    exact_mod_cast hi
  rw [abs_mul, abs_of_pos (zpow_pos (show (0 : ℝ) < 2 from two_pos) e)]
  exact (mul_le_mul_of_nonneg_right hm' (le_of_lt (zpow_pos two_pos e))).trans
    (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ one_le_two hmax)
      (le_trans (abs_nonneg _) hm'))

/-- Negation preserves finite binary representability and its exponent range. -/
theorem IsBinaryRep.neg {fmt : Float.Model.Format} {x : ℝ} (hx : IsBinaryRep fmt x) :
    IsBinaryRep fmt (-x) := by
  obtain ⟨m, e, hm, hmin, hmax, rfl⟩ := hx
  exact ⟨-m, e, by simpa only [abs_neg] using hm, hmin, hmax, by push_cast; ring⟩

/-- Binary rounding with gradual underflow. The format's target exponent is the larger of
the normal significand exponent and the smallest subnormal exponent. The selector rounds the
scaled input to an integer; nearest tie behavior is supplied by its error certificate. -/
noncomputable def binaryFloatRound (fmt : Float.Model.Format) (r : ℝ → ℤ) (x : ℝ) : ℝ :=
  let e := fmt.targetExponent (Int.log 2 |x| + 1)
  (r (x / (2 : ℝ) ^ e) : ℝ) * (2 : ℝ) ^ e

private theorem selector_intCast {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (m : ℤ) : r (m : ℝ) = m := by
  have h : |(m : ℝ) - (r (m : ℝ) : ℝ)| ≤ 1 / 2 := by
    simpa only [AbsRelErr, zero_mul, zero_add] using hr (m : ℝ)
  have hi : |m - r (m : ℝ)| < 1 := by
    exact_mod_cast (h.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  have hb := abs_lt.mp hi
  omega

/-- Binary rounding returns zero exactly for an exact zero input, for every nearest tie policy. -/
theorem binaryFloatRound_zero (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) : binaryFloatRound fmt r 0 = 0 := by
  have hz := selector_intCast hr 0
  simpa only [binaryFloatRound, zero_div, Int.cast_zero, zero_mul] using
    congrArg (fun m : ℤ => (m : ℝ) * (2 : ℝ) ^
      (fmt.targetExponent (Int.log 2 |(0 : ℝ)| + 1))) hz

private theorem local_error (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (x : ℝ) :
    |x - binaryFloatRound fmt r x| ≤
      (1 / 2 : ℝ) * 2 ^ fmt.targetExponent (Int.log 2 |x| + 1) := by
  set e := fmt.targetExponent (Int.log 2 |x| + 1)
  have he : (0 : ℝ) < 2 ^ e := zpow_pos two_pos _
  have hq : |x / (2 : ℝ) ^ e - (r (x / (2 : ℝ) ^ e) : ℝ)| ≤ 1 / 2 := by
    simpa only [AbsRelErr, zero_mul, zero_add] using hr (x / (2 : ℝ) ^ e)
  have heq : x - binaryFloatRound fmt r x =
      (x / (2 : ℝ) ^ e - (r (x / (2 : ℝ) ^ e) : ℝ)) * 2 ^ e := by
    dsimp only [binaryFloatRound, e]
    field_simp
  rw [heq, abs_mul, abs_of_pos he]
  exact mul_le_mul_of_nonneg_right hq he.le

/-- Rounding with precision $p$ and smallest subnormal spacing $2^{e_{\min}}$ has error at most
$2^{-p}\lvert x\rvert+2^{e_{\min}}/2$. The selector may choose either neighbor at a tie.
[Higham2002, §2.2], in mixed absolute-relative form for gradual underflow. -/
theorem absRelErr_binaryFloatRound (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (x : ℝ) :
    AbsRelErr ((2 : ℝ)⁻¹ ^ fmt.mantissaBits) ((2 : ℝ) ^ fmt.minExponent / 2)
      x (binaryFloatRound fmt r x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [binaryFloatRound_zero fmt hr]
    simp only [AbsRelErr, sub_self, abs_zero, mul_zero, zero_add]
    positivity
  set k := Int.log 2 |x|
  set e := fmt.targetExponent (k + 1)
  have herr : |x - binaryFloatRound fmt r x| ≤ (1 / 2 : ℝ) * 2 ^ e := local_error fmt hr x
  have hk : (2 : ℝ) ^ k ≤ |x| := by
    exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr hx)
  by_cases hnormal : fmt.minExponent ≤ k + 1 - fmt.mantissaBits
  · have heq : e = k + 1 - fmt.mantissaBits := max_eq_left hnormal
    have hhalf : (1 / 2 : ℝ) * 2 ^ e = (2 : ℝ)⁻¹ ^ fmt.mantissaBits * 2 ^ k := by
      rw [heq, zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, inv_pow]
      field_simp
    apply herr.trans
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hk (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  · have heq : e = fmt.minExponent := max_eq_right (le_of_not_ge hnormal)
    apply herr.trans
    rw [heq]
    have hu : 0 ≤ (2 : ℝ)⁻¹ ^ fmt.mantissaBits * |x| := by positivity
    linarith

/-- In the normal range the binary quantizer has pure relative error at most $2^{-p}$.
The hypothesis says that the normal significand exponent is no smaller than the format's
smallest exponent; no absolute underflow term is needed. [Higham2002, Theorem 2.2]. -/
theorem relErr_binaryFloatRound_of_minExponent_le (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (x : ℝ)
    (hnormal : fmt.minExponent ≤ Int.log 2 |x| + 1 - fmt.mantissaBits) :
    RelErr ((2 : ℝ)⁻¹ ^ fmt.mantissaBits) x (binaryFloatRound fmt r x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [binaryFloatRound_zero fmt hr]
    exact ⟨0, by simp only [abs_zero]; positivity, by simp only [zero_mul]⟩
  apply AbsRelErr.relErr _ (by positivity)
  change |x - binaryFloatRound fmt r x| ≤ (2 : ℝ)⁻¹ ^ fmt.mantissaBits * |x| + 0
  rw [add_zero]
  have hk : (2 : ℝ) ^ Int.log 2 |x| ≤ |x| := by
    exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr hx)
  have herr := local_error fmt hr x
  have heq : fmt.targetExponent (Int.log 2 |x| + 1) =
      Int.log 2 |x| + 1 - fmt.mantissaBits := max_eq_left hnormal
  have hhalf : (1 / 2 : ℝ) * 2 ^ fmt.targetExponent (Int.log 2 |x| + 1) =
      (2 : ℝ)⁻¹ ^ fmt.mantissaBits * 2 ^ Int.log 2 |x| := by
    rw [heq, zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, inv_pow]
    field_simp
  rw [hhalf] at herr
  exact herr.trans (mul_le_mul_of_nonneg_left hk (by positivity))

/-- A positive value one quarter of the smallest subnormal spacing rounds to zero for every
nearest tie policy. This is strict underflow, not a tie, and shows why a relative-only error
model cannot describe the complete finite exponent range. -/
theorem binaryFloatRound_two_zpow_sub_two (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) :
    binaryFloatRound fmt r ((2 : ℝ) ^ (fmt.minExponent - 2)) = 0 := by
  have he : fmt.targetExponent (fmt.minExponent - 2 + 1) = fmt.minExponent := by
    apply max_eq_right
    omega
  have hq : (2 : ℝ) ^ (fmt.minExponent - 2) / (2 : ℝ) ^ fmt.minExponent = 1 / 4 := by
    rw [← zpow_sub₀ two_ne_zero, show fmt.minExponent - 2 - fmt.minExponent = -2 by ring]
    norm_num
  have hrq : r (1 / 4 : ℝ) = 0 := by
    have h : |(1 / 4 : ℝ) - (r (1 / 4 : ℝ) : ℝ)| ≤ 1 / 2 := by
      simpa only [AbsRelErr, zero_mul, zero_add] using hr (1 / 4 : ℝ)
    have hb := abs_le.mp h
    have hlo : (-1 : ℤ) < r (1 / 4 : ℝ) := by
      exact_mod_cast (show (-1 : ℝ) < (r (1 / 4 : ℝ) : ℝ) from by linarith)
    have hhi : r (1 / 4 : ℝ) < (1 : ℤ) := by
      exact_mod_cast (show (r (1 / 4 : ℝ) : ℝ) < 1 from by linarith)
    omega
  have hlog : Int.log 2 ((2 : ℝ) ^ (fmt.minExponent - 2)) = fmt.minExponent - 2 := by
    simpa only [Nat.cast_ofNat] using
      (Int.log_zpow (R := ℝ) (b := 2) one_lt_two (fmt.minExponent - 2))
  rw [binaryFloatRound, abs_of_pos (zpow_pos (show (0 : ℝ) < 2 from two_pos) _),
    hlog, he, hq, hrq, Int.cast_zero, zero_mul]

private theorem scaled_abs_lt (fmt : Float.Model.Format) (x : ℝ) :
    |x / (2 : ℝ) ^ fmt.targetExponent (Int.log 2 |x| + 1)| <
      (2 : ℝ) ^ fmt.mantissaBits := by
  have he : Int.log 2 |x| + 1 ≤
      fmt.targetExponent (Int.log 2 |x| + 1) + fmt.mantissaBits := by
    dsimp only [Format.targetExponent]
    have := le_max_left (Int.log 2 |x| + 1 - fmt.mantissaBits) fmt.minExponent
    omega
  rw [abs_div, abs_of_pos (zpow_pos (show (0 : ℝ) < 2 from two_pos) _),
    div_lt_iff₀ (zpow_pos two_pos _),
    ← zpow_natCast, ← zpow_add₀ two_ne_zero]
  have hx : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
    exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) one_lt_two |x|
  exact hx.trans_le (zpow_le_zpow_right₀ one_le_two (by omega))

private theorem exponent_le_of_abs_le (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) {x : ℝ} (hx : x ≠ 0)
    (h : |x| ≤ fmt.maxFinite) :
    fmt.targetExponent (Int.log 2 |x| + 1) ≤
      (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
        fmt.mantissaBitsWithoutImplicit := by
  set emax : ℤ := (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
    fmt.mantissaBitsWithoutImplicit
  have hmin : fmt.minExponent ≤ emax := by
    obtain ⟨m, e, hm, hlo, hhi, hz⟩ := isBinaryRep_zero fmt he
    exact hlo.trans hhi
  have hk : (2 : ℝ) ^ Int.log 2 |x| ≤ |x| := by
    exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr hx)
  have hlt : |x| < (2 : ℝ) ^ (emax + fmt.mantissaBits) := by
    calc
      |x| ≤ ((2 : ℝ) ^ fmt.mantissaBits - 1) * 2 ^ emax := by
        simpa only [Format.maxFinite, Format.maxExponentBound, Nat.cast_pow, Nat.cast_ofNat]
          using h
      _ < (2 : ℝ) ^ fmt.mantissaBits * 2 ^ emax := by
        exact mul_lt_mul_of_pos_right (sub_lt_self _ zero_lt_one) (zpow_pos two_pos _)
      _ = (2 : ℝ) ^ (emax + fmt.mantissaBits) := by
        rw [zpow_add₀ two_ne_zero, zpow_natCast]
        ring
  have hlog := (zpow_lt_zpow_iff_right₀ one_lt_two).mp (hk.trans_lt hlt)
  exact max_le (by omega) hmin

private theorem repr_of_mantissa_le (fmt : Float.Model.Format) (m e : ℤ)
    (hm : |m| ≤ (2 : ℤ) ^ fmt.mantissaBits) (hmin : fmt.minExponent ≤ e)
    (hmax : e ≤ (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
      fmt.mantissaBitsWithoutImplicit)
    (hcarry : |m| = (2 : ℤ) ^ fmt.mantissaBits →
      e < (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
        fmt.mantissaBitsWithoutImplicit) :
    IsBinaryRep fmt ((m : ℝ) * (2 : ℝ) ^ e) := by
  rcases hm.lt_or_eq with hlt | heq
  · exact ⟨m, e, hlt, hmin, hmax, rfl⟩
  have hmax' := hcarry heq
  have hp : fmt.mantissaBits = fmt.mantissaBitsWithoutImplicit + 1 := by
    simp only [Format.mantissaBits, Nat.add_comm]
  have hhalf : |(2 : ℤ) ^ fmt.mantissaBitsWithoutImplicit| <
      (2 : ℤ) ^ fmt.mantissaBits := by
    rw [abs_of_pos (pow_pos two_pos _), hp, pow_succ]
    nlinarith [pow_pos (show (0 : ℤ) < 2 from two_pos) fmt.mantissaBitsWithoutImplicit]
  have hmcase : m = (2 : ℤ) ^ fmt.mantissaBits ∨ m = -(2 : ℤ) ^ fmt.mantissaBits := by
    rcases le_or_gt 0 m with hm0 | hm0
    · left; simpa only [abs_of_nonneg hm0] using heq
    · right; have := heq; rw [abs_of_neg hm0] at this; omega
  rcases hmcase with rfl | rfl
  · refine ⟨(2 : ℤ) ^ fmt.mantissaBitsWithoutImplicit, e + 1, hhalf, by omega,
      by omega, ?_⟩
    rw [hp, pow_succ, zpow_add₀ two_ne_zero, zpow_one]
    push_cast
    ring
  · refine ⟨-(2 : ℤ) ^ fmt.mantissaBitsWithoutImplicit, e + 1,
      by simpa only [abs_neg] using hhalf, by omega, by omega, ?_⟩
    rw [hp, pow_succ, zpow_add₀ two_ne_zero, zpow_one]
    push_cast
    ring

/-- Rounding an input of magnitude at most the largest finite value produces a represented
value with bounded significand and exponent. The exponent layout has at least two bits; this
excludes older core's degenerate one-bit layouts. Mantissa carry is handled explicitly. -/
theorem isBinaryRep_binaryFloatRound (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) {x : ℝ}
    (hx : |x| ≤ fmt.maxFinite) : IsBinaryRep fmt (binaryFloatRound fmt r x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [binaryFloatRound_zero fmt hr]
    exact isBinaryRep_zero fmt he
  set e := fmt.targetExponent (Int.log 2 |x| + 1)
  set q := x / (2 : ℝ) ^ e
  set m := r q
  have hq : |q| < (2 : ℝ) ^ fmt.mantissaBits := scaled_abs_lt fmt x
  have hmr : |(m : ℝ)| ≤ |q| + 1 / 2 := by
    simpa only [add_zero, zero_mul, one_mul] using (hr q).abs_le
  have hm : |m| ≤ (2 : ℤ) ^ fmt.mantissaBits := by
    have hlt : |m| < (2 : ℤ) ^ fmt.mantissaBits + 1 := by
      exact_mod_cast (show |(m : ℝ)| < (2 : ℝ) ^ fmt.mantissaBits + 1 from by linarith)
    omega
  have hemin : fmt.minExponent ≤ e := le_max_right _ _
  have hemax := exponent_le_of_abs_le fmt he hx0 hx
  apply repr_of_mantissa_le fmt m e hm hemin hemax
  intro hcarry
  by_contra hnot
  have heq : e = (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
      fmt.mantissaBitsWithoutImplicit := le_antisymm hemax (le_of_not_gt hnot)
  have hq' : |q| ≤ (2 : ℝ) ^ fmt.mantissaBits - 1 := by
    dsimp only [q]
    rw [abs_div, abs_of_pos (zpow_pos (show (0 : ℝ) < 2 from two_pos) _),
      div_le_iff₀ (zpow_pos two_pos _)]
    simpa only [heq, Float.Model.Format.maxFinite, Float.Model.Format.maxExponentBound,
      Nat.cast_pow, Nat.cast_ofNat] using hx
  have hm' : |(m : ℝ)| = (2 : ℝ) ^ fmt.mantissaBits := by exact_mod_cast hcarry
  linarith

/-- Every represented finite value is fixed by binary rounding, for every nearest tie policy. -/
theorem binaryFloatRound_eq_self (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) {x : ℝ} (hx : IsBinaryRep fmt x) :
    binaryFloatRound fmt r x = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact binaryFloatRound_zero fmt hr
  obtain ⟨m, e', hm, hemin, hemax, rfl⟩ := hx
  set k := Int.log 2 |(m : ℝ) * (2 : ℝ) ^ e'|
  set e := fmt.targetExponent (k + 1)
  have hk : (2 : ℝ) ^ k ≤ |(m : ℝ) * (2 : ℝ) ^ e'| := by
    exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr hx0)
  have hm' : |(m : ℝ)| < (2 : ℝ) ^ fmt.mantissaBits := by exact_mod_cast hm
  have hlt : |(m : ℝ) * (2 : ℝ) ^ e'| < (2 : ℝ) ^ (e' + fmt.mantissaBits) := by
    rw [abs_mul, abs_of_pos (zpow_pos (show (0 : ℝ) < 2 from two_pos) _),
      zpow_add₀ two_ne_zero, zpow_natCast]
    exact (mul_lt_mul_of_pos_right hm' (zpow_pos two_pos _)).trans_eq (mul_comm _ _)
  have hnormal : k + 1 - fmt.mantissaBits ≤ e' := by
    have := (zpow_lt_zpow_iff_right₀ one_lt_two).mp (hk.trans_lt hlt)
    omega
  have hee : e ≤ e' := max_le hnormal hemin
  obtain ⟨n, hn⟩ : ∃ n : ℕ, e' = e + n := ⟨(e' - e).toNat, by omega⟩
  have hq : (m : ℝ) * (2 : ℝ) ^ e' / (2 : ℝ) ^ e = ((m * 2 ^ n : ℤ) : ℝ) := by
    rw [hn, zpow_add₀ two_ne_zero, zpow_natCast]
    push_cast
    field_simp
  change (r ((m : ℝ) * (2 : ℝ) ^ e' / (2 : ℝ) ^ e) : ℝ) * (2 : ℝ) ^ e = _
  rw [hq, selector_intCast hr, ← hq]
  field_simp

/-- Rounding with precision $p$ and smallest exponent $e_{\min}$ errs by at most
$2^{-p}\max(\lvert x\rvert, 2^{e_{\min} + p - 1})$: relative error $2^{-p}$ above the smallest
normal number $2^{e_{\min} + p - 1}$ and absolute error half the subnormal spacing below it. The
selector may choose either neighbor at a tie. [Higham2002, §2.2], with gradual underflow as a
floor. -/
theorem abs_sub_binaryFloatRound_le (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (x : ℝ) :
    |x - binaryFloatRound fmt r x| ≤
      (2 : ℝ)⁻¹ ^ fmt.mantissaBits *
        max |x| ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [binaryFloatRound_zero fmt hr, sub_self, abs_zero]
    positivity
  set k := Int.log 2 |x|
  set e := fmt.targetExponent (k + 1)
  have herr : |x - binaryFloatRound fmt r x| ≤ (1 / 2 : ℝ) * 2 ^ e := local_error fmt hr x
  have hu : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ fmt.mantissaBits := by positivity
  by_cases hnormal : fmt.minExponent ≤ k + 1 - fmt.mantissaBits
  · have hk : (2 : ℝ) ^ k ≤ |x| := by
      exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr hx)
    have hhalf : (1 / 2 : ℝ) * 2 ^ e = (2 : ℝ)⁻¹ ^ fmt.mantissaBits * 2 ^ k := by
      rw [show e = k + 1 - fmt.mantissaBits from max_eq_left hnormal, zpow_sub₀ two_ne_zero,
        zpow_add₀ two_ne_zero, zpow_natCast, inv_pow]
      field_simp
    rw [hhalf] at herr
    exact herr.trans (mul_le_mul_of_nonneg_left (hk.trans (le_max_left _ _)) hu)
  · have hhalf : (1 / 2 : ℝ) * 2 ^ e = (2 : ℝ)⁻¹ ^ fmt.mantissaBits *
        (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) := by
      rw [show e = fmt.minExponent from max_eq_right (le_of_not_ge hnormal),
        zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, inv_pow]
      field_simp
    rw [hhalf] at herr
    exact herr.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hu)

/-- Rounding does not exceed a represented value of larger magnitude: if $y$ is represented in
`fmt` and $\lvert x\rvert \le \lvert y\rvert$, the rounding of $x$ has magnitude at most
$\lvert y\rvert$, for every nearest tie policy. -/
theorem abs_binaryFloatRound_le_of_abs_le (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) {x y : ℝ} (hy : IsBinaryRep fmt y)
    (hxy : |x| ≤ |y|) : |binaryFloatRound fmt r x| ≤ |y| := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [binaryFloatRound_zero fmt hr, abs_zero]
    exact abs_nonneg y
  obtain ⟨m, e', hm, hemin, -, rfl⟩ := hy
  set k := Int.log 2 |x|
  set e := fmt.targetExponent (k + 1)
  have he0 : (0 : ℝ) < 2 ^ e := zpow_pos two_pos _
  have hk : (2 : ℝ) ^ k ≤ |x| := by
    exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr hx)
  have hm' : |(m : ℝ)| < (2 : ℝ) ^ fmt.mantissaBits := by exact_mod_cast hm
  have hlt : |(m : ℝ) * (2 : ℝ) ^ e'| < (2 : ℝ) ^ (e' + fmt.mantissaBits) := by
    rw [abs_mul, abs_of_pos (zpow_pos (show (0 : ℝ) < 2 from two_pos) _),
      zpow_add₀ two_ne_zero, zpow_natCast]
    exact (mul_lt_mul_of_pos_right hm' (zpow_pos two_pos _)).trans_eq (mul_comm _ _)
  have hnormal : k + 1 - fmt.mantissaBits ≤ e' := by
    have := (zpow_lt_zpow_iff_right₀ one_lt_two).mp ((hk.trans hxy).trans_lt hlt)
    omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, e' = e + n := ⟨(e' - e).toNat, by
    have : e ≤ e' := max_le hnormal hemin
    omega⟩
  set M : ℤ := m * 2 ^ n
  have hy : (m : ℝ) * (2 : ℝ) ^ e' = (M : ℝ) * 2 ^ e := by
    rw [hn, zpow_add₀ two_ne_zero, zpow_natCast]
    push_cast [M]
    ring
  have hq : |x / (2 : ℝ) ^ e| ≤ |(M : ℝ)| := by
    have h' : |(M : ℝ)| * 2 ^ e = |(m : ℝ) * (2 : ℝ) ^ e'| := by
      rw [hy, abs_mul, abs_of_pos he0]
    rw [abs_div, abs_of_pos he0, div_le_iff₀ he0, h']
    exact hxy
  have hrq : |(r (x / (2 : ℝ) ^ e) : ℝ)| ≤ |(M : ℝ)| := by
    have h1 : |(r (x / (2 : ℝ) ^ e) : ℝ)| ≤ |x / (2 : ℝ) ^ e| + 1 / 2 := by
      simpa only [add_zero, zero_mul, one_mul] using (hr (x / (2 : ℝ) ^ e)).abs_le
    have h2 : |r (x / (2 : ℝ) ^ e)| < |M| + 1 := by
      have : |(r (x / (2 : ℝ) ^ e) : ℝ)| < |(M : ℝ)| + 1 := by linarith
      exact_mod_cast this
    exact_mod_cast (show |r (x / (2 : ℝ) ^ e)| ≤ |M| by omega)
  change |(r (x / (2 : ℝ) ^ e) : ℝ) * (2 : ℝ) ^ e| ≤ _
  rw [hy, abs_mul, abs_mul, abs_of_pos he0]
  exact mul_le_mul_of_nonneg_right hrq he0.le

end NLAlib.Computation
