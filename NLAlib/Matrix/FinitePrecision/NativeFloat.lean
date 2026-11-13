/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.BinaryFloat
public import NLAlib.ForMathlib.Data.Float.Operations
public import NLAlib.ForMathlib.Data.Float.Literals

/-!
# Native finite binary64 arithmetic in the logical Float model

The arithmetic functions are Lean's actual Float operations. Their decoded accuracy and
finite-range guarantees are consequences of core normalization, rounding and packing, with
mixed error retained for gradual underflow. No optional evaluator is used.

The original core-model proofs follow the NumLean provenance recorded in
`docs/design/Finite-Precision-Arithmetic.md`. Native runtime replacements and their physical
costs are separate implementation obligations.

## Main results

* `NLAlib.Computation.absRelErr_float_mul`: mixed multiplication error.
* `NLAlib.Computation.isFinite_float_mul_of_abs_le`: finite in-range products.
* `NLAlib.Computation.floatDecode_add_eq_of_decode_zero`: exact zero addition.
-/

@[expose] public section

namespace NLAlib.Computation

set_option maxRecDepth 8192 in
/-- Squaring the smallest positive binary64 subnormal gives positive zero under the
logical native multiplication. The identity is checked by reduction of the bit operations. -/
theorem mul_float_ofBits_one :
    Float.ofBits 1 * Float.ofBits 1 = Float.ofBits 0 := by
  rfl

/-- Gradual underflow prevents an all-range relative multiplication bound with any
roundoff below one. An absolute underflow allowance or a restricted range is necessary. -/
theorem not_forall_float_mul_relErr {u : ℝ} (hu : u < 1) :
    ¬ ∀ x y : Float, RelErr u (floatDecode x * floatDecode y) (floatDecode (x * y)) := by
  intro h
  obtain ⟨δ, hδ, he⟩ := h (Float.ofBits 1) (Float.ofBits 1)
  rw [mul_float_ofBits_one, floatDecode_ofBits_zero, floatDecode_ofBits_one] at he
  have hp : (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-1074 : ℤ) ≠ 0 := by positivity
  have hone : 1 + δ = 0 := (mul_eq_zero.mp he.symm).resolve_left hp
  have hd : δ = -1 := by linarith
  rw [hd] at hδ
  norm_num at hδ
  exact (not_le_of_gt hu) hδ

open Float.Model Float.Model.UnpackedFloat

private local instance : Fact (2 ≤ Format.binary64.exponentBits) := ⟨by decide⟩

private theorem native_canonical (x : Float) : IsCanonical .binary64 x.toModel.unpack :=
  unpack_isCanonical .binary64 x.toModel.toBits.toBitVec

/-- The checked Float decoding agrees with the real value of core's unpacked model. -/
theorem floatDecode_eq_toReal (x : Float) : floatDecode x = x.toModel.unpack.toReal := by
  unfold floatDecode
  cases x.toModel.unpack with
  | finite s m e hm => cases s <;> simp only [toReal, Sign.toReal, neg_mul, one_mul]
  | _ => rfl

private theorem native_pack_value {x : Float} {r : UnpackedFloat}
    (hr : IsCanonical .binary64 r)
    (hx : x.toModel.unpack = UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r))
    (hf : x.isFinite = true) : r.IsFinite ∧ floatDecode x = r.toReal := by
  have hf' : (UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r)).IsFinite := by
    rw [← hx]
    exact hf
  have he := unpack_pack_of_isFinite hr hf'
  rw [he] at hf'
  exact ⟨hf', by rw [floatDecode_eq_toReal, hx, he]⟩

/-- Native binary64 addition has relative error on a finite result. [Higham2002, §2.2]. -/
theorem absRelErr_float_add (x y : Float) (hf : (x + y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) 0
      (floatDecode x + floatDecode y) (floatDecode (x + y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x + y)
    (add_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_add_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, add_zero, abs_sub_comm] using he

/-- Native binary64 subtraction has relative error on a finite result. [Higham2002, §2.2]. -/
theorem absRelErr_float_sub (x y : Float) (hf : (x - y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) 0
      (floatDecode x - floatDecode y) (floatDecode (x - y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x - y)
    (sub_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_sub_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, add_zero, abs_sub_comm] using he

/-- Native binary64 multiplication has mixed error on a finite result. [Higham2002, §2.2]. -/
theorem absRelErr_float_mul (x y : Float) (hf : (x * y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) (Format.binary64.underflowBound)
      (floatDecode x * floatDecode y) (floatDecode (x * y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x * y)
    (mul_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_mul_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, abs_sub_comm] using he

/-- Native binary64 division has mixed error on a finite result. [Higham2002, §2.2]. -/
theorem absRelErr_float_div (x y : FiniteFloat) (hf : (x.val / y.val).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) (Format.binary64.underflowBound)
      (floatDecode x.val / floatDecode y.val) (floatDecode (x.val / y.val)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x.val / y.val)
    (div_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)) rfl hf
  have he := abs_toReal_div_sub_le _ _ (native_canonical x.val) (native_canonical y.val)
    x.property y.property hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, abs_sub_comm] using he

open Float.Model.BinaryRounding

private theorem native_isFinite_of_nearest {r : UnpackedFloat} {a : ℝ}
    (hc : IsCanonical .binary64 r) (hf : r.IsFinite)
    (hn : IsNearestFloat Format.binary64.mantissaBits Format.binary64.minExponent a r.toReal)
    (hs : |a| ≤ Format.binary64.maxFinite) :
    (Float.ofModel (Float.Model.pack r)).isFinite = true := by
  have hm : 0 ≤ Format.binary64.maxFinite := by
    unfold Format.maxFinite
    exact mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (by positivity)
  have hb := hn.abs_le_of_abs_le (Format.isBinaryFloat_maxFinite .binary64)
    (by rwa [abs_of_nonneg hm])
  rw [abs_of_nonneg hm] at hb
  have he := unpack_pack_of_abs_toReal_le hc hf hb
  change (UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r)).isFinite = true
  rw [he]
  exact hf

/-- An in-range exact sum of finite words has a finite native result. [Higham2002, §2.2]. -/
theorem isFinite_float_add_of_abs_le (x y : FiniteFloat)
    (hs : |floatDecode x.val + floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val + y.val).isFinite = true := by
  have hc := add_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  have hf := isFinite_add_of_isFinite (spec := .binary64) _ _ x.property y.property
  have hn := isNearestFloat_toReal_add _ _ (native_canonical x.val) (native_canonical y.val) hf
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

/-- An in-range exact difference of finite words has a finite native result. [Higham2002, §2.2]. -/
theorem isFinite_float_sub_of_abs_le (x y : FiniteFloat)
    (hs : |floatDecode x.val - floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val - y.val).isFinite = true := by
  have hc := sub_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  have hf := isFinite_sub_of_isFinite (spec := .binary64) _ _ x.property y.property
  have hn := isNearestFloat_toReal_sub _ _ (native_canonical x.val) (native_canonical y.val) hf
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

/-- An in-range exact product of finite words has a finite native result. [Higham2002, §2.2]. -/
theorem isFinite_float_mul_of_abs_le (x y : FiniteFloat)
    (hs : |floatDecode x.val * floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val * y.val).isFinite = true := by
  have hc := mul_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  have hf := isFinite_mul_of_isFinite (spec := .binary64) _ _ x.property y.property
  have hn := isNearestFloat_toReal_mul _ _ (native_canonical x.val) (native_canonical y.val) hf
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

private theorem div_finite_nearest
    (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (s₁ s₂ : Sign) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    IsNearestFloat Format.binary64.mantissaBits Format.binary64.minExponent
      ((UnpackedFloat.finite s₁ m₁ e₁ hm₁).toReal /
        (UnpackedFloat.finite s₂ m₂ e₂ hm₂).toReal)
      (UnpackedFloat.div .binary64 (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂)).toReal := by
  obtain ⟨w, hw, hwv, he⟩ := exists_approximates_divCore (spec := .binary64)
    m₁ e₁ m₂ e₂ hm₁ hm₂
  have hn := isNearestFloat_toReal_roundWithAccuracy .binary64 (s₁ / s₂) _ _ _ w hw he
  rw [hwv] at hn
  have hv : toReal (.finite s₁ m₁ e₁ hm₁) / toReal (.finite s₂ m₂ e₂ hm₂)
      = (s₁ / s₂).toReal * ((m₁ * 2 ^ e₁) / (m₂ * 2 ^ e₂)) := by
    simp only [toReal, Sign.toReal_div]
    field_simp
    cases s₂ <;> cases s₁ <;> simp [Sign.toReal]
  rw [hv]
  exact hn

private theorem div_finite_nearest_of_finite (x y : UnpackedFloat)
    (hx : x.IsFinite) (hy : y.IsFinite) (hy0 : y.toReal ≠ 0) :
    (UnpackedFloat.div .binary64 x y).IsFinite ∧
      IsNearestFloat Format.binary64.mantissaBits Format.binary64.minExponent
        (x.toReal / y.toReal) (UnpackedFloat.div .binary64 x y).toReal := by
  cases x <;> cases y <;>
    first
    | (simp only [UnpackedFloat.IsFinite, UnpackedFloat.isFinite, Bool.false_eq_true] at hx; done)
    | (simp only [UnpackedFloat.IsFinite, UnpackedFloat.isFinite, Bool.false_eq_true] at hy; done)
    | (simp only [toReal, ne_eq, not_true_eq_false] at hy0; done)
    | skip
  case zero.finite s₁ s₂ m₂ e₂ hm₂ =>
    simp only [UnpackedFloat.div, UnpackedFloat.IsFinite, UnpackedFloat.isFinite, toReal,
      zero_div, true_and]
    exact isNearestFloat_self isBinaryFloat_zero
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    exact ⟨isFinite_roundWithAccuracy _ _ _ _ _, div_finite_nearest m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂⟩

/-- An in-range exact quotient with a nonzero divisor has a finite native result.
[Higham2002, §2.2]. -/
theorem isFinite_float_div_of_abs_le (x y : FiniteFloat) (hy : floatDecode y.val ≠ 0)
    (hs : |floatDecode x.val / floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val / y.val).isFinite = true := by
  have hc := div_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  obtain ⟨hf, hn⟩ := div_finite_nearest_of_finite x.val.toModel.unpack y.val.toModel.unpack
    x.property y.property (by rwa [← floatDecode_eq_toReal])
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

/-- Native negation preserves finite words and negates their exact real decoding.
[Higham2002, §2.2]. -/
theorem FiniteFloat.neg_spec (x : FiniteFloat) :
    (-x.val).isFinite = true ∧ floatDecode (-x.val) = -floatDecode x.val := by
  have hb : |floatDecode x.val| ≤ Format.binary64.maxFinite := by
    exact (isBinaryRep_floatDecode x.val).abs_le
  have hc := neg_isCanonical x.val.toModel.unpack (native_canonical x.val)
  have hf : x.val.toModel.unpack.neg.IsFinite :=
    (isFinite_neg x.val.toModel.unpack).mpr x.property
  have hv : x.val.toModel.unpack.neg.toReal = -floatDecode x.val := by
    rw [toReal_neg, ← floatDecode_eq_toReal]
  have hn := isNearestFloat_self (isBinaryFloat_toReal hc)
  have hout : (-x.val).isFinite = true :=
    native_isFinite_of_nearest hc hf hn (by rw [hv, abs_neg]; exact hb)
  have hvalue := native_pack_value (x := -x.val) hc rfl hout
  exact ⟨hout, hvalue.2.trans hv⟩

/-- Adding a finite word that decodes to zero preserves the other decoded value, including
subnormal values and both signs of zero. The equality concerns decoded values. -/
theorem floatDecode_add_eq_of_decode_zero (x y : FiniteFloat) (hx : floatDecode x.val = 0) :
    floatDecode (x.val + y.val) = floatDecode y.val := by
  have hf := isFinite_float_add_of_abs_le x y (by
    rw [hx, zero_add]
    exact (isBinaryRep_floatDecode y.val).abs_le)
  obtain ⟨hr, hv⟩ := native_pack_value (x := x.val + y.val)
    (add_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)) rfl hf
  have hn := isNearestFloat_toReal_add _ _ (native_canonical x.val) (native_canonical y.val) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, hx, zero_add] at hn
  have hrepr : Float.Model.BinaryRounding.IsBinaryFloat Format.binary64.mantissaBits
      Format.binary64.minExponent (floatDecode y.val) := by
    rw [floatDecode_eq_toReal]
    exact isBinaryFloat_toReal (native_canonical y.val)
  exact hv.trans (hn.eq_of_isBinaryFloat hrepr)

end NLAlib.Computation
