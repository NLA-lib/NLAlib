/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.WordRepresentation
public import NLAlib.Matrix.FinitePrecision.NativeFloatSqrt
public import NLAlib.Ops.Catalog.Scalar

/-!
# Total finite-word binary64 arithmetic for Ops

Addition, subtraction, multiplication, division, negation and square root use Lean's native
Float functions on finite words. A nonfinite result is replaced by positive zero; the accuracy
range proves that fallback is inactive. Rational literals use a separately specified nearest
binary64 word constructor, avoiding overflow in separate numerator/denominator conversions.
Its tie policy is Mathlib's integer rounding policy, not a claim about a native rational API.

The numerical model retains gradual underflow and an explicit largest-finite-result range.
It concerns core's logical Float functions; native runtime replacement and physical operation
costs require their own implementation certificates.

## Main results

* `NLAlib.Ops.Float64.mixedModel_machine`: in-range native arithmetic with gradual underflow.
* `NLAlib.Ops.Float64.decode_lit_zero`: the zero literal decodes exactly.
* `NLAlib.Ops.Float64.decode_add_of_decode_zero`: exact accumulation from decoded zero.
* `NLAlib.Ops.Float64.exists_scalar_model`: joint functional and numerical realization.
-/

@[expose] public section

namespace NLAlib.Ops.Float64

open Computation Float.Model

/-- The real decoding of a finite logical binary64 word. -/
noncomputable def decode (x : FiniteFloat) : ℝ := floatDecode x.val

/-- Positive zero is a finite binary64 word. -/
def zeroWord : FiniteFloat := ⟨Float.ofBits 0, rfl⟩

/-- The explicit policy for a nonfinite arithmetic result is positive zero. Accuracy theorems
prove this branch is inactive on their stated range. -/
def finiteOrZero (x : Float) : FiniteFloat :=
  if h : x.isFinite = true then ⟨x, h⟩ else zeroWord

/-- A finite result is retained as its actual native word, including its sign of zero. -/
theorem val_finiteOrZero (x : Float) (h : x.isFinite = true) : (finiteOrZero x).val = x := by
  simp [finiteOrZero, h]

/-- Exact target values in the closed largest-finite binary64 interval. -/
noncomputable def safe (x : ℝ) : Prop := |x| ≤ Format.binary64.maxFinite

/-- Mathlib's nearest integer rounding has the half-unit absolute allowance used by the
declared binary64 literal constructor. -/
theorem absRelErr_round (x : ℝ) : AbsRelErr 0 (1 / 2) x (round x : ℝ) := by
  simpa only [AbsRelErr, zero_mul, zero_add] using abs_sub_round x

/-- Round a real target to a represented binary64 word within range, and return positive zero
outside range. This is the declared logical literal policy, separate from native arithmetic. -/
noncomputable def roundedWord (x : ℝ) : FiniteFloat := by
  classical
  exact if h : safe x then
    finiteFloatOfRep (binaryFloatRound .binary64 round x)
      (isBinaryRep_binaryFloatRound .binary64 (by decide) absRelErr_round h)
  else zeroWord

/-- In-range literal construction decodes to the existing mathematical binary quantizer. -/
theorem decode_roundedWord {x : ℝ} (h : safe x) :
    decode (roundedWord x) = binaryFloatRound .binary64 round x := by
  simp only [roundedWord, dif_pos h, decode, floatDecode_finiteFloatOfRep]

/-- The rounded-word constructor has binary64 relative and absolute underflow allowances.
[Higham2002, §2.2]. -/
theorem abs_decode_roundedWord_sub_le {x : ℝ} (h : safe x) :
    |decode (roundedWord x) - x| ≤
      Format.binary64.unitRoundoff * |x| + Format.binary64.underflowBound := by
  rw [decode_roundedWord h]
  have he := absRelErr_binaryFloatRound .binary64 absRelErr_round x
  simpa only [AbsRelErr, Format.unitRoundoff, Format.underflowBound, zpow_neg,
    zpow_natCast, inv_pow, abs_sub_comm] using he

/-- The actual native arithmetic functions on finite words, totalized at nonfinite results.
Rational literals follow `roundedWord`; square root of a negative input has the same fallback. -/
noncomputable def machine : Machine FiniteFloat where
  lit q := roundedWord q
  add a b := finiteOrZero (a.val + b.val)
  sub a b := finiteOrZero (a.val - b.val)
  mul a b := finiteOrZero (a.val * b.val)
  div a b := finiteOrZero (a.val / b.val)
  neg a := finiteOrZero (-a.val)
  sqrt a := finiteOrZero a.val.sqrt

/-- Native finite-word arithmetic satisfies the mixed model on exact results in the largest
finite interval. The proof excludes overflow through the range and retains gradual underflow.
No execution-success premise or numerical assertion outside that range is used.
[Higham2002, §2.2]. -/
theorem mixedModel_machine :
    MixedModel Format.binary64.unitRoundoff Format.binary64.underflowBound decode machine safe where
  roundoff_nonneg := Format.unitRoundoff_nonneg _
  absolute_nonneg := Format.underflowBound_nonneg _
  lit q h := abs_decode_roundedWord_sub_le h
  add a b h := by
    have hf := isFinite_float_add_of_abs_le a b h
    have he := (absRelErr_float_add a.val b.val hf).mono le_rfl
      (Format.underflowBound_nonneg .binary64)
    simpa only [machine, decode, val_finiteOrZero _ hf, AbsRelErr, abs_sub_comm] using he
  sub a b h := by
    have hf := isFinite_float_sub_of_abs_le a b h
    have he := (absRelErr_float_sub a.val b.val hf).mono le_rfl
      (Format.underflowBound_nonneg .binary64)
    simpa only [machine, decode, val_finiteOrZero _ hf, AbsRelErr, abs_sub_comm] using he
  mul a b h := by
    have hf := isFinite_float_mul_of_abs_le a b h
    have he := absRelErr_float_mul a.val b.val hf
    simpa only [machine, decode, val_finiteOrZero _ hf, AbsRelErr, abs_sub_comm] using he
  div a b hb h := by
    have hf := isFinite_float_div_of_abs_le a b hb h
    have he := absRelErr_float_div a b hf
    simpa only [machine, decode, val_finiteOrZero _ hf, AbsRelErr, abs_sub_comm] using he
  neg a := by
    obtain ⟨hf, hv⟩ := a.neg_spec
    simpa only [machine, decode, val_finiteOrZero _ hf] using hv
  sqrt a ha _ := by
    obtain ⟨hf, _, he⟩ := a.sqrt_spec ha
    simpa only [machine, decode, val_finiteOrZero _ hf, AbsRelErr, abs_sub_comm,
      abs_of_nonneg (Real.sqrt_nonneg _)] using he

/-- The literal zero has exact zero decoding, beyond what the mixed error allowance alone says. -/
theorem decode_lit_zero : decode (machine.lit 0) = 0 := by
  simp only [machine, Rat.cast_zero]
  rw [decode_roundedWord (by simpa [safe] using Format.binary64.maxFinite_pos.le)]
  exact binaryFloatRound_zero .binary64 absRelErr_round

/-- An accumulation starting from decoded zero preserves the other decoded word exactly.
This includes the subnormal range and makes no equality claim about signed-zero bit patterns. -/
theorem decode_add_of_decode_zero (a b : FiniteFloat) (h : decode a = 0) :
    decode (machine.add a b) = decode b := by
  have hf := isFinite_float_add_of_abs_le a b (by
    change |decode a + decode b| ≤ _
    rw [h, zero_add]
    exact (isBinaryRep_floatDecode b.val).abs_le)
  simpa only [machine, decode, val_finiteOrZero _ hf] using
    floatDecode_add_eq_of_decode_zero a b h

/-- The same word functions simultaneously realize scalar execution and the mixed numerical
model. Neither interpretation nor arithmetic accuracy depends on an algorithm's output. -/
theorem exists_scalar_model :
    ∃ I : Interp ScalarOp Empty FiniteFloat, IsScalar machine I ∧
      MixedModel Format.binary64.unitRoundoff Format.binary64.underflowBound decode machine safe :=
  ⟨Interp.ofFns machine.fn, isScalar_ofFns _ _ (fun _ => rfl), mixedModel_machine⟩

end NLAlib.Ops.Float64
