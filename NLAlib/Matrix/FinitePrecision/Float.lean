/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Float.Basic

/-!
# Finite binary words and their real values

Binary representability, decoding and word encoding depend only on Lean core's logical
floating-point model. No arithmetic semantics or program evaluator is imported.

## Main results

* `NLAlib.Computation.isBinaryRep_floatDecode`: finite-format representability of decoding.
* `NLAlib.Computation.floatEncode_injective`: injective word encoding.
* `NLAlib.Computation.checkedFloat_eq_some_iff`: finiteness of a checked word.
-/

@[expose] public section

namespace NLAlib.Computation

open Float.Model Float.Model.UnpackedFloat

/-- A real value has a signed-integer mantissa whose magnitude is below two raised to the
format precision, and an exponent between its minimum and largest finite significand exponent.
The format is
Lean core's IEEE layout; this predicate makes no assumption about arithmetic or tie breaking. -/
def IsBinaryRep (fmt : Float.Model.Format) (x : ℝ) : Prop :=
  ∃ m e : ℤ, |m| < 2 ^ fmt.mantissaBits ∧ fmt.minExponent ≤ e ∧
    e ≤ (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
      fmt.mantissaBitsWithoutImplicit ∧ x = m * 2 ^ e

/-- The exact real value of a finite `Float`, with both signed zeros interpreted as zero.
Nonfinite words also decode to zero as a junk value; an arithmetic certificate must separately
exclude those words. -/
noncomputable def floatDecode (x : Float) : ℝ :=
  match x.toModel.unpack with
  | .finite s m e _ =>
    (match s with | .negative => -(m : ℝ) | .positive => (m : ℝ)) * 2 ^ e
  | _ => 0

/-- Zero is representable in a binary format with at least two exponent bits. The extra
hypothesis excludes one-bit formats allowed by older versions of core's layout structure. -/
theorem isBinaryRep_zero (fmt : Float.Model.Format) (he : 2 ≤ fmt.exponentBits) :
    IsBinaryRep fmt 0 := by
  refine ⟨0, fmt.minExponent, ?_, le_rfl, ?_, by simp⟩
  · simp
  · have hpow : 4 ≤ 2 ^ fmt.exponentBits := by
      calc 4 = 2 ^ 2 := rfl
           _ ≤ _ := Nat.pow_le_pow_right (by decide) he
    have hpow' : (4 : ℤ) ≤ 2 ^ fmt.exponentBits := by exact_mod_cast hpow
    have hp : 1 ≤ 2 ^ (fmt.exponentBits - 1) := Nat.one_le_two_pow
    simp only [Format.minExponent, Format.exponentBias, Format.mantissaBits]
    push_cast [hp]
    omega

/-- Every decoded `Float` has a binary64 representation: a signed integer mantissa of
magnitude less than $2^{53}$ and a significand exponent between $-1074$ and $971$.
Nonfinite words satisfy this statement only because their junk decoding is zero. -/
theorem isBinaryRep_floatDecode (x : Float) : IsBinaryRep .binary64 (floatDecode x) := by
  have hem := (unpackExponent (spec := .binary64) x.toModel.toBits.toBitVec).isLt
  have hmn := (unpackMantissa (spec := .binary64) x.toModel.toBits.toBitVec).isLt
  dsimp only [Format.binary64, Format.exponentBits] at hem
  dsimp only [Format.binary64, Format.mantissaBitsWithoutImplicit] at hmn
  have repr (s : Float.Model.UnpackedFloat.Sign) (m : ℕ) (e : ℤ) (hm : m < 2 ^ (53 : ℕ))
      (hemin : -1074 ≤ e) (hemax : e ≤ 971) :
      IsBinaryRep .binary64
        ((match s with | .negative => -(m : ℝ) | .positive => (m : ℝ)) * 2 ^ e) := by
    cases s
    · exact ⟨-(m : ℤ), e, by
          simpa [Format.binary64, Format.mantissaBits] using
            (show (m : ℤ) < 2 ^ (53 : ℕ) from by omega),
        hemin, hemax, by simp⟩
    · exact ⟨(m : ℤ), e, by
          simpa [Format.binary64, Format.mantissaBits] using
            (show (m : ℤ) < 2 ^ (53 : ℕ) from by omega),
        hemin, hemax, by simp⟩
  unfold floatDecode Float.Model.unpack UnpackedFloat.unpack
  dsimp only
  by_cases hmax : unpackExponent (spec := .binary64) x.toModel.toBits.toBitVec = -1#11
  · by_cases hm : unpackMantissa (spec := .binary64) x.toModel.toBits.toBitVec = 0#52
    <;> simp only [hmax, hm, ↓reduceIte]
    <;> exact isBinaryRep_zero _ (by decide)
  · by_cases hzero : unpackExponent (spec := .binary64) x.toModel.toBits.toBitVec = 0#11
    · by_cases hm : unpackMantissa (spec := .binary64) x.toModel.toBits.toBitVec = 0#52
      · simp only [hzero, hm, ↓reduceIte]
        exact isBinaryRep_zero _ (by decide)
      · simp only [hzero, hm, ↓reduceIte, BitVec.toNat_ofNat]
        exact repr _ _ _ (by omega) (by decide) (by decide)
    · have hmax' : (unpackExponent (spec := .binary64) x.toModel.toBits.toBitVec).toNat ≠ 2047 := by
        intro h
        apply hmax
        apply BitVec.eq_of_toNat_eq
        exact h
      have hzero' : (unpackExponent (spec := .binary64) x.toModel.toBits.toBitVec).toNat ≠ 0 := by
        intro h
        apply hzero
        apply BitVec.eq_of_toNat_eq
        exact h
      have hmm := (1#1 ++ unpackMantissa (spec := .binary64) x.toModel.toBits.toBitVec).isLt
      simp only [hmax, hzero, ↓reduceIte]
      apply repr _ _ _ hmm
      · change -1074 ≤ _ - 1075
        omega
      · change _ - 1075 ≤ 971
        omega

/-- The canonical bit encoding of a `Float`. This preserves signed zero; core canonicalizes
NaN encodings in its logical model. -/
def floatEncode (x : Float) : BitVec 64 := x.toBits.toBitVec

/-- Distinct logical floating-point words have distinct canonical 64-bit encodings. This
certifies a word representation, independently of any arithmetic accuracy or runtime bound. -/
theorem floatEncode_injective : Function.Injective floatEncode := by
  intro x y h
  cases x with
  | ofModel xm =>
    cases y with
    | ofModel ym =>
      congr
      cases xm with
      | mk xb hxb =>
        cases ym with
        | mk yb hyb =>
          congr
          exact UInt64.eq_of_toBitVec_eq h

/-- Retain a finite floating-point word and fail on NaN or either infinity. -/
def checkedFloat (x : Float) : Option Float := if x.isFinite then some x else none

/-- A successful check returns exactly the input word and certifies that it is finite. -/
theorem checkedFloat_eq_some_iff (x z : Float) :
    checkedFloat x = some z ↔ x.isFinite = true ∧ x = z := by
  by_cases h : x.isFinite = true <;> simp [checkedFloat, h]

/-- A successful check can equivalently be described using core's logical word model.
The model equality is propositional word equality, preserving the sign of zero. -/
theorem checkedFloat_eq_some_model_iff (x z : Float) :
    checkedFloat x = some z ↔ z.isFinite = true ∧ z.toModel = x.toModel := by
  rw [checkedFloat_eq_some_iff]
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hz, hm⟩
    have hzx : z = x := congrArg Float.ofModel hm
    exact ⟨hzx ▸ hz, hzx.symm⟩

/-- The smallest positive subnormal has exact real value $2^{-1074}$. -/
theorem floatDecode_ofBits_one : floatDecode (Float.ofBits 1) = 2 ^ (-1074 : ℤ) := by
  have hx : (Float.ofBits 1).toModel.unpack =
      .finite .positive 1 (-1074) (by decide) := rfl
  simp only [floatDecode, hx, Nat.cast_one, one_mul]

/-- Positive zero decodes to zero. -/
theorem floatDecode_ofBits_zero : floatDecode (Float.ofBits 0) = 0 := rfl

/-- The finite words of Lean's binary64 type. Unlike the raw carrier, every word has a
faithful real decoding; nonfinite IEEE outcomes are represented by execution failure. -/
abbrev FiniteFloat := {x : Float // x.isFinite = true}

/-- The valid-word carrier inherits the injective 64-bit encoding of raw `Float` words. -/
theorem FiniteFloat.floatEncode_injective :
    Function.Injective (fun x : FiniteFloat => floatEncode x.val) := by
  intro x y h
  apply Subtype.ext
  exact NLAlib.Computation.floatEncode_injective h

end NLAlib.Computation
