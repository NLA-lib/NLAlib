/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite binary representation and checked Lean Float execution

Lean's `Float.Model.Format` describes the layout. `IsBinaryRep` records only finite real
representability; it imposes no arithmetic or rounding policy. `floatDecode` reads finite
words exactly and uses zero as a junk value for nonfinite words. `checkedFloatSem` rejects
nonfinite operands and results, so a successful comparison never observes that junk value.
`FiniteFloat` restricts the carrier to valid finite words, and `finiteFloatSem` lifts the checked
operations to that carrier without repeating their finiteness checks. The raw interpreter cannot
satisfy unconditional arithmetic-success clauses on a carrier that still includes NaN.
Both checked interpreters leave conversion to a natural index unsupported: `toNat` always
fails, even at zero. Their arithmetic certificates therefore do not supply index exactness
for a dynamic binder. A separate conversion implementation is required for that use.

The certificates below establish bounded exponents, a 64-bit injective encoding, and
correspondence to core's logical floating-point operations. They do not assert the
mixed-error accuracy contract for `Float`. Core's native operation replacements remain in
the trust boundary. No private package or SciLean dependency is needed.

## Main results

* `NLAlib.Computation.isBinaryRep_floatDecode`: every decoded word has a bounded binary
  representation; nonfinite words decode to the representable junk value zero.
* `NLAlib.Computation.floatEncode_injective`: words have an injective 64-bit encoding.
* `NLAlib.Computation.checkedFloat_eq_some_iff`: successful checks preserve finite words.
* `NLAlib.Computation.map_finiteFloatSem_bin`: finite-word execution erases to the raw interpreter.
* `NLAlib.Computation.not_isArithErrSem_checkedFloatSem`: raw nonfinite words obstruct an
  unconditional arithmetic contract, independently of the error relation.
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

/-- Checked binary64 arithmetic. Nonfinite inputs and outputs fail; unsupported bitwise
operations fail. Rational literals first convert numerator and denominator separately, then
perform division, with finiteness checks at all three stages. This is not a claim that arbitrary
rational literals are correctly rounded once. Conversions preserve a checked word. -/
def checkedFloatSem : ScalarSem Unit Float where
  lit _ q := do
    let x ← checkedFloat (Float.ofInt q.num)
    let y ← checkedFloat (Float.ofNat q.den)
    checkedFloat (x / y)
  bin _ b x y :=
    if x.isFinite && y.isFinite then
      match b with
      | .add => checkedFloat (x + y)
      | .sub => checkedFloat (x - y)
      | .mul => checkedFloat (x * y)
      | .div => checkedFloat (x / y)
      | _ => none
    else none
  un _ o x :=
    if x.isFinite then
      match o with
      | .neg => checkedFloat (-x)
      | .conj | .re => some x
      | .sqrt => checkedFloat x.sqrt
      | .bnot => none
    else none
  cmp _ c x y :=
    if x.isFinite && y.isFinite then
      match c with
      | .eq => some (x == y)
      | .lt => some (x < y)
      | .le => some (decide (x ≤ y))
    else none
  convert _ _ x := checkedFloat x

/-- A successful binary instruction has finite inputs and output and is exactly the
corresponding operation of Lean core's logical model. Unsupported bitwise instructions cannot
succeed. This theorem asserts execution correspondence, not numerical accuracy. -/
theorem bin_checkedFloatSem_eq_some_iff (b : BinOp) (x y z : Float) :
    checkedFloatSem.bin () b x y = some z ↔
      x.isFinite = true ∧ y.isFinite = true ∧ z.isFinite = true ∧
        match b with
        | .add => z.toModel = x.toModel + y.toModel
        | .sub => z.toModel = x.toModel - y.toModel
        | .mul => z.toModel = x.toModel * y.toModel
        | .div => z.toModel = x.toModel / y.toModel
        | _ => False := by
  cases b <;> by_cases hx : x.isFinite = true <;>
    by_cases hy : y.isFinite = true <;>
    simp only [checkedFloatSem, Option.bind_eq_bind, Bool.and_eq_true, hx, hy,
      Bool.false_eq_true, and_false, and_true, and_self, ↓reduceIte, reduceCtorEq,
      checkedFloat_eq_some_model_iff, true_and, false_and, and_congr_right_iff]
  all_goals intro hz; rfl

/-- A successful unary instruction has finite input and output and is the corresponding
core model operation. Conjugation and real-part extraction preserve the real scalar word. -/
theorem un_checkedFloatSem_eq_some_iff (o : UnOp) (x z : Float) :
    checkedFloatSem.un () o x = some z ↔
      x.isFinite = true ∧ z.isFinite = true ∧
        match o with
        | .neg => z.toModel = -x.toModel
        | .conj | .re => z = x
        | .sqrt => z.toModel = Float.Model.sqrt x.toModel
        | .bnot => False := by
  cases o <;> by_cases hx : x.isFinite = true <;>
    simp only [checkedFloatSem, Option.bind_eq_bind, hx, ↓reduceIte,
      checkedFloat_eq_some_model_iff, true_and, false_and, reduceCtorEq]
  · rfl
  · constructor
    · intro h
      cases h
      exact ⟨hx, rfl⟩
    · rintro ⟨hz, rfl⟩
      rfl
  · constructor
    · intro h
      cases h
      exact ⟨hx, rfl⟩
    · rintro ⟨hz, rfl⟩
      rfl
  · rfl
  · simp

/-- A comparison succeeds exactly when both inputs are finite, and returns their actual
IEEE comparison. This does not identify comparisons of NaN with comparisons of real numbers. -/
theorem cmp_checkedFloatSem_eq_some_iff (c : CmpOp) (x y : Float) (z : Bool) :
    checkedFloatSem.cmp () c x y = some z ↔
      x.isFinite = true ∧ y.isFinite = true ∧
        z = match c with
          | .eq => x == y
          | .lt => x < y
          | .le => decide (x ≤ y) := by
  cases c <;> by_cases hx : x.isFinite = true <;>
    by_cases hy : y.isFinite = true <;>
    simp only [checkedFloatSem, Bool.and_eq_true, hx, hy, Bool.false_eq_true,
      and_self, and_true, and_false, ↓reduceIte, reduceCtorEq, false_and, true_and,
      Option.some.injEq]
  all_goals exact eq_comm

-- The closed pack/unpack computation traverses the core bit representation.
set_option maxRecDepth 2048 in
/-- The smallest positive subnormal has exact real value $2^{-1074}$. -/
theorem floatDecode_ofBits_one : floatDecode (Float.ofBits 1) = 2 ^ (-1074 : ℤ) := by
  have hx : (Float.ofBits 1).toModel.unpack =
      .finite .positive 1 (-1074) (by decide) := rfl
  simp only [floatDecode, hx, Nat.cast_one, one_mul]

/-- Positive zero decodes to zero. -/
theorem floatDecode_ofBits_zero : floatDecode (Float.ofBits 0) = 0 := rfl

-- Core's closed rounded multiplication recurses through the subnormal exponent shift.
set_option maxRecDepth 8192 in
/-- Squaring the smallest positive subnormal underflows to positive zero. This is a theorem
of core's logical operations, not a native floating-point evaluation used as evidence. -/
theorem bin_checkedFloatSem_mul_ofBits_one :
    checkedFloatSem.bin () .mul (Float.ofBits 1) (Float.ofBits 1) =
      some (Float.ofBits 0) := by
  rfl

/-- Checked binary64 arithmetic cannot satisfy an all-range pure-relative error contract
with unit roundoff below one: the square of a nonzero subnormal rounds to zero. The predicate
`safe` is arbitrary, since the error clause constrains every successful operation. -/
theorem not_isRelErrSem_checkedFloatSem (u : Unit → ℝ)
    (safe : Unit → ℝ → Prop) (hu : u () < 1) :
    ¬ IsRelErrSem u (fun _ => floatDecode) safe checkedFloatSem := by
  intro h
  obtain ⟨δ, hδ, heq⟩ := h.bin_err () .mul (Float.ofBits 1) (Float.ofBits 1)
    (Float.ofBits 0) trivial bin_checkedFloatSem_mul_ofBits_one
  rw [floatDecode_ofBits_zero, floatDecode_ofBits_one] at heq
  change 0 = (2 ^ (-1074 : ℤ) * 2 ^ (-1074 : ℤ) : ℝ) * (1 + δ) at heq
  have hpow : (2 : ℝ) ^ (-1074 : ℤ) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hone : 1 + δ = 0 := (mul_eq_zero.mp heq.symm).resolve_left (mul_ne_zero hpow hpow)
  have hδ' : δ = -1 := by linarith
  rw [hδ'] at hδ
  norm_num at hδ
  exact (not_le_of_gt hu) hδ

/-- The finite words of Lean's binary64 type. Unlike the raw carrier, every word has a
faithful real decoding; nonfinite IEEE outcomes are represented by execution failure. -/
abbrev FiniteFloat := {x : Float // x.isFinite = true}

/-- A successful literal evaluation returns a finite word. This certifies the actual sequence
of conversions in `checkedFloatSem`, without an accuracy claim about those conversions. -/
theorem isFinite_of_checkedFloatSem_lit_eq_some (q : ℚ) (z : Float)
    (h : checkedFloatSem.lit () q = some z) : z.isFinite = true := by
  simp only [checkedFloatSem, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨x, hx, y, hy, hxy⟩
  rcases (checkedFloat_eq_some_iff _ _).mp hxy with ⟨hf, rfl⟩
  exact hf

/-- Lift an optional word whose successful values have already been proved finite. The proof
is erased and this function performs no further finiteness check. -/
def finiteFloatLift :
    (o : Option Float) → (∀ x, o = some x → x.isFinite = true) → Option FiniteFloat
  | none, _ => none
  | some x, h => some ⟨x, h x rfl⟩

private theorem map_finiteFloatLift (o : Option Float)
    (h : ∀ x, o = some x → x.isFinite = true) :
    (finiteFloatLift o h).map Subtype.val = o := by
  cases o <;> rfl

/-- Checked binary64 execution on a valid-word carrier. Results are lifted using proofs of
finiteness already established by `checkedFloatSem`; the lift performs no further finiteness
check. `isArithErrSem_finiteFloatSem` in `Computation/IEEE.lean` certifies binary arithmetic
accuracy and range success. Arbitrary rational-literal accuracy and correctness of native
runtime replacements remain separate obligations. Conversion to a natural index remains
unsupported and always returns `none`. -/
def finiteFloatSem : ScalarSem Unit FiniteFloat where
  lit _ q := finiteFloatLift (checkedFloatSem.lit () q)
    (fun z h => isFinite_of_checkedFloatSem_lit_eq_some q z h)
  bin _ b x y := finiteFloatLift (checkedFloatSem.bin () b x.val y.val)
    (fun z h => ((bin_checkedFloatSem_eq_some_iff b x.val y.val z).mp h).2.2.1)
  un _ o x := finiteFloatLift (checkedFloatSem.un () o x.val)
    (fun z h => ((un_checkedFloatSem_eq_some_iff o x.val z).mp h).2.1)
  cmp _ c x y := checkedFloatSem.cmp () c x.val y.val
  convert _ _ x := finiteFloatLift (checkedFloatSem.convert () () x.val)
    (fun z h => (checkedFloat_eq_some_model_iff x.val z).mp h |>.1)

/-- Forgetting the finite-word proof recovers exactly the checked literal evaluation. -/
theorem map_finiteFloatSem_lit (q : ℚ) :
    (finiteFloatSem.lit () q).map Subtype.val = checkedFloatSem.lit () q :=
  map_finiteFloatLift _ _

/-- Forgetting finite-word proofs recovers exactly the checked binary operation. -/
theorem map_finiteFloatSem_bin (b : BinOp) (x y : FiniteFloat) :
    (finiteFloatSem.bin () b x y).map Subtype.val = checkedFloatSem.bin () b x.val y.val :=
  map_finiteFloatLift _ _

/-- Forgetting finite-word proofs recovers exactly the checked unary operation. -/
theorem map_finiteFloatSem_un (o : UnOp) (x : FiniteFloat) :
    (finiteFloatSem.un () o x).map Subtype.val = checkedFloatSem.un () o x.val :=
  map_finiteFloatLift _ _

/-- Comparisons on finite words are precisely the checked comparisons on their underlying words. -/
theorem cmp_finiteFloatSem (c : CmpOp) (x y : FiniteFloat) :
    finiteFloatSem.cmp () c x y = checkedFloatSem.cmp () c x.val y.val := rfl

/-- Forgetting the finite-word proof recovers exactly the checked conversion. -/
theorem map_finiteFloatSem_convert (x : FiniteFloat) :
    (finiteFloatSem.convert () () x).map Subtype.val = checkedFloatSem.convert () () x.val :=
  map_finiteFloatLift _ _

/-- The checked finite-word interpreter has no index-conversion implementation. This is
execution failure even for nonnegative decoded words, not a floor-conversion certificate. -/
theorem toNat_finiteFloatSem (x : FiniteFloat) : finiteFloatSem.toNat () x = none := rfl

/-- The valid-word carrier inherits the injective 64-bit encoding of raw `Float` words. -/
theorem FiniteFloat.floatEncode_injective :
    Function.Injective (fun x : FiniteFloat => floatEncode x.val) := by
  intro x y h
  apply Subtype.ext
  exact NLAlib.Computation.floatEncode_injective h

-- The closed NaN check unfolds core's canonical packed representation.
set_option maxRecDepth 2048 in
/-- The raw checked interpreter cannot satisfy the arithmetic contract for any error relation,
decoding or safe-result predicate: the contract requires conjugation to succeed on every word,
whereas the interpreter rejects NaN. Use a finite-word carrier for future arithmetic adapters. -/
theorem not_isArithErrSem_checkedFloatSem
    (err : Unit → BinOp → ℝ → ℝ → Prop) (dec : Unit → Float → ℝ)
    (safe : Unit → ℝ → Prop) : ¬ IsArithErrSem err dec safe checkedFloatSem := by
  intro h
  obtain ⟨z, hz, _⟩ := h.conj () (Float.ofBits 0x7ff8000000000000)
  have hf : checkedFloatSem.un () .conj (Float.ofBits 0x7ff8000000000000) = none := rfl
  rw [hf] at hz
  cases hz

end NLAlib.Computation
