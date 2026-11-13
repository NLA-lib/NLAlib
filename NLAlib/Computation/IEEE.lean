/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import NLAlib.Computation.BinaryFloat
public import NLAlib.Computation.MatvecRoutine
public import NLAlib.Computation.VectorErrors
public import NLAlib.ForMathlib.Data.List.Range
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import NLAlib.ForMathlib.Data.Float.Operations
public import NLAlib.ForMathlib.Data.Float.Literals

/-!
# Certified finite binary64 arithmetic

The finite-word endpoint uses actual Lean `Float` operations through core's logical model.
The inherited arithmetic interface separates successful-operation accuracy from input-based
range success. Gradual underflow is retained as an absolute error allowance; overflow and
invalid operations are rejected by checked execution. No private numerical package is imported.

The format-generic core-model accuracy proofs are adapted from the supplied NumLean archive;
source paths, archive hash and licensing status are recorded in
`docs/design/Finite-Precision-Arithmetic.md`. Native runtime replacements remain trusted to
implement Lean's model. Counts and physical kernel costs are separate certificates.

## Main results

* `NLAlib.Computation.isArithErrSem_finiteFloatSem`: mixed-error accuracy and range success.
* `NLAlib.Computation.addsZeroExactly_finiteFloatSem`: exact zero addition for kernel accumulation.
* `NLAlib.Computation.isMatvecErrOn_finiteFloatVectorDoubleOracle`: input-range success and
  mixed normwise error for actual vector doubling in every dimension.
-/

@[expose] public section

namespace NLAlib.Computation

open Float.Model Float.Model.UnpackedFloat
open scoped Matrix

/-- Positive binary64 zero on the finite-word carrier. -/
def finiteFloatZero : FiniteFloat := ⟨Float.ofBits 0, rfl⟩

/-- Binary64 one on the finite-word carrier. -/
def finiteFloatOne : FiniteFloat := ⟨Float.ofBits 0x3ff0000000000000, rfl⟩

/-- Positive binary64 zero decodes exactly to zero. -/
theorem floatDecode_finiteFloatZero : floatDecode finiteFloatZero.val = 0 := rfl

-- The closed pack/unpack computation traverses the binary64 bit representation.
set_option maxRecDepth 4096 in
/-- Binary64 one decodes exactly to one. -/
theorem floatDecode_finiteFloatOne : floatDecode finiteFloatOne.val = 1 := by
  have hx : (Float.ofBits 0x3ff0000000000000).toModel.unpack =
      .finite .positive (2 ^ 52) (-52) (by decide) := rfl
  norm_num [finiteFloatOne, floatDecode, hx]

/-- A checked binary64 stored-entry interpreter with the supplied finite ROM, zero tape,
no oracles or black-box kernels, 64-bit words, and one logical charge per operation.
Scalar overflow and invalid operations fail; index conversion is unsupported. The scalar
accuracy certificate is `isArithErrSem_finiteFloatSem`. Logical charges do not certify native
runtime costs. This interpreter supports concrete finite-word program examples.
No printed source. -/
def finiteFloatStoredInterp (values : Array FiniteFloat) : Interp Unit Unit FiniteFloat ℕ where
  sem := finiteFloatSem
  charge _ := 1
  tape _ _ := finiteFloatZero
  oracle _ _ _ := none
  height _ := 0
  rom i := values[i]?
  romSize _ := values.size
  width _ := 64

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

private theorem float_add_error (x y : Float) (hf : (x + y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) 0
      (floatDecode x + floatDecode y) (floatDecode (x + y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x + y)
    (add_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_add_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, add_zero, abs_sub_comm] using he

private theorem float_sub_error (x y : Float) (hf : (x - y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) 0
      (floatDecode x - floatDecode y) (floatDecode (x - y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x - y)
    (sub_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_sub_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, add_zero, abs_sub_comm] using he

private theorem float_mul_error (x y : Float) (hf : (x * y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) (Format.binary64.underflowBound)
      (floatDecode x * floatDecode y) (floatDecode (x * y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x * y)
    (mul_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_mul_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, abs_sub_comm] using he

private theorem float_div_error (x y : FiniteFloat) (hf : (x.val / y.val).isFinite = true) :
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

private theorem float_add_isFinite (x y : FiniteFloat)
    (hs : |floatDecode x.val + floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val + y.val).isFinite = true := by
  have hc := add_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  have hf := isFinite_add_of_isFinite (spec := .binary64) _ _ x.property y.property
  have hn := isNearestFloat_toReal_add _ _ (native_canonical x.val) (native_canonical y.val) hf
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

private theorem float_sub_isFinite (x y : FiniteFloat)
    (hs : |floatDecode x.val - floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val - y.val).isFinite = true := by
  have hc := sub_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  have hf := isFinite_sub_of_isFinite (spec := .binary64) _ _ x.property y.property
  have hn := isNearestFloat_toReal_sub _ _ (native_canonical x.val) (native_canonical y.val) hf
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

private theorem float_mul_isFinite (x y : FiniteFloat)
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

private theorem float_div_isFinite (x y : FiniteFloat) (hy : floatDecode y.val ≠ 0)
    (hs : |floatDecode x.val / floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val / y.val).isFinite = true := by
  have hc := div_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  obtain ⟨hf, hn⟩ := div_finite_nearest_of_finite x.val.toModel.unpack y.val.toModel.unpack
    x.property y.property (by rwa [← floatDecode_eq_toReal])
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

private theorem finiteFloatSem_bin_error (b : BinOp) (x y z : FiniteFloat)
    (hb : b.IsArith) (h : finiteFloatSem.bin () b x y = some z) :
    AbsRelErr Format.binary64.unitRoundoff Format.binary64.underflowBound
      (b.realOp (floatDecode x.val) (floatDecode y.val)) (floatDecode z.val) := by
  have hr := map_finiteFloatSem_bin b x y
  rw [h, Option.map_some] at hr
  obtain ⟨_, _, _, hm⟩ := (bin_checkedFloatSem_eq_some_iff b x.val y.val z.val).mp hr.symm
  cases b <;> simp only [BinOp.IsArith] at hb
  case add =>
    have heq : z.val = x.val + y.val := congrArg Float.ofModel hm
    have he := float_add_error x.val y.val (heq ▸ z.property)
    simpa only [BinOp.realOp, heq] using
      he.mono le_rfl (Format.underflowBound_nonneg .binary64)
  case sub =>
    have heq : z.val = x.val - y.val := congrArg Float.ofModel hm
    have he := float_sub_error x.val y.val (heq ▸ z.property)
    simpa only [BinOp.realOp, heq] using
      he.mono le_rfl (Format.underflowBound_nonneg .binary64)
  case mul =>
    have heq : z.val = x.val * y.val := congrArg Float.ofModel hm
    have he := float_mul_error x.val y.val (heq ▸ z.property)
    simpa only [BinOp.realOp, heq] using he
  case div =>
    have heq : z.val = x.val / y.val := congrArg Float.ofModel hm
    have he := float_div_error x y (heq ▸ z.property)
    simpa only [BinOp.realOp, heq] using he

private theorem finiteFloatSem_bin_exists_of_raw {b : BinOp} {x y : FiniteFloat} {z : Float}
    (h : checkedFloatSem.bin () b x.val y.val = some z) :
    ∃ w, finiteFloatSem.bin () b x y = some w := by
  have hr := map_finiteFloatSem_bin b x y
  rw [h] at hr
  obtain ⟨w, hw, _⟩ := Option.map_eq_some_iff.mp hr
  exact ⟨w, hw⟩

private theorem finiteFloatSem_bin_exists (b : BinOp) (x y : FiniteFloat)
    (hb : b.IsArith) (hdiv : b = .div → floatDecode y.val ≠ 0)
    (hs : |b.realOp (floatDecode x.val) (floatDecode y.val)| ≤ Format.binary64.maxFinite) :
    ∃ z, finiteFloatSem.bin () b x y = some z := by
  cases b <;> simp only [BinOp.IsArith] at hb
  case add =>
    have hf := float_add_isFinite x y hs
    apply finiteFloatSem_bin_exists_of_raw (z := x.val + y.val)
    simp only [checkedFloatSem, x.property, y.property, Bool.and_self, ↓reduceIte,
      checkedFloat, hf]
  case sub =>
    have hf := float_sub_isFinite x y hs
    apply finiteFloatSem_bin_exists_of_raw (z := x.val - y.val)
    simp only [checkedFloatSem, x.property, y.property, Bool.and_self, ↓reduceIte,
      checkedFloat, hf]
  case mul =>
    have hf := float_mul_isFinite x y hs
    apply finiteFloatSem_bin_exists_of_raw (z := x.val * y.val)
    simp only [checkedFloatSem, x.property, y.property, Bool.and_self, ↓reduceIte,
      checkedFloat, hf]
  case div =>
    have hf := float_div_isFinite x y (hdiv rfl) hs
    apply finiteFloatSem_bin_exists_of_raw (z := x.val / y.val)
    simp only [checkedFloatSem, x.property, y.property, Bool.and_self, ↓reduceIte,
      checkedFloat, hf]




private theorem native_neg_exact (x : FiniteFloat) :
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

private theorem finiteFloatSem_neg (x : FiniteFloat) :
    ∃ z, finiteFloatSem.un () .neg x = some z ∧
      floatDecode z.val = -floatDecode x.val := by
  obtain ⟨hf, hv⟩ := native_neg_exact x
  refine ⟨⟨-x.val, hf⟩, ?_, hv⟩
  apply Option.map_injective Subtype.val_injective
  rw [map_finiteFloatSem_un, Option.map_some]
  exact (un_checkedFloatSem_eq_some_iff .neg x.val (-x.val)).2 ⟨x.property, hf, rfl⟩

private theorem finiteFloatSem_zero :
    ∃ z, finiteFloatSem.lit () 0 = some z ∧ floatDecode z.val = 0 := by
  refine ⟨⟨Float.ofBits 0, rfl⟩, ?_, ?_⟩
  · apply Option.map_injective Subtype.val_injective
    rw [map_finiteFloatSem_lit, Option.map_some]
    simp only [checkedFloatSem, Rat.num_zero, Rat.den_zero, checkedFloat,
      Float.isFinite_ofInt_zero,
      Float.isFinite_ofNat_one, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
      Float.div_ofInt_zero_ofNat_one]
    rfl
  · rfl

private theorem finiteFloatSem_conj (x : FiniteFloat) :
    ∃ z, finiteFloatSem.un () .conj x = some z ∧ floatDecode z.val = floatDecode x.val := by
  refine ⟨x, ?_, rfl⟩
  apply Option.map_injective Subtype.val_injective
  rw [map_finiteFloatSem_un, Option.map_some]
  exact (un_checkedFloatSem_eq_some_iff .conj x.val x.val).2 ⟨x.property, x.property, rfl⟩

/-- Adding a finite binary64 word whose real value is zero preserves the other real value
exactly whenever the checked operation succeeds, including the subnormal range and signed zero.
The assertion concerns decoded values, not equality of signed-zero bit patterns. -/
theorem addsZeroExactly_finiteFloatSem :
    AddsZeroExactly (fun _ (x : FiniteFloat) => floatDecode x.val) finiteFloatSem := by
  intro p x y z hrun hx
  cases p
  change floatDecode x.val = 0 at hx
  have hm := map_finiteFloatSem_bin .add x y
  rw [hrun] at hm
  have hraw : checkedFloatSem.bin () .add x.val y.val = some z.val := hm.symm
  have heq := ((bin_checkedFloatSem_eq_some_iff .add x.val y.val z.val).mp hraw).2.2.2
  have hz : z.val = x.val + y.val := congrArg Float.ofModel heq
  have hf : (x.val + y.val).isFinite = true := by rw [← hz]; exact z.property
  obtain ⟨hr, hv⟩ := native_pack_value (x := x.val + y.val)
    (add_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)) rfl hf
  have hn := isNearestFloat_toReal_add _ _ (native_canonical x.val) (native_canonical y.val) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, hx, zero_add] at hn
  have hrepr : Float.Model.BinaryRounding.IsBinaryFloat Format.binary64.mantissaBits
      Format.binary64.minExponent (floatDecode y.val) := by
    rw [floatDecode_eq_toReal]
    exact isBinaryFloat_toReal (native_canonical y.val)
  have hfix := hn.eq_of_isBinaryFloat hrepr
  change floatDecode z.val = floatDecode y.val
  rw [hz, hv, hfix]


/-- Finite binary64 arithmetic satisfies the existing scalar arithmetic contract with relative
allowance $2^{-53}$ and absolute underflow allowance $2^{-1075}$. Every exact arithmetic result
within the largest finite magnitude succeeds, with a nonzero divisor for division. The absolute
allowance is conservative for addition and subtraction, which need no underflow term.

This is proved from Lean core's logical `Float.Model`, including bounded exponents and gradual
underflow. It certifies the checked interpreter on finite words, not the correctness or physical
cost of native runtime replacements. Only the zero literal is required by this arithmetic
contract; arbitrary rational-literal conversion is a separate obligation.
[Higham2002, §2.2]. -/
theorem isArithErrSem_finiteFloatSem :
    IsArithErrSem
      (fun _ _ => AbsRelErr Format.binary64.unitRoundoff Format.binary64.underflowBound)
      (fun _ (x : FiniteFloat) => floatDecode x.val)
      (fun _ a => |a| ≤ Format.binary64.maxFinite) finiteFloatSem := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p b x y z hb hrun
    cases p
    exact finiteFloatSem_bin_error b x y z hb hrun
  · intro p b x y hb hdiv hs
    cases p
    exact finiteFloatSem_bin_exists b x y hb hdiv hs
  · intro p
    cases p
    exact finiteFloatSem_zero
  · intro p x
    cases p
    exact finiteFloatSem_neg x
  · intro p x
    cases p
    exact finiteFloatSem_conj x

/-- The finite binary64 interpreter does not implement exact floor conversion to a natural
index: its conversion fails even on the exact zero literal. Arithmetic range and accuracy
certificates do not imply dynamic-index support. No printed source. -/
theorem not_isExactToNat_finiteFloatSem :
    ¬ IsExactToNat (fun _ (x : FiniteFloat) => floatDecode x.val) finiteFloatSem := by
  intro h
  obtain ⟨z, _, hd⟩ := isArithErrSem_finiteFloatSem.lit_zero ()
  have ht := h () z
  change none = (if 0 ≤ floatDecode z.val then some ⌊floatDecode z.val⌋₊ else none) at ht
  rw [hd] at ht
  norm_num at ht
  cases ht

/-- A one-column, one-coordinate oracle computing twice its input by checked finite binary64
addition. Other shapes are rejected. Overflow is execution failure. This executable oracle
is a concrete consumer of the input-domain matvec contract. No printed source. -/
def finiteFloatDoubleOracle (cols : ℕ) (X : Array FiniteFloat) : Option (Array FiniteFloat) :=
  if h : cols = 1 ∧ X.size = 1 then
    (finiteFloatSem.bin () .add (X[0]'(by omega)) (X[0]'(by omega))).map fun z => #[z]
  else none

/-- Checked binary64 doubling satisfies the input-domain matvec contract for the matrix
$[2]$ on $\lvert 2x\rvert\le M$, with $M$ the largest finite magnitude, coefficient $2u$
and absolute allowance $\eta$, where $u=2^{-53}$ and $\eta=2^{-1075}$.
The certificate proves success from
the input bound; it assumes no observed intermediate finiteness. No printed source. -/
theorem isMatvecErrOn_finiteFloatDoubleOracle {ι C : Type}
    (I : Interp Unit ι FiniteFloat C) (o : ι) (hh : I.height o = 1)
    (ho : I.oracle o = finiteFloatDoubleOracle) :
    IsMatvecErrOn I o (fun _ x => floatDecode x.val) ()
      (fun (_ _ : Fin 1) => (2 : ℝ))
      (fun x => |2 * x 0| ≤ Format.binary64.maxFinite)
      (2 * Format.binary64.unitRoundoff) Format.binary64.underflowBound := by
  refine ⟨hh, fun X hX hx => ?_⟩
  let x := X[0]'(by omega)
  have hs : |BinOp.add.realOp (floatDecode x.val) (floatDecode x.val)| ≤
      Format.binary64.maxFinite := by
    simpa only [BinOp.realOp, ← two_mul, x, Fin.val_zero] using hx
  obtain ⟨z, hz⟩ := isArithErrSem_finiteFloatSem.bin_ok () .add x x trivial
    (fun h => nomatch h) hs
  have he := isArithErrSem_finiteFloatSem.bin_err () .add x x z trivial hz
  refine ⟨#[z], rfl, ?_, ?_⟩
  · rw [ho]
    simp only [finiteFloatDoubleOracle, hX, and_self, ↓reduceDIte, x, hz, Option.map_some]
  · have hn (v : Fin 1 → ℝ) : ‖WithLp.toLp 2 v‖ = |v 0| := by
      rw [EuclideanSpace.norm_eq]
      simp only [Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
    rw [hn, hn]
    simpa [AbsRelErr, Matrix.mulVec, dotProduct, x, BinOp.realOp, abs_mul, mul_assoc, mul_left_comm,
      ← two_mul] using he

/-- The checked finite binary64 doubling oracle executes a stored matvec from a readable
source into a disjoint writable destination whenever $\lvert 2x\rvert\le M$.
Its returned word is the actual block write and has error at most $2u\lvert x\rvert+\eta$.
This is a finite-format execution
endpoint for one oracle call, not a complete Krylov solver. No printed source. -/
theorem exec_apply_of_finiteFloatDoubleOracle {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (o : ι) (hh : I.height o = 1)
    (ho : I.oracle o = finiteFloatDoubleOracle) (st : St Unit FiniteFloat C)
    (src dst : ℕ) (sOff dOff : IExp ℕ) (hne : dst ≠ src) (x : Fin 1 → ℝ)
    (hx : |2 * x 0| ≤ Format.binary64.maxFinite)
    (hr : ∀ i : Fin 1, ∃ w, st.store.read () src (sOff.eval + i) = some w ∧
      floatDecode w.val = x i)
    (hw : ∀ i < 1, ∃ len, st.store.shape[dst]? = some ((), len) ∧ dOff.eval + i < len) :
    ∃ (out : St Unit FiniteFloat C) (W : Fin 1 → FiniteFloat),
      exec I (.apply o () dst dOff src sOff 1) st = some out ∧
      st.store.writeBlock () dst dOff.eval (Array.ofFn W) = some out.store ∧
      ‖WithLp.toLp 2 ((fun (_ _ : Fin 1) => (2 : ℝ)) *ᵥ x -
        fun i : Fin 1 => floatDecode (W i).val)‖ ≤
          (2 * Format.binary64.unitRoundoff) * ‖WithLp.toLp 2 x‖ +
            Format.binary64.underflowBound :=
  (isMatvecErrOn_finiteFloatDoubleOracle I o hh ho).exec_apply
    st src dst sOff dOff hne x hx hr hw

private theorem exists_unpack_eq_zero_of_floatDecode_eq_zero (x : FiniteFloat)
    (hx : floatDecode x.val = 0) :
    ∃ s, x.val.toModel.unpack = .zero s := by
  rw [floatDecode_eq_toReal] at hx
  have hxf : x.val.toModel.unpack.IsFinite := x.property
  cases hxm : x.val.toModel.unpack with
  | notANumber => simp only [hxm, UnpackedFloat.IsFinite, UnpackedFloat.isFinite,
      Bool.false_eq_true] at hxf
  | infinity s => simp only [hxm, UnpackedFloat.IsFinite, UnpackedFloat.isFinite,
      Bool.false_eq_true] at hxf
  | zero s => exact ⟨s, rfl⟩
  | finite s m e hm =>
    exfalso
    rw [hxm, toReal] at hx
    have hn : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    have hp : (2 : ℝ) ^ e ≠ 0 := ne_of_gt (zpow_pos two_pos e)
    cases s <;> simp only [Sign.toReal] at hx <;>
      exact (mul_ne_zero (mul_ne_zero (by norm_num) hn) hp) hx

/-- The checked finite binary64 equality comparison returns true for any two decoded zeros,
including either choice of signed-zero bit pattern. No printed source. -/
theorem cmp_eq_eq_some_true_finiteFloatSem_of_zero (x y : FiniteFloat)
    (hx : floatDecode x.val = 0) (hy : floatDecode y.val = 0) :
    finiteFloatSem.cmp () .eq x y = some true := by
  rw [cmp_finiteFloatSem]
  apply (cmp_checkedFloatSem_eq_some_iff .eq x.val y.val true).2
  refine ⟨x.property, y.property, ?_⟩
  obtain ⟨sx, hxm⟩ := exists_unpack_eq_zero_of_floatDecode_eq_zero x hx
  obtain ⟨sy, hym⟩ := exists_unpack_eq_zero_of_floatDecode_eq_zero y hy
  change true = x.val.toModel.unpack.beq y.val.toModel.unpack
  rw [hxm, hym]
  rfl

/-- The checked finite binary64 comparison with a decoded zero is true for every positive
decoded finite right operand, including positive subnormals and either signed zero on the left.
This certifies the positive-curvature comparison used by CG. No printed source. -/
theorem cmp_lt_eq_some_true_finiteFloatSem_of_zero_of_pos (x y : FiniteFloat)
    (hx : floatDecode x.val = 0) (hy : 0 < floatDecode y.val) :
    finiteFloatSem.cmp () .lt x y = some true := by
  rw [cmp_finiteFloatSem]
  apply (cmp_checkedFloatSem_eq_some_iff .lt x.val y.val true).2
  refine ⟨x.property, y.property, ?_⟩
  change true = decide (Float.lt x.val y.val = true)
  unfold Float.lt
  change true = decide ((decide (x.val.toModel.unpack.lt y.val.toModel.unpack = true)) = true)
  simp only [Bool.decide_eq_true]
  obtain ⟨sx, hxm⟩ := exists_unpack_eq_zero_of_floatDecode_eq_zero x hx
  rw [floatDecode_eq_toReal] at hy
  rw [hxm]
  cases hym : y.val.toModel.unpack with
  | notANumber => simp only [hym, toReal] at hy; linarith
  | infinity t => simp only [hym, toReal] at hy; linarith
  | zero t => simp only [hym, toReal] at hy; linarith
  | finite t m e hm =>
    cases t with
    | positive => rfl
    | negative =>
      rw [hym, toReal, Sign.toReal] at hy
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      have hp := zpow_pos (show (0 : ℝ) < 2 by norm_num) e
      nlinarith

/-- A one-column oracle for twice the identity in any dimension. Every coordinate is
computed by actual checked binary64 addition, and overflow causes failure. Dimension zero
returns the empty array. No printed source. -/
def finiteFloatVectorDoubleOracle (N cols : ℕ) (X : Array FiniteFloat) :
    Option (Array FiniteFloat) :=
  if cols = 1 ∧ X.size = N then X.mapM fun x => finiteFloatSem.bin () .add x x else none

/-- The checked binary64 vector-doubling oracle implements twice the identity on the
input domain $\lvert 2x_i\rvert\le M$ in every coordinate, where $M$ is the largest
finite magnitude. Its mixed Euclidean error is at most
$2u\|\mathbf{x}\|+\sqrt{N}\eta$, including dimension zero and subnormal inputs.
Success follows from decoded input ranges rather than observed intermediate values.
No printed source. -/
theorem isMatvecErrOn_finiteFloatVectorDoubleOracle {ι C : Type}
    (I : Interp Unit ι FiniteFloat C) (o : ι) (N : ℕ) (hh : I.height o = N)
    (ho : I.oracle o = finiteFloatVectorDoubleOracle N) :
    IsMatvecErrOn I o (fun _ x => floatDecode x.val) ()
      ((2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ))
      (fun x => ∀ i, |2 * x i| ≤ Format.binary64.maxFinite)
      (2 * Format.binary64.unitRoundoff) (Real.sqrt N * Format.binary64.underflowBound) := by
  classical
  refine ⟨hh, fun X hX hx => ?_⟩
  let f := fun x : FiniteFloat => finiteFloatSem.bin () .add x x
  have hok (x : FiniteFloat) (hm : x ∈ X) : ∃ z, f x = some z := by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hm
    apply isArithErrSem_finiteFloatSem.bin_ok () .add _ _ trivial (fun h => nomatch h)
    simpa only [BinOp.realOp, ← two_mul] using hx ⟨i, by omega⟩
  let g := fun x : FiniteFloat => if hm : x ∈ X then (hok x hm).choose else finiteFloatZero
  have hg (x : FiniteFloat) (hm : x ∈ X) : f x = some (g x) := by
    simpa only [g, dif_pos hm] using (hok x hm).choose_spec
  have hmap : X.mapM f = some (X.map g) := by
    rw [Array.mapM_eq_mapM_toList,
      List.mapM_eq_some_map _ (fun x hm => hg x (by simpa using hm))]
    change some ((X.toList.map g).toArray) = some (X.map g)
    rw [← Array.toList_map, Array.toArray_toList]
  refine ⟨X.map g, by simp only [Array.size_map, hX], ?_, ?_⟩
  · rw [ho]
    simp only [finiteFloatVectorDoubleOracle, hX, and_self, ↓reduceIte]
    exact hmap
  · have he (i : Fin N) : AbsRelErr Format.binary64.unitRoundoff
        Format.binary64.underflowBound
        (2 * floatDecode (X[i.val]'(by omega)).val)
        (floatDecode ((X.map g)[i.val]'(by simp only [Array.size_map]; omega)).val) := by
      have hr := hg (X[i.val]'(by omega)) (Array.getElem_mem (by omega))
      have he := isArithErrSem_finiteFloatSem.bin_err () .add _ _ _ trivial hr
      simpa only [f, Array.getElem_map, BinOp.realOp, ← two_mul] using he
    have he := AbsRelErr.norm_sub_le he (Format.unitRoundoff_nonneg .binary64)
      (Format.underflowBound_nonneg .binary64)
    let x : Fin N → ℝ := fun i => floatDecode (X[i.val]'(by omega)).val
    let z : Fin N → ℝ := fun i =>
      floatDecode ((X.map g)[i.val]'(by simp only [Array.size_map]; omega)).val
    change ‖WithLp.toLp 2 ((2 : ℝ) • x - z)‖ ≤
      Format.binary64.unitRoundoff * ‖WithLp.toLp 2 ((2 : ℝ) • x)‖ +
        Real.sqrt (Fintype.card (Fin N)) * Format.binary64.underflowBound at he
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Fintype.card_fin, x, z, mul_assoc, mul_left_comm] using he

end NLAlib.Computation
