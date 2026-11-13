/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.BinaryFloat
public import NLAlib.Ops.Catalog.Scalar

/-!
# Binary-format quantization as an Ops arithmetic model

The mathematical real carrier stores the quantized values. A certified nearest-integer selector
fixes the tie policy. Mixed accuracy includes gradual
underflow; a separate representability theorem requires the finite-range condition. This
model does not claim a physical finite word encoding or a native arithmetic implementation.

## Main results

* `NLAlib.Ops.BinaryQuantized.mixedModel_machine`: the scalar arithmetic accuracy law.
* `NLAlib.Ops.BinaryQuantized.decode_lit_zero`: exact literal zero.
-/

@[expose] public section

namespace NLAlib.Ops.BinaryQuantized

open Computation

/-- Arithmetic rounds exact targets with the selected binary-format quantizer.
Negation and copying are exact, including on words supplied by the caller. -/
noncomputable def machine (fmt : Float.Model.Format) (r : ℝ → ℤ) : Machine ℝ where
  lit q := binaryFloatRound fmt r q
  add a b := binaryFloatRound fmt r (a + b)
  sub a b := binaryFloatRound fmt r (a - b)
  mul a b := binaryFloatRound fmt r (a * b)
  div a b := binaryFloatRound fmt r (a / b)
  neg a := -a
  sqrt a := binaryFloatRound fmt r (Real.sqrt a)

/-- The quantizer gives mixed arithmetic error, with a largest-finite-result range.
The selector law is a scalar rounding property, independent of any algorithm execution. -/
theorem mixedModel_machine (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) :
    MixedModel ((2 : ℝ)⁻¹ ^ fmt.mantissaBits) ((2 : ℝ) ^ fmt.minExponent / 2)
      id (machine fmt r) (fun x => |x| ≤ fmt.maxFinite) where
  roundoff_nonneg := by positivity
  absolute_nonneg := by positivity
  lit q _ := by
    simpa only [machine, id_eq, AbsRelErr, abs_sub_comm] using
      absRelErr_binaryFloatRound fmt hr (q : ℝ)
  add a b _ := by
    simpa only [machine, id_eq, AbsRelErr, abs_sub_comm] using
      absRelErr_binaryFloatRound fmt hr (a + b)
  sub a b _ := by
    simpa only [machine, id_eq, AbsRelErr, abs_sub_comm] using
      absRelErr_binaryFloatRound fmt hr (a - b)
  mul a b _ := by
    simpa only [machine, id_eq, AbsRelErr, abs_sub_comm] using
      absRelErr_binaryFloatRound fmt hr (a * b)
  div a b _ _ := by
    simpa only [machine, id_eq, AbsRelErr, abs_sub_comm] using
      absRelErr_binaryFloatRound fmt hr (a / b)
  neg _ := rfl
  sqrt a _ _ := by
    simpa only [machine, id_eq, AbsRelErr, abs_sub_comm,
      abs_of_nonneg (Real.sqrt_nonneg a)] using
      absRelErr_binaryFloatRound fmt hr (Real.sqrt a)

/-- Every certified nearest tie policy rounds literal zero to exactly zero. -/
theorem decode_lit_zero (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) : (machine fmt r).lit 0 = 0 := by
  simpa only [machine, Rat.cast_zero] using binaryFloatRound_zero fmt hr

end NLAlib.Ops.BinaryQuantized
