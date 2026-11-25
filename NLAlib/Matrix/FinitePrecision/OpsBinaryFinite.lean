/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.BinaryFloatCarrier
public import NLAlib.Ops.Catalog.GuardedScalar

/-!
# Rejecting binary quantization on a finite word carrier

Words are the existing finite type of represented values. The total machine uses zero as
a default outside the representable exact-result range. Its guarded scalar functions reject
that range before returning any default. Thus the actual guarded interpretation uses the
optional bounded quantizer, including gradual underflow and the declared nearest tie policy.
This is a mathematical finite-value model, without a claim about native IEEE arithmetic.

## Main results

* `NLAlib.Ops.BinaryFinite.guarded_round_eq_quantize`: rejection matches bounded quantization.
* `NLAlib.Ops.BinaryFinite.mixedModel_machine`: mixed error on the finite word carrier.
* `NLAlib.Ops.BinaryFinite.decode_lit_zero`: the zero literal is exact.
-/

@[expose] public section

namespace NLAlib.Ops.BinaryFinite

open Computation

variable (fmt : Float.Model.Format) (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
  (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ))

/-- The represented zero word supplies the default used outside the accepted range. -/
def zero : BinaryFloat fmt := ⟨0, isBinaryRep_zero fmt he⟩

/-- Totalize the bounded quantizer with a represented zero. The guarded interpretation
rejects an out-of-range target before this default can become an arithmetic output. -/
noncomputable def round (x : ℝ) : BinaryFloat fmt :=
  (binaryFloatQuantize fmt he r hr x).getD (zero fmt he)

/-- The decoded totalized word equals the original rounding whenever quantization is in range. -/
theorem round_val_of_abs_le {x : ℝ} (hx : |x| ≤ fmt.maxFinite) :
    (round fmt he r hr x).val = binaryFloatRound fmt r x := by
  obtain ⟨w, hw⟩ := exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hx
  simp only [round, hw, Option.getD_some]
  exact val_eq_binaryFloatRound_of_binaryFloatQuantize hw

open Classical in
/-- The optional output of the guarded totalization is exactly the bounded quantizer.
In particular, out-of-range targets produce no word rather than the default zero. -/
theorem guarded_round_eq_quantize (x : ℝ) :
    (if |x| ≤ fmt.maxFinite then some (round fmt he r hr x) else none) =
      binaryFloatQuantize fmt he r hr x := by
  by_cases hx : |x| ≤ fmt.maxFinite
  · obtain ⟨w, hw⟩ := exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hx
    simp only [hx, ite_true, round, hw, Option.getD_some]
  · simp only [hx, ite_false, binaryFloatQuantize, ↓reduceDIte]

/-- Scalar word functions on the finite represented-value carrier. Copying is the ordinary
scalar copy; negation preserves representability. Range rejection is supplied by guardedFn. -/
noncomputable def machine : Machine (BinaryFloat fmt) where
  lit q := round fmt he r hr q
  add a b := round fmt he r hr (a.val + b.val)
  sub a b := round fmt he r hr (a.val - b.val)
  mul a b := round fmt he r hr (a.val * b.val)
  div a b := round fmt he r hr (a.val / b.val)
  neg a := ⟨-a.val, a.property.neg⟩
  sqrt a := round fmt he r hr (Real.sqrt a.val)

/-- Every in-range scalar target satisfies the existing mixed arithmetic model, on a finite
word type. The absolute allowance is half the least subnormal spacing. -/
theorem mixedModel_machine :
    MixedModel ((2 : ℝ)⁻¹ ^ fmt.mantissaBits) ((2 : ℝ) ^ fmt.minExponent / 2)
      Subtype.val (machine fmt he r hr) (fun x => |x| ≤ fmt.maxFinite) where
  roundoff_nonneg := by positivity
  absolute_nonneg := by positivity
  lit q hq := by
    change |(round fmt he r hr q).val - (q : ℝ)| ≤ _
    rw [round_val_of_abs_le fmt he r hr hq]
    simpa only [AbsRelErr, abs_sub_comm] using absRelErr_binaryFloatRound fmt hr (q : ℝ)
  add a b h := by
    change |(round fmt he r hr (a.val + b.val)).val - (a.val + b.val)| ≤ _
    rw [round_val_of_abs_le fmt he r hr h]
    simpa only [AbsRelErr, abs_sub_comm] using absRelErr_binaryFloatRound fmt hr (a.val + b.val)
  sub a b h := by
    change |(round fmt he r hr (a.val - b.val)).val - (a.val - b.val)| ≤ _
    rw [round_val_of_abs_le fmt he r hr h]
    simpa only [AbsRelErr, abs_sub_comm] using absRelErr_binaryFloatRound fmt hr (a.val - b.val)
  mul a b h := by
    change |(round fmt he r hr (a.val * b.val)).val - a.val * b.val| ≤ _
    rw [round_val_of_abs_le fmt he r hr h]
    simpa only [AbsRelErr, abs_sub_comm] using absRelErr_binaryFloatRound fmt hr (a.val * b.val)
  div a b _ h := by
    change |(round fmt he r hr (a.val / b.val)).val - a.val / b.val| ≤ _
    rw [round_val_of_abs_le fmt he r hr h]
    simpa only [AbsRelErr, abs_sub_comm] using absRelErr_binaryFloatRound fmt hr (a.val / b.val)
  neg _ := rfl
  sqrt a _ h := by
    change |(round fmt he r hr (Real.sqrt a.val)).val - Real.sqrt a.val| ≤ _
    rw [round_val_of_abs_le fmt he r hr h]
    simpa only [AbsRelErr, abs_sub_comm, abs_of_nonneg (Real.sqrt_nonneg a.val)] using
      absRelErr_binaryFloatRound fmt hr (Real.sqrt a.val)

/-- The zero literal is exact for every certified nearest tie policy. -/
theorem decode_lit_zero : ((machine fmt he r hr).lit 0).val = 0 := by
  have hzero : |(0 : ℝ)| ≤ fmt.maxFinite := (zero fmt he).property.abs_le
  have hv := round_val_of_abs_le fmt he r hr hzero
  rw [binaryFloatRound_zero fmt hr] at hv
  simpa only [machine, Rat.cast_zero] using hv

end NLAlib.Ops.BinaryFinite
