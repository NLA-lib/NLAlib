/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.NativeFloat
public import NLAlib.ForMathlib.Data.Float.Sqrt

/-!
# Native square roots of finite binary64 words

Core's packing and nearest-rounding theorems give a finite result and mixed error for every
finite nonnegative input. This is a theorem about the logical Float operation, without an
optional program evaluator or a guarantee about runtime replacements.

## Main results

* `NLAlib.Computation.FiniteFloat.sqrt_spec`: finiteness, nonnegativity and mixed error.
-/

@[expose] public section

namespace NLAlib.Computation

open Float.Model Float.Model.UnpackedFloat Float.Model.BinaryRounding

private local instance : Fact (2 ≤ Format.binary64.exponentBits) := ⟨by decide⟩

private theorem one_le_maxFinite_binary64 : 1 ≤ Format.binary64.maxFinite := by
  unfold Format.maxFinite
  have hp : 1 ≤ (2 : ℝ) ^ Format.binary64.mantissaBits - 1 := by
    norm_num [Format.mantissaBits, Format.mantissaBitsWithoutImplicit, Format.binary64]
  have he : 1 ≤ (2 : ℝ) ^ Format.binary64.maxExponentBound :=
    one_le_zpow₀ (by norm_num) (by decide)
  exact one_le_mul_of_one_le_of_one_le hp he

private theorem unpack_pack_sqrt (x : FiniteFloat) (hx : 0 ≤ floatDecode x.val) :
    let r := UnpackedFloat.sqrt .binary64 x.val.toModel.unpack
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r) = r := by
  have ha : 0 ≤ x.val.toModel.unpack.toReal := by rwa [← floatDecode_eq_toReal]
  have hroot : Real.sqrt x.val.toModel.unpack.toReal ≤ Format.binary64.maxFinite := by
    apply (Real.sqrt_le_iff).2
    refine ⟨Format.binary64.maxFinite_pos.le, ?_⟩
    have hbound := (isBinaryRep_floatDecode x.val).abs_le
    rw [floatDecode_eq_toReal] at hbound
    have hm := one_le_maxFinite_binary64
    have hprod := mul_nonneg (Format.binary64.maxFinite_pos.le)
      (sub_nonneg.mpr hm)
    nlinarith [le_abs_self x.val.toModel.unpack.toReal]
  have hn := isNearestFloat_toReal_sqrt (spec := .binary64) _ x.property ha
  have hnonneg := toReal_sqrt_nonneg (spec := .binary64) _ x.property ha
  exact unpack_pack_of_abs_toReal_le (sqrt_isCanonical _) (isFinite_sqrt_of_nonneg _ x.property ha)
    (by
      rw [abs_of_nonneg hnonneg]
      exact hn.le_of_le (Format.isBinaryFloat_maxFinite .binary64) hroot)

/-- Native square root of a finite nonnegative word is finite and nonnegative, with
binary64 relative and gradual-underflow allowances. [Higham2002, §2.2]. -/
theorem FiniteFloat.sqrt_spec (x : FiniteFloat) (hx : 0 ≤ floatDecode x.val) :
    x.val.sqrt.isFinite = true ∧ 0 ≤ floatDecode x.val.sqrt ∧
      AbsRelErr Format.binary64.unitRoundoff Format.binary64.underflowBound
        (Real.sqrt (floatDecode x.val)) (floatDecode x.val.sqrt) := by
  have ha : 0 ≤ x.val.toModel.unpack.toReal := by rwa [← floatDecode_eq_toReal]
  have hpack := unpack_pack_sqrt x hx
  have hf : x.val.sqrt.isFinite = true := by
    change (UnpackedFloat.unpack .binary64
      (UnpackedFloat.pack .binary64 (UnpackedFloat.sqrt .binary64 x.val.toModel.unpack))).isFinite
        = true
    rw [hpack]
    exact isFinite_sqrt_of_nonneg _ x.property ha
  have hv : floatDecode x.val.sqrt =
      (UnpackedFloat.sqrt .binary64 x.val.toModel.unpack).toReal := by
    rw [floatDecode_eq_toReal]
    change (UnpackedFloat.unpack .binary64
      (UnpackedFloat.pack .binary64 (UnpackedFloat.sqrt .binary64 x.val.toModel.unpack))).toReal = _
    rw [hpack]
  refine ⟨hf, ?_, ?_⟩
  · rw [hv]
    exact toReal_sqrt_nonneg _ x.property ha
  · rw [hv, floatDecode_eq_toReal]
    simpa only [AbsRelErr, abs_sub_comm, abs_of_nonneg (Real.sqrt_nonneg _)] using
      abs_toReal_sqrt_sub_le (spec := .binary64)
        x.val.toModel.unpack (isFinite_sqrt_of_nonneg _ x.property ha)

end NLAlib.Computation
