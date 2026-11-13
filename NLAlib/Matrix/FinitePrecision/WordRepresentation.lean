/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.NativeFloat

/-!
# Represented real values as finite binary64 words

Core normalization fixes a represented real value. Its bounded exponent then ensures packing
produces a finite word with exactly that decoding. This bridge constructs a word without
passing through overflowing numerator and denominator conversions.

## Main results

* `NLAlib.Computation.IsBinaryRep.exists_finiteFloat`: an actual word with the represented value.
* `NLAlib.Computation.floatDecode_finiteFloatOfRep`: exact decoding of the selected word.
-/

@[expose] public section

namespace NLAlib.Computation

open Float.Model Float.Model.UnpackedFloat Float.Model.BinaryRounding

private local instance : Fact (2 ≤ Format.binary64.exponentBits) := ⟨by decide⟩

/-- Every bounded binary64 represented real value is the exact decoding of a finite logical
Float word. Normalization and packing supply the word; no numerical approximation is added. -/
theorem IsBinaryRep.exists_finiteFloat {x : ℝ} (h : IsBinaryRep .binary64 x) :
    ∃ z : FiniteFloat, floatDecode z.val = x := by
  have hbound := h.abs_le
  obtain ⟨m, e, hm, he, _, hx⟩ := h
  let r := UnpackedFloat.normalize .binary64 m e .positive
  have hc : IsCanonical .binary64 r := normalize_isCanonical m e .positive he
  have hf : r.IsFinite := isFinite_normalize m e .positive
  have hv : r.toReal = (m : ℝ) * 2 ^ e :=
    (isNearestFloat_toReal_normalize m e .positive he).eq_of_isBinaryFloat ⟨m, e, he, hm, rfl⟩
  have hp := unpack_pack_of_abs_toReal_le hc hf (by rw [hv, ← hx]; exact hbound)
  let z : Float := Float.ofModel (Float.Model.pack r)
  have hz : z.isFinite = true := by
    change (UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r)).isFinite = true
    rw [hp]
    exact hf
  refine ⟨⟨z, hz⟩, ?_⟩
  rw [floatDecode_eq_toReal]
  change (UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r)).toReal = x
  rw [hp, hv, ← hx]

/-- Select a finite logical word for an exactly represented real value. The supplied proof
only certifies representability; it does not assert anything about a program execution. -/
noncomputable def finiteFloatOfRep (x : ℝ) (h : IsBinaryRep .binary64 x) : FiniteFloat :=
  Classical.choose h.exists_finiteFloat

/-- The selected finite logical word decodes exactly to the represented real value. -/
theorem floatDecode_finiteFloatOfRep (x : ℝ) (h : IsBinaryRep .binary64 x) :
    floatDecode (finiteFloatOfRep x h).val = x :=
  Classical.choose_spec h.exists_finiteFloat

end NLAlib.Computation
