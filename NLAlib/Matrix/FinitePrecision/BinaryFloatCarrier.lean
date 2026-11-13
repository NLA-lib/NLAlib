/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.BinaryFloat
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finite.Prod
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite represented-value carriers for binary formats

The carrier stores represented real values rather than native bit patterns. Quantization uses
an explicit nearest-integer selector and rejects exact values outside the finite range. These
are mathematical representation and quantizer results, with no program evaluator dependency.

## Main results

* `NLAlib.Computation.finite_binaryFloat` proves finite representability.
* `NLAlib.Computation.binaryFloatQuantize` is the optional bounded quantizer.
* `NLAlib.Computation.exists_binaryFloatQuantize_eq_some_of_abs_le` gives range success.
-/

@[expose] public section

namespace NLAlib.Computation

/-- The real values represented by a bounded binary format, including subnormal values.
This mathematical carrier has no separate signed zeros or nonfinite sentinel values. -/
abbrev BinaryFloat (fmt : Float.Model.Format) := {x : ℝ // IsBinaryRep fmt x}

/-- A bounded binary format has finitely many represented real values. This is a
representation theorem, independently of a native implementation or arithmetic cost. -/
theorem finite_binaryFloat (fmt : Float.Model.Format) : Finite (BinaryFloat fmt) := by
  have hfinite := ((Set.finite_Ioo (-(2 ^ fmt.mantissaBits : ℤ))
    (2 ^ fmt.mantissaBits)).prod (Set.finite_Icc fmt.minExponent
      ((2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
        fmt.mantissaBitsWithoutImplicit))).image
    (fun me : ℤ × ℤ => (me.1 : ℝ) * (2 : ℝ) ^ me.2)
  apply Set.Finite.to_subtype (hfinite.subset ?_)
  intro x hx
  obtain ⟨m, e, hm, hmin, hmax, hx⟩ := hx
  exact ⟨(m, e), ⟨abs_lt.mp hm, ⟨hmin, hmax⟩⟩, hx.symm⟩

/-- Round an in-range real value to the bounded binary format; reject an exact result
outside its finite interval. The represented output uses the supplied nearest tie policy. -/
noncomputable def binaryFloatQuantize (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (a : ℝ) : Option (BinaryFloat fmt) := by
  classical
  exact if h : |a| ≤ fmt.maxFinite then
    some ⟨binaryFloatRound fmt r a, isBinaryRep_binaryFloatRound fmt he hr h⟩
  else none

/-- Successful quantization returns the actual rounded input value. -/
theorem val_eq_binaryFloatRound_of_binaryFloatQuantize
    {fmt : Float.Model.Format} {he : 2 ≤ fmt.exponentBits} {r : ℝ → ℤ}
    {hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)} {a : ℝ} {w : BinaryFloat fmt}
    (h : binaryFloatQuantize fmt he r hr a = some w) : w.val = binaryFloatRound fmt r a := by
  unfold binaryFloatQuantize at h
  split_ifs at h
  · cases h
    rfl

/-- Every exact input in the finite interval can be rounded successfully. -/
theorem exists_binaryFloatQuantize_eq_some_of_abs_le (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) {a : ℝ}
    (ha : |a| ≤ fmt.maxFinite) : ∃ w, binaryFloatQuantize fmt he r hr a = some w := by
  exact ⟨⟨binaryFloatRound fmt r a, isBinaryRep_binaryFloatRound fmt he hr ha⟩,
    by simp only [binaryFloatQuantize, ha, ↓reduceDIte]⟩

end NLAlib.Computation
