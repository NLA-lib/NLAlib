/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Conditional Jensen's inequality on a convex set that is not closed

Mathlib's `ConcaveOn.condExp_map_le` proves `μ[φ ∘ f | m] ≤ φ ∘ μ[f | m]` for `φ` concave and
upper semicontinuous on a closed convex set `s`. Closedness serves only to put the conditional
mean of `f` in `s`; when the conditional mean is known to lie in `s` almost surely, the inequality
holds on any convex set on which `φ` is continuous. This is the form needed on the cone of
positive definite matrices, which is open (conditional Lieb,
`NLAlib/Probability/MatrixConcentration/ConditionalMGFBound.lean`). The conditional form of
`ConcaveOn.le_map_integral_of_integral_mem` (`NLAlib/ForMathlib/Analysis/Convex/Integral.lean`).
Upstream candidate for `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean`.

## Main results

* `ConcaveOn.condExp_map_le_of_condExp_mem`: conditional Jensen for a concave function, on a
  convex set containing the conditional mean.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

variable {Ω E : Type*} {m mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure Ω}

/-- **Conditional Jensen's inequality** `μ[φ ∘ f | m] ≤ φ ∘ μ[f | m]` almost everywhere, for `φ`
concave and continuous on a convex set `s` that need not be closed, provided `f` lies in `s` and
its conditional mean lies in `s` almost everywhere. Mathlib's `ConcaveOn.condExp_map_le` needs
`s` closed.
Port of the prototype lemma of the same name
(`NLAlib/ForMathlib/MeasureTheory/ConditionalJensen.lean`).
Proof: the closed hypograph argument of `ConcaveOn.le_map_integral_of_integral_mem`, with
Mathlib's `Convex.condExp_mem` for the pair `(f, φ ∘ f)` in the closure of the hypograph and
`ContinuousLinearMap.comp_condExp_comm` for its two coordinates; easy (the prototype proof is
about 20 lines). -/
theorem ConcaveOn.condExp_map_le_of_condExp_mem (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set E} {φ : E → ℝ} {f : Ω → E} (hφ : ConcaveOn ℝ s φ) (hφc : ContinuousOn φ s)
    (hfs : ∀ᵐ ω ∂μ, f ω ∈ s) (hf : Integrable f μ) (hφf : Integrable (fun ω => φ (f ω)) μ)
    (hmean : ∀ᵐ ω ∂μ, μ[f | m] ω ∈ s) :
    μ[fun ω => φ (f ω) | m] ≤ᵐ[μ] fun ω => φ (μ[f | m] ω) := by
  sorry
