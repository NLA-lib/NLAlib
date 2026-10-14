/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Integral

/-!
# Jensen's inequality on a convex set that is not closed

Mathlib's `ConcaveOn.le_map_integral` proves `∫ g ∘ f ≤ g (∫ f)` for `g` concave and continuous on
a closed convex set `s`. Closedness serves only to put the mean of `f` in `s`; when the mean is
known to lie in `s`, the inequality holds on any convex set. This is the form needed on the cone of
positive definite matrices, which is open. Upstream candidate for
`Mathlib.Analysis.Convex.Integral`.

## Main results

* `ConcaveOn.le_map_integral_of_integral_mem`: Jensen's inequality for a concave function, on a
  convex set containing the mean.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {s : Set E} {f : α → E} {g : E → ℝ}

/-- **Jensen's inequality** `∫ g ∘ f ≤ g (∫ f)` for `g` concave and continuous on a convex set `s`
that need not be closed, provided the mean of `f` lies in `s`. Mathlib's
`ConcaveOn.le_map_integral` needs `s` closed. Port of the prototype lemma of the same name. -/
theorem ConcaveOn.le_map_integral_of_integral_mem [IsProbabilityMeasure μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) (hm : ∫ x, f x ∂μ ∈ s) :
    ∫ x, g (f x) ∂μ ≤ g (∫ x, f x ∂μ) := by
  have hi : (∫ x, (f x, g (f x)) ∂μ) ∈ closure {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} :=
    hg.convex_hypograph.closure.integral_mem isClosed_closure
      (hfs.mono fun x hx => subset_closure ⟨hx, le_rfl⟩) (hfi.prodMk hgi)
  have hpair : ∫ x, (f x, g (f x)) ∂μ = (∫ x, f x ∂μ, ∫ x, g (f x) ∂μ) := integral_pair hfi hgi
  rw [hpair] at hi
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hi
  have hglim : Tendsto (fun k => g (u k).1) atTop (𝓝 (g (∫ x, f x ∂μ))) :=
    (hgc _ hm).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨(continuous_fst.tendsto _).comp hlim, Eventually.of_forall fun k => (hu k).1⟩)
  exact le_of_tendsto_of_tendsto' ((continuous_snd.tendsto _).comp hlim) hglim fun k => (hu k).2
