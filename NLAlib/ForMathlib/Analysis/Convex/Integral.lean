/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import NLAlib.ForMathlib.Analysis.Convex.SupportingLine

/-!
# Jensen's inequality on a convex set that is not closed

Mathlib's `ConcaveOn.le_map_integral` proves $\int g \circ f \, d\mu
\le g\bigl(\int f \, d\mu\bigr)$ for $g$ concave and continuous on a closed convex set $s$.
Closedness serves only to put the mean of $f$ in $s$; when the mean is known to lie in $s$, the
inequality holds on any convex set. This is the form needed on the cone of positive definite
matrices, which is open. Upstream candidate for `Mathlib.Analysis.Convex.Integral`.

## Main results

* `ConcaveOn.le_map_integral_of_integral_mem`: Jensen's inequality for a concave function, on a
  convex set containing the mean.
* `HasSupportingLineOn.le_integral_comp`: Jensen's inequality for a function with a supporting line
  at the mean, convex or not.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {s : Set E} {f : α → E} {g : E → ℝ}

/-- **Jensen's inequality** $\int g(f(x)) \, d\mu(x) \le g\bigl(\int f(x) \, d\mu(x)\bigr)$ for a
probability measure $\mu$ and $g$ concave and continuous on a convex set $s$ that need not be
closed, provided $f$ takes values in $s$ almost everywhere, $f$ and $g \circ f$ are integrable,
and the mean of $f$ lies in $s$. Mathlib's `ConcaveOn.le_map_integral` needs $s$ closed.
[Vershynin2018, §1.2] gives the scalar convex form on the real line. -/
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


/-- **Jensen's inequality from a supporting line**: for a probability measure $\mu$, a real random
variable $X$ with values in $s$ almost everywhere, and $\varphi$ with a supporting line on $s$ at
the mean of $X$,
$$\varphi\Bigl(\int X \, d\mu\Bigr) \le \int \varphi(X) \, d\mu\,,$$
with no convexity assumed. [TroppWebber2023, Lemma 9.4], the scalar half of the almost-convex
Jensen inequality; there with $X$ a Gaussian functional. -/
theorem HasSupportingLineOn.le_integral_comp [IsProbabilityMeasure μ] {φ : ℝ → ℝ} {t : Set ℝ}
    {X : α → ℝ} (h : HasSupportingLineOn φ t (∫ ω, X ω ∂μ)) (hX : ∀ᵐ ω ∂μ, X ω ∈ t)
    (hi : Integrable X μ) (hφi : Integrable (φ ∘ X) μ) :
    φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ := by
  obtain ⟨c, hc⟩ := h
  set a := ∫ ω, X ω ∂μ
  have hs : Integrable (fun ω => c * (X ω - a)) μ := (hi.sub (integrable_const a)).const_mul c
  have hli : Integrable (fun ω => φ a + c * (X ω - a)) μ := (integrable_const _).add hs
  have hl : ∫ ω, (φ a + c * (X ω - a)) ∂μ = φ a := by
    rw [integral_add (integrable_const _) hs, integral_const_mul,
      integral_sub hi (integrable_const a)]
    simp [a]
  calc φ a = ∫ ω, (φ a + c * (X ω - a)) ∂μ := hl.symm
    _ ≤ ∫ ω, φ (X ω) ∂μ := integral_mono_ae hli hφi (hX.mono fun ω hω => hc _ hω)
