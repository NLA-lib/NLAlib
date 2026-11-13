/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Derivatives from continuous linear secants

Upstream candidate for Mathlib's Fréchet derivative API. A continuous family of exact
linear increment maps yields the derivative on the diagonal. This applies equally to a
function and to its derivative in operator norm.

## Main results

* `hasFDerivAt_of_continuous_secant`: continuity at the base point suffices.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If an exact increment is a continuously varying linear map applied to
the input increment, its value on the diagonal is the full Fréchet derivative. -/
theorem hasFDerivAt_of_continuous_secant {f : E → F} {L : E → E →L[𝕜] F} {x : E}
    (hL : ContinuousAt L x)
    (hsec : ∀ᶠ y in 𝓝 x, f y - f x = L y (y - x)) :
    HasFDerivAt f (L x) x := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hsmall : ∀ᶠ y in 𝓝 x, ‖L y - L x‖ < ε := by
    exact (hL.sub continuousAt_const).norm.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [hsec, hsmall] with y hy hsmall
  rw [hy, ← sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg _))
