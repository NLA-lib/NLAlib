/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Frobenius

/-!
# Componentwise backward solutions of linear systems

A vector $\mathbf{x}$ is a componentwise backward solution of $\mathbf{M}\mathbf{x} = \mathbf{b}$
with the relative perturbation $\varepsilon$ and the diagonal floor $\sigma$ if
$(\mathbf{M} + \Delta)\mathbf{x} = \mathbf{b}$ for some $\Delta$ with
$\lvert\Delta_{ik}\rvert \le \varepsilon\lvert m_{ik}\rvert + \sigma[i = k]$. The residual of such
a solution is small in the Euclidean norm, and conversely a small residual in each row gives a
componentwise backward solution (the theorem of Oettli and Prager, [Higham2002, Theorem 7.3],
with a diagonal floor). The converse is how the rounding of a substitution is turned into a
backward error.

## Main definitions

* `NLAlib.IsComponentwiseBackwardSolution`: the backward solution predicate.

## Main results

* `NLAlib.IsComponentwiseBackwardSolution.norm_mulVec_sub_le`: the residual is at most
  $(\varepsilon\|\mathbf{M}\|_{\mathsf F} + \sigma)\|\mathbf{x}\|$.
* `NLAlib.isComponentwiseBackwardSolution_of_norm_sub_le`: a small residual in each row gives a
  backward solution (Oettli–Prager).
* `NLAlib.IsComponentwiseBackwardSolution.mono`: larger perturbations are weaker.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **A componentwise backward solution**: `x` solves $(\mathbf{M} + \Delta)\mathbf{x} = \mathbf{b}$
for a perturbation with $\lvert\Delta_{ik}\rvert \le \varepsilon\lvert m_{ik}\rvert$ off the
diagonal and $\lvert\Delta_{ii}\rvert \le \varepsilon\lvert m_{ii}\rvert + \sigma$ on it. -/
def IsComponentwiseBackwardSolution (ε σ : ℝ) (M : Matrix n n 𝕜) (b x : n → 𝕜) : Prop :=
  ∃ Δ : Matrix n n 𝕜, (∀ i k, ‖Δ i k‖ ≤ ε * ‖M i k‖ + if i = k then σ else 0) ∧
    (M + Δ) *ᵥ x = b

/-- **Larger perturbations are weaker**: a backward solution with $(\varepsilon, \sigma)$ is one
with any $\varepsilon' \ge \varepsilon$ and $\sigma' \ge \sigma$. -/
theorem IsComponentwiseBackwardSolution.mono {ε σ ε' σ' : ℝ} {M : Matrix n n 𝕜} {b x : n → 𝕜}
    (h : IsComponentwiseBackwardSolution ε σ M b x) (hε : ε ≤ ε') (hσ : σ ≤ σ') :
    IsComponentwiseBackwardSolution ε' σ' M b x := by
  sorry

/-- **The residual of a componentwise backward solution**: for $\varepsilon, \sigma \ge 0$,
$\|\mathbf{M}\mathbf{x} - \mathbf{b}\| \le (\varepsilon\|\mathbf{M}\|_{\mathsf F} + \sigma)
\|\mathbf{x}\|$ in the Euclidean norm. [Higham2002, Theorem 7.3] -/
theorem IsComponentwiseBackwardSolution.norm_mulVec_sub_le {ε σ : ℝ} {M : Matrix n n 𝕜}
    {b x : n → 𝕜} (h : IsComponentwiseBackwardSolution ε σ M b x) (hε : 0 ≤ ε) (hσ : 0 ≤ σ) :
    ‖WithLp.toLp 2 (M *ᵥ x - b)‖ ≤ (ε * frobNorm M + σ) * ‖WithLp.toLp 2 x‖ := by
  sorry

/-- **Oettli–Prager with a diagonal floor**: for $\varepsilon, \sigma \ge 0$, if every row of the
residual satisfies $\lvert(\mathbf{M}\mathbf{x} - \mathbf{b})_i\rvert \le
\varepsilon\sum_k\lvert m_{ik}\rvert\lvert x_k\rvert + \sigma\lvert x_i\rvert$, then `x` is a
componentwise backward solution of $\mathbf{M}\mathbf{x} = \mathbf{b}$ with
$(\varepsilon, \sigma)$. [Higham2002, Theorem 7.3] -/
theorem isComponentwiseBackwardSolution_of_norm_sub_le {ε σ : ℝ} {M : Matrix n n 𝕜}
    {b x : n → 𝕜} (hε : 0 ≤ ε) (hσ : 0 ≤ σ)
    (h : ∀ i, ‖(M *ᵥ x - b) i‖ ≤ ε * ∑ k, ‖M i k‖ * ‖x k‖ + σ * ‖x i‖) :
    IsComponentwiseBackwardSolution ε σ M b x := by
  sorry

end NLAlib
