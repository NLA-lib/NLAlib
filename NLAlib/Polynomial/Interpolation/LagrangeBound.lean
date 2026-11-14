/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Lagrange basis polynomials on relatively separated nodes

For real nodes $\lambda_0 > \lambda_1 > \dots > \lambda_{t-1}$ with relative gaps at least
$\Delta$, $\lambda_{k+1} \le (1 - \Delta)\lambda_k$, the Lagrange basis polynomials
$\ell_i(x) = \prod_{k \ne i}(x - \lambda_k)/(\lambda_i - \lambda_k)$
(Mathlib's `Lagrange.basis Finset.univ v i`) are at most $\Delta^{-(t-1)}$ in absolute value
below the nodes, on $0 \le x \le \lambda_{t-1}$: each of the $t - 1$ factors is at most
$\Delta^{-1}$. This is the conditioning factor of a Krylov–Vandermonde matrix on a spectrum with
a separated head, with the nodes the squared head singular values and $x$ a squared tail singular
value.

## Main results

* `NLAlib.abs_eval_basis_le_inv_pow`: $\lvert\ell_i(x)\rvert \le \Delta^{-(t-1)}$.
-/

@[expose] public section

open Polynomial

namespace NLAlib

/-- **Lagrange basis polynomials below relatively separated nodes**: let
$\lambda_0, \dots, \lambda_{t-1}$ be real nodes with
$\lambda_{k+1} \le (1 - \Delta)\lambda_k$ for $k + 1 < t$ and some $\Delta > 0$, and let
$0 \le x \le \lambda_k$ for every $k$ (so the nodes are nonnegative and non-increasing, and
$x$ is at most the smallest). Then every Lagrange basis polynomial
$\ell_i(x) = \prod_{k \ne i}(x - \lambda_k)/(\lambda_i - \lambda_k)$ of the nodes has
$$\lvert\ell_i(x)\rvert \le \Delta^{-(t-1)}\,.$$
Each of the $t - 1$ factors is at most $\Delta^{-1}$: for $k < i$,
$\lvert x - \lambda_k\rvert \le \lambda_k$ and $\lambda_k - \lambda_i \ge \Delta\lambda_k$; for
$k > i$, $\lvert x - \lambda_k\rvert \le \lambda_{k-1}$ and
$\lambda_i - \lambda_k \ge \Delta\lambda_{k-1}$. Positivity of the nodes is not assumed: where
nodes coincide (necessarily at $0$) the division convention $a/0 = 0$ makes the factor vanish.
The exponent is in $\mathbb{N}$; for $t = 0$ there is no basis polynomial. -/
theorem abs_eval_basis_le_inv_pow {t : ℕ} {v : Fin t → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ i j : Fin t, (i : ℕ) + 1 = j → v j ≤ (1 - Δ) * v i) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : ∀ i, x ≤ v i) (i : Fin t) :
    |(Lagrange.basis Finset.univ v i).eval x| ≤ Δ⁻¹ ^ (t - 1) := by
  -- Unfold `Lagrange.basis` and `Lagrange.basisDivisor`: the value is
  -- `∏ k ∈ univ.erase i, (v i - v k)⁻¹ * (x - v k)` (`Polynomial.eval_prod`), so by
  -- `Finset.abs_prod` and `Finset.prod_le_pow_card` (with `Finset.card_erase_of_mem`,
  -- `Finset.card_univ`, `Fintype.card_fin`) it suffices that each factor is at most `Δ⁻¹`.
  -- From `hgap`, `hx0`, `hx`: `0 ≤ v k`, `v` is antitone, and `Δ * v a ≤ v a - v b` for `a < b`
  -- (induction on `b` from the consecutive case). For `k < i` use `|x - v k| ≤ v k` and
  -- `Δ * v k ≤ v k - v i`; for `i < k` use `|x - v k| ≤ v k ≤ v (k - 1)` and
  -- `Δ * v (k - 1) ≤ v i - v k`; if the lower bound of the denominator is `0` the numerator is.
  sorry

end NLAlib
