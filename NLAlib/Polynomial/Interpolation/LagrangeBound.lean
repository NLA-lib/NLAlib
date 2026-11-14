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

/-- A quotient with numerator at most $u$ and denominator at least $\Delta u$ in absolute
value is at most $\Delta^{-1}$, also when $u = 0$ (then the numerator vanishes). -/
private theorem abs_inv_mul_le_inv {Δ u N D : ℝ} (hΔ : 0 < Δ) (hN : |N| ≤ u)
    (hD : Δ * u ≤ |D|) : |D⁻¹ * N| ≤ Δ⁻¹ := by
  have hu : 0 ≤ u := (abs_nonneg N).trans hN
  rcases hu.eq_or_lt with h | h
  · have hN0 : N = 0 := abs_eq_zero.mp (le_antisymm (h ▸ hN) (abs_nonneg N))
    rw [hN0, mul_zero, abs_zero]
    exact (inv_pos.mpr hΔ).le
  · have hDpos : 0 < |D| := (mul_pos hΔ h).trans_le hD
    rw [abs_mul, abs_inv, inv_mul_le_iff₀ hDpos]
    calc |N| ≤ u := hN
      _ = Δ * u * Δ⁻¹ := by field_simp
      _ ≤ |D| * Δ⁻¹ := mul_le_mul_of_nonneg_right hD (inv_pos.mpr hΔ).le

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
  have hv0 : ∀ k, 0 ≤ v k := fun k => hx0.trans (hx k)
  have hstep : ∀ a b : Fin t, (a : ℕ) + 1 = b → v b ≤ v a := fun a b h =>
    (hgap a b h).trans (by nlinarith [hv0 a])
  have hanti : ∀ d : ℕ, ∀ a b : Fin t, (a : ℕ) + d = b → v b ≤ v a := by
    intro d
    induction d with
    | zero =>
      intro a b h
      rw [Fin.ext (a := a) (b := b) (by omega)]
    | succ d ih =>
      intro a b h
      have hc : (a : ℕ) + d < t := by omega
      exact (hstep ⟨a + d, hc⟩ b (by simp only; omega)).trans (ih a ⟨a + d, hc⟩ rfl)
  have hlt : ∀ a b : Fin t, a < b → Δ * v a ≤ v a - v b := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hc : (a : ℕ) + 1 < t := by omega
    have h1 := hgap a ⟨a + 1, hc⟩ rfl
    have h2 := hanti (b - (a + 1)) ⟨a + 1, hc⟩ b (by simp only; omega)
    linarith
  have hfac : ∀ k ∈ Finset.univ.erase i, |(v i - v k)⁻¹ * (x - v k)| ≤ Δ⁻¹ := by
    intro k hk
    have hN : |x - v k| ≤ v k := abs_le.mpr ⟨by linarith, by linarith [hx k, hv0 k]⟩
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with h | h
    · refine abs_inv_mul_le_inv hΔ hN ?_
      rw [abs_sub_comm]
      exact (hlt k i h).trans (le_abs_self _)
    · have hik : (i : ℕ) < k := h
      exact abs_inv_mul_le_inv hΔ (hN.trans (hanti (k - i) i k (by omega)))
        ((hlt i k h).trans (le_abs_self _))
  rw [Lagrange.basis, Polynomial.eval_prod, Finset.abs_prod]
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  refine (Finset.prod_le_prod (fun k _ => abs_nonneg _) hfac).trans_eq ?_
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

end NLAlib
