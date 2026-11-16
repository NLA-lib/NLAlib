/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LocalErrors
public import NLAlib.Matrix.Factorizations.Hessenberg
public import NLAlib.Matrix.Norms.Compare

/-!
# The perturbed Lanczos recurrence and Ritz residuals

The polynomial bounds below assume $k\varepsilon \le 1/100$ explicitly; the recurrence
identities need only local accuracy. The matrix form of the local error bounds of a run
`L : NLAlib.LanczosRun n k`: with the computed
basis $\mathbf{V}_k = [\mathbf{v}_1, \dots, \mathbf{v}_k]$ (`L.basis`, column $j$ is
$\mathbf{v}_{j+1}$), the computed tridiagonal matrix $\mathbf{T}_k$ (`L.tridiagonal`, entries
indexed from $0$ as `NLAlib.lanczosTridiagonal`) and the residual matrix $\mathbf{F}_k$ of the
recurrence,
$$\mathbf{H}\mathbf{V}_k = \mathbf{V}_k\mathbf{T}_k +
\beta_k\mathbf{v}_{k+1}\mathbf{e}_k^{\mathsf{T}} + \mathbf{F}_k,
\qquad \|\mathbf{F}_k\|_{\mathsf{F}} \le 6k^{3/2}\varepsilon\|\mathbf{H}\|_2 \,,$$
and its consequence for a Ritz pair $(\theta, \mathbf{V}_k\mathbf{y})$: the residual is the
scalar estimate $\beta_k\lvert y_k\rvert$ up to $O(\varepsilon\|\mathbf{H}\|_2)$.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `eq:governing`, `eq:ritz-residual-identity`, `eq:ritz-residual-bound`.

## Main definitions

* `NLAlib.LanczosRun.basis`, `NLAlib.LanczosRun.tridiagonal`, `NLAlib.LanczosRun.residual`,
  `NLAlib.LanczosRun.lastIndex`.
* `NLAlib.lanczosResidualFactor`: the factor <!-- value lanczosResidualFactor k --> $6k\sqrt{k}$
  of the residual bound.

## Main results

* `NLAlib.LanczosRun.mul_basis`: the perturbed recurrence.
* `NLAlib.LanczosRun.frobNorm_residual_le`, `NLAlib.LanczosRun.specNorm_residual_le`: its residual.
* `NLAlib.LanczosRun.mulVec_basis_mulVec_sub_smul`: the Ritz residual identity.
* `NLAlib.LanczosRun.norm_mulVec_basis_mulVec_sub_smul_le`: the Ritz residual bound.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- **The factor of the residual bound** of a finite-precision Lanczos run of $k$ steps
(`NLAlib.LanczosRun.frobNorm_residual_le`): <!-- value lanczosResidualFactor k -->
$$6k\sqrt{k} \,,$$
from $\sqrt{k}$ columns bounded by the local error factor at the last step. The maintainer's
draft has $\sqrt{k}\max_j\|\mathbf{f}_j\|$; its formalization has the factor $700k^2$. -/
noncomputable irreducible_def lanczosResidualFactor (k : ℕ) : ℝ := 6 * k * Real.sqrt k

/-- The explicit value the documentation displays: the residual factor of $k$ steps is at
most <!-- value lanczosResidualFactor k -->$6k\sqrt{k}$ (at present an equality). -/
theorem lanczosResidualFactor_le (k : ℕ) : lanczosResidualFactor k ≤ 6 * k * Real.sqrt k := by
  rw [lanczosResidualFactor_def]

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The **computed Lanczos basis** $\mathbf{V}_k$: column $j$ is $\mathbf{v}_{j+1}$. -/
def basis : Matrix (Fin n) (Fin k) ℝ := L.toLanczosData.basis

/-- The **computed tridiagonal matrix** $\mathbf{T}_k$, indexed from $0$:
$\alpha_{i+1}$ at $(i, i)$, and $\beta_i$ at $(i, i - 1)$ and $(i - 1, i)$. -/
def tridiagonal : Matrix (Fin k) (Fin k) ℝ := L.toLanczosData.tridiagonal

/-- The **residual matrix** $\mathbf{F}_k$ of the recurrence: column $j$ is
`NLAlib.LanczosRun.recurrenceError L j`. -/
noncomputable def residual : Matrix (Fin n) (Fin k) ℝ := L.toLanczosData.residual

/-- The index $k - 1$ of the last column, as an element of `Fin k` (a run has $k \ge 1$). -/
def lastIndex : Fin k := L.toLanczosData.lastIndex

/-- The computed tridiagonal matrix is symmetric. -/
theorem transpose_tridiagonal : L.tridiagonalᵀ = L.tridiagonal :=
  L.toLanczosData.transpose_tridiagonal

/-- The computed tridiagonal matrix is tridiagonal. -/
theorem isTridiagonal_tridiagonal : IsTridiagonal L.tridiagonal :=
  L.toLanczosData.isTridiagonal_tridiagonal

/-- **The perturbed Lanczos recurrence**: the computed basis satisfies
$$\mathbf{H}\mathbf{V}_k = \mathbf{V}_k\mathbf{T}_k +
(\beta_k\mathbf{v}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}} + \mathbf{F}_k$$
($\mathbf{e}_{k-1}$ the last coordinate vector, indexed from $0$), an identity of the
definitions. No printed source; the maintainer's draft, `eq:governing`, writes it as
$\mathbf{V}_{k+1}\underline{\mathbf{T}}_k + \mathbf{F}_k$. -/
theorem mul_basis :
    L.H * L.basis = L.basis * L.tridiagonal +
      Matrix.vecMulVec (L.β k • L.v (k + 1)) (Pi.single L.lastIndex 1) + L.residual :=
  L.toLanczosData.mul_basis

/-- **The residual of the perturbed recurrence is small**
(assuming $k\varepsilon \le 1/100$): <!-- value lanczosResidualFactor k -->
$\|\mathbf{F}_k\|_{\mathsf{F}} \le 6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, proof of `cor:gram-commutator`, uses
$\|\mathbf{F}_k\| \le \sqrt{k}\max_j\|\mathbf{f}_j\|$ (its formalization: $700k^2$). -/
theorem frobNorm_residual_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) :
    frobNorm L.residual ≤ lanczosResidualFactor k * L.ε * specNorm L.H := by
  rw [lanczosResidualFactor_def]
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hcol : ∀ j : Fin k, ‖WithLp.toLp 2 (L.residual.col j)‖ ≤ 6 * k * L.ε * specNorm L.H := by
    intro j
    have hjk : ((j : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast j.2
    refine (L.norm_recurrenceError_le hsmall j.2).trans ?_
    rw [lanczosRecurrenceErrorFactor_def]
    gcongr
  have hsq : frobNorm L.residual ^ 2 ≤ (6 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    calc ∑ j, ‖WithLp.toLp 2 (L.residual.col j)‖ ^ 2
        ≤ ∑ _j : Fin k, (6 * k * L.ε * specNorm L.H) ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcol j) 2
      _ = (6 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hs : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
          calc (k : ℝ) * (6 * k * L.ε * specNorm L.H) ^ 2
              = Real.sqrt (k : ℝ) ^ 2 * (6 * k * L.ε * specNorm L.H) ^ 2 := by rw [hs]
            _ = _ := by ring
  exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq

/-- **The residual of the perturbed recurrence is small**
(assuming $k\varepsilon \le 1/100$) in the spectral
norm: <!-- value lanczosResidualFactor k -->
$\|\mathbf{F}_k\|_2 \le 6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, proof of `cor:gram-commutator`. -/
theorem specNorm_residual_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) :
    specNorm L.residual ≤ lanczosResidualFactor k * L.ε * specNorm L.H :=
  (specNorm_le_frobNorm _).trans (L.frobNorm_residual_le hsmall)

/-- The last computed vector, scaled: $\|\beta_k\mathbf{v}_{k+1}\| \le
\sqrt{1 + \varepsilon}\,\beta_k$ ($\mathbf{v}_{k+1}$ is nearly unit when $\beta_k \neq 0$). -/
theorem norm_β_smul_v_le : ‖WithLp.toLp 2 (L.β k • L.v (k + 1))‖ ≤ Real.sqrt (1 + L.ε) * L.β k := by
  have hβ := L.β_nonneg k le_rfl
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ, mul_comm]
  rcases hβ.eq_or_lt with h | h
  · rw [← h, mul_zero, mul_zero]
  · gcongr
    apply Real.le_sqrt_of_sq_le
    have := (abs_le.mp (L.abs_norm_v_succ_sq_sub_one_le h.ne')).2
    linarith

/-- **The Ritz residual identity**: for an eigenpair $\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$
of the computed tridiagonal matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$
satisfies $(\mathbf{H} - \theta\mathbf{I})\mathbf{x} = y_{k-1}\,(\beta_k\mathbf{v}_{k+1})
+ \mathbf{F}_k\mathbf{y}$. No printed source; the maintainer's draft,
`eq:ritz-residual-identity`. -/
theorem mulVec_basis_mulVec_sub_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) :
    L.H *ᵥ (L.basis *ᵥ y) - θ • (L.basis *ᵥ y) =
      y L.lastIndex • (L.β k • L.v (k + 1)) + L.residual *ᵥ y :=
  L.toLanczosData.mulVec_basis_mulVec_sub_smul hy

/-- **The Ritz residual bound for finite-precision Lanczos**
(assuming $k\varepsilon \le 1/100$): for a unit eigenpair
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$, $\|\mathbf{y}\| = 1$, of the computed tridiagonal
matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$
satisfies <!-- value lanczosResidualFactor k -->
$$\|\mathbf{H}\mathbf{x} - \theta\mathbf{x}\|
\le \sqrt{1 + \varepsilon}\,\beta_k\lvert y_{k-1}\rvert +
6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `eq:ritz-residual-bound`, with
$\|\mathbf{F}_k\|$ for the last term and both sides divided by $\|\mathbf{x}\|$.
Result: lanczos-ritz-residual -/
theorem norm_mulVec_basis_mulVec_sub_smul_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100)
    {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    ‖WithLp.toLp 2 (L.H *ᵥ (L.basis *ᵥ y) - θ • (L.basis *ᵥ y))‖ ≤
      Real.sqrt (1 + L.ε) * L.β k * |y L.lastIndex| +
        lanczosResidualFactor k * L.ε * specNorm L.H := by
  rw [L.mulVec_basis_mulVec_sub_smul hy, WithLp.toLp_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, mul_comm]
    gcongr
    exact L.norm_β_smul_v_le
  · refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [hy1, mul_one]
    exact L.specNorm_residual_le hsmall

end LanczosRun

end NLAlib
