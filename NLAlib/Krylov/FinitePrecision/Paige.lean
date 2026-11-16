/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.Recurrence

/-!
# Paige's loss-of-orthogonality bound

For a run `L : NLAlib.LanczosRun n k`, split the Gram matrix of the computed basis as
$\mathbf{V}_k^{\mathsf{T}}\mathbf{V}_k = \mathbf{I} + \mathbf{R}_k^{\mathsf{T}} + \mathbf{\Gamma}
+ \mathbf{R}_k$ with $\mathbf{R}_k$ strictly upper triangular and $\mathbf{\Gamma}$ diagonal. The
**Gram commutator**
$\mathbf{M}_k = \mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k
- (\mathbf{V}_k^{\mathsf{T}}\beta_k\mathbf{v}_{k+1})\mathbf{e}_k^{\mathsf{T}}$ is upper triangular
and, under $k\varepsilon \le 1/100$, of size $O(k^2\varepsilon\|\mathbf{H}\|_2)$,
although $\mathbf{R}_k$ itself need not be small.
In the quadratic form of an eigenvector of $\mathbf{T}_k$ the commutator vanishes, which gives
Paige's bound: a Ritz vector loses orthogonality to $\mathbf{v}_{k+1}$ only when its scalar
residual estimate $\beta_k\lvert y_k\rvert$ is small, that is, only after it has converged.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `eq:M-def`, `cor:gram-commutator`, `lem:gram-commutator`, `thm:paige`;
[Paige1980, (3.11)–(3.13)] for the bound under Paige's rounding model.

## Main definitions

* `NLAlib.LanczosRun.gramStrictUpper`, `NLAlib.LanczosRun.normSqDefect`: the strict upper
  triangle $\mathbf{R}_k$ and the diagonal defects $\mathbf{\Gamma}$ of the Gram matrix.
* `NLAlib.LanczosRun.gramCommutator`: the Gram commutator $\mathbf{M}_k$.
* `NLAlib.lanczosGramCommutatorFactor`: the factor <!-- value lanczosGramCommutatorFactor k -->
  $30k^2$ of its bound and of Paige's bound.

## Main results

* `NLAlib.LanczosRun.isUpperTriangular_gramCommutator`,
  `NLAlib.LanczosRun.gramCommutator_sub_transpose`,
  `NLAlib.LanczosRun.specNorm_gramCommutator_le`: the Gram commutator.
* `NLAlib.LanczosRun.abs_basis_mulVec_dotProduct_mul_abs_le`: Paige's bound.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- **The factor of the Gram commutator bound** of a finite-precision Lanczos run of $k$ steps
(`NLAlib.LanczosRun.specNorm_gramCommutator_le`, and Paige's bound
`NLAlib.LanczosRun.abs_basis_mulVec_dotProduct_mul_abs_le`):
the factor <!-- value lanczosGramCommutatorFactor k -->
$$30k^2 \,.$$
The maintainer's draft states the bound as $\lesssim_k \varepsilon\|\mathbf{A}\|_2$; its
formalization has the factor $3000k^3$. -/
noncomputable irreducible_def lanczosGramCommutatorFactor (k : ℕ) : ℝ := 30 * (k : ℝ) ^ 2

/-- The explicit value the documentation displays: the Gram commutator factor of $k$ steps is at
most <!-- value lanczosGramCommutatorFactor k -->$30k^2$ (at present an equality). -/
theorem lanczosGramCommutatorFactor_le (k : ℕ) :
    lanczosGramCommutatorFactor k ≤ 30 * (k : ℝ) ^ 2 := by
  rw [lanczosGramCommutatorFactor_def]

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The **strict upper triangle of the Gram matrix** of the computed basis:
$(\mathbf{R}_k)_{i,j} = \mathbf{v}_{i+1}^{\mathsf{T}}\mathbf{v}_{j+1}$ for $i < j$. -/
def gramStrictUpper : Matrix (Fin k) (Fin k) ℝ := L.toLanczosData.gramStrictUpper

/-- The **diagonal defects** of the Gram matrix of the computed basis:
$\gamma_i = \|\mathbf{v}_{i+1}\|^2 - 1$ (the paper's $g_{i+1}$). -/
noncomputable def normSqDefect (i : Fin k) : ℝ := L.toLanczosData.normSqDefect i

/-- The **Gram commutator**
$\mathbf{M}_k = \mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k
- (\mathbf{V}_k^{\mathsf{T}}\beta_k\mathbf{v}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}}$
(`eq:M-def` of the maintainer's draft). -/
noncomputable def gramCommutator : Matrix (Fin k) (Fin k) ℝ := L.toLanczosData.gramCommutator

/-- The Gram commutator is upper triangular. No printed source; the maintainer's draft,
`lem:gram-commutator`. -/
theorem isUpperTriangular_gramCommutator : L.gramCommutator.IsUpperTriangular :=
  L.toLanczosData.isUpperTriangular_gramCommutator

/-- The diagonal entries of the Gram commutator are differences of inner products of consecutive
vectors: $(\mathbf{M}_k)_{i,i} = \beta_i\mathbf{v}_i^{\mathsf{T}}\mathbf{v}_{i+1}
- \mathbf{v}_{i+1}^{\mathsf{T}}(\beta_{i+1}\mathbf{v}_{i+2})$. -/
theorem gramCommutator_apply_self (i : Fin k) :
    L.gramCommutator i i =
      L.β i * (L.v i ⬝ᵥ L.v ((i : ℕ) + 1)) - L.adjacentInner i :=
  L.toLanczosData.gramCommutator_apply_self i

/-- **The skew part of the Gram commutator** is given by the residual and the diagonal defects:
$$\mathbf{M}_k - \mathbf{M}_k^{\mathsf{T}} = \mathbf{V}_k^{\mathsf{T}}\mathbf{F}_k -
\mathbf{F}_k^{\mathsf{T}}\mathbf{V}_k -
(\mathbf{T}_k\mathbf{\Gamma} - \mathbf{\Gamma}\mathbf{T}_k),
\qquad \mathbf{\Gamma} = \operatorname{diag}(\|\mathbf{v}_{i+1}\|^2 - 1)_i \,.$$
No printed source; the maintainer's draft, `eq:generic-commutator`. -/
theorem gramCommutator_sub_transpose :
    L.gramCommutator - L.gramCommutatorᵀ =
      L.basisᵀ * L.residual - L.residualᵀ * L.basis -
        (L.tridiagonal * Matrix.diagonal L.normSqDefect -
          Matrix.diagonal L.normSqDefect * L.tridiagonal) :=
  L.toLanczosData.gramCommutator_sub_transpose


/-- The computed basis has Frobenius norm at most $(1 + \varepsilon/2)\sqrt{k}$. -/
theorem frobNorm_basis_le : frobNorm L.basis ≤ (1 + L.ε / 2) * Real.sqrt k := by
  have hε0 := L.ε_nonneg
  have hsq : frobNorm L.basis ^ 2 ≤ ((1 + L.ε / 2) * Real.sqrt k) ^ 2 := by
    rw [frobNorm_sq_eq_sum_col, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    calc ∑ j, ‖WithLp.toLp 2 (L.basis.col j)‖ ^ 2 ≤ ∑ _j : Fin k, (1 + L.ε / 2) ^ 2 :=
          Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (L.norm_v_le (j := (j : ℕ) + 1) j.2) 2
      _ = (1 + L.ε / 2) ^ 2 * k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq

/-- **The Gram commutator is small**
(assuming $k\varepsilon \le 1/100$): <!-- value lanczosGramCommutatorFactor k -->
$\|\mathbf{M}_k\|_2 \le 30k^2\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `cor:gram-commutator`, states
$\|\mathbf{M}_k\| \lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization: $3000k^3$); here the
strict upper part is bounded in the Frobenius norm by that of
`NLAlib.LanczosRun.gramCommutator_sub_transpose`, and the diagonal entry by entry, which saves a
factor $k$. [Paige1976, (22)]; [Paige1980, (2.17)–(2.18)].
Result: lanczos-gram-commutator -/
theorem specNorm_gramCommutator_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) :
    specNorm L.gramCommutator ≤ lanczosGramCommutatorFactor k * L.ε * specNorm L.H := by
  rw [lanczosGramCommutatorFactor_def]
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  have ha : ∀ j < k, |L.toLanczosData.adjacentInner j| ≤ 7 * k * L.ε * specNorm L.H :=
    fun j hj => (L.abs_adjacentInner_le hsmall hj).trans (by
      rw [lanczosAdjacentInnerFactor_def]
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
      gcongr)
  have hb : ∀ j < k, |L.toLanczosData.β j| ≤ 5 / 4 * k * specNorm L.H := fun j hj => by
    change |L.β j| ≤ _
    rw [abs_of_nonneg (L.β_nonneg j hj.le)]
    refine (L.β_le hsmall hj.le).trans ?_
    have : (j : ℝ) ≤ k := by exact_mod_cast hj.le
    gcongr
  have hg : ∀ i, |L.toLanczosData.normSqDefect i| ≤ L.ε := fun i =>
    L.abs_norm_v_sq_sub_one_le ((i : ℕ) + 1) (by omega) i.2
  have h := L.toLanczosData.specNorm_gramCommutator_le ha hb hg
  have hV := L.frobNorm_basis_le
  have hF := L.frobNorm_residual_le hsmall
  rw [lanczosResidualFactor_def] at hF
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  have hVF : frobNorm L.basis * frobNorm L.residual ≤
      201 / 200 * 6 * k ^ 2 * L.ε * specNorm L.H := by
    calc frobNorm L.basis * frobNorm L.residual
        ≤ ((1 + L.ε / 2) * Real.sqrt k) * (6 * k * Real.sqrt k * L.ε * specNorm L.H) := by
          gcongr
      _ = (1 + L.ε / 2) * 6 * (Real.sqrt k * Real.sqrt k) * k * L.ε * specNorm L.H := by ring
      _ ≤ 201 / 200 * 6 * k ^ 2 * L.ε * specNorm L.H := by
          rw [hsk]
          have : (1 + L.ε / 2) ≤ 201 / 200 := by linarith
          have h0 : 0 ≤ (k : ℝ) * k * L.ε * specNorm L.H := by positivity
          nlinarith
  change specNorm L.toLanczosData.gramCommutator ≤ _
  refine h.trans ?_
  change 2 * (7 * k * L.ε * specNorm L.H) + 2 * (frobNorm L.basis * frobNorm L.residual) +
    k * (5 / 4 * k * specNorm L.H * (2 * L.ε)) ≤ _
  have h0 : 0 ≤ L.ε * specNorm L.H := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ k ^ 2 by nlinarith) h0]

/-- **Paige's loss-of-orthogonality bound**
(assuming $k\varepsilon \le 1/100$): for a unit eigenpair
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$, $\|\mathbf{y}\| = 1$, of the computed tridiagonal
matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$
satisfies <!-- value lanczosGramCommutatorFactor k -->
$$\lvert\mathbf{x}^{\mathsf{T}}(\beta_k\mathbf{v}_{k+1})\rvert\,\lvert y_{k-1}\rvert
\le 30k^2\varepsilon\|\mathbf{H}\|_2$$
($y_{k-1}$ the last entry, indexed from $0$): orthogonality to $\mathbf{v}_{k+1}$ is lost only
along Ritz vectors whose residual estimate $\beta_k\lvert y_{k-1}\rvert$ is small.
No printed source; the maintainer's draft, `thm:paige`, states
$\lvert\mathbf{x}^{\mathsf{T}}\mathbf{v}_{k+1}\rvert\beta_k\lvert\mathbf{e}_k^{\mathsf{T}}
\mathbf{y}\rvert \lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization: $3000k^3$);
[Paige1980, (3.11)–(3.13)].
Result: paige-loss-of-orthogonality -/
theorem abs_basis_mulVec_dotProduct_mul_abs_le
    (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    |(L.basis *ᵥ y) ⬝ᵥ (L.β k • L.v (k + 1))| * |y L.lastIndex| ≤
      lanczosGramCommutatorFactor k * L.ε * specNorm L.H :=
  (L.toLanczosData.abs_basis_mulVec_dotProduct_mul_abs_le hy hy1).trans
    (L.specNorm_gramCommutator_le hsmall)

end LanczosRun

end NLAlib
