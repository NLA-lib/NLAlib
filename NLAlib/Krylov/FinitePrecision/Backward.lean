/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.Normalized
public import NLAlib.Krylov.FinitePrecision.DilationEstimates

/-!
# A backward model for finite-precision Lanczos

The computed tridiagonal matrix of a run `L : NLAlib.LanczosRun n k` is exactly what $k$ steps of
exact Lanczos produce on a symmetric matrix $\tilde{\mathbf{H}}$ of dimension $n(k+1)$ that is
close to $\mathbf{I}_{k+1} \otimes \mathbf{H}$, from a starting vector whose spectral weights
with respect to $\mathbf{I}_{k+1} \otimes \mathbf{H}$ are those of the normalised
$\bar{\mathbf{v}}_1$ with respect to $\mathbf{H}$ (a Greenbaum-type backward model, with a
perturbation of order $k^3\varepsilon\|\mathbf{H}\|_2$ under the explicit horizon
$k\varepsilon \le 1/100$). The construction and exact reproduction need only local accuracy.

The construction: normalise the computed vectors (`NLAlib.LanczosRun.normalized`, whose local
errors have that polynomial bound under the same horizon); dilate them to orthonormal vectors
(`NLAlib.orthonormalDilation`), which satisfy the computed recurrence with the computed
coefficients up to a residual $\hat{\mathbf{E}}$ (`NLAlib.LanczosRun.dilatedResidual`),
controlled through the Gram commutator of the normalised vectors; remove the residual by the
symmetric perturbation
$\mathbf{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `sec:backward`, `lem:normalized-errors`, `cor:normalized-commutator`,
`lem:exchange`, `lem:dilated-recurrence`, `thm:greenbaum`; [Greenbaum1989] for the original
model (perturbation of order $\varepsilon^{1/4}$), [Paige2010] for the augmented model of
dimension $n + k$.

## Main definitions

* `NLAlib.LanczosRun.dilatedH`, `NLAlib.LanczosRun.dilatedBasisSucc`,
  `NLAlib.LanczosRun.dilatedBasis`, `NLAlib.LanczosRun.dilatedStart`,
  `NLAlib.LanczosRun.dilatedResidual`: the dilated recurrence.
* `NLAlib.LanczosRun.backwardPerturbation`, `NLAlib.LanczosRun.backwardH`: the backward model.
* `NLAlib.lanczosDilatedResidualFactor`, `NLAlib.lanczosBackwardFactor`: the factors of the
  two bounds: residual <!-- value lanczosDilatedResidualFactor k --> $280k^3$
  and backward <!-- value lanczosBackwardFactor k --> $400k^3$.

The construction and its exact properties are stated for any symmetric three-term datum with unit
vectors (`NLAlib.LanczosData.dilatedResidual`, `NLAlib.LanczosData.backwardH`,
`NLAlib.LanczosData.frobNorm_dilatedResidual_le_of_le`, with the recurrence residual and the
Gram commutator as inputs); the run versions are their instances for `L.normalized`.

## Main results

* `NLAlib.LanczosRun.frobNorm_dilatedResidual_le`: the dilated recurrence.
* `NLAlib.LanczosRun.backwardH_mul_dilatedBasis`,
  `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le`: the backward model.
* `NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`,
  `NLAlib.LanczosRun.lanczosAlpha_backwardH_dilatedStart`,
  `NLAlib.LanczosRun.lanczosState_backwardH_dilatedStart_succ_beta`: exact Lanczos on the model
  computes $\mathbf{T}_k$ and the coefficients.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- **The factor of the dilated residual bound** of a finite-precision Lanczos run of $k$ steps
(`NLAlib.LanczosRun.frobNorm_dilatedResidual_le`, Frobenius
norm): <!-- value lanczosDilatedResidualFactor k -->
$$280k^3 \,.$$
The maintainer's draft states the bound as $\lesssim_k \varepsilon\|\mathbf{A}\|_2$; its
formalization has the factor $240000k^6$, in the spectral norm. -/
noncomputable irreducible_def lanczosDilatedResidualFactor (k : ℕ) : ℝ := 280 * (k : ℝ) ^ 3

/-- **The factor of the backward perturbation** of a finite-precision Lanczos run of $k$ steps
(`NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le`, Frobenius norm), using the orthogonal
completion estimate: <!-- value lanczosBackwardFactor k -->
$$400k^3 \,.$$
The maintainer's draft states the bound as $\lesssim_k \varepsilon\|\mathbf{A}\|_2$; its
formalization has the factor $480000k^6$, in the spectral norm. -/
noncomputable irreducible_def lanczosBackwardFactor (k : ℕ) : ℝ := 400 * (k : ℝ) ^ 3

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-! ### The dilated recurrence

The constructions of `NLAlib.LanczosData` for the normalised run `L.normalized`, under the names
of the run. -/

/-- The **dilated matrix** $\hat{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H}$, block
diagonal with $k + 1$ copies of $\mathbf{H}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => L.H

/-- The **dilated vectors** $\hat{\mathbf{V}}_{k+1}$: the orthonormal dilation of the normalised
vectors $\bar{\mathbf{v}}_1, \dots, \bar{\mathbf{v}}_{k+1}$. -/
noncomputable def dilatedBasisSucc : Matrix (Fin n × Fin (k + 1)) (Fin (k + 1)) ℝ :=
  orthonormalDilation L.normalized.basisSucc

/-- The first $k$ dilated vectors $\hat{\mathbf{V}}_k$. -/
noncomputable def dilatedBasis : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  L.dilatedBasisSucc.submatrix id Fin.castSucc

/-- The **dilated starting vector** $(\bar{\mathbf{v}}_1, \mathbf{0}, \dots, \mathbf{0})$. -/
noncomputable def dilatedStart : Fin n × Fin (k + 1) → ℝ :=
  fun p => if (p.2 : ℕ) = 0 then L.normalizedV 1 p.1 else 0

/-- The tridiagonal matrix with the extra row, $\underline{\mathbf{T}}_k$
(`NLAlib.LanczosData.tridiagonalSucc` of the run). -/
def tridiagonalSucc : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  L.toLanczosData.tridiagonalSucc

/-- The **residual of the dilated recurrence**
$\hat{\mathbf{E}} = \hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}
\underline{\mathbf{T}}_k$. -/
noncomputable def dilatedResidual : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  L.dilatedH * L.dilatedBasis - L.dilatedBasisSucc * L.tridiagonalSucc

/-- The normalised vectors have unit length: the Gram matrix of $\bar{\mathbf{V}}_{k+1}$ has unit
diagonal. -/
theorem transpose_basisSucc_mul_self_apply (j : Fin (k + 1)) :
    (L.normalized.basisSuccᵀ * L.normalized.basisSucc) j j = 1 :=
  L.normalized.transpose_basisSucc_mul_self_apply_of_norm
    (fun _ h1 h2 => L.norm_normalizedV h1 h2) j

/-- **The dilated vectors are orthonormal**. No printed source; the maintainer's draft,
`lem:dilation`. -/
theorem hasOrthonormalCols_dilatedBasisSucc : HasOrthonormalCols L.dilatedBasisSucc :=
  L.normalized.hasOrthonormalCols_dilatedBasisSucc L.transpose_basisSucc_mul_self_apply

/-- The first dilated vector is the dilated starting vector. No printed source; the maintainer's
draft, `lem:dilation`. -/
theorem dilatedBasisSucc_col_zero : L.dilatedBasisSucc.col 0 = L.dilatedStart :=
  L.normalized.dilatedBasisSucc_col_zero

/-- The **exchange defect** $\mathbf{Y}_r = \underline{\mathbf{T}}_k\mathbf{K}_k^r -
\mathbf{K}^r\underline{\mathbf{T}}_k$ of the dilation ($\mathbf{K}_k$ the leading block of
$\mathbf{K}$), which measures how far $\mathbf{K}^r$ is from intertwining
$\underline{\mathbf{T}}_k$ (`lem:exchange` of the maintainer's draft). -/
noncomputable def exchangeDefect (r : ℕ) : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  L.tridiagonalSucc *
      (dilationK L.normalized.basisSucc ^ r).submatrix Fin.castSucc Fin.castSucc -
    dilationK L.normalized.basisSucc ^ r * L.tridiagonalSucc

/-- Block $r$ of the dilated residual:
$\hat{\mathbf{E}}_r = \bar{\mathbf{F}}_k(\mathbf{C}\mathbf{K}^r)_k
+ \bar{\mathbf{V}}_{k+1}(\mathbf{Y}_r - \mathbf{Y}_{r+1})$. -/
theorem dilatedResidual_submatrix (r : Fin (k + 1)) :
    L.dilatedResidual.submatrix (fun i => (i, r)) id =
      L.normalized.residual * (dilationC L.normalized.basisSucc *
          dilationK L.normalized.basisSucc ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc +
        L.normalized.basisSucc * (L.exchangeDefect r - L.exchangeDefect (r + 1)) :=
  L.normalized.dilatedResidual_submatrix r

/-- The exchange defects satisfy $\mathbf{Y}_{r+1} = \mathbf{Y}_r\mathbf{K}_k +
\mathbf{K}^r\mathbf{Y}_1$. -/
theorem exchangeDefect_succ (r : ℕ) :
    L.exchangeDefect (r + 1) =
      L.exchangeDefect r * (dilationK L.normalized.basisSucc).submatrix Fin.castSucc
          Fin.castSucc +
        dilationK L.normalized.basisSucc ^ r * L.exchangeDefect 1 :=
  L.normalized.exchangeDefect_succ r

/-- $\mathbf{Y}_0 = \mathbf{0}$. -/
theorem exchangeDefect_zero : L.exchangeDefect 0 = 0 :=
  L.normalized.exchangeDefect_zero

/-- **The exchange rule**: $\mathbf{Y}_1 = \mathbf{C}(\underline{\mathbf{T}}_k\mathbf{R}_k -
\mathbf{R}\underline{\mathbf{T}}_k)\mathbf{C}_k$. No printed source; the maintainer's draft,
`eq:L-commutator`; [Paige2010, (3.9)]. -/
theorem exchangeDefect_one :
    L.exchangeDefect 1 = dilationC L.normalized.basisSucc *
      (L.tridiagonalSucc * (strictUpperGram L.normalized.basisSucc).submatrix Fin.castSucc
          Fin.castSucc - strictUpperGram L.normalized.basisSucc * L.tridiagonalSucc) *
      (dilationC L.normalized.basisSucc).submatrix Fin.castSucc Fin.castSucc :=
  L.normalized.exchangeDefect_one

/-- The commutator of the normalised Gram matrix with $\underline{\mathbf{T}}_k$ is the
normalised Gram commutator with a zero last row:
$\underline{\mathbf{T}}_k\mathbf{R}_k - \mathbf{R}\underline{\mathbf{T}}_k =
\mathbf{J}\bar{\mathbf{M}}_k$, $\mathbf{J}$ the first $k$ columns of $\mathbf{I}_{k+1}$. -/
theorem tridiagonalSucc_mul_sub_eq :
    L.tridiagonalSucc * (strictUpperGram L.normalized.basisSucc).submatrix Fin.castSucc
        Fin.castSucc - strictUpperGram L.normalized.basisSucc * L.tridiagonalSucc =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id Fin.castSucc *
        L.normalized.gramCommutator :=
  L.normalized.tridiagonalSucc_mul_sub_eq

/-- The normalised basis with the next vector has Frobenius norm $\sqrt{k + 1}$. -/
theorem frobNorm_normalized_basisSucc :
    frobNorm L.normalized.basisSucc = Real.sqrt (k + 1) :=
  L.normalized.frobNorm_basisSucc_of_unit L.transpose_basisSucc_mul_self_apply

/-- **The exchange rule, bounds**
(assuming $k\varepsilon \le 1/100$): $\|\mathbf{Y}_1\|_2 \le 160k^2\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:exchange`. -/
theorem specNorm_exchangeDefect_one_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) :
    specNorm (L.exchangeDefect 1) ≤ 160 * k ^ 2 * L.ε * specNorm L.H := by
  have h := L.normalized.specNorm_exchangeDefect_one_le L.transpose_basisSucc_mul_self_apply
    (L.specNorm_normalized_gramCommutator_le hsmall)
  exact h.trans_eq (by ring)

/-- The exchange defects grow at most linearly: $\|\mathbf{Y}_r\|_2 \le r\|\mathbf{Y}_1\|_2$. -/
theorem specNorm_exchangeDefect_le (r : ℕ) :
    specNorm (L.exchangeDefect r) ≤ r * specNorm (L.exchangeDefect 1) :=
  L.normalized.specNorm_exchangeDefect_le L.transpose_basisSucc_mul_self_apply r

/-- **The dilated recurrence**
(assuming $k\varepsilon \le 1/100$) (the exchange rule and the dilated residual): the orthonormal
dilated vectors satisfy the computed recurrence with the computed coefficients up
to <!-- value lanczosDilatedResidualFactor k -->
$$\|\hat{\mathbf{E}}\|_{\mathsf{F}} =
\|\hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k\|_{\mathsf{F}}
\le 280k^3\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `lem:exchange` and `lem:dilated-recurrence`, state
$\lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization: $240000k^6$ in the spectral norm).
Result: lanczos-dilated-recurrence -/
theorem frobNorm_dilatedResidual_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) :
    frobNorm L.dilatedResidual ≤ lanczosDilatedResidualFactor k * L.ε * specNorm L.H := by
  rw [lanczosDilatedResidualFactor_def]
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  set A := L.ε * specNorm L.H with hA
  have hA0 : 0 ≤ A := by positivity
  have hE := L.normalized.frobNorm_dilatedResidual_le_of_frobNorm_gramCommutator_le
    L.transpose_basisSucc_mul_self_apply (L.frobNorm_normalized_residual_le hsmall)
    (L.frobNorm_normalized_gramCommutator_le hsmall)
  refine hE.trans ?_
  have hss : Real.sqrt (k + 1) * Real.sqrt k ≤ 3 / 2 * k := by
    rw [← Real.sqrt_mul (by positivity), Real.sqrt_le_left (by positivity)]
    nlinarith
  have heq : 2 * Real.sqrt (k + 1) * (12 * k * Real.sqrt k * L.ε * specNorm L.H) +
      (4 * k + 2) * (40 * k ^ 2 * L.ε * specNorm L.H) =
      (24 * k * (Real.sqrt (k + 1) * Real.sqrt k) +
        (4 * k + 2) * (40 * k ^ 2)) * A := by simp only [hA]; ring
  rw [heq]
  have hpoly : 24 * (k : ℝ) * (3 / 2 * k) + (4 * k + 2) * (40 * k ^ 2) ≤
      280 * (k : ℝ) ^ 3 := by
    have h3 : (k : ℝ) ^ 2 ≤ k ^ 3 := by nlinarith
    nlinarith
  calc _ ≤ (24 * k * (3 / 2 * k) + (4 * k + 2) * (40 * k ^ 2)) * A := by gcongr
    _ ≤ 280 * k ^ 3 * A := by gcongr
    _ = 280 * k ^ 3 * L.ε * specNorm L.H := by rw [hA]; ring

/-! ### The backward model -/

/-- The **backward perturbation**
$\mathbf{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$. -/
noncomputable def backwardPerturbation : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  -(L.dilatedResidual * L.dilatedBasisᵀ) -
    L.dilatedBasis * L.dilatedResidualᵀ * (1 - L.dilatedBasis * L.dilatedBasisᵀ)

/-- The **backward model** $\tilde{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H} +
\mathbf{\Delta}$. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  L.dilatedH + L.backwardPerturbation

/-- The backward model of the run is that of its normalised run. -/
theorem backwardH_eq_normalized_backwardH : L.backwardH = L.normalized.backwardH :=
  rfl

/-- The first $k$ dilated vectors are orthonormal. -/
theorem hasOrthonormalCols_dilatedBasis : HasOrthonormalCols L.dilatedBasis :=
  L.normalized.hasOrthonormalCols_dilatedBasis L.transpose_basisSucc_mul_self_apply

/-- $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k
= \mathbf{T}_k$. -/
theorem transpose_dilatedBasis_mul_dilatedBasisSucc_mul :
    L.dilatedBasisᵀ * (L.dilatedBasisSucc * L.tridiagonalSucc) = L.tridiagonal :=
  L.normalized.transpose_dilatedBasis_mul_dilatedBasisSucc_mul
    L.transpose_basisSucc_mul_self_apply

/-- $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}}$ is symmetric:
$\hat{\mathbf{E}}^{\mathsf{T}}\hat{\mathbf{V}}_k
= \hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}}$. -/
theorem transpose_dilatedResidual_mul_dilatedBasis :
    L.dilatedResidualᵀ * L.dilatedBasis = L.dilatedBasisᵀ * L.dilatedResidual :=
  L.normalized.transpose_dilatedResidual_mul_dilatedBasis L.transpose_basisSucc_mul_self_apply

/-- The backward model is symmetric. -/
theorem transpose_backwardH : L.backwardHᵀ = L.backwardH :=
  L.normalized.transpose_backwardH L.transpose_basisSucc_mul_self_apply

/-- **The backward model satisfies the computed recurrence exactly**:
$\tilde{\mathbf{H}}\hat{\mathbf{V}}_k = \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k$ with
$\hat{\mathbf{V}}_{k+1}$ orthonormal. No printed source; the maintainer's draft, `thm:greenbaum`. -/
theorem backwardH_mul_dilatedBasis :
    L.backwardH * L.dilatedBasis = L.dilatedBasisSucc * L.tridiagonalSucc :=
  L.normalized.backwardH_mul_dilatedBasis L.transpose_basisSucc_mul_self_apply

/-- **Greenbaum-type backward model for finite-precision Lanczos**
(assuming $k\varepsilon \le 1/100$): the symmetric backward model
$\tilde{\mathbf{H}}$ is close to $\mathbf{I}_{k+1} \otimes
\mathbf{H}$, <!-- value lanczosBackwardFactor k -->
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}
\le 400k^3\varepsilon\|\mathbf{H}\|_2 \,,$$
and it satisfies the computed recurrence exactly with orthonormal vectors
(`NLAlib.LanczosRun.backwardH_mul_dilatedBasis`), so exact Lanczos on it from the dilated
starting vector computes $\mathbf{T}_k$ and $\beta_k$
(`NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`).
No printed source; the maintainer's draft, `thm:greenbaum`, states
$\|\mathbf{\Delta}\|_2 \lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization:
$480000k^6$ in the spectral norm); the Frobenius norm here is at least the spectral norm.
[Greenbaum1989, (7.10)] has a perturbation of order $\varepsilon^{1/4}$.
Result: greenbaum-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) :
    frobNorm (L.backwardH - L.dilatedH) ≤ lanczosBackwardFactor k * L.ε * specNorm L.H := by
  have hE := L.frobNorm_dilatedResidual_le hsmall
  rw [lanczosDilatedResidualFactor_def] at hE
  rw [lanczosBackwardFactor_def]
  have h := L.normalized.frobNorm_backwardH_sub_dilatedH_le_sqrt_two_mul
    L.transpose_basisSucc_mul_self_apply
  change frobNorm (L.backwardH - L.dilatedH) ≤ Real.sqrt 2 * frobNorm L.dilatedResidual at h
  have hs : Real.sqrt (2 : ℝ) ≤ 10 / 7 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  calc _ ≤ Real.sqrt 2 * frobNorm L.dilatedResidual := h
    _ ≤ Real.sqrt 2 * (280 * k ^ 3 * L.ε * specNorm L.H) := by gcongr
    _ ≤ (10 / 7) * (280 * k ^ 3 * L.ε * specNorm L.H) := by
      have := L.ε_nonneg
      gcongr
    _ = _ := by ring

/-- The dilated vectors as a sequence: $\hat{\mathbf{u}}_m$ is column $m - 1$ of
$\hat{\mathbf{V}}_{k+1}$ for $1 \le m \le k + 1$, and $\mathbf{0}$ otherwise. -/
noncomputable def dilatedV (m : ℕ) : Fin n × Fin (k + 1) → ℝ :=
  fun p => if h : 1 ≤ m ∧ m ≤ k + 1 then L.dilatedBasisSucc p ⟨m - 1, by omega⟩ else 0

/-- **Exact Lanczos on the backward model computes the computed tridiagonal matrix**: $k$ steps
of the Lanczos recurrence on $\tilde{\mathbf{H}}$ from
$(\bar{\mathbf{v}}_1, \mathbf{0}, \dots, \mathbf{0})$ give $\mathbf{T}_k$.
No printed source; the maintainer's draft, `thm:greenbaum`. -/
theorem lanczosTridiagonal_backwardH_dilatedStart :
    lanczosTridiagonal L.backwardH L.dilatedStart k = L.tridiagonal :=
  LanczosData.lanczosTridiagonal_backwardH_dilatedStart (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos

/-- Exact Lanczos on the backward model computes the dilated vectors:
`lanczosMatrix` of $\tilde{\mathbf{H}}$ from the dilated start is $\hat{\mathbf{V}}_k$. -/
theorem lanczosMatrix_backwardH_dilatedStart :
    lanczosMatrix L.backwardH L.dilatedStart k = L.dilatedBasis :=
  LanczosData.lanczosMatrix_backwardH_dilatedStart (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos

/-- Exact Lanczos on the backward model computes the last coefficient: $\beta_k$ is the
coefficient of the state after $k$ steps. -/
theorem lanczosState_backwardH_dilatedStart_beta :
    (lanczosState L.backwardH L.dilatedStart k).beta = L.β k :=
  LanczosData.lanczosState_backwardH_dilatedStart_beta (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos

/-- Exact Lanczos on the backward model computes the computed diagonal coefficients: for
$j < k$, the coefficient $\alpha$ of step $j$ of the Lanczos recurrence on
$\tilde{\mathbf{H}}$ from the dilated start is $\alpha_{j+1}$. -/
theorem lanczosAlpha_backwardH_dilatedStart {j : ℕ} (hj : j < k) :
    lanczosAlpha L.backwardH (lanczosState L.backwardH L.dilatedStart j) = L.α (j + 1) :=
  LanczosData.lanczosAlpha_backwardH_dilatedStart (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos hj

/-- Exact Lanczos on the backward model computes the computed off-diagonal coefficients: for
$j < k$, the coefficient $\beta$ of the state after $j + 1$ steps of the Lanczos recurrence on
$\tilde{\mathbf{H}}$ from the dilated start is $\beta_{j+1}$. -/
theorem lanczosState_backwardH_dilatedStart_succ_beta {j : ℕ} (hj : j < k) :
    (lanczosState L.backwardH L.dilatedStart (j + 1)).beta = L.β (j + 1) :=
  LanczosData.lanczosState_backwardH_dilatedStart_succ_beta (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos hj

end LanczosRun

end NLAlib
