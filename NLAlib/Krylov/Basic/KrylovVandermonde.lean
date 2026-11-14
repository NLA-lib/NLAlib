/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde
public import NLAlib.Krylov.Basic.BlockSpace

/-!
# Krylov matrices of diagonalized pairs and Vandermonde matrices

The Krylov matrix of a diagonal matrix $\operatorname{diag}(\mathbf{d})$ and a vector
$\mathbf{g}$ is $\operatorname{diag}(\mathbf{g})\,\mathbf{V}$ with $\mathbf{V} = (d_i^{\,j})$ the
Vandermonde matrix of the diagonal (Mathlib's `Matrix.vandermonde`). More generally, if
$\mathbf{Y}\mathbf{H} = \operatorname{diag}(\mathbf{d})\mathbf{Y}$ (the rows of $\mathbf{Y}$ are
left eigenvectors of $\mathbf{H}$), then
$\mathbf{Y}\,\mathbf{K}_t(\mathbf{H}, \mathbf{x}) =
\operatorname{diag}(\mathbf{Y}\mathbf{x})\,\mathbf{V}$, which is invertible exactly when the $d_i$
are distinct and no coordinate of $\mathbf{Y}\mathbf{x}$ vanishes. For Hermitian $\mathbf{H}$ and
a frame $\mathbf{Z}$ of eigenvectors with real eigenvalues this is the head block
$\mathbf{Z}^{\mathsf{H}}\mathbf{K}$ of the single-vector simulated block of randomized block Krylov
iteration.

## Main results

* `NLAlib.krylovMatrix_diagonal`: $\mathbf{K}_t(\operatorname{diag}(\mathbf{d}), \mathbf{g}) =
  \operatorname{diag}(\mathbf{g})\,\mathbf{V}$.
* `NLAlib.mul_krylovMatrix_eq_diagonal_mul_vandermonde`: the intertwined form.
* `NLAlib.isUnit_det_mul_krylovMatrix`: invertibility for distinct $d_i$ and nonzero coordinates.
* `Matrix.IsHermitian.conjTranspose_mul_blockKrylovMatrix_replicateCol`,
  `Matrix.IsHermitian.rank_conjTranspose_mul_blockKrylovMatrix_replicateCol`: the head block of
  the one-column block Krylov matrix of a Hermitian matrix, and its rank.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {t : ℕ}

/-- **The Krylov matrix of a diagonal matrix**: for $\mathbf{d}, \mathbf{g} \in \Bbbk^t$,
$$\mathbf{K}_t(\operatorname{diag}(\mathbf{d}), \mathbf{g}) =
\operatorname{diag}(\mathbf{g})\,\mathbf{V}\,,\qquad \mathbf{V}_{ij} = d_i^{\,j}\,,$$
with $\mathbf{V}$ the Vandermonde matrix of $\mathbf{d}$. -/
theorem krylovMatrix_diagonal (d g : Fin t → 𝕜) :
    krylovMatrix (Matrix.diagonal d) g t = Matrix.diagonal g * Matrix.vandermonde d := by
  ext i j
  rw [krylovMatrix_apply, Matrix.diagonal_pow, Matrix.mulVec_diagonal, Matrix.diagonal_mul,
    Matrix.vandermonde_apply, Pi.pow_apply, mul_comm]

/-- **The Krylov matrix in left eigenvector coordinates**: if
$\mathbf{Y}\mathbf{H} = \operatorname{diag}(\mathbf{d})\,\mathbf{Y}$ for
$\mathbf{Y} \in \Bbbk^{t \times n}$, then for every $\mathbf{x}$,
$$\mathbf{Y}\,\mathbf{K}_t(\mathbf{H}, \mathbf{x}) =
\operatorname{diag}(\mathbf{Y}\mathbf{x})\,\mathbf{V}\,,\qquad \mathbf{V}_{ij} = d_i^{\,j}\,,$$
with $\mathbf{V}$ the Vandermonde matrix of $\mathbf{d}$. No orthogonality is assumed. -/
theorem mul_krylovMatrix_eq_diagonal_mul_vandermonde {H : Matrix n n 𝕜}
    {Y : Matrix (Fin t) n 𝕜} {d : Fin t → 𝕜} (hY : Y * H = Matrix.diagonal d * Y) (x : n → 𝕜) :
    Y * krylovMatrix H x t = Matrix.diagonal (Y *ᵥ x) * Matrix.vandermonde d := by
  have hpow : ∀ k : ℕ, Y * H ^ k = Matrix.diagonal d ^ k * Y := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
    | succ k ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hY, ← Matrix.mul_assoc, ← pow_succ]
  ext i j
  have h : (Y * krylovMatrix H x t) i j = (Y *ᵥ (H ^ (j : ℕ) *ᵥ x)) i := rfl
  rw [h, Matrix.mulVec_mulVec, hpow, ← Matrix.mulVec_mulVec, Matrix.diagonal_pow,
    Matrix.mulVec_diagonal, Matrix.diagonal_mul, Matrix.vandermonde_apply, Pi.pow_apply, mul_comm]

/-- **Invertibility of the Krylov matrix in left eigenvector coordinates**: if
$\mathbf{Y}\mathbf{H} = \operatorname{diag}(\mathbf{d})\,\mathbf{Y}$ for
$\mathbf{Y} \in \Bbbk^{t \times n}$ with distinct $d_0, \dots, d_{t-1}$, and no coordinate of
$\mathbf{Y}\mathbf{x}$ vanishes, then the $t \times t$ matrix
$\mathbf{Y}\,\mathbf{K}_t(\mathbf{H}, \mathbf{x})$ is invertible. -/
theorem isUnit_det_mul_krylovMatrix {H : Matrix n n 𝕜} {Y : Matrix (Fin t) n 𝕜} {d : Fin t → 𝕜}
    (hY : Y * H = Matrix.diagonal d * Y) (hd : Function.Injective d) {x : n → 𝕜}
    (hx : ∀ i, (Y *ᵥ x) i ≠ 0) : IsUnit (Y * krylovMatrix H x t).det := by
  rw [mul_krylovMatrix_eq_diagonal_mul_vandermonde hY, Matrix.det_mul, Matrix.det_diagonal,
    isUnit_iff_ne_zero]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hx i)
    (Matrix.det_vandermonde_ne_zero_iff.mpr hd)

/-- **The head block of a single-vector simulated block**: for Hermitian $\mathbf{H}$ and a
frame $\mathbf{Z} \in \Bbbk^{n \times t}$ of eigenvectors,
$\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\mathbf{d})$ with real $\mathbf{d}$,
the one-column block Krylov matrix
$\mathbf{K} = [\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$ has
$$\mathbf{Z}^{\mathsf{H}}\mathbf{K} =
\operatorname{diag}(\mathbf{Z}^{\mathsf{H}}\mathbf{x})\,\mathbf{V}\,,\qquad
\mathbf{V}_{ij} = d_i^{\,j}\,,$$
with $\mathbf{V}$ the Vandermonde matrix of $\mathbf{d}$, up to the reindexing of the columns of
the block Krylov matrix by `Fin t × Unit`. The frame need not be orthonormal. -/
theorem _root_.Matrix.IsHermitian.conjTranspose_mul_blockKrylovMatrix_replicateCol
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {Z : Matrix n (Fin t) 𝕜} {d : Fin t → ℝ}
    (hHZ : H * Z = Z * Matrix.diagonal fun i => (d i : 𝕜)) (x : n → 𝕜) :
    Zᴴ * blockKrylovMatrix H (Matrix.replicateCol Unit x) t =
      (Matrix.diagonal (Zᴴ *ᵥ x) * Matrix.vandermonde fun i => (d i : 𝕜)).submatrix id
        Prod.fst := by
  have hY : Zᴴ * H = Matrix.diagonal (fun i => (d i : 𝕜)) * Zᴴ := by
    have h := congrArg Matrix.conjTranspose hHZ
    rw [Matrix.conjTranspose_mul, hH.eq, Matrix.conjTranspose_mul,
      Matrix.diagonal_conjTranspose] at h
    rw [h]
    congr 2
    funext i
    simp
  rw [← mul_krylovMatrix_eq_diagonal_mul_vandermonde hY x, blockKrylovMatrix_replicateCol]
  rfl

open scoped ComplexOrder in
/-- **The head block of a single-vector simulated block has full rank**: for Hermitian
$\mathbf{H}$ and a frame $\mathbf{Z} \in \Bbbk^{n \times t}$ of eigenvectors,
$\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\mathbf{d})$ with distinct real
$d_0, \dots, d_{t-1}$, and a vector $\mathbf{x}$ with no vanishing coordinate of
$\mathbf{Z}^{\mathsf{H}}\mathbf{x}$, the one-column block Krylov matrix
$\mathbf{K} = [\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$ has
$\operatorname{rank}(\mathbf{K}^{\mathsf{H}}\mathbf{Z}) = t$. The frame need not be orthonormal;
for an orthonormal frame $t$ is its rank, which is the rank hypothesis of the structural bounds
of the range finder. -/
theorem _root_.Matrix.IsHermitian.rank_conjTranspose_mul_blockKrylovMatrix_replicateCol
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {Z : Matrix n (Fin t) 𝕜} {d : Fin t → ℝ}
    (hHZ : H * Z = Z * Matrix.diagonal fun i => (d i : 𝕜)) (hd : Function.Injective d)
    {x : n → 𝕜} (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) :
    ((blockKrylovMatrix H (Matrix.replicateCol Unit x) t)ᴴ * Z).rank = t := by
  have hdet : IsUnit (Matrix.diagonal (Zᴴ *ᵥ x) * Matrix.vandermonde fun i => (d i : 𝕜)).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hx i)
      (Matrix.det_vandermonde_ne_zero_iff.mpr (RCLike.ofReal_injective.comp hd))
  rw [← Matrix.rank_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hH.conjTranspose_mul_blockKrylovMatrix_replicateCol hHZ x]
  exact (Matrix.rank_submatrix _ (Equiv.refl (Fin t)) (Equiv.prodPUnit (Fin t))).trans
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)).trans
      (Fintype.card_fin t))

end NLAlib
