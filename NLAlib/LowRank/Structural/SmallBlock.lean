/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Vandermonde
public import NLAlib.Krylov.Basic.KrylovVandermonde
public import NLAlib.LowRank.Structural.BlockKrylov
public import NLAlib.LowRank.Structural.Filter
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.Polynomial.Interpolation.LagrangeBound

/-!
# Randomized block Krylov iteration with a single start vector

The deterministic part of the analysis of randomized block Krylov iteration with block size one,
start vector $\mathbf{x}$. With $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$,
$\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)$ is at least as good as the randomized SVD at the
filtered simulated block
$f(\mathbf{H})\mathbf{K}$, $\mathbf{K} = [\mathbf{x}, \mathbf{H}\mathbf{x}, \dots,
\mathbf{H}^{t-1}\mathbf{x}]$, for every polynomial $f$ of degree less than $d$ with
$t + d \le q + 1$ (`NLAlib.singularValues_sub_rbki_le_of_degree_lt_of_add_le`). For an
orthonormal frame $\mathbf{Z}$ of right singular vectors for $\sigma_0 > \dots > \sigma_{t-1} > 0$
the head block is $\mathbf{Z}^{\mathsf{H}}\mathbf{K} =
\operatorname{diag}(\mathbf{Z}^{\mathsf{H}}\mathbf{x})\,\mathbf{V}$ with $\mathbf{V}$ the
Vandermonde matrix of $\sigma_i^2$, the columns of $\mathbf{V}^{-1}$ are the coefficients of the
Lagrange basis polynomials $\ell_i$ of these nodes, and column $i$ of the sketch residual of the
filtered range finder is
$(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i^{-1}\,\mathbf{A}f(\mathbf{H})\ell_i(\mathbf{H})
(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}$. On the tail spectrum
$\lvert\ell_i\rvert \le \Delta^{-(t-1)}$ for the relative gap $\Delta$ of the squared head
singular values, which gives the starting-block factor
$\Delta^{-2(t-1)}\sum_i \lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}$ in place of the
inverse moment of a Gaussian block of width at least $t + 2$.

The statements carry the sharp factors; nothing is random here.

## Main results

* `NLAlib.frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le`: the sketch
  residual of the single-vector simulated block.
* `NLAlib.specNorm_sub_rbki_replicateCol_sq_le`,
  `NLAlib.frobNorm_sub_rbki_replicateCol_sq_le`: the single-vector bound,
  spectral and Frobenius.
* `NLAlib.rbki_replicateCol_eq_self`: the exact case, distinct nonzero
  singular values and $q \ge \operatorname{rank}\mathbf{A}$.
-/

@[expose] public section

open scoped Matrix ComplexOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The sketch residual of the single-vector simulated block**: let
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, let $\mathbf{Z} \in \Bbbk^{n \times t}$ be an
orthonormal frame with
$\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$\sigma_i = \sigma_i(\mathbf{A}) > 0$ for $i < t$ and
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$, $\Delta > 0$, and let $\mathbf{x}$
have no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$. For a real polynomial $f$
with $\lvert f \rvert \le a$ on $[0, \sigma_t^2]$, the block
$\mathbf{K} = [\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$ and
$\mathbf{B} = \mathbf{A}f(\mathbf{H})$,
$$\bigl\|(\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{K}
(\mathbf{Z}^{\mathsf{H}}\mathbf{K})^{+}\bigr\|_{\mathsf{F}}^2 \le
a^2\,\Delta^{-2(t-1)}\Bigl(\sum_{i<t}\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}\Bigr)
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$
The exponent $2(t - 1)$ is in $\mathbb{N}$; for $t = 0$ both sides vanish. -/
theorem frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le {t : ℕ}
    (A : Matrix m n 𝕜) (x : n → 𝕜) {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    {Δ : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) (f : ℝ[X]) {a : ℝ}
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ a) :
    frobNorm ((A * aeval (Aᴴ * A) f - A * aeval (Aᴴ * A) f * Z * Zᴴ) *
        blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t *
        pinv (Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)) ^ 2 ≤
      a ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
        ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  -- With `H = Aᴴ * A`, `g = Zᴴ *ᵥ x`, `V = vandermonde (σ i ^ 2)`: by
  -- `Matrix.IsHermitian.conjTranspose_mul_blockKrylovMatrix_replicateCol`,
  -- `Zᴴ * K = (diagonal g * V).submatrix id Prod.fst` is invertible up to `Equiv.prodPUnit`, so
  -- its `pinv` is the reindexed `V⁻¹ * diagonal g⁻¹`, and by `Matrix.inv_vandermonde` column `i`
  -- of `K * pinv (Zᴴ * K)` is `(g i)⁻¹ • aeval H ℓ_i *ᵥ x`.
  -- `Z * Zᴴ` commutes with `H` (`hAZ` and its adjoint), so column `i` of the residual is
  -- `(g i)⁻¹ • (A * aeval H (f * ℓ_i)) *ᵥ w`, `w = (1 - Z * Zᴴ) *ᵥ x`, and the squared Frobenius
  -- norm is the sum of the squared column norms. Finally `‖A * p(H) *ᵥ w‖ ≤ sup |p| * ‖A *ᵥ w‖`
  -- with the supremum over the eigenvalues of `H` on the complement of `Z`, which are the
  -- `σ j ^ 2`, `j ≥ t`, all in `[0, σ t ^ 2]` (spectral decomposition of `H` extending `Z`,
  -- `singularValues_antitone`); there `|f| ≤ a` and `|ℓ_i| ≤ Δ⁻¹ ^ (t - 1)`
  -- (`abs_eval_basis_le_inv_pow`).
  sorry

/-- **Randomized block Krylov iteration with a single start vector, spectral norm**: let
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, let $\mathbf{Z} \in \Bbbk^{n \times t}$ be an
orthonormal frame with
$\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$\sigma_i = \sigma_i(\mathbf{A}) > 0$ for $i < t$ and
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$, $\Delta > 0$, and let $\mathbf{x}$
have no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$. For a real polynomial $f$ of
degree less than $d$ with $t + d \le q + 1$, a head index $r \le t$,
$\lvert f(\sigma_i^2) \rvert \ge c > 0$ for $i < r$ and $\lvert f \rvert \le a$ on
$[0, \sigma_t^2]$,
$$\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2 \le \sigma_r^2 +
\Bigl(\frac{a}{c}\Bigr)^2\Delta^{-2(t-1)}
\Bigl(\sum_{i<t}\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}\Bigr)
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$
The exponent $2(t - 1)$ is in $\mathbb{N}$ and sharp for this argument: for $t = 1$ the gap
hypothesis is empty and no power of $\Delta$ appears; for $t = 0$ the bound is
$\|\mathbf{A}\|_2^2$. The gap hypothesis does not separate $\sigma_{t-1}$ from $\sigma_t$, so
the tail is that of the frame $\mathbf{Z}$, which need not be the truncated SVD. The first $r$
columns of $\mathbf{Z}$ are the head frame of the filtered structural bound, and the head block
$\mathbf{Z}^{\mathsf{H}}[\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$ is
a diagonal matrix times a Vandermonde matrix, invertible under the hypotheses. -/
theorem specNorm_sub_rbki_replicateCol_sq_le {t : ℕ} (A : Matrix m n 𝕜)
    (x : n → 𝕜) {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    {Δ : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q d r : ℕ} {f : ℝ[X]} (hf : f.degree < d)
    (hd : t + d ≤ q + 1) (hr : r ≤ t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ a) :
    specNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      singularValues A r ^ 2 +
        (a / c) ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  -- `singularValues_sub_rbki_le_of_degree_lt_of_add_le` (at `s = t`, index `0`, with
  -- `singularValues_zero_eq_specNorm`) reduces to `rsvd A (aeval H f * K)`, `K` the simulated
  -- block, and `Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq` turns `aeval H f` into
  -- `cfc (fun y => f.eval y) H`. Apply `HasOrthonormalCols.specNorm_sub_rsvd_cfc_sq_le` with
  -- `W = Z.submatrix id (Fin.castLE hr)`, `hΩ` from
  -- `Matrix.IsHermitian.rank_conjTranspose_mul_blockKrylovMatrix_replicateCol` and `hZ.rank`.
  -- Then `specNorm (A - A * W * Wᴴ) = singularValues A r` (the Gram matrix is `H` with the
  -- eigenvalues `σ i ^ 2`, `i < r`, removed), `specNorm M ≤ frobNorm M`, and
  -- `frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le`.
  sorry

/-- **Randomized block Krylov iteration with a single start vector, Frobenius norm**: let
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, let $\mathbf{Z} \in \Bbbk^{n \times t}$ be an
orthonormal frame with
$\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$\sigma_i = \sigma_i(\mathbf{A}) > 0$ for $i < t$ and
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$, $\Delta > 0$, and let $\mathbf{x}$
have no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$. For a real polynomial $f$ of
degree less than $d$ with $t + d \le q + 1$, a head index $r \le t$,
$\lvert f(\sigma_i^2) \rvert \ge c > 0$ for $i < r$ and $\lvert f \rvert \le a$ on
$[0, \sigma_t^2]$,
$$\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
\Bigl(\frac{a}{c}\Bigr)^2\Delta^{-2(t-1)}
\Bigl(\sum_{i<t}\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}\Bigr)
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$
The exponent $2(t - 1)$ is in $\mathbb{N}$. The head frame of the filtered structural bound is
the first $r$ columns $\mathbf{W}$ of $\mathbf{Z}$; when $\sigma_{r-1} = \sigma_r$ (possible only
for $r = t$) the matrix $\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}$ need not be
$\llbracket\mathbf{A}\rrbracket_r$, but the two have the same Frobenius error. -/
theorem frobNorm_sub_rbki_replicateCol_sq_le {t : ℕ} (A : Matrix m n 𝕜)
    (x : n → 𝕜) {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    {Δ : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q d r : ℕ} {f : ℝ[X]} (hf : f.degree < d)
    (hd : t + d ≤ q + 1) (hr : r ≤ t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ a) :
    frobNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        (a / c) ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  -- As the spectral form, summing `singularValues_sub_rbki_le_of_degree_lt_of_add_le` over the
  -- index (the Frobenius norm is monotone in the singular values) and applying
  -- `HasOrthonormalCols.frobNorm_sub_rsvd_cfc_sq_le`. The head term is
  -- `frobNorm (A - A * W * Wᴴ) ^ 2 = ∑ j ≥ r, σ j ^ 2 = frobNorm (A - truncatedSVD A r) ^ 2`
  -- (`frobNorm_sub_truncatedSVD_sq`): the Gram matrix of `A - A * W * Wᴴ` is `H` with the
  -- eigenvalues `σ i ^ 2`, `i < r`, removed, whichever eigenvectors `W` picks.
  sorry

/-- **Randomized block Krylov iteration with a single start vector is exact at the rank**: let
$\mathbf{A}$ have rank at most $t$, let $\mathbf{Z} \in \Bbbk^{n \times t}$ be an orthonormal
frame with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$\sigma_i = \sigma_i(\mathbf{A})$, with $\sigma_0 > \sigma_1 > \dots > \sigma_{t-1}$, and let
$\mathbf{x}$ have no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$. Then for every
$q \ge t$,
$$\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q) = \mathbf{A}\,.$$
This is the case the gapped single-vector bound excludes by asking for positive head singular
values: there $\mathbf{A}$ vanishes on the complement of the frame, and the Krylov space of depth
$t$ already contains the range of $\mathbf{Z}$. Distinctness and the nonvanishing coordinates
cannot be dropped: the Krylov space of one vector has dimension at most the number of distinct
eigenvalues it meets. -/
theorem rbki_replicateCol_eq_self {t : ℕ} (A : Matrix m n 𝕜)
    (x : n → 𝕜) {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    (hrank : A.rank ≤ t)
    (hlt : ∀ i j, i < j → j < t → singularValues A j < singularValues A i)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q : ℕ} (hq : t ≤ q) :
    rbki A (Matrix.replicateCol Unit x) q = A := by
  -- By `singularValues_sub_rbki_le_of_le` it suffices to take `q = t` (all singular values of the
  -- error vanish). `A * (1 - Z * Zᴴ) = 0`: its Gram matrix is `H` with the eigenvalues
  -- `σ i ^ 2`, `i < t`, removed, and `σ j = 0` for `j ≥ t` (`singularValues_eq_zero_iff`). So
  -- `A * K = A * Z * (Zᴴ * K)` with `Zᴴ * K` invertible up to reindexing
  -- (`Matrix.IsHermitian.conjTranspose_mul_blockKrylovMatrix_replicateCol`,
  -- `isUnit_det_mul_krylovMatrix`), the range of `A * K` is that of `A * Z`, which is the range
  -- of `A = A * Z * Zᴴ`, and `rangeProjector_mul_eq_self_iff` finishes.
  sorry

end NLAlib
