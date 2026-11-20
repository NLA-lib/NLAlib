/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.LowRank

/-!
# Singular values of a compression

Singular values and Frobenius errors of a compression $\mathbf{P}\mathbf{A}$ of a matrix by an
orthogonal projector $\mathbf{P}$. The quantities
$\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2 \ge 0$ are called the *deficits* of
$\mathbf{P}$: they are bounded by how much of the best rank-$(i+1)$ approximation $\mathbf{P}$
misses, they decrease when the range of $\mathbf{P}$ grows, their sum over $i < k$ is exactly the
excess of the Frobenius error of $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ over the optimal
one, and a small sum of the first $L$ deficits together with a gap after $\sigma_{L-1}$ forces
the range of $\mathbf{P}$ to capture $\llbracket\mathbf{A}\rrbracket_L$.

## Main results

* `IsStarProjection.sq_singularValues_sub_sq_specNorm_le`: $\sigma_i(\mathbf{P}\mathbf{A})^2 \ge
  \sigma_i(\mathbf{A})^2 - \|(\mathbf{I} - \mathbf{P})\llbracket\mathbf{A}\rrbracket_{i+1}\|_2^2$.
* `NLAlib.singularValues_rangeProjector_mul_le_of_range_le`: a larger range gives larger singular
  values of the compression.
* `IsStarProjection.frobNorm_sub_mul_sq_eq_add_sum`,
  `IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq`: the Frobenius error as the optimal error
  plus the sum of the deficits.
* `NLAlib.HasOrthonormalCols.mul_frobNorm_truncatedSVD_sub_mul_sq_le`,
  `IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le`: an energy deficit and a gap give
  head capture.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n s : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq s]

omit [DecidableEq n] in
/-- **Singular values of a compression from below**: for an orthogonal projector $\mathbf{P}$
($m \times m$), an $m \times n$ matrix $\mathbf{A}$ and every index $i$ (from $0$),
$$\sigma_i(\mathbf{A})^2 -
\|(\mathbf{I} - \mathbf{P})\llbracket\mathbf{A}\rrbracket_{i+1}\|_2^2 \le
\sigma_i(\mathbf{P}\mathbf{A})^2\,.$$
On the row space of $\llbracket\mathbf{A}\rrbracket_{i+1}$, of dimension $i + 1$ when
$\sigma_i > 0$, the compression loses at most the second term (Pythagoras), and the min–max
characterization `NLAlib.le_singularValues_of_forall_mem` applies.
[MuscoMusco2015, Theorem 12]; used there in the proof of the per-vector guarantee, for the
projector of a Krylov space. -/
theorem _root_.IsStarProjection.sq_singularValues_sub_sq_specNorm_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (i : ℕ) :
    singularValues A i ^ 2 - specNorm ((1 - P) * truncatedSVD A (i + 1)) ^ 2 ≤
      singularValues (P * A) i ^ 2 := sorry

omit [DecidableEq m] in
omit [DecidableEq n] [DecidableEq s] in
/-- Monotonicity of the singular values of a compression in the range: if the range of
$\mathbf{Y}'$ is contained in the range of $\mathbf{Y}$, then for every $\mathbf{A}$ and $i$,
$$\sigma_i(\mathbf{P}_{\mathbf{Y}'}\mathbf{A}) \le \sigma_i(\mathbf{P}_{\mathbf{Y}}\mathbf{A})\,,$$
since $\mathbf{P}_{\mathbf{Y}'} = \mathbf{P}_{\mathbf{Y}'}\mathbf{P}_{\mathbf{Y}}$. The twin for
the error $\mathbf{A} - \mathbf{P}_{\mathbf{Y}}\mathbf{A}$ of the randomized SVD is
`NLAlib.singularValues_one_sub_rangeProjector_mul_le_of_range_le`. -/
theorem singularValues_rangeProjector_mul_le_of_range_le {Y : Matrix m l 𝕜} {Y' : Matrix m s 𝕜}
    (h : LinearMap.range Y'.mulVecLin ≤ LinearMap.range Y.mulVecLin) (A : Matrix m n 𝕜) (i : ℕ) :
    singularValues (rangeProjector Y' * A) i ≤ singularValues (rangeProjector Y * A) i := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The Frobenius error of a compression of rank at most $k$**: for an orthogonal projector
$\mathbf{P}$ with $\operatorname{rank}\mathbf{P} \le k$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 =
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
\sum_{i<k} \bigl(\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2\bigr)\,,$$
the optimal error plus the deficits of $\mathbf{P}$. It holds for every such projector, whether
or not its range is spanned by singular vectors of a compression.
[MuscoMusco2015, Definition 8]; the sum of the deficits is the error function
$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 -
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ defined there for a frame with
$k$ orthonormal columns, here written through the singular values of $\mathbf{P}\mathbf{A}$. -/
theorem _root_.IsStarProjection.frobNorm_sub_mul_sq_eq_add_sum {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) {k : ℕ} (hk : P.rank ≤ k) :
    frobNorm (A - P * A) ^ 2 = frobNorm (A - truncatedSVD A k) ^ 2 +
      ∑ i ∈ Finset.range k, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The Frobenius error of a truncated compression**: for an orthogonal projector $\mathbf{P}$
(of any rank) and every $k$,
$$\|\mathbf{A} - \llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 =
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
\sum_{i<k} \bigl(\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2\bigr)\,.$$
The truncation $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ is $\mathbf{\Pi}\mathbf{A}$ for the
projector $\mathbf{\Pi}$ onto its column space, which lies in the range of $\mathbf{P}$ and has
rank at most $k$. [MuscoMusco2015, Definition 8]; the error function defined there, at the frame
of the column space of $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$. -/
theorem _root_.IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (P * A) k) ^ 2 = frobNorm (A - truncatedSVD A k) ^ 2 +
      ∑ i ∈ Finset.range k, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **An energy deficit and a gap give head capture, frame form**: let $\mathbf{W}$ have at most
$L = h + 1$ orthonormal columns, let $\theta \le 1$ be a relative gap,
$\sigma_L(\mathbf{A})^2 \le (1 - \theta)\,\sigma_h(\mathbf{A})^2$, and let the energy of
$\mathbf{W}$ be within $\eta$ of the largest possible,
$\sum_{i<L} \sigma_i(\mathbf{A})^2 - \eta \le \|\mathbf{A}^{\mathsf{H}}\mathbf{W}\|_{\mathsf{F}}^2$.
Then the range of $\mathbf{W}$ captures the best rank-$L$ approximation,
$$\theta\,\|\llbracket\mathbf{A}\rrbracket_L -
\mathbf{W}\mathbf{W}^{\mathsf{H}}\llbracket\mathbf{A}\rrbracket_L\|_{\mathsf{F}}^2 \le \eta\,.$$
For $\theta \le 0$ the statement is trivial; without $\theta \le 1$ it is false.
[BakshiClarksonWoodruff2022, Lemma 3.5]; there for exactly $L$ columns with a per-vector
hypothesis and an unspecified polynomial accuracy, here for at most $L$ columns, with the summed
energy deficit and the gap explicit. -/
theorem HasOrthonormalCols.mul_frobNorm_truncatedSVD_sub_mul_sq_le {W : Matrix m s 𝕜}
    (hW : HasOrthonormalCols W) (A : Matrix m n 𝕜) {h L : ℕ} (hL : h + 1 = L)
    (hcard : Fintype.card s ≤ L) {θ η : ℝ} (hθ : θ ≤ 1)
    (hgap : singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hη : ∑ i ∈ Finset.range L, singularValues A i ^ 2 - η ≤ frobNorm (Aᴴ * W) ^ 2) :
    θ * frobNorm (truncatedSVD A L - W * Wᴴ * truncatedSVD A L) ^ 2 ≤ η := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **Small deficits and a gap give head capture**: for an orthogonal projector $\mathbf{P}$,
$L = h + 1$ and a relative gap $\theta \le 1$ with
$\sigma_L(\mathbf{A})^2 \le (1 - \theta)\,\sigma_h(\mathbf{A})^2$,
$$\theta\,\|\llbracket\mathbf{A}\rrbracket_L -
\mathbf{P}\llbracket\mathbf{A}\rrbracket_L\|_{\mathsf{F}}^2 \le
\sum_{i<L} \bigl(\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2\bigr)\,.$$
The frame form `NLAlib.HasOrthonormalCols.mul_frobNorm_truncatedSVD_sub_mul_sq_le` at a frame of
the column space of $\llbracket\mathbf{P}\mathbf{A}\rrbracket_L$.
[BakshiClarksonWoodruff2022, Corollary 3.7]; there for a basis of the range of
$\mathbf{A}^{\mathsf{T}}\mathbf{W}$ and an unspecified polynomial accuracy, here one-sided, for
any projector, with the sum of the deficits on the right. -/
theorem _root_.IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) {h L : ℕ} (hL : h + 1 = L) {θ : ℝ}
    (hθ : θ ≤ 1) (hgap : singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2) :
    θ * frobNorm (truncatedSVD A L - P * truncatedSVD A L) ^ 2 ≤
      ∑ i ∈ Finset.range L, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

end NLAlib
