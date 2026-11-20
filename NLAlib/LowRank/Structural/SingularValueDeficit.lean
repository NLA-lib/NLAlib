/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.Norms.SchattenPinching
public import NLAlib.Matrix.Spectral.CompressionSingularValues
public import NLAlib.Matrix.Spectral.SingularValueDecay

/-!
# Low-rank approximation error from singular value deficits

Deterministic error bounds, in Schatten norms, for a low-rank approximation built from an
orthogonal projector $\mathbf{P}$ on the left, in terms of the *deficits*
$\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2$, $i < k$, of the compression
$\mathbf{P}\mathbf{A}$. Two outputs are covered. The *two-sided* output $\mathbf{A}\mathbf{Q}$,
for an orthogonal projector $\mathbf{Q}$ with $\mathbf{P}\mathbf{A}\mathbf{Q} =
\mathbf{P}\mathbf{A}$ (the row space of $\mathbf{P}\mathbf{A}$ lies in the range of
$\mathbf{Q}$), for $1 \le p < \infty$; the *one-sided* output $\mathbf{P}\mathbf{A}$, for
$2 \le p < \infty$ and in the Frobenius norm. Nothing here is about a Krylov space or a random
matrix: the hypotheses are inequalities between singular values.

The *tail-count forms* replace the case analysis of [BakshiClarksonWoodruff2022] by one
inequality: if $\sigma_k \le \kappa\,\sigma_{k+j}$ (the spectrum has not dropped by the factor
$\kappa$ after $j$ more singular values), then $\sigma_k^p$ is at most
$\kappa^p/(j + 1)$ times the optimal error, so deficits of relative size $\gamma$ cost
$k\gamma\kappa^p/(j + 1)$.

## Main results

* `IsStarProjection.schattenNorm_sub_mul_rpow_add_le`,
  `IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum`,
  `IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum_mul`: the two-sided error from the
  deficits, $1 \le p < \infty$.
* `IsStarProjection.matrixNorm_sub_mul_le_matrixNorm_sub_mul`: the two-sided error is at most the
  one-sided error, in every unitarily invariant norm.
* `IsStarProjection.schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul`,
  `IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq_le_of_singularValues_le_mul`,
  `NLAlib.min_schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul`: the tail-count forms for
  $1 \le p \le 2$, for the Frobenius norm, and for the better of two candidates.
* `IsStarProjection.schattenNorm_sub_mul_le_add_rpow`,
  `IsStarProjection.schattenNorm_sub_mul_le_of_sq_singularValues_sub_le`,
  `IsStarProjection.schattenNorm_sub_mul_le_mul_of_singularValues_le_mul`: the head split and
  the tail-count form for $2 \le p < \infty$, one-sided.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### The two-sided output, $1 \le p < \infty$ -/

omit [DecidableEq m] [DecidableEq n] in
/-- **The two-sided error against the energy of the compression**: for $1 \le p < \infty$ and
orthogonal projectors $\mathbf{P}$, $\mathbf{Q}$ with
$\mathbf{P}\mathbf{A}\mathbf{Q} = \mathbf{P}\mathbf{A}$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{S_p}^p + \|\mathbf{P}\mathbf{A}\|_{S_p}^p \le
\|\mathbf{A}\|_{S_p}^p\,.$$
Under the hypothesis, $(\mathbf{I} - \mathbf{P})\mathbf{A}(\mathbf{I} - \mathbf{Q}) =
\mathbf{A}(\mathbf{I} - \mathbf{Q})$, so this is
`IsStarProjection.schattenNorm_mul_mul_rpow_add_le`.
[BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there with $\mathbf{P} =
\mathbf{W}\mathbf{W}^{\mathsf{T}}$ for a Krylov basis $\mathbf{W}$ and $\mathbf{Q}$ the projector
onto the range of $\mathbf{A}^{\mathsf{T}}\mathbf{W}$, here for any pair of projectors with
$\mathbf{P}\mathbf{A}\mathbf{Q} = \mathbf{P}\mathbf{A}$. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_add_le {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) :
    schattenNorm p (A - A * Q) ^ p.toReal + schattenNorm p (P * A) ^ p.toReal ≤
      schattenNorm p A ^ p.toReal := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The two-sided error from the deficits in $p$-th powers**: for $1 \le p < \infty$, orthogonal
projectors $\mathbf{P}$, $\mathbf{Q}$ with $\mathbf{P}\mathbf{A}\mathbf{Q} =
\mathbf{P}\mathbf{A}$ and every $k$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{S_p}^p \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sum_{i<k} \bigl(\sigma_i(\mathbf{A})^p - \sigma_i(\mathbf{P}\mathbf{A})^p\bigr)\,.$$
[BakshiClarksonWoodruff2022, Lemma 3.4]; there for a basis with a per-vector guarantee and inside
a probability, here deterministic, with hypotheses on the singular values of
$\mathbf{P}\mathbf{A}$ only. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) (k : ℕ) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤ schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
      ∑ i ∈ Finset.range k,
        (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal) := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The two-sided error from the deficits in squares**: for $1 \le p < \infty$, orthogonal
projectors $\mathbf{P}$, $\mathbf{Q}$ with $\mathbf{P}\mathbf{A}\mathbf{Q} =
\mathbf{P}\mathbf{A}$ and every $k$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{S_p}^p \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sum_{i<k} \max\Bigl(1, \frac{p}{2}\Bigr)\,\sigma_i(\mathbf{A})^{p-2}
\bigl(\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2\bigr)\,,$$
termwise from `Real.rpow_sub_rpow_le_max_mul` at the exponent $p/2$.
[BakshiClarksonWoodruff2022, Lemma 3.4]; there with the constant $p/2$, which is correct only
for $p \ge 2$; here $\max(1, p/2)$. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum_mul {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) (k : ℕ) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤ schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
      ∑ i ∈ Finset.range k, max 1 (p.toReal / 2) * singularValues A i ^ (p.toReal - 2) *
        (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- The two-sided error is at most the one-sided error: for a matrix $\mathbf{P}$, an orthogonal
projector $\mathbf{Q}$ with $\mathbf{P}\mathbf{A}\mathbf{Q} = \mathbf{P}\mathbf{A}$ and every
unitarily invariant norm,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{\Phi} \le \|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\Phi}\,,$$
since $\mathbf{A} - \mathbf{A}\mathbf{Q} =
(\mathbf{A} - \mathbf{P}\mathbf{A})(\mathbf{I} - \mathbf{Q})$. It transfers every bound for the
one-sided output $\mathbf{P}\mathbf{A}$ to the two-sided output $\mathbf{A}\mathbf{Q}$. -/
theorem _root_.IsStarProjection.matrixNorm_sub_mul_le_matrixNorm_sub_mul (Φ : SymmetricGauge)
    {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) :
    Φ.matrixNorm (A - A * Q) ≤ Φ.matrixNorm (A - P * A) := sorry

/-! ### Tail-count forms, $1 \le p \le 2$ and Frobenius -/

omit [DecidableEq m] [DecidableEq n] in
/-- **The tail-count form of the two-sided error, $1 \le p \le 2$**: let $\mathbf{P}$,
$\mathbf{Q}$ be orthogonal projectors with $\mathbf{P}\mathbf{A}\mathbf{Q} =
\mathbf{P}\mathbf{A}$, let $\gamma, \kappa \ge 0$ and $\beta_i \ge 0$ for $i < k$, with
$\beta_i = 0$ for all $i < k$ if $\sigma_k(\mathbf{A}) = 0$. If the tail is flat,
$\sigma_k \le \kappa\,\sigma_{k+j}$, and the deficits satisfy
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 - \beta_i \le
\sigma_i(\mathbf{P}\mathbf{A})^2$ for $i < k$, then
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{S_p}^p \le
\Bigl(1 + \frac{k\gamma\kappa^p}{j + 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sigma_k(\mathbf{A})^{p-2} \sum_{i<k} \beta_i\,.$$
The relative part $\gamma$ of the deficits is paid for by the tail count
`NLAlib.mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow`; the absolute parts
$\beta_i$ enter through their sum. The condition at $\sigma_k = 0$ is needed because
$\sigma_k^{p-2}$ is $0$ there in Lean for $p < 2$; at $p = 2$ it is not needed.
[BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there the case of a heavy tail, with
unspecified constants, here one inequality with the flatness $\kappa$ and the count $j + 1$ as
parameters. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) {k j : ℕ} {γ κ : ℝ} {β : ℕ → ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (hβ : ∀ i < k, 0 ≤ β i) (hβ0 : singularValues A k = 0 → ∀ i < k, β i = 0)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 - β i ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤
      (1 + k * γ * κ ^ p.toReal / ((j : ℝ) + 1)) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) * ∑ i ∈ Finset.range k, β i := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The tail-count form of the Frobenius error, one-sided**: let $\mathbf{P}$ be an orthogonal
projector, $\gamma, \kappa \ge 0$ and $\beta_i \ge 0$ for $i < k$. If the tail is flat,
$\sigma_k \le \kappa\,\sigma_{k+j}$, and the deficits satisfy
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 - \beta_i \le
\sigma_i(\mathbf{P}\mathbf{A})^2$ for $i < k$, then
$$\|\mathbf{A} - \llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k\gamma\kappa^2}{j + 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 + \sum_{i<k} \beta_i\,.$$
[BakshiClarksonWoodruff2022, proof of Theorem 3.1]; the case $p = 2$ of the heavy-tail case
there, here for the truncated compression $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ with the
flatness $\kappa$ and the count $j + 1$ as parameters. -/
theorem _root_.IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq_le_of_singularValues_le_mul
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) {A : Matrix m n 𝕜} {k j : ℕ} {γ κ : ℝ}
    {β : ℕ → ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hβ : ∀ i < k, 0 ≤ β i)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 - β i ≤
      singularValues (P * A) i ^ 2) :
    frobNorm (A - truncatedSVD (P * A) k) ^ 2 ≤
      (1 + k * γ * κ ^ 2 / ((j : ℝ) + 1)) * frobNorm (A - truncatedSVD A k) ^ 2 +
        ∑ i ∈ Finset.range k, β i := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The better of two candidates, $1 \le p \le 2$**: let $(\mathbf{P}_1, \mathbf{Q}_1)$ and
$(\mathbf{P}_2, \mathbf{Q}_2)$ be pairs of orthogonal projectors with
$\mathbf{P}_a\mathbf{A}\mathbf{Q}_a = \mathbf{P}_a\mathbf{A}$, let
$\gamma_1, \gamma_2, \kappa \ge 0$ and $\beta^{(1)}_i, \beta^{(2)}_i \ge 0$ for $i < k$, all
zero if $\sigma_k(\mathbf{A}) = 0$. Suppose the first pair has deficits
$\sigma_i(\mathbf{A})^2 - \gamma_1\sigma_k(\mathbf{A})^2 - \beta^{(1)}_i \le
\sigma_i(\mathbf{P}_1\mathbf{A})^2$ for $i < k$, and the second pair has
$\sigma_i(\mathbf{A})^2 - \gamma_2\sigma_k(\mathbf{A})^2 - \beta^{(2)}_i \le
\sigma_i(\mathbf{P}_2\mathbf{A})^2$ for $i < k$ whenever there is a gap,
$\kappa\,\sigma_{k+j} < \sigma_k$. Then
$$\min\bigl(\|\mathbf{A} - \mathbf{A}\mathbf{Q}_1\|_{S_p}^p,
\|\mathbf{A} - \mathbf{A}\mathbf{Q}_2\|_{S_p}^p\bigr) \le
\Bigl(1 + k\max\Bigl(\frac{\gamma_1\kappa^p}{j + 1}, \gamma_2\Bigr)\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sigma_k(\mathbf{A})^{p-2}
\max\Bigl(\sum_{i<k} \beta^{(1)}_i, \sum_{i<k} \beta^{(2)}_i\Bigr)\,.$$
[BakshiClarksonWoodruff2022, Algorithm 3.2]; there the algorithm selects one of two block Krylov
runs from estimated singular values, here a statement about two pairs of projectors produced in
any way, with no selection rule. -/
theorem min_schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P₁ P₂ : Matrix m m 𝕜} {Q₁ Q₂ : Matrix n n 𝕜}
    (hP₁ : IsStarProjection P₁) (hQ₁ : IsStarProjection Q₁) (hP₂ : IsStarProjection P₂)
    (hQ₂ : IsStarProjection Q₂) {A : Matrix m n 𝕜} (h₁ : P₁ * A * Q₁ = P₁ * A)
    (h₂ : P₂ * A * Q₂ = P₂ * A) {k j : ℕ} {γ₁ γ₂ κ : ℝ} {β₁ β₂ : ℕ → ℝ} (hγ₁ : 0 ≤ γ₁)
    (hγ₂ : 0 ≤ γ₂) (hκ : 0 ≤ κ) (hβ₁ : ∀ i < k, 0 ≤ β₁ i) (hβ₂ : ∀ i < k, 0 ≤ β₂ i)
    (hβ0 : singularValues A k = 0 → ∀ i < k, β₁ i = 0 ∧ β₂ i = 0)
    (hritz₁ : ∀ i < k, singularValues A i ^ 2 - γ₁ * singularValues A k ^ 2 - β₁ i ≤
      singularValues (P₁ * A) i ^ 2)
    (hritz₂ : κ * singularValues A (k + j) < singularValues A k →
      ∀ i < k, singularValues A i ^ 2 - γ₂ * singularValues A k ^ 2 - β₂ i ≤
        singularValues (P₂ * A) i ^ 2) :
    min (schattenNorm p (A - A * Q₁) ^ p.toReal) (schattenNorm p (A - A * Q₂) ^ p.toReal) ≤
      (1 + k * max (γ₁ * κ ^ p.toReal / ((j : ℝ) + 1)) γ₂) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) *
          max (∑ i ∈ Finset.range k, β₁ i) (∑ i ∈ Finset.range k, β₂ i) := sorry

/-! ### The one-sided output, $2 \le p < \infty$ -/

omit [DecidableEq m] [DecidableEq n] in
/-- **The head split of the one-sided error, $2 \le p < \infty$**: for an orthogonal projector
$\mathbf{P}$ and $L \le k$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{S_p} \le
\|\llbracket\mathbf{A}\rrbracket_L - \mathbf{P}\llbracket\mathbf{A}\rrbracket_L\|_{S_p} +
\Bigl(\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sum_{L \le i < k} \bigl(\sigma_i(\mathbf{A})^p - \sigma_i(\mathbf{P}\mathbf{A})^p\bigr)
\Bigr)^{1/p}\,.$$
The head $\llbracket\mathbf{A}\rrbracket_L$ is split off by the triangle inequality, and the
rest is `IsStarProjection.schattenNorm_mul_rpow_add_le` for
$\mathbf{A} - \llbracket\mathbf{A}\rrbracket_L$ with Weyl's inequality for a perturbation of rank
at most $L$. [BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there for the two-sided output
with the pair-of-projectors inequality, here one-sided. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_add_rpow {p : ℝ≥0∞}
    (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P) (A : Matrix m n 𝕜)
    {L k : ℕ} (hLk : L ≤ k) :
    schattenNorm p (A - P * A) ≤
      schattenNorm p (truncatedSVD A L - P * truncatedSVD A L) +
        (schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
          ∑ i ∈ Finset.Ico L k,
            (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal)) ^
          p.toReal⁻¹ := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The head split with deficits, $2 \le p < \infty$**: let $\mathbf{P}$ be an orthogonal
projector, $L \le k$, $\delta, \gamma \ge 0$, $0 < \theta \le 1$ and $\kappa \ge 1$. Suppose
there is a gap before $L$, $\sigma_L^2 \le (1 - \theta)\,\sigma_h^2$ when $L = h + 1$; the
spectrum is flat from $L$ to $k$, $\sigma_L \le \kappa\,\sigma_k$; the head deficits satisfy
$\sigma_i(\mathbf{A})^2 - \delta\,\sigma_k(\mathbf{A})^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$
for $i < L$; and the others satisfy
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$
for $L \le i < k$. Then
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{S_p} \le
\sqrt{\frac{L\delta}{\theta}}\;\sigma_k(\mathbf{A}) +
\Bigl(\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\frac{p}{2}\,\kappa^{p-2}(k - L)\,\gamma\,\sigma_k(\mathbf{A})^p\Bigr)^{1/p}\,.$$
The first term is the head capture
`IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le`, the Schatten norm bounded by the
Frobenius norm. [BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there the case of large
singular values, with accuracies that are unspecified polynomials in $\varepsilon/d$, here with
explicit $\delta$, $\gamma$, $\theta$, $\kappa$. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_of_sq_singularValues_sub_le
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {A : Matrix m n 𝕜} {L k : ℕ} (hLk : L ≤ k) {δ γ θ κ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hκ : 1 ≤ κ)
    (hgap : ∀ h, h + 1 = L → singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hflat : singularValues A L ≤ κ * singularValues A k)
    (hhead : ∀ i < L, singularValues A i ^ 2 - δ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2)
    (hmid : ∀ i, L ≤ i → i < k → singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - P * A) ≤
      Real.sqrt (L * δ / θ) * singularValues A k +
        (schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
          p.toReal / 2 * κ ^ (p.toReal - 2) * ((k : ℝ) - L) * γ *
            singularValues A k ^ p.toReal) ^ p.toReal⁻¹ := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The tail-count form of the one-sided error, $2 \le p < \infty$**: let $\mathbf{P}$ be an
orthogonal projector and $\delta, \gamma, \kappa \ge 0$. Suppose the tail is flat,
$\sigma_k \le \kappa\,\sigma_{k+j}$; every $i < k$ has the deficit
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$;
and every large singular value, $i < k$ with $(1 + 1/(2p))\,\sigma_k < \sigma_i$, has the
smaller deficit
$\sigma_i(\mathbf{A})^2 - \delta\,\sigma_k(\mathbf{A})^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$.
Then
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{S_p} \le
\Bigl(k\sqrt{2(p + 1)\delta} +
\Bigl(1 + \frac{e\,p\,k\gamma\kappa^p}{2(j + 1)}\Bigr)^{1/p}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}\,.$$
The head index is chosen by `NLAlib.exists_le_singularValues_le_and_gap`; the factor $e$ bounds
$(1 + 1/p)^p$. [BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there with a head index that
need not exist and unspecified accuracies, for the two-sided output; here one-sided, with
explicit constants. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_mul_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {A : Matrix m n 𝕜} {k j : ℕ} {δ γ κ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hhead : ∀ i < k, (1 + 1 / (2 * p.toReal)) * singularValues A k < singularValues A i →
      singularValues A i ^ 2 - δ * singularValues A k ^ 2 ≤ singularValues (P * A) i ^ 2)
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - P * A) ≤
      (k * Real.sqrt (2 * (p.toReal + 1) * δ) +
        (1 + Real.exp 1 * (p.toReal / 2) * k * γ * κ ^ p.toReal / ((j : ℝ) + 1)) ^ p.toReal⁻¹) *
        schattenNorm p (A - truncatedSVD A k) := sorry

end NLAlib
