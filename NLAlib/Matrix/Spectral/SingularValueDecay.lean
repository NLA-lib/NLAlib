/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Schatten
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Decay of singular values against the optimal Schatten error

Statements about the singular values $\sigma_0 \ge \sigma_1 \ge \cdots$ of one matrix and its
optimal rank-$k$ error $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}$: a tail count
(if $\sigma_{k+j}$ is not much smaller than $\sigma_k$, the optimal error is at least of order
$(j + 1)^{1/p}\sigma_k$), a comparison of the Frobenius tail with the Schatten tail for
$p \le 2$, and the choice of a head index $L \le k$ with a relative gap before it and a flat
spectrum after it.

## Main results

* `NLAlib.mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow`:
  $(j + 1)\,\sigma_{k+j}^p \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p$.
* `NLAlib.singularValues_rpow_mul_frobNorm_sub_truncatedSVD_sq_le`:
  $\sigma_k^{p-2}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le
  \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p$ for $1 \le p \le 2$.
* `NLAlib.exists_le_singularValues_le_and_gap`: a head index with a gap.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- **Tail count**: for $0 < p < \infty$ and all $k$, $j$,
$$(j + 1)\,\sigma_{k+j}(\mathbf{A})^p \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,,$$
since the $j + 1$ singular values $\sigma_k, \dots, \sigma_{k+j}$ of the tail are at least
$\sigma_{k+j}$. [BakshiClarksonWoodruff2022, proof of Theorem 3.1]; used there with the count of
the wide block in place of $j + 1$. -/
theorem mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ⊤) (A : Matrix m n 𝕜) (k j : ℕ) :
    ((j : ℝ) + 1) * singularValues A (k + j) ^ p.toReal ≤
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- The Frobenius tail against the Schatten tail: for $1 \le p \le 2$ and every $k$,
$$\sigma_k(\mathbf{A})^{p-2}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,,$$
termwise from $\sigma_i^2\,\sigma_k^{p-2} \le \sigma_i^p$ for $i \ge k$. When $\sigma_k = 0$ and
$p < 2$ the power $\sigma_k^{p-2}$ is $0$ in Lean and the inequality holds. -/
theorem singularValues_rpow_mul_frobNorm_sub_truncatedSVD_sq_le {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ (p.toReal - 2) * frobNorm (A - truncatedSVD A k) ^ 2 ≤
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **A head index with a gap**: for every matrix $\mathbf{A}$, every $k$ and real $p \ge 1$
there is $L \le k$ such that the spectrum is flat from $L$ to $k$,
$\sigma_L \le (1 + 1/p)\,\sigma_k$, and, when $L = h + 1 \ge 1$, the head is large and is
followed by a relative gap,
$$\Bigl(1 + \frac{1}{2p}\Bigr)\sigma_k < \sigma_h \qquad\text{and}\qquad
\sigma_L^2 \le \Bigl(1 - \frac{1}{2k(p + 1)}\Bigr)\sigma_h^2\,.$$
The index $L = 0$ is allowed and then says $\sigma_0 \le (1 + 1/p)\,\sigma_k$.
[BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there the largest index with a relative gap
$\varepsilon/d$ is taken, which exists only under a condition relating $k$, $p$, $\varepsilon$
and the dimension $d$; here the gap is $1/(2k(p + 1))$ on the squares and there is no
condition. -/
theorem exists_le_singularValues_le_and_gap (A : Matrix m n 𝕜) (k : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ L ≤ k, singularValues A L ≤ (1 + 1 / p) * singularValues A k ∧
      ∀ h, h + 1 = L → (1 + 1 / (2 * p)) * singularValues A k < singularValues A h ∧
        singularValues A L ^ 2 ≤ (1 - 1 / (2 * k * (p + 1))) * singularValues A h ^ 2 := sorry

end NLAlib
