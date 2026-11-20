/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.SchattenPowers
public import NLAlib.Matrix.Norms.UnitarilyInvariant

/-!
# Pinching by a pair of projectors in Schatten norms

For orthogonal projectors $\mathbf{P}$ and $\mathbf{Q}$, of any ranks, the pinching
$\mathbf{A} \mapsto \mathbf{P}\mathbf{A}\mathbf{Q} +
(\mathbf{I} - \mathbf{P})\mathbf{A}(\mathbf{I} - \mathbf{Q})$ of a rectangular matrix does not
increase a unitarily invariant norm, and the $p$-th powers of the Schatten norms of its two
summands add. Together these give
$$\|\mathbf{P}\mathbf{A}\mathbf{Q}\|_{S_p}^p +
\|(\mathbf{I} - \mathbf{P})\mathbf{A}(\mathbf{I} - \mathbf{Q})\|_{S_p}^p \le
\|\mathbf{A}\|_{S_p}^p\,, \qquad 1 \le p < \infty\,,$$
the inequality behind the Schatten-norm analysis of low-rank approximations of the form
$\mathbf{A}\mathbf{Q}$ [BakshiClarksonWoodruff2022]. For $2 \le p < \infty$ there is a one-sided
form with no $\mathbf{Q}$.

## Main results

* `NLAlib.SymmetricGauge.matrixNorm_mul_mul_add_one_sub_mul_mul_one_sub_le`: the pinching does
  not increase a unitarily invariant norm.
* `NLAlib.schattenNorm_add_rpow_of_conjTranspose_mul_eq_zero_of_mul_conjTranspose_eq_zero`:
  $\|\mathbf{X} + \mathbf{Y}\|_{S_p}^p = \|\mathbf{X}\|_{S_p}^p + \|\mathbf{Y}\|_{S_p}^p$ for
  $\mathbf{X}^{\mathsf{H}}\mathbf{Y} = \mathbf{0}$ and $\mathbf{X}\mathbf{Y}^{\mathsf{H}} =
  \mathbf{0}$.
* `IsStarProjection.schattenNorm_mul_mul_rpow_add_le`: the two-sided inequality, $1 \le p$.
* `IsStarProjection.schattenNorm_mul_rpow_add_le`: the one-sided inequality, $2 \le p$.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- **Pinching by a pair of projectors**: for orthogonal projectors $\mathbf{P}$ ($m \times m$)
and $\mathbf{Q}$ ($n \times n$), an $m \times n$ matrix $\mathbf{A}$ and every unitarily
invariant norm $\|\cdot\|_{\Phi}$,
$$\|\mathbf{P}\mathbf{A}\mathbf{Q} +
(\mathbf{I} - \mathbf{P})\mathbf{A}(\mathbf{I} - \mathbf{Q})\|_{\Phi} \le
\|\mathbf{A}\|_{\Phi}\,.$$
The left side is the average of $\mathbf{A}$ and
$(2\mathbf{P} - \mathbf{I})\mathbf{A}(2\mathbf{Q} - \mathbf{I})$, and the two reflections are
unitary. [BakshiClarksonWoodruff2022, Fact 2.9]; there for Schatten norms and a square matrix cut
into square blocks of equal size, here for every unitarily invariant norm, a rectangular matrix
and projectors of any ranks. -/
theorem SymmetricGauge.matrixNorm_mul_mul_add_one_sub_mul_mul_one_sub_le (Φ : SymmetricGauge)
    {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (A : Matrix m n 𝕜) :
    Φ.matrixNorm (P * A * Q + (1 - P) * A * (1 - Q)) ≤ Φ.matrixNorm A := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **Schatten powers add on an orthogonal sum**: for $0 < p < \infty$ and $m \times n$ matrices
with $\mathbf{X}^{\mathsf{H}}\mathbf{Y} = \mathbf{0}$ and
$\mathbf{X}\mathbf{Y}^{\mathsf{H}} = \mathbf{0}$ (orthogonal column spaces and orthogonal row
spaces),
$$\|\mathbf{X} + \mathbf{Y}\|_{S_p}^p = \|\mathbf{X}\|_{S_p}^p + \|\mathbf{Y}\|_{S_p}^p\,.$$
The singular values of $\mathbf{X} + \mathbf{Y}$ are those of $\mathbf{X}$ and of $\mathbf{Y}$
together. The cases $p = 2$ and $p = \infty$ are
`NLAlib.frobNorm_add_sq_of_conjTranspose_mul_eq_zero` and the maximum of the spectral norms.
[BakshiClarksonWoodruff2022, Lemma 3.3]; used there in the proof, for a block diagonal matrix. -/
theorem schattenNorm_add_rpow_of_conjTranspose_mul_eq_zero_of_mul_conjTranspose_eq_zero
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {X Y : Matrix m n 𝕜} (h₁ : Xᴴ * Y = 0)
    (h₂ : X * Yᴴ = 0) :
    schattenNorm p (X + Y) ^ p.toReal =
      schattenNorm p X ^ p.toReal + schattenNorm p Y ^ p.toReal := sorry

/-- **Schatten norms under a pair of projectors**: for $1 \le p < \infty$, orthogonal projectors
$\mathbf{P}$ ($m \times m$) and $\mathbf{Q}$ ($n \times n$) and an $m \times n$ matrix
$\mathbf{A}$,
$$\|\mathbf{P}\mathbf{A}\mathbf{Q}\|_{S_p}^p +
\|(\mathbf{I} - \mathbf{P})\mathbf{A}(\mathbf{I} - \mathbf{Q})\|_{S_p}^p \le
\|\mathbf{A}\|_{S_p}^p\,.$$
[BakshiClarksonWoodruff2022, Lemma 3.3]; there for real matrices and two projectors of the same
rank $k$, here over $\Bbbk$ with no condition on the ranks. -/
theorem _root_.IsStarProjection.schattenNorm_mul_mul_rpow_add_le {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (A : Matrix m n 𝕜) :
    schattenNorm p (P * A * Q) ^ p.toReal + schattenNorm p ((1 - P) * A * (1 - Q)) ^ p.toReal ≤
      schattenNorm p A ^ p.toReal := sorry

omit [DecidableEq n] in
/-- **Schatten norms under one projector**: for $2 \le p < \infty$, an orthogonal projector
$\mathbf{P}$ ($m \times m$) and an $m \times n$ matrix $\mathbf{A}$,
$$\|\mathbf{P}\mathbf{A}\|_{S_p}^p + \|(\mathbf{I} - \mathbf{P})\mathbf{A}\|_{S_p}^p \le
\|\mathbf{A}\|_{S_p}^p\,.$$
For $p = 2$ it is the Pythagorean identity; for $p < 2$ the inequality fails. It is McCarthy's
inequality `Matrix.PosSemidef.re_trace_rpow_add_le` for
$\mathbf{A}^{\mathsf{H}}\mathbf{P}\mathbf{A}$ and
$\mathbf{A}^{\mathsf{H}}(\mathbf{I} - \mathbf{P})\mathbf{A}$ at the exponent $p/2 \ge 1$.
[BakshiClarksonWoodruff2022, Fact 2.7]; there for two matrices with orthogonal row spans or
orthogonal column spans, here for the two parts $\mathbf{P}\mathbf{A}$ and
$(\mathbf{I} - \mathbf{P})\mathbf{A}$ of one matrix. -/
theorem _root_.IsStarProjection.schattenNorm_mul_rpow_add_le {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P) (A : Matrix m n 𝕜) :
    schattenNorm p (P * A) ^ p.toReal + schattenNorm p ((1 - P) * A) ^ p.toReal ≤
      schattenNorm p A ^ p.toReal := sorry

end NLAlib
