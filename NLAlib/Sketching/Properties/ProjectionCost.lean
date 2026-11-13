/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.Sketching.Properties.MatrixMultiplication
public import NLAlib.Sketching.Properties.SubspaceEmbedding

/-!
# Projection-cost-preserving sketches

For $\mathbf{A} \in \Bbbk^{m \times n}$, a matrix $\tilde{\mathbf{A}} \in \Bbbk^{m \times l}$ with
the same rows, for instance a sketch $\mathbf{A}\mathbf{\Omega}$, is a *rank-$k$
projection-cost-preserving sketch* of $\mathbf{A}$ with constants $a$, $b$ when, up to one offset
$c \ge 0$ that does not depend on the projector, the cost
$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2$ of every orthogonal projector $\mathbf{P}$ of
rank at most $k$ is preserved:
$$a\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\tilde{\mathbf{A}} - \mathbf{P}\tilde{\mathbf{A}}\|_{\mathsf{F}}^2 + c \le
b\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2\,.$$
The literature's $\varepsilon$ is $a = 1 - \varepsilon$, $b = 1 + \varepsilon$ (two-sided) or
$a = 1$ (one-sided), written so. A projector that is nearly optimal for the sketch is then nearly
optimal for $\mathbf{A}$ (`NLAlib.IsProjectionCostPreserving.mul_frobNorm_sub_mul_sq_le`), which is
how a constrained low-rank problem (a set of rank-$k$ projectors, $k$-means) is solved on a sketch.
A subspace embedding of the row space of $\mathbf{A}$ gives one for every $k$ with offset $0$.

**The head–tail constructor.** For a frame $\mathbf{Z}$ whose residual
$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ is at most the optimal one,
a subspace embedding of $\operatorname{range}\mathbf{Z}$ (the head) and approximate matrix
multiplication of the tail $\mathbf{E}$ against itself and against $\mathbf{Z}$, with upper
Frobenius preservation of $\mathbf{E}$, give a projection-cost-preserving sketch whose dimension
does not depend on the rank of $\mathbf{A}$ (CEMMP's Lemma 6 at a frame split). Its random form,
the predicate `NLAlib.HasProjectionCostPreserving S A k a b δ μ` on a sketch $\mathbf{S}$ in the
Sketching orientation ($\tilde{\mathbf{A}} = \mathbf{A}\mathbf{S}^{\mathsf{H}}$), is reached by a
union bound over the four events, and from an OSE plus the JL moment property for every $\mathbf{A}$
over $\mathbb{R}$. The family statements (Gaussian, sub-Gaussian, CountSketch) are in the family
files.

Degenerate cases: for $a \le 0$ the lower half holds automatically and the consequence is vacuous;
at $k = 0$ the only projector is $\mathbf{0}$ and the predicate is a scaled preservation of
$\|\mathbf{A}\|_{\mathsf{F}}^2$; for $k \ge \lvert m \rvert$ the projector $\mathbf{I}$ forces
$c = 0$; at $k = 0$ the head is void and only the upper Frobenius preservation of $\mathbf{A}$
remains, which is why the family sizes carry $d + 1$.

## Main definitions

* `NLAlib.IsProjectionCostPreserving A Ã k a b`: the predicate.
* `NLAlib.HasProjectionCostPreserving S A k a b δ μ`: its tail form for a random sketch.
* `NLAlib.projectionCostTailDim`: the rows of the tail events at the family budgets, at
  present <!-- value projectionCostTailDim v d \varepsilon \delta -->
  $384 \cdot v (d + 1)/(\varepsilon^2 \delta)$.

## Main results

* `NLAlib.IsProjectionCostPreserving.mono`: monotonicity in the rank and the constants.
* `NLAlib.IsSubspaceEmbedding.isProjectionCostPreserving`: a subspace embedding of the row space
  is a projection-cost-preserving sketch for every rank.
* `NLAlib.IsProjectionCostPreserving.mul_frobNorm_sub_mul_sq_le`: constrained low-rank
  approximation through the sketch.
* `NLAlib.IsSubspaceEmbedding.isProjectionCostPreserving_of_hasOrthonormalCols`: the head–tail
  constructor.
* `NLAlib.HasProjectionCostPreserving.mono`,
  `NLAlib.hasProjectionCostPreserving_conjTranspose_iff`: monotonicity and the test-matrix
  orientation.
* `NLAlib.HasSubspaceEmbedding.hasProjectionCostPreserving`,
  `NLAlib.IsObliviousSubspaceEmbedding.hasProjectionCostPreserving`: the row-space constructors on
  the event.
* `NLAlib.HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasOrthonormalCols`: the head–tail
  constructor on the event, by a union bound.
* `NLAlib.IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment`: an OSE plus the
  JL moment property, over $\mathbb{R}$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- $\tilde{\mathbf{A}}$ is a **rank-$k$ projection-cost-preserving sketch** of $\mathbf{A}$ with
constants $a$, $b$: for some offset $c \ge 0$, independent of the projector, every orthogonal
projector $\mathbf{P}$ of rank at most $k$ has
$$a\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\tilde{\mathbf{A}} - \mathbf{P}\tilde{\mathbf{A}}\|_{\mathsf{F}}^2 + c \le
b\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2\,.$$
The two-sided form is $a = 1 - \varepsilon$, $b = 1 + \varepsilon$; the one-sided form is $a = 1$.
The sketch $\tilde{\mathbf{A}}$ is any matrix with the rows of $\mathbf{A}$, not only
$\mathbf{A}\mathbf{\Omega}$.
[CohenElderMuscoMuscoPersu2015, Definitions 1 and 2]; there over $\mathbb{R}$, with $\varepsilon$,
and for projectors of rank exactly $k$; here constants $a$, $b$, any `RCLike` field, rank at most
$k$, so that projectors of smaller rank (a rank-deficient truncation) are covered. -/
def IsProjectionCostPreserving (A : Matrix m n 𝕜) (Ã : Matrix m l 𝕜) (k : ℕ) (a b : ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ P : Matrix m m 𝕜, IsStarProjection P → P.rank ≤ k →
    a * frobNorm (A - P * A) ^ 2 ≤ frobNorm (Ã - P * Ã) ^ 2 + c ∧
      frobNorm (Ã - P * Ã) ^ 2 + c ≤ b * frobNorm (A - P * A) ^ 2

/-- A projection-cost-preserving sketch of rank $k$ with constants $a$, $b$ is one of every rank
$k' \le k$ with every $a' \le a$ and $b' \ge b$. -/
theorem IsProjectionCostPreserving.mono {A : Matrix m n 𝕜} {Ã : Matrix m l 𝕜} {k k' : ℕ}
    {a a' b b' : ℝ} (h : IsProjectionCostPreserving A Ã k a b) (hk : k' ≤ k) (ha : a' ≤ a)
    (hb : b ≤ b') : IsProjectionCostPreserving A Ã k' a' b' := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun P hP hPk => ?_⟩
  obtain ⟨h₁, h₂⟩ := h P hP (hPk.trans hk)
  have hx := sq_nonneg (frobNorm (A - P * A))
  exact ⟨(mul_le_mul_of_nonneg_right ha hx).trans h₁,
    h₂.trans (mul_le_mul_of_nonneg_right hb hx)⟩

/-- A subspace embedding for $\operatorname{range}\mathbf{U}$ bounds the squared Frobenius norm of
every $\mathbf{U}\mathbf{C}$ from both sides, column by column. -/
private theorem frobNorm_sq_le_and_le_of_isSubspaceEmbedding {q : Type*} [Fintype q]
    {S : Matrix l n 𝕜} {U : Matrix n m 𝕜} {a b : ℝ} (h : IsSubspaceEmbedding S U a b)
    (C : Matrix m q 𝕜) :
    a * frobNorm (U * C) ^ 2 ≤ frobNorm (S * (U * C)) ^ 2 ∧
      frobNorm (S * (U * C)) ^ 2 ≤ b * frobNorm (U * C) ^ 2 := by
  have hv := isSubspaceEmbedding_iff_forall_mem_range.mp h
  have hcol : ∀ j, (U * C).col j ∈ LinearMap.range U.mulVecLin := fun j =>
    ⟨C.col j, by
      ext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.col_apply, Matrix.mul_apply,
        dotProduct]⟩
  have hS : ∀ j, (S * (U * C)).col j = S *ᵥ (U * C).col j := fun j => by
    ext i
    simp only [Matrix.mulVec, Matrix.col_apply, Matrix.mul_apply, dotProduct]
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum, Finset.mul_sum]
  simp only [hS]
  exact ⟨Finset.sum_le_sum fun j _ => (hv _ (hcol j)).1,
    Finset.sum_le_sum fun j _ => (hv _ (hcol j)).2⟩

/-- **A subspace embedding of the row space is a projection-cost-preserving sketch** for every
rank, with offset $0$: if $\mathbf{\Omega}^{\mathsf{H}}$ is a subspace embedding for
$\operatorname{range}\mathbf{A}^{\mathsf{H}}$ with constants $a$, $b$, then
$\mathbf{A}\mathbf{\Omega}$ is a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with
the same constants, for every $k$. The bound holds for every left factor, not only the complement
of a projector, which is why $k$ is free; the embedding dimension is at least
$\operatorname{rank}\mathbf{A}$.
[CohenElderMuscoMuscoPersu2015, §1.1]; [Woodruff2014, proof of Theorem 61]; there a remark and a
proof step, in Woodruff transposed (his column space of $\mathbf{A}$ is the row space here); here
every $k$, offset $0$ and the embedding's constants carried over. -/
theorem IsSubspaceEmbedding.isProjectionCostPreserving {A : Matrix m n 𝕜} {X : Matrix n l 𝕜}
    {a b : ℝ} (h : IsSubspaceEmbedding Xᴴ Aᴴ a b) (k : ℕ) :
    IsProjectionCostPreserving A (A * X) k a b := by
  classical
  refine ⟨0, le_rfl, fun P _ _ => ?_⟩
  have e₁ : A - P * A = (Aᴴ * (1 - P)ᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.one_mul]
  have e₂ : A * X - P * (A * X) = (Xᴴ * (Aᴴ * (1 - P)ᴴ))ᴴ := by
    rw [Matrix.conjTranspose_mul, ← e₁, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_assoc]
  rw [add_zero, e₁, e₂, frobNorm_conjTranspose, frobNorm_conjTranspose]
  exact frobNorm_sq_le_and_le_of_isSubspaceEmbedding h _

/-! ### The head–tail constructor -/

section HeadTail

variable {r : Type*} [Fintype r] [DecidableEq r]

/-- The sketch cost of a projector at a frame split: with
$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$, the head part, the tail
cost, the Frobenius distortion of the tail, the projector against the tail Gram error, and the
cross term. -/
private theorem frobNorm_mul_sub_mul_sq_eq {A : Matrix m n 𝕜} {X : Matrix n l 𝕜}
    {Z : Matrix n r 𝕜} (hZ : HasOrthonormalCols Z) {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    frobNorm (A * X - P * (A * X)) ^ 2 =
      frobNorm ((A * Z - P * (A * Z)) * (Zᴴ * X)) ^ 2 +
        frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) ^ 2 +
        (frobNorm ((A - A * Z * Zᴴ) * X) ^ 2 - frobNorm (A - A * Z * Zᴴ) ^ 2) -
        frobInner P ((A - A * Z * Zᴴ) * X * Xᴴ * (A - A * Z * Zᴴ)ᴴ -
          (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) +
        2 * frobInner (A * Z - P * (A * Z))
          ((A - A * Z * Zᴴ) * X * Xᴴ * Z - (A - A * Z * Zᴴ) * Z) := by
  have hdec : A * X - P * (A * X) =
      (A * Z - P * (A * Z)) * (Zᴴ * X) + (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) * X := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have hEZ : (A - A * Z * Zᴴ) * Z = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (A * Z), hZ.conjTranspose_mul_self, Matrix.mul_one,
      sub_self]
  generalize A - A * Z * Zᴴ = E at hdec hEZ ⊢
  set R₁ := A * Z - P * (A * Z) with hR₁
  have htail : frobNorm ((E - P * E) * X) ^ 2 = frobNorm (E * X) ^ 2 -
      frobInner P (E * X * Xᴴ * Eᴴ) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc P, hP.frobNorm_sub_mul_sq_eq_sub_frobInner,
      Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
  have hr₂ := hP.frobNorm_sub_mul_sq_eq_sub_frobInner E
  have hcross : frobInner (R₁ * (Zᴴ * X)) ((E - P * E) * X) =
      frobInner R₁ (E * X * Xᴴ * Z - E * Z) := by
    rw [frobInner_mul_right, hEZ, sub_zero, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc P,
      Matrix.mul_assoc P, hR₁, hP.frobInner_sub_mul_sub_mul]
    simp only [Matrix.mul_assoc]
  rw [hdec, frobNorm_add_sq, hcross, htail, hr₂, frobInner_sub_right P]
  ring

/-- The real inequalities behind the head–tail constructor. -/
private theorem head_tail_le {a b εw εχ εF sk x r₁ t e H D pw cr W χ : ℝ} (ha : a ≤ 1)
    (hb : 1 ≤ b) (hεw : 0 ≤ εw) (hεχ : 0 ≤ εχ) (hεF : 0 ≤ εF) (hsk : 0 ≤ sk) (hr₁ : 0 ≤ r₁)
    (ht : 0 ≤ t)
    (he : 0 ≤ e) (hx : x ^ 2 = r₁ ^ 2 + t) (hx0 : 0 ≤ x) (hex : e ≤ x)
    (hH₁ : a * r₁ ^ 2 ≤ H) (hH₂ : H ≤ b * r₁ ^ 2) (hD : D ≤ εF * e ^ 2)
    (hpw : |pw| ≤ sk * W) (hW : W ≤ εw * e ^ 2) (hcr : |cr| ≤ r₁ * χ) (hχ : χ ≤ εχ * e) :
    (a - sk * εw - 2 * εχ) * x ^ 2 ≤ H + t + D - pw + 2 * cr + max 0 (-D) ∧
      H + t + D - pw + 2 * cr + max 0 (-D) ≤ (b + sk * εw + 2 * εχ + εF) * x ^ 2 := by
  have hr₁x : r₁ ≤ x := by nlinarith
  have hDc₀ : 0 ≤ D + max 0 (-D) := by
    rcases le_total 0 D with h | h
    · rw [max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith)]; linarith
  have hDc₁ : D + max 0 (-D) ≤ εF * x ^ 2 := by
    have hex2 : e ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ he hex 2
    have h1 : εF * e ^ 2 ≤ εF * x ^ 2 := mul_le_mul_of_nonneg_left hex2 hεF
    rcases le_total 0 D with h | h
    · rw [max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith)]; nlinarith
  have hpw' : |pw| ≤ sk * εw * x ^ 2 := by
    have hex2 : e ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ he hex 2
    calc |pw| ≤ sk * W := hpw
      _ ≤ sk * (εw * e ^ 2) := mul_le_mul_of_nonneg_left hW hsk
      _ ≤ sk * (εw * x ^ 2) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hex2 hεw) hsk
      _ = sk * εw * x ^ 2 := by ring
  have hcr' : |cr| ≤ εχ * x ^ 2 := by
    calc |cr| ≤ r₁ * χ := hcr
      _ ≤ r₁ * (εχ * e) := mul_le_mul_of_nonneg_left hχ hr₁
      _ ≤ x * (εχ * x) := mul_le_mul hr₁x (mul_le_mul_of_nonneg_left hex hεχ)
          (mul_nonneg hεχ he) hx0
      _ = εχ * x ^ 2 := by ring
  have h1 := neg_abs_le pw
  have h2 := le_abs_self pw
  have h3 := neg_abs_le cr
  have h4 := le_abs_self cr
  have h5 : a * t ≤ t := by nlinarith
  have h6 : t ≤ b * t := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- **Projection-cost preservation from a head embedding and tail approximate
multiplication.** Let $\mathbf{Z}$ have orthonormal columns and
$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ with
$\|\mathbf{E}\|_{\mathsf{F}} \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$;
let $\mathbf{\Omega}^{\mathsf{H}}$ be a subspace embedding for $\operatorname{range}\mathbf{Z}$ with
constants $a \le 1 \le b$, and for $\varepsilon_w, \varepsilon_\chi, \varepsilon_{\mathrm{F}} \ge 0$
$$\begin{aligned}
\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}} &\le \varepsilon_w\|\mathbf{E}\|_{\mathsf{F}}^2,\\
\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\|_{\mathsf{F}} &\le \varepsilon_\chi\|\mathbf{E}\|_{\mathsf{F}},\\
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2 &\le
(1 + \varepsilon_{\mathrm{F}})\|\mathbf{E}\|_{\mathsf{F}}^2\,.
\end{aligned}$$
Then $\mathbf{A}\mathbf{\Omega}$ is a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$
with constants $a - \sqrt{k}\,\varepsilon_w - 2\varepsilon_\chi$ and
$b + \sqrt{k}\,\varepsilon_w + 2\varepsilon_\chi + \varepsilon_{\mathrm{F}}$, with offset
$\max\{0, \|\mathbf{E}\|_{\mathsf{F}}^2 - \|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2\}$. Only the
upper half of the tail's Frobenius preservation is needed, and the frame may be wider than $k$
(at $\mathbf{Z} = \mathbf{I}$ this is `NLAlib.IsSubspaceEmbedding.isProjectionCostPreserving`).
[CohenElderMuscoMuscoPersu2015, Lemma 6 and proof of Theorem 12]; there $\mathbf{Z} = \mathbf{V}_k$,
error budgets summing to $\varepsilon$, over $\mathbb{R}$, with the cross terms through a
semi-inner product; here any frame whose residual is at most the optimal one (their Lemma 10 uses
width $2k$), constants $a$, $b$, any `RCLike` field, the cross term by Cauchy–Schwarz.
Result: pcp-sufficient-conditions -/
theorem IsSubspaceEmbedding.isProjectionCostPreserving_of_hasOrthonormalCols
    {A : Matrix m n 𝕜} {X : Matrix n l 𝕜} {Z : Matrix n r 𝕜} {a b εw εχ εF : ℝ} {k : ℕ}
    (h : IsSubspaceEmbedding Xᴴ Z a b) (hZ : HasOrthonormalCols Z) (ha : a ≤ 1) (hb : 1 ≤ b)
    (hZA : frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A k))
    (hεw : 0 ≤ εw) (hεχ : 0 ≤ εχ) (hεF : 0 ≤ εF)
    (hw : frobNorm ((A - A * Z * Zᴴ) * X * Xᴴ * (A - A * Z * Zᴴ)ᴴ -
        (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) ≤ εw * frobNorm (A - A * Z * Zᴴ) ^ 2)
    (hχ : frobNorm ((A - A * Z * Zᴴ) * X * Xᴴ * Z - (A - A * Z * Zᴴ) * Z) ≤
        εχ * frobNorm (A - A * Z * Zᴴ))
    (hF : frobNorm ((A - A * Z * Zᴴ) * X) ^ 2 ≤ (1 + εF) * frobNorm (A - A * Z * Zᴴ) ^ 2) :
    IsProjectionCostPreserving A (A * X) k (a - √(k : ℝ) * εw - 2 * εχ)
      (b + √(k : ℝ) * εw + 2 * εχ + εF) := by
  refine ⟨max 0 (-(frobNorm ((A - A * Z * Zᴴ) * X) ^ 2 - frobNorm (A - A * Z * Zᴴ) ^ 2)),
    le_max_left _ _, fun P hP hPk => ?_⟩
  have hhead := frobNorm_sq_le_and_le_of_isSubspaceEmbedding h (A * Z - P * (A * Z))ᴴ
  have e₁ : frobNorm (Z * (A * Z - P * (A * Z))ᴴ) = frobNorm (A * Z - P * (A * Z)) := by
    rw [hZ.frobNorm_mul_left, frobNorm_conjTranspose]
  have e₂ : frobNorm (Xᴴ * (Z * (A * Z - P * (A * Z))ᴴ)) =
      frobNorm ((A * Z - P * (A * Z)) * (Zᴴ * X)) := by
    rw [← frobNorm_conjTranspose]
    congr 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e₁, e₂] at hhead
  have hEY : frobNorm (A - truncatedSVD A k) ≤ frobNorm (A - P * A) :=
    frobNorm_sub_truncatedSVD_le_of_rank_le A ((Matrix.rank_mul_le_left P A).trans hPk)
  rw [frobNorm_mul_sub_mul_sq_eq hZ hP]
  exact head_tail_le ha hb hεw hεχ hεF (Real.sqrt_nonneg _) (frobNorm_nonneg _) (sq_nonneg _)
    (frobNorm_nonneg _) (hZ.frobNorm_sub_mul_sq_eq_add A P) (frobNorm_nonneg _)
    (hZA.trans hEY) hhead.1 hhead.2 (by linarith)
    (hP.abs_frobInner_le_sqrt_mul_frobNorm hPk _) hw (abs_frobInner_le _ _) hχ

end HeadTail

/-- **Constrained low-rank approximation through a projection-cost-preserving sketch.** If
$\mathbf{P}$ is $\gamma$-optimal for the sketch against a competitor $\mathbf{P}'$, both orthogonal
projectors of rank at most $k$ and $\gamma \ge 1$, then it is $\gamma b / a$-optimal for
$\mathbf{A}$:
$$a\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\gamma\, b\,\|\mathbf{A} - \mathbf{P}'\mathbf{A}\|_{\mathsf{F}}^2\,.$$
In the two-sided form the factor is $\gamma(1+\varepsilon)/(1-\varepsilon)$. The multiplied form
needs no $a > 0$ and is vacuous for $a \le 0$.
[CohenElderMuscoMuscoPersu2015, Lemmas 3 and 4]; there for the minimizer over a set of rank-$k$
projectors and the factors $(1+\varepsilon)/(1-\varepsilon)$ or $1 + \varepsilon$; here any
competitor and constants $a$, $b$.
Result: projection-cost-preserving-sketch -/
theorem IsProjectionCostPreserving.mul_frobNorm_sub_mul_sq_le {A : Matrix m n 𝕜}
    {Ã : Matrix m l 𝕜} {k : ℕ} {a b : ℝ} (h : IsProjectionCostPreserving A Ã k a b)
    {P P' : Matrix m m 𝕜} (hP : IsStarProjection P) (hPk : P.rank ≤ k)
    (hP' : IsStarProjection P') (hP'k : P'.rank ≤ k) {γ : ℝ} (hγ : 1 ≤ γ)
    (hopt : frobNorm (Ã - P * Ã) ^ 2 ≤ γ * frobNorm (Ã - P' * Ã) ^ 2) :
    a * frobNorm (A - P * A) ^ 2 ≤ γ * b * frobNorm (A - P' * A) ^ 2 := by
  obtain ⟨c, hc, h⟩ := h
  have h₁ := (h P hP hPk).1
  have h₂ := mul_le_mul_of_nonneg_left (h P' hP' hP'k).2 (zero_le_one.trans hγ)
  have h₃ := mul_nonneg (sub_nonneg.mpr hγ) hc
  linarith

/-! ### Random projection-cost-preserving sketches -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The random sketch $\mathbf{S}$ is a **rank-$k$ projection-cost-preserving sketch for
$\mathbf{A}$ with probability $1 - \delta$**: the event that $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ is
not a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with constants $a$, $b$
(`NLAlib.IsProjectionCostPreserving`) has probability at most $\delta$. The offset may depend on
$\omega$. With a test matrix $\mathbf{\Omega}$ the sketch is $\mathbf{\Omega}^{\mathsf{H}}$
(`NLAlib.hasProjectionCostPreserving_conjTranspose_iff`). No measurability is assumed: the
predicate bounds the real measure of an arbitrary set.
[CohenElderMuscoMuscoPersu2015, Definition 1] for the predicate at each $\omega$;
[CohenElderMuscoMuscoPersu2015, Theorem 12] for the form "with probability at least
$1 - O(\delta)$", there with error $O(\varepsilon)$. -/
def HasProjectionCostPreserving (S : Ω → Matrix l n 𝕜) (A : Matrix m n 𝕜) (k : ℕ) (a b δ : ℝ)
    (μ : Measure Ω) : Prop :=
  μ.real {ω | ¬ IsProjectionCostPreserving A (A * (S ω)ᴴ) k a b} ≤ δ

/-- A random projection-cost-preserving sketch of rank $k$ is one of every rank $k' \le k$, with
weaker constants and a larger failure probability. -/
theorem HasProjectionCostPreserving.mono [IsFiniteMeasure μ] {S : Ω → Matrix l n 𝕜}
    {A : Matrix m n 𝕜} {k k' : ℕ} {a a' b b' δ δ' : ℝ}
    (h : HasProjectionCostPreserving S A k a b δ μ) (hk : k' ≤ k) (ha : a' ≤ a) (hb : b ≤ b')
    (hδ : δ ≤ δ') : HasProjectionCostPreserving S A k' a' b' δ' μ :=
  (measureReal_mono (Set.ofPred_subset_ofPred.2 fun _ hω h' => hω (h'.mono hk ha hb))).trans
    (h.trans hδ)

/-- A test matrix $\mathbf{\Omega}$ makes $\mathbf{\Omega}^{\mathsf{H}}$ a
projection-cost-preserving sketch exactly when $\mathbf{A}\mathbf{\Omega}$ fails to be one with
probability at most $\delta$: the form LowRank consumers rewrite with. -/
theorem hasProjectionCostPreserving_conjTranspose_iff {X : Ω → Matrix n l 𝕜}
    {A : Matrix m n 𝕜} {k : ℕ} {a b δ : ℝ} :
    HasProjectionCostPreserving (fun ω => (X ω)ᴴ) A k a b δ μ ↔
      μ.real {ω | ¬ IsProjectionCostPreserving A (A * X ω) k a b} ≤ δ := by
  simp only [HasProjectionCostPreserving, Matrix.conjTranspose_conjTranspose]

/-- With no columns every sketch is a projection-cost-preserving sketch. If $n$ is empty then
$\mathbf{A} = \mathbf{0}$, so $\mathbf{A}\mathbf{S}(\omega)^{\mathsf{H}} = \mathbf{0}$ and the
rank-$d$ property holds with offset $c = 0$ for every sketch $\mathbf{S}$, constants $a$, $b$
and $\delta \ge 0$:
$\mu\{\omega : \mathbf{A}\mathbf{S}(\omega)^{\mathsf{H}}\text{ fails}\} = 0 \le \delta$. It
disposes of the degenerate case in proofs that otherwise need a column. -/
theorem hasProjectionCostPreserving_of_isEmpty [IsEmpty n] (S : Ω → Matrix l n 𝕜)
    (A : Matrix m n 𝕜) (d : ℕ) (a b : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    HasProjectionCostPreserving S A d a b δ μ := by
  have hA : A = 0 := Matrix.ext fun _ j => isEmptyElim j
  have e : {ω | ¬ IsProjectionCostPreserving A (A * (S ω)ᴴ) d a b} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun ω hω => hω ⟨0, le_rfl, fun P _ _ => ?_⟩
    simp only [hA, Matrix.zero_mul, Matrix.mul_zero, sub_self, frobNorm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, le_refl, and_self]
  unfold HasProjectionCostPreserving
  rw [e, measureReal_empty]
  exact hδ

/-- **A random subspace embedding of the row space is a projection-cost-preserving sketch** for
every rank, with the same constants and failure probability:
`NLAlib.IsSubspaceEmbedding.isProjectionCostPreserving` on the event. Its dimension is at least
$\operatorname{rank}\mathbf{A}$. [CohenElderMuscoMuscoPersu2015, §1.1];
[Woodruff2014, proof of Theorem 61]; there a remark and a proof step, here on the event. -/
theorem HasSubspaceEmbedding.hasProjectionCostPreserving [IsFiniteMeasure μ]
    {S : Ω → Matrix l n 𝕜} {A : Matrix m n 𝕜} {a b δ : ℝ}
    (h : HasSubspaceEmbedding S Aᴴ a b δ μ) (k : ℕ) : HasProjectionCostPreserving S A k a b δ μ :=
  (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' => hω
    (IsSubspaceEmbedding.isProjectionCostPreserving
      (by rwa [Matrix.conjTranspose_conjTranspose]) k))).trans h

open scoped ComplexOrder in
/-- **An OSE for dimension $d \ge \operatorname{rank}\mathbf{A}$ is a projection-cost-preserving
sketch of $\mathbf{A}$** for every rank, with the same constants and failure probability. Every
family with an OSE is one at dimension $O(\operatorname{rank}\mathbf{A})$ through this; the
head–tail constructor
`NLAlib.IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment` removes the rank.
[CohenElderMuscoMuscoPersu2015, §1.1]; [Woodruff2014, proof of Theorem 61]. -/
theorem IsObliviousSubspaceEmbedding.hasProjectionCostPreserving [IsFiniteMeasure μ]
    {S : Ω → Matrix l n 𝕜} {d : ℕ} {a b δ : ℝ}
    (h : IsObliviousSubspaceEmbedding S d a b δ μ) {A : Matrix m n 𝕜} (hA : A.rank ≤ d) (k : ℕ) :
    HasProjectionCostPreserving S A k a b δ μ :=
  (h.hasSubspaceEmbedding (by rwa [Matrix.rank_conjTranspose])).hasProjectionCostPreserving k

variable {r : Type*} [Fintype r] [DecidableEq r]

/-- **The head–tail constructor, tail form**: under the frame hypotheses of
`NLAlib.IsSubspaceEmbedding.isProjectionCostPreserving_of_hasOrthonormalCols`, with
$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$, if the head embedding fails
with probability $\delta_1$ and the three tail conditions
$$\begin{aligned}
\|\mathbf{E}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}} &\le \varepsilon_w\|\mathbf{E}\|_{\mathsf{F}}^2,\\
\|\mathbf{E}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{Z} - \mathbf{E}\mathbf{Z}\|_{\mathsf{F}}
&\le \varepsilon_\chi\|\mathbf{E}\|_{\mathsf{F}},\\
\|\mathbf{S}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}^2 &\le
(1 + \varepsilon_{\mathrm{F}})\|\mathbf{E}\|_{\mathsf{F}}^2
\end{aligned}$$
fail with probabilities $\delta_2$, $\delta_3$, $\delta_4$, then $\mathbf{S}$ is a rank-$k$
projection-cost-preserving sketch of $\mathbf{A}$ with constants
$a - \sqrt{k}\,\varepsilon_w - 2\varepsilon_\chi$ and
$b + \sqrt{k}\,\varepsilon_w + 2\varepsilon_\chi + \varepsilon_{\mathrm{F}}$, except with
probability $\delta_1 + \delta_2 + \delta_3 + \delta_4$ (union bound). The interface for a family
with its own approximate-multiplication tails, over any field. [CohenElderMuscoMuscoPersu2015,
proof of Theorem 12].
Result: pcp-sufficient-conditions -/
theorem HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasOrthonormalCols
    [IsFiniteMeasure μ] {S : Ω → Matrix l n 𝕜} {Z : Matrix n r 𝕜} {a b δ₁ δ₂ δ₃ δ₄ εw εχ εF : ℝ}
    (h : HasSubspaceEmbedding S Z a b δ₁ μ) (hZ : HasOrthonormalCols Z) (ha : a ≤ 1) (hb : 1 ≤ b)
    {A : Matrix m n 𝕜} {k : ℕ} (hZA : frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A k))
    (hεw : 0 ≤ εw) (hεχ : 0 ≤ εχ) (hεF : 0 ≤ εF)
    (hw : μ.real {ω | εw * frobNorm (A - A * Z * Zᴴ) ^ 2 < frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ *
        S ω * (A - A * Z * Zᴴ)ᴴ - (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)} ≤ δ₂)
    (hχ : μ.real {ω | εχ * frobNorm (A - A * Z * Zᴴ) <
        frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ * S ω * Z - (A - A * Z * Zᴴ) * Z)} ≤ δ₃)
    (hF : μ.real {ω | (1 + εF) * frobNorm (A - A * Z * Zᴴ) ^ 2 <
        frobNorm (S ω * (A - A * Z * Zᴴ)ᴴ) ^ 2} ≤ δ₄) :
    HasProjectionCostPreserving S A k (a - √(k : ℝ) * εw - 2 * εχ)
      (b + √(k : ℝ) * εw + 2 * εχ + εF) (δ₁ + δ₂ + δ₃ + δ₄) μ := by
  have hsub : {ω | ¬ IsProjectionCostPreserving A (A * (S ω)ᴴ) k (a - √(k : ℝ) * εw - 2 * εχ)
      (b + √(k : ℝ) * εw + 2 * εχ + εF)} ⊆
      (({ω | ¬ IsSubspaceEmbedding (S ω) Z a b} ∪
        {ω | εw * frobNorm (A - A * Z * Zᴴ) ^ 2 < frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ *
          S ω * (A - A * Z * Zᴴ)ᴴ - (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)}) ∪
        {ω | εχ * frobNorm (A - A * Z * Zᴴ) <
          frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ * S ω * Z - (A - A * Z * Zᴴ) * Z)}) ∪
        {ω | (1 + εF) * frobNorm (A - A * Z * Zᴴ) ^ 2 <
          frobNorm (S ω * (A - A * Z * Zᴴ)ᴴ) ^ 2} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt] at hnot hω
    obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hnot
    refine hω (IsSubspaceEmbedding.isProjectionCostPreserving_of_hasOrthonormalCols
      (by rwa [Matrix.conjTranspose_conjTranspose]) hZ ha hb hZA hεw hεχ hεF ?_ ?_ ?_)
    · rwa [Matrix.conjTranspose_conjTranspose]
    · rwa [Matrix.conjTranspose_conjTranspose]
    · rwa [← frobNorm_conjTranspose ((A - A * Z * Zᴴ) * (S ω)ᴴ), Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
  refine (measureReal_mono hsub).trans ?_
  have u₁ := measureReal_union_le (μ := μ) ({ω | ¬ IsSubspaceEmbedding (S ω) Z a b} ∪
    {ω | εw * frobNorm (A - A * Z * Zᴴ) ^ 2 < frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ *
      S ω * (A - A * Z * Zᴴ)ᴴ - (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)} ∪
    {ω | εχ * frobNorm (A - A * Z * Zᴴ) <
      frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ * S ω * Z - (A - A * Z * Zᴴ) * Z)})
    {ω | (1 + εF) * frobNorm (A - A * Z * Zᴴ) ^ 2 < frobNorm (S ω * (A - A * Z * Zᴴ)ᴴ) ^ 2}
  have u₂ := measureReal_union_le (μ := μ) ({ω | ¬ IsSubspaceEmbedding (S ω) Z a b} ∪
    {ω | εw * frobNorm (A - A * Z * Zᴴ) ^ 2 < frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ *
      S ω * (A - A * Z * Zᴴ)ᴴ - (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)})
    {ω | εχ * frobNorm (A - A * Z * Zᴴ) <
      frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ * S ω * Z - (A - A * Z * Zᴴ) * Z)}
  have u₃ := measureReal_union_le (μ := μ) {ω | ¬ IsSubspaceEmbedding (S ω) Z a b}
    {ω | εw * frobNorm (A - A * Z * Zᴴ) ^ 2 < frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ *
      S ω * (A - A * Z * Zᴴ)ᴴ - (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)}
  unfold HasSubspaceEmbedding at h
  linarith

/-- A frame with at most $k$ columns has Frobenius norm at most $\sqrt{k}$. -/
private theorem frobNorm_le_sqrt_of_hasOrthonormalCols {Z : Matrix n r 𝕜}
    (hZ : HasOrthonormalCols Z) {k : ℕ} (hrk : Fintype.card r ≤ k) : frobNorm Z ≤ √(k : ℝ) := by
  rw [← Real.sqrt_sq (frobNorm_nonneg Z), hZ.frobNorm_sq]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hrk)

/-- A head embedding, approximate multiplication of the residual against itself and the frame,
and a JL moment for scalar Frobenius preservation give a projection-cost-preserving sketch.
For a frame with at most $k$ columns the cross-error is amplified by at most $\sqrt{k}$.
This shared bridge is valid over $\Bbbk$: the AMM hypotheses can come from any sketch family,
including the real JL-moment route and the complex CountSketch route.
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12]. -/
theorem HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasApproximateMatrixMultiplication
    [IsFiniteMeasure μ] {S : Ω → Matrix l n 𝕜} {k : ℕ} {a b δ ε δ' p : ℝ}
    {A : Matrix m n 𝕜} {Z : Matrix n r 𝕜} (h : HasSubspaceEmbedding S Z a b δ μ)
    (hJL : HasJLMoment S ε δ' p μ) (hS : AEMeasurable S μ)
    (ha : a ≤ 1) (hb : 1 ≤ b) (hε : 0 < ε) (hp : 1 ≤ p) (hδ' : 0 ≤ δ')
    (hZ : HasOrthonormalCols Z)
    (hZA : frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A k))
    (hrk : Fintype.card r ≤ k)
    (hAA : HasApproximateMatrixMultiplication S (A - A * Z * Zᴴ)ᴴ
      (A - A * Z * Zᴴ)ᴴ ε δ' μ)
    (hAZ : HasApproximateMatrixMultiplication S (A - A * Z * Zᴴ)ᴴ Z ε δ' μ) :
    HasProjectionCostPreserving S A k (a - 3 * √(k : ℝ) * ε) (b + 3 * √(k : ℝ) * ε + ε)
      (δ + 3 * δ') μ := by
  have hZF := frobNorm_le_sqrt_of_hasOrthonormalCols hZ hrk
  have key := h.hasProjectionCostPreserving_of_hasOrthonormalCols (εw := ε) (εχ := √(k : ℝ) * ε)
    (εF := ε) (δ₂ := δ') (δ₃ := δ') (δ₄ := δ') hZ ha hb hZA hε.le (by positivity) hε.le ?_ ?_ ?_
  · exact key.mono le_rfl (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
  · refine (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => ?_)).trans hAA
    simp only [Matrix.conjTranspose_conjTranspose, frobNorm_conjTranspose]
    simpa only [mul_assoc, ← sq] using hω
  · refine (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => ?_)).trans hAZ
    simp only [Matrix.conjTranspose_conjTranspose, frobNorm_conjTranspose]
    have hle := mul_le_mul_of_nonneg_left hZF
      (mul_nonneg hε.le (frobNorm_nonneg (A - A * Z * Zᴴ)))
    exact lt_of_le_of_lt (by nlinarith only [hle]) hω
  · generalize A - A * Z * Zᴴ = E
    rcases eq_or_ne E 0 with rfl | hE
    · simpa only [Matrix.conjTranspose_zero, Matrix.mul_zero, frobNorm_zero, zero_pow two_ne_zero,
        mul_zero, lt_self_iff_false, Set.ofPred_false, measureReal_empty] using hδ'
    have hEh : Eᴴ ≠ 0 := by rwa [Ne, Matrix.conjTranspose_eq_zero]
    refine (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => ?_)).trans
      (hJL.measureReal_abs_frobNorm_mul_sq_sub_ge_le hε hp hS hEh)
    rw [frobNorm_conjTranspose]
    exact le_abs.2 (Or.inl (by linarith))

/-- The OSE-plus-JL-moment constructor at a given frame. -/
private theorem hasProjectionCostPreserving_of_hasJLMoment_of_frame [IsFiniteMeasure μ]
    {S : Ω → Matrix l n ℝ} {k : ℕ} {a b δ ε δ' p : ℝ}
    (h : IsObliviousSubspaceEmbedding S k a b δ μ) (hJL : HasJLMoment S ε δ' p μ)
    (hS : AEMeasurable S μ) (ha : a ≤ 1) (hb : 1 ≤ b) (hε : 0 < ε) (hp : 2 ≤ p) (hδ' : 0 ≤ δ')
    {A : Matrix m n ℝ} {Z : Matrix n r ℝ} (hZ : HasOrthonormalCols Z)
    (hZA : frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A k))
    (hrk : Fintype.card r ≤ k) :
    HasProjectionCostPreserving S A k (a - 3 * √(k : ℝ) * ε) (b + 3 * √(k : ℝ) * ε + ε)
      (δ + 3 * δ') μ := by
  have hhead : HasSubspaceEmbedding S Z a b δ μ :=
    h.hasSubspaceEmbedding (by rw [hZ.rank_eq]; exact hrk)
  apply hhead.hasProjectionCostPreserving_of_hasApproximateMatrixMultiplication
    hJL hS ha hb hε (by linarith) hδ' hZ hZA hrk
  all_goals
    apply hasApproximateMatrixMultiplication_of_measureReal_ge_le hδ'
    intro hA hB
    exact hJL.measureReal_frobNorm_conjTranspose_mul_sub_ge_le hε hp hS hA hB

/-- **An OSE plus the JL moment property gives a projection-cost-preserving sketch**: a real sketch
that is an OSE for dimension $k$ with constants $a \le 1 \le b$ and failure probability $\delta$,
and has the $(\varepsilon, \delta', p)$ JL moment property with $\varepsilon > 0$, $p \ge 2$,
$\delta' \ge 0$, is for every $\mathbf{A}$ a rank-$k$ projection-cost-preserving sketch with
constants $a - 3\sqrt{k}\,\varepsilon$ and $b + 3\sqrt{k}\,\varepsilon + \varepsilon$, except with
probability $\delta + 3\delta'$. No dimension of $\mathbf{A}$ enters: the head is the top-$k$ frame
(the identity when $k$ exceeds the number of columns), the tail terms are approximate matrix
multiplication and `NLAlib.HasJLMoment.measureReal_abs_frobNorm_mul_sq_sub_ge_le`. With JL moments
at
$p = 2$ this is $O((k+1)/(\varepsilon^2\delta))$ rows; the $(k + \log(1/\delta))/\varepsilon^2$ of
CEMMP's Lemma 11 needs stable-rank spectral approximate multiplication.
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12]; there $O(k\log(1/\delta)/\varepsilon^2)$ for
dense sign matrices with higher moments and unspecified constants; here explicit, any $p \ge 2$.
Result: pcp-sufficient-conditions -/
theorem IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment
    [IsFiniteMeasure μ] {S : Ω → Matrix l n ℝ} {k : ℕ} {a b δ ε δ' p : ℝ}
    (h : IsObliviousSubspaceEmbedding S k a b δ μ) (hJL : HasJLMoment S ε δ' p μ)
    (hS : AEMeasurable S μ) (ha : a ≤ 1) (hb : 1 ≤ b) (hε : 0 < ε) (hp : 2 ≤ p) (hδ' : 0 ≤ δ')
    (A : Matrix m n ℝ) :
    HasProjectionCostPreserving S A k (a - 3 * √(k : ℝ) * ε) (b + 3 * √(k : ℝ) * ε + ε)
      (δ + 3 * δ') μ := by
  classical
  rcases le_or_gt k (Fintype.card n) with hk | hk
  · obtain ⟨Z, hZ, hAZ⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD (p := Fin k) A
        (Fintype.card_fin k) hk
    exact hasProjectionCostPreserving_of_hasJLMoment_of_frame h hJL hS ha hb hε hp hδ' hZ
      (by rw [hAZ]) (by rw [Fintype.card_fin])
  · refine hasProjectionCostPreserving_of_hasJLMoment_of_frame h hJL hS ha hb hε hp hδ'
      (hasOrthonormalCols_one (𝕜 := ℝ) (n := n)) ?_ hk.le
    rw [Matrix.mul_one, Matrix.conjTranspose_one, Matrix.mul_one, sub_self, frobNorm_zero]
    exact frobNorm_nonneg _

/-- The **tail rows of the head–tail constructor**, at
present <!-- value projectionCostTailDim v d \varepsilon \delta -->
$384 \cdot v (d + 1)/(\varepsilon^2 \delta)$: for a sketch whose JL moment at $p = 2$ has
failure $v/(\lvert k \rvert \varepsilon_J^2)$ at every $\varepsilon_J > 0$ (for CountSketch, also
its approximate-multiplication tail), at least this many rows make the three tail events of
`NLAlib.HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasOrthonormalCols` fail with total
probability at most $\delta/2$ at the budgets $\varepsilon_J = \varepsilon/(8\sqrt{d+1})$ of the
family statements. The proof's value; [CohenElderMuscoMuscoPersu2015, proof of Theorem 12]
bounds the same tail terms through approximate matrix multiplication at accuracy
$\varepsilon/\sqrt{d}$ for rank $d$, with no constant.
Consumers use `NLAlib.projectionCostTailDim_le`. Junk value: $0$ at $\varepsilon = 0$ or
$\delta = 0$. -/
noncomputable irreducible_def projectionCostTailDim (v : ℝ) (d : ℕ) (ε δ : ℝ) : ℝ :=
  384 * v * ((d : ℝ) + 1) / (ε ^ 2 * δ)

/-- The tail rows are nonnegative for $v \ge 0$ and $\delta \ge 0$. -/
theorem projectionCostTailDim_nonneg {v : ℝ} (hv : 0 ≤ v) (d : ℕ) (ε : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) : 0 ≤ projectionCostTailDim v d ε δ := by
  rw [projectionCostTailDim_def]
  positivity

/-- The tail rows are monotone in the JL constant $v \ge 0$ and the rank $d$, and antitone in the
distortion $\varepsilon > 0$ and the failure probability $\delta > 0$. -/
theorem projectionCostTailDim_mono {v v' : ℝ} {d d' : ℕ} {ε ε' δ δ' : ℝ} (hv : 0 ≤ v)
    (hvv' : v ≤ v') (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    projectionCostTailDim v d ε' δ' ≤ projectionCostTailDim v' d' ε δ := by
  rw [projectionCostTailDim_def, projectionCostTailDim_def]
  have hdd : (d : ℝ) ≤ d' := Nat.cast_le.2 hd
  have hv' : 0 ≤ v' := hv.trans hvv'
  exact div_le_div₀ (by positivity) (by gcongr) (by positivity)
    (mul_le_mul (pow_le_pow_left₀ hε.le hεε' 2) hδδ' hδ.le (by positivity))

/-- The explicit comparison: `NLAlib.projectionCostTailDim v d ε δ` is at
most <!-- value projectionCostTailDim v d \varepsilon \delta -->
$384 \cdot v (d + 1)/(\varepsilon^2 \delta)$, the value consumers invert with (at present an
equality); an improved definition keeps it true. -/
theorem projectionCostTailDim_le (v : ℝ) (d : ℕ) (ε δ : ℝ) :
    projectionCostTailDim v d ε δ ≤ 384 * v * ((d : ℝ) + 1) / (ε ^ 2 * δ) := by
  rw [projectionCostTailDim_def]

end Random

end NLAlib
