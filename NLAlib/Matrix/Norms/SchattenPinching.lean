/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.AbsoluteValue
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

-- TODO(move): NLAlib/Matrix/Basic/Projector.lean
/-- The reflection $2\mathbf{P} - \mathbf{I}$ through the range of an orthogonal projector is
unitary. -/
theorem _root_.IsStarProjection.hasOrthonormalCols_two_smul_sub_one {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) : HasOrthonormalCols ((2 : 𝕜) • P - 1) := by
  have h : ((2 : 𝕜) • P - 1)ᴴ = (2 : 𝕜) • P - 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.conjTranspose_eq,
      Matrix.conjTranspose_one, star_ofNat]
  rw [HasOrthonormalCols, h, sub_mul, mul_sub, mul_sub, smul_mul_smul_comm, hP.mul_self,
    mul_one, one_mul, one_mul]
  rw [show (2 : 𝕜) * 2 = 2 + 2 by norm_num, add_smul]
  abel

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
    Φ.matrixNorm (P * A * Q + (1 - P) * A * (1 - Q)) ≤ Φ.matrixNorm A := by
  have hV : ((2 : 𝕜) • Q - 1)ᴴ = (2 : 𝕜) • Q - 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hQ.conjTranspose_eq,
      Matrix.conjTranspose_one, star_ofNat]
  have key : (2 : 𝕜) • (P * A * Q + (1 - P) * A * (1 - Q)) =
      A + ((2 : 𝕜) • P - 1) * A * ((2 : 𝕜) • Q - 1)ᴴ := by
    rw [hV]
    simp only [two_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    abel
  have h2 := Φ.matrixNorm_add_le A (((2 : 𝕜) • P - 1) * A * ((2 : 𝕜) • Q - 1)ᴴ)
  rw [Φ.isUnitarilyInvariant_matrixNorm _ hP.hasOrthonormalCols_two_smul_sub_one _
    hQ.hasOrthonormalCols_two_smul_sub_one, ← key, Φ.matrixNorm_smul] at h2
  norm_num at h2
  linarith

open scoped ComplexOrder MatrixOrder in
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
      schattenNorm p X ^ p.toReal + schattenNorm p Y ^ p.toReal := by
  classical
  obtain ⟨q, hq, rfl⟩ : ∃ q : ℝ, 0 < q ∧ p = ENNReal.ofReal q :=
    ⟨p.toReal, ENNReal.toReal_pos hp0 hp, (ENNReal.ofReal_toReal hp).symm⟩
  rw [ENNReal.toReal_ofReal hq.le]
  set G := Matrix.fromCols X Y
  have h₁' : Yᴴ * X = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose X, ← Matrix.conjTranspose_mul, h₁,
      Matrix.conjTranspose_zero]
  have h₂' : Y * Xᴴ = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose Y, ← Matrix.conjTranspose_mul, h₂,
      Matrix.conjTranspose_zero]
  have hG₁ : (X + Y)ᴴᴴ * (X + Y)ᴴ = Gᴴᴴ * Gᴴ := by
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
      Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h₂, h₂',
      add_zero, zero_add]
  have hG₂ : Gᴴ * G = Matrix.fromBlocks (Xᴴ * X) 0 0 (Yᴴ * Y) := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols,
      h₁, h₁']
  have hX := Matrix.posSemidef_conjTranspose_mul_self X
  have hY := Matrix.posSemidef_conjTranspose_mul_self Y
  have hB : (Matrix.fromBlocks (Xᴴ * X) 0 0 (Yᴴ * Y)).PosSemidef :=
    hG₂ ▸ Matrix.posSemidef_conjTranspose_mul_self G
  rw [← schattenNorm_conjTranspose (A := X + Y), schattenNorm_rpow_eq_re_trace_rpow _ hq, hG₁,
    ← schattenNorm_rpow_eq_re_trace_rpow _ hq, schattenNorm_conjTranspose (A := G),
    schattenNorm_rpow_eq_re_trace_rpow _ hq, schattenNorm_rpow_eq_re_trace_rpow _ hq,
    schattenNorm_rpow_eq_re_trace_rpow _ hq, hG₂, CFC.rpow_eq_cfc_real hB.nonneg,
    CFC.rpow_eq_cfc_real hX.nonneg, CFC.rpow_eq_cfc_real hY.nonneg,
    hX.isHermitian.cfc_fromBlocks_zero₁₂_zero₂₁ hY.isHermitian, Matrix.trace_fromBlocks, map_add]

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

open scoped ComplexOrder in
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
      schattenNorm p A ^ p.toReal := by
  classical
  obtain ⟨q, hq, rfl⟩ : ∃ q : ℝ, 0 ≤ q ∧ p = ENNReal.ofReal q :=
    ⟨p.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hp).symm⟩
  have hq2 : 2 ≤ q := by
    simpa [ENNReal.toReal_ofReal hq] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hp2
  have hgram {R : Matrix m m 𝕜} (hR : IsStarProjection R) :
      (R * A)ᴴ * (R * A) = Aᴴ * R * A := by
    rw [Matrix.conjTranspose_mul, hR.conjTranspose_eq, Matrix.mul_assoc, ← Matrix.mul_assoc R R A,
      hR.mul_self, Matrix.mul_assoc]
  have hsum : (P * A)ᴴ * (P * A) + ((1 - P) * A)ᴴ * ((1 - P) * A) = Aᴴ * A := by
    rw [hgram hP, hgram hP.one_sub, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
      ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  rw [ENNReal.toReal_ofReal hq, schattenNorm_rpow_eq_re_trace_rpow _ (by linarith),
    schattenNorm_rpow_eq_re_trace_rpow _ (by linarith),
    schattenNorm_rpow_eq_re_trace_rpow _ (by linarith), ← hsum]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).re_trace_rpow_add_le
    (Matrix.posSemidef_conjTranspose_mul_self _) (by linarith)

end NLAlib
