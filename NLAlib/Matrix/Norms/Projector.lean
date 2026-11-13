/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import NLAlib.Matrix.Basic.ComplementaryProjector
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Functions.TraceFunctions
public import NLAlib.Matrix.Norms.Compare

/-!
# Norms and orthogonal projectors

An orthogonal projector is a contraction in both norms, splits the squared Frobenius norm
(Pythagoras), and gives the best approximation from its range. The statements about
$(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}$, the projection residual, with
$\mathbf{P}_{\mathbf{Y}}$ the orthogonal projector onto the range of $\mathbf{Y}$
(`rangeProjector`), are the ones range finders and low-rank approximation bounds consume.

## Main results

* `NLAlib.HasOrthonormalCols.frobNorm_add_mul_conjTranspose_le`: the orthogonal completion.
* `IsStarProjection.specNorm_le_one`, `IsStarProjection.specNorm_mul_le`,
  `IsStarProjection.frobNorm_mul_le`: contraction.
* `IsStarProjection.frobNorm_sq_eq_add`: Pythagoras;
  `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_sq_eq_add`: its head–tail form for a frame.
* `IsStarProjection.frobInner_sub_mul_sub_mul`,
  `IsStarProjection.frobNorm_sub_mul_sq_eq_sub_frobInner`: the residual of a projector, with no
  identity matrix.
* `IsStarProjection.frobNorm_sq_eq_rank`, `IsStarProjection.abs_frobInner_le_sqrt_mul_frobNorm`:
  the Frobenius norm of a projector is the square root of its rank, and the $\sqrt{k}$ bound.
* `NLAlib.frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul`,
  `NLAlib.specNorm_one_sub_rangeProjector_mul_le_specNorm_sub_mul`: the projection residual is
  the smallest residual $\mathbf{A} - \mathbf{B}\mathbf{X}$.
* `NLAlib.frobNorm_sub_mul_sq`: the exact error split for an arbitrary $\mathbf{X}$.
* `NLAlib.frobNorm_one_sub_rangeProjector_mul_sq_eq_add`: Pythagoras for the compressed residual
  $(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})$.
* `NLAlib.specNorm_one_sub_rangeProjector_mul_le_of_range_le`: a larger range gives a smaller
  residual.
* `NLAlib.specNorm_le_goldenRatio_mul_of_one_sub_mul_mul_one_sub_eq_zero`: a matrix with one
  vanishing block relative to two orthogonal projectors.
* `IsStarProjection.specNorm_mul_pow_le`: the power lemma
  $\|\mathbf{P}\mathbf{A}\|_2^{2j+1} \le
  \|\mathbf{P}(\mathbf{A}\mathbf{A}^{\mathsf{H}})^j\mathbf{A}\|_2$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Star projections -/

/-- An orthogonal projector has spectral norm at most one. -/
theorem _root_.IsStarProjection.specNorm_le_one {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    specNorm P ≤ 1 := by
  refine (specNorm_le_iff zero_le_one).2 fun x => ?_
  rw [one_mul]
  exact hP.norm_toLp_mulVec_le x

/-- A nonzero orthogonal projector has spectral norm one. -/
theorem _root_.IsStarProjection.specNorm_eq_one {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (h : P ≠ 0) : specNorm P = 1 := by
  have hsq := specNorm_conjTranspose_mul_self P
  rw [hP.conjTranspose_eq, hP.mul_self] at hsq
  have h0 : specNorm P ≠ 0 := fun h0 => h (specNorm_eq_zero_iff.1 h0)
  exact mul_left_cancel₀ h0 (by rw [mul_one, ← sq, ← hsq])

/-- Left multiplication by an orthogonal projector does not increase the spectral norm:
$\|\mathbf{P}\mathbf{A}\|_2 \le \|\mathbf{A}\|_2$. -/
theorem _root_.IsStarProjection.specNorm_mul_le {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : specNorm (P * A) ≤ specNorm A := by
  exact (NLAlib.specNorm_mul_le P A).trans
    (mul_le_of_le_one_left (specNorm_nonneg A) hP.specNorm_le_one)

/-- Left multiplication by an orthogonal projector does not increase the Frobenius norm:
$\|\mathbf{P}\mathbf{A}\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem _root_.IsStarProjection.frobNorm_mul_le {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : frobNorm (P * A) ≤ frobNorm A := by
  exact (frobNorm_mul_le_specNorm_mul_frobNorm P A).trans
    (mul_le_of_le_one_left (frobNorm_nonneg A) hP.specNorm_le_one)

/-- Right multiplication by an orthogonal projector does not increase the spectral norm:
$\|\mathbf{A}\mathbf{P}\|_2 \le \|\mathbf{A}\|_2$. -/
theorem _root_.IsStarProjection.specNorm_mul_right_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix n m 𝕜) : specNorm (A * P) ≤ specNorm A := by
  exact (NLAlib.specNorm_mul_le A P).trans
    (mul_le_of_le_one_right (specNorm_nonneg A) hP.specNorm_le_one)

/-- Right multiplication by an orthogonal projector does not increase the Frobenius norm:
$\|\mathbf{A}\mathbf{P}\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem _root_.IsStarProjection.frobNorm_mul_right_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix n m 𝕜) : frobNorm (A * P) ≤ frobNorm A := by
  exact (frobNorm_mul_le_frobNorm_mul_specNorm A P).trans
    (mul_le_of_le_one_right (frobNorm_nonneg A) hP.specNorm_le_one)

/-- The two parts of a matrix cut out by an orthogonal projector and its complement are
orthogonal in the Frobenius inner product:
$\langle \mathbf{P}\mathbf{A}, (\mathbf{I} - \mathbf{P})\mathbf{B} \rangle_{\mathsf{F}} = 0$. -/
theorem _root_.IsStarProjection.frobInner_mul_one_sub_mul [DecidableEq m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A B : Matrix m n 𝕜) :
    frobInner (P * A) ((1 - P) * B) = 0 := by
  rw [frobInner_mul_left, hP.conjTranspose_eq, ← Matrix.mul_assoc, hP.mul_one_sub_self,
    Matrix.zero_mul, frobInner_zero_right]

/-- **Pythagoras** for an orthogonal projector $\mathbf{P}$:
$\|\mathbf{A}\|_{\mathsf{F}}^2 = \|\mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 +
\|(\mathbf{I} - \mathbf{P})\mathbf{A}\|_{\mathsf{F}}^2$.
[TrefethenBau1997, Lecture 6]. -/
theorem _root_.IsStarProjection.frobNorm_sq_eq_add [DecidableEq m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = frobNorm (P * A) ^ 2 + frobNorm ((1 - P) * A) ^ 2 := by
  have h := frobNorm_add_sq_of_frobInner_eq_zero (hP.frobInner_mul_one_sub_mul A A)
  rwa [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul] at h

/-- Pythagoras on the right for an orthogonal projector $\mathbf{P}$:
$\|\mathbf{A}\|_{\mathsf{F}}^2 = \|\mathbf{A}\mathbf{P}\|_{\mathsf{F}}^2 +
\|\mathbf{A}(\mathbf{I} - \mathbf{P})\|_{\mathsf{F}}^2$, the conjugate transpose of
`IsStarProjection.frobNorm_sq_eq_add`. -/
theorem _root_.IsStarProjection.frobNorm_sq_eq_add_mul_right [DecidableEq n] {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = frobNorm (A * P) ^ 2 + frobNorm (A * (1 - P)) ^ 2 := by
  have h := hP.frobNorm_sq_eq_add Aᴴ
  rwa [frobNorm_conjTranspose, ← hP.conjTranspose_eq, ← Matrix.conjTranspose_mul,
    frobNorm_conjTranspose, hP.conjTranspose_eq, ← hP.one_sub.conjTranspose_eq,
    ← Matrix.conjTranspose_mul, frobNorm_conjTranspose] at h

/-- The residual of an orthogonal projector is orthogonal to its range part:
$$\langle \mathbf{B} - \mathbf{P}\mathbf{B}, \mathbf{X} - \mathbf{P}\mathbf{X} \rangle_{\mathsf{F}}
= \langle \mathbf{B} - \mathbf{P}\mathbf{B}, \mathbf{X} \rangle_{\mathsf{F}}\,,$$
the identity-free form of `IsStarProjection.frobInner_mul_one_sub_mul`. -/
theorem _root_.IsStarProjection.frobInner_sub_mul_sub_mul {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (B X : Matrix m n 𝕜) :
    frobInner (B - P * B) (X - P * X) = frobInner (B - P * B) X := by
  have h0 : frobInner (B - P * B) (P * X) = 0 := by
    rw [frobInner_comm, frobInner_mul_left, hP.conjTranspose_eq, Matrix.mul_sub,
      ← Matrix.mul_assoc, hP.mul_self, sub_self, frobInner_zero_right]
  rw [frobInner_sub_right, h0, sub_zero]

/-- The squared residual of an orthogonal projector, with no identity matrix:
$$\|\mathbf{X} - \mathbf{P}\mathbf{X}\|_{\mathsf{F}}^2 = \|\mathbf{X}\|_{\mathsf{F}}^2 -
\langle \mathbf{P}, \mathbf{X}\mathbf{X}^{\mathsf{H}} \rangle_{\mathsf{F}}\,.$$ -/
theorem _root_.IsStarProjection.frobNorm_sub_mul_sq_eq_sub_frobInner {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (X : Matrix m n 𝕜) :
    frobNorm (X - P * X) ^ 2 = frobNorm X ^ 2 - frobInner P (X * Xᴴ) := by
  rw [← frobInner_self (X - P * X), hP.frobInner_sub_mul_sub_mul, frobInner_sub_left,
    frobInner_self, frobInner_mul_right]

/-- For orthonormal columns of $\mathbf{Q}$, the two summands of the orthogonal completion
have orthogonal row spaces, giving
$$\|\mathbf{A}\mathbf{Q}^{\mathsf{H}} + \mathbf{Q}\mathbf{A}^{\mathsf{H}}
(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\|_{\mathsf{F}}
\le \sqrt{2}\|\mathbf{A}\|_{\mathsf{F}} \,.$$
This norm bound does not require a compatibility or Hermitian hypothesis on $\mathbf{A}$. -/
theorem HasOrthonormalCols.frobNorm_add_mul_conjTranspose_le [DecidableEq m] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    frobNorm (A * Qᴴ + Q * Aᴴ * (1 - Q * Qᴴ)) ≤ Real.sqrt 2 * frobNorm A := by
  have hPQ : (1 - Q * Qᴴ) * Q = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQ.conjTranspose_mul_self,
      Matrix.mul_one, sub_self]
  have hz : frobInner (A * Qᴴ) (Q * Aᴴ * (1 - Q * Qᴴ)) = 0 := by
    rw [frobInner_mul_right, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      hPQ, Matrix.mul_zero, frobInner_zero_right]
  have hb : frobNorm (Q * Aᴴ * (1 - Q * Qᴴ)) ≤ frobNorm A := by
    rw [Matrix.mul_assoc, hQ.frobNorm_mul_left]
    exact (hQ.isStarProjection_mul_conjTranspose.one_sub.frobNorm_mul_right_le Aᴴ).trans_eq
      (frobNorm_conjTranspose A)
  apply (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).mp
  rw [frobNorm_add_sq_of_frobInner_eq_zero hz, hQ.frobNorm_mul_conjTranspose_right,
    mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith only [pow_le_pow_left₀ (frobNorm_nonneg _) hb 2]

/-- The head–tail split of a projection residual for a frame $\mathbf{Z}$ and any
$\mathbf{P}$: with $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 =
\|\mathbf{A}\mathbf{Z} - \mathbf{P}\mathbf{A}\mathbf{Z}\|_{\mathsf{F}}^2 +
\|\mathbf{E} - \mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2\,;$$
`IsStarProjection.frobNorm_sq_eq_add` at $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$, transposed. -/
theorem HasOrthonormalCols.frobNorm_sub_mul_sq_eq_add [DecidableEq p] {Z : Matrix n p 𝕜}
    (hZ : HasOrthonormalCols Z) (A : Matrix m n 𝕜) (P : Matrix m m 𝕜) :
    frobNorm (A - P * A) ^ 2 =
      frobNorm (A * Z - P * (A * Z)) ^ 2 +
        frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) ^ 2 := by
  classical
  have h := hZ.isStarProjection_mul_conjTranspose.frobNorm_sq_eq_add (A - P * A)ᴴ
  have e₁ : (Z * Zᴴ * (A - P * A)ᴴ)ᴴ = (A * Z - P * (A * Z)) * Zᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_assoc]
  have e₂ : ((1 - Z * Zᴴ) * (A - P * A)ᴴ)ᴴ = A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc]
  rw [frobNorm_conjTranspose, ← frobNorm_conjTranspose (Z * Zᴴ * _), e₁,
    hZ.frobNorm_mul_conjTranspose_right, ← frobNorm_conjTranspose ((1 - Z * Zᴴ) * _), e₂] at h
  exact h

/-! ### The range projector -/

/-- The trace of the range projector is the rank:
$\operatorname{tr} \mathbf{P}_{\mathbf{A}} = \operatorname{rank} \mathbf{A}$. -/
theorem trace_rangeProjector (A : Matrix m n 𝕜) : (rangeProjector A).trace = A.rank := by
  obtain ⟨Q, hQ, hrange⟩ :=
    exists_hasOrthonormalCols_range_eq (p := Fin A.rank) A (Fintype.card_fin _)
  rw [← rangeProjector_inj.mpr hrange, hQ.rangeProjector_eq, Matrix.trace_mul_comm,
    hQ.conjTranspose_mul_self, Matrix.trace_one, Fintype.card_fin]

/-- The squared Frobenius norm of the range projector is the rank:
$\|\mathbf{P}_{\mathbf{A}}\|_{\mathsf{F}}^2 = \operatorname{rank} \mathbf{A}$. -/
theorem frobNorm_rangeProjector_sq (A : Matrix m n 𝕜) :
    frobNorm (rangeProjector A) ^ 2 = A.rank := by
  rw [frobNorm_sq_eq_re_trace, conjTranspose_rangeProjector, rangeProjector_mul_rangeProjector,
    trace_rangeProjector, RCLike.natCast_re]

/-- The squared Frobenius norm of an orthogonal projector is its rank:
$\|\mathbf{P}\|_{\mathsf{F}}^2 = \operatorname{rank} \mathbf{P}$; the projector form of
`NLAlib.frobNorm_rangeProjector_sq`. -/
theorem _root_.IsStarProjection.frobNorm_sq_eq_rank {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    frobNorm P ^ 2 = P.rank := by
  have h := frobNorm_rangeProjector_sq P
  rwa [hP.rangeProjector_eq] at h

/-- An orthogonal projector of rank at most $k$ meets any $\mathbf{W}$ in at most
$\sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}$:
$\lvert\langle\mathbf{P}, \mathbf{W}\rangle_{\mathsf{F}}\rvert
\le \sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}$. This is the Ky Fan step
$\sum_{i < k}\lvert\lambda_i(\mathbf{W})\rvert \le \sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}$ in
the form the sketching proofs use. [CohenElderMuscoMuscoPersu2015, proof of Theorem 12]; there
the sum of the $k$ largest absolute eigenvalues of a symmetric error; here the inner product with
a projector, any `RCLike` field. -/
theorem _root_.IsStarProjection.abs_frobInner_le_sqrt_mul_frobNorm {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {k : ℕ} (hPk : P.rank ≤ k) (W : Matrix m m 𝕜) :
    |frobInner P W| ≤ √(k : ℝ) * frobNorm W := by
  have hPF : frobNorm P ≤ √(k : ℝ) := by
    rw [← Real.sqrt_sq (frobNorm_nonneg P), hP.frobNorm_sq_eq_rank]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hPk)
  exact (abs_frobInner_le P W).trans (mul_le_mul_of_nonneg_right hPF (frobNorm_nonneg W))

/-! ### The projection residual -/

variable [DecidableEq m]

/-- The projection residual has spectral norm at most that of the matrix:
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}\|_2 \le \|\mathbf{A}\|_2$. -/
theorem specNorm_one_sub_rangeProjector_mul_le (Y : Matrix m p 𝕜) (A : Matrix m n 𝕜) :
    specNorm ((1 - rangeProjector Y) * A) ≤ specNorm A := by
  exact (isStarProjection_one_sub_rangeProjector Y).specNorm_mul_le A

/-- The projection residual has Frobenius norm at most that of the matrix:
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}}$.
-/
theorem frobNorm_one_sub_rangeProjector_mul_le (Y : Matrix m p 𝕜) (A : Matrix m n 𝕜) :
    frobNorm ((1 - rangeProjector Y) * A) ≤ frobNorm A := by
  exact (isStarProjection_one_sub_rangeProjector Y).frobNorm_mul_le A


/-- **Pythagoras for the compressed residual.** For any $\mathbf{Y}$ with $m$ rows and any square
$\mathbf{A}$ of size $m$, with $\mathbf{P} = \mathbf{P}_{\mathbf{Y}}$,
$$\|(\mathbf{I} - \mathbf{P})\mathbf{A}\|_{\mathsf{F}}^2 =
\|(\mathbf{I} - \mathbf{P})\mathbf{A}\mathbf{P}\|_{\mathsf{F}}^2 +
\|(\mathbf{I} - \mathbf{P})\mathbf{A}(\mathbf{I} - \mathbf{P})\|_{\mathsf{F}}^2\,,$$
`IsStarProjection.frobNorm_sq_eq_add` applied on the right. With
$\mathbf{P} = \mathbf{P}_{\mathbf{A}\mathbf{S}}$ the left side is
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}}^2$ and the last term is the
squared Frobenius norm of the residual Hutch++ estimates; it is the exact form of the
submultiplicativity step in [MeyerMuscoMuscoWoodruff2021, proof of Theorem 10]. -/
theorem frobNorm_one_sub_rangeProjector_mul_sq_eq_add (Y : Matrix m p 𝕜) (A : Matrix m m 𝕜) :
    frobNorm ((1 - rangeProjector Y) * A) ^ 2 =
      frobNorm ((1 - rangeProjector Y) * A * rangeProjector Y) ^ 2 +
        frobNorm ((1 - rangeProjector Y) * A * (1 - rangeProjector Y)) ^ 2 := by
  set M := (1 - rangeProjector Y) * A
  have hP := isStarProjection_rangeProjector Y
  have h := hP.frobNorm_sq_eq_add Mᴴ
  rwa [← hP.conjTranspose_eq, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_one,
    ← Matrix.conjTranspose_sub, ← Matrix.conjTranspose_mul, frobNorm_conjTranspose,
    frobNorm_conjTranspose, frobNorm_conjTranspose] at h

/-- The exact error split: for any coefficient matrix $\mathbf{X}$, the squared Frobenius
error of $\mathbf{B}\mathbf{X}$ as an approximation of $\mathbf{A}$ is the squared projection
residual plus the squared error inside the range of $\mathbf{B}$:
$$\|\mathbf{A} - \mathbf{B}\mathbf{X}\|_{\mathsf{F}}^2
  = \|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{A}\|_{\mathsf{F}}^2 +
  \|\mathbf{P}_{\mathbf{B}}\mathbf{A} - \mathbf{B}\mathbf{X}\|_{\mathsf{F}}^2\,.$$ -/
theorem frobNorm_sub_mul_sq (B : Matrix m p 𝕜) (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    frobNorm (A - B * X) ^ 2 =
      frobNorm ((1 - rangeProjector B) * A) ^ 2 + frobNorm (rangeProjector B * A - B * X) ^ 2 := by
  have hPX : rangeProjector B * A - B * X = rangeProjector B * (A - B * X) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, rangeProjector_mul_self]
  have hsplit : A - B * X = (1 - rangeProjector B) * A + rangeProjector B * (A - B * X) := by
    rw [← hPX, one_sub_rangeProjector_mul]
    abel
  have h0 : frobInner ((1 - rangeProjector B) * A) (rangeProjector B * (A - B * X)) = 0 := by
    rw [frobInner_comm]
    exact (isStarProjection_rangeProjector B).frobInner_mul_one_sub_mul _ _
  rw [hPX, ← frobNorm_add_sq_of_frobInner_eq_zero h0, ← hsplit]

/-- **Best approximation in the Frobenius norm.** The projection residual is at most the
residual of any approximation $\mathbf{B}\mathbf{X}$ with columns in the range of $\mathbf{B}$:
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{A}\|_{\mathsf{F}}
\le \|\mathbf{A} - \mathbf{B}\mathbf{X}\|_{\mathsf{F}}$.
[GolubVanLoan2013, §5.3.1]. -/
theorem frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul (B : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    frobNorm ((1 - rangeProjector B) * A) ≤ frobNorm (A - B * X) := by
  rw [← one_sub_rangeProjector_mul_sub_mul B A X]
  exact frobNorm_one_sub_rangeProjector_mul_le B _

/-- **Best approximation in the spectral norm.** The projection residual is at most the residual
of any approximation $\mathbf{B}\mathbf{X}$ with columns in the range of $\mathbf{B}$:
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{A}\|_2 \le \|\mathbf{A} -
\mathbf{B}\mathbf{X}\|_2$.
[HalkoMartinssonTropp2011, Proposition 8.5]. -/
theorem specNorm_one_sub_rangeProjector_mul_le_specNorm_sub_mul (B : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    specNorm ((1 - rangeProjector B) * A) ≤ specNorm (A - B * X) := by
  rw [← one_sub_rangeProjector_mul_sub_mul B A X]
  exact specNorm_one_sub_rangeProjector_mul_le B _

omit [Fintype n] in
private theorem one_sub_rangeProjector_mul_one_sub_rangeProjector_mul {B : Matrix m p 𝕜}
    {Y : Matrix m l 𝕜} (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin)
    (A : Matrix m n 𝕜) :
    (1 - rangeProjector B) * ((1 - rangeProjector Y) * A) = (1 - rangeProjector B) * A := by
  have hmul : (1 - rangeProjector B) * (1 - rangeProjector Y) = 1 - rangeProjector B := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
      rangeProjector_mul_rangeProjector_of_range_le h, sub_self, sub_zero]
  rw [← Matrix.mul_assoc, hmul]

/-- A larger range gives a smaller projection residual, in spectral norm: if the range of
$\mathbf{Y}$ is contained in the range of $\mathbf{B}$ then
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{A}\|_2
\le \|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}\|_2$.
[HalkoMartinssonTropp2011, Proposition 8.5]. -/
theorem specNorm_one_sub_rangeProjector_mul_le_of_range_le {B : Matrix m p 𝕜} {Y : Matrix m l 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) (A : Matrix m n 𝕜) :
    specNorm ((1 - rangeProjector B) * A) ≤ specNorm ((1 - rangeProjector Y) * A) := by
  rw [← one_sub_rangeProjector_mul_one_sub_rangeProjector_mul h A]
  exact specNorm_one_sub_rangeProjector_mul_le B _

/-- A larger range gives a smaller projection residual, in Frobenius norm: if the range of
$\mathbf{Y}$ is contained in the range of $\mathbf{B}$ then
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{A}\|_{\mathsf{F}}
\le \|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}\|_{\mathsf{F}}$. -/
theorem frobNorm_one_sub_rangeProjector_mul_le_of_range_le {B : Matrix m p 𝕜} {Y : Matrix m l 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) (A : Matrix m n 𝕜) :
    frobNorm ((1 - rangeProjector B) * A) ≤ frobNorm ((1 - rangeProjector Y) * A) := by
  rw [← one_sub_rangeProjector_mul_one_sub_rangeProjector_mul h A]
  exact frobNorm_one_sub_rangeProjector_mul_le B _

/-! ### A matrix with a vanishing block -/

/-- The scalar inequality behind the golden-ratio bound: the matrix
$\begin{bmatrix} 1 & 1 \\ 1 & 0 \end{bmatrix}$ has norm $(1 + \sqrt{5})/2$. -/
private theorem add_sq_add_sq_le_goldenRatio_sq_mul (s t : ℝ) :
    (s + t) ^ 2 + s ^ 2 ≤ Real.goldenRatio ^ 2 * (s ^ 2 + t ^ 2) := by
  have h : Real.goldenRatio * (Real.goldenRatio ^ 2 * (s ^ 2 + t ^ 2) - ((s + t) ^ 2 + s ^ 2)) =
      (s - Real.goldenRatio * t) ^ 2 := by
    linear_combination
      ((Real.goldenRatio + 1) * s ^ 2 + Real.goldenRatio * t ^ 2) * Real.goldenRatio_sq
  have h0 : 0 ≤ Real.goldenRatio ^ 2 * (s ^ 2 + t ^ 2) - ((s + t) ^ 2 + s ^ 2) :=
    (mul_nonneg_iff_of_pos_left Real.goldenRatio_pos).mp (h ▸ sq_nonneg _)
  linarith

/-- A matrix with three blocks of norm at most $d$ and a vanishing fourth block, relative to two
orthogonal projectors, has spectral norm at most $(1 + \sqrt{5}) d / 2$: for orthogonal
projectors $\mathbf{P}$, $\mathbf{Q}$ with
$(\mathbf{I} - \mathbf{Q})\mathbf{Z}(\mathbf{I} - \mathbf{P}) = \mathbf{0}$ and
$\|\mathbf{Q}\mathbf{Z}\mathbf{P}\|_2$, $\|\mathbf{Q}\mathbf{Z}(\mathbf{I} - \mathbf{P})\|_2$,
$\|(\mathbf{I} - \mathbf{Q})\mathbf{Z}\mathbf{P}\|_2$ all at most $d$,
$\|\mathbf{Z}\|_2 \le (1 + \sqrt{5}) d / 2$. This is the step that gives the golden ratio in
Wedin's bound for the pseudoinverse. [Wedin1973, Theorem 4.1]. -/
theorem specNorm_le_goldenRatio_mul_of_one_sub_mul_mul_one_sub_eq_zero [DecidableEq n]
    {Z : Matrix m n 𝕜} {P : Matrix n n 𝕜} {Q : Matrix m m 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {d : ℝ} (h00 : (1 - Q) * Z * (1 - P) = 0)
    (h11 : specNorm (Q * Z * P) ≤ d) (h12 : specNorm (Q * Z * (1 - P)) ≤ d)
    (h21 : specNorm ((1 - Q) * Z * P) ≤ d) :
    specNorm Z ≤ Real.goldenRatio * d := by
  have hd : 0 ≤ d := (specNorm_nonneg _).trans h11
  refine (specNorm_le_iff (mul_nonneg Real.goldenRatio_pos.le hd)).2 fun x => ?_
  have hin := norm_toLp_sq_eq_add_one_sub_rangeProjector P x
  have hout := norm_toLp_sq_eq_add_one_sub_rangeProjector Q (Z *ᵥ x)
  rw [hP.rangeProjector_eq] at hin
  rw [hQ.rangeProjector_eq] at hout
  have e0 : (1 - Q) * Z = (1 - Q) * Z * P := by
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h00
  have e1 : Q *ᵥ (Z *ᵥ x) =
      (Q * Z * P) *ᵥ (P *ᵥ x) + (Q * Z * (1 - P)) *ᵥ ((1 - P) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc (Q * Z) P P, hP.mul_self, Matrix.mul_assoc (Q * Z) (1 - P) (1 - P),
      hP.one_sub.mul_self, ← Matrix.add_mulVec, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  have e2 : (1 - Q) *ᵥ (Z *ᵥ x) = ((1 - Q) * Z * P) *ᵥ (P *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ P P, hP.mul_self, ← e0]
  have h1 : ‖WithLp.toLp 2 (Q *ᵥ (Z *ᵥ x))‖ ≤
      d * (‖WithLp.toLp 2 (P *ᵥ x)‖ + ‖WithLp.toLp 2 ((1 - P) *ᵥ x)‖) := by
    rw [e1, WithLp.toLp_add, mul_add]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right h11 (norm_nonneg _)))
      ((norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right h12 (norm_nonneg _))))
  have h2 : ‖WithLp.toLp 2 ((1 - Q) *ᵥ (Z *ᵥ x))‖ ≤ d * ‖WithLp.toLp 2 (P *ᵥ x)‖ := by
    rw [e2]
    exact (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right h21 (norm_nonneg _))
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hg := mul_le_mul_of_nonneg_left (add_sq_add_sq_le_goldenRatio_sq_mul
    ‖WithLp.toLp 2 (P *ᵥ x)‖ ‖WithLp.toLp 2 ((1 - P) *ᵥ x)‖) (sq_nonneg d)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (mul_nonneg Real.goldenRatio_pos.le hd)
    (norm_nonneg _)) two_ne_zero).mp ?_
  rw [hout, mul_pow, mul_pow, hin]
  nlinarith

/-! ### Powers -/


/-- **The power lemma**: for an orthogonal projector $\mathbf{P}$ and every $j$,
$$\|\mathbf{P}\mathbf{A}\|_2^{2j+1} \le
\|\mathbf{P}(\mathbf{A}\mathbf{A}^{\mathsf{H}})^j\mathbf{A}\|_2\,,$$
so a power iteration can only improve the projection error. With $\mathbf{P}$ the residual
projector of a range finder it turns a bound for the sketch of
$(\mathbf{A}\mathbf{A}^{\mathsf{H}})^j\mathbf{A}$ into one for $\mathbf{A}$.
[HalkoMartinssonTropp2011, Proposition 8.6]; [TroppWebber2023, §9.3 (proof of Theorem 9.1)]. -/
theorem _root_.IsStarProjection.specNorm_mul_pow_le {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) (j : ℕ) :
    specNorm (P * A) ^ (2 * j + 1) ≤ specNorm (P * ((A * Aᴴ) ^ j * A)) := by
  rcases (specNorm_nonneg (P * A)).eq_or_lt with h₀ | h₀
  · rw [← h₀, zero_pow (Nat.succ_ne_zero _)]
    exact specNorm_nonneg _
  have hH : (A * Aᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self A
  have hsa : IsSelfAdjoint (A * Aᴴ) := hH
  have hB : (A * Aᴴ) ^ j * A * ((A * Aᴴ) ^ j * A)ᴴ =
      cfc (fun t : ℝ => t ^ (2 * j + 1)) (A * Aᴴ) := by
    rw [cfc_pow_id (A * Aᴴ) (2 * j + 1) hsa, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow,
      hH.eq, pow_succ, two_mul, pow_add]
    simp only [Matrix.mul_assoc, (Commute.pow_left (Commute.refl (A * Aᴴ)) j).eq]
  have hφ : HasSupportingLineOn (fun t : ℝ => t ^ (2 * j + 1)) (Set.Ici 0)
      (specNorm (P * A) ^ 2) :=
    (convexOn_pow (2 * j + 1)).hasSupportingLineOn (Set.mem_Ici.mpr (sq_nonneg _))
      (differentiableAt_pow _)
  have h := apply_specNorm_mul_sq_le_specNorm_mul_sq_of_hasSupportingLineOn hB hP h₀ hφ
  rw [← pow_mul, mul_comm, pow_mul] at h
  exact (pow_le_pow_iff_left₀ (pow_nonneg (specNorm_nonneg _) _) (specNorm_nonneg _)
    two_ne_zero).mp h

end NLAlib
