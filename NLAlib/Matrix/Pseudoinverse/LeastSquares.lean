/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.ComplementaryProjector
public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Subspaces.ObliqueProjector

/-!
# Linear least squares

`NLAlib.IsLeastSquaresSolution A b x` says that $\mathbf{x}$ minimises
$\|\mathbf{b} - \mathbf{A}\mathbf{x}\|$ over all vectors. It is the interface for "$\mathbf{x}$
solves the least-squares problem": a theorem about a solver concludes it, and a theorem about a
solution takes it. The minimisers are characterised by the normal equations and by
$\mathbf{A}\mathbf{x}$ being the projection of $\mathbf{b}$ onto the column space; the pseudoinverse
gives the one of smallest norm, and the residual is $(\mathbf{I} -
\mathbf{P}_{\mathbf{A}})\mathbf{b}$, with $\mathbf{P}_{\mathbf{A}}$ the orthogonal projector onto
the range of $\mathbf{A}$ (`rangeProjector`).

Sketch-and-solve replaces the problem by the one sketched by $\mathbf{S}$; its solution
`NLAlib.sketchAndSolve A S B`, written
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$, has fitted values the oblique
projection $\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{B}$, and when $\mathbf{S}$ keeps the rank of
$\mathbf{A}$ it is the exact minimum-norm solution plus the sketched solution for the optimal
residual. The solution does not change when the sketch is multiplied by a nonzero scalar, so
the normalisations of Gaussian and Haar sketches do not matter for it.

## Main definitions

* `NLAlib.IsLeastSquaresSolution`: $\mathbf{x}$ minimises $\|\mathbf{b} - \mathbf{A}\mathbf{x}\|$.
* `NLAlib.sketchAndSolve`: the sketch-and-solve solution.

## Main results

* `NLAlib.isLeastSquaresSolution_iff_normal_equations`: the normal equations.
* `NLAlib.isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec`:
  $\mathbf{A}\mathbf{x} = \mathbf{P}_{\mathbf{A}}\mathbf{b}$.
* `NLAlib.isLeastSquaresSolution_pinv_mulVec`: $\mathbf{A}^{+}\mathbf{b}$ is a solution.
* `NLAlib.IsLeastSquaresSolution.norm_pinv_mulVec_le`: it is the solution of smallest norm.
* `NLAlib.existsUnique_isLeastSquaresSolution_iff`: uniqueness exactly for full column rank.
* `NLAlib.mul_sketchAndSolve`, `NLAlib.sketchAndSolve_eq_pinv_mul_add`,
  `NLAlib.HasOrthonormalCols.sketchAndSolve_eq_add`: sketch-and-solve, its fitted values and its
  error decomposition.
* `NLAlib.sketchAndSolve_smul_sketch`: rescaling the sketch does not change the solution.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- $\mathbf{x}$ is a **least-squares solution** of $\mathbf{A}\mathbf{x} \approx \mathbf{b}$:
it minimises the Euclidean norm of the residual $\mathbf{b} - \mathbf{A}\mathbf{x}$ over all
vectors, $\|\mathbf{b} - \mathbf{A}\mathbf{x}\| \le \|\mathbf{b} - \mathbf{A}\mathbf{y}\|$ for every
$\mathbf{y}$.
[GolubVanLoan2013, §5.3]. -/
def IsLeastSquaresSolution (A : Matrix m n 𝕜) (b : m → 𝕜) (x : n → 𝕜) : Prop :=
  ∀ y : n → 𝕜, ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤ ‖WithLp.toLp 2 (b - A *ᵥ y)‖

/-- `IsLeastSquaresSolution` unfolded. -/
theorem isLeastSquaresSolution_iff {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔
      ∀ y : n → 𝕜, ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤ ‖WithLp.toLp 2 (b - A *ᵥ y)‖ :=
  Iff.rfl

/-! ### Characterisations -/

/-- The projector characterisation, proved first: the other characterisations follow from it. -/
private theorem isLeastSquaresSolution_iff_aux {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔ A *ᵥ x = rangeProjector A *ᵥ b := by
  classical
  constructor
  · intro h
    obtain ⟨y, hy⟩ : rangeProjector A *ᵥ b ∈ LinearMap.range A.mulVecLin :=
      rangeProjector_mulVec_eq_self_iff.mp (by
        rw [Matrix.mulVec_mulVec, rangeProjector_mul_rangeProjector])
    rw [Matrix.mulVecLin_apply] at hy
    have h1 : (1 - rangeProjector A) *ᵥ (b - A *ᵥ x) = b - A *ᵥ y := by
      rw [hy, Matrix.mulVec_sub, Matrix.mulVec_mulVec, one_sub_rangeProjector_mul_self,
        Matrix.zero_mulVec, sub_zero, Matrix.sub_mulVec, Matrix.one_mulVec]
    have h2 : rangeProjector A *ᵥ (b - A *ᵥ x) = rangeProjector A *ᵥ b - A *ᵥ x := by
      rw [Matrix.mulVec_sub, rangeProjector_mulVec_mulVec]
    have hp := norm_toLp_sq_eq_add_one_sub_rangeProjector A (b - A *ᵥ x)
    rw [h1, h2] at hp
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (h y) 2
    have h0 : ‖WithLp.toLp 2 (rangeProjector A *ᵥ b - A *ᵥ x)‖ ^ 2 ≤ 0 := by linarith
    have hz := le_antisymm h0 (sq_nonneg _)
    rw [sq_eq_zero_iff, norm_eq_zero, WithLp.toLp_eq_zero, sub_eq_zero] at hz
    exact hz.symm
  · intro h y
    have hr : b - A *ᵥ x = (1 - rangeProjector A) *ᵥ b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h]
    rw [hr]
    exact norm_one_sub_rangeProjector_mulVec_le A b y

/-- A least-squares solution is a global minimiser of the residual norm, in Mathlib's
vocabulary. The constrained problem, minimising over a subspace $K$ as Krylov methods do, is
`IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖) K x`; it has no separate predicate. -/
theorem isLeastSquaresSolution_iff_isMinOn {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔
      IsMinOn (fun y : n → 𝕜 => ‖WithLp.toLp 2 (b - A *ᵥ y)‖) Set.univ x := by
  rw [isMinOn_univ_iff, isLeastSquaresSolution_iff]

/-- **The normal equations.** $\mathbf{x}$ is a least-squares solution exactly when
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{x} = \mathbf{A}^{\mathsf{H}}\mathbf{b}$.
[GolubVanLoan2013, §5.3.1].
Result: normal-equations -/
theorem isLeastSquaresSolution_iff_normal_equations {A : Matrix m n 𝕜} {b : m → 𝕜}
    {x : n → 𝕜} : IsLeastSquaresSolution A b x ↔ Aᴴ *ᵥ (A *ᵥ x) = Aᴴ *ᵥ b := by
  rw [isLeastSquaresSolution_iff_aux, eq_comm (a := Aᴴ *ᵥ (A *ᵥ x)),
    ← sub_eq_zero (a := Aᴴ *ᵥ b), ← Matrix.mulVec_sub, ← rangeProjector_mulVec_eq_zero_iff,
    Matrix.mulVec_sub, rangeProjector_mulVec_mulVec, sub_eq_zero, eq_comm]

/-- $\mathbf{x}$ is a least-squares solution exactly when the residual is orthogonal to the
column space: $\mathbf{A}^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\mathbf{x}) = \mathbf{0}$. -/
theorem isLeastSquaresSolution_iff_conjTranspose_mulVec_sub_eq_zero {A : Matrix m n 𝕜}
    {b : m → 𝕜} {x : n → 𝕜} : IsLeastSquaresSolution A b x ↔ Aᴴ *ᵥ (b - A *ᵥ x) = 0 := by
  rw [isLeastSquaresSolution_iff_aux, ← rangeProjector_mulVec_eq_zero_iff, Matrix.mulVec_sub,
    rangeProjector_mulVec_mulVec, sub_eq_zero, eq_comm]

/-- $\mathbf{x}$ is a least-squares solution exactly when $\mathbf{A}\mathbf{x}$ is the
projection of $\mathbf{b}$ onto the column space of $\mathbf{A}$:
$\mathbf{A}\mathbf{x} = \mathbf{P}_{\mathbf{A}}\mathbf{b}$. -/
theorem isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec {A : Matrix m n 𝕜}
    {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔ A *ᵥ x = rangeProjector A *ᵥ b := by
  exact isLeastSquaresSolution_iff_aux

/-- An exact solution is a least-squares solution: if $\mathbf{A}\mathbf{x} = \mathbf{b}$ then
$\mathbf{x}$ is one. -/
theorem isLeastSquaresSolution_of_mulVec_eq {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜}
    (h : A *ᵥ x = b) : IsLeastSquaresSolution A b x := by
  intro y
  rw [h, sub_self, WithLp.toLp_zero, norm_zero]
  exact norm_nonneg _

/-- Multiplying the system by a matrix $\mathbf{Q}$ with orthonormal columns does not change its
least-squares solutions: those of $\mathbf{Q}\mathbf{A}\mathbf{x} \approx \mathbf{Q}\mathbf{b}$
are those of $\mathbf{A}\mathbf{x} \approx \mathbf{b}$. -/
theorem HasOrthonormalCols.isLeastSquaresSolution_mul_iff [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution (Q * A) (Q *ᵥ b) x ↔ IsLeastSquaresSolution A b x := by
  rw [isLeastSquaresSolution_iff, isLeastSquaresSolution_iff]
  refine forall_congr' fun y => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, ← Matrix.mulVec_sub,
    hQ.norm_toLp_mulVec, hQ.norm_toLp_mulVec]

namespace IsLeastSquaresSolution

variable {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜}

/-- For a least-squares solution $\mathbf{x}$, $\mathbf{A}\mathbf{x} =
\mathbf{P}_{\mathbf{A}}\mathbf{b}$ is the projection of $\mathbf{b}$ onto the column space of
$\mathbf{A}$: the forward direction of `isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec`.
-/
theorem mulVec_eq_rangeProjector_mulVec (h : IsLeastSquaresSolution A b x) :
    A *ᵥ x = rangeProjector A *ᵥ b := by
  exact isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec.mp h

/-! ### The residual -/

/-- The least-squares residual is the projection of $\mathbf{b}$ onto the orthogonal complement
of the column space: $\mathbf{b} - \mathbf{A}\mathbf{x} = (\mathbf{I} -
\mathbf{P}_{\mathbf{A}})\mathbf{b}$. -/
theorem sub_mulVec_eq [DecidableEq m] (h : IsLeastSquaresSolution A b x) :
    b - A *ᵥ x = (1 - rangeProjector A) *ᵥ b := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, h.mulVec_eq_rangeProjector_mulVec]

/-- The smallest possible residual:
$\|\mathbf{b} - \mathbf{A}\mathbf{x}\| = \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{b}\|$. -/
theorem norm_sub_mulVec_eq [DecidableEq m] (h : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ = ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖ := by
  rw [h.sub_mulVec_eq]

/-- **Pythagoras for least squares.** For a least-squares solution $\mathbf{x}$ and any
$\mathbf{y}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{y}\|^2 = \|\mathbf{b} - \mathbf{A}\mathbf{x}\|^2 +
  \|\mathbf{A}(\mathbf{x} - \mathbf{y})\|^2\,.$$
[GolubVanLoan2013, §5.3] discusses full-rank least squares. Here orthogonality of the residual
gives the identity at any rank. -/
theorem norm_sub_mulVec_sq_eq_add (h : IsLeastSquaresSolution A b x) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (b - A *ᵥ y)‖ ^ 2 =
      ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2 + ‖WithLp.toLp 2 (A *ᵥ (x - y))‖ ^ 2 := by
  classical
  have hx := h.mulVec_eq_rangeProjector_mulVec
  have h1 : (1 - rangeProjector A) *ᵥ (b - A *ᵥ y) = b - A *ᵥ x := by
    rw [hx, Matrix.mulVec_sub, Matrix.mulVec_mulVec, one_sub_rangeProjector_mul_self,
      Matrix.zero_mulVec, sub_zero, Matrix.sub_mulVec, Matrix.one_mulVec]
  have h2 : rangeProjector A *ᵥ (b - A *ᵥ y) = A *ᵥ (x - y) := by
    rw [Matrix.mulVec_sub (rangeProjector A), rangeProjector_mulVec_mulVec, ← hx,
      Matrix.mulVec_sub]
  rw [norm_toLp_sq_eq_add_one_sub_rangeProjector A (b - A *ᵥ y), h1, h2, add_comm]

/-- The squared residual of a least-squares solution is
$\|\mathbf{b} - \mathbf{A}\mathbf{x}\|^2 = \|\mathbf{b}\|^2 - \|\mathbf{A}\mathbf{x}\|^2$. -/
theorem norm_sub_mulVec_sq (h : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2 =
      ‖WithLp.toLp 2 b‖ ^ 2 - ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 := by
  classical
  rw [norm_toLp_sq_eq_add_one_sub_rangeProjector A b, ← h.sub_mulVec_eq,
    ← h.mulVec_eq_rangeProjector_mulVec, add_sub_cancel_left]

/-- Two least-squares solutions have the same image under $\mathbf{A}$. -/
theorem mulVec_eq {y : n → 𝕜} (hx : IsLeastSquaresSolution A b x)
    (hy : IsLeastSquaresSolution A b y) : A *ᵥ x = A *ᵥ y := by
  rw [hx.mulVec_eq_rangeProjector_mulVec, hy.mulVec_eq_rangeProjector_mulVec]

/-! ### The minimum-norm solution -/

/-- The pseudoinverse sends the image $\mathbf{A}\mathbf{x}$ of a least-squares solution
$\mathbf{x}$ to the pseudoinverse solution: $\mathbf{A}^{+}\mathbf{A}\mathbf{x} =
\mathbf{A}^{+}\mathbf{b}$. So $\mathbf{A}^{+}\mathbf{b}$ is the projection of any least-squares
solution onto the row space of $\mathbf{A}$. -/
theorem pinv_mulVec_mulVec (h : IsLeastSquaresSolution A b x) :
    pinv A *ᵥ (A *ᵥ x) = pinv A *ᵥ b := by
  rw [h.mulVec_eq_rangeProjector_mulVec, ← mul_pinv,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, pinv_mul_mul_pinv]

/-- **The pseudoinverse solution has the smallest norm** among least-squares solutions:
$\|\mathbf{A}^{+}\mathbf{b}\| \le \|\mathbf{x}\|$ for every least-squares solution $\mathbf{x}$.
[GolubVanLoan2013, §5.5.2].
Result: minimum-norm-least-squares -/
theorem norm_pinv_mulVec_le (h : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 (pinv A *ᵥ b)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  rw [← h.pinv_mulVec_mulVec, Matrix.mulVec_mulVec, pinv_mul]
  exact (isStarProjection_rangeProjector Aᴴ).norm_toLp_mulVec_le x

/-- A least-squares solution whose norm does not exceed that of the pseudoinverse solution is
the pseudoinverse solution: $\|\mathbf{x}\| \le \|\mathbf{A}^{+}\mathbf{b}\|$ implies
$\mathbf{x} = \mathbf{A}^{+}\mathbf{b}$. -/
theorem eq_pinv_mulVec_of_norm_le (h : IsLeastSquaresSolution A b x)
    (hx : ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (pinv A *ᵥ b)‖) : x = pinv A *ᵥ b := by
  classical
  rw [← h.pinv_mulVec_mulVec, Matrix.mulVec_mulVec, pinv_mul] at hx ⊢
  have hp := norm_toLp_sq_eq_add_one_sub_rangeProjector Aᴴ x
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have h0 : ‖WithLp.toLp 2 ((1 - rangeProjector Aᴴ) *ᵥ x)‖ ^ 2 ≤ 0 := by linarith
  have hz := le_antisymm h0 (sq_nonneg _)
  rw [sq_eq_zero_iff, norm_eq_zero, WithLp.toLp_eq_zero, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at hz
  exact hz

end IsLeastSquaresSolution

/-- **The pseudoinverse solves least squares.** $\mathbf{A}^{+}\mathbf{b}$ is a least-squares
solution.
[GolubVanLoan2013, §5.5.2].
Result: least-squares-pseudoinverse -/
theorem isLeastSquaresSolution_pinv_mulVec (A : Matrix m n 𝕜) (b : m → 𝕜) :
    IsLeastSquaresSolution A b (pinv A *ᵥ b) := by
  rw [isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec, Matrix.mulVec_mulVec, mul_pinv]

/-- **Pythagoras for least squares**, through the pseudoinverse. For every $\mathbf{y}$, the
squared residual is the squared optimal residual plus the squared distance, measured through
$\mathbf{A}$, from $\mathbf{y}$ to the pseudoinverse solution:
$$\|\mathbf{b} - \mathbf{A}\mathbf{y}\|^2
  = \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{b}\|^2 +
  \|\mathbf{A}(\mathbf{y} - \mathbf{A}^{+}\mathbf{b})\|^2\,.$$
Every sketch-and-solve error bound starts from this.
[GolubVanLoan2013, §5.3.1]. -/
theorem norm_sub_mulVec_sq_eq_add_norm_mulVec_sub_pinv_sq [DecidableEq m] (A : Matrix m n 𝕜)
    (b : m → 𝕜) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (b - A *ᵥ y)‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖ ^ 2 +
        ‖WithLp.toLp 2 (A *ᵥ (y - pinv A *ᵥ b))‖ ^ 2 := by
  have h := isLeastSquaresSolution_pinv_mulVec A b
  rw [h.norm_sub_mulVec_sq_eq_add y, h.sub_mulVec_eq, ← neg_sub y, Matrix.mulVec_neg,
    WithLp.toLp_neg, norm_neg]

/-- A least-squares solution exists. -/
theorem exists_isLeastSquaresSolution (A : Matrix m n 𝕜) (b : m → 𝕜) :
    ∃ x, IsLeastSquaresSolution A b x := by
  exact ⟨pinv A *ᵥ b, isLeastSquaresSolution_pinv_mulVec A b⟩

/-- All least-squares solutions: they are the pseudoinverse solution plus an element of the
kernel of $\mathbf{A}$: $\mathbf{x}$ is a least-squares solution exactly when
$\mathbf{x} = \mathbf{A}^{+}\mathbf{b} + (\mathbf{I} - \mathbf{A}^{+}\mathbf{A})\mathbf{z}$ for some
$\mathbf{z}$. -/
theorem isLeastSquaresSolution_iff_exists [DecidableEq n] {A : Matrix m n 𝕜} {b : m → 𝕜}
    {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔ ∃ z : n → 𝕜, x = pinv A *ᵥ b + (1 - pinv A * A) *ᵥ z := by
  constructor
  · intro h
    refine ⟨x, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, h.pinv_mulVec_mulVec,
      add_sub_cancel]
  · rintro ⟨z, rfl⟩
    rw [isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_pinv, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_pinv_mul_self, sub_self, Matrix.zero_mulVec, add_zero]

/-- With full column rank the pseudoinverse solution is the only least-squares solution:
$\mathbf{x}$ is one exactly when $\mathbf{x} = \mathbf{A}^{+}\mathbf{b}$. -/
theorem isLeastSquaresSolution_iff_eq_pinv_mulVec {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔ x = pinv A *ᵥ b := by
  constructor
  · intro h
    rw [← h.pinv_mulVec_mulVec, pinv_mulVec_mulVec_of_injective hA]
  · rintro rfl
    exact isLeastSquaresSolution_pinv_mulVec A b

/-- Uniqueness: the least-squares problem has a unique solution, for one right-hand side
or equivalently for all, exactly when $\mathbf{A}$ has full column rank
($\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ injective). -/
theorem existsUnique_isLeastSquaresSolution_iff (A : Matrix m n 𝕜) (b : m → 𝕜) :
    (∃! x, IsLeastSquaresSolution A b x) ↔ Function.Injective A.mulVec := by
  constructor
  · rintro ⟨x, hx, huniq⟩ u v huv
    have huv' : A *ᵥ u = A *ᵥ v := huv
    have h : IsLeastSquaresSolution A b (x + (u - v)) := by
      rw [isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec] at hx ⊢
      rw [Matrix.mulVec_add, Matrix.mulVec_sub, huv', sub_self, add_zero, hx]
    exact sub_eq_zero.mp (add_eq_left.mp (huniq _ h))
  · intro hA
    exact ⟨pinv A *ᵥ b, isLeastSquaresSolution_pinv_mulVec A b,
      fun y hy => (isLeastSquaresSolution_iff_eq_pinv_mulVec hA).mp hy⟩

/-! ### Sketch-and-solve

The least-squares problem sketched by $\mathbf{S}$, $\min_{\mathbf{X}}
\|\mathbf{S}(\mathbf{A}\mathbf{X} - \mathbf{B})\|_{\mathsf{F}}$, and its minimum-norm solution
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$, whose fitted values are the oblique
projection $\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{B}$ (`NLAlib.obliqueProjector`). -/

section SketchAndSolve

variable {k p q : Type*} [Fintype k] {S : Matrix k m 𝕜}

/-- The **sketch-and-solve solution**
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B}) :=
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{B}$, the minimum-norm minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{X} - \mathbf{B})\|_{\mathsf{F}}$, column by column
(`NLAlib.isLeastSquaresSolution_pinv_mulVec`). Total; its junk value is $\mathbf{0}$ when
$\mathbf{S}\mathbf{A} = \mathbf{0}$. The argument order is system, sketch, right-hand side, as in
`NLAlib.obliqueProjector`.
[EpperlyWebber2026, §2]; there with $\mathbf{S} = \mathbf{\Omega}^{\mathsf{H}}$.
Algorithm: sketch-and-solve -/
noncomputable def sketchAndSolve (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜) :
    Matrix n p 𝕜 :=
  pinv (S * A) * (S * B)

/-- The fitted values of sketch-and-solve are the oblique projection of the right-hand side:
$$\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B}) =
\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{B}\,.$$ -/
theorem mul_sketchAndSolve (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜) :
    A * sketchAndSolve A S B = obliqueProjector A S * B := by
  rw [sketchAndSolve, obliqueProjector]
  simp only [Matrix.mul_assoc]

/-- **Sketch-and-solve error decomposition**: when
$\operatorname{rank}(\mathbf{S}\mathbf{A}) = \operatorname{rank}\mathbf{A}$,
$$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B}) = \mathbf{A}^{+}\mathbf{B} +
\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, (\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B})\,:$$
the sketched solution is the exact minimum-norm solution plus the sketch-and-solve solution for the
optimal residual. This is the exact identity beside the bound `sketch-and-solve-ls`
(`NLAlib.IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le`).
[EpperlyWebber2026, Lemma 5.1, (5.1)]; there in a factorization $\mathbf{A} = \mathbf{Q}\mathbf{R}$,
here basis-free.
Result: sketch-and-solve-error-decomposition -/
theorem sketchAndSolve_eq_pinv_mul_add [DecidableEq m] {A : Matrix m n 𝕜}
    (h : (S * A).rank = A.rank) (B : Matrix m p 𝕜) :
    sketchAndSolve A S B = pinv A * B + sketchAndSolve A S ((1 - rangeProjector A) * B) := by
  have hP : rangeProjector (S * A)ᴴ = rangeProjector Aᴴ :=
    rangeProjector_inj.mpr (Matrix.range_conjTranspose_mul_eq_of_rank_eq h)
  have key : pinv (S * A) * (S * (rangeProjector A * B)) = pinv A * B := by
    calc pinv (S * A) * (S * (rangeProjector A * B))
        = pinv (S * A) * (S * A) * pinv A * B := by
          rw [← mul_pinv]
          simp only [Matrix.mul_assoc]
      _ = pinv A * B := by
          rw [pinv_mul, hP, ← pinv_mul, pinv_mul_mul_pinv]
  rw [sketchAndSolve, sketchAndSolve, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_sub, key]
  abel

/-- **Core noise**: for $\mathbf{Q}$ with orthonormal columns and
$\operatorname{rank}(\mathbf{S}\mathbf{Q}) = \operatorname{rank}\mathbf{Q}$ (full column rank of
$\mathbf{S}\mathbf{Q}$), the sketched core is the exact core plus noise,
$$\mathsf{sketchAndSolve}(\mathbf{Q}, \mathbf{S}, \mathbf{B}) = \mathbf{Q}^{\mathsf{H}}\mathbf{B} +
\mathsf{sketchAndSolve}(\mathbf{Q}, \mathbf{S},
(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{B})\,.$$
[TroppYurtseverUdellCevher2017, Lemma A.4]; [CamanoEpperlyMeyerTropp2025, Lemma 2.6]; there with a
complement frame.
Result: sketch-and-solve-error-decomposition -/
theorem HasOrthonormalCols.sketchAndSolve_eq_add [Fintype q] [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (h : (S * Q).rank = Q.rank)
    (B : Matrix m p 𝕜) :
    sketchAndSolve Q S B = Qᴴ * B + sketchAndSolve Q S ((1 - Q * Qᴴ) * B) := by
  rw [sketchAndSolve_eq_pinv_mul_add h B, hQ.pinv_eq, hQ.rangeProjector_eq]

/-- Rescaling the sketch does not change the sketch-and-solve solution:
$\mathsf{sketchAndSolve}(\mathbf{A}, c\mathbf{S}, \mathbf{B}) =
\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$ for $c \ne 0$, for instance the
normalisations $\lvert k \rvert^{-1/2}\mathbf{G}$ and
$\sqrt{\lvert n \rvert / \lvert k \rvert}\,\mathbf{Q}^{\mathsf{H}}$ of Gaussian and Haar sketches;
a real scalar is the case `RCLike.real_smul_eq_coe_smul`. The fitted values are the case
`NLAlib.obliqueProjector_smul_right`. -/
theorem sketchAndSolve_smul_sketch (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜)
    {c : 𝕜} (hc : c ≠ 0) : sketchAndSolve A (c • S) B = sketchAndSolve A S B := by
  simp only [sketchAndSolve, Matrix.smul_mul, pinv_smul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, mul_inv_cancel₀ hc, one_smul]

end SketchAndSolve

end NLAlib
