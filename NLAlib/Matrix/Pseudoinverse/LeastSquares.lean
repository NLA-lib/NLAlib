/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.ComplementaryProjector
public import NLAlib.Matrix.Pseudoinverse.NormBounds

/-!
# Linear least squares

`NLAlib.IsLeastSquaresSolution A b x` says that `x` minimises `‖b - A x‖` over all vectors. It is
the interface for "`x` solves the least-squares problem": a theorem about a solver concludes it,
and a theorem about a solution takes it. The minimisers are characterised by the normal
equations and by `A x` being the projection of `b` onto the column space; the pseudoinverse gives
the one of smallest norm, and the residual is `(1 - rangeProjector A) *ᵥ b`.

## Main definitions

* `NLAlib.IsLeastSquaresSolution`: `x` minimises `‖b - A x‖`.

## Main results

* `NLAlib.isLeastSquaresSolution_iff_normal_equations`: the normal equations.
* `NLAlib.isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec`: `A x = P_A b`.
* `NLAlib.isLeastSquaresSolution_pinv_mulVec`: `pinv A *ᵥ b` is a solution.
* `NLAlib.IsLeastSquaresSolution.norm_pinv_mulVec_le`: it is the solution of smallest norm.
* `NLAlib.existsUnique_isLeastSquaresSolution_iff`: uniqueness exactly for full column rank.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- `x` is a **least-squares solution** of `A x ≈ b`: it minimises the Euclidean norm of the
residual `b - A x` over all vectors. [GolubVanLoan2013, §5.3].
Port of `NLAlib.IsLeastSquaresSolution`, there over `ℝ`. -/
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
vocabulary. The constrained problem, minimising over a subspace `K` as Krylov methods do, is
`IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖) K x`; it has no separate predicate. -/
theorem isLeastSquaresSolution_iff_isMinOn {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔
      IsMinOn (fun y : n → 𝕜 => ‖WithLp.toLp 2 (b - A *ᵥ y)‖) Set.univ x := by
  rw [isMinOn_univ_iff, isLeastSquaresSolution_iff]

/-- **The normal equations.** `x` is a least-squares solution exactly when
`Aᴴ (A x) = Aᴴ b`. [GolubVanLoan2013, §5.3.1].
Port of `NLAlib.isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq`.
Result: normal-equations -/
theorem isLeastSquaresSolution_iff_normal_equations {A : Matrix m n 𝕜} {b : m → 𝕜}
    {x : n → 𝕜} : IsLeastSquaresSolution A b x ↔ Aᴴ *ᵥ (A *ᵥ x) = Aᴴ *ᵥ b := by
  rw [isLeastSquaresSolution_iff_aux, eq_comm (a := Aᴴ *ᵥ (A *ᵥ x)),
    ← sub_eq_zero (a := Aᴴ *ᵥ b), ← Matrix.mulVec_sub, ← rangeProjector_mulVec_eq_zero_iff,
    Matrix.mulVec_sub, rangeProjector_mulVec_mulVec, sub_eq_zero, eq_comm]

/-- `x` is a least-squares solution exactly when the residual is orthogonal to the column space:
`Aᴴ (b - A x) = 0`.
Port of `NLAlib.isLeastSquaresSolution_iff_forall_dotProduct_mulVec_eq_zero`. -/
theorem isLeastSquaresSolution_iff_conjTranspose_mulVec_sub_eq_zero {A : Matrix m n 𝕜}
    {b : m → 𝕜} {x : n → 𝕜} : IsLeastSquaresSolution A b x ↔ Aᴴ *ᵥ (b - A *ᵥ x) = 0 := by
  rw [isLeastSquaresSolution_iff_aux, ← rangeProjector_mulVec_eq_zero_iff, Matrix.mulVec_sub,
    rangeProjector_mulVec_mulVec, sub_eq_zero, eq_comm]

/-- `x` is a least-squares solution exactly when `A x` is the projection of `b` onto the column
space of `A`. Port of `NLAlib.isLeastSquaresSolution_iff_mulVec_eq`. -/
theorem isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec {A : Matrix m n 𝕜}
    {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔ A *ᵥ x = rangeProjector A *ᵥ b := by
  exact isLeastSquaresSolution_iff_aux

/-- An exact solution is a least-squares solution. -/
theorem isLeastSquaresSolution_of_mulVec_eq {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜}
    (h : A *ᵥ x = b) : IsLeastSquaresSolution A b x := by
  intro y
  rw [h, sub_self, WithLp.toLp_zero, norm_zero]
  exact norm_nonneg _

/-- Multiplying the system by a matrix with orthonormal columns does not change its
least-squares solutions. -/
theorem HasOrthonormalCols.isLeastSquaresSolution_mul_iff [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution (Q * A) (Q *ᵥ b) x ↔ IsLeastSquaresSolution A b x := by
  rw [isLeastSquaresSolution_iff, isLeastSquaresSolution_iff]
  refine forall_congr' fun y => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, ← Matrix.mulVec_sub,
    hQ.norm_toLp_mulVec, hQ.norm_toLp_mulVec]

namespace IsLeastSquaresSolution

variable {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜}

/-- For a least-squares solution `x`, `A x` is the projection of `b` onto the column space of
`A`: the forward direction of `isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec`. -/
theorem mulVec_eq_rangeProjector_mulVec (h : IsLeastSquaresSolution A b x) :
    A *ᵥ x = rangeProjector A *ᵥ b := by
  exact isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec.mp h

/-! ### The residual -/

/-- The least-squares residual is the projection of `b` onto the orthogonal complement of the
column space. Port of `NLAlib.IsLeastSquaresSolution.sub_mulVec_eq`. -/
theorem sub_mulVec_eq [DecidableEq m] (h : IsLeastSquaresSolution A b x) :
    b - A *ᵥ x = (1 - rangeProjector A) *ᵥ b := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, h.mulVec_eq_rangeProjector_mulVec]

/-- The smallest possible residual: `‖(1 - rangeProjector A) b‖`. -/
theorem norm_sub_mulVec_eq [DecidableEq m] (h : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ = ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖ := by
  rw [h.sub_mulVec_eq]

/-- **Pythagoras for least squares.** For a least-squares solution `x` and any `y`,
`‖b - A y‖² = ‖b - A x‖² + ‖A (x - y)‖²`.
Port of `NLAlib.norm_sub_mulVec_sq_eq_add_of_transpose_mulVec_eq_zero`. -/
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

/-- The squared residual is `‖b‖² - ‖A x‖²`.
Port of `NLAlib.IsLeastSquaresSolution.norm_sub_mulVec_sq_eq`. -/
theorem norm_sub_mulVec_sq (h : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2 =
      ‖WithLp.toLp 2 b‖ ^ 2 - ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 := by
  classical
  rw [norm_toLp_sq_eq_add_one_sub_rangeProjector A b, ← h.sub_mulVec_eq,
    ← h.mulVec_eq_rangeProjector_mulVec, add_sub_cancel_left]

/-- Two least-squares solutions have the same image under `A`. -/
theorem mulVec_eq {y : n → 𝕜} (hx : IsLeastSquaresSolution A b x)
    (hy : IsLeastSquaresSolution A b y) : A *ᵥ x = A *ᵥ y := by
  rw [hx.mulVec_eq_rangeProjector_mulVec, hy.mulVec_eq_rangeProjector_mulVec]

/-! ### The minimum-norm solution -/

/-- The pseudoinverse sends the image `A x` of a least-squares solution `x` to the pseudoinverse
solution: `pinv A *ᵥ (A *ᵥ x) = pinv A *ᵥ b`. So `pinv A *ᵥ b` is the projection of any
least-squares solution onto the row space of `A`. -/
theorem pinv_mulVec_mulVec (h : IsLeastSquaresSolution A b x) :
    pinv A *ᵥ (A *ᵥ x) = pinv A *ᵥ b := by
  rw [h.mulVec_eq_rangeProjector_mulVec, ← mul_pinv,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, pinv_mul_mul_pinv]

/-- **The pseudoinverse solution has the smallest norm** among least-squares solutions.
[GolubVanLoan2013, §5.5.2].
Port of `NLAlib.IsLeastSquaresSolution.norm_moorePenroseInverse_mulVec_le`.
Result: minimum-norm-least-squares -/
theorem norm_pinv_mulVec_le (h : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 (pinv A *ᵥ b)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  rw [← h.pinv_mulVec_mulVec, Matrix.mulVec_mulVec, pinv_mul]
  exact (isStarProjection_rangeProjector Aᴴ).norm_toLp_mulVec_le x

/-- A least-squares solution whose norm does not exceed that of the pseudoinverse solution is
the pseudoinverse solution. -/
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

/-- **The pseudoinverse solves least squares.** `pinv A *ᵥ b` is a least-squares solution.
[GolubVanLoan2013, §5.5.2].
Port of `NLAlib.isLeastSquaresSolution_moorePenroseInverse_mulVec`.
Result: least-squares-pseudoinverse -/
theorem isLeastSquaresSolution_pinv_mulVec (A : Matrix m n 𝕜) (b : m → 𝕜) :
    IsLeastSquaresSolution A b (pinv A *ᵥ b) := by
  rw [isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec, Matrix.mulVec_mulVec, mul_pinv]

/-- **Pythagoras for least squares**, through the pseudoinverse. For every `y`, the squared
residual is the squared optimal residual plus the squared distance, measured through `A`, from
`y` to the pseudoinverse solution. Every sketch-and-solve error bound starts from this.
[GolubVanLoan2013, §5.3.1]. -/
theorem norm_sub_mulVec_sq_eq_add_norm_mulVec_sub_pinv_sq [DecidableEq m] (A : Matrix m n 𝕜)
    (b : m → 𝕜) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (b - A *ᵥ y)‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖ ^ 2 +
        ‖WithLp.toLp 2 (A *ᵥ (y - pinv A *ᵥ b))‖ ^ 2 := by
  have h := isLeastSquaresSolution_pinv_mulVec A b
  rw [h.norm_sub_mulVec_sq_eq_add y, h.sub_mulVec_eq, ← neg_sub y, Matrix.mulVec_neg,
    WithLp.toLp_neg, norm_neg]

/-- A least-squares solution exists. Port of `NLAlib.exists_isLeastSquaresSolution`. -/
theorem exists_isLeastSquaresSolution (A : Matrix m n 𝕜) (b : m → 𝕜) :
    ∃ x, IsLeastSquaresSolution A b x := by
  exact ⟨pinv A *ᵥ b, isLeastSquaresSolution_pinv_mulVec A b⟩

/-- **All least-squares solutions.** They are the pseudoinverse solution plus an element of the
kernel of `A`: `x = pinv A b + (1 - pinv A A) z`. -/
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

/-- With full column rank the pseudoinverse solution is the only least-squares solution.
Port of `NLAlib.isLeastSquaresSolution_iff_eq_moorePenroseInverse_mulVec`. -/
theorem isLeastSquaresSolution_iff_eq_pinv_mulVec {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔ x = pinv A *ᵥ b := by
  constructor
  · intro h
    rw [← h.pinv_mulVec_mulVec, pinv_mulVec_mulVec_of_injective hA]
  · rintro rfl
    exact isLeastSquaresSolution_pinv_mulVec A b

/-- **Uniqueness.** The least-squares problem has a unique solution, for one right-hand side
or equivalently for all, exactly when `A` has full column rank.
Port of `NLAlib.existsUnique_isLeastSquaresSolution_iff`. -/
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

end NLAlib
