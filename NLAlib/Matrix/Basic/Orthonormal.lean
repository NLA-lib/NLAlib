/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.UnitaryGroup
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrices with orthonormal columns

`NLAlib.HasOrthonormalCols Q` says $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$. It is the
library's single spelling of orthonormality and is always taken as a hypothesis in this form.
Orthonormal rows are `HasOrthonormalCols Qᴴ`; a unitary matrix is a square $\mathbf{Q}$ with
`HasOrthonormalCols Q`.

## Main definitions

* `NLAlib.HasOrthonormalCols`: $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$.

## Main results

* `NLAlib.hasOrthonormalCols_iff_orthonormal`: the bridge to Mathlib's `Orthonormal`.
* `NLAlib.hasOrthonormalCols_iff_mem_unitaryGroup`: the bridge to `Matrix.unitaryGroup`.
* `NLAlib.HasOrthonormalCols.norm_toLp_mulVec`: multiplication by $\mathbf{Q}$ preserves the
  Euclidean norm.
* `NLAlib.HasOrthonormalCols.star_col_dotProduct_eq_zero_of_mem_span`: a column is orthogonal to
  the span of the other columns.
* `NLAlib.hasOrthonormalCols_replicateCol`: a unit vector as a column.
* `NLAlib.exists_norm_eq_one_and_norm_mulVec_sq_sub_norm_sq_eq`: the distortion
  $\|\mathbf{A}\mathbf{x}\|^2 - \|\mathbf{x}\|^2$ at $\mathbf{x} \ne \mathbf{0}$ through a unit
  vector.
* `NLAlib.HasOrthonormalCols.mulVec_injective`: $\mathbf{Q}$ has full column rank;
  `NLAlib.HasOrthonormalCols.mulVec_injective_of_mul`: so does $\mathbf{B}$ when
  $\mathbf{S}\mathbf{B}$ has orthonormal columns.
* `NLAlib.HasOrthonormalCols.mul_conjTranspose_self`: for square $\mathbf{Q}$, also
  $\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{I}$.
* `NLAlib.HasOrthonormalCols.hasOrthonormalCols_mul_diagonal`: a unitary times a diagonal of
  signs is unitary.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype m] [DecidableEq n]

/-- $\mathbf{Q}$ has orthonormal columns: $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$. Over
$\mathbb{R}$ this is $\mathbf{Q}^{\mathsf{T}}\mathbf{Q} = \mathbf{I}$. Orthonormal rows are
expressed by applying the predicate to $\mathbf{Q}^{\mathsf{H}}$, and a unitary matrix is a square
matrix with this property. -/
def HasOrthonormalCols (Q : Matrix m n 𝕜) : Prop :=
  Qᴴ * Q = 1

/-- `HasOrthonormalCols Q` unfolds to $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$. -/
theorem hasOrthonormalCols_iff {Q : Matrix m n 𝕜} : HasOrthonormalCols Q ↔ Qᴴ * Q = 1 :=
  Iff.rfl

namespace HasOrthonormalCols

/-- The defining equation $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$, as a rewrite rule. -/
theorem conjTranspose_mul_self {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : Qᴴ * Q = 1 :=
  hQ

end HasOrthonormalCols

/-! ### Bridges to Mathlib -/

/-- $\mathbf{Q}$ has orthonormal columns exactly when its columns are an orthonormal family in
`EuclideanSpace 𝕜 m`, in the sense of Mathlib's `Orthonormal`. -/
theorem hasOrthonormalCols_iff_orthonormal {Q : Matrix m n 𝕜} :
    HasOrthonormalCols Q ↔ Orthonormal 𝕜 fun j => WithLp.toLp 2 (Q.col j) := by
  rw [orthonormal_iff_ite, HasOrthonormalCols, ← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply, Matrix.one_apply, dotProduct]
  simp only [Matrix.conjTranspose_apply, Matrix.col_apply, Pi.star_apply, mul_comm]

/-- A square matrix has orthonormal columns exactly when it belongs to Mathlib's
`Matrix.unitaryGroup`. -/
theorem hasOrthonormalCols_iff_mem_unitaryGroup [Fintype n] {Q : Matrix n n 𝕜} :
    HasOrthonormalCols Q ↔ Q ∈ Matrix.unitaryGroup n 𝕜 :=
  Matrix.mem_unitaryGroup_iff'.symm

/-! ### Constructions -/

/-- The identity matrix has orthonormal columns. -/
theorem hasOrthonormalCols_one [Fintype n] : HasOrthonormalCols (1 : Matrix n n 𝕜) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_one, Matrix.one_mul]

open scoped ComplexOrder in
omit [DecidableEq n] in
/-- A zero diagonal entry of the Gram matrix forces the corresponding column to vanish.
This supplies the zero-column case when normalizing singular columns. -/
theorem col_eq_zero_of_conjTranspose_mul_self_apply_eq_zero (B : Matrix m n 𝕜) {i : n}
    (hi : (Bᴴ * B) i i = 0) : B.col i = 0 :=
  dotProduct_star_self_eq_zero.mp hi

/-- If the Gram matrix of $\mathbf{B}$ is the diagonal of the real squares $s_i^2$, then
any injectively selected columns with $s_i \ne 0$, divided by $s_i$, are orthonormal.
This is the shared normalization step for singular and generalized singular columns.
Proof material adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Factorizations/GeneralizedSVD.lean`. -/
theorem hasOrthonormalCols_div_of_conjTranspose_mul_self_eq_diagonal
    {B : Matrix m n 𝕜} {s : n → ℝ}
    (hB : Bᴴ * B = Matrix.diagonal (fun i => ((s i ^ 2 : ℝ) : 𝕜)))
    {r : Type*} [DecidableEq r] (e : r → n) (he : Function.Injective e)
    (hs : ∀ i, s (e i) ≠ 0) :
    HasOrthonormalCols (Matrix.of (fun j i => B j (e i) / (s (e i) : 𝕜))) := by
  ext i j
  have hij := congrArg (fun M : Matrix n n 𝕜 => M (e i) (e j)) hB
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply] at hij
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_div₀, RCLike.star_def, RCLike.conj_ofReal, div_mul_div_comm,
    ← Finset.sum_div, Matrix.one_apply]
  simp only [RCLike.star_def] at hij
  by_cases h : i = j
  · subst j
    simp only [ite_true] at hij ⊢
    rw [hij]
    have hi : (s (e i) : 𝕜) ≠ 0 := by exact_mod_cast hs i
    push_cast
    field_simp
  · have hij' : e i ≠ e j := fun h' => h (he h')
    simp only [hij', ite_false] at hij
    rw [hij]
    simp only [zero_div, h, ite_false]

namespace HasOrthonormalCols

/-- A product of matrices with orthonormal columns has orthonormal columns. -/
protected theorem mul [Fintype l] [DecidableEq m] {Q : Matrix l m 𝕜} {W : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (hW : HasOrthonormalCols W) : HasOrthonormalCols (Q * W) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ,
    hQ.conjTranspose_mul_self, Matrix.one_mul, hW.conjTranspose_mul_self]

/-- Relabelling the rows by a bijection and selecting columns by an injective map preserves
orthonormality of the columns. -/
protected theorem submatrix [Fintype l] [DecidableEq p] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (e₁ : l ≃ m) {e₂ : p → n} (he₂ : Function.Injective e₂) :
    HasOrthonormalCols (Q.submatrix e₁ e₂) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    hQ.conjTranspose_mul_self, Matrix.submatrix_one e₂ he₂]

end HasOrthonormalCols

/-- Two blocks of columns placed side by side have orthonormal columns exactly when each block
does and the blocks are mutually orthogonal. -/
theorem hasOrthonormalCols_fromCols_iff [DecidableEq p] {Q₁ : Matrix m n 𝕜}
    {Q₂ : Matrix m p 𝕜} :
    HasOrthonormalCols (Matrix.fromCols Q₁ Q₂) ↔
      HasOrthonormalCols Q₁ ∧ HasOrthonormalCols Q₂ ∧ Q₁ᴴ * Q₂ = 0 := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨h₁, h₁₂, -, h₂⟩
    exact ⟨h₁, h₂, h₁₂⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    refine ⟨h₁, h₁₂, ?_, h₂⟩
    rw [← Matrix.conjTranspose_eq_zero, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    exact h₁₂

/-- A unit vector, as a single column, has orthonormal columns: for $\|\mathbf{v}\| = 1$,
`HasOrthonormalCols (Matrix.replicateCol Unit v)`. -/
theorem hasOrthonormalCols_replicateCol {v : m → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1) :
    HasOrthonormalCols (Matrix.replicateCol Unit v) := by
  have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v)
  rw [hv, one_pow] at h
  rw [hasOrthonormalCols_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.replicateCol_apply,
    RCLike.star_def, RCLike.conj_mul, Matrix.one_apply, Subsingleton.elim a b, if_true]
  exact_mod_cast h.symm

omit [DecidableEq n] in
/-- Reduction of the distortion to unit vectors: a nonzero $\mathbf{x}$ is $\|\mathbf{x}\|$
times the unit vector $\mathbf{u} = \mathbf{x}/\|\mathbf{x}\|$, and for every matrix
$\mathbf{A}$,
$\|\mathbf{A}\mathbf{x}\|^2 - \|\mathbf{x}\|^2
= \|\mathbf{x}\|^2 (\|\mathbf{A}\mathbf{u}\|^2 - 1)$. It transfers every JL statement on unit
vectors to all vectors. -/
theorem exists_norm_eq_one_and_norm_mulVec_sq_sub_norm_sq_eq {k : Type*} [Fintype k] [Fintype n]
    {x : n → 𝕜} (hx : x ≠ 0) :
    ∃ u : n → 𝕜, ‖WithLp.toLp 2 u‖ = 1 ∧ ∀ A : Matrix k n 𝕜,
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2 =
        ‖WithLp.toLp 2 x‖ ^ 2 * (‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 - 1) := by
  set c := ‖WithLp.toLp 2 x‖ with hc
  have hc0 : 0 < c := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  refine ⟨(c⁻¹ : ℝ) • x, ?_, fun A => ?_⟩
  · rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0,
      inv_mul_cancel₀ hc0.ne']
  · have hx' : x = c • ((c⁻¹ : ℝ) • x) := by rw [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
    conv_lhs => rw [hx']
    rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    ring

namespace HasOrthonormalCols

variable [Fintype n]

/-! ### Cancellation -/

/-- $\mathbf{Q}^{\mathsf{H}}$ cancels $\mathbf{Q}$ on the left of a product:
$\mathbf{Q}^{\mathsf{H}}(\mathbf{Q}\mathbf{A}) = \mathbf{A}$. -/
theorem conjTranspose_mul_cancel_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix n p 𝕜) : Qᴴ * (Q * A) = A := by
  rw [← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul]

/-- $\mathbf{Q}$ cancels $\mathbf{Q}^{\mathsf{H}}$ on the right of a product:
$\mathbf{A}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{A}$. -/
theorem mul_conjTranspose_mul_cancel_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : A * Qᴴ * Q = A := by
  rw [Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.mul_one]

/-- $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{Q}$: the projector
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ fixes the columns of $\mathbf{Q}$. -/
theorem mul_conjTranspose_mul_self {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Q * Qᴴ * Q = Q :=
  hQ.mul_conjTranspose_mul_cancel_right Q

/-- The residual of the projection onto the columns of $\mathbf{Q}$ is annihilated by
$\mathbf{Q}$:
$(\mathbf{A} - \mathbf{A}\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{Q} = \mathbf{0}$. -/
theorem sub_mul_mul_conjTranspose_mul_eq_zero {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p m 𝕜) : (A - A * Q * Qᴴ) * Q = 0 := by
  rw [Matrix.sub_mul, Matrix.mul_assoc (A * Q), hQ.conjTranspose_mul_self, Matrix.mul_one,
    sub_self]

/-- Multiplication by $\mathbf{Q}$ on the left preserves Gram products:
$(\mathbf{Q}\mathbf{A})^{\mathsf{H}}(\mathbf{Q}\mathbf{B}) = \mathbf{A}^{\mathsf{H}}\mathbf{B}$.
In particular $(\mathbf{Q}\mathbf{A})^{\mathsf{H}}(\mathbf{Q}\mathbf{A})
= \mathbf{A}^{\mathsf{H}}\mathbf{A}$. -/
theorem conjTranspose_mul_mul {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜)
    (B : Matrix n l 𝕜) : (Q * A)ᴴ * (Q * B) = Aᴴ * B := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hQ.conjTranspose_mul_cancel_left]

/-- Left multiplication by a matrix with orthonormal columns is injective:
$\mathbf{Q}\mathbf{A} = \mathbf{Q}\mathbf{B}$ iff $\mathbf{A} = \mathbf{B}$. -/
theorem mul_right_inj {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) {A B : Matrix n p 𝕜} :
    Q * A = Q * B ↔ A = B := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [← hQ.conjTranspose_mul_cancel_left A, h, hQ.conjTranspose_mul_cancel_left]

/-! ### Action on vectors -/

/-- A matrix with orthonormal columns has full column rank:
$\mathbf{x} \mapsto \mathbf{Q}\mathbf{x}$ is injective. -/
theorem mulVec_injective {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Function.Injective Q.mulVec := by
  intro x y h
  have h' := congrArg (Qᴴ *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec] using h'

/-- If a product $\mathbf{S}\mathbf{B}$ has orthonormal columns, the right factor $\mathbf{B}$ has
full column rank: `B.mulVec` is injective. A sketched basis $\mathbf{S}\mathbf{A}\mathbf{M}$ with
orthonormal columns thus certifies that $\mathbf{A}\mathbf{M}$ and $\mathbf{M}$ have full column
rank. -/
theorem mulVec_injective_of_mul [Fintype l] {S : Matrix l m 𝕜} {B : Matrix m n 𝕜}
    (h : HasOrthonormalCols (S * B)) : Function.Injective B.mulVec := by
  refine Function.Injective.of_comp (f := S.mulVec) ?_
  have hcomp : S.mulVec ∘ B.mulVec = (S * B).mulVec := by
    ext x : 1
    simp only [Function.comp_apply, Matrix.mulVec_mulVec]
  rw [hcomp]
  exact h.mulVec_injective

/-- $\mathbf{Q}^{\mathsf{H}}$ undoes $\mathbf{Q}$ on vectors:
$\mathbf{Q}^{\mathsf{H}}(\mathbf{Q}\mathbf{x}) = \mathbf{x}$. -/
theorem conjTranspose_mulVec_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (x : n → 𝕜) :
    Qᴴ *ᵥ (Q *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec]

/-- Multiplication by $\mathbf{Q}$ preserves the pairing $\mathbf{x}^{\mathsf{H}}\mathbf{y}$:
$(\mathbf{Q}\mathbf{x})^{\mathsf{H}}(\mathbf{Q}\mathbf{y}) = \mathbf{x}^{\mathsf{H}}\mathbf{y}$. -/
theorem star_mulVec_dotProduct_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (x y : n → 𝕜) : star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hQ.conjTranspose_mulVec_mulVec]

omit [Fintype n] in
/-- A column of a matrix with orthonormal columns is orthogonal to the span of the other columns:
for $i \notin s$ and $\mathbf{x} \in \operatorname{span}\{\mathbf{q}_k : k \in s\}$,
$\mathbf{q}_i^{\mathsf{H}}\mathbf{x} = 0$, with $\mathbf{q}_k$ column $k$ of $\mathbf{Q}$. -/
theorem star_col_dotProduct_eq_zero_of_mem_span {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    {s : Set n} {i : n} (hi : i ∉ s) {x : m → 𝕜} (hx : x ∈ Submodule.span 𝕜 (Q.col '' s)) :
    star (Q.col i) ⬝ᵥ x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    have h := congrFun (congrFun hQ.conjTranspose_mul_self i) k
    rw [Matrix.one_apply_ne (fun h => hi (by rw [h]; exact hk)), Matrix.mul_apply'] at h
    exact h
  | zero => exact dotProduct_zero _
  | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
  | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]

/-- Multiplication by a matrix with orthonormal columns preserves the Euclidean norm:
$\|\mathbf{Q}\mathbf{x}\| = \|\mathbf{x}\|$. -/
theorem norm_toLp_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct,
    EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct, hQ.star_mulVec_dotProduct_mulVec]

omit [Fintype n] in
/-- The columns of a matrix with orthonormal columns are unit vectors:
$\|\mathbf{Q}\mathbf{e}_j\| = 1$. -/
theorem norm_toLp_col {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (j : n) :
    ‖WithLp.toLp 2 (Q.col j)‖ = 1 := by
  have h := congrFun (congrFun hQ.conjTranspose_mul_self j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
  rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct]
  simp only [dotProduct, Matrix.col_apply, Pi.star_apply, Matrix.conjTranspose_apply] at h ⊢
  rw [h, RCLike.one_re]

/-- Multiplication by $\mathbf{Q}^{\mathsf{H}}$ does not increase the Euclidean norm (Bessel's
inequality): $\|\mathbf{Q}^{\mathsf{H}}\mathbf{x}\| \le \|\mathbf{x}\|$. -/
theorem norm_toLp_conjTranspose_mulVec_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (x : m → 𝕜) : ‖WithLp.toLp 2 (Qᴴ *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have h := (hasOrthonormalCols_iff_orthonormal.mp hQ).sum_inner_products_le
    (x := WithLp.toLp 2 x) (s := Finset.univ)
  rw [EuclideanSpace.norm_sq_eq]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) h
  simp only [EuclideanSpace.inner_toLp_toLp, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Matrix.col_apply, Pi.star_apply, mul_comm]

/-! ### Rank and size -/

/-- A matrix with orthonormal columns has at most as many columns as rows:
$\lvert n \rvert \le \lvert m \rvert$. -/
theorem card_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Fintype.card n ≤ Fintype.card m := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := Q.mulVecLin) hQ.mulVec_injective
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h

/-- A matrix with orthonormal columns has rank equal to its number of columns,
$\operatorname{rank} \mathbf{Q} = \lvert n \rvert$. -/
theorem rank_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : Q.rank = Fintype.card n := by
  refine le_antisymm Q.rank_le_card_width ?_
  have h := Matrix.rank_mul_le_right Qᴴ Q
  rwa [hQ.conjTranspose_mul_self, Matrix.rank_one] at h

/-- Left multiplication by a matrix with orthonormal columns preserves rank:
$\operatorname{rank}(\mathbf{Q}\mathbf{A}) = \operatorname{rank} \mathbf{A}$. -/
theorem rank_mul [Fintype p] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    (Q * A).rank = A.rank := by
  refine le_antisymm (Matrix.rank_mul_le_right Q A) ?_
  have h := Matrix.rank_mul_le_right Qᴴ (Q * A)
  rwa [hQ.conjTranspose_mul_cancel_left] at h

/-! ### Square matrices -/

/-- A matrix with orthonormal columns and as many rows as columns also satisfies
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{I}$. The row and column index types may differ. -/
theorem mul_conjTranspose_self_of_card_eq [DecidableEq m] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (h : Fintype.card m = Fintype.card n) : Q * Qᴴ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq m n 𝕜 h).mpr hQ

/-- A square matrix with orthonormal columns satisfies
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{I}$. -/
theorem mul_conjTranspose_self {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : Q * Qᴴ = 1 :=
  hQ.mul_conjTranspose_self_of_card_eq rfl

/-- If $\mathbf{Q}$ has orthonormal columns and as many rows as columns, then
$\mathbf{Q}^{\mathsf{H}}$ has orthonormal columns. -/
theorem conjTranspose_of_card_eq [DecidableEq m] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (h : Fintype.card m = Fintype.card n) :
    HasOrthonormalCols Qᴴ := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose]
  exact hQ.mul_conjTranspose_self_of_card_eq h

/-- The conjugate transpose of a square matrix with orthonormal columns has orthonormal
columns. -/
protected theorem conjTranspose {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) :
    HasOrthonormalCols Qᴴ :=
  hQ.conjTranspose_of_card_eq rfl

/-- A square matrix with orthonormal columns is invertible. -/
theorem isUnit {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : IsUnit Q :=
  isUnit_iff_exists.mpr ⟨Qᴴ, hQ.mul_conjTranspose_self, hQ⟩

/-- The inverse of a square matrix with orthonormal columns is its conjugate transpose:
$\mathbf{Q}^{-1} = \mathbf{Q}^{\mathsf{H}}$. -/
theorem inv_eq {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : Q⁻¹ = Qᴴ :=
  Matrix.inv_eq_left_inv hQ

/-- A unitary times a diagonal of signs is unitary: if
$\mathbf{F}^{\mathsf{H}}\mathbf{F} = \mathbf{I}$ and $y_i^2 = 1$ for every $i$, then
$\mathbf{D} = \operatorname{diag}(\mathbf{y})$ has $\mathbf{D}^{\mathsf{H}}\mathbf{D} = \mathbf{I}$
and $(\mathbf{F}\mathbf{D})^{\mathsf{H}}\mathbf{F}\mathbf{D} = \mathbf{D}^{\mathsf{H}}\mathbf{D}
= \mathbf{I}$. -/
theorem hasOrthonormalCols_mul_diagonal {F : Matrix n n 𝕜}
    (hF : HasOrthonormalCols F) {y : n → ℝ} (hy : ∀ i, y i ^ 2 = 1) :
    HasOrthonormalCols (F * Matrix.diagonal fun i => (y i : 𝕜)) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ,
    hF.conjTranspose_mul_self, Matrix.one_mul, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← sq, hy i,
    RCLike.ofReal_one]

end HasOrthonormalCols

end NLAlib
