/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Spectral.Congruence

/-!
# Generalized singular value decomposition

For rectangular matrices with a common column type, `NLAlib.IsGSVD A B X c s` records
invertible common right coordinates that diagonalize both Gram matrices. The nonnegative
coordinate pairs satisfy $c_i^2+s_i^2=1$ on the active coordinates and vanish together on
the common kernel. The columns of $\mathbf{X}$ need not be orthonormal.

This is the normalized Gram formulation of the GSVD in [PaigeSaunders1981]. Active and inactive
coordinates are represented by subsets of the common column type, without an ordering or
relative row-dimension assumption.
Proof material adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Factorizations/GeneralizedSVD.lean`.

## Main results

* `NLAlib.exists_isGSVD`: existence for every rectangular pair, including rank deficiency.
* `NLAlib.IsGSVD.rank_fromRows`: the active-coordinate count is the stacked rank.
* `NLAlib.IsGSVD.mulVec_eq_zero_iff`: the common kernel in generalized singular coordinates.
* `NLAlib.IsGSVD.hasOrthonormalCols_div`: normalized positive columns are orthonormal.
* `NLAlib.IsGSVD.col_mul_eq_zero`: a zero generalized singular value gives a zero column.
* `NLAlib.IsGSVD.ker_inf_ker_eq_span`: inactive columns span the common kernel.

`NLAlib.IsGSVD.swap` exchanges the pair, so the column results apply to either matrix.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- Normalized generalized singular coordinates for two rectangular matrices with a common
column type. The invertible $\mathbf{X}$ diagonalizes both Gram matrices, with nonnegative
$c_i,s_i$ and $c_i^2+s_i^2$ equal to zero or one. The zero pairs represent the common kernel;
$\mathbf{X}$ is not required to be unitary. [PaigeSaunders1981, pp. 398–405]; the normalized
Gram formulation avoids a choice of ordering and permits arbitrary finite index types. -/
structure IsGSVD (A : Matrix m n 𝕜) (B : Matrix p n 𝕜)
    (X : Matrix n n 𝕜) (c s : n → ℝ) : Prop where
  /-- The common right coordinate matrix is invertible. -/
  isUnit : IsUnit X
  /-- The first Gram matrix is diagonal in the common right coordinates. -/
  conjTranspose_mul_mul_left :
    Xᴴ * (Aᴴ * A) * X = Matrix.diagonal (fun i => ((c i ^ 2 : ℝ) : 𝕜))
  /-- The second Gram matrix is diagonal in the common right coordinates. -/
  conjTranspose_mul_mul_right :
    Xᴴ * (Bᴴ * B) * X = Matrix.diagonal (fun i => ((s i ^ 2 : ℝ) : 𝕜))
  /-- The generalized singular values for the first matrix are nonnegative. -/
  nonneg_left : ∀ i, 0 ≤ c i
  /-- The generalized singular values for the second matrix are nonnegative. -/
  nonneg_right : ∀ i, 0 ≤ s i
  /-- Each coordinate is inactive or has squared generalized singular values summing to one. -/
  normalized : ∀ i, c i ^ 2 + s i ^ 2 = 0 ∨ c i ^ 2 + s i ^ 2 = 1

namespace IsGSVD

variable {A : Matrix m n 𝕜} {B : Matrix p n 𝕜}
  {X : Matrix n n 𝕜} {c s : n → ℝ}

/-- Exchanging the matrices exchanges their generalized singular values and keeps the same
common right coordinates. This lets each column lemma serve both sides of the pair. -/
theorem swap (h : IsGSVD A B X c s) : IsGSVD B A X s c :=
  ⟨h.isUnit, h.conjTranspose_mul_mul_right, h.conjTranspose_mul_mul_left,
    h.nonneg_right, h.nonneg_left, fun i => by simpa only [add_comm] using h.normalized i⟩

/-- The Gram matrix of the transformed columns is the diagonal of their squared generalized
singular values. Apply `IsGSVD.swap` to obtain the equation for the other matrix. -/
theorem conjTranspose_mul_self_mul (h : IsGSVD A B X c s) :
    (A * X)ᴴ * (A * X) = Matrix.diagonal (fun i => ((c i ^ 2 : ℝ) : 𝕜)) := by
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h.conjTranspose_mul_mul_left

/-- The stacked Gram matrix in normalized common right coordinates is the diagonal of
$c_i^2+s_i^2$, which is the indicator of the active coordinates. -/
theorem conjTranspose_mul_mul_fromRows (h : IsGSVD A B X c s) :
    Xᴴ * ((Matrix.fromRows A B)ᴴ * Matrix.fromRows A B) * X =
      Matrix.diagonal (fun i => ((c i ^ 2 + s i ^ 2 : ℝ) : 𝕜)) := by
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows,
    Matrix.mul_add, Matrix.add_mul, h.conjTranspose_mul_mul_left,
    h.conjTranspose_mul_mul_right, Matrix.diagonal_add]
  simp only [map_add]

end IsGSVD

/-- **Normalized GSVD of a rectangular pair.** Every pair
$\mathbf{A},\mathbf{B}$ of real or complex rectangular matrices with a common column type
admits invertible right coordinates $\mathbf{X}$ with
$$\mathbf{X}^{\mathsf{H}}\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{X}
  =\operatorname{diag}(c_i^2),\qquad
\mathbf{X}^{\mathsf{H}}\mathbf{B}^{\mathsf{H}}\mathbf{B}\mathbf{X}
  =\operatorname{diag}(s_i^2),$$
where $c_i,s_i\ge0$ and $c_i^2+s_i^2\in\{0,1\}$. Empty dimensions and arbitrary common
kernels are included. [PaigeSaunders1981, pp. 398–405]; stated here in normalized Gram form
over any `RCLike` field and arbitrary finite index types.
Result: gsvd-normalized-pair -/
theorem exists_isGSVD (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    ∃ X c s, IsGSVD A B X c s := by
  obtain ⟨X, a, b, hX, hA, hB, ha, hb, hab⟩ :=
    (Matrix.posSemidef_conjTranspose_mul_self A).exists_conjTranspose_mul_mul_eq_diagonal
      (Matrix.posSemidef_conjTranspose_mul_self B)
  refine ⟨X, fun i => Real.sqrt (a i), fun i => Real.sqrt (b i),
    (Matrix.isUnit_iff_isUnit_det X).mpr hX, ?_, ?_,
    fun i => Real.sqrt_nonneg _, fun i => Real.sqrt_nonneg _, ?_⟩
  · simpa only [Real.sq_sqrt (ha _)] using hA
  · simpa only [Real.sq_sqrt (hb _)] using hB
  · simpa only [Real.sq_sqrt (ha _), Real.sq_sqrt (hb _)] using hab

namespace IsGSVD

variable {A : Matrix m n 𝕜} {B : Matrix p n 𝕜}
  {X : Matrix n n 𝕜} {c s : n → ℝ}

/-- **The active-coordinate count in a GSVD.** For normalized generalized singular
coordinates of $\mathbf{A},\mathbf{B}$, the rank of the stacked matrix
$\begin{bmatrix}\mathbf{A}\\\mathbf{B}\end{bmatrix}$ is the number of coordinates with
$c_i^2+s_i^2=1$. Zero matrices and empty dimensions are included.
[PaigeSaunders1981, pp. 398–405]; the rank statement is expressed through the normalized
Gram coordinates without choosing an ordering.
Result: gsvd-normalized-pair -/
theorem rank_fromRows (h : IsGSVD A B X c s) :
    (Matrix.fromRows A B).rank = Fintype.card {i // c i ^ 2 + s i ^ 2 = 1} := by
  classical
  have he := congrArg Matrix.rank h.conjTranspose_mul_mul_fromRows
  rw [Matrix.rank_mul_eq_left_of_isUnit_det X _ ((Matrix.isUnit_iff_isUnit_det X).mp h.isUnit),
    Matrix.rank_mul_eq_right_of_isUnit_det Xᴴ _ ((Matrix.isUnit_iff_isUnit_det Xᴴ).mp
      ((Matrix.isUnit_conjTranspose X).mpr h.isUnit)), Matrix.rank_conjTranspose_mul_self,
    Matrix.rank_diagonal] at he
  convert he using 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  rcases h.normalized i with hi | hi <;> simp [hi]

/-- In normalized generalized singular coordinates, $\mathbf{X}\mathbf{y}$ belongs to
the common kernel of $\mathbf{A},\mathbf{B}$ exactly when every active coordinate of
$\mathbf{y}$ vanishes. The stacked equation represents both kernel conditions. -/
theorem mulVec_eq_zero_iff (h : IsGSVD A B X c s) (y : n → 𝕜) :
    (Matrix.fromRows A B) *ᵥ (X *ᵥ y) = 0 ↔
      ∀ i, c i ^ 2 + s i ^ 2 = 1 → y i = 0 := by
  rw [← Matrix.conjTranspose_mul_self_mulVec_eq_zero (Matrix.fromRows A B)]
  have hi : Function.Injective Xᴴ.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_conjTranspose X).mpr h.isUnit)
  rw [← hi.eq_iff]
  rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h.conjTranspose_mul_mul_fromRows, funext_iff]
  simp only [Matrix.mulVec_diagonal, Pi.zero_apply]
  constructor
  · intro hh i hi
    simpa only [hi, RCLike.ofReal_one, one_mul] using hh i
  · intro hh i
    rcases h.normalized i with hi | hi
    · rw [hi, RCLike.ofReal_zero, zero_mul]
    · rw [hi, RCLike.ofReal_one, one_mul, hh i hi]

/-- The columns of $\mathbf{A}\mathbf{X}$ with $c_i>0$, divided by $c_i$, are orthonormal
for normalized generalized singular coordinates. The positive-column set may be empty.
Apply `IsGSVD.swap` for the corresponding columns of $\mathbf{B}\mathbf{X}$. -/
theorem hasOrthonormalCols_div (h : IsGSVD A B X c s) :
    HasOrthonormalCols (Matrix.of (fun i (j : {j // 0 < c j}) =>
      (A * X) i j / (c j : 𝕜))) := by
  classical
  exact hasOrthonormalCols_div_of_conjTranspose_mul_self_eq_diagonal
    h.conjTranspose_mul_self_mul Subtype.val Subtype.val_injective
    (fun i => ne_of_gt i.property)

/-- A zero generalized singular value $c_i=0$ forces column $i$ of
$\mathbf{A}\mathbf{X}$ to vanish. Apply `IsGSVD.swap` for the other matrix. -/
theorem col_mul_eq_zero (h : IsGSVD A B X c s) (i : n) (hi : c i = 0) :
    (A * X).col i = 0 := by
  apply col_eq_zero_of_conjTranspose_mul_self_apply_eq_zero
  rw [h.conjTranspose_mul_self_mul, Matrix.diagonal_apply_eq, hi, zero_pow two_ne_zero,
    RCLike.ofReal_zero]

/-- **The common-kernel block of a GSVD.** For normalized generalized singular coordinates
of $\mathbf{A},\mathbf{B}$, their common kernel is precisely the span of the columns of
$\mathbf{X}$ with $c_i^2+s_i^2=0$. This includes an empty common-kernel block and the case
where every coordinate is inactive. [PaigeSaunders1981, pp. 398–405]; the block is stated as
an indexed span, without permuting the inactive coordinates to the end.
Result: gsvd-normalized-pair -/
theorem ker_inf_ker_eq_span (h : IsGSVD A B X c s) :
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin =
      Submodule.span 𝕜 (X.col '' {i | c i ^ 2 + s i ^ 2 = 0}) := by
  classical
  apply le_antisymm
  · intro z hz
    obtain ⟨y, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr h.isUnit z
    have hy := (h.mulVec_eq_zero_iff y).mp (show
        (Matrix.fromRows A B) *ᵥ (X *ᵥ y) = 0 from by
      rw [Matrix.fromRows_mulVec]
      ext i
      cases i with
      | inl i => exact congrFun hz.1 i
      | inr i => exact congrFun hz.2 i)
    rw [Matrix.mulVec_eq_sum]
    apply Submodule.sum_mem
    intro i _
    rw [op_smul_eq_smul]
    change y i • X.col i ∈ _
    rcases h.normalized i with hi | hi
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [hy i hi, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change c i ^ 2 + s i ^ 2 = 0 at hi
    have hc : c i = 0 := by nlinarith [sq_nonneg (s i), sq_nonneg (c i)]
    have hs : s i = 0 := by nlinarith [sq_nonneg (s i), sq_nonneg (c i)]
    exact ⟨h.col_mul_eq_zero i hc, h.swap.col_mul_eq_zero i hs⟩

end IsGSVD

end NLAlib
