/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import NLAlib.Matrix.Basic.SchurComplement
public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Pseudoinverse.Pinv
public import NLAlib.Matrix.Spectral.SpectralRadius

/-!
# Positive semidefinite block matrices

Criteria for a Hermitian block matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\
\mathbf{B}^{\mathsf{H}} & \mathbf{C} \end{bmatrix}$ to be positive semidefinite that do not need an
inverse: the Cauchy–Schwarz test on the off-diagonal block, the factorisation
$\mathbf{B} = \mathbf{A}^{1/2}\mathbf{X}\mathbf{C}^{1/2}$ with a contraction $\mathbf{X}$, and the
special cases with identity or equal diagonal blocks. The Schur complement criteria are in
`NLAlib.Matrix.Basic.SchurComplement` and `NLAlib.Matrix.Pseudoinverse.GeneralizedSchur`.

## Main results

* `Matrix.PosSemidef.norm_star_dotProduct_mulVec_sq_le`: Cauchy–Schwarz for a positive
  semidefinite form.
* `Matrix.PosSemidef.posSemidef_fromBlocks_iff_forall_norm_sq_le`: the bilinear test.
* `Matrix.PosSemidef.posSemidef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt`: the contraction factor.
* `Matrix.PosDef.posDef_fromBlocks_iff_forall_norm_sq_lt`: the strict bilinear test.
* `Matrix.PosDef.posDef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt`: strict contraction factors.
* `Matrix.PosDef.posDef_fromBlocks_iff_specRadius_lt_one`: the relative spectral-radius test.
* `NLAlib.posSemidef_fromBlocks_one_iff_specNorm_le_one`.
* `NLAlib.posSemidef_fromBlocks_self_iff`: equal diagonal blocks.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Cauchy–Schwarz -/

/-- **Cauchy–Schwarz for a positive semidefinite form**: for positive semidefinite $\mathbf{A}$,
$$\lvert \mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{y} \rvert^2
  \le \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})
  \operatorname{Re}(\mathbf{y}^{\mathsf{H}}\mathbf{A}\mathbf{y})\,.$$
[HornJohnson2013, §7.7]. -/
theorem _root_.Matrix.PosSemidef.norm_star_dotProduct_mulVec_sq_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (x y : n → 𝕜) :
    ‖star x ⬝ᵥ A *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm A y) := by
  classical
  have hSS : (CFC.sqrt A)ᴴ * CFC.sqrt A = A := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  generalize CFC.sqrt A = S at hSS
  subst hSS
  rw [quadForm_conjTranspose_mul_self, quadForm_conjTranspose_mul_self, RCLike.ofReal_re,
    RCLike.ofReal_re, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    ← EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-- The real part of the quadratic form of a block matrix with off-diagonal blocks
$\mathbf{B}$ and $\mathbf{B}^{\mathsf{H}}$ (the diagonal blocks are arbitrary):
$$\operatorname{Re}\left(\begin{bmatrix} \mathbf{x} \\ \mathbf{y} \end{bmatrix}^{\mathsf{H}}
  \begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{B}^{\mathsf{H}} & \mathbf{C} \end{bmatrix}
  \begin{bmatrix} \mathbf{x} \\ \mathbf{y} \end{bmatrix}\right)
  = \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) +
  2\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{B}\mathbf{y}) +
  \operatorname{Re}(\mathbf{y}^{\mathsf{H}}\mathbf{C}\mathbf{y})\,.$$ -/
theorem re_quadForm_fromBlocks (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n n 𝕜)
    (x : m → 𝕜) (y : n → 𝕜) :
    RCLike.re (quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim x y)) =
      RCLike.re (quadForm A x) + 2 * RCLike.re (star x ⬝ᵥ B *ᵥ y) +
        RCLike.re (quadForm C y) := by
  have h : star y ⬝ᵥ (Bᴴ *ᵥ x) = star (star x ⬝ᵥ (B *ᵥ y)) := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.dotProduct_mulVec]
  simp only [quadForm, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Function.star_sumElim, sumElim_dotProduct_sumElim, dotProduct_add, h, map_add,
    RCLike.star_def, RCLike.conj_re]
  ring

/-! ### The bilinear test -/

/-- If the block matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{B}^{\mathsf{H}} &
\mathbf{C} \end{bmatrix}$ is positive semidefinite, its off-diagonal block satisfies the
Cauchy–Schwarz bound
$$\lvert \mathbf{x}^{\mathsf{H}}\mathbf{B}\mathbf{y} \rvert^2 \le
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})
\operatorname{Re}(\mathbf{y}^{\mathsf{H}}\mathbf{C}\mathbf{y})\,.$$
[HornJohnson2013, Theorem 7.7.7]. -/
theorem _root_.Matrix.PosSemidef.norm_star_dotProduct_mulVec_sq_le_of_fromBlocks {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (x : m → 𝕜) (y : n → 𝕜) :
    ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm C y) := by
  have h1 := h.norm_star_dotProduct_mulVec_sq_le (Sum.elim x 0) (Sum.elim 0 y)
  simpa only [quadForm, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Function.star_sumElim, sumElim_dotProduct_sumElim, star_zero, Matrix.mulVec_zero,
    zero_dotProduct, dotProduct_zero, add_zero, zero_add] using h1

/-- **The bilinear test.** For positive semidefinite $\mathbf{A}$ and $\mathbf{C}$, the block
matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{B}^{\mathsf{H}} & \mathbf{C}
\end{bmatrix}$ is positive semidefinite exactly when
$$\lvert \mathbf{x}^{\mathsf{H}}\mathbf{B}\mathbf{y} \rvert^2 \le
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})
\operatorname{Re}(\mathbf{y}^{\mathsf{H}}\mathbf{C}\mathbf{y})$$
for all $\mathbf{x}$, $\mathbf{y}$.
[HornJohnson2013, Theorem 7.7.7].
Result: block-positivity -/
theorem _root_.Matrix.PosSemidef.posSemidef_fromBlocks_iff_forall_norm_sq_le {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      ∀ (x : m → 𝕜) (y : n → 𝕜),
        ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm C y) := by
  refine ⟨Matrix.PosSemidef.norm_star_dotProduct_mulVec_sq_le_of_fromBlocks, fun h => ?_⟩
  have hH : (Matrix.fromBlocks A B Bᴴ C).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hA.isHermitian rfl hC.isHermitian
  rw [posSemidef_iff_quadForm_nonneg]
  refine ⟨hH, fun z => ?_⟩
  obtain ⟨x, y, rfl⟩ : ∃ x y, z = Sum.elim x y :=
    ⟨z ∘ Sum.inl, z ∘ Sum.inr, (Sum.elim_comp_inl_inr z).symm⟩
  rw [← hH.coe_re_quadForm, RCLike.ofReal_nonneg, re_quadForm_fromBlocks]
  have ha := hA.re_quadForm_nonneg x
  have hc := hC.re_quadForm_nonneg y
  have hb := h x y
  have hre : RCLike.re (star x ⬝ᵥ B *ᵥ y) ^ 2 ≤ ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (RCLike.abs_re_le_norm _) 2
  have hsq : (2 * RCLike.re (star x ⬝ᵥ B *ᵥ y)) ^ 2 ≤
      (RCLike.re (quadForm A x) + RCLike.re (quadForm C y)) ^ 2 := by
    nlinarith [sq_nonneg (RCLike.re (quadForm A x) - RCLike.re (quadForm C y))]
  have := (abs_le_of_sq_le_sq' hsq (add_nonneg ha hc)).1
  linarith

/-! ### Contraction factors -/

/-- $\begin{bmatrix} \mathbf{I} & \mathbf{X} \\ \mathbf{X}^{\mathsf{H}} & \mathbf{I} \end{bmatrix}$
is positive semidefinite exactly when $\|\mathbf{X}\|_2 \le 1$.
[HornJohnson2013, §7.7]. -/
theorem posSemidef_fromBlocks_one_iff_specNorm_le_one [DecidableEq m] [DecidableEq n]
    (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks 1 X Xᴴ 1).PosSemidef ↔ specNorm X ≤ 1 := by
  rw [posSemidef_fromBlocks_iff_exists, ← sq_le_one_iff₀ (specNorm_nonneg X),
    specNorm_sq_le_iff_conjTranspose_mul_self_le zero_le_one, one_smul, Matrix.le_iff]
  constructor
  · rintro ⟨-, Y, hY, h⟩
    rw [Matrix.one_mul] at hY
    subst hY
    rwa [Matrix.mul_one] at h
  · intro h
    exact ⟨Matrix.PosSemidef.one, X, Matrix.one_mul X, by rwa [Matrix.mul_one]⟩

/-- $\mathbf{I} - \mathbf{X}^{\mathsf{H}}\mathbf{X}$ is positive definite exactly when
$\|\mathbf{X}\|_2 < 1$. -/
private theorem posDef_one_sub_conjTranspose_mul_self_iff [DecidableEq n] (X : Matrix m n 𝕜) :
    (1 - Xᴴ * X).PosDef ↔ specNorm X < 1 := by
  have hH : (1 - Xᴴ * X).IsHermitian :=
    Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self X)
  have hq : ∀ x : n → 𝕜, RCLike.re (quadForm (1 - Xᴴ * X) x) =
      ‖WithLp.toLp 2 x‖ ^ 2 - ‖WithLp.toLp 2 (X *ᵥ x)‖ ^ 2 := by
    intro x
    rw [quadForm_sub_left, map_sub, quadForm_one, quadForm_conjTranspose_mul_self,
      RCLike.ofReal_re, RCLike.ofReal_re]
  constructor
  · intro h
    rcases isEmpty_or_nonempty n with hn | hn
    · rw [Subsingleton.elim X 0, specNorm_zero]
      exact zero_lt_one
    · obtain ⟨u, hu, hXu⟩ := exists_norm_eq_one_and_norm_mulVec_eq_specNorm X
      have hu0 : u ≠ 0 := by
        rintro rfl
        simp at hu
      have hpos := h.re_quadForm_pos hu0
      rw [hq, hu, hXu] at hpos
      nlinarith [specNorm_nonneg X]
  · intro h
    rw [posDef_iff_quadForm_pos]
    refine ⟨hH, fun x hx => ?_⟩
    rw [← hH.coe_re_quadForm, hq, RCLike.ofReal_pos]
    have hx' : 0 < ‖WithLp.toLp 2 x‖ := by
      have : WithLp.toLp 2 x ≠ 0 := by simpa using hx
      positivity
    have h1 := norm_toLp_mulVec_le X x
    have h2 : ‖WithLp.toLp 2 (X *ᵥ x)‖ < ‖WithLp.toLp 2 x‖ :=
      h1.trans_lt (by nlinarith)
    nlinarith [norm_nonneg (WithLp.toLp 2 (X *ᵥ x))]

/-- $\begin{bmatrix} \mathbf{I} & \mathbf{X} \\ \mathbf{X}^{\mathsf{H}} & \mathbf{I} \end{bmatrix}$
is positive definite exactly when $\|\mathbf{X}\|_2 < 1$. -/
theorem posDef_fromBlocks_one_iff_specNorm_lt_one [DecidableEq m] [DecidableEq n]
    (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks 1 X Xᴴ 1).PosDef ↔ specNorm X < 1 := by
  rw [posDef_fromBlocks_iff, inv_one, Matrix.mul_one, posDef_one_sub_conjTranspose_mul_self_iff]
  exact and_iff_right Matrix.PosDef.one

/-- For Hermitian $\mathbf{S}$, the real quadratic form of $\mathbf{S}\mathbf{S}$ at
$\mathbf{S}^{+}\mathbf{u}$ is at most $\|\mathbf{u}\|^2$. -/
private theorem re_quadForm_mul_self_pinv_mulVec_le {S : Matrix n n 𝕜} (hS : S.IsHermitian)
    (u : n → 𝕜) :
    RCLike.re (quadForm (S * S) (pinv S *ᵥ u)) ≤ ‖WithLp.toLp 2 u‖ ^ 2 := by
  have e : S * S = Sᴴ * S := by rw [hS.eq]
  rw [e, quadForm_conjTranspose_mul_self, RCLike.ofReal_re, Matrix.mulVec_mulVec, mul_pinv]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((isStarProjection_rangeProjector S).norm_toLp_mulVec_le u) 2

/-- The contraction factor of a positive semidefinite block matrix, for any Hermitian square
roots $\mathbf{S}$, $\mathbf{T}$ of the diagonal blocks:
$\mathbf{X} = \mathbf{S}^{+}\mathbf{B}\mathbf{T}^{+}$. -/
private theorem exists_specNorm_le_one_and_eq_mul_mul {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} {S : Matrix m m 𝕜} {T : Matrix n n 𝕜} (hS : S.IsHermitian)
    (hT : T.IsHermitian) (hA : S * S = A) (hC : T * T = C)
    (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    ∃ X : Matrix m n 𝕜, specNorm X ≤ 1 ∧ B = S * X * T := by
  classical
  subst hA hC
  have h' : (Matrix.fromBlocks (T * T) Bᴴ Bᴴᴴ (S * S)).PosSemidef := by
    have h1 := h.submatrix Sum.swap
    rwa [Matrix.fromBlocks_submatrix_sum_swap_sum_swap,
      ← Matrix.conjTranspose_conjTranspose B, Matrix.conjTranspose_conjTranspose Bᴴ] at h1
  have hB1 : S * pinv S * B = B := mul_pinv_mul_eq_of_range_le
    ((Matrix.PosSemidef.range_le_of_fromBlocks h).trans
      (range_le_iff_exists_mul.mpr ⟨S, rfl⟩))
  have hB2 : B * pinv T * T = B := by
    have h2 : T * pinv T * Bᴴ = Bᴴ := mul_pinv_mul_eq_of_range_le
      ((Matrix.PosSemidef.range_le_of_fromBlocks h').trans
        (range_le_iff_exists_mul.mpr ⟨T, rfl⟩))
    have h3 := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hT.pinv.eq, hT.eq,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at h3
  refine ⟨pinv S * B * pinv T, ?_, ?_⟩
  · refine specNorm_le_of_forall_norm_star_dotProduct_mulVec_le zero_le_one fun u v hu hv => ?_
    have e : star u ⬝ᵥ (pinv S * B * pinv T) *ᵥ v =
        star (pinv S *ᵥ u) ⬝ᵥ B *ᵥ (pinv T *ᵥ v) := by
      rw [Matrix.star_mulVec, hS.pinv.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec]
    have key := Matrix.PosSemidef.norm_star_dotProduct_mulVec_sq_le_of_fromBlocks h (pinv S *ᵥ u)
      (pinv T *ᵥ v)
    have h1 := re_quadForm_mul_self_pinv_mulVec_le hS u
    have h2 := re_quadForm_mul_self_pinv_mulVec_le hT v
    rw [hu, one_pow] at h1
    rw [hv, one_pow] at h2
    have h0 := (posSemidef_fromBlocks_iff_exists.mp h').1.re_quadForm_nonneg (pinv T *ᵥ v)
    rw [e, ← sq_le_one_iff₀ (norm_nonneg _)]
    exact key.trans (mul_le_one₀ h1 h0 h2)
  · calc B = S * pinv S * (B * pinv T * T) := by rw [hB2, hB1]
      _ = S * (pinv S * B * pinv T) * T := by simp only [Matrix.mul_assoc]

private theorem fromBlocks_sqrt_congruence [DecidableEq m] [DecidableEq n]
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜} (hA : A.PosSemidef) (hC : C.PosSemidef)
    (X : Matrix m n 𝕜) :
    let D := Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt C)
    Dᴴ * Matrix.fromBlocks 1 X Xᴴ 1 * D = Matrix.fromBlocks A
      (CFC.sqrt A * X * CFC.sqrt C) (CFC.sqrt A * X * CFC.sqrt C)ᴴ C := by
  have hS := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hT := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian.eq
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hS, hT,
    Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.conjTranspose_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg,
    CFC.sqrt_mul_sqrt_self C hC.nonneg, Matrix.mul_assoc]

open scoped Classical in
/-- **The contraction factor.** For positive semidefinite $\mathbf{A}$ and $\mathbf{C}$, the
block matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{B}^{\mathsf{H}} & \mathbf{C}
\end{bmatrix}$ is positive semidefinite exactly when $\mathbf{B} =
\mathbf{A}^{1/2}\mathbf{X}\mathbf{C}^{1/2}$ for some contraction $\mathbf{X}$, $\|\mathbf{X}\|_2 \le
1$; here $\mathbf{A}^{1/2}$ is the positive semidefinite square root (`CFC.sqrt`).
[HornJohnson2013, Theorem 7.7.9].
Result: block-positivity -/
theorem _root_.Matrix.PosSemidef.posSemidef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt
    {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      ∃ X : Matrix m n 𝕜, specNorm X ≤ 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C := by
  have hS : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hT : (CFC.sqrt C).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hTT : CFC.sqrt C * CFC.sqrt C = C := CFC.sqrt_mul_sqrt_self C hC.nonneg
  refine ⟨exists_specNorm_le_one_and_eq_mul_mul hS hT hSS hTT, ?_⟩
  rintro ⟨X, hX, rfl⟩
  have h := ((posSemidef_fromBlocks_one_iff_specNorm_le_one X).mpr hX).conjTranspose_mul_mul_same
    (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt C))
  rwa [fromBlocks_sqrt_congruence hA hC X] at h

omit [Fintype n] in
/-- For positive definite $\mathbf{A}$ and any $\mathbf{X}$,
$\begin{bmatrix} \mathbf{A} & \mathbf{X} \\ \mathbf{X}^{\mathsf{H}} &
\mathbf{X}^{\mathsf{H}}\mathbf{A}^{-1}\mathbf{X} \end{bmatrix}$ is positive semidefinite. -/
theorem _root_.Matrix.PosDef.posSemidef_fromBlocks_conjTranspose_mul_inv_mul [Finite n]
    [DecidableEq m]
    {A : Matrix m m 𝕜} (hA : A.PosDef) (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks A X Xᴴ (Xᴴ * A⁻¹ * X)).PosSemidef := by
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  refine posSemidef_fromBlocks_iff_exists.mpr
    ⟨hA.posSemidef, A⁻¹ * X, by rw [← Matrix.mul_assoc, hAA, Matrix.one_mul], ?_⟩
  have e : (A⁻¹ * X)ᴴ * A * (A⁻¹ * X) = Xᴴ * A⁻¹ * X := by
    rw [Matrix.conjTranspose_mul, hA.isHermitian.inv.eq, Matrix.mul_assoc, ← Matrix.mul_assoc A,
      hAA, Matrix.one_mul]
  rw [e, sub_self]
  exact Matrix.PosSemidef.zero

/-! ### Strict bilinear tests -/

/-- For positive semidefinite diagonal blocks, positivity is equivalent to bounding twice
the modulus of the cross term by the sum of the diagonal quadratic forms.
[HornJohnson2013, Theorem 7.7.7]. -/
theorem _root_.Matrix.PosSemidef.posSemidef_fromBlocks_iff_forall_two_mul_norm_le
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔ ∀ (x : m → 𝕜) (y : n → 𝕜),
      2 * ‖star x ⬝ᵥ B *ᵥ y‖ ≤ RCLike.re (quadForm A x) + RCLike.re (quadForm C y) := by
  constructor
  · intro h x y
    have hxy := h.norm_star_dotProduct_mulVec_sq_le_of_fromBlocks x y
    apply le_of_sq_le_sq _ (add_nonneg (hA.re_quadForm_nonneg x) (hC.re_quadForm_nonneg y))
    nlinarith [sq_nonneg (RCLike.re (quadForm A x) - RCLike.re (quadForm C y))]
  · intro h
    have hH := hA.isHermitian.fromBlocks (B := B) rfl hC.isHermitian
    refine posSemidef_iff_quadForm_nonneg.mpr ⟨hH, fun z => ?_⟩
    obtain ⟨x, y, rfl⟩ : ∃ x y, z = Sum.elim x y :=
      ⟨z ∘ Sum.inl, z ∘ Sum.inr, (Sum.elim_comp_inl_inr z).symm⟩
    rw [← hH.coe_re_quadForm, RCLike.ofReal_nonneg, re_quadForm_fromBlocks]
    linarith [h x y, (abs_le.mp (RCLike.abs_re_le_norm (star x ⬝ᵥ B *ᵥ y))).1]

/-- The strict block Cauchy–Schwarz bound holds when both test vectors are nonzero.
[HornJohnson2013, Theorem 7.7.7]. -/
theorem _root_.Matrix.PosDef.norm_star_dotProduct_mulVec_sq_lt_of_fromBlocks
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (h : (Matrix.fromBlocks A B Bᴴ C).PosDef) {x : m → 𝕜} {y : n → 𝕜} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 < RCLike.re (quadForm A x) * RCLike.re (quadForm C y) := by
  classical
  obtain ⟨hA, hS⟩ := posDef_fromBlocks_iff.mp h
  have hc := hS.re_quadForm_pos hy
  rw [quadForm_sub_left, map_sub, sub_pos] at hc
  have hG := hA.posSemidef_fromBlocks_conjTranspose_mul_inv_mul B
  exact (hG.norm_star_dotProduct_mulVec_sq_le_of_fromBlocks x y).trans_lt
    (mul_lt_mul_of_pos_left hc (hA.re_quadForm_pos hx))

private theorem forall_two_mul_norm_lt_of_forall_norm_sq_lt
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.PosDef) (hC : C.PosDef)
    (h : ∀ (x : m → 𝕜) (y : n → 𝕜), x ≠ 0 → y ≠ 0 →
      ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 < RCLike.re (quadForm A x) * RCLike.re (quadForm C y)) :
    ∀ (x : m → 𝕜) (y : n → 𝕜), x ≠ 0 ∨ y ≠ 0 →
      2 * ‖star x ⬝ᵥ B *ᵥ y‖ < RCLike.re (quadForm A x) + RCLike.re (quadForm C y) := by
  intro x y hxy
  by_cases hx : x = 0
  · subst x
    simpa [quadForm] using hC.re_quadForm_pos (hxy.resolve_left (by simp))
  by_cases hy : y = 0
  · subst y
    simpa [quadForm] using hA.re_quadForm_pos hx
  have hsq := h x y hx hy
  apply (sq_lt_sq₀ (by positivity) (add_nonneg (hA.re_quadForm_pos hx).le
    (hC.re_quadForm_pos hy).le)).mp
  nlinarith [sq_nonneg (RCLike.re (quadForm A x) - RCLike.re (quadForm C y))]

/-- For positive definite diagonal blocks, strict positivity is equivalent to the strict
additive cross-term bound for every nonzero pair. [HornJohnson2013, Theorem 7.7.7]. -/
theorem _root_.Matrix.PosDef.posDef_fromBlocks_iff_forall_two_mul_norm_lt
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.PosDef) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔ ∀ (x : m → 𝕜) (y : n → 𝕜), x ≠ 0 ∨ y ≠ 0 →
      2 * ‖star x ⬝ᵥ B *ᵥ y‖ < RCLike.re (quadForm A x) + RCLike.re (quadForm C y) := by
  constructor
  · exact fun h => forall_two_mul_norm_lt_of_forall_norm_sq_lt hA hC fun _ _ =>
      h.norm_star_dotProduct_mulVec_sq_lt_of_fromBlocks
  · intro h
    have hH := hA.isHermitian.fromBlocks (B := B) rfl hC.isHermitian
    refine posDef_iff_quadForm_pos.mpr ⟨hH, fun z hz => ?_⟩
    obtain ⟨x, y, rfl⟩ : ∃ x y, z = Sum.elim x y :=
      ⟨z ∘ Sum.inl, z ∘ Sum.inr, (Sum.elim_comp_inl_inr z).symm⟩
    have hxy : x ≠ 0 ∨ y ≠ 0 := by
      by_contra! he
      obtain ⟨rfl, rfl⟩ := he
      exact hz (by ext i; cases i <;> rfl)
    rw [← hH.coe_re_quadForm, RCLike.ofReal_pos, re_quadForm_fromBlocks]
    linarith [h x y hxy, (abs_le.mp (RCLike.abs_re_le_norm (star x ⬝ᵥ B *ᵥ y))).1]

/-- **Strict block positivity.** For positive definite diagonal blocks, strict Cauchy–Schwarz
on nonzero vectors characterises positivity of the full block.
[HornJohnson2013, Theorem 7.7.7].
Result: block-positivity -/
theorem _root_.Matrix.PosDef.posDef_fromBlocks_iff_forall_norm_sq_lt
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.PosDef) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔ ∀ (x : m → 𝕜) (y : n → 𝕜), x ≠ 0 → y ≠ 0 →
      ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 < RCLike.re (quadForm A x) * RCLike.re (quadForm C y) :=
  ⟨fun h _ _ => h.norm_star_dotProduct_mulVec_sq_lt_of_fromBlocks, fun h =>
    (hA.posDef_fromBlocks_iff_forall_two_mul_norm_lt hC).mpr
      (forall_two_mul_norm_lt_of_forall_norm_sq_lt hA hC h)⟩

/-! ### Relative spectral radius and strict contractions -/

private theorem isUnit_fromBlocks_sqrt [DecidableEq m] [DecidableEq n]
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜} (hA : A.PosDef) (hC : C.PosDef) :
    IsUnit (Matrix.fromBlocks (CFC.sqrt A) (0 : Matrix m n 𝕜) 0 (CFC.sqrt C)) :=
  Matrix.isUnit_fromBlocks_zero₂₁.mpr
    ⟨(CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit,
      (CFC.isUnit_sqrt_iff C hC.posSemidef.nonneg).mpr hC.isUnit⟩

open scoped Classical in
private theorem posDef_fromBlocks_sqrt_iff_specNorm_lt
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜} (hA : A.PosDef) (hC : C.PosDef) (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks A (CFC.sqrt A * X * CFC.sqrt C) (CFC.sqrt A * X * CFC.sqrt C)ᴴ C).PosDef ↔
      specNorm X < 1 := by
  rw [← fromBlocks_sqrt_congruence hA.posSemidef hC.posSemidef,
    ← Matrix.star_eq_conjTranspose,
    Matrix.IsUnit.posDef_star_left_conjugate_iff (isUnit_fromBlocks_sqrt hA hC),
    posDef_fromBlocks_one_iff_specNorm_lt_one]

open scoped Classical in
/-- **Strict contraction factorization.** With positive definite diagonal blocks, the full
block is positive definite precisely when the off-diagonal block factors through a strict
contraction between the two positive square roots. [HornJohnson2013, Theorem 7.7.7].
Result: block-positivity -/
theorem _root_.Matrix.PosDef.posDef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (hA : A.PosDef) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔
      ∃ X : Matrix m n 𝕜, specNorm X < 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C := by
  constructor
  · intro h
    obtain ⟨X, -, hB⟩ :=
      (hA.posSemidef.posSemidef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt hC.posSemidef).mp
        h.posSemidef
    exact ⟨X, (posDef_fromBlocks_sqrt_iff_specNorm_lt hA hC X).mp (hB ▸ h), hB⟩
  · rintro ⟨X, hX, rfl⟩
    exact (posDef_fromBlocks_sqrt_iff_specNorm_lt hA hC X).mpr hX

private theorem specRadius_relative_of_sqrt_factor [DecidableEq m] [DecidableEq n]
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜} (hA : A.PosDef) (hC : C.PosDef)
    (X : Matrix m n 𝕜) :
    let B := CFC.sqrt A * X * CFC.sqrt C
    specRadius (Bᴴ * A⁻¹ * B * C⁻¹) = specNorm X ^ 2 := by
  let S := CFC.sqrt A
  let T := CFC.sqrt C
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hT : T.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian
  have hs : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).mp
    ((CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit)
  have ht : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det _).mp
    ((CFC.isUnit_sqrt_iff C hC.posSemidef.nonneg).mpr hC.isUnit)
  have hss : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have htt : T * T = C := CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg
  change specRadius ((S * X * T)ᴴ * A⁻¹ * (S * X * T) * C⁻¹) = _
  have eq : (S * X * T)ᴴ * A⁻¹ * (S * X * T) * C⁻¹ = T * ((Xᴴ * X) * T⁻¹) := by
    rw [← hss, ← htt]
    simp only [Matrix.conjTranspose_mul, hS.eq, hT.eq, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hs, Matrix.nonsing_inv_mul_cancel_left _ _ hs,
      Matrix.mul_nonsing_inv_cancel_left _ _ ht]
  have hn : IsStarNormal (Xᴴ * X) :=
    ⟨by rw [Matrix.star_eq_conjTranspose, (Matrix.isHermitian_conjTranspose_mul_self X).eq]⟩
  rw [eq, specRadius_mul_comm, Matrix.mul_assoc, Matrix.nonsing_inv_mul T ht, Matrix.mul_one,
    ← hn.specNorm_eq_specRadius,
    specNorm_conjTranspose_mul_self]

open scoped Classical in
private theorem exists_sqrt_factor {A : Matrix m m 𝕜}
    {C : Matrix n n 𝕜} (hA : A.PosDef) (hC : C.PosDef) (B : Matrix m n 𝕜) :
    ∃ X : Matrix m n 𝕜, B = CFC.sqrt A * X * CFC.sqrt C := by
  have hs := (Matrix.isUnit_iff_isUnit_det _).mp
    ((CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit)
  have ht := (Matrix.isUnit_iff_isUnit_det _).mp
    ((CFC.isUnit_sqrt_iff C hC.posSemidef.nonneg).mpr hC.isUnit)
  refine ⟨(CFC.sqrt A)⁻¹ * B * (CFC.sqrt C)⁻¹, ?_⟩
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hs]

/-- With positive definite diagonal blocks, the Hermitian block is positive semidefinite
exactly when the relative spectral radius is at most one. [HornJohnson2013, §7.7]. -/
theorem _root_.Matrix.PosDef.posSemidef_fromBlocks_iff_specRadius_le_one [DecidableEq m]
    [DecidableEq n] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.PosDef) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔ specRadius (Bᴴ * A⁻¹ * B * C⁻¹) ≤ 1 := by
  obtain ⟨X, rfl⟩ := exists_sqrt_factor hA hC B
  rw [specRadius_relative_of_sqrt_factor hA hC X, sq_le_one_iff₀ (specNorm_nonneg X),
    ← fromBlocks_sqrt_congruence hA.posSemidef hC.posSemidef, ← Matrix.star_eq_conjTranspose,
    Matrix.IsUnit.posSemidef_star_left_conjugate_iff (isUnit_fromBlocks_sqrt hA hC),
    posSemidef_fromBlocks_one_iff_specNorm_le_one]

/-- With positive definite diagonal blocks, the Hermitian block is positive definite
exactly when the relative spectral radius is strictly below one. [HornJohnson2013, §7.7]. -/
theorem _root_.Matrix.PosDef.posDef_fromBlocks_iff_specRadius_lt_one [DecidableEq m]
    [DecidableEq n] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.PosDef) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔ specRadius (Bᴴ * A⁻¹ * B * C⁻¹) < 1 := by
  obtain ⟨X, rfl⟩ := exists_sqrt_factor hA hC B
  rw [specRadius_relative_of_sqrt_factor hA hC X, sq_lt_one_iff₀ (specNorm_nonneg X),
    posDef_fromBlocks_sqrt_iff_specNorm_lt hA hC]

/-! ### Equal diagonal blocks -/

omit [Fintype n] in
/-- **Equal diagonal blocks.** $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{B} & \mathbf{A}
\end{bmatrix}$ is positive semidefinite exactly when
$-\mathbf{A} \preceq \mathbf{B} \preceq \mathbf{A}$.
[HornJohnson2013, §7.7]. -/
theorem posSemidef_fromBlocks_self_iff [Finite n] {A B : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B B A).PosSemidef ↔ -A ≤ B ∧ B ≤ A := by
  classical
  have := Fintype.ofFinite n
  rw [Matrix.le_iff, Matrix.le_iff, sub_neg_eq_add]
  constructor
  · intro h
    have h1 := (h.conjTranspose_mul_mul_same (Matrix.fromRows (1 : Matrix n n 𝕜) 1)).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h2 := (h.conjTranspose_mul_mul_same (Matrix.fromRows (1 : Matrix n n 𝕜) (-1))).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows] at h1 h2
    constructor
    · convert h1 using 1
      simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      module
    · convert h2 using 1
      simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_neg, Matrix.one_mul,
        Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
      module
  · rintro ⟨h1, h2⟩
    have hd : (Matrix.fromBlocks (B + A) 0 (0 : Matrix n n 𝕜)ᴴ (A - B)).PosSemidef :=
      posSemidef_fromBlocks_iff_exists.mpr ⟨h1, 0, by simp, by simpa using h2⟩
    have h := (hd.conjTranspose_mul_mul_same
      (Matrix.fromBlocks 1 1 1 (-1) : Matrix (n ⊕ n) (n ⊕ n) 𝕜)).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_one, Matrix.conjTranspose_neg, Matrix.conjTranspose_zero,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_zero,
      add_zero, zero_add, Matrix.fromBlocks_smul]
    congr 1 <;> module

/-- For Hermitian $\mathbf{A}$ and $\mathbf{B}$, the bound
$-\mathbf{A} \preceq \mathbf{B} \preceq \mathbf{A}$ is the quadratic-form bound
$\lvert \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{B}\mathbf{x}) \rvert
\le \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$ for all $\mathbf{x}$. -/
theorem _root_.Matrix.IsHermitian.neg_le_and_le_iff_forall_abs_re_quadForm_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    -A ≤ B ∧ B ≤ A ↔ ∀ x : n → 𝕜, |RCLike.re (quadForm B x)| ≤ RCLike.re (quadForm A x) := by
  rw [hA.neg.le_iff_re_quadForm_le hB, hB.le_iff_re_quadForm_le hA, ← forall_and]
  simp only [quadForm_neg_left, map_neg, abs_le]

/-- If $\begin{bmatrix}\mathbf{S} & \mathbf{B} \\ \mathbf{B}^{\mathsf H} & \mathbf{S}\end{bmatrix}$
is positive semidefinite, then $\|\mathbf{B}\|_2 \le \|\mathbf{S}\|_2$.
[Bhatia1997, §IX.1]. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_specNorm_of_fromBlocks {S B : Matrix m m 𝕜}
    (h : (Matrix.fromBlocks S B Bᴴ S).PosSemidef) : specNorm B ≤ specNorm S := by
  classical
  have hS : S.PosSemidef := h.submatrix (Sum.inl : m → m ⊕ m)
  obtain ⟨K, hK, rfl⟩ := (hS.posSemidef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt hS).mp h
  have hnorm := specNorm_conjTranspose_mul_self (CFC.sqrt S)
  have hs : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  rw [hs.eq, CFC.sqrt_mul_sqrt_self _ hS.nonneg] at hnorm
  calc
    _ ≤ (specNorm (CFC.sqrt S) * specNorm K) * specNorm (CFC.sqrt S) :=
      (specNorm_mul_le _ _).trans (by gcongr; exact specNorm_mul_le _ _)
    _ ≤ (specNorm (CFC.sqrt S) * 1) * specNorm (CFC.sqrt S) := by gcongr
    _ = _ := by rw [mul_one, ← sq, ← hnorm]

end NLAlib
