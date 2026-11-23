/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.EigenvectorConditioning
public import NLAlib.Matrix.Perturbation.EigenvalueMatching
public import NLAlib.Matrix.FinitePrecision.Deflation

/-!
# Approximate eigendecompositions from an approximate Schur form

From an approximate Schur form $\mathbf{X} \approx \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}$
($\mathbf{U}$ near orthonormal, $\mathbf{T}$ upper triangular) and approximate eigenvectors
$\mathbf{Y}$ of $\mathbf{T}$, the matrix $\mathbf{V} \approx \mathbf{U}\mathbf{Y}$ is an approximate
eigenvector matrix of $\mathbf{X}$ with the eigenvalues $t_{jj}$: each column residual is at most
the Schur error, the orthogonality error and the triangular residual, with no gap of
$\mathbf{T}$. When $\mathbf{X}$ is a scaled matrix of the class $(B, \Gamma)$ near $\mathbf{A}$,
$\mathbf{V}$ is also well conditioned
(`NLAlib.IsConditionedDiagonalizable.pseudoConditionNumber_le_of_residual`),
$\mathbf{V}\operatorname{diag}(t_{jj})\mathbf{V}^{-1}$ is near $\mathbf{A}$, and the diagonal of
$\mathbf{T}$ is separated. All of this is program-free.

## Main definitions

* `NLAlib.EigResidualOf`, `NLAlib.EigDecompOf`: the residual part and the whole of an approximate
  eigendecomposition.
* `NLAlib.eigEta`, `NLAlib.eigColTol`: the column residual budget and the column-norm tolerance.

## Main results

* `NLAlib.norm_mulVec_sub_smul_le_of_schur`, `NLAlib.specNorm_mul_sub_mul_diagonal_le_of_schur`:
  the column and matrix residual from a Schur form.
* `NLAlib.sqrt_one_sub_mul_norm_le_norm_mulVec`: a near-orthonormal matrix is bounded below.
* `NLAlib.specNorm_mul_diagonal_mul_inv_sub_le`: the backward form from the residual.
* `NLAlib.one_sub_mul_specNorm_le_specNorm_mul_mul_conjTranspose`: the triangular factor of a
  near-orthonormal similarity is bounded.
* `NLAlib.exists_hasOrthonormalCols_add_eq_mul_mul_conjTranspose_of_le`: an approximate Schur
  form is an exact Schur form of a nearby matrix.
* `NLAlib.specNorm_mul_sub_mul_diagonal_le_of_forall_col`: the matrix residual from the column
  residuals.
* `NLAlib.eigDecompOf_of_schur`: an eigendecomposition from a Schur form of a regularized matrix.
* `NLAlib.eigResidualOf_of_schur`: the residual part from a Schur form of the matrix itself.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The column residual from a Schur form**: for any $\mathbf{Z}$, $\mathbf{U}$, $\mathbf{T}$,
vectors $\mathbf{y}$, $\mathbf{v}$ and $\mu \in \mathbb{C}$,
$$\|(\mathbf{Z} - \mu\mathbf{I})\mathbf{v}\| \le (\|\mathbf{Z} - \mathbf{U}\mathbf{T}
  \mathbf{U}^{\mathsf H}\|_2\|\mathbf{U}\|_2 + \|\mathbf{U}\|_2\|\mathbf{T}\|_2
  \|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2)\|\mathbf{y}\| +
  \|\mathbf{U}\|_2\|(\mathbf{T} - \mu\mathbf{I})\mathbf{y}\| +
  (\|\mathbf{Z}\|_2 + \lvert\mu\rvert)\|\mathbf{v} - \mathbf{U}\mathbf{y}\|\,.$$ -/
theorem norm_mulVec_sub_smul_le_of_schur (Z U T : Matrix n n ℂ) (y v : n → ℂ) (μ : ℂ) :
    ‖WithLp.toLp 2 ((Z - μ • 1) *ᵥ v)‖ ≤
      (specNorm (Z - U * T * Uᴴ) * specNorm U +
          specNorm U * specNorm T * specNorm (Uᴴ * U - 1)) * ‖WithLp.toLp 2 y‖ +
        specNorm U * ‖WithLp.toLp 2 ((T - μ • 1) *ᵥ y)‖ +
        (specNorm Z + ‖μ‖) * ‖WithLp.toLp 2 (v - U *ᵥ y)‖ := by
  have key : (Z - μ • 1) *ᵥ v = (Z - U * T * Uᴴ) *ᵥ (U *ᵥ y) + (U * T) *ᵥ ((Uᴴ * U - 1) *ᵥ y) +
      U *ᵥ ((T - μ • 1) *ᵥ y) + (Z - μ • 1) *ᵥ (v - U *ᵥ y) := by
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul]
    abel
  have hZμ : specNorm (Z - μ • 1) ≤ specNorm Z + ‖μ‖ := by
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_smul]
    gcongr
    exact (mul_le_of_le_one_right (norm_nonneg _) specNorm_one_le)
  have h1 : ‖WithLp.toLp 2 ((Z - U * T * Uᴴ) *ᵥ (U *ᵥ y))‖ ≤
      specNorm (Z - U * T * Uᴴ) * specNorm U * ‖WithLp.toLp 2 y‖ := by
    refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [mul_assoc (specNorm (Z - U * T * Uᴴ))]
    exact mul_le_mul_of_nonneg_left (norm_toLp_mulVec_le _ _) (specNorm_nonneg _)
  have h2 : ‖WithLp.toLp 2 ((U * T) *ᵥ ((Uᴴ * U - 1) *ᵥ y))‖ ≤
      specNorm U * specNorm T * specNorm (Uᴴ * U - 1) * ‖WithLp.toLp 2 y‖ := by
    refine (norm_toLp_mulVec_le _ _).trans ?_
    calc specNorm (U * T) * ‖WithLp.toLp 2 ((Uᴴ * U - 1) *ᵥ y)‖
        ≤ (specNorm U * specNorm T) * (specNorm (Uᴴ * U - 1) * ‖WithLp.toLp 2 y‖) :=
          mul_le_mul (specNorm_mul_le _ _) (norm_toLp_mulVec_le _ _) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have h3 := norm_toLp_mulVec_le U ((T - μ • 1) *ᵥ y)
  have h4 : ‖WithLp.toLp 2 ((Z - μ • 1) *ᵥ (v - U *ᵥ y))‖ ≤
      (specNorm Z + ‖μ‖) * ‖WithLp.toLp 2 (v - U *ᵥ y)‖ :=
    (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hZμ (norm_nonneg _))
  rw [key, WithLp.toLp_add, WithLp.toLp_add, WithLp.toLp_add]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)) h4) |>.trans (le_of_eq ?_)
  ring

/-- **The matrix residual from a Schur form**: for any $\mathbf{Z}$, $\mathbf{U}$, $\mathbf{T}$,
$\mathbf{Y}$, $\mathbf{V}$ and $\mathbf{D} = \operatorname{diag}(\mathbf{d})$,
$$\|\mathbf{Z}\mathbf{V} - \mathbf{V}\mathbf{D}\|_2 \le (\|\mathbf{Z} - \mathbf{U}\mathbf{T}
  \mathbf{U}^{\mathsf H}\|_2\|\mathbf{U}\|_2 + \|\mathbf{U}\|_2\|\mathbf{T}\|_2
  \|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2)\|\mathbf{Y}\|_2 +
  \|\mathbf{U}\|_2\|\mathbf{T}\mathbf{Y} - \mathbf{Y}\mathbf{D}\|_2 +
  (\|\mathbf{Z}\|_2 + \|\mathbf{D}\|_2)\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|_2\,.$$ -/
theorem specNorm_mul_sub_mul_diagonal_le_of_schur (Z U T Y V : Matrix n n ℂ) (d : n → ℂ) :
    specNorm (Z * V - V * Matrix.diagonal d) ≤
      (specNorm (Z - U * T * Uᴴ) * specNorm U +
          specNorm U * specNorm T * specNorm (Uᴴ * U - 1)) * specNorm Y +
        specNorm U * specNorm (T * Y - Y * Matrix.diagonal d) +
        (specNorm Z + specNorm (Matrix.diagonal d)) * specNorm (V - U * Y) := by
  have key : Z * V - V * Matrix.diagonal d = (Z - U * T * Uᴴ) * (U * Y) +
      (U * T) * ((Uᴴ * U - 1) * Y) + U * (T * Y - Y * Matrix.diagonal d) + Z * (V - U * Y) -
      (V - U * Y) * Matrix.diagonal d := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul]
    abel
  have h1 : specNorm ((Z - U * T * Uᴴ) * (U * Y)) ≤
      specNorm (Z - U * T * Uᴴ) * specNorm U * specNorm Y := by
    refine (specNorm_mul_le _ _).trans ?_
    rw [mul_assoc (specNorm (Z - U * T * Uᴴ))]
    exact mul_le_mul_of_nonneg_left (specNorm_mul_le U Y) (specNorm_nonneg _)
  have h2 : specNorm ((U * T) * ((Uᴴ * U - 1) * Y)) ≤
      specNorm U * specNorm T * specNorm (Uᴴ * U - 1) * specNorm Y := by
    refine (specNorm_mul_le _ _).trans ?_
    calc specNorm (U * T) * specNorm ((Uᴴ * U - 1) * Y)
        ≤ (specNorm U * specNorm T) * (specNorm (Uᴴ * U - 1) * specNorm Y) :=
          mul_le_mul (specNorm_mul_le _ _) (specNorm_mul_le _ _) (specNorm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have h3 := specNorm_mul_le U (T * Y - Y * Matrix.diagonal d)
  have h4 := specNorm_mul_le Z (V - U * Y)
  have h5 := specNorm_mul_le (V - U * Y) (Matrix.diagonal d)
  rw [key]
  refine (specNorm_sub_le _ _).trans ?_
  refine (add_le_add ((specNorm_add_le _ _).trans (add_le_add ((specNorm_add_le _ _).trans
    (add_le_add ((specNorm_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)) h5).trans
    (le_of_eq ?_)
  ring

/-- **A near-orthonormal matrix is bounded below**: if
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e \le 1$, then
$\|\mathbf{U}\mathbf{x}\| \ge \sqrt{1 - e}\,\|\mathbf{x}\|$ for every $\mathbf{x}$. -/
theorem sqrt_one_sub_mul_norm_le_norm_mulVec {m : Type*} [Fintype m] {U : Matrix m n ℂ} {e : ℝ}
    (hU : specNorm (Uᴴ * U - 1) ≤ e) (he : e ≤ 1) (x : n → ℂ) :
    √(1 - e) * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (U *ᵥ x)‖ := by
  have he0 : 0 ≤ 1 - e := by linarith
  have hsq : (1 - e) * ‖WithLp.toLp 2 x‖ ^ 2 ≤ ‖WithLp.toLp 2 (U *ᵥ x)‖ ^ 2 := by
    have hid : star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x + star x ⬝ᵥ ((Uᴴ * U - 1) *ᵥ x) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← dotProduct_add, Matrix.sub_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_mulVec, add_sub_cancel]
    rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct,
      EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct, hid, map_add,
      ← EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct]
    have h1 := norm_star_dotProduct_mulVec_le (Uᴴ * U - 1) x x
    have h2 := (abs_le.mp (RCLike.abs_re_le_norm (star x ⬝ᵥ ((Uᴴ * U - 1) *ᵥ x)))).1
    nlinarith [mul_le_mul_of_nonneg_right hU (sq_nonneg ‖WithLp.toLp 2 x‖)]
  refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 ?_
  rw [mul_pow, Real.sq_sqrt he0]
  exact hsq

/-- **The backward form of an eigendecomposition**: for an invertible $\mathbf{V}$, any
$\mathbf{Z}$ and $\mathbf{D} = \operatorname{diag}(\mathbf{d})$,
$\|\mathbf{V}\mathbf{D}\mathbf{V}^{-1} - \mathbf{Z}\|_2 \le
\|\mathbf{Z}\mathbf{V} - \mathbf{V}\mathbf{D}\|_2\|\mathbf{V}^{-1}\|_2$. -/
theorem specNorm_mul_diagonal_mul_inv_sub_le {Z V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V) :
    specNorm (V * Matrix.diagonal d * V⁻¹ - Z) ≤
      specNorm (Z * V - V * Matrix.diagonal d) * specNorm V⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have h : V * Matrix.diagonal d * V⁻¹ - Z = (V * Matrix.diagonal d - Z * V) * V⁻¹ := by
    rw [Matrix.sub_mul, Matrix.mul_assoc Z, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [h, specNorm_sub_comm]
  exact specNorm_mul_le _ _

/-- A near-orthonormal matrix is bounded above: if
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e$, then
$\|\mathbf{U}\|_2 \le \sqrt{1 + e}$. -/
theorem specNorm_le_sqrt_one_add_of_conjTranspose_mul_self_sub_one_le {m : Type*} [Fintype m]
    {U : Matrix m n ℂ} {e : ℝ} (hU : specNorm (Uᴴ * U - 1) ≤ e) : specNorm U ≤ √(1 + e) := by
  refine Real.le_sqrt_of_sq_le ?_
  rw [← specNorm_conjTranspose_mul_self]
  have h := specNorm_add_le (Uᴴ * U - 1) 1
  rw [sub_add_cancel] at h
  linarith [specNorm_one_le (n := n) (𝕜 := ℂ)]

/-- A near-orthonormal square matrix is invertible: if
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e < 1$, then $\mathbf{U}$ is invertible
and $\sqrt{1 - e}\,\|\mathbf{U}^{-1}\|_2 \le 1$. -/
theorem isUnit_and_sqrt_one_sub_mul_specNorm_inv_le {U : Matrix n n ℂ} {e : ℝ}
    (hU : specNorm (Uᴴ * U - 1) ≤ e) (he : e < 1) :
    IsUnit U ∧ √(1 - e) * specNorm U⁻¹ ≤ 1 := by
  have hc : 0 < √(1 - e) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨hu, hinv⟩ := isUnit_and_specNorm_inv_le_of_mul_norm_le hc
    (sqrt_one_sub_mul_norm_le_norm_mulVec hU he.le)
  refine ⟨hu, ?_⟩
  calc √(1 - e) * specNorm U⁻¹ ≤ √(1 - e) * (√(1 - e))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hc.ne'

/-- The triangular factor of a near-orthonormal similarity is bounded: if
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e < 1$, then
$(1 - e)\|\mathbf{T}\|_2 \le \|\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2$. -/
theorem one_sub_mul_specNorm_le_specNorm_mul_mul_conjTranspose {U : Matrix n n ℂ} {e : ℝ}
    (hU : specNorm (Uᴴ * U - 1) ≤ e) (he : e < 1) (T : Matrix n n ℂ) :
    (1 - e) * specNorm T ≤ specNorm (U * T * Uᴴ) := by
  obtain ⟨hu, hinv⟩ := isUnit_and_sqrt_one_sub_mul_specNorm_inv_le hU he
  have hdet := (Matrix.isUnit_iff_isUnit_det U).mp hu
  have hT : T = U⁻¹ * (U * T * Uᴴ) * Uᴴ⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      (by rw [Matrix.det_conjTranspose]; exact hdet.star), Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hn : specNorm Uᴴ⁻¹ = specNorm U⁻¹ := by
    rw [← Matrix.conjTranspose_nonsing_inv, specNorm_conjTranspose]
  have hs : √(1 - e) ^ 2 = 1 - e := Real.sq_sqrt (by linarith)
  have h1 : specNorm T ≤ specNorm U⁻¹ * specNorm (U * T * Uᴴ) * specNorm U⁻¹ := by
    conv_lhs => rw [hT]
    refine (specNorm_mul_le _ _).trans ?_
    rw [hn]
    exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
  have h0 := specNorm_nonneg (U * T * Uᴴ)
  have hi0 := specNorm_nonneg U⁻¹
  have hr0 := Real.sqrt_nonneg (1 - e)
  calc (1 - e) * specNorm T
      ≤ (1 - e) * (specNorm U⁻¹ * specNorm (U * T * Uᴴ) * specNorm U⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (√(1 - e) * specNorm U⁻¹) * (√(1 - e) * specNorm U⁻¹) * specNorm (U * T * Uᴴ) := by
        linear_combination (-(specNorm U⁻¹ * specNorm (U * T * Uᴴ) * specNorm U⁻¹)) * hs
    _ ≤ 1 * 1 * specNorm (U * T * Uᴴ) := by gcongr
    _ = _ := by ring

/-- **An approximate Schur form is an exact Schur form of a nearby matrix**: if
$\|\mathbf{Z} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2 \le \delta$ and
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e \le 1/8$, there are a unitary
$\mathbf{W}$ and $\mathbf{E}$ with $\mathbf{Z} + \mathbf{E} = \mathbf{W}\mathbf{T}
\mathbf{W}^{\mathsf H}$ and $\|\mathbf{E}\|_2 \le \delta + 4e(\|\mathbf{Z}\|_2 + \delta)$
($\mathbf{W}$ the polar factor of $\mathbf{U}$). No printed source. -/
theorem exists_hasOrthonormalCols_add_eq_mul_mul_conjTranspose_of_le {Z U T : Matrix n n ℂ}
    {δ e : ℝ} (hZ : specNorm (Z - U * T * Uᴴ) ≤ δ) (hU : specNorm (Uᴴ * U - 1) ≤ e)
    (he : e ≤ 1 / 8) :
    ∃ W E : Matrix n n ℂ, HasOrthonormalCols W ∧
      specNorm E ≤ δ + 4 * e * (specNorm Z + δ) ∧ Z + E = W * T * Wᴴ := by
  have he0 : 0 ≤ e := (specNorm_nonneg _).trans hU
  obtain ⟨W, hW, hWU⟩ :=
    exists_hasOrthonormalCols_specNorm_sub_le_of_specNorm_conjTranspose_mul_self_sub_one_le
      he0 (by linarith) hU
  have hη : specNorm (U - W) ≤ e := by rwa [specNorm_sub_comm]
  have hη0 := specNorm_nonneg (U - W)
  have ht0 := specNorm_nonneg T
  have hD : specNorm (W * T * Wᴴ - U * T * Uᴴ) ≤
      (2 * specNorm (U - W) + specNorm (U - W) ^ 2) * specNorm T := by
    have e' : W * T * Wᴴ - U * T * Uᴴ = -((U - W) * T * Uᴴ + W * T * (U - W)ᴴ) := by
      simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
      abel
    have hUn : specNorm U ≤ 1 + specNorm (U - W) := by
      have := specNorm_add_le W (U - W)
      rw [add_sub_cancel] at this
      linarith [hW.specNorm_le_one]
    have h₁ : specNorm ((U - W) * T * Uᴴ) ≤ specNorm (U - W) * specNorm T *
        (1 + specNorm (U - W)) := by
      refine (specNorm_mul_le _ _).trans (mul_le_mul (specNorm_mul_le _ _) ?_
        (specNorm_nonneg _) (mul_nonneg hη0 ht0))
      rwa [specNorm_conjTranspose]
    have h₂ : specNorm (W * T * (U - W)ᴴ) ≤ specNorm T * specNorm (U - W) := by
      rw [Matrix.mul_assoc, hW.specNorm_mul_left]
      refine (specNorm_mul_le _ _).trans (le_of_eq ?_)
      rw [specNorm_conjTranspose]
    rw [e', specNorm_neg]
    refine (specNorm_add_le _ _).trans ?_
    nlinarith
  have hT : (1 - e) * specNorm T ≤ specNorm Z + δ := by
    refine (one_sub_mul_specNorm_le_specNorm_mul_mul_conjTranspose hU (by linarith) T).trans ?_
    have := specNorm_add_le Z (U * T * Uᴴ - Z)
    rw [add_sub_cancel, specNorm_sub_comm] at this
    linarith
  refine ⟨W, W * T * Wᴴ - Z, hW, ?_, by abel⟩
  have hsplit : W * T * Wᴴ - Z = (W * T * Wᴴ - U * T * Uᴴ) + (U * T * Uᴴ - Z) := by abel
  rw [hsplit]
  refine (specNorm_add_le _ _).trans ?_
  rw [specNorm_sub_comm (U * T * Uᴴ)]
  have hk : (2 * specNorm (U - W) + specNorm (U - W) ^ 2) * specNorm T ≤
      4 * e * (specNorm Z + δ) := by
    have h1 : 2 * specNorm (U - W) + specNorm (U - W) ^ 2 ≤ 2 * e + e ^ 2 := by nlinarith
    have h2 : (2 * e + e ^ 2) ≤ 4 * e * (1 - e) := by nlinarith
    calc (2 * specNorm (U - W) + specNorm (U - W) ^ 2) * specNorm T
        ≤ 4 * e * ((1 - e) * specNorm T) := by nlinarith [mul_le_mul_of_nonneg_right h1 ht0]
      _ ≤ _ := by gcongr
  linarith

/-- The matrix residual from the column residuals: if
$\|(\mathbf{Z} - d_j\mathbf{I})\mathbf{v}_j\| \le k\|\mathbf{v}_j\|$ for every column, then
$\|\mathbf{Z}\mathbf{V} - \mathbf{V}\operatorname{diag}(\mathbf{d})\|_2 \le \sqrt N k
\|\mathbf{V}\|_2$, $N$ the order. -/
theorem specNorm_mul_sub_mul_diagonal_le_of_forall_col {Z V : Matrix n n ℂ} {d : n → ℂ} {k : ℝ}
    (hk : 0 ≤ k)
    (h : ∀ j, ‖WithLp.toLp 2 ((Z - d j • 1) *ᵥ V.col j)‖ ≤ k * ‖WithLp.toLp 2 (V.col j)‖) :
    specNorm (Z * V - V * Matrix.diagonal d) ≤ √(Fintype.card n : ℝ) * k * specNorm V := by
  have hcol (j : n) : (Z * V - V * Matrix.diagonal d).col j = (Z - d j • 1) *ᵥ V.col j := by
    funext i
    simp only [Matrix.col_apply, Matrix.sub_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hF : frobNorm (Z * V - V * Matrix.diagonal d) ≤ k * frobNorm V := by
    refine (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow, frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcol, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h j) 2
  calc specNorm (Z * V - V * Matrix.diagonal d) ≤ k * frobNorm V :=
        (specNorm_le_frobNorm _).trans hF
    _ ≤ k * (√(Fintype.card n : ℝ) * specNorm V) := by
        gcongr; exact frobNorm_le_sqrt_card_mul_specNorm V
    _ = _ := by ring

end General

/-! ### Approximate eigendecompositions -/

/-- **The residual part of an approximate eigendecomposition** of $\mathbf{A}$ by the columns of
`V` and the diagonal of `T`: column norms within `c` of $1$, column residuals
$\|(\mathbf{A} - t_{jj}\mathbf{I})\mathbf{v}_j\| \le e_C\|\mathbf{A}\|_2\|\mathbf{v}_j\|$ and the
matrix residual $\|\mathbf{A}\mathbf{V} - \mathbf{V}\mathbf{D}\|_2 \le
e_M\|\mathbf{A}\|_2\|\mathbf{V}\|_2$, $\mathbf{D} = \operatorname{diag}(t_{jj})$. -/
def EigResidualOf {n : ℕ} (A T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (eC eM c : ℝ) : Prop :=
  (∀ j, |‖WithLp.toLp 2 (V.col j)‖ - 1| ≤ c) ∧
  (∀ j, ‖WithLp.toLp 2 ((A - T j j • 1) *ᵥ V.col j)‖ ≤
    eC * specNorm A * ‖WithLp.toLp 2 (V.col j)‖) ∧
  specNorm (A * V - V * Matrix.diagonal (fun i => T i i)) ≤ eM * specNorm A * specNorm V

/-- **An approximate eigendecomposition** of $\mathbf{A}$: the residual part
(`NLAlib.EigResidualOf`), `V` invertible with $\kappa(\mathbf{V}) \le K$, the backward form
$\|\mathbf{V}\mathbf{D}\mathbf{V}^{-1} - \mathbf{A}\|_2 \le e_E\|\mathbf{A}\|_2$ and the gaps
$\lvert t_{ii} - t_{jj}\rvert \ge g\|\mathbf{A}\|_2$ for $i \ne j$. -/
def EigDecompOf {n : ℕ} (A T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c eE K g : ℝ) : Prop :=
  EigResidualOf A T V eC eM c ∧ IsUnit V ∧ pseudoConditionNumber V ≤ K ∧
    specNorm (V * Matrix.diagonal (fun i => T i i) * V⁻¹ - A) ≤ eE * specNorm A ∧
    ∀ i j, i ≠ j → g * specNorm A ≤ ‖T i i - T j j‖

/-- **The column residual budget** $\eta = 2e + 3e_U + 4\sqrt{n + 1}\,c_R + 8(n + 1)c_V$: the
residual of a column of $\mathbf{V}$ in units of $\|\mathbf{A}\|_2\|\mathbf{v}_j\|$, for a Schur
error $e$ and an orthogonality error $e_U$, triangular residuals $c_R$ and a product error $c_V$. -/
noncomputable def eigEta (n : ℕ) (e eU cR cV : ℝ) : ℝ :=
  2 * e + 3 * eU + 4 * √((n : ℝ) + 1) * cR + 8 * ((n : ℝ) + 1) * cV

/-- **The column-norm tolerance** $c_N + 2e_U + 2(n + 1)c_V$ of $\mathbf{V}$. -/
noncomputable def eigColTol (n : ℕ) (eU cV cN : ℝ) : ℝ := cN + 2 * eU + 2 * ((n : ℝ) + 1) * cV

/-- The order as a real number: $\lvert\mathrm{Fin}(n + 1)\rvert = n + 1$. -/
private theorem card_fin_succ_cast (n : ℕ) : ((Fintype.card (Fin (n + 1)) : ℕ) : ℝ) = n + 1 := by
  simp

/-- The columns of $\mathbf{V} \approx \mathbf{U}\mathbf{Y}$: $\|\mathbf{U}\|_2 \le 17/16$,
$\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|_2 \le \tfrac{153}{128}(n + 1)c_V$, and every column of
$\mathbf{V}$ has norm within $c$ of $1$, at least $7/8$, while $\|\mathbf{y}_j\| \le 9/8$. -/
private theorem eig_col_facts {n : ℕ} {U Y V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {eU cV cN : ℝ} (hU : specNorm (Uᴴ * U - 1) ≤ eU)
    (hYn : ∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ cN)
    (hV : specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y) (hcV : 0 ≤ cV)
    (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8) :
    specNorm U ≤ 17 / 16 ∧ specNorm (V - U * Y) ≤ 153 / 128 * ((n : ℝ) + 1) * cV ∧
      ∀ j, |‖WithLp.toLp 2 (V.col j)‖ - 1| ≤ eigColTol n eU cV cN ∧
        ‖WithLp.toLp 2 (Y.col j)‖ ≤ 9 / 8 ∧ 7 / 8 ≤ ‖WithLp.toLp 2 (V.col j)‖ ∧
        ‖WithLp.toLp 2 (V.col j - U *ᵥ Y.col j)‖ ≤ specNorm (V - U * Y) := by
  have heU0 : 0 ≤ eU := (specNorm_nonneg _).trans hU
  have hcN0 : 0 ≤ cN := (abs_nonneg _).trans (hYn 0)
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  unfold eigColTol at hc ⊢
  have hNc : 0 ≤ ((n : ℝ) + 1) * cV := by positivity
  have hcN : cN ≤ 1 / 8 := by linarith
  have hu : specNorm U ≤ 1 + eU / 2 :=
    (specNorm_le_sqrt_one_add_of_conjTranspose_mul_self_sub_one_le hU).trans
      (Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩)
  have hy (j : Fin (n + 1)) : ‖WithLp.toLp 2 (Y.col j)‖ ≤ 1 + cN := by
    linarith [(abs_le.mp (hYn j)).2]
  have hsN : √((n : ℝ) + 1) * √((n : ℝ) + 1) = (n : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have hFU : frobNorm U ≤ √((n : ℝ) + 1) * specNorm U := by
    have := frobNorm_le_sqrt_card_mul_specNorm U
    rwa [card_fin_succ_cast] at this
  have hFY : frobNorm Y ≤ √((n : ℝ) + 1) * (1 + cN) := by
    have := frobNorm_le_sqrt_card_mul_of_forall_norm_toLp_col_le hy
    rwa [card_fin_succ_cast] at this
  have hw : specNorm (V - U * Y) ≤ 153 / 128 * ((n : ℝ) + 1) * cV := by
    refine hV.trans ?_
    calc cV * frobNorm U * frobNorm Y
        ≤ cV * (√((n : ℝ) + 1) * (17 / 16)) * (√((n : ℝ) + 1) * (9 / 8)) := by
          gcongr
          · exact hFU.trans (by gcongr; linarith)
          · exact hFY.trans (by gcongr; linarith)
      _ = 153 / 128 * (√((n : ℝ) + 1) * √((n : ℝ) + 1)) * cV := by ring
      _ = _ := by rw [hsN]
  refine ⟨hu.trans (by linarith), hw, fun j => ?_⟩
  have hcolj : V.col j - U *ᵥ Y.col j = (V - U * Y).col j := by
    funext i
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
  have hd : ‖WithLp.toLp 2 (V.col j - U *ᵥ Y.col j)‖ ≤ specNorm (V - U * Y) := by
    rw [hcolj]; exact norm_toLp_col_le_specNorm _ j
  have hup : ‖WithLp.toLp 2 (U *ᵥ Y.col j)‖ ≤ (1 + eU / 2) * (1 + cN) :=
    (norm_toLp_mulVec_le _ _).trans (mul_le_mul hu (hy j) (norm_nonneg _) (by positivity))
  have hlo : (1 - eU) * (1 - cN) ≤ ‖WithLp.toLp 2 (U *ᵥ Y.col j)‖ := by
    refine le_trans ?_ (sqrt_one_sub_mul_norm_le_norm_mulVec hU (by linarith) (Y.col j))
    have h1 : 1 - eU ≤ √(1 - eU) := Real.le_sqrt_of_sq_le (by nlinarith)
    have h2 : 1 - cN ≤ ‖WithLp.toLp 2 (Y.col j)‖ := by linarith [(abs_le.mp (hYn j)).1]
    exact mul_le_mul h1 h2 (by linarith) (Real.sqrt_nonneg _)
  have hv1 : ‖WithLp.toLp 2 (V.col j)‖ ≤ ‖WithLp.toLp 2 (U *ᵥ Y.col j)‖ +
      ‖WithLp.toLp 2 (V.col j - U *ᵥ Y.col j)‖ := by
    have := EuclideanSpace.norm_toLp_add_le (U *ᵥ Y.col j) (V.col j - U *ᵥ Y.col j)
    rwa [add_sub_cancel] at this
  have hv2 : ‖WithLp.toLp 2 (U *ᵥ Y.col j)‖ ≤ ‖WithLp.toLp 2 (V.col j)‖ +
      ‖WithLp.toLp 2 (V.col j - U *ᵥ Y.col j)‖ := by
    have := EuclideanSpace.norm_toLp_sub_le (V.col j) (V.col j - U *ᵥ Y.col j)
    rwa [sub_sub_cancel] at this
  have habs : |‖WithLp.toLp 2 (V.col j)‖ - 1| ≤ cN + 2 * eU + 2 * ((n : ℝ) + 1) * cV := by
    rw [abs_le]
    constructor <;> nlinarith
  exact ⟨habs, by linarith [hy j], by linarith [(abs_le.mp habs).1], hd⟩

/-- The column residual against $\mathbf{Z}$ from a Schur form of $\mathbf{Z}$: with
$\|\mathbf{Z}\|_2 + e a \le \tfrac32a$ and
$\|\mathbf{Z} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2 \le ea$, each column satisfies
$\|(\mathbf{Z} - t_{jj}\mathbf{I})\mathbf{v}_j\| \le \eta a\|\mathbf{v}_j\|$,
$\eta$ = `eigEta n e eU cR cV`. -/
private theorem eig_col_residual_le {n : ℕ} {Z U T Y V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a e eU cR cV cN : ℝ} (ha : 0 ≤ a) (he0 : 0 ≤ e) (hZe : specNorm Z + e * a ≤ 3 / 2 * a)
    (hZT : specNorm (Z - U * T * Uᴴ) ≤ e * a) (hU : specNorm (Uᴴ * U - 1) ≤ eU)
    (hY : ∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ cN ∧
      ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤ cR * frobNorm T * ‖WithLp.toLp 2 (Y.col j)‖)
    (hV : specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y) (hcV : 0 ≤ cV) (hcR : 0 ≤ cR)
    (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8) (j : Fin (n + 1)) :
    ‖WithLp.toLp 2 ((Z - T j j • 1) *ᵥ V.col j)‖ ≤
      eigEta n e eU cR cV * a * ‖WithLp.toLp 2 (V.col j)‖ := by
  obtain ⟨hu, hw, hcol⟩ := eig_col_facts hU (fun j => (hY j).1) hV hcV heU hc
  obtain ⟨-, hy, hv, hd⟩ := hcol j
  have heU0 : 0 ≤ eU := (specNorm_nonneg _).trans hU
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hT : specNorm T ≤ 12 / 7 * a := by
    have h1 := one_sub_mul_specNorm_le_specNorm_mul_mul_conjTranspose hU (by linarith) T
    have h2 := specNorm_add_le Z (U * T * Uᴴ - Z)
    rw [add_sub_cancel, specNorm_sub_comm] at h2
    nlinarith [specNorm_nonneg T]
  have hTF : frobNorm T ≤ √((n : ℝ) + 1) * specNorm T := by
    have := frobNorm_le_sqrt_card_mul_specNorm T
    rwa [card_fin_succ_cast] at this
  set nv := ‖WithLp.toLp 2 (V.col j)‖
  set ny := ‖WithLp.toLp 2 (Y.col j)‖
  set sN := √((n : ℝ) + 1)
  have hsN : 0 ≤ sN := Real.sqrt_nonneg _
  have hyv : ny ≤ 9 / 7 * nv := by linarith
  have hu0 := specNorm_nonneg U
  have h1 : (specNorm (Z - U * T * Uᴴ) * specNorm U +
      specNorm U * specNorm T * specNorm (Uᴴ * U - 1)) * ny ≤
      a * nv * (153 / 112 * e + 459 / 196 * eU) := by
    calc (specNorm (Z - U * T * Uᴴ) * specNorm U +
          specNorm U * specNorm T * specNorm (Uᴴ * U - 1)) * ny
        ≤ (e * a * (17 / 16) + 17 / 16 * (12 / 7 * a) * eU) * (9 / 7 * nv) := by
          gcongr
      _ = a * nv * (153 / 112 * e + 459 / 196 * eU) := by ring
  have h2 : specNorm U * ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤
      a * nv * (459 / 196 * (sN * cR)) := by
    calc specNorm U * ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖
        ≤ 17 / 16 * (cR * (sN * (12 / 7 * a)) * (9 / 7 * nv)) := by
          refine mul_le_mul hu ((hY j).2.trans ?_) (norm_nonneg _) (by norm_num)
          gcongr
          exact hTF.trans (by gcongr)
      _ = a * nv * (459 / 196 * (sN * cR)) := by ring
  have h3 : (specNorm Z + ‖T j j‖) * ‖WithLp.toLp 2 (V.col j - U *ᵥ Y.col j)‖ ≤
      a * nv * (6885 / 1568 * (((n : ℝ) + 1) * cV)) := by
    have hZ : specNorm Z ≤ 3 / 2 * a := by nlinarith
    have htt : ‖T j j‖ ≤ 12 / 7 * a := (norm_apply_le_specNorm T j j).trans hT
    calc (specNorm Z + ‖T j j‖) * ‖WithLp.toLp 2 (V.col j - U *ᵥ Y.col j)‖
        ≤ (3 / 2 * a + 12 / 7 * a) * (153 / 128 * ((n : ℝ) + 1) * cV * (8 / 7 * nv)) := by
          gcongr
          refine hd.trans (hw.trans ?_)
          have : 0 ≤ 153 / 128 * ((n : ℝ) + 1) * cV := by positivity
          nlinarith
      _ = a * nv * (6885 / 1568 * (((n : ℝ) + 1) * cV)) := by ring
  refine (norm_mulVec_sub_smul_le_of_schur Z U T (Y.col j) (V.col j) (T j j)).trans ?_
  have hanv : 0 ≤ a * nv := by positivity
  have hcR' : 0 ≤ sN * cR := mul_nonneg hsN hcR
  have hcV' : 0 ≤ ((n : ℝ) + 1) * cV := by positivity
  calc _ ≤ a * nv * (153 / 112 * e + 459 / 196 * eU) + a * nv * (459 / 196 * (sN * cR)) +
        a * nv * (6885 / 1568 * (((n : ℝ) + 1) * cV)) := add_le_add (add_le_add h1 h2) h3
    _ ≤ a * nv * (2 * e + 3 * eU + 4 * (sN * cR) + 8 * (((n : ℝ) + 1) * cV)) := by
        rw [← mul_add, ← mul_add]
        exact mul_le_mul_of_nonneg_left (by linarith) hanv
    _ = eigEta n e eU cR cV * a * nv := by unfold eigEta; ring

/-- A triangular residual constant is nonnegative when $\mathbf{T} \ne 0$ and the columns of
$\mathbf{Y}$ are nonzero. -/
private theorem nonneg_of_col_residual_le {n : ℕ} {T Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {cR cN : ℝ} (hT : T ≠ 0) (hcN : cN < 1)
    (hY : ∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ cN ∧
      ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤ cR * frobNorm T * ‖WithLp.toLp 2 (Y.col j)‖) :
    0 ≤ cR := by
  have hy : 0 < ‖WithLp.toLp 2 (Y.col 0)‖ := by linarith [(abs_le.mp (hY 0).1).1]
  have hF : 0 < frobNorm T :=
    lt_of_le_of_ne (frobNorm_nonneg T) (Ne.symm (mt frobNorm_eq_zero_iff.mp hT))
  have h := (norm_nonneg _).trans (hY 0).2
  by_contra hneg
  have : cR * frobNorm T * ‖WithLp.toLp 2 (Y.col 0)‖ < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (not_le.mp hneg) hF) hy
  linarith

/-- The residual part against $\mathbf{A}$ from the column residuals against $\mathbf{X}$, with
$\|\mathbf{A} - \mathbf{X}\|_2 \le e_R\|\mathbf{A}\|_2$; also the matrix residual against
$\mathbf{X}$. -/
private theorem eigResidualOf_of_col_residual {n : ℕ}
    {A X T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {eR η c : ℝ} (hη : 0 ≤ η)
    (hAX : specNorm (A - X) ≤ eR * specNorm A)
    (hcol : ∀ j, |‖WithLp.toLp 2 (V.col j)‖ - 1| ≤ c)
    (hres : ∀ j, ‖WithLp.toLp 2 ((X - T j j • 1) *ᵥ V.col j)‖ ≤
      η * specNorm A * ‖WithLp.toLp 2 (V.col j)‖) :
    EigResidualOf A T V (eR + η) (eR + √((n : ℝ) + 1) * η) c ∧
      specNorm (X * V - V * Matrix.diagonal (fun i => T i i)) ≤
        √((n : ℝ) + 1) * η * specNorm A * specNorm V := by
  have ha := specNorm_nonneg A
  have hXV : specNorm (X * V - V * Matrix.diagonal (fun i => T i i)) ≤
      √((n : ℝ) + 1) * η * specNorm A * specNorm V := by
    have := specNorm_mul_sub_mul_diagonal_le_of_forall_col (Z := X) (V := V)
      (d := fun i => T i i) (mul_nonneg hη ha) (fun j => hres j)
    rw [card_fin_succ_cast] at this
    linarith
  refine ⟨⟨hcol, fun j => ?_, ?_⟩, hXV⟩
  · have hsplit : (A - T j j • 1) *ᵥ V.col j =
        (A - X) *ᵥ V.col j + (X - T j j • 1) *ᵥ V.col j := by
      rw [← Matrix.add_mulVec]; congr 1; abel
    rw [hsplit, WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    have h1 := (norm_toLp_mulVec_le (A - X) (V.col j)).trans
      (mul_le_mul_of_nonneg_right hAX (norm_nonneg _))
    linarith [hres j]
  · have hsplit : A * V - V * Matrix.diagonal (fun i => T i i) =
        (A - X) * V + (X * V - V * Matrix.diagonal (fun i => T i i)) := by
      rw [Matrix.sub_mul]; abel
    rw [hsplit]
    refine (specNorm_add_le _ _).trans ?_
    have h1 := (specNorm_mul_le (A - X) V).trans
      (mul_le_mul_of_nonneg_right hAX (specNorm_nonneg _))
    linarith

/-- The Schur diagonal of an approximate Schur form of a scaled matrix of the class is
separated: if $s^{-1}\mathbf{X}$ is of the class $(B, \Gamma)$, $s > 0$, and
$s^{-1}(\delta + 4e_U(\|\mathbf{X}\|_2 + \delta)) \le \Gamma/(16(n + 1)B)$, then
$\tfrac78\Gamma \le s^{-1}\lvert t_{ii} - t_{jj}\rvert$ for $i \ne j$. -/
private theorem le_inv_mul_norm_sub_diag {n : ℕ} {X U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {s B Γ δ eU : ℝ} (hC : IsConditionedDiagonalizable B Γ (s⁻¹ • X)) (hΓ : 0 < Γ) (hs : 0 < s)
    (hT : T.IsUpperTriangular) (hXT : specNorm (X - U * T * Uᴴ) ≤ δ)
    (hU : specNorm (Uᴴ * U - 1) ≤ eU) (heU : eU ≤ 1 / 8)
    (hE : s⁻¹ * (δ + 4 * eU * (specNorm X + δ)) ≤ Γ / (16 * (n + 1) * B)) :
    ∀ i j, i ≠ j → 7 / 8 * Γ ≤ s⁻¹ * ‖T i i - T j j‖ := by
  obtain ⟨W, E, hW, hEn, hXE⟩ :=
    exists_hasOrthonormalCols_add_eq_mul_mul_conjTranspose_of_le hXT hU heU
  have hT' : (s⁻¹ • T).IsUpperTriangular := fun i j hij => by
    simp [Matrix.smul_apply, hT hij]
  have hXE' : s⁻¹ • X + s⁻¹ • E = W * (s⁻¹ • T) * Wᴴ := by
    rw [← smul_add, hXE, Matrix.mul_smul, Matrix.smul_mul]
  have hE' : specNorm (s⁻¹ • E) ≤ Γ / (16 * (n + 1) * B) := by
    rw [specNorm_real_smul, abs_of_pos (inv_pos.mpr hs)]
    exact (mul_le_mul_of_nonneg_left hEn (inv_nonneg.mpr hs.le)).trans hE
  intro i j hij
  have h := hC.le_norm_sub_diag_of_add_eq hΓ hW hT' hXE' hE' i j hij
  rwa [Matrix.smul_apply, Matrix.smul_apply, ← smul_sub, norm_smul, Real.norm_of_nonneg
    (inv_nonneg.mpr hs.le)] at h

/-- The conditioning of $\mathbf{V}$ from the class of $s^{-1}\mathbf{X}$: columns with norms
within $c \le 1/8$ of $1$, column residuals $\|(\mathbf{X} - t_{jj}\mathbf{I})\mathbf{v}_j\| \le
\rho\|\mathbf{v}_j\|$ with $8\sqrt{n + 1}\,Bs^{-1}\rho \le \Gamma$, and the diagonal
$\tfrac78\Gamma$-separated after scaling give $\kappa(\mathbf{V}) \le 2\sqrt{n + 1}\,B$. -/
private theorem isUnit_and_pseudoConditionNumber_le_of_class {n : ℕ}
    {X T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s B Γ ρ c : ℝ}
    (hC : IsConditionedDiagonalizable B Γ (s⁻¹ • X)) (hΓ : 0 < Γ) (hs : 0 < s) (hρ : 0 ≤ ρ)
    (hsmall : 8 * √((n : ℝ) + 1) * B * (s⁻¹ * ρ) ≤ Γ) (hc : c ≤ 1 / 8)
    (hcol : ∀ j, |‖WithLp.toLp 2 (V.col j)‖ - 1| ≤ c)
    (hres : ∀ j, ‖WithLp.toLp 2 ((X - T j j • 1) *ᵥ V.col j)‖ ≤ ρ * ‖WithLp.toLp 2 (V.col j)‖)
    (hgap : ∀ i j, i ≠ j → 7 / 8 * Γ ≤ s⁻¹ * ‖T i i - T j j‖) :
    IsUnit V ∧ pseudoConditionNumber V ≤ 2 * √((n : ℝ) + 1) * B := by
  have hB0 : 0 ≤ B := by
    obtain ⟨W, -, -, -, hB, -⟩ := hC
    exact (pseudoConditionNumber_nonneg W).trans hB
  have hsi : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hcol 0)
  have hres' (j : Fin (n + 1)) : ‖WithLp.toLp 2 ((s⁻¹ • X - (s⁻¹ • T j j) • 1) *ᵥ V.col j)‖ ≤
      s⁻¹ * ρ * ‖WithLp.toLp 2 (V.col j)‖ := by
    have h : s⁻¹ • X - (s⁻¹ • T j j) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
        s⁻¹ • (X - T j j • 1) := by
      rw [smul_sub, smul_assoc]
    rw [h, Matrix.smul_mulVec, WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hsi, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hres j) hsi
  have hsep (i j : Fin (n + 1)) (hij : i ≠ j) : Γ / 2 ≤ ‖s⁻¹ • T i i - s⁻¹ • T j j‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hsi]
    linarith [hgap i j hij]
  obtain ⟨hVu, -, hκ⟩ := hC.pseudoConditionNumber_le_of_residual (ev := fun j => s⁻¹ • T j j)
    (m := 1 - c) (m' := 1 + c) hΓ (mul_nonneg hsi hρ)
    (by rw [card_fin_succ_cast]; linarith) (by linarith)
    (fun j => ⟨by linarith [(abs_le.mp (hcol j)).1], by linarith [(abs_le.mp (hcol j)).2]⟩)
    hres' hsep
  refine ⟨hVu, hκ.trans ?_⟩
  rw [card_fin_succ_cast]
  have hq : (1 + c) / (1 - c) ≤ 9 / 7 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hsB : 0 ≤ √((n : ℝ) + 1) * B := mul_nonneg (Real.sqrt_nonneg _) hB0
  calc 7 / 5 * √((n : ℝ) + 1) * B * ((1 + c) / (1 - c))
      ≤ 7 / 5 * √((n : ℝ) + 1) * B * (9 / 7) := by gcongr
    _ ≤ 2 * √((n : ℝ) + 1) * B := by nlinarith

/-- **An eigendecomposition from a Schur form of a regularized matrix.** Let $\mathbf{A} \ne 0$ be
of order $n + 1$, $\|\mathbf{A} - \mathbf{X}\|_2 \le e_R\|\mathbf{A}\|_2$,
$\|\mathbf{X} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2 \le e_X\|\mathbf{A}\|_2$ with
$\mathbf{T}$ upper triangular and $\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e_U$,
and $s^{-1}\mathbf{X}$ of the class $(B, \Gamma)$, $\Gamma > 0$, for some
$s \ge c_1\|\mathbf{A}\|_{\mathsf F}$, $c_1 > 0$. Let the columns of $\mathbf{Y}$ have norms within
$c_N$ of $1$ and residuals $\|(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y}_j\| \le
c_R\|\mathbf{T}\|_{\mathsf F}\|\mathbf{y}_j\|$, and $\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|_2 \le
c_V\|\mathbf{U}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$, $c_V \ge 0$. With $\eta$ =
`eigEta n eX eU cR cV` and
$c$ = `eigColTol n eU cV cN`, let $e_R + e_X \le 1/2$, $e_U \le 1/8$, $c \le 1/8$,
$e_X + 6e_U \le c_1\Gamma/(16(n + 1)B)$ and $8\sqrt{n + 1}\,B\eta \le c_1\Gamma$. Then the columns
of $\mathbf{V}$ have norms within $c$ of $1$ and residuals at most $(e_R + \eta)\|\mathbf{A}\|_2
\|\mathbf{v}_j\|$, the matrix residual is at most $(e_R + \sqrt{n + 1}\,\eta)\|\mathbf{A}\|_2
\|\mathbf{V}\|_2$, $\mathbf{V}$ is invertible with $\kappa(\mathbf{V}) \le 2\sqrt{n + 1}\,B$,
$\|\mathbf{V}\mathbf{D}\mathbf{V}^{-1} - \mathbf{A}\|_2 \le (e_R + 2(n + 1)B\eta)\|\mathbf{A}\|_2$,
and $\lvert t_{ii} - t_{jj}\rvert \ge \tfrac78c_1\Gamma\|\mathbf{A}\|_2$ for $i \ne j$.
No printed source. -/
theorem eigDecompOf_of_schur {n : ℕ} {A X U T Y V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {s c₁ B Γ eR eX eU cR cV cN : ℝ}
    (hT : T.IsUpperTriangular) (hU : specNorm (Uᴴ * U - 1) ≤ eU)
    (hAX : specNorm (A - X) ≤ eR * specNorm A) (hXT : specNorm (X - U * T * Uᴴ) ≤ eX * specNorm A)
    (hs : c₁ * frobNorm A ≤ s) (hc₁ : 0 < c₁) (hA : A ≠ 0)
    (hC : IsConditionedDiagonalizable B Γ (s⁻¹ • X)) (hΓ : 0 < Γ)
    (hY : ∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ cN ∧
      ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤ cR * frobNorm T * ‖WithLp.toLp 2 (Y.col j)‖)
    (hV : specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y) (hcV : 0 ≤ cV)
    (he : eR + eX ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hsep : eX + 6 * eU ≤ c₁ * Γ / (16 * (n + 1) * B))
    (hκ : 8 * √((n : ℝ) + 1) * B * eigEta n eX eU cR cV ≤ c₁ * Γ) :
    EigDecompOf A T V (eR + eigEta n eX eU cR cV) (eR + √((n : ℝ) + 1) * eigEta n eX eU cR cV)
      (eigColTol n eU cV cN) (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR cV)
      (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) := by
  set a := specNorm A
  set η := eigEta n eX eU cR cV
  have ha : 0 < a := lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp hA))
  have heR0 : 0 ≤ eR := le_of_mul_le_mul_right (by simpa using (specNorm_nonneg _).trans hAX) ha
  have heX0 : 0 ≤ eX := le_of_mul_le_mul_right (by simpa using (specNorm_nonneg _).trans hXT) ha
  have heU0 : 0 ≤ eU := (specNorm_nonneg _).trans hU
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hX : specNorm X ≤ (1 + eR) * a := by
    have := specNorm_add_le A (X - A)
    rw [add_sub_cancel, specNorm_sub_comm] at this
    linarith
  have hZe : specNorm X + eX * a ≤ 3 / 2 * a := by nlinarith
  have hT0 : T ≠ 0 := by
    rintro rfl
    have h1 := specNorm_add_le (A - X) X
    rw [sub_add_cancel] at h1
    simp only [Matrix.mul_zero, Matrix.zero_mul, sub_zero] at hXT
    nlinarith
  have hcR : 0 ≤ cR := nonneg_of_col_residual_le hT0 (by unfold eigColTol at hc; nlinarith) hY
  have hη : 0 ≤ η := by
    have h1 := mul_nonneg (Real.sqrt_nonneg ((n : ℝ) + 1)) hcR
    have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1) hcV
    simp only [η, eigEta]; nlinarith
  have hres := eig_col_residual_le ha.le heX0 hZe hXT hU hY hV hcV hcR heU hc
  obtain ⟨-, -, hcol⟩ := eig_col_facts hU (fun j => (hY j).1) hV hcV heU hc
  obtain ⟨hR, hXV⟩ := eigResidualOf_of_col_residual hη hAX (fun j => (hcol j).1) hres
  have hsA : c₁ * a ≤ s := (mul_le_mul_of_nonneg_left (specNorm_le_frobNorm A) hc₁.le).trans hs
  have hs0 : 0 < s := lt_of_lt_of_le (mul_pos hc₁ ha) hsA
  have hB1 : 1 ≤ B := by
    obtain ⟨W, -, hW, -, hB, -⟩ := hC
    exact (one_le_pseudoConditionNumber hW.ne_zero).trans hB
  have hK0 : 0 ≤ Γ / (16 * (n + 1) * B) := by positivity
  have hgap := le_inv_mul_norm_sub_diag hC hΓ hs0 hT hXT hU heU (by
    rw [mul_div_assoc] at hsep
    have h1 : eX * a + 4 * eU * (specNorm X + eX * a) ≤ s * (Γ / (16 * (n + 1) * B)) := by
      nlinarith [mul_le_mul_of_nonneg_right hsep ha.le]
    calc s⁻¹ * (eX * a + 4 * eU * (specNorm X + eX * a))
        ≤ s⁻¹ * (s * (Γ / (16 * (n + 1) * B))) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hs0.le)
      _ = _ := by field_simp)
  obtain ⟨hVu, hκV⟩ := isUnit_and_pseudoConditionNumber_le_of_class hC hΓ hs0
    (mul_nonneg hη ha.le) (by
      have h1 : 8 * √((n : ℝ) + 1) * B * (s⁻¹ * (η * a)) =
          s⁻¹ * a * (8 * √((n : ℝ) + 1) * B * η) := by ring
      rw [h1]
      calc s⁻¹ * a * (8 * √((n : ℝ) + 1) * B * η) ≤ s⁻¹ * a * (c₁ * Γ) := by gcongr
        _ = s⁻¹ * (c₁ * a) * Γ := by ring
        _ ≤ s⁻¹ * s * Γ := by gcongr
        _ = Γ := by field_simp) (by unfold eigColTol at hc ⊢; linarith)
      (fun j => (hcol j).1) hres hgap
  refine ⟨hR, hVu, hκV, ?_, fun i j hij => ?_⟩
  · have hsplit : V * Matrix.diagonal (fun i => T i i) * V⁻¹ - A =
        (V * Matrix.diagonal (fun i => T i i) * V⁻¹ - X) + (X - A) := by abel
    rw [hsplit]
    refine (specNorm_add_le _ _).trans ?_
    have h1 := specNorm_mul_diagonal_mul_inv_sub_le (Z := X) (d := fun i => T i i) hVu
    rw [specNorm_sub_comm X A]
    have hκ' : specNorm V * specNorm V⁻¹ ≤ 2 * √((n : ℝ) + 1) * B := by
      rwa [← pseudoConditionNumber_of_isUnit hVu]
    have hsN : √((n : ℝ) + 1) * √((n : ℝ) + 1) = (n : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have h2 : specNorm (X * V - V * Matrix.diagonal (fun i => T i i)) * specNorm V⁻¹ ≤
        2 * ((n : ℝ) + 1) * B * η * a := by
      calc _ ≤ √((n : ℝ) + 1) * η * a * specNorm V * specNorm V⁻¹ :=
            mul_le_mul_of_nonneg_right hXV (specNorm_nonneg _)
        _ = √((n : ℝ) + 1) * η * a * (specNorm V * specNorm V⁻¹) := by ring
        _ ≤ √((n : ℝ) + 1) * η * a * (2 * √((n : ℝ) + 1) * B) := by gcongr
        _ = 2 * (√((n : ℝ) + 1) * √((n : ℝ) + 1)) * B * η * a := by ring
        _ = _ := by rw [hsN]
    linarith
  · have h := hgap i j hij
    have hsa : 7 / 8 * Γ * (c₁ * a) ≤ 7 / 8 * Γ * s := by gcongr
    have h2 : 7 / 8 * Γ * s ≤ ‖T i i - T j j‖ := by
      have h3 : s * (s⁻¹ * ‖T i i - T j j‖) = ‖T i i - T j j‖ := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left h hs0.le]
    nlinarith

/-- **The residual of an eigendecomposition from a Schur form of the matrix itself**: let
$\|\mathbf{A} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2 \le e_A\|\mathbf{A}\|_2$ and
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e_U$ at the order $n + 1$, the columns of
$\mathbf{Y}$ with norms within $c_N$ of $1$ and residuals $\|(\mathbf{T} - t_{jj}\mathbf{I})
\mathbf{y}_j\| \le c_R\|\mathbf{T}\|_{\mathsf F}\|\mathbf{y}_j\|$, and
$\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|_2 \le
c_V\|\mathbf{U}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$, $c_V \ge 0$. With $\eta$ =
`eigEta n eA eU cR cV`
and $c$ = `eigColTol n eU cV cN`, let $e_A \le 1/2$, $e_U \le 1/8$ and $c \le 1/8$. Then the columns
of $\mathbf{V}$ have norms within $c$ of $1$ and residuals at most
$\eta\|\mathbf{A}\|_2\|\mathbf{v}_j\|$, and the matrix residual is at most
$\sqrt{n + 1}\,\eta\|\mathbf{A}\|_2\|\mathbf{V}\|_2$. No hypothesis on $\mathbf{A}$.
No printed source. -/
theorem eigResidualOf_of_schur {n : ℕ} {A U T Y V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {eA eU cR cV cN : ℝ} (hU : specNorm (Uᴴ * U - 1) ≤ eU)
    (hAT : specNorm (A - U * T * Uᴴ) ≤ eA * specNorm A)
    (hY : ∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ cN ∧
      ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤ cR * frobNorm T * ‖WithLp.toLp 2 (Y.col j)‖)
    (hV : specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y) (hcV : 0 ≤ cV)
    (he : eA ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8) :
    EigResidualOf A T V (eigEta n eA eU cR cV) (√((n : ℝ) + 1) * eigEta n eA eU cR cV)
      (eigColTol n eU cV cN) := by
  obtain ⟨-, -, hcol⟩ := eig_col_facts hU (fun j => (hY j).1) hV hcV heU hc
  have heU0 : 0 ≤ eU := (specNorm_nonneg _).trans hU
  by_cases hA : A = 0
  · subst hA
    have hT : T = 0 := by
      rw [specNorm_zero, mul_zero, zero_sub, specNorm_neg] at hAT
      have h := one_sub_mul_specNorm_le_specNorm_mul_mul_conjTranspose hU (by linarith) T
      have : specNorm T = 0 := le_antisymm (by nlinarith [specNorm_nonneg T]) (specNorm_nonneg T)
      exact specNorm_eq_zero_iff.mp this
    subst hT
    refine ⟨fun j => (hcol j).1, fun j => ?_, ?_⟩ <;> simp
  set a := specNorm A
  have ha : 0 < a := lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp hA))
  have heA0 : 0 ≤ eA := le_of_mul_le_mul_right (by simpa using (specNorm_nonneg _).trans hAT) ha
  have hT0 : T ≠ 0 := by
    rintro rfl
    simp only [Matrix.mul_zero, Matrix.zero_mul, sub_zero] at hAT
    nlinarith
  have hcR : 0 ≤ cR := nonneg_of_col_residual_le hT0 (by
    have : 0 ≤ ((n : ℝ) + 1) * cV := mul_nonneg (by positivity) hcV
    unfold eigColTol at hc; nlinarith) hY
  have hη : 0 ≤ eigEta n eA eU cR cV := by
    have h1 := mul_nonneg (Real.sqrt_nonneg ((n : ℝ) + 1)) hcR
    have h2 := mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hcV
    unfold eigEta; nlinarith
  have hres := eig_col_residual_le ha.le heA0 (by nlinarith) hAT hU hY hV hcV hcR heU hc
  obtain ⟨hR, -⟩ :=
    eigResidualOf_of_col_residual (eR := 0) hη (by simp) (fun j => (hcol j).1) hres
  simpa only [zero_add] using hR

end NLAlib
