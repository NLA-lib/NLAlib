/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.EigenvectorConditioning
public import NLAlib.Matrix.Perturbation.EigenvalueMatching

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
      Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mul_assoc, Matrix.mul_one, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul]
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

/-- **An eigendecomposition from a Schur form of a regularized matrix.** Let $\mathbf{A} \ne 0$ be
of order $n + 1$, $\|\mathbf{A} - \mathbf{X}\|_2 \le e_R\|\mathbf{A}\|_2$,
$\|\mathbf{X} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2 \le e_X\|\mathbf{A}\|_2$ with
$\mathbf{T}$ upper triangular and $\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e_U$,
and $s^{-1}\mathbf{X}$ of the class $(B, \Gamma)$, $\Gamma > 0$, for some
$s \ge c_1\|\mathbf{A}\|_{\mathsf F}$, $c_1 > 0$. Let the columns of $\mathbf{Y}$ have norms within
$c_N$ of $1$ and residuals $\|(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y}_j\| \le
c_R\|\mathbf{T}\|_{\mathsf F}\|\mathbf{y}_j\|$, and $\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|_2 \le
c_V\|\mathbf{U}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$. With $\eta$ = `eigEta n eX eU cR cV` and
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
    (hV : specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y)
    (he : eR + eX ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hsep : eX + 6 * eU ≤ c₁ * Γ / (16 * (n + 1) * B))
    (hκ : 8 * √((n : ℝ) + 1) * B * eigEta n eX eU cR cV ≤ c₁ * Γ) :
    EigDecompOf A T V (eR + eigEta n eX eU cR cV) (eR + √((n : ℝ) + 1) * eigEta n eX eU cR cV)
      (eigColTol n eU cV cN) (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR cV)
      (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) := by
  sorry

/-- **The residual of an eigendecomposition from a Schur form of the matrix itself**: let
$\|\mathbf{A} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2 \le e_A\|\mathbf{A}\|_2$ and
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e_U$ at the order $n + 1$, the columns of
$\mathbf{Y}$ with norms within $c_N$ of $1$ and residuals $\|(\mathbf{T} - t_{jj}\mathbf{I})
\mathbf{y}_j\| \le c_R\|\mathbf{T}\|_{\mathsf F}\|\mathbf{y}_j\|$, and
$\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|_2 \le
c_V\|\mathbf{U}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$. With $\eta$ = `eigEta n eA eU cR cV`
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
    (hV : specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y)
    (he : eA ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8) :
    EigResidualOf A T V (eigEta n eA eU cR cV) (√((n : ℝ) + 1) * eigEta n eA eU cR cV)
      (eigColTol n eU cV cN) := by
  sorry

end NLAlib
