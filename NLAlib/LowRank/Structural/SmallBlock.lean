/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Vandermonde
public import NLAlib.Krylov.Basic.KrylovVandermonde
public import NLAlib.LowRank.Structural.BlockKrylov
public import NLAlib.LowRank.Structural.Filter
public import NLAlib.Matrix.Functions.Polynomial
public import NLAlib.Matrix.Spectral.FrameDeflation
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.Polynomial.Interpolation.LagrangeBound

/-!
# Randomized block Krylov iteration with a single start vector

The deterministic part of the analysis of randomized block Krylov iteration with block size one,
start vector $\mathbf{x}$. With $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$,
$\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)$ is at least as good as the randomized SVD at the
filtered simulated block
$f(\mathbf{H})\mathbf{K}$, $\mathbf{K} = [\mathbf{x}, \mathbf{H}\mathbf{x}, \dots,
\mathbf{H}^{t-1}\mathbf{x}]$, for every polynomial $f$ of degree less than $d$ with
$t + d \le q + 1$ (`NLAlib.singularValues_sub_rbki_le_of_degree_lt_of_add_le`). For an
orthonormal frame $\mathbf{Z}$ of right singular vectors for $\sigma_0 > \dots > \sigma_{t-1} > 0$
the head block is $\mathbf{Z}^{\mathsf{H}}\mathbf{K} =
\operatorname{diag}(\mathbf{Z}^{\mathsf{H}}\mathbf{x})\,\mathbf{V}$ with $\mathbf{V}$ the
Vandermonde matrix of $\sigma_i^2$, the columns of $\mathbf{V}^{-1}$ are the coefficients of the
Lagrange basis polynomials $\ell_i$ of these nodes, and column $i$ of the sketch residual of the
filtered range finder is
$(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i^{-1}\,\mathbf{A}f(\mathbf{H})\ell_i(\mathbf{H})
(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}$. On the tail spectrum
$\lvert\ell_i\rvert \le \Delta^{-(t-1)}$ for the relative gap $\Delta$ of the squared head
singular values, which gives the starting-block factor
$\Delta^{-2(t-1)}\sum_i \lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}$ in place of the
inverse moment of a Gaussian block of width at least $t + 2$.

The statements carry the sharp factors; nothing is random here.

## Main results

* `NLAlib.frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le`: the sketch
  residual of the single-vector simulated block.
* `NLAlib.specNorm_sub_rbki_replicateCol_sq_le`,
  `NLAlib.frobNorm_sub_rbki_replicateCol_sq_le`: the single-vector bound,
  spectral and Frobenius.
* `NLAlib.rbki_replicateCol_eq_self`: the exact case, distinct nonzero
  singular values and $q \ge \operatorname{rank}\mathbf{A}$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The Lagrange basis polynomials of real nodes, mapped to $\Bbbk$, are those of the nodes in
$\Bbbk$. -/
private theorem basis_ofReal_eq_map {t : ℕ} (d : Fin t → ℝ) (i : Fin t) :
    Lagrange.basis Finset.univ (fun j => (d j : 𝕜)) i =
      (Lagrange.basis Finset.univ d i).map (algebraMap ℝ 𝕜) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, map_inv₀, map_sub,
    RCLike.algebraMap_eq_ofReal]

/-- Column $i$ of $\mathbf{K}_t(\mathbf{H}, \mathbf{x})\mathbf{V}^{-1}$, $\mathbf{V}$ the
Vandermonde matrix of distinct nodes, is $\ell_i(\mathbf{H})\mathbf{x}$. -/
private theorem krylovMatrix_mul_inv_vandermonde_apply (H : Matrix n n 𝕜) (x : n → 𝕜) {t : ℕ}
    {v : Fin t → 𝕜} (hv : Function.Injective v) (a : n) (i : Fin t) :
    (krylovMatrix H x t * (Matrix.vandermonde v)⁻¹) a i =
      (aeval H (Lagrange.basis Finset.univ v i) *ᵥ x) a := by
  have hdeg : (Lagrange.basis Finset.univ v i).natDegree < t := by
    rw [Lagrange.natDegree_basis hv.injOn (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have := i.isLt
    omega
  rw [Matrix.inv_vandermonde hv, Matrix.mul_apply, aeval_eq_sum_range' hdeg, Matrix.sum_mulVec,
    Finset.sum_apply, ← Fin.sum_univ_eq_sum_range
      (fun j => (((Lagrange.basis Finset.univ v i).coeff j • H ^ j) *ᵥ x) a)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [krylovMatrix_apply, Matrix.of_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    mul_comm]

/-- Column $i$ of $\mathbf{K}(\mathbf{Z}^{\mathsf{H}}\mathbf{K})^{+}$ for the single-vector
simulated block $\mathbf{K}$ and an eigenframe $\mathbf{Z}$ with distinct eigenvalues is
$(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i^{-1}\,\ell_i(\mathbf{H})\mathbf{x}$. -/
private theorem blockKrylovMatrix_mul_pinv_apply {t : ℕ} {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) {Z : Matrix n (Fin t) 𝕜} {d : Fin t → ℝ}
    (hHZ : H * Z = Z * Matrix.diagonal fun i => (d i : 𝕜)) (hd : Function.Injective d)
    {x : n → 𝕜} (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) (a : n) (i : Fin t) :
    (blockKrylovMatrix H (Matrix.replicateCol Unit x) t *
        pinv (Zᴴ * blockKrylovMatrix H (Matrix.replicateCol Unit x) t)) a i =
      (aeval H (Lagrange.basis Finset.univ d i) *ᵥ x) a * ((Zᴴ *ᵥ x) i)⁻¹ := by
  have hv : Function.Injective fun i => (d i : 𝕜) := RCLike.ofReal_injective.comp hd
  have hV := (Matrix.det_vandermonde_ne_zero_iff.mpr hv).isUnit
  have hinv : (Matrix.diagonal (Zᴴ *ᵥ x) * Matrix.vandermonde fun i => (d i : 𝕜))⁻¹ =
      (Matrix.vandermonde fun i => (d i : 𝕜))⁻¹ * Matrix.diagonal fun i => ((Zᴴ *ᵥ x) i)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.vandermonde _), Matrix.mul_nonsing_inv _ hV,
      Matrix.one_mul, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun i => mul_inv_cancel₀ (hx i))
  have hunit : IsUnit (Matrix.diagonal (Zᴴ *ᵥ x) * Matrix.vandermonde fun i => (d i : 𝕜)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hx i) hV.ne_zero
  rw [hH.conjTranspose_mul_blockKrylovMatrix_replicateCol hHZ x, blockKrylovMatrix_replicateCol,
    show Matrix.submatrix (Matrix.diagonal (Zᴴ *ᵥ x) * Matrix.vandermonde fun i => (d i : 𝕜)) id
        Prod.fst = Matrix.submatrix _ (Equiv.refl (Fin t)) (Equiv.prodPUnit (Fin t)) from rfl,
    pinv_submatrix_equiv, pinv_of_isUnit hunit, hinv]
  have hmul := Matrix.submatrix_mul_equiv (krylovMatrix H x t)
    ((Matrix.vandermonde fun i => (d i : 𝕜))⁻¹ * Matrix.diagonal fun i => ((Zᴴ *ᵥ x) i)⁻¹)
    id (Equiv.prodPUnit (Fin t)) id
  rw [Matrix.submatrix_id_id] at hmul
  rw [show (krylovMatrix H x t).submatrix id Prod.fst =
      (krylovMatrix H x t).submatrix id (Equiv.prodPUnit (Fin t)) from rfl,
    show ⇑(Equiv.refl (Fin t)) = id from rfl, hmul, ← Matrix.mul_assoc, Matrix.mul_diagonal,
    krylovMatrix_mul_inv_vandermonde_apply H x hv, basis_ofReal_eq_map, aeval_map_algebraMap]

/-- A polynomial filter on the complement of an eigenframe: for an orthonormal frame
$\mathbf{Z}$ invariant under $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, the deflated matrix
$\mathbf{C} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ and real polynomials
$f$, $\ell$,
$(\mathbf{A}f(\mathbf{H}) - \mathbf{A}f(\mathbf{H})\mathbf{Z}\mathbf{Z}^{\mathsf{H}})
\ell(\mathbf{H}) = (f\ell)(\mathbf{C}\mathbf{C}^{\mathsf{H}})\,\mathbf{C}$. -/
private theorem sub_mul_mul_conjTranspose_mul_aeval [DecidableEq m] {s : Type*} [Fintype s]
    [DecidableEq s] (A : Matrix m n 𝕜) {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    {d : s → ℝ} (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i => (d i : 𝕜)) (f ℓ : ℝ[X]) :
    (A * aeval (Aᴴ * A) f - A * aeval (Aᴴ * A) f * Z * Zᴴ) * aeval (Aᴴ * A) ℓ =
      aeval ((A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) (f * ℓ) * (A - A * Z * Zᴴ) := by
  have hHh := Matrix.isHermitian_conjTranspose_mul_self A
  set H := Aᴴ * A with hH
  set P := 1 - Z * Zᴴ with hP
  have hproj : IsStarProjection P := hZ.isStarProjection_mul_conjTranspose.one_sub
  have hPP : P * P = P := hproj.isIdempotentElem.eq
  have hZH : Zᴴ * H = (Matrix.diagonal fun i => (d i : 𝕜)) * Zᴴ := by
    have h := congrArg Matrix.conjTranspose hAZ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul Z,
      Matrix.conjTranspose_diagonal_ofReal, hHh.eq] at h
  have hPH : H * P = P * H := by
    rw [hP, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc,
      hAZ, Matrix.mul_assoc Z Zᴴ H, hZH, Matrix.mul_assoc]
  have hC (B : Matrix m n 𝕜) : B - B * Z * Zᴴ = B * P := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hCH : (A * P) * (A * P)ᴴ * (A * P) = (A * P) * H := by
    rw [Matrix.conjTranspose_mul, hproj.conjTranspose_eq]
    calc A * P * (P * Aᴴ) * (A * P) = A * (P * P * (H * P)) := by
          simp only [Matrix.mul_assoc, hH]
      _ = A * P * H := by rw [hPP, hPH, ← Matrix.mul_assoc P, hPP, Matrix.mul_assoc]
  have hq (q : ℝ[X]) : aeval H q * P = P * aeval H q := aeval_mul_eq_mul_aeval_of_mul_eq_mul hPH q
  rw [hC, hC, aeval_mul_eq_mul_aeval_of_mul_eq_mul hCH (f * ℓ), Matrix.mul_assoc A,
    Matrix.mul_assoc A, Matrix.mul_assoc A, Matrix.mul_assoc _ P, ← hq ℓ, ← Matrix.mul_assoc _ _ P,
    ← map_mul, hq]

omit [DecidableEq n] in
/-- A polynomial in $\mathbf{C}\mathbf{C}^{\mathsf{H}}$ applied to a vector is bounded by the
polynomial on $[0, \|\mathbf{C}\|_2^2]$. -/
private theorem norm_toLp_aeval_mul_conjTranspose_self_mulVec_le [DecidableEq m]
    (C : Matrix m n 𝕜) (q : ℝ[X]) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y ∈ Set.Icc 0 (specNorm C ^ 2), |q.eval y| ≤ c) (u : m → 𝕜) :
    ‖WithLp.toLp 2 (aeval (C * Cᴴ) q *ᵥ u)‖ ≤ c * ‖WithLp.toLp 2 u‖ := by
  have h₁ : (0 : ℝ) • (1 : Matrix m m 𝕜) ≤ C * Cᴴ := by
    rw [zero_smul]
    exact Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_self_mul_conjTranspose C)
  have h₂ : C * Cᴴ ≤ (specNorm C ^ 2) • (1 : Matrix m m 𝕜) := by
    have h := conjTranspose_mul_self_le_specNorm_sq_smul_one Cᴴ
    rwa [Matrix.conjTranspose_conjTranspose, specNorm_conjTranspose] at h
  exact (norm_toLp_mulVec_le _ u).trans (mul_le_mul_of_nonneg_right
    (specNorm_aeval_le_of_forall_mem_Icc h₁ h₂ q hc h) (norm_nonneg _))

omit [DecidableEq n] in
/-- Positive singular values with relative gaps of the squares have distinct squares. -/
private theorem sq_singularValues_injective {t : ℕ} (A : Matrix m n 𝕜) {Δ : ℝ} (hΔ : 0 < Δ)
    (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    Function.Injective fun i : Fin t => singularValues A i ^ 2 := by
  have hanti : StrictAnti fun i : Fin t => singularValues A i ^ 2 := by
    intro i j hij
    have hij' : (i : ℕ) + 1 ≤ j := hij
    have h1 := hgap i (by omega)
    have h2 : singularValues A j ^ 2 ≤ singularValues A (i + 1) ^ 2 :=
      pow_le_pow_left₀ (singularValues_nonneg _ _) (singularValues_antitone A hij') 2
    have h3 : 0 < Δ * singularValues A i ^ 2 := mul_pos hΔ (pow_pos (hpos i i.isLt) 2)
    change singularValues A j ^ 2 < singularValues A i ^ 2
    linarith
  exact hanti.injective

omit [DecidableEq n] in
/-- The first $r$ columns of an orthonormal frame of right singular vectors: an orthonormal
frame of right singular vectors with range in that of the frame. -/
private theorem submatrix_castLE_frame {t r : ℕ} (A : Matrix m n 𝕜) {Z : Matrix n (Fin t) 𝕜}
    (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜)) (hr : r ≤ t) :
    HasOrthonormalCols (Z.submatrix id (Fin.castLE hr)) ∧
      LinearMap.range (Z.submatrix id (Fin.castLE hr)).mulVecLin ≤
        LinearMap.range Z.mulVecLin ∧
      Aᴴ * A * Z.submatrix id (Fin.castLE hr) = Z.submatrix id (Fin.castLE hr) *
        Matrix.diagonal fun i : Fin r => ((singularValues A i ^ 2 : ℝ) : 𝕜) := by
  refine ⟨hZ.submatrix (Equiv.refl _) (Fin.castLE_injective hr), range_le_iff_exists_mul.mpr
    ⟨(1 : Matrix (Fin t) (Fin t) 𝕜).submatrix (Equiv.refl _) (Fin.castLE hr), by
      rw [Matrix.mul_submatrix_one]; rfl⟩, ?_⟩
  ext a j
  have h := congrFun (congrFun hAZ a) (Fin.castLE hr j)
  simp only [Matrix.mul_diagonal] at h ⊢
  exact h

/-- **The sketch residual of the single-vector simulated block**: let
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, let $\mathbf{Z} \in \Bbbk^{n \times t}$ be an
orthonormal frame with
$\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$\sigma_i = \sigma_i(\mathbf{A}) > 0$ for $i < t$ and
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$, $\Delta > 0$, and let $\mathbf{x}$
have no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$. For a real polynomial $f$
with $\lvert f \rvert \le a$ on $[0, \sigma_t^2]$, the block
$\mathbf{K} = [\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$ and
$\mathbf{B} = \mathbf{A}f(\mathbf{H})$,
$$\bigl\|(\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{K}
(\mathbf{Z}^{\mathsf{H}}\mathbf{K})^{+}\bigr\|_{\mathsf{F}}^2 \le
a^2\,\Delta^{-2(t-1)}\Bigl(\sum_{i<t}\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}\Bigr)
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$
The exponent $2(t - 1)$ is in $\mathbb{N}$; for $t = 0$ both sides vanish.
[MeyerMuscoMusco2023, Theorem 3 (proof)], the argument, not the statement: there for a Gaussian
vector and a positive semidefinite matrix, through Lagrange interpolation at the squared head
singular values; constants differ. -/
theorem frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le {t : ℕ}
    (A : Matrix m n 𝕜) (x : n → 𝕜) {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    {Δ : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) (f : ℝ[X]) {a : ℝ}
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ a) :
    frobNorm ((A * aeval (Aᴴ * A) f - A * aeval (Aᴴ * A) f * Z * Zᴴ) *
        blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t *
        pinv (Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)) ^ 2 ≤
      a ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
        ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  classical
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have hd := sq_singularValues_injective A hΔ hpos hgap
  have ha : 0 ≤ a := (abs_nonneg _).trans (htail 0 ⟨le_rfl, sq_nonneg _⟩)
  have hΔ' : 0 ≤ Δ⁻¹ ^ (t - 1) := pow_nonneg (inv_pos.mpr hΔ).le _
  set C := A - A * Z * Zᴴ with hC
  have hCt : specNorm C = singularValues A t := hZ.specNorm_sub_mul_mul_conjTranspose hAZ
  have hcol (i : Fin t) : ‖WithLp.toLp 2 (((A * aeval (Aᴴ * A) f - A * aeval (Aᴴ * A) f * Z * Zᴴ) *
      blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t *
      pinv (Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)).col i)‖ ≤
      ‖(Zᴴ *ᵥ x) i‖⁻¹ * (a * Δ⁻¹ ^ (t - 1)) * ‖WithLp.toLp 2 (C *ᵥ x)‖ := by
    set ℓ := Lagrange.basis Finset.univ (fun i : Fin t => singularValues A i ^ 2) i with hℓ
    have hcol' : ((A * aeval (Aᴴ * A) f - A * aeval (Aᴴ * A) f * Z * Zᴴ) *
        blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t *
        pinv (Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)).col i =
        ((Zᴴ *ᵥ x) i)⁻¹ • (aeval (C * Cᴴ) (f * ℓ) *ᵥ (C *ᵥ x)) := by
      have hN : (blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t *
          pinv (Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)).col i =
          ((Zᴴ *ᵥ x) i)⁻¹ • (aeval (Aᴴ * A) ℓ *ᵥ x) := funext fun b =>
        (blockKrylovMatrix_mul_pinv_apply hH hAZ hd hx b i).trans (mul_comm _ _)
      rw [Matrix.mulVec_mulVec, ← sub_mul_mul_conjTranspose_mul_aeval A hZ hAZ f ℓ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← hN,
        Matrix.mul_assoc _ (blockKrylovMatrix _ _ _) _]
      rfl
    have hq : ∀ y ∈ Set.Icc 0 (specNorm C ^ 2), |(f * ℓ).eval y| ≤ a * Δ⁻¹ ^ (t - 1) := by
      intro y hy
      rw [hCt] at hy
      rw [eval_mul, abs_mul]
      refine mul_le_mul (htail y hy) (abs_eval_basis_le_inv_pow hΔ (fun i j hij => ?_) hy.1
        (fun k => hy.2.trans (pow_le_pow_left₀ (singularValues_nonneg _ _)
          (singularValues_antitone A k.isLt.le) 2)) i) (abs_nonneg _) ha
      rw [← hij]
      exact hgap i (by have := j.isLt; omega)
    rw [hcol', WithLp.toLp_smul, norm_smul, norm_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_toLp_aeval_mul_conjTranspose_self_mulVec_le C (f * ℓ)
      (mul_nonneg ha hΔ') hq _) (inv_nonneg.mpr (norm_nonneg _))
  rw [frobNorm_sq_eq_sum_col, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    (pow_le_pow_left₀ (norm_nonneg _) (hcol i) 2).trans_eq (by ring)

/-- **Randomized block Krylov iteration with a single start vector, spectral norm**: let
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, let $\mathbf{Z} \in \Bbbk^{n \times t}$ be an
orthonormal frame with
$\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$\sigma_i = \sigma_i(\mathbf{A}) > 0$ for $i < t$ and
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$, $\Delta > 0$, and let $\mathbf{x}$
have no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$. For a real polynomial $f$ of
degree less than $d$ with $t + d \le q + 1$, a head index $r \le t$,
$\lvert f(\sigma_i^2) \rvert \ge c > 0$ for $i < r$ and $\lvert f \rvert \le a$ on
$[0, \sigma_t^2]$,
$$\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2 \le \sigma_r^2 +
\Bigl(\frac{a}{c}\Bigr)^2\Delta^{-2(t-1)}
\Bigl(\sum_{i<t}\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}\Bigr)
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$
The exponent $2(t - 1)$ is in $\mathbb{N}$ and sharp for this argument: for $t = 1$ the gap
hypothesis is empty and no power of $\Delta$ appears; for $t = 0$ the bound is
$\|\mathbf{A}\|_2^2$. The gap hypothesis does not separate $\sigma_{t-1}$ from $\sigma_t$, so
the tail is that of the frame $\mathbf{Z}$, which need not be the truncated SVD. The first $r$
columns of $\mathbf{Z}$ are the head frame of the filtered structural bound, and the head block
$\mathbf{Z}^{\mathsf{H}}[\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$ is
a diagonal matrix times a Vandermonde matrix, invertible under the hypotheses.
[MeyerMuscoMusco2023, Theorem 3], there the simulated block of a Gaussian vector is shown, in
probability and for a positive semidefinite matrix, to be a good starting matrix of block Krylov
iteration; here the deterministic bound for a given vector, composed with a polynomial filter;
constants differ.
Result: rbki-single-vector-structural-error -/
theorem specNorm_sub_rbki_replicateCol_sq_le {t : ℕ} (A : Matrix m n 𝕜)
    (x : n → 𝕜) {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    {Δ : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q d r : ℕ} {f : ℝ[X]} (hf : f.degree < d)
    (hd : t + d ≤ q + 1) (hr : r ≤ t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ a) :
    specNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      singularValues A r ^ 2 +
        (a / c) ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  classical
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have hG : cfc (fun y => f.eval y) (Aᴴ * A) = aeval (Aᴴ * A) f := cfc_polynomial f (Aᴴ * A) hH
  obtain ⟨hW, hWZ, hAW⟩ := submatrix_castLE_frame A hZ hAZ hr
  have hΩ : ((blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)ᴴ * Z).rank = Z.rank := by
    rw [hH.rank_conjTranspose_mul_blockKrylovMatrix_replicateCol hAZ
      (sq_singularValues_injective A hΔ hpos hgap) hx, hZ.rank_eq, Fintype.card_fin]
  have h1 := singularValues_sub_rbki_le_of_degree_lt_of_add_le A (Matrix.replicateCol Unit x) hf
    hd 0
  rw [singularValues_zero_eq_specNorm, singularValues_zero_eq_specNorm] at h1
  have h2 := hW.specNorm_sub_rsvd_cfc_sq_le (fun y => f.eval y) hAW hZ hΩ hWZ hc
    fun i => hhead i i.isLt
  rw [hG, hW.specNorm_sub_mul_mul_conjTranspose hAW] at h2
  have h3 := frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le A x hZ hAZ hΔ hpos hgap hx f
    htail
  have hc2 : 0 ≤ c⁻¹ ^ 2 := sq_nonneg _
  calc specNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2
      ≤ specNorm (A - rsvd A (aeval (Aᴴ * A) f *
          blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)) ^ 2 :=
        pow_le_pow_left₀ (specNorm_nonneg _) h1 2
    _ ≤ _ := h2
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm _) 2).trans h3) hc2)
    _ = _ := by ring

/-- **Randomized block Krylov iteration with a single start vector, Frobenius norm**: let
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, let $\mathbf{Z} \in \Bbbk^{n \times t}$ be an
orthonormal frame with
$\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$\sigma_i = \sigma_i(\mathbf{A}) > 0$ for $i < t$ and
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$, $\Delta > 0$, and let $\mathbf{x}$
have no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$. For a real polynomial $f$ of
degree less than $d$ with $t + d \le q + 1$, a head index $r \le t$,
$\lvert f(\sigma_i^2) \rvert \ge c > 0$ for $i < r$ and $\lvert f \rvert \le a$ on
$[0, \sigma_t^2]$,
$$\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
\Bigl(\frac{a}{c}\Bigr)^2\Delta^{-2(t-1)}
\Bigl(\sum_{i<t}\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}\Bigr)
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$
The exponent $2(t - 1)$ is in $\mathbb{N}$. The head frame of the filtered structural bound is
the first $r$ columns $\mathbf{W}$ of $\mathbf{Z}$; when $\sigma_{r-1} = \sigma_r$ (possible only
for $r = t$) the matrix $\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}$ need not be
$\llbracket\mathbf{A}\rrbracket_r$, but the two have the same Frobenius error.
[MeyerMuscoMusco2023, Theorem 3], there the simulated block of a Gaussian vector is shown, in
probability and for a positive semidefinite matrix, to be a good starting matrix of block Krylov
iteration; here the deterministic bound for a given vector, composed with a polynomial filter;
constants differ.
Result: rbki-single-vector-structural-error -/
theorem frobNorm_sub_rbki_replicateCol_sq_le {t : ℕ} (A : Matrix m n 𝕜)
    (x : n → 𝕜) {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    {Δ : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q d r : ℕ} {f : ℝ[X]} (hf : f.degree < d)
    (hd : t + d ≤ q + 1) (hr : r ≤ t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ a) :
    frobNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        (a / c) ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  classical
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have hG : cfc (fun y => f.eval y) (Aᴴ * A) = aeval (Aᴴ * A) f := cfc_polynomial f (Aᴴ * A) hH
  obtain ⟨hW, hWZ, hAW⟩ := submatrix_castLE_frame A hZ hAZ hr
  have hΩ : ((blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)ᴴ * Z).rank = Z.rank := by
    rw [hH.rank_conjTranspose_mul_blockKrylovMatrix_replicateCol hAZ
      (sq_singularValues_injective A hΔ hpos hgap) hx, hZ.rank_eq, Fintype.card_fin]
  have h1 : frobNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      frobNorm (A - rsvd A (aeval (Aᴴ * A) f *
        blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)) ^ 2 := by
    rw [frobNorm_sq_eq_sum_singularValues_sq, frobNorm_sq_eq_sum_singularValues_sq]
    exact Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (singularValues_nonneg _ _)
      (singularValues_sub_rbki_le_of_degree_lt_of_add_le A (Matrix.replicateCol Unit x) hf hd k) 2
  have h2 := hW.frobNorm_sub_rsvd_cfc_sq_le (fun y => f.eval y) hAW hZ hΩ hWZ hc
    fun i => hhead i i.isLt
  rw [hG, hW.frobNorm_sub_mul_mul_conjTranspose_sq_eq_truncatedSVD hAW] at h2
  have h3 := frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le A x hZ hAZ hΔ hpos hgap hx f
    htail
  have hc2 : 0 ≤ c⁻¹ ^ 2 := sq_nonneg _
  calc frobNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2
      ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 hc2)
    _ = _ := by ring

/-- **Randomized block Krylov iteration with a single start vector is exact at the rank**: let
$\mathbf{A}$ have rank at most $t$, let $\mathbf{Z} \in \Bbbk^{n \times t}$ be an orthonormal
frame with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$\sigma_i = \sigma_i(\mathbf{A})$, with $\sigma_0 > \sigma_1 > \dots > \sigma_{t-1}$, and let
$\mathbf{x}$ have no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$. Then for every
$q \ge t$,
$$\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q) = \mathbf{A}\,.$$
This is the case the gapped single-vector bound excludes by asking for positive head singular
values: there $\mathbf{A}$ vanishes on the complement of the frame, and the Krylov space of depth
$t$ already contains the range of $\mathbf{Z}$. Distinctness and the nonvanishing coordinates
cannot be dropped: the Krylov space of one vector has dimension at most the number of distinct
eigenvalues it meets.
No printed source.
Result: rbki-single-vector-structural-error -/
theorem rbki_replicateCol_eq_self {t : ℕ} (A : Matrix m n 𝕜)
    (x : n → 𝕜) {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z =
      Z * Matrix.diagonal fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    (hrank : A.rank ≤ t)
    (hlt : ∀ i j, i < j → j < t → singularValues A j < singularValues A i)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q : ℕ} (hq : t ≤ q) :
    rbki A (Matrix.replicateCol Unit x) q = A := by
  classical
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have hd : Function.Injective fun i : Fin t => singularValues A i ^ 2 := by
    intro i j hij
    have h := (sq_eq_sq₀ (singularValues_nonneg _ _) (singularValues_nonneg _ _)).mp hij
    rcases lt_trichotomy i j with hlt' | heq | hgt
    · exact absurd h (hlt i j hlt' j.isLt).ne'
    · exact heq
    · exact absurd h (hlt j i hgt i.isLt).ne
  have hA : A = A * Z * Zᴴ := by
    refine sub_eq_zero.mp (singularValues_eq_zero.mp (funext fun i => ?_))
    rw [hZ.singularValues_sub_mul_mul_conjTranspose hAZ]
    exact (singularValues_eq_zero_iff A).mpr (hrank.trans (Nat.le_add_right t i))
  have hdet : IsUnit (Matrix.diagonal (Zᴴ *ᵥ x) *
      Matrix.vandermonde fun i : Fin t => ((singularValues A i ^ 2 : ℝ) : 𝕜)).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hx i)
      (Matrix.det_vandermonde_ne_zero_iff.mpr (RCLike.ofReal_injective.comp hd))
  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin t × Unit) (Fin t) 𝕜,
      Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t * R = 1 := by
    refine ⟨((Matrix.diagonal (Zᴴ *ᵥ x) * Matrix.vandermonde fun i : Fin t =>
      ((singularValues A i ^ 2 : ℝ) : 𝕜))⁻¹).submatrix Prod.fst id, ?_⟩
    rw [hH.conjTranspose_mul_blockKrylovMatrix_replicateCol hAZ x]
    refine (Matrix.submatrix_mul_equiv _ _ id (Equiv.prodPUnit (Fin t)) id).trans ?_
    rw [Matrix.mul_nonsing_inv _ hdet, Matrix.submatrix_id_id]
  have ht : rbki A (Matrix.replicateCol Unit x) t = A := by
    rw [rbki_def, rsvd]
    refine rangeProjector_mul_eq_self_iff.mpr (range_le_iff_exists_mul.mpr ⟨R * Zᴴ, ?_⟩)
    calc A = A * Z * (Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t * R) *
          Zᴴ := by rw [hR, Matrix.mul_one, ← hA]
      _ = A * Z * Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t * (R * Zᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = A * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t * (R * Zᴴ) := by
          rw [← hA]
  have h0 : A - rbki A (Matrix.replicateCol Unit x) q = 0 :=
    singularValues_eq_zero.mp (funext fun i => le_antisymm (by
      have h := singularValues_sub_rbki_le_of_le A (Matrix.replicateCol Unit x) hq i
      rwa [ht, sub_self, singularValues_zero] at h) (singularValues_nonneg _ _))
  exact (sub_eq_zero.mp h0).symm

end NLAlib
