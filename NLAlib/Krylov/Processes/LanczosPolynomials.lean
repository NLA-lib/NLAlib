/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Compression
public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Orthogonal.Recurrence

/-!
# The Lanczos polynomials

For Hermitian $\mathbf{A}$ the Lanczos method from $\mathbf{b}$ computes the orthogonal
polynomials of the spectral measure $\mu_{\mathbf{A},\mathbf{b}}$: column $j$ of the canonical
Lanczos basis is $\pi_j(\mathbf{A})\mathbf{b}/\|\pi_j(\mathbf{A})\mathbf{b}\|$, the Lanczos
coefficients are $\alpha_j(\mu_{\mathbf{A},\mathbf{b}})$ and
$\sqrt{\beta_{j+1}(\mu_{\mathbf{A},\mathbf{b}})}$, and the Lanczos tridiagonal matrix is the Jacobi
matrix of $\mu_{\mathbf{A},\mathbf{b}}$, for every number of steps (past the grade both sides are
padded with the same zeros). The spectral measure is positive definite up to degree $k$ exactly
when $k$ is at most the grade.
[GolubMeurant2010]; [Gautschi2004].

## Main results

* `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff`: definiteness is the grade.
* `Matrix.IsHermitian.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec`: the Lanczos
  vectors.
* `Matrix.IsHermitian.lanczosAlpha_lanczosState`, `Matrix.IsHermitian.lanczosState_beta`: the
  Lanczos coefficients.
* `Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix`: the tridiagonal is the Jacobi matrix.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Definiteness of the spectral measure is the grade: for Hermitian $\mathbf{A}$, every
$\mathbf{b}$ and every $k$, $\mu_{\mathbf{A},\mathbf{b}}$ is positive definite on the polynomials
of degree less than $k$ exactly when $k \le \nu$, $\nu$ the grade of $\mathbf{b}$. -/
theorem _root_.Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (k : ℕ) :
    IsMomentPosDef (spectralMeasure A b) k ↔ k ≤ krylovGrade A b := by
  constructor
  · -- past the grade the Ritz polynomial of $\mathcal{K}_\nu$ annihilates $\mathbf{b}$
    intro h
    by_contra! hν
    obtain ⟨r, Q, hQ, hK⟩ :=
      exists_hasOrthonormalCols_range_eq_krylovSpace A b (krylovGrade A b + 1)
    have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
    have hr : Fintype.card (Fin r) = krylovGrade A b := by
      have h1 : Fintype.card (Fin r) = min (krylovGrade A b + 1) (krylovGrade A b) := by
        rw [← hQ.rank_eq, ← finrank_krylovSpace, ← hK]
        rfl
      rw [h1, Nat.min_eq_right (Nat.le_succ _)]
    -- the Ritz values, at most $\nu$ of them
    set s : Finset ℝ := Finset.image hT.eigenvalues Finset.univ with hsdef
    have hcard : s.card ≤ krylovGrade A b :=
      Finset.card_image_le.trans (by rw [Finset.card_univ, hr])
    have hs : spectrum ℝ (Qᴴ * A * Q) ⊆ (s : Set ℝ) := by
      rw [hT.spectrum_real_eq_range_eigenvalues]
      exact fun x ⟨i, hi⟩ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
    have hdeg : (Lagrange.nodal s id).degree < krylovGrade A b + 1 := by
      rw [Lagrange.degree_nodal]
      exact_mod_cast Nat.lt_succ_of_le hcard
    have hzero : aeval A (Lagrange.nodal s id) *ᵥ b = 0 := by
      rw [← hQ.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq hK hdeg,
        hT.aeval_nodal_eq_zero hs, Matrix.zero_mulVec, Matrix.mulVec_zero]
    refine (h (Lagrange.nodal s id) Lagrange.nodal_monic.ne_zero
      (hdeg.trans_le (by exact_mod_cast Nat.succ_le_of_lt hν))).ne' ?_
    rw [← hA.norm_aeval_mulVec_sq b (Lagrange.nodal s id), hzero, WithLp.toLp_zero, norm_zero,
      zero_pow two_ne_zero]
  · -- below the grade no nonzero polynomial of small degree annihilates $\mathbf{b}$
    intro hk p hp0 hp
    rw [← hA.norm_aeval_mulVec_sq b p]
    exact pow_pos (norm_pos_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr
      (aeval_mulVec_ne_zero_of_degree_lt_krylovGrade hp0
        (hp.trans_le (by exact_mod_cast hk))))) 2

/-- $\pi_j(\mathbf{A})\mathbf{b}$ differs from $\mathbf{A}^j\mathbf{b}$ by a Krylov vector: for
every measure $\mu$ on $\mathbb{R}$, every square $\mathbf{A}$, $\mathbf{b}$ and $j$,
$\pi_j(\mathbf{A})\mathbf{b} - \mathbf{A}^j\mathbf{b} \in \mathcal{K}_j(\mathbf{A}, \mathbf{b})$,
$\pi_j$ the monic orthogonal polynomial of degree $j$ of $\mu$. -/
theorem aeval_orthogonalPolynomial_mulVec_sub_pow_mulVec_mem_krylovSpace (μ : Measure ℝ)
    (A : Matrix n n 𝕜) (b : n → 𝕜) (j : ℕ) :
    aeval A (orthogonalPolynomial μ j) *ᵥ b - A ^ j *ᵥ b ∈ krylovSpace A b j := by
  have h : aeval A (orthogonalPolynomial μ j - (X : ℝ[X]) ^ j) *ᵥ b ∈ krylovSpace A b j := by
    refine aeval_mulVec_mem_krylovSpace A b ?_
    have hdeg : (orthogonalPolynomial μ j - (X : ℝ[X]) ^ j).degree <
        (orthogonalPolynomial μ j).degree :=
      degree_sub_lt_left (by rw [degree_orthogonalPolynomial, degree_X_pow])
        (monic_orthogonalPolynomial μ j).ne_zero
        (by rw [(monic_orthogonalPolynomial μ j).leadingCoeff, Polynomial.leadingCoeff_X_pow])
    rwa [degree_orthogonalPolynomial] at hdeg
  rwa [map_sub, Matrix.sub_mulVec, aeval_X_pow] at h

/-- $\pi_j(\mathbf{A})\mathbf{b}$ is orthogonal to the Krylov space: for Hermitian $\mathbf{A}$,
every $\mathbf{b}$, $j$ and $\mathbf{x} \in \mathcal{K}_j(\mathbf{A}, \mathbf{b})$,
$\langle\mathbf{x}, \pi_j(\mathbf{A})\mathbf{b}\rangle = 0$, $\pi_j$ the monic orthogonal
polynomial of degree $j$ of $\mu_{\mathbf{A},\mathbf{b}}$. -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_aeval_orthogonalPolynomial_mulVec_eq_zero_of_mem
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b x : n → 𝕜} {j : ℕ}
    (hx : x ∈ krylovSpace A b j) :
    star x ⬝ᵥ (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) = 0 := by
  have key : ∀ i : ℕ, i < j →
      star (A ^ i *ᵥ b) ⬝ᵥ (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) = 0 := by
    intro i hi
    have hX : A ^ i *ᵥ b = aeval A (X ^ i : ℝ[X]) *ᵥ b := by rw [map_pow, aeval_X]
    rw [hX, hA.star_aeval_mulVec_dotProduct_aeval_mulVec]
    obtain ⟨a, a', hμ⟩ := exists_ae_mem_Icc_spectralMeasure A b
    have hortho := isOrthogonalPolynomial_orthogonalPolynomial hμ j (X ^ i)
      (by rw [degree_X_pow]; exact_mod_cast hi)
    simp only [mul_comm, hortho, RCLike.ofReal_zero]
  rw [krylovSpace_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨⟨i, hi⟩, rfl⟩ := hy; exact key i hi
  | zero => simp
  | add y z _ _ hy hz => rw [star_add, add_dotProduct, hy, hz, add_zero]
  | smul c y _ hy => rw [star_smul, smul_dotProduct, hy, smul_zero]

/-- From the grade on, $\pi_j(\mathbf{A})\mathbf{b}$ vanishes: for Hermitian $\mathbf{A}$, every
$\mathbf{b}$ and $j \ge \nu$, $\nu$ the grade of $\mathbf{b}$, $\pi_j(\mathbf{A})\mathbf{b} =
\mathbf{0}$, $\pi_j$ the monic orthogonal polynomial of degree $j$ of
$\mu_{\mathbf{A},\mathbf{b}}$. -/
theorem _root_.Matrix.IsHermitian.aeval_orthogonalPolynomial_mulVec_eq_zero_of_krylovGrade_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {j : ℕ} (hj : krylovGrade A b ≤ j) :
    aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b = 0 := by
  obtain ⟨a, a', hmem⟩ := exists_ae_mem_Icc_spectralMeasure A b
  have hnot : ¬ IsMomentPosDef (spectralMeasure A b) (j + 1) := by
    rw [hA.isMomentPosDef_spectralMeasure_iff]
    omega
  rw [isMomentPosDef_succ_iff hmem j, not_lt, ← hA.norm_aeval_mulVec_sq b] at hnot
  have h0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hnot (sq_nonneg _)))
  simpa using congrArg WithLp.ofLp h0

/-- The last Lanczos vector below the grade: for Hermitian $\mathbf{A}$ and $j < \nu$, the last
column of the canonical Lanczos basis with $j + 1$ columns is
$\pi_j(\mathbf{A})\mathbf{b}/\|\pi_j(\mathbf{A})\mathbf{b}\|$. -/
private theorem arnoldiMatrix_col_last_eq_of_lt_krylovGrade {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : n → 𝕜} {j : ℕ} (hj : j < krylovGrade A b) :
    (arnoldiMatrix A b (j + 1)).col (Fin.last j) =
      (‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)‖⁻¹ : 𝕜) •
        (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) := by
  obtain ⟨y, hy, hjy⟩ := exists_gramSchmidtR_smul_arnoldiMatrix_col_last A b j
  obtain ⟨ρ, hρ0, hρ⟩ := RCLike.nonneg_iff_exists_ofReal.mp
    (gramSchmidtR_apply_self_nonneg (krylovMatrix A b (j + 1)) (Fin.last j))
  have hρne : ρ ≠ 0 := fun h0 =>
    (not_le.mpr hj) (gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff.mp
      (by rw [← hρ, h0, RCLike.ofReal_zero]))
  rw [← hρ] at hjy
  have hK := aeval_orthogonalPolynomial_mulVec_sub_pow_mulVec_mem_krylovSpace
    (spectralMeasure A b) A b j
  -- the difference $\rho\mathbf{q}_j - \pi_j(\mathbf{A})\mathbf{b}$ lies in $\mathcal{K}_j$
  have hd : (ρ : 𝕜) • (arnoldiMatrix A b (j + 1)).col (Fin.last j) -
      aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b ∈ krylovSpace A b j := by
    have e : (ρ : 𝕜) • (arnoldiMatrix A b (j + 1)).col (Fin.last j) -
        aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b =
        -(y + (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b - A ^ j *ᵥ b)) := by
      rw [hjy]; abel
    rw [e]; exact Submodule.neg_mem _ (Submodule.add_mem _ hy hK)
  -- so it is orthogonal to itself, hence zero
  have h1 := hA.star_dotProduct_aeval_orthogonalPolynomial_mulVec_eq_zero_of_mem (b := b) hd
  have h2 := star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem A b le_rfl hd
  have h3 : star ((ρ : 𝕜) • (arnoldiMatrix A b (j + 1)).col (Fin.last j) -
      aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) ⬝ᵥ
      (arnoldiMatrix A b (j + 1)).col (Fin.last j) = 0 := by
    have := congrArg star h2
    rwa [Matrix.star_dotProduct, star_star, star_zero] at this
  have h4 : star ((ρ : 𝕜) • (arnoldiMatrix A b (j + 1)).col (Fin.last j) -
      aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) ⬝ᵥ
      ((ρ : 𝕜) • (arnoldiMatrix A b (j + 1)).col (Fin.last j) -
      aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) = 0 := by
    rw [dotProduct_sub, h1, dotProduct_smul, h3, smul_zero, sub_zero]
  have hv : (ρ : 𝕜) • (arnoldiMatrix A b (j + 1)).col (Fin.last j) =
      aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b :=
    sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp h4)
  -- normalise
  rw [← hv, WithLp.toLp_smul, norm_smul, norm_arnoldiMatrix_col_last hj, mul_one,
    RCLike.norm_ofReal, abs_of_nonneg hρ0, smul_smul, ← RCLike.ofReal_inv, ← RCLike.ofReal_mul,
    inv_mul_cancel₀ hρne, RCLike.ofReal_one, one_smul]

/-- **The Lanczos vectors are the orthogonal polynomials of the spectral measure**: for
Hermitian $\mathbf{A}$, every $q$ and $j < q$, column $j$ of the canonical Lanczos basis
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$ is
$\pi_j(\mathbf{A})\mathbf{b}/\|\pi_j(\mathbf{A})\mathbf{b}\|$, $\pi_j$ the monic orthogonal
polynomial of degree $j$ of $\mu_{\mathbf{A},\mathbf{b}}$; from the grade on both sides are
$\mathbf{0}$. [GolubMeurant2010, Theorems 4.1–4.2].
Result: lanczos-orthogonal-polynomials -/
theorem _root_.Matrix.IsHermitian.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} (j : Fin q) :
    (arnoldiMatrix A b q).col j =
      (‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)‖⁻¹ : 𝕜) •
        (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) := by
  rw [arnoldiMatrix_col_eq_col_last A b j]
  rcases lt_or_ge (j : ℕ) (krylovGrade A b) with h | h
  · exact arnoldiMatrix_col_last_eq_of_lt_krylovGrade hA h
  · rw [arnoldiMatrix_col_last_eq_zero_iff.mpr h,
      Matrix.IsHermitian.aeval_orthogonalPolynomial_mulVec_eq_zero_of_krylovGrade_le hA h,
      smul_zero]

/-- The diagonal Lanczos coefficient is the recurrence coefficient of the spectral measure: for
Hermitian $\mathbf{A}$, every $\mathbf{b}$ and $j$, the coefficient $\alpha_j$ computed by the
Lanczos recurrence from $\mathbf{b}$ is $\alpha_j(\mu_{\mathbf{A},\mathbf{b}})$. -/
theorem _root_.Matrix.IsHermitian.lanczosAlpha_lanczosState {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    lanczosAlpha A (lanczosState A b j) = jacobiAlpha (spectralMeasure A b) j := by
  set π := orthogonalPolynomial (spectralMeasure A b) j with hπ
  have hnorm := hA.norm_aeval_mulVec_sq b π
  have hdot := hA.star_aeval_mulVec_dotProduct_aeval_mulVec b π (X * π)
  have hentry := congrFun (congrFun (hA.lanczosTridiagonal_eq b (j + 1)) (Fin.last j)) (Fin.last j)
  rw [Matrix.mul_assoc, conjTranspose_mul_apply,
    hA.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec b (Fin.last j)] at hentry
  simp only [lanczosTridiagonal, Matrix.of_apply, if_true] at hentry
  rw [show (A * arnoldiMatrix A b (j + 1)).col (Fin.last j)
      = A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j) from rfl,
    hA.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec b (Fin.last j)] at hentry
  simp only [Fin.val_last, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul] at hentry
  rw [map_mul, aeval_X, ← Matrix.mulVec_mulVec] at hdot
  have hx : ∫ x, π.eval x * (X * π).eval x ∂spectralMeasure A b
      = ∫ x, x * π.eval x ^ 2 ∂spectralMeasure A b := by
    congr 1; ext x; simp only [eval_mul, eval_X]; ring
  rw [hx] at hdot
  rw [← hπ] at hentry
  rw [jacobiAlpha, ← hπ, ← hnorm]
  generalize aeval A π *ᵥ b = v at *
  generalize ‖WithLp.toLp 2 v‖ = N at *
  rw [hdot] at hentry
  apply RCLike.ofReal_inj (K := 𝕜) |>.mp
  rw [hentry, RCLike.ofReal_div, RCLike.ofReal_pow]
  simp only [RCLike.star_def, map_inv₀, RCLike.conj_ofReal]
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · have : (N : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hN
    field_simp

/-- The off-diagonal Lanczos coefficient is the square root of the recurrence coefficient of the
spectral measure: for Hermitian $\mathbf{A}$, every $\mathbf{b}$ and $j$, the coefficient
$\beta_{j+1}$ computed by the Lanczos recurrence from $\mathbf{b}$ is
$\sqrt{\beta_{j+1}(\mu_{\mathbf{A},\mathbf{b}})}$ (Gautschi's $\beta$, the ratio of squared
norms). -/
theorem _root_.Matrix.IsHermitian.lanczosState_beta {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosState A b (j + 1)).beta = √(jacobiBeta (spectralMeasure A b) (j + 1)) := by
  obtain ⟨a, a', hμ⟩ := exists_ae_mem_Icc_spectralMeasure A b
  have hT := congrFun (congrFun (hA.lanczosTridiagonal_eq b (j + 2)) ⟨j + 1, by omega⟩)
    ⟨j, by omega⟩
  have h1 := hA.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec b
    (⟨j + 1, by omega⟩ : Fin (j + 2))
  have h0 := hA.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec b
    (⟨j, by omega⟩ : Fin (j + 2))
  have hAP : A *ᵥ (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) =
      aeval A (X * orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b := by
    rw [aeval_mul, aeval_X, Matrix.mulVec_mulVec]
  have hint : star (aeval A (orthogonalPolynomial (spectralMeasure A b) (j + 1)) *ᵥ b) ⬝ᵥ
      (aeval A (X * orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) =
      ((∫ x, (orthogonalPolynomial (spectralMeasure A b) (j + 1)).eval x ^ 2
        ∂spectralMeasure A b : ℝ) : 𝕜) := by
    rw [hA.star_aeval_mulVec_dotProduct_aeval_mulVec,
      ← integral_mul_orthogonalPolynomial_mul_orthogonalPolynomial_succ hμ j]
    congr 2
    funext x
    simp only [eval_mul, eval_X]
    ring
  have hβ : ((lanczosState A b (j + 1)).beta : 𝕜) =
      star ((arnoldiMatrix A b (j + 2)).col ⟨j + 1, by omega⟩) ⬝ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 2)).col ⟨j, by omega⟩) := by
    simp only [lanczosTridiagonal, Fin.ext_iff, Matrix.of_apply, Nat.add_eq_left, one_ne_zero,
      ↓reduceIte] at hT
    rw [Matrix.mul_assoc, conjTranspose_mul_apply] at hT
    exact hT
  rw [h1, h0] at hβ
  have hβ' : (lanczosState A b (j + 1)).beta =
      ‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) (j + 1)) *ᵥ b)‖⁻¹ *
        ‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)‖⁻¹ *
        ∫ x, (orthogonalPolynomial (spectralMeasure A b) (j + 1)).eval x ^ 2
          ∂spectralMeasure A b := by
    simp only [star_smul, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, hAP, hint,
      smul_eq_mul, star_inv₀, RCLike.star_def, RCLike.conj_ofReal] at hβ
    apply RCLike.ofReal_injective (K := 𝕜)
    rw [hβ]
    push_cast
    ring
  have hn1 := hA.norm_aeval_mulVec_sq b (orthogonalPolynomial (spectralMeasure A b) (j + 1))
  have hn0 := hA.norm_aeval_mulVec_sq b (orthogonalPolynomial (spectralMeasure A b) j)
  have alg : ∀ x y : ℝ, x⁻¹ * y⁻¹ * x ^ 2 = x / y := fun x y => by
    rw [sq, mul_right_comm, ← mul_assoc, inv_mul_mul_self, div_eq_mul_inv]
  simp only [jacobiBeta]
  rw [hβ', ← hn1, ← hn0, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _), alg]

/-- **The Lanczos tridiagonal is the Jacobi matrix of the spectral measure**: for Hermitian
$\mathbf{A}$ and every $q$, the tridiagonal matrix of $q$ steps of the Lanczos recurrence from
$\mathbf{b}$ is $\mathbf{J}_q(\mu_{\mathbf{A},\mathbf{b}})$; past the grade both are padded with
the same zeros. [GolubMeurant2010, Theorems 4.1–4.2]; [Gautschi2004, Theorem 1.31, §1.3.2].
Result: lanczos-jacobi-matrix -/
theorem _root_.Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosTridiagonal A b q = (jacobiMatrix (spectralMeasure A b) q).map (algebraMap ℝ 𝕜) := by
  ext i j
  simp only [lanczosTridiagonal, jacobiMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · subst h1
    rw [Matrix.IsHermitian.lanczosAlpha_lanczosState hA b i, RCLike.algebraMap_eq_ofReal]
  · rw [h2, Matrix.IsHermitian.lanczosState_beta hA b j, RCLike.algebraMap_eq_ofReal]
  · rw [h3, Matrix.IsHermitian.lanczosState_beta hA b i, RCLike.algebraMap_eq_ofReal]
  · simp

end NLAlib
