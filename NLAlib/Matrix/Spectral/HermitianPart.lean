/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import NLAlib.Matrix.Spectral.EigenvectorPairing
public import NLAlib.Matrix.Spectral.Schur
public import NLAlib.Matrix.Majorization.Schur
public import NLAlib.Matrix.Inequalities.SchurHorn

/-!
# The Hermitian part and the real parts of the eigenvalues

The Hermitian part of a square matrix is `NLAlib.hermitianPart A`,
$\tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$, Mathlib's `selfAdjointPart ℝ A` as a matrix.
The real parts of the eigenvalues of a complex matrix are majorized by the eigenvalues of its
Hermitian part (Ky Fan), so they lie between its extreme eigenvalues (Bendixson).

## Main definitions

* `NLAlib.hermitianPart`: $\tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$, with the real
  scalar $2^{-1}$.

## Main results

* `NLAlib.majorized_re_of_isEigenvalueListing`: Ky Fan's majorization.
* `NLAlib.majorized_re_iff_exists_isEigenvalueListing_hermitianPart`: majorization is the exact
  compatibility condition for a prescribed complex spectrum and Hermitian-part spectrum.
* `NLAlib.re_le_eigenvalue_zero_hermitianPart`, `NLAlib.eigenvalue_hermitianPart_le_re`:
  Bendixson's bounds.
* `Matrix.PosDef.det_ne_zero_of_hermitianPart`: a matrix with positive definite Hermitian part is
  invertible.
* `NLAlib.quadForm_hermitianPart`, `NLAlib.trace_conjTranspose_mul_hermitianPart_mul`: over
  $\mathbb{R}$, quadratic forms and traces of compressions see only the symmetric part.
* `Matrix.IsHermitian.frobNorm_sub_sq`: orthogonal decomposition of the error to a Hermitian
  matrix into its skew-Hermitian and Hermitian components.
* `Matrix.IsHermitian.frobNorm_sub_eq_frobNorm_sub_hermitianPart_iff`: uniqueness of the
  nearest Hermitian matrix in Frobenius norm.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-- The **Hermitian part** of a square matrix, $\tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$.
[HornJohnson2013, §4.1.2]. -/
noncomputable def hermitianPart (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (2⁻¹ : ℝ) • (A + Aᴴ)

/-- The Hermitian part is Mathlib's `selfAdjointPart`. -/
theorem hermitianPart_eq_selfAdjointPart (A : Matrix n n 𝕜) :
    hermitianPart A = (selfAdjointPart ℝ A : Matrix n n 𝕜) := by
  rw [selfAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose, hermitianPart]

/-- The Hermitian part is Hermitian. -/
theorem isHermitian_hermitianPart (A : Matrix n n 𝕜) : (hermitianPart A).IsHermitian := by
  rw [Matrix.IsHermitian, hermitianPart, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

/-- A Hermitian matrix is its own Hermitian part. -/
theorem _root_.Matrix.IsHermitian.hermitianPart_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hermitianPart A = A := by
  rw [hermitianPart, hA.eq, ← two_smul ℝ A, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- Taking the Hermitian part commutes with subtraction. This transports the norm contraction
to differences of two matrices. -/
theorem hermitianPart_sub (A B : Matrix n n 𝕜) :
    hermitianPart (A - B) = hermitianPart A - hermitianPart B := by
  simp only [hermitianPart, Matrix.conjTranspose_sub, smul_sub, smul_add]
  abel

variable [Fintype n]

/-- A Hermitian matrix is Frobenius-orthogonal to the skew-Hermitian part of any matrix.
Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`frobInner_eq_zero_of_skewHermitian_of_isHermitian`, for the canonical decomposition. -/
theorem _root_.Matrix.IsHermitian.frobInner_sub_hermitianPart {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) (A : Matrix n n 𝕜) :
    frobInner (A - hermitianPart A) X = 0 := by
  have h := frobInner_conjTranspose A X
  rw [hX.eq] at h
  rw [frobInner_sub_left, hermitianPart, frobInner_smul_left, frobInner_add_left, h]
  ring

/-- For any matrix $\mathbf{A}$ and Hermitian $\mathbf{X}$, with
$\mathbf{H}=(\mathbf{A}+\mathbf{A}^{\mathsf{H}})/2$, the squared error splits orthogonally:
$$\|\mathbf{A}-\mathbf{X}\|_{\mathsf{F}}^2 =
\|\mathbf{A}-\mathbf{H}\|_{\mathsf{F}}^2 + \|\mathbf{H}-\mathbf{X}\|_{\mathsf{F}}^2\,.$$
[Higham1988, proof of Theorem 2.1]; generalized from real matrices to either scalar field.
This identity gives nearest-Hermitian approximation and its error certificate. -/
theorem _root_.Matrix.IsHermitian.frobNorm_sub_sq {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) (A : Matrix n n 𝕜) :
    frobNorm (A - X) ^ 2 = frobNorm (A - hermitianPart A) ^ 2 +
      frobNorm (hermitianPart A - X) ^ 2 := by
  have horth := ((isHermitian_hermitianPart A).sub hX).frobInner_sub_hermitianPart A
  rw [show A - X = (A - hermitianPart A) + (hermitianPart A - X) by abel,
    frobNorm_add_sq_of_frobInner_eq_zero horth]

/-- For any matrix $\mathbf{A}$ and Hermitian $\mathbf{X}$, the Frobenius distance to
$\mathbf{X}$ equals that to $\mathbf{H}=(\mathbf{A}+\mathbf{A}^{\mathsf{H}})/2$ exactly when
$\mathbf{X}=\mathbf{H}$. Thus the Hermitian-part approximation has a unique minimizer.
[Higham1988, proof of Theorem 2.1]; generalized from real matrices to either scalar field. -/
theorem _root_.Matrix.IsHermitian.frobNorm_sub_eq_frobNorm_sub_hermitianPart_iff
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (A : Matrix n n 𝕜) :
    frobNorm (A - X) = frobNorm (A - hermitianPart A) ↔ X = hermitianPart A := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have he := hX.frobNorm_sub_sq A
  rw [h] at he
  have hz : frobNorm (hermitianPart A - X) = 0 := by nlinarith
  exact (sub_eq_zero.mp (frobNorm_eq_zero_iff.mp hz)).symm

/-- The Hermitian part does not increase the Frobenius norm:
$$\|\tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})\|_{\mathsf{F}} \le
\|\mathbf{A}\|_{\mathsf{F}}\,,$$
by the triangle inequality and $\|\mathbf{A}^{\mathsf{H}}\|_{\mathsf{F}} =
\|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem frobNorm_hermitianPart_le (A : Matrix n n 𝕜) : frobNorm (hermitianPart A) ≤ frobNorm A := by
  rw [hermitianPart, frobNorm_real_smul]
  have h := frobNorm_add_le A Aᴴ
  rw [frobNorm_conjTranspose] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  linarith

/-- The quadratic form of the Hermitian part is the real part of the quadratic form:
$\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{H}\mathbf{x}) =
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$ for
$\mathbf{H} = \tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$. -/
theorem re_quadForm_hermitianPart (A : Matrix n n 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm (hermitianPart A) x) = RCLike.re (quadForm A x) := by
  rw [hermitianPart, RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left,
    quadForm_add_left, ← star_quadForm, RCLike.re_ofReal_mul, map_add, RCLike.star_def,
    RCLike.conj_re]
  ring

/-- Over $\mathbb{R}$ a quadratic form sees only the symmetric part:
$\mathbf{x}^{\mathsf{T}}\mathbf{H}\mathbf{x} = \mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x}$ for
$\mathbf{H} = \tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{T}})$. The real case of
`NLAlib.re_quadForm_hermitianPart`; it turns a statement about symmetric matrices into one about
all real matrices. -/
theorem quadForm_hermitianPart (A : Matrix n n ℝ) (x : n → ℝ) :
    quadForm (hermitianPart A) x = quadForm A x := by
  simpa only [RCLike.re_to_real] using re_quadForm_hermitianPart A x

/-- The trace of the Hermitian part is the real part of the trace:
$\operatorname{tr} \tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}}) =
\operatorname{Re} \operatorname{tr} \mathbf{A}$. Over $\mathbb{R}$ it says that the trace sees
only the symmetric part (`simpa using trace_hermitianPart A`). -/
theorem trace_hermitianPart (A : Matrix n n 𝕜) :
    (hermitianPart A).trace = ((RCLike.re A.trace : ℝ) : 𝕜) := by
  rw [hermitianPart, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, RCLike.star_def, RCLike.add_conj]
  push_cast
  ring

open scoped MatrixOrder in
/-- A contraction from a field-of-values bound: if the Hermitian part of $\mathbf{A}$
satisfies $a\mathbf{I} \preceq \tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$ with
$a \ge 0$, and $\|\mathbf{A}\|_2 \le a'$, then with $\alpha = a/a'^2$
$$\|\mathbf{I} - \alpha\mathbf{A}\|_2 \le \sqrt{1 - (a/a')^2}\,.$$
The one-step bound of Elman's GMRES estimate; for $a' = 0$ the step is $\alpha = 0$. -/
theorem specNorm_one_sub_smul_le_of_smul_one_le_hermitianPart [DecidableEq n]
    {A : Matrix n n 𝕜} {a a' : ℝ} (ha : 0 ≤ a) (hH : a • (1 : Matrix n n 𝕜) ≤ hermitianPart A)
    (hA : specNorm A ≤ a') : specNorm (1 - (a / a' ^ 2) • A) ≤ √(1 - (a / a') ^ 2) := by
  rcases eq_or_ne a' 0 with rfl | ha'
  · simpa using (specNorm_one_le (𝕜 := 𝕜) (n := n))
  set α : ℝ := a / a' ^ 2 with hα
  have hα0 : 0 ≤ α := by positivity
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) α A]
  refine (specNorm_le_iff (Real.sqrt_nonneg _)).2 fun v => ?_
  have hq : a * ‖WithLp.toLp 2 v‖ ^ 2 ≤ RCLike.re (quadForm A v) := by
    have h := re_quadForm_le_re_quadForm_of_le hH v
    rwa [re_quadForm_real_smul_one, re_quadForm_hermitianPart] at h
  have hAv : ‖WithLp.toLp 2 (A *ᵥ v)‖ ≤ a' * ‖WithLp.toLp 2 v‖ :=
    (norm_toLp_mulVec_le A v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hexp : ‖WithLp.toLp 2 ((1 - (α : 𝕜) • A) *ᵥ v)‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 -
      2 * α * RCLike.re (quadForm A v) + α ^ 2 * ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2 := by
    have e : WithLp.toLp 2 ((1 - (α : 𝕜) • A) *ᵥ v) =
        WithLp.toLp 2 v - (α : 𝕜) • WithLp.toLp 2 (A *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, WithLp.toLp_sub,
        WithLp.toLp_smul]
    rw [e, @norm_sub_sq 𝕜, inner_smul_right, EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
      ← quadForm_def, RCLike.re_ofReal_mul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hα0]
    ring
  have hle : ‖WithLp.toLp 2 ((1 - (α : 𝕜) • A) *ᵥ v)‖ ^ 2 ≤
      (1 - (a / a') ^ 2) * ‖WithLp.toLp 2 v‖ ^ 2 := by
    have h2 : α ^ 2 * ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2 ≤ α ^ 2 * (a' * ‖WithLp.toLp 2 v‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hAv 2) (sq_nonneg _)
    have h3 : 2 * α * (a * ‖WithLp.toLp 2 v‖ ^ 2) ≤ 2 * α * RCLike.re (quadForm A v) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    have hid : ‖WithLp.toLp 2 v‖ ^ 2 - 2 * α * (a * ‖WithLp.toLp 2 v‖ ^ 2) +
        α ^ 2 * (a' * ‖WithLp.toLp 2 v‖) ^ 2 = (1 - (a / a') ^ 2) * ‖WithLp.toLp 2 v‖ ^ 2 := by
      rw [hα]
      field_simp
      ring
    rw [hexp]
    linarith
  calc ‖WithLp.toLp 2 ((1 - (α : 𝕜) • A) *ᵥ v)‖
      = Real.sqrt (‖WithLp.toLp 2 ((1 - (α : 𝕜) • A) *ᵥ v)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 - (a / a') ^ 2) * ‖WithLp.toLp 2 v‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = √(1 - (a / a') ^ 2) * ‖WithLp.toLp 2 v‖ := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Over $\mathbb{R}$ the trace of a compression sees only the symmetric part:
$\operatorname{tr}(\mathbf{Q}^{\mathsf{T}}\mathbf{H}\mathbf{Q})
= \operatorname{tr}(\mathbf{Q}^{\mathsf{T}}\mathbf{A}\mathbf{Q})$ for
$\mathbf{H} = \tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{T}})$ and any $\mathbf{Q}$. -/
theorem trace_conjTranspose_mul_hermitianPart_mul {k : Type*} [Fintype k] (Q : Matrix n k ℝ)
    (A : Matrix n n ℝ) : (Qᴴ * hermitianPart A * Q).trace = (Qᴴ * A * Q).trace := by
  have h : (Qᴴ * Aᴴ * Q).trace = (Qᴴ * A * Q).trace := by
    have e : Qᴴ * Aᴴ * Q = (Qᴴ * A * Q)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e, Matrix.trace_conjTranspose, star_trivial]
  rw [hermitianPart, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_add,
    Matrix.add_mul, Matrix.trace_add, h, smul_eq_mul]
  ring

/-- The Hermitian part commutes with unitary conjugation: the Hermitian part of
$\mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}}$ is $\mathbf{U}\mathbf{H}\mathbf{U}^{\mathsf{H}}$ for
$\mathbf{H} = \tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$, for any square $\mathbf{U}$. -/
theorem hermitianPart_mul_mul_conjTranspose (U A : Matrix n n 𝕜) :
    hermitianPart (U * A * Uᴴ) = U * hermitianPart A * Uᴴ := by
  simp only [hermitianPart, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

variable [DecidableEq n]

/-- **The real parts of the eigenvalues are majorized by the eigenvalues of the Hermitian
part** (Ky Fan): if $\mathbf{z}$ lists the eigenvalues of a complex matrix $\mathbf{A}$ and the
real $\mathbf{x}$ lists those of $\tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$, then
$(\operatorname{Re} \mathbf{z}_i)_i$ is majorized by $\mathbf{x}$ (`Majorized`).
[HornJohnson1991, §3.3]; [Bhatia1997, Proposition III.5.3].
Result: real-part-majorization -/
theorem majorized_re_of_isEigenvalueListing {A : Matrix n n ℂ} {z : n → ℂ} {x : n → ℝ}
    (hz : IsEigenvalueListing A z)
    (hx : IsEigenvalueListing (hermitianPart A) fun i => ((x i : ℝ) : ℂ)) :
    Majorized (fun i => (z i).re) x := by
  classical
  let _ : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨U, hU, -, hdiag⟩ := hz.exists_hasOrthonormalCols_isUpperTriangular
  have hH : hermitianPart (Uᴴ * A * U) = Uᴴ * hermitianPart A * U := by
    have h := hermitianPart_mul_mul_conjTranspose Uᴴ A
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hherm := isHermitian_hermitianPart (Uᴴ * A * U)
  have hre : ∀ i, RCLike.re (hermitianPart (Uᴴ * A * U) i i) = (z i).re := by
    intro i
    rw [hermitianPart, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, hdiag,
      RCLike.re_to_complex, Complex.real_smul, Complex.re_ofReal_mul, Complex.add_re,
      Complex.star_def, Complex.conj_re]
    ring
  have hmaj := hherm.majorized_re_diag_eigenvalues
  simp only [hre] at hmaj
  have hlist : IsEigenvalueListing (hermitianPart A) fun i => ((hherm.eigenvalues i : ℝ) : ℂ) := by
    have hchar : (hermitianPart (Uᴴ * A * U)).charpoly = (hermitianPart A).charpoly := by
      rw [hH, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU.mul_conjTranspose_self,
        Matrix.one_mul]
    exact hchar.symm.trans hherm.charpoly_eq
  obtain ⟨e, he⟩ := hlist.exists_equiv_eq hx
  have heq : hherm.eigenvalues = x ∘ e := funext fun i => Complex.ofReal_injective (congrFun he i)
  rw [heq] at hmaj
  exact hmaj.trans (majorized_comp_equiv x e)

/-- **Realization of a spectrum and a Hermitian-part spectrum.** For real $\mathbf{x}$ and
complex $\mathbf{z}$ indexed by any finite type, if $(\operatorname{Re}\mathbf{z}_i)_i$ is
majorized by $\mathbf{x}$, there is a complex matrix $\mathbf{A}$ whose eigenvalues are
$\mathbf{z}$ and whose Hermitian part has eigenvalues $\mathbf{x}$. Both listings include
algebraic multiplicities; repeated entries and the empty index type are allowed.
[HornJohnson2013, Theorem 4.3.50]. Adapted from `tchen-research/NLAlib`, commit
`77514ce42a0e437d837797a063ac161f41022730`,
`exists_matrix_charpoly_and_selfAdjointPart_charpoly_of_majorized`.
Result: real-part-majorization -/
theorem exists_isEigenvalueListing_hermitianPart_of_majorized
    {x : n → ℝ} {z : n → ℂ} (h : Majorized (fun i => (z i).re) x) :
    ∃ A : Matrix n n ℂ, IsEigenvalueListing A z ∧
      IsEigenvalueListing (hermitianPart A) (fun i => (x i : ℂ)) := by
  classical
  let _ : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨Q, hQ, hdiag⟩ := exists_hasOrthonormalCols_diag_eq_of_majorized h
  let K := Q * Matrix.diagonal x * Qᴴ
  have hK : K.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose Q (Matrix.isHermitian_diagonal x)
  have hKd (i : n) : K i i = (z i).re := congrFun hdiag i
  let T : Matrix n n ℂ := fun i j =>
    if i = j then z i else if i < j then 2 * (K i j : ℂ) else 0
  have hTd (i : n) : T i i = z i := by simp [T]
  have hTri : T.IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [T, ne_of_gt hij, not_lt.mpr hij.le]
  have hc (r : ℝ) : RCLike.toComplex r = (r : ℂ) :=
    RCLike.toComplex_ofReal (𝕜 := ℝ) r
  have hPart : hermitianPart T = complexify K := by
    ext i j
    change (2⁻¹ : ℝ) • (T i j + star (T j i)) = RCLike.toComplex (K i j)
    rw [hc]
    have hKji : K j i = K i j := by
      simpa only [Matrix.conjTranspose_apply, star_trivial] using
        congrArg (fun M : Matrix n n ℝ => M i j) hK.eq
    by_cases hij : i = j
    · subst j
      rw [hTd, hKd, Complex.star_def, Complex.add_conj, Complex.real_smul]
      push_cast
      ring
    · have hji := Ne.symm hij
      by_cases hlt : i < j
      · have hnlt : ¬j < i := not_lt.mpr hlt.le
        simp [T, hij, hji, hlt, hnlt, Complex.real_smul]
      · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
        simp [T, hij, hji, hlt, hgt, hKji, Complex.real_smul]
  refine ⟨T, ?_, ?_⟩
  · simpa only [hTd] using hTri.isEigenvalueListing_diag
  · change (hermitianPart T).charpoly = ∏ i, (X - C (x i : ℂ))
    rw [hPart]
    simp only [K, complexify_mul, complexify_conjTranspose, complexify_diagonal, hc]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      hQ.complexify.conjTranspose_mul_self, Matrix.one_mul, Matrix.charpoly_diagonal]

/-- **Real-part majorization characterizes spectral compatibility.** For a real list
$\mathbf{x}$ and a complex list $\mathbf{z}$ indexed by the same finite type,
$(\operatorname{Re}\mathbf{z}_i)_i$ is majorized by $\mathbf{x}$ if and only if a complex
matrix has eigenvalue listing $\mathbf{z}$ and its Hermitian part has eigenvalue listing
$\mathbf{x}$. The listings record algebraic multiplicities, including repeated entries;
the index type may be empty.
[HornJohnson2013, Theorem 4.3.50]. Adapted from `tchen-research/NLAlib`, commit
`77514ce42a0e437d837797a063ac161f41022730`,
`majorized_real_parts_iff_exists_charpoly_and_selfAdjointPart_charpoly`.
Result: real-part-majorization -/
theorem majorized_re_iff_exists_isEigenvalueListing_hermitianPart
    (x : n → ℝ) (z : n → ℂ) :
    Majorized (fun i => (z i).re) x ↔
      ∃ A : Matrix n n ℂ, IsEigenvalueListing A z ∧
        IsEigenvalueListing (hermitianPart A) (fun i => (x i : ℂ)) := by
  refine ⟨exists_isEigenvalueListing_hermitianPart_of_majorized, ?_⟩
  rintro ⟨A, hz, hx⟩
  exact majorized_re_of_isEigenvalueListing hz hx

/-- An eigenvalue is the value of the quadratic form at a unit eigenvector: for $\mu$ in the
spectrum there is $\mathbf{v} \ne \mathbf{0}$ with
$\operatorname{Re}(\mathbf{v}^{\mathsf{H}}\mathbf{A}\mathbf{v}) = \operatorname{Re}(\mu)
\|\mathbf{v}\|^2$. -/
private theorem exists_re_quadForm_eq_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ v : n → 𝕜, 0 < ‖WithLp.toLp 2 v‖ ^ 2 ∧
      RCLike.re (quadForm A v) = RCLike.re μ * ‖WithLp.toLp 2 v‖ ^ 2 := by
  obtain ⟨v, hv, hAv⟩ := exists_mulVec_eq_smul_of_mem_spectrum hμ
  refine ⟨v, pow_pos (norm_pos_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hv)) 2, ?_⟩
  rw [quadForm, hAv, dotProduct_smul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
    smul_eq_mul, RCLike.re_mul_ofReal]

/-- **Bendixson's upper bound**: the real part of every eigenvalue $\mu$ of $\mathbf{A}$ is at
most the largest eigenvalue of the Hermitian part:
$\operatorname{Re} \mu \le \lambda_0\bigl(\tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})\bigr)$.
[HornJohnson2013, §5.6]. -/
theorem re_le_eigenvalue_zero_hermitianPart {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : RCLike.re μ ≤ eigenvalue (hermitianPart A) 0 := by
  obtain ⟨v, hv, hq⟩ := exists_re_quadForm_eq_of_mem_spectrum hμ
  have h := (isHermitian_hermitianPart A).re_quadForm_le_eigenvalue_zero_mul v
  rw [re_quadForm_hermitianPart, hq] at h
  exact le_of_mul_le_mul_right h hv

/-- **Bendixson's lower bound**: the real part of every eigenvalue $\mu$ of $\mathbf{A}$ is at
least the smallest eigenvalue of the Hermitian part:
$\lambda_j\bigl(\tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})\bigr) \le \operatorname{Re} \mu$
for $j + 1 = \lvert n \rvert$.
[HornJohnson1991, §1.5] (locator to check). -/
theorem eigenvalue_hermitianPart_le_re {A : Matrix n n 𝕜} {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A)
    {j : ℕ} (hj : j + 1 = Fintype.card n) : eigenvalue (hermitianPart A) j ≤ RCLike.re μ := by
  obtain ⟨v, hv, hq⟩ := exists_re_quadForm_eq_of_mem_spectrum hμ
  have h := (isHermitian_hermitianPart A).eigenvalue_last_mul_le_re_quadForm hj v
  rw [re_quadForm_hermitianPart, hq] at h
  exact le_of_mul_le_mul_right h hv

open scoped ComplexOrder in
/-- **A matrix with positive definite Hermitian part is invertible**: $\det \mathbf{A} \ne 0$. A
null vector $\mathbf{v}$ of $\mathbf{A}$ would have
$\operatorname{Re}(\mathbf{v}^{\mathsf{H}}\mathbf{A}\mathbf{v}) = 0$, which is the quadratic form
of the Hermitian part. [HornJohnson2013, §7.1 context]. -/
theorem _root_.Matrix.PosDef.det_ne_zero_of_hermitianPart {A : Matrix n n 𝕜}
    (h : (hermitianPart A).PosDef) :
    A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hpos := h.re_quadForm_pos hv
  rw [re_quadForm_hermitianPart, quadForm, hAv, dotProduct_zero, map_zero] at hpos
  exact lt_irrefl 0 hpos

end NLAlib
