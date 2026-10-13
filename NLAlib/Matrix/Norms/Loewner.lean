/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.PosDef
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Compare

/-!
# Norm bounds as Loewner inequalities

A spectral norm bound on a matrix `T` is a Loewner inequality on its Gram matrix, and for a
Hermitian matrix it is a two-sided Loewner inequality on the matrix itself. These are the forms
in which matrix concentration inequalities conclude and in which a subspace embedding is stated,
so the lemmas here are the bridge between those layers and `specNorm`.

A scalar multiple of the identity in a Loewner inequality is always written with the real scalar
action, `(a : ℝ) • (1 : Matrix n n 𝕜)`.

## Main results

* `NLAlib.conjTranspose_mul_self_le_smul_one_iff`, `NLAlib.smul_one_le_conjTranspose_mul_self_iff`:
  an upper or lower Loewner bound on `Tᴴ * T` is a bound on `‖T x‖ ^ 2` for every `x`.
* `NLAlib.specNorm_sq_le_iff_conjTranspose_mul_self_le`: the upper bound in terms of `specNorm`.
* `NLAlib.mul_specNorm_sq_le_of_smul_one_le`, `NLAlib.mul_frobNorm_sq_le_of_smul_one_le`: a factor
  bounded below cannot shrink a norm by more than its lower bound.
* `Matrix.IsHermitian.specNorm_le_iff`: for Hermitian `A`, `specNorm A ≤ c` iff
  `-(c • 1) ≤ A ≤ c • 1`.
* `NLAlib.one_sub_smul_one_le_conjTranspose_mul_self_of_specNorm_le`,
  `NLAlib.conjTranspose_mul_self_le_one_add_smul_one_of_specNorm_le`: from the Gram error
  `specNorm (Tᴴ * T - 1) ≤ ε` to the Loewner bounds `(1 - ε) • 1 ≤ Tᴴ * T ≤ (1 + ε) • 1`.
* `Matrix.PosSemidef.specNorm_le_specNorm_of_le`: the spectral norm is monotone on the positive
  semidefinite cone.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Quadratic forms -/

/-- The quadratic form is bounded by the spectral norm: `|zᴴ A z| ≤ specNorm A * ‖z‖ ^ 2`.
Port of `NLAlib.abs_re_star_dotProduct_mulVec_le_specNorm`. -/
theorem norm_quadForm_le (A : Matrix n n 𝕜) (z : n → 𝕜) :
    ‖quadForm A z‖ ≤ specNorm A * ‖WithLp.toLp 2 z‖ ^ 2 := by
  refine (norm_star_dotProduct_mulVec_le A z z).trans_eq ?_
  ring

/-- The real part of the quadratic form is bounded by the spectral norm. -/
theorem abs_re_quadForm_le (A : Matrix n n 𝕜) (z : n → 𝕜) :
    |RCLike.re (quadForm A z)| ≤ specNorm A * ‖WithLp.toLp 2 z‖ ^ 2 := by
  exact (RCLike.abs_re_le_norm _).trans (norm_quadForm_le A z)

/-! ### Gram matrices -/

/-- An upper Loewner bound on the Gram matrix of `T` is an upper bound on `‖T x‖ ^ 2`. -/
theorem conjTranspose_mul_self_le_smul_one_iff [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ} :
    Tᴴ * T ≤ a • (1 : Matrix n n 𝕜) ↔
      ∀ x, ‖WithLp.toLp 2 (T *ᵥ x)‖ ^ 2 ≤ a * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [(Matrix.isHermitian_conjTranspose_mul_self T).le_iff_re_quadForm_le
    (isHermitian_real_smul_one a)]
  simp only [quadForm_conjTranspose_mul_self, RCLike.ofReal_re, re_quadForm_real_smul_one]

/-- A lower Loewner bound on the Gram matrix of `T` is a lower bound on `‖T x‖ ^ 2`. This is the
form in which a one-sided subspace embedding is used vector by vector.
Port of the hypothesis of `NLAlib.mul_specNorm_le_specNorm_mul_of_mulVec_sq_le`. -/
theorem smul_one_le_conjTranspose_mul_self_iff [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ} :
    a • (1 : Matrix n n 𝕜) ≤ Tᴴ * T ↔
      ∀ x, a * ‖WithLp.toLp 2 x‖ ^ 2 ≤ ‖WithLp.toLp 2 (T *ᵥ x)‖ ^ 2 := by
  rw [(isHermitian_real_smul_one a).le_iff_re_quadForm_le
    (Matrix.isHermitian_conjTranspose_mul_self T)]
  simp only [quadForm_conjTranspose_mul_self, RCLike.ofReal_re, re_quadForm_real_smul_one]

/-- The squared spectral norm of `T` is at most `a ≥ 0` exactly when `Tᴴ * T ≤ a • 1`. -/
theorem specNorm_sq_le_iff_conjTranspose_mul_self_le [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ}
    (ha : 0 ≤ a) : specNorm T ^ 2 ≤ a ↔ Tᴴ * T ≤ a • (1 : Matrix n n 𝕜) := by
  rw [conjTranspose_mul_self_le_smul_one_iff, ← Real.le_sqrt (specNorm_nonneg T) ha,
    specNorm_le_iff (Real.sqrt_nonneg a)]
  refine forall_congr' fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt ha]

/-- The Gram matrix is below the squared spectral norm times the identity. -/
theorem conjTranspose_mul_self_le_specNorm_sq_smul_one [DecidableEq n] (T : Matrix m n 𝕜) :
    Tᴴ * T ≤ (specNorm T ^ 2) • (1 : Matrix n n 𝕜) := by
  exact (specNorm_sq_le_iff_conjTranspose_mul_self_le (sq_nonneg _)).mp le_rfl

/-- A factor `T` with `Tᴴ * T ≤ a • 1` enlarges the squared spectral norm by at most `a`. -/
theorem specNorm_mul_sq_le_of_conjTranspose_mul_self_le [DecidableEq m] {T : Matrix l m 𝕜}
    {a : ℝ} (h : Tᴴ * T ≤ a • (1 : Matrix m m 𝕜)) (X : Matrix m n 𝕜) :
    specNorm (T * X) ^ 2 ≤ a * specNorm X ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · calc specNorm (T * X) ^ 2 ≤ (specNorm T * specNorm X) ^ 2 := by
          gcongr
          exact specNorm_mul_le T X
      _ = specNorm T ^ 2 * specNorm X ^ 2 := mul_pow _ _ _
      _ ≤ a * specNorm X ^ 2 := by
          gcongr
          exact (specNorm_sq_le_iff_conjTranspose_mul_self_le ha).mpr h
  · rw [conjTranspose_mul_self_le_smul_one_iff] at h
    have hX : X = 0 := by
      rw [← specNorm_eq_zero_iff]
      refine le_antisymm ((specNorm_le_iff le_rfl).mpr fun x => ?_) (specNorm_nonneg X)
      have hx := h (X *ᵥ x)
      have h0 : ‖WithLp.toLp 2 (X *ᵥ x)‖ ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg ‖WithLp.toLp 2 (T *ᵥ (X *ᵥ x))‖, sq_nonneg ‖WithLp.toLp 2 (X *ᵥ x)‖]
      rw [zero_mul]
      exact (sq_nonpos_iff _).mp h0 |>.le
    rw [hX, Matrix.mul_zero, specNorm_zero]
    norm_num

/-- A factor `T` with `a • 1 ≤ Tᴴ * T` shrinks the squared spectral norm by at most `a`.
Port of `NLAlib.mul_specNorm_le_specNorm_mul_of_mulVec_sq_le`, there over `ℝ` with the
hypothesis as a raw condition on vectors and the bound unsquared. -/
theorem mul_specNorm_sq_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    a * specNorm X ^ 2 ≤ specNorm (T * X) ^ 2 := by
  rw [smul_one_le_conjTranspose_mul_self_iff] at h
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim X 0, Matrix.mul_zero, specNorm_zero]
    norm_num
  · obtain ⟨x, hx, hmax⟩ := exists_norm_eq_one_and_norm_mulVec_eq_specNorm X
    have hTX := norm_toLp_mulVec_le (T * X) x
    rw [hx, mul_one, ← Matrix.mulVec_mulVec] at hTX
    calc a * specNorm X ^ 2 = a * ‖WithLp.toLp 2 (X *ᵥ x)‖ ^ 2 := by rw [hmax]
      _ ≤ ‖WithLp.toLp 2 (T *ᵥ (X *ᵥ x))‖ ^ 2 := h _
      _ ≤ specNorm (T * X) ^ 2 := by gcongr

/-- A factor `T` with `Tᴴ * T ≤ a • 1` enlarges the squared Frobenius norm by at most `a`. -/
theorem frobNorm_mul_sq_le_of_conjTranspose_mul_self_le [DecidableEq m] {T : Matrix l m 𝕜}
    {a : ℝ} (h : Tᴴ * T ≤ a • (1 : Matrix m m 𝕜)) (X : Matrix m n 𝕜) :
    frobNorm (T * X) ^ 2 ≤ a * frobNorm X ^ 2 := by
  rw [conjTranspose_mul_self_le_smul_one_iff] at h
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => h (X.col j)

/-- A factor `T` with `a • 1 ≤ Tᴴ * T` shrinks the squared Frobenius norm by at most `a`.
Port of `NLAlib.mul_frobSq_le_frobSq_mul_of_mulVec_sq_le`. -/
theorem mul_frobNorm_sq_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    a * frobNorm X ^ 2 ≤ frobNorm (T * X) ^ 2 := by
  rw [smul_one_le_conjTranspose_mul_self_iff] at h
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => h (X.col j)

/-- The unsquared form of `NLAlib.mul_specNorm_sq_le_of_smul_one_le`, for a lower bound written
as a square. -/
theorem mul_specNorm_le_of_sq_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {c : ℝ}
    (hc : 0 ≤ c) (h : (c ^ 2) • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    c * specNorm X ≤ specNorm (T * X) := by
  rw [← sq_le_sq₀ (by positivity) (specNorm_nonneg _), mul_pow]
  exact mul_specNorm_sq_le_of_smul_one_le h X

/-! ### Hermitian matrices -/

/-- For a Hermitian matrix and `c ≥ 0`, `specNorm A ≤ c` exactly when the real quadratic form is
bounded by `c * ‖x‖ ^ 2`. Port of `NLAlib.specNorm_le_iff_abs_dotProduct_mulVec_le`, there over
`ℝ`. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_iff_abs_re_quadForm_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ ∀ x, |RCLike.re (quadForm A x)| ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  classical
  refine ⟨fun h x => (abs_re_quadForm_le A x).trans (by gcongr), fun h => ?_⟩
  have hT : (Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) A :
      EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  change ‖Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ ≤ c
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hT]
  refine ciSup_le fun x => ?_
  rw [← WithLp.toLp_ofLp 2 x, ← rayleighQuotient_eq_toEuclideanCLM, rayleighQuotient_def, abs_div,
    abs_pow, abs_norm]
  exact div_le_of_le_mul₀ (sq_nonneg _) hc (h x.ofLp)

/-- The spectral norm of a Hermitian matrix is attained by its quadratic form at a unit vector.
Port of `NLAlib.exists_unit_abs_quadForm_eq_specNorm`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.exists_norm_eq_one_and_abs_re_quadForm_eq_specNorm [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 ∧ |RCLike.re (quadForm A x)| = specNorm A := by
  classical
  obtain ⟨i⟩ := ‹Nonempty n›
  have hne : (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1).Nonempty :=
    ⟨EuclideanSpace.single i 1, by simp⟩
  have hcont : Continuous fun x : EuclideanSpace 𝕜 n => |RCLike.re (quadForm A x.ofLp)| := by
    unfold quadForm
    fun_prop
  obtain ⟨x, hx, hmax⟩ :=
    (isCompact_sphere (0 : EuclideanSpace 𝕜 n) 1).exists_isMaxOn hne hcont.continuousOn
  rw [mem_sphere_zero_iff_norm] at hx
  refine ⟨x.ofLp, hx, le_antisymm ?_ ?_⟩
  · have h := abs_re_quadForm_le A x.ofLp
    rwa [show ‖WithLp.toLp 2 x.ofLp‖ = 1 from hx, one_pow, mul_one] at h
  · refine (hA.specNorm_le_iff_abs_re_quadForm_le (abs_nonneg _)).mpr fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · rw [quadForm_zero_right, map_zero, abs_zero]
      positivity
    have hy' : ‖WithLp.toLp 2 y‖ ≠ 0 := norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hy)
    have hc : ((‖WithLp.toLp 2 y‖⁻¹ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (inv_ne_zero hy')
    have hu : ‖WithLp.toLp 2 (((‖WithLp.toLp 2 y‖⁻¹ : ℝ) : 𝕜) • y)‖ = 1 := by
      rw [WithLp.toLp_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
        inv_mul_cancel₀ hy']
    have hle : |RCLike.re (quadForm A (((‖WithLp.toLp 2 y‖⁻¹ : ℝ) : 𝕜) • y))| ≤
        |RCLike.re (quadForm A x.ofLp)| := hmax (mem_sphere_zero_iff_norm.2 hu)
    rw [← rayleighQuotient_of_norm_eq_one A hu, rayleighQuotient_smul A hc] at hle
    rw [re_quadForm_eq_rayleighQuotient_mul, abs_mul, abs_pow, abs_norm]
    gcongr

/-- The upper half of `Matrix.IsHermitian.specNorm_le_iff`. -/
theorem _root_.Matrix.IsHermitian.le_smul_one_of_specNorm_le [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (h : specNorm A ≤ c) : A ≤ c • (1 : Matrix n n 𝕜) := by
  rw [hA.le_iff_re_quadForm_le (isHermitian_real_smul_one c)]
  intro x
  rw [re_quadForm_real_smul_one]
  calc RCLike.re (quadForm A x) ≤ |RCLike.re (quadForm A x)| := le_abs_self _
    _ ≤ specNorm A * ‖WithLp.toLp 2 x‖ ^ 2 := abs_re_quadForm_le A x
    _ ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by gcongr

/-- The lower half of `Matrix.IsHermitian.specNorm_le_iff`. -/
theorem _root_.Matrix.IsHermitian.neg_smul_one_le_of_specNorm_le [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} (h : specNorm A ≤ c) :
    -(c • (1 : Matrix n n 𝕜)) ≤ A := by
  rw [(isHermitian_real_smul_one c).neg.le_iff_re_quadForm_le hA]
  intro x
  rw [quadForm_neg_left, map_neg, re_quadForm_real_smul_one]
  calc -(c * ‖WithLp.toLp 2 x‖ ^ 2) ≤ -(specNorm A * ‖WithLp.toLp 2 x‖ ^ 2) := by gcongr
    _ ≤ -|RCLike.re (quadForm A x)| := neg_le_neg (abs_re_quadForm_le A x)
    _ ≤ RCLike.re (quadForm A x) := neg_abs_le _

/-- A Hermitian matrix is below its spectral norm times the identity. -/
theorem _root_.Matrix.IsHermitian.le_specNorm_smul_one [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A ≤ specNorm A • (1 : Matrix n n 𝕜) := by
  exact hA.le_smul_one_of_specNorm_le le_rfl

/-- A Hermitian matrix is above minus its spectral norm times the identity. -/
theorem _root_.Matrix.IsHermitian.neg_specNorm_smul_one_le [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : -(specNorm A • (1 : Matrix n n 𝕜)) ≤ A := by
  exact hA.neg_smul_one_le_of_specNorm_le le_rfl

/-- A Hermitian matrix sandwiched between `-(c • 1)` and `c • 1` has spectral norm at most `c`,
for `c ≥ 0`. This is how a two-sided eigenvalue bound becomes a norm bound. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_of_le_smul_one [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (h₁ : -(c • (1 : Matrix n n 𝕜)) ≤ A)
    (h₂ : A ≤ c • (1 : Matrix n n 𝕜)) : specNorm A ≤ c := by
  rw [hA.specNorm_le_iff_abs_re_quadForm_le hc]
  intro x
  have h₁' := re_quadForm_le_re_quadForm_of_le h₁ x
  have h₂' := re_quadForm_le_re_quadForm_of_le h₂ x
  rw [quadForm_neg_left, map_neg, re_quadForm_real_smul_one] at h₁'
  rw [re_quadForm_real_smul_one] at h₂'
  exact abs_le.mpr ⟨h₁', h₂'⟩

/-- For a Hermitian matrix and `c ≥ 0`, `specNorm A ≤ c` exactly when `-(c • 1) ≤ A ≤ c • 1`.
[HornJohnson2013, §7.7]. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ -(c • (1 : Matrix n n 𝕜)) ≤ A ∧ A ≤ c • (1 : Matrix n n 𝕜) := by
  exact ⟨fun h => ⟨hA.neg_smul_one_le_of_specNorm_le h, hA.le_smul_one_of_specNorm_le h⟩,
    fun h => hA.specNorm_le_of_le_smul_one hc h.1 h.2⟩

/-! ### Gram matrices close to the identity -/

/-- If the Gram matrix of `T` is within `ε` of the identity in spectral norm, then
`(1 - ε) • 1 ≤ Tᴴ * T`. This turns the Gram-error form of a subspace embedding,
`specNorm (Tᴴ * T - 1) ≤ ε`, into the lower Loewner bound that
`NLAlib.mul_specNorm_sq_le_of_smul_one_le` consumes. -/
theorem one_sub_smul_one_le_conjTranspose_mul_self_of_specNorm_le [DecidableEq n]
    {T : Matrix m n 𝕜} {ε : ℝ} (h : specNorm (Tᴴ * T - 1) ≤ ε) :
    (1 - ε) • (1 : Matrix n n 𝕜) ≤ Tᴴ * T := by
  have hH : (Tᴴ * T - 1).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self T).sub Matrix.isHermitian_one
  rw [sub_smul, one_smul, sub_le_iff_le_add]
  exact neg_le_sub_iff_le_add.mp (hH.neg_smul_one_le_of_specNorm_le h)

/-- If the Gram matrix of `T` is within `ε` of the identity in spectral norm, then
`Tᴴ * T ≤ (1 + ε) • 1`. This turns the Gram-error form of a subspace embedding,
`specNorm (Tᴴ * T - 1) ≤ ε`, into the upper Loewner bound that
`NLAlib.specNorm_mul_sq_le_of_conjTranspose_mul_self_le` consumes. -/
theorem conjTranspose_mul_self_le_one_add_smul_one_of_specNorm_le [DecidableEq n]
    {T : Matrix m n 𝕜} {ε : ℝ} (h : specNorm (Tᴴ * T - 1) ≤ ε) :
    Tᴴ * T ≤ (1 + ε) • (1 : Matrix n n 𝕜) := by
  have hH : (Tᴴ * T - 1).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self T).sub Matrix.isHermitian_one
  rw [add_smul, one_smul]
  exact sub_le_iff_le_add'.mp (hH.le_smul_one_of_specNorm_le h)

/-! ### Positive semidefinite matrices -/

/-- For a positive semidefinite matrix and `c ≥ 0`, `specNorm A ≤ c` exactly when
`A ≤ c • 1`. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ A ≤ c • (1 : Matrix n n 𝕜) := by
  refine ⟨hA.isHermitian.le_smul_one_of_specNorm_le, fun h => ?_⟩
  rw [hA.isHermitian.specNorm_le_iff_abs_re_quadForm_le hc]
  intro x
  rw [abs_of_nonneg (hA.re_quadForm_nonneg x), ← re_quadForm_real_smul_one]
  exact re_quadForm_le_re_quadForm_of_le h x

/-- The spectral norm is monotone on the positive semidefinite cone. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_specNorm_of_le {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≤ B) : specNorm A ≤ specNorm B := by
  rw [hA.isHermitian.specNorm_le_iff_abs_re_quadForm_le (specNorm_nonneg B)]
  intro x
  rw [abs_of_nonneg (hA.re_quadForm_nonneg x)]
  calc RCLike.re (quadForm A x) ≤ RCLike.re (quadForm B x) := re_quadForm_le_re_quadForm_of_le h x
    _ ≤ |RCLike.re (quadForm B x)| := le_abs_self _
    _ ≤ specNorm B * ‖WithLp.toLp 2 x‖ ^ 2 := abs_re_quadForm_le B x

/-- The Frobenius norm of a positive semidefinite matrix is at most the real part of its
trace. -/
theorem _root_.Matrix.PosSemidef.frobNorm_le_re_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    frobNorm A ≤ RCLike.re A.trace := by
  rw [← sq_le_sq₀ (frobNorm_nonneg A) hA.re_trace_nonneg, frobNorm_sq_eq_sum, Matrix.trace,
    map_sum, sq, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hA.norm_apply_sq_le i j

/-- The spectral norm of a positive semidefinite matrix is at most the real part of its
trace. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_re_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    specNorm A ≤ RCLike.re A.trace :=
  (specNorm_le_frobNorm A).trans hA.frobNorm_le_re_trace

end NLAlib
