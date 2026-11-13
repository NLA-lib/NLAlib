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

A spectral norm bound on a matrix $\mathbf{T}$ is a Loewner inequality on its Gram matrix, and
for a Hermitian matrix it is a two-sided Loewner inequality on the matrix itself. These are the
forms in which matrix concentration inequalities conclude and in which a subspace embedding is
stated, so the lemmas here are the bridge between those layers and the spectral norm (`specNorm`).

A scalar multiple of the identity in a Loewner inequality is always written with the real scalar
action, `(a : ℝ) • (1 : Matrix n n 𝕜)`.

## Main results

* `NLAlib.conjTranspose_mul_self_le_smul_one_iff`, `NLAlib.smul_one_le_conjTranspose_mul_self_iff`:
  an upper or lower Loewner bound on $\mathbf{T}^{\mathsf{H}}\mathbf{T}$ is a bound on
  $\|\mathbf{T}\mathbf{x}\|^2$ for every $\mathbf{x}$.
* `NLAlib.specNorm_sq_le_iff_conjTranspose_mul_self_le`: the upper bound in terms of
  $\|\mathbf{T}\|_2$.
* `NLAlib.mul_specNorm_sq_le_of_smul_one_le`, `NLAlib.mul_frobNorm_sq_le_of_smul_one_le`: a factor
  bounded below cannot shrink a norm by more than its lower bound.
* `Matrix.IsHermitian.specNorm_le_iff`: for Hermitian $\mathbf{A}$ and $c \ge 0$,
  $\|\mathbf{A}\|_2 \le c$ iff $-c\mathbf{I} \preceq \mathbf{A} \preceq c\mathbf{I}$.
* `NLAlib.one_sub_smul_one_le_conjTranspose_mul_self_of_specNorm_le`,
  `NLAlib.conjTranspose_mul_self_le_one_add_smul_one_of_specNorm_le`: from the Gram error
  $\|\mathbf{T}^{\mathsf{H}}\mathbf{T} - \mathbf{I}\|_2 \le \varepsilon$ to the Loewner bounds
  $(1 - \varepsilon)\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}
  \preceq (1 + \varepsilon)\mathbf{I}$.
* `Matrix.PosSemidef.specNorm_le_specNorm_of_le`: the spectral norm is monotone on the positive
  semidefinite cone.
* `NLAlib.isHermitian_of_le_smul_one`, `NLAlib.isHermitian_of_smul_one_le`,
  `NLAlib.smul_one_le_smul_one_iff`, `NLAlib.smul_one_le_diagonal_iff`: comparisons with
  multiples of the identity.
* `NLAlib.smul_le_smul_of_nonneg`: scaling by $c \ge 0$ is monotone, for any index type.
* `NLAlib.inv_mul_smul_vecMulVec_star_self_le`: a weighted rank-one matrix
  $(c w)^{-1} \mathbf{b}^{\mathsf{H}} \mathbf{b}$ lies below $(L / c)\,\mathbf{I}$ when
  $\|\mathbf{b}\|^2 \le L w$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Quadratic forms -/

/-- The quadratic form is bounded by the spectral norm:
$\lvert \mathbf{z}^{\mathsf{H}}\mathbf{A}\mathbf{z} \rvert \le \|\mathbf{A}\|_2 \|\mathbf{z}\|^2$.
-/
theorem norm_quadForm_le (A : Matrix n n 𝕜) (z : n → 𝕜) :
    ‖quadForm A z‖ ≤ specNorm A * ‖WithLp.toLp 2 z‖ ^ 2 := by
  refine (norm_star_dotProduct_mulVec_le A z z).trans_eq ?_
  ring

/-- The real part of the quadratic form is bounded by the spectral norm:
$\lvert \operatorname{Re}(\mathbf{z}^{\mathsf{H}}\mathbf{A}\mathbf{z}) \rvert
\le \|\mathbf{A}\|_2 \|\mathbf{z}\|^2$. -/
theorem abs_re_quadForm_le (A : Matrix n n 𝕜) (z : n → 𝕜) :
    |RCLike.re (quadForm A z)| ≤ specNorm A * ‖WithLp.toLp 2 z‖ ^ 2 := by
  exact (RCLike.abs_re_le_norm _).trans (norm_quadForm_le A z)

open scoped Matrix.Norms.L2Operator in
/-- For positive semidefinite $\mathbf{A}\preceq u\mathbf{I}$, its action satisfies
$\|\mathbf{A}\mathbf{x}\|^2\le u\operatorname{Re}
(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$.
This converts a Loewner upper bound into a residual-versus-energy estimate. -/
theorem _root_.Matrix.PosSemidef.norm_toLp_mulVec_sq_le [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {u : ℝ}
    (hu : A ≤ u • (1 : Matrix n n 𝕜)) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 ≤ u * RCLike.re (quadForm A x) := by
  have hs : ∀ t ∈ spectrum ℝ A, t ≤ u := by
    apply (le_algebraMap_iff_spectrum_le hA.isHermitian).mp
    simpa only [Algebra.algebraMap_eq_smul_one] using hu
  have hle : cfc (fun t : ℝ => t ^ 2) A ≤ cfc (fun t : ℝ => u * t) A := by
    refine cfc_mono (fun t ht => ?_) (by fun_prop) (by fun_prop)
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hs t ht)
      (spectrum_nonneg_of_nonneg hA.nonneg ht)
  have hid : cfc (fun t : ℝ => t ^ 2) A = A ^ 2 :=
    cfc_pow_id (R := ℝ) A 2 hA.isHermitian
  have hmul : cfc (fun t : ℝ => u * t) A = u • A :=
    cfc_const_mul_id u A hA.isHermitian
  rw [hid, hmul, pow_two] at hle
  have hgram : Aᴴ * A ≤ u • A := by simpa only [hA.isHermitian.eq] using hle
  have hq := re_quadForm_le_re_quadForm_of_le hgram x
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left,
    RCLike.re_ofReal_mul, quadForm_conjTranspose_mul_self, RCLike.ofReal_re] at hq
  exact hq

/-! ### Congruence -/

omit [Fintype n] in
/-- **Congruence preserves the Loewner order**, for a factor of any shape: if
$\mathbf{G} \preceq \mathbf{H}$ then
$\mathbf{X}^{\mathsf{H}}\mathbf{G}\mathbf{X} \preceq \mathbf{X}^{\mathsf{H}}\mathbf{H}\mathbf{X}$.
This is `Matrix.PosSemidef.conjTranspose_mul_mul_same'` applied to $\mathbf{H} - \mathbf{G}$,
so the column index type of $\mathbf{X}$ need not be finite. [HornJohnson2013, §7.7]. -/
theorem conjTranspose_mul_mul_le_conjTranspose_mul_mul {G H : Matrix m m 𝕜}
    (h : G ≤ H) (X : Matrix m n 𝕜) : Xᴴ * G * X ≤ Xᴴ * H * X := by
  rw [Matrix.le_iff] at h ⊢
  have h' := h.conjTranspose_mul_mul_same' X
  rwa [Matrix.mul_sub, Matrix.sub_mul] at h'

/-! ### Multiples of the identity -/

omit [Fintype n] in
/-- A matrix below a real multiple of the identity in the Loewner order is Hermitian: if
$\mathbf{M} \preceq b\mathbf{I}$, $b$ real, then $\mathbf{M}$ is Hermitian. A Loewner bound against
$b\mathbf{I}$ therefore needs no separate Hermitian hypothesis. -/
theorem isHermitian_of_le_smul_one [DecidableEq n] {M : Matrix n n 𝕜} {b : ℝ}
    (h : M ≤ b • (1 : Matrix n n 𝕜)) : M.IsHermitian := by
  have h' := (isHermitian_real_smul_one (𝕜 := 𝕜) (n := n) b).sub (Matrix.le_iff.mp h).isHermitian
  rwa [sub_sub_cancel] at h'

omit [Fintype n] in
/-- A matrix above a real multiple of the identity in the Loewner order is Hermitian: if
$a\mathbf{I} \preceq \mathbf{M}$, $a$ real, then $\mathbf{M}$ is Hermitian. -/
theorem isHermitian_of_smul_one_le [DecidableEq n] {M : Matrix n n 𝕜} {a : ℝ}
    (h : a • (1 : Matrix n n 𝕜) ≤ M) : M.IsHermitian := by
  have h' := (Matrix.le_iff.mp h).isHermitian.add (isHermitian_real_smul_one (𝕜 := 𝕜) (n := n) a)
  rwa [sub_add_cancel] at h'

omit [Fintype n] in
/-- A real diagonal matrix is above $c\mathbf{I}$ in the Loewner order exactly when its entries
are at least $c$: $c\mathbf{I} \preceq \operatorname{diag}(\mathbf{d})$ iff $c \le \mathbf{d}_i$
for all $i$. -/
theorem smul_one_le_diagonal_iff [DecidableEq n] {d : n → ℝ} {c : ℝ} :
    c • (1 : Matrix n n 𝕜) ≤ Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) ↔ ∀ i, c ≤ d i := by
  have e : (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) - c • (1 : Matrix n n 𝕜) =
      Matrix.diagonal fun i => ((d i - c : ℝ) : 𝕜) := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c, ← Matrix.diagonal_one, ← Matrix.diagonal_smul,
      Matrix.diagonal_sub]
    congr 1
    ext i
    simp
  rw [Matrix.le_iff, e, Matrix.posSemidef_diagonal_iff]
  exact forall_congr' fun i => by rw [RCLike.ofReal_nonneg, sub_nonneg]

omit [Fintype n] in
/-- Real multiples of the identity are ordered as their scalars: $a \le b$ implies
$a\mathbf{I} \preceq b\mathbf{I}$. -/
theorem smul_one_le_smul_one [DecidableEq n] {a b : ℝ} (h : a ≤ b) :
    a • (1 : Matrix n n 𝕜) ≤ b • (1 : Matrix n n 𝕜) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr h)

omit [Fintype n] in
/-- On a nonempty index type, real multiples of the identity are ordered exactly as their
scalars: $a\mathbf{I} \preceq b\mathbf{I}$ iff $a \le b$. -/
theorem smul_one_le_smul_one_iff [DecidableEq n] [Nonempty n] {a b : ℝ} :
    a • (1 : Matrix n n 𝕜) ≤ b • (1 : Matrix n n 𝕜) ↔ a ≤ b := by
  have e : b • (1 : Matrix n n 𝕜) = Matrix.diagonal fun _ => ((b : ℝ) : 𝕜) := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) b, ← Matrix.diagonal_one, ← Matrix.diagonal_smul]
    congr 1
    ext i
    simp
  rw [e, smul_one_le_diagonal_iff, forall_const]

/-! ### Gram matrices -/

/-- An upper Loewner bound on the Gram matrix of $\mathbf{T}$ is an upper bound on
$\|\mathbf{T}\mathbf{x}\|^2$: $\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq a\mathbf{I}$ iff
$\|\mathbf{T}\mathbf{x}\|^2 \le a \|\mathbf{x}\|^2$ for every $\mathbf{x}$. -/
theorem conjTranspose_mul_self_le_smul_one_iff [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ} :
    Tᴴ * T ≤ a • (1 : Matrix n n 𝕜) ↔
      ∀ x, ‖WithLp.toLp 2 (T *ᵥ x)‖ ^ 2 ≤ a * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [(Matrix.isHermitian_conjTranspose_mul_self T).le_iff_re_quadForm_le
    (isHermitian_real_smul_one a)]
  simp only [quadForm_conjTranspose_mul_self, RCLike.ofReal_re, re_quadForm_real_smul_one]

/-- A lower Loewner bound on the Gram matrix of $\mathbf{T}$ is a lower bound on
$\|\mathbf{T}\mathbf{x}\|^2$: $a\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$ iff
$a \|\mathbf{x}\|^2 \le \|\mathbf{T}\mathbf{x}\|^2$ for every $\mathbf{x}$. This is the form in
which a one-sided subspace embedding is used vector by vector. -/
theorem smul_one_le_conjTranspose_mul_self_iff [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ} :
    a • (1 : Matrix n n 𝕜) ≤ Tᴴ * T ↔
      ∀ x, a * ‖WithLp.toLp 2 x‖ ^ 2 ≤ ‖WithLp.toLp 2 (T *ᵥ x)‖ ^ 2 := by
  rw [(isHermitian_real_smul_one a).le_iff_re_quadForm_le
    (Matrix.isHermitian_conjTranspose_mul_self T)]
  simp only [quadForm_conjTranspose_mul_self, RCLike.ofReal_re, re_quadForm_real_smul_one]

/-- The squared spectral norm of $\mathbf{T}$ is at most $a \ge 0$ exactly when
$\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq a\mathbf{I}$. -/
theorem specNorm_sq_le_iff_conjTranspose_mul_self_le [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ}
    (ha : 0 ≤ a) : specNorm T ^ 2 ≤ a ↔ Tᴴ * T ≤ a • (1 : Matrix n n 𝕜) := by
  rw [conjTranspose_mul_self_le_smul_one_iff, ← Real.le_sqrt (specNorm_nonneg T) ha,
    specNorm_le_iff (Real.sqrt_nonneg a)]
  refine forall_congr' fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt ha]

/-- The Gram matrix is below the squared spectral norm times the identity:
$\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq \|\mathbf{T}\|_2^2 \, \mathbf{I}$. -/
theorem conjTranspose_mul_self_le_specNorm_sq_smul_one [DecidableEq n] (T : Matrix m n 𝕜) :
    Tᴴ * T ≤ (specNorm T ^ 2) • (1 : Matrix n n 𝕜) := by
  exact (specNorm_sq_le_iff_conjTranspose_mul_self_le (sq_nonneg _)).mp le_rfl

/-- A factor $\mathbf{T}$ with $\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq a\mathbf{I}$ enlarges the
squared spectral norm by at most $a$: $\|\mathbf{T}\mathbf{X}\|_2^2 \le a \|\mathbf{X}\|_2^2$. -/
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

/-- A factor $\mathbf{T}$ with $a\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$ shrinks the
squared spectral norm by at most $a$: $a \|\mathbf{X}\|_2^2 \le \|\mathbf{T}\mathbf{X}\|_2^2$. -/
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

/-- A factor $\mathbf{T}$ with $\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq a\mathbf{I}$ enlarges the
squared Frobenius norm by at most $a$:
$\|\mathbf{T}\mathbf{X}\|_{\mathsf{F}}^2 \le a \|\mathbf{X}\|_{\mathsf{F}}^2$. -/
theorem frobNorm_mul_sq_le_of_conjTranspose_mul_self_le [DecidableEq m] {T : Matrix l m 𝕜}
    {a : ℝ} (h : Tᴴ * T ≤ a • (1 : Matrix m m 𝕜)) (X : Matrix m n 𝕜) :
    frobNorm (T * X) ^ 2 ≤ a * frobNorm X ^ 2 := by
  rw [conjTranspose_mul_self_le_smul_one_iff] at h
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => h (X.col j)

/-- A factor $\mathbf{T}$ with $a\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$ shrinks the
squared Frobenius norm by at most $a$:
$a \|\mathbf{X}\|_{\mathsf{F}}^2 \le \|\mathbf{T}\mathbf{X}\|_{\mathsf{F}}^2$. -/
theorem mul_frobNorm_sq_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    a * frobNorm X ^ 2 ≤ frobNorm (T * X) ^ 2 := by
  rw [smul_one_le_conjTranspose_mul_self_iff] at h
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => h (X.col j)

/-- The unsquared form of `NLAlib.mul_specNorm_sq_le_of_smul_one_le`, for a lower bound written
as a square: if $c \ge 0$ and $c^2\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$ then
$c \|\mathbf{X}\|_2 \le \|\mathbf{T}\mathbf{X}\|_2$. -/
theorem mul_specNorm_le_of_sq_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {c : ℝ}
    (hc : 0 ≤ c) (h : (c ^ 2) • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    c * specNorm X ≤ specNorm (T * X) := by
  rw [← sq_le_sq₀ (by positivity) (specNorm_nonneg _), mul_pow]
  exact mul_specNorm_sq_le_of_smul_one_le h X

/-! ### Hermitian matrices -/

/-- For a Hermitian matrix and $c \ge 0$, $\|\mathbf{A}\|_2 \le c$ exactly when the real quadratic
form is bounded by $c \|\mathbf{x}\|^2$:
$\lvert \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \rvert \le c
\|\mathbf{x}\|^2$ for every $\mathbf{x}$. -/
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

/-- The spectral norm of a Hermitian matrix is attained by its quadratic form at a unit vector:
on a nonempty index type there is $\mathbf{x}$ with $\|\mathbf{x}\| = 1$ and
$\lvert \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \rvert = \|\mathbf{A}\|_2$.
-/
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

/-- The upper half of `Matrix.IsHermitian.specNorm_le_iff`: for Hermitian $\mathbf{A}$,
$\|\mathbf{A}\|_2 \le c$ implies $\mathbf{A} \preceq c\mathbf{I}$. -/
theorem _root_.Matrix.IsHermitian.le_smul_one_of_specNorm_le [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (h : specNorm A ≤ c) : A ≤ c • (1 : Matrix n n 𝕜) := by
  rw [hA.le_iff_re_quadForm_le (isHermitian_real_smul_one c)]
  intro x
  rw [re_quadForm_real_smul_one]
  calc RCLike.re (quadForm A x) ≤ |RCLike.re (quadForm A x)| := le_abs_self _
    _ ≤ specNorm A * ‖WithLp.toLp 2 x‖ ^ 2 := abs_re_quadForm_le A x
    _ ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by gcongr

/-- The lower half of `Matrix.IsHermitian.specNorm_le_iff`: for Hermitian $\mathbf{A}$,
$\|\mathbf{A}\|_2 \le c$ implies $-c\mathbf{I} \preceq \mathbf{A}$. -/
theorem _root_.Matrix.IsHermitian.neg_smul_one_le_of_specNorm_le [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} (h : specNorm A ≤ c) :
    -(c • (1 : Matrix n n 𝕜)) ≤ A := by
  rw [(isHermitian_real_smul_one c).neg.le_iff_re_quadForm_le hA]
  intro x
  rw [quadForm_neg_left, map_neg, re_quadForm_real_smul_one]
  calc -(c * ‖WithLp.toLp 2 x‖ ^ 2) ≤ -(specNorm A * ‖WithLp.toLp 2 x‖ ^ 2) := by gcongr
    _ ≤ -|RCLike.re (quadForm A x)| := neg_le_neg (abs_re_quadForm_le A x)
    _ ≤ RCLike.re (quadForm A x) := neg_abs_le _

/-- A Hermitian matrix is below its spectral norm times the identity:
$\mathbf{A} \preceq \|\mathbf{A}\|_2 \, \mathbf{I}$. -/
theorem _root_.Matrix.IsHermitian.le_specNorm_smul_one [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A ≤ specNorm A • (1 : Matrix n n 𝕜) := by
  exact hA.le_smul_one_of_specNorm_le le_rfl

/-- A Hermitian matrix is above minus its spectral norm times the identity:
$-\|\mathbf{A}\|_2 \, \mathbf{I} \preceq \mathbf{A}$. -/
theorem _root_.Matrix.IsHermitian.neg_specNorm_smul_one_le [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : -(specNorm A • (1 : Matrix n n 𝕜)) ≤ A := by
  exact hA.neg_smul_one_le_of_specNorm_le le_rfl

/-- A Hermitian matrix sandwiched between $-c\mathbf{I}$ and $c\mathbf{I}$ has spectral norm at
most $c$, for $c \ge 0$. This is how a two-sided eigenvalue bound becomes a norm bound. -/
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

/-- For a Hermitian matrix and $c \ge 0$, $\|\mathbf{A}\|_2 \le c$ exactly when
$-c\mathbf{I} \preceq \mathbf{A} \preceq c\mathbf{I}$.
[HornJohnson2013, §7.7]. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ -(c • (1 : Matrix n n 𝕜)) ≤ A ∧ A ≤ c • (1 : Matrix n n 𝕜) := by
  exact ⟨fun h => ⟨hA.neg_smul_one_le_of_specNorm_le h, hA.le_smul_one_of_specNorm_le h⟩,
    fun h => hA.specNorm_le_of_le_smul_one hc h.1 h.2⟩

/-! ### Gram matrices close to the identity -/

/-- If the Gram matrix of $\mathbf{T}$ is within $\varepsilon$ of $N\mathbf{I}$ in spectral norm,
$\|\mathbf{T}^{\mathsf{H}}\mathbf{T} - N\mathbf{I}\|_2 \le \varepsilon$, then
$\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq (N + \varepsilon)\mathbf{I}$. With $N$ the number of
rows of a sketch it is the upper Loewner bound of an unnormalised sketch. -/
theorem conjTranspose_mul_self_le_add_smul_one_of_specNorm_sub_smul_one_le [DecidableEq n]
    {T : Matrix m n 𝕜} {N ε : ℝ} (h : specNorm (Tᴴ * T - N • (1 : Matrix n n 𝕜)) ≤ ε) :
    Tᴴ * T ≤ (N + ε) • (1 : Matrix n n 𝕜) := by
  have hH : (Tᴴ * T - N • (1 : Matrix n n 𝕜)).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self T).sub (isHermitian_real_smul_one N)
  rw [add_smul]
  exact sub_le_iff_le_add'.mp (hH.le_smul_one_of_specNorm_le h)

/-- If the Gram matrix of $\mathbf{T}$ is within $\varepsilon$ of $N\mathbf{I}$ in spectral norm,
$\|\mathbf{T}^{\mathsf{H}}\mathbf{T} - N\mathbf{I}\|_2 \le \varepsilon$, then
$(N - \varepsilon)\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$. With $N$ the number of
rows of a sketch it is the lower Loewner bound of an unnormalised sketch. -/
theorem sub_smul_one_le_conjTranspose_mul_self_of_specNorm_sub_smul_one_le [DecidableEq n]
    {T : Matrix m n 𝕜} {N ε : ℝ} (h : specNorm (Tᴴ * T - N • (1 : Matrix n n 𝕜)) ≤ ε) :
    (N - ε) • (1 : Matrix n n 𝕜) ≤ Tᴴ * T := by
  have hH : (Tᴴ * T - N • (1 : Matrix n n 𝕜)).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self T).sub (isHermitian_real_smul_one N)
  rw [sub_smul, sub_le_iff_le_add]
  exact neg_le_sub_iff_le_add.mp (hH.neg_smul_one_le_of_specNorm_le h)

/-- If the Gram matrix of $\mathbf{T}$ is within $\varepsilon$ of the identity in spectral norm,
then $(1 - \varepsilon)\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$. This turns the
Gram-error form of a subspace embedding, $\|\mathbf{T}^{\mathsf{H}}\mathbf{T} - \mathbf{I}\|_2 \le
\varepsilon$, into the lower Loewner bound that
`NLAlib.mul_specNorm_sq_le_of_smul_one_le` consumes. -/
theorem one_sub_smul_one_le_conjTranspose_mul_self_of_specNorm_le [DecidableEq n]
    {T : Matrix m n 𝕜} {ε : ℝ} (h : specNorm (Tᴴ * T - 1) ≤ ε) :
    (1 - ε) • (1 : Matrix n n 𝕜) ≤ Tᴴ * T :=
  sub_smul_one_le_conjTranspose_mul_self_of_specNorm_sub_smul_one_le (N := 1) (by rwa [one_smul])

/-- If the Gram matrix of $\mathbf{T}$ is within $\varepsilon$ of the identity in spectral norm,
then $\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq (1 + \varepsilon)\mathbf{I}$. This turns the
Gram-error form of a subspace embedding, $\|\mathbf{T}^{\mathsf{H}}\mathbf{T} - \mathbf{I}\|_2 \le
\varepsilon$, into the upper Loewner bound that
`NLAlib.specNorm_mul_sq_le_of_conjTranspose_mul_self_le` consumes. -/
theorem conjTranspose_mul_self_le_one_add_smul_one_of_specNorm_le [DecidableEq n]
    {T : Matrix m n 𝕜} {ε : ℝ} (h : specNorm (Tᴴ * T - 1) ≤ ε) :
    Tᴴ * T ≤ (1 + ε) • (1 : Matrix n n 𝕜) :=
  conjTranspose_mul_self_le_add_smul_one_of_specNorm_sub_smul_one_le (N := 1) (by rwa [one_smul])

/-! ### Positive semidefinite matrices -/

/-- For a positive semidefinite matrix and $c \ge 0$, $\|\mathbf{A}\|_2 \le c$ exactly when
$\mathbf{A} \preceq c\mathbf{I}$. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ A ≤ c • (1 : Matrix n n 𝕜) := by
  refine ⟨hA.isHermitian.le_smul_one_of_specNorm_le, fun h => ?_⟩
  rw [hA.isHermitian.specNorm_le_iff_abs_re_quadForm_le hc]
  intro x
  rw [abs_of_nonneg (hA.re_quadForm_nonneg x), ← re_quadForm_real_smul_one]
  exact re_quadForm_le_re_quadForm_of_le h x

/-- The spectral norm is monotone on the positive semidefinite cone: if
$\mathbf{0} \preceq \mathbf{A} \preceq \mathbf{B}$ then $\|\mathbf{A}\|_2 \le \|\mathbf{B}\|_2$. -/
@[gcongr]
theorem _root_.Matrix.PosSemidef.specNorm_le_specNorm_of_le {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≤ B) : specNorm A ≤ specNorm B := by
  rw [hA.isHermitian.specNorm_le_iff_abs_re_quadForm_le (specNorm_nonneg B)]
  intro x
  rw [abs_of_nonneg (hA.re_quadForm_nonneg x)]
  calc RCLike.re (quadForm A x) ≤ RCLike.re (quadForm B x) := re_quadForm_le_re_quadForm_of_le h x
    _ ≤ |RCLike.re (quadForm B x)| := le_abs_self _
    _ ≤ specNorm B * ‖WithLp.toLp 2 x‖ ^ 2 := abs_re_quadForm_le B x

/-- The Frobenius norm of a positive semidefinite matrix is at most the real part of its
trace: $\|\mathbf{A}\|_{\mathsf{F}} \le \operatorname{Re} \operatorname{tr} \mathbf{A}$. -/
theorem _root_.Matrix.PosSemidef.frobNorm_le_re_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    frobNorm A ≤ RCLike.re A.trace := by
  rw [← sq_le_sq₀ (frobNorm_nonneg A) hA.re_trace_nonneg, frobNorm_sq_eq_sum, Matrix.trace,
    map_sum, sq, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hA.norm_apply_sq_le i j

/-- The spectral norm of a positive semidefinite matrix is at most the real part of its
trace: $\|\mathbf{A}\|_2 \le \operatorname{Re} \operatorname{tr} \mathbf{A}$. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_re_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    specNorm A ≤ RCLike.re A.trace :=
  (specNorm_le_frobNorm A).trans hA.frobNorm_le_re_trace

omit [Fintype n] in
/-- Scaling by a nonnegative real is monotone in the Loewner order: $\mathbf{G} \preceq \mathbf{H}$
and $c \ge 0$ give $c\,\mathbf{G} \preceq c\,\mathbf{H}$, for square matrices over any index type.
Mathlib's `smul_le_smul_of_nonneg_left` gives it for a finite index type. -/
theorem smul_le_smul_of_nonneg {G H : Matrix n n 𝕜} (h : G ≤ H) {c : ℝ} (hc : 0 ≤ c) :
    c • G ≤ c • H := by
  rw [Matrix.le_iff, ← smul_sub]
  exact (Matrix.le_iff.mp h).smul hc

open scoped NNReal in
/-- A Loewner bound on a weighted rank-one matrix (the row-sampling atom bound). For
$c \ge 0$ samples and a weight $w \ge 0$, the importance-weighted rank-one atom
$(c w)^{-1} \mathbf{b}^{\mathsf{H}} \mathbf{b}$ of a row $\mathbf{b}$ (`vecMulVec (star b) b`)
satisfies
$(c w)^{-1} \mathbf{b}^{\mathsf{H}} \mathbf{b} \preceq (L / c)\,\mathbf{I}$ when
$\|\mathbf{b}\|^2 \le L w$ and $L \ge 0$. Junk values: for $w = 0$ or $c = 0$ the atom is
$\mathbf{0}$ (junk inverse) and the bound is $\mathbf{0} \preceq (L / c)\,\mathbf{I}$. It is the
hypothesis `hle` of matrix Chernoff for row sampling, with or without replacement: with
replacement at $c = \lvert k \rvert$, $\mathbf{b}$ the sampled row and $w$ its weight; without
replacement at uniform weights. -/
theorem inv_mul_smul_vecMulVec_star_self_le {r : Type*} [Fintype r] [DecidableEq r] {c L : ℝ}
    {w : ℝ≥0} (hc : 0 ≤ c) (hL : 0 ≤ L) {b : r → 𝕜} (hb : ‖WithLp.toLp 2 b‖ ^ 2 ≤ L * w) :
    (c * w)⁻¹ • Matrix.vecMulVec (star b) b ≤ (L / c) • (1 : Matrix r r 𝕜) := by
  have hcw : (0 : ℝ) ≤ (c * w)⁻¹ := inv_nonneg.2 (mul_nonneg hc w.coe_nonneg)
  have hpsd : ((c * w)⁻¹ • Matrix.vecMulVec (star b) b).PosSemidef :=
    (Matrix.posSemidef_vecMulVec_star_self b).smul hcw
  refine hpsd.isHermitian.le_smul_one_of_specNorm_le ?_
  rw [specNorm_real_smul, specNorm_vecMulVec, EuclideanSpace.norm_toLp_star, abs_of_nonneg hcw,
    ← sq]
  rcases eq_or_ne w 0 with h0 | h0
  · rw [h0, NNReal.coe_zero, mul_zero, inv_zero, zero_mul]
    exact div_nonneg hL hc
  have hpos : 0 < (w : ℝ) := lt_of_le_of_ne w.coe_nonneg (by exact_mod_cast h0.symm)
  rcases hc.eq_or_lt with hk | hk
  · rw [← hk, zero_mul, inv_zero, zero_mul, div_zero]
  calc (c * w)⁻¹ * ‖WithLp.toLp 2 b‖ ^ 2 ≤ (c * w)⁻¹ * (L * w) :=
        mul_le_mul_of_nonneg_left hb hcw
    _ = L / c := by field_simp

end NLAlib
