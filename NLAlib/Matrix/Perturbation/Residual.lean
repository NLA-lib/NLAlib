/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Residual bounds for eigenvalues

A posteriori bounds: from an approximate eigenpair $(\mu, \mathbf{x})$ and its residual
$\mathbf{A}\mathbf{x} - \mu\mathbf{x}$ to the distance of $\mu$ from the spectrum. For Hermitian
matrices the residual bounds the distance to the nearest eigenvalue, the Rayleigh quotient
minimises the residual, and with a gap the error of the Rayleigh quotient is quadratic in the
residual (Kato–Temple). For diagonalisable matrices the bound carries the condition number of the
eigenvector matrix (Bauer–Fike).

## Main results

* `Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le`: an eigenvalue within the residual.
* `Matrix.IsHermitian.norm_mulVec_sub_rayleighQuotient_smul_le`: the Rayleigh quotient minimises
  the residual.
* `Matrix.IsHermitian.hasGradientAt_rayleighQuotient`: the real gradient is a scaled residual.
* `Matrix.IsHermitian.abs_sub_rayleighQuotient_mul_le_norm_sq`: the quadratic residual bound.
* `Matrix.IsHermitian.rayleighQuotient_sub_le_of_lt`,
  `Matrix.IsHermitian.le_rayleighQuotient_add_of_lt`: the Kato–Temple inequalities.
* `NLAlib.exists_norm_sub_le_pseudoConditionNumber_mul_specNorm`: the Bauer–Fike theorem.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Hermitian matrices -/

/-- Coordinates in an orthonormal eigenbasis of a Hermitian matrix: a map $T$ that preserves the
Euclidean norm and turns the squared norm of a shifted residual into a weighted sum. -/
private theorem exists_eigencoordinates_residual {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ T : (n → 𝕜) → Fin (Fintype.card n) → 𝕜,
      (∀ x, ‖WithLp.toLp 2 x‖ ^ 2 = ∑ j, ‖T x j‖ ^ 2) ∧
      ∀ (x : n → 𝕜) (μ : ℝ), ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ ^ 2 =
        ∑ j : Fin (Fintype.card n), (eigenvalue A j - μ) ^ 2 * ‖T x j‖ ^ 2 := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hU' : HasOrthonormalCols Uᴴ := hU.conjTranspose_of_card_eq (Fintype.card_fin _).symm
  refine ⟨fun x => Uᴴ *ᵥ x, fun x => ?_, fun x μ => ?_⟩
  · rw [← hU'.norm_toLp_mulVec x, EuclideanSpace.norm_sq_eq]
  · have h2 : Uᴴ *ᵥ (A *ᵥ x) =
        (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) *ᵥ
          (Uᴴ *ᵥ x) := by
      conv_lhs => rw [hAU]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hU.conjTranspose_mul_self, Matrix.one_mul]
    have h1 : Uᴴ *ᵥ (A *ᵥ x - μ • x) =
        fun j : Fin (Fintype.card n) => ((eigenvalue A j - μ : ℝ) : 𝕜) * (Uᴴ *ᵥ x) j := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h2]
      funext j
      rw [Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply, RCLike.real_smul_eq_coe_mul,
        RCLike.ofReal_sub, sub_mul]
    rw [← hU'.norm_toLp_mulVec, h1, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

/-- **An eigenvalue within the residual.** For Hermitian $\mathbf{A}$ with $\lvert n \rvert \ge 1$,
any vector $\mathbf{x}$ and any real $\mu$, some eigenvalue $\lambda_i(\mathbf{A})$,
$i < \lvert n \rvert$, satisfies $\lvert \lambda_i(\mathbf{A}) - \mu \rvert \, \|\mathbf{x}\|
\le \|\mathbf{A}\mathbf{x} - \mu\mathbf{x}\|$.
[Parlett1998, Theorem 4.5.1]. -/
theorem _root_.Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ∃ i, i < Fintype.card n ∧
      |eigenvalue A i - μ| * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_eigencoordinates_residual hA
  have : Nonempty (Fin (Fintype.card n)) := ⟨⟨0, Fintype.card_pos⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_min fun j : Fin (Fintype.card n) => |eigenvalue A j - μ|
  refine ⟨i, i.isLt, ?_⟩
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
  rw [mul_pow, hT₁, hT₂, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← sq_abs (eigenvalue A j - μ)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hi j) 2

/-- For Hermitian $\mathbf{A}$, the residual at the Rayleigh quotient $\rho$ of $\mathbf{x}$ is
orthogonal to $\mathbf{x}$: $\mathbf{x}^{\mathsf{H}}(\mathbf{A}\mathbf{x} - \rho\mathbf{x}) = 0$. -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_mulVec_sub_rayleighQuotient_smul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x - rayleighQuotient A x • x) = 0 := by
  rw [dotProduct_sub, dotProduct_smul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
    ← quadForm_def, ← hA.coe_re_quadForm, re_quadForm_eq_rayleighQuotient_mul,
    RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul, sub_self]

/-- **Gradient of the Rayleigh quotient.** For Hermitian $\mathbf{A}$ and nonzero
$\mathbf{x} \in \Bbbk^n$, let $\rho(\mathbf{x}) =
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) / \|\mathbf{x}\|_2^2$.
On the underlying real Euclidean space its gradient is
$$\nabla \rho(\mathbf{x}) = \frac{2}{\|\mathbf{x}\|_2^2}
  (\mathbf{A}\mathbf{x} - \rho(\mathbf{x})\mathbf{x}).$$
[TrefethenBau1997, (27.2), p. 203] gives the real symmetric case.
Result: eigenvalue-residual-bounds -/
theorem _root_.Matrix.IsHermitian.hasGradientAt_rayleighQuotient {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : EuclideanSpace 𝕜 n} (hx : x ≠ 0) :
    HasGradientAt (fun y : EuclideanSpace 𝕜 n => rayleighQuotient A y.ofLp)
      ((2 / ‖x‖ ^ 2) • (WithLp.toLp 2 (A *ᵥ x.ofLp) - rayleighQuotient A x.ofLp • x)) x := by
  classical
  let T := Matrix.toEuclideanCLM (𝕜 := 𝕜) A
  have hinner (v w : EuclideanSpace 𝕜 n) :
      inner ℝ v w = RCLike.re (inner 𝕜 v w) := by
    simp only [PiLp.inner_apply, map_sum]
    rfl
  have hsym : (T.restrictScalars ℝ).toLinearMap.IsSymmetric := fun v w => by
    rw [hinner, hinner]
    exact congrArg RCLike.re (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA v w)
  have hρ (y : EuclideanSpace 𝕜 n) :
      rayleighQuotient A y.ofLp = (T.restrictScalars ℝ).rayleighQuotient y := by
    rw [rayleighQuotient_eq_toEuclideanCLM, WithLp.toLp_ofLp]
    change _ / _ = inner ℝ (T y) y / _
    rw [hinner]
    rfl
  have hnum := (hsym.hasStrictFDerivAt_reApplyInnerSelf x).hasFDerivAt
  have hden := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hd := hnum.mul ((hasFDerivAt_inv hn).comp x hden)
  simp_rw [hρ]
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hd using 1
  ext y
  change inner ℝ ((2 / ‖x‖ ^ 2) • ((T.restrictScalars ℝ) x -
    (T.restrictScalars ℝ).rayleighQuotient x • x)) y = _
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    real_inner_smul_left, inner_sub_left, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Function.comp_apply]
  field_simp
  ring

/-- **Pythagoras for residuals.** For Hermitian $\mathbf{A}$, any vector $\mathbf{x}$ and real
$\mu$,
$$\|\mathbf{A}\mathbf{x} - \mu\mathbf{x}\|^2
  = \|\mathbf{A}\mathbf{x} - \rho\mathbf{x}\|^2 + (\mu - \rho)^2 \|\mathbf{x}\|^2,$$
with $\rho$ the Rayleigh quotient of $\mathbf{x}$.
[Saad2011, proof of Lemma 3.2] uses the orthogonality identity for a unit trial vector. -/
theorem _root_.Matrix.IsHermitian.norm_mulVec_sub_smul_sq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ ^ 2 =
      ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 +
        (μ - rayleighQuotient A x) ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 := by
  have hsplit : (WithLp.toLp 2 (A *ᵥ x - μ • x) : EuclideanSpace 𝕜 n) =
      WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x) +
        (rayleighQuotient A x - μ) • WithLp.toLp 2 x := by
    rw [← WithLp.toLp_smul, ← WithLp.toLp_add, sub_smul]
    abel_nf
  have horth : inner 𝕜 (WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x) : EuclideanSpace 𝕜 n)
      ((rayleighQuotient A x - μ) • WithLp.toLp 2 x) = 0 := by
    rw [inner_smul_right_eq_smul, EuclideanSpace.inner_toLp_toLp, Matrix.dotProduct_star,
      dotProduct_comm, hA.star_dotProduct_mulVec_sub_rayleighQuotient_smul, star_zero, smul_zero]
  rw [hsplit, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth, norm_smul,
    Real.norm_eq_abs]
  rw [← sq, ← sq, mul_pow, sq_abs, ← neg_sub μ, neg_sq]

/-- **The Rayleigh quotient minimises the residual** over real shifts: for Hermitian $\mathbf{A}$,
$\|\mathbf{A}\mathbf{x} - \rho\mathbf{x}\| \le \|\mathbf{A}\mathbf{x} - \mu\mathbf{x}\|$ for every
real $\mu$, with $\rho$ the Rayleigh quotient of $\mathbf{x}$.
[Parlett1998, §1.5]. -/
theorem _root_.Matrix.IsHermitian.norm_mulVec_sub_rayleighQuotient_smul_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [hA.norm_mulVec_sub_smul_sq x μ]
  exact le_add_of_nonneg_right (by positivity)

/-- If every eigenvalue lies outside the open interval between $\ell$ and $a$, the squared residual
of a unit vector at its Rayleigh quotient $\rho$ is at least $(\ell - \rho)(\rho - a)$. -/
private theorem sub_mul_sub_le_norm_sq {A : Matrix n n 𝕜} (hA : A.IsHermitian) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) {ℓ a : ℝ}
    (hp : ∀ i, i < Fintype.card n → 0 ≤ (eigenvalue A i - ℓ) * (eigenvalue A i - a)) :
    (ℓ - rayleighQuotient A x) * (rayleighQuotient A x - a) ≤
      ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_eigencoordinates_residual hA
  have h1 : ((ℓ - a) / 2) ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      ‖WithLp.toLp 2 (A *ᵥ x - ((ℓ + a) / 2) • x)‖ ^ 2 := by
    rw [hT₁, hT₂, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hp j j.isLt]
  have h2 := hA.norm_mulVec_sub_smul_sq x ((ℓ + a) / 2)
  rw [hx] at h1 h2
  nlinarith

/-- **The quadratic residual bound.** Let $\mathbf{A}$ be Hermitian, $\mathbf{x}$ a unit vector with
Rayleigh quotient $\rho$, $\delta > 0$, and $\ell$ a number with
$\lvert \ell - \rho \rvert < \delta$ such that every eigenvalue $\lambda_i(\mathbf{A})$ with
$\lvert \lambda_i(\mathbf{A}) - \rho \rvert < \delta$ equals $\ell$. Then
$\lvert \ell - \rho \rvert \, \delta \le \|\mathbf{A}\mathbf{x} - \rho\mathbf{x}\|^2$.
[Parlett1998, Theorem 11.7.1]. -/
theorem _root_.Matrix.IsHermitian.abs_sub_rayleighQuotient_mul_le_norm_sq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) {ℓ δ : ℝ} (hδ : 0 < δ)
    (hℓ : |ℓ - rayleighQuotient A x| < δ)
    (hiso : ∀ i, i < Fintype.card n → |eigenvalue A i - rayleighQuotient A x| < δ →
      eigenvalue A i = ℓ) :
    |ℓ - rayleighQuotient A x| * δ ≤
      ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 := by
  obtain ⟨hℓ₁, hℓ₂⟩ := abs_lt.mp hℓ
  have hp : ∀ a, |a - rayleighQuotient A x| = δ → ∀ i, i < Fintype.card n →
      0 ≤ (eigenvalue A i - ℓ) * (eigenvalue A i - a) := by
    intro a ha i hi
    by_cases h : |eigenvalue A i - rayleighQuotient A x| < δ
    · rw [hiso i hi h, sub_self, zero_mul]
    · rw [not_lt, le_abs'] at h
      rcases eq_or_eq_neg_of_abs_eq ha with ha | ha <;> rcases h with h | h <;> nlinarith
  have h1 := sub_mul_sub_le_norm_sq hA hx
    (hp (rayleighQuotient A x - δ) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ]))
  have h2 := sub_mul_sub_le_norm_sq hA hx
    (hp (rayleighQuotient A x + δ) (by rw [add_sub_cancel_left, abs_of_pos hδ]))
  rw [sub_sub_cancel] at h1
  rw [sub_add_cancel_left] at h2
  rcases abs_cases (ℓ - rayleighQuotient A x) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- The sign condition behind the Kato–Temple inequalities: if $\ell \in (\alpha, \beta)$ and
$t = \ell$ whenever $t \in (\alpha, \beta)$, then $(t - \ell)(t - a) \ge 0$ for each endpoint $a$ of
$(\alpha, \beta)$. -/
private theorem sub_mul_sub_nonneg_of_isolated {α β ℓ t a : ℝ} (hαℓ : α < ℓ) (hℓβ : ℓ < β)
    (ha : a = α ∨ a = β) (hiso : α < t → t < β → t = ℓ) : 0 ≤ (t - ℓ) * (t - a) := by
  by_cases h₁ : α < t
  · by_cases h₂ : t < β
    · rw [hiso h₁ h₂, sub_self, zero_mul]
    · rcases ha with rfl | rfl <;> nlinarith
  · rcases ha with rfl | rfl <;> nlinarith

/-- **Kato–Temple, lower bound.** Let $\mathbf{A}$ be Hermitian, $\mathbf{x}$ a unit vector with
Rayleigh quotient $\rho < \beta$, and $\ell \in (\alpha, \beta)$ such that no eigenvalue other than
$\ell$ lies in $(\alpha, \beta)$. Then
$$\rho - \frac{\|\mathbf{A}\mathbf{x} - \rho\mathbf{x}\|^2}{\beta - \rho} \le \ell.$$
The bound $\alpha < \rho$ of the classical statement is not needed.
[Parlett1998, §11.7]; [Kato1995, §I.6 context]. -/
theorem _root_.Matrix.IsHermitian.rayleighQuotient_sub_le_of_lt {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) {α β ℓ : ℝ}
    (hρβ : rayleighQuotient A x < β) (hαℓ : α < ℓ) (hℓβ : ℓ < β)
    (hiso : ∀ i, i < Fintype.card n → α < eigenvalue A i → eigenvalue A i < β →
      eigenvalue A i = ℓ) :
    rayleighQuotient A x -
        ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 / (β - rayleighQuotient A x) ≤
      ℓ := by
  have h := sub_mul_sub_le_norm_sq hA hx (ℓ := ℓ) (a := β) fun i hi =>
    sub_mul_sub_nonneg_of_isolated hαℓ hℓβ (Or.inr rfl) (hiso i hi)
  have hd : 0 < β - rayleighQuotient A x := sub_pos.mpr hρβ
  rw [sub_le_comm, le_div_iff₀ hd]
  linarith

/-- **Kato–Temple, upper bound**: for Hermitian $\mathbf{A}$, a unit vector $\mathbf{x}$ with
Rayleigh quotient $\rho > \alpha$, and $\ell \in (\alpha, \beta)$ such that no eigenvalue other than
$\ell$ lies in $(\alpha, \beta)$,
$$\ell \le \rho + \frac{\|\mathbf{A}\mathbf{x} - \rho\mathbf{x}\|^2}{\rho - \alpha}.$$
The bound $\rho < \beta$ of the classical statement is not needed.
[Saad2011, Theorem 3.8]. -/
theorem _root_.Matrix.IsHermitian.le_rayleighQuotient_add_of_lt {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) {α β ℓ : ℝ}
    (hαρ : α < rayleighQuotient A x) (hαℓ : α < ℓ) (hℓβ : ℓ < β)
    (hiso : ∀ i, i < Fintype.card n → α < eigenvalue A i → eigenvalue A i < β →
      eigenvalue A i = ℓ) :
    ℓ ≤ rayleighQuotient A x +
      ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 / (rayleighQuotient A x - α) := by
  have h := sub_mul_sub_le_norm_sq hA hx (ℓ := ℓ) (a := α) fun i hi =>
    sub_mul_sub_nonneg_of_isolated hαℓ hℓβ (Or.inl rfl) (hiso i hi)
  have hd : 0 < rayleighQuotient A x - α := sub_pos.mpr hαρ
  rw [← sub_le_iff_le_add', le_div_iff₀ hd]
  exact h

/-! ### Diagonalisable matrices -/

variable [DecidableEq n]

/-- **Bauer–Fike, residual form.** If
$\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and
$\lvert n \rvert \ge 1$, then for any vector $\mathbf{x}$ and scalar $\mu$ some $\mathbf{d}_i$
satisfies $\lvert \mathbf{d}_i - \mu \rvert \, \|\mathbf{x}\|
\le \kappa(\mathbf{V}) \, \|\mathbf{A}\mathbf{x} - \mu\mathbf{x}\|$.
[GolubVanLoan2013, Theorem 7.2.2]; [HornJohnson2013, Theorem 6.3.2].
-/
theorem exists_norm_sub_mul_norm_le_pseudoConditionNumber_mul [Nonempty n] {A V : Matrix n n 𝕜}
    {d : n → 𝕜} (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal d) (x : n → 𝕜) (μ : 𝕜) :
    ∃ i, ‖d i - μ‖ * ‖WithLp.toLp 2 x‖ ≤
      pseudoConditionNumber V * ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  obtain ⟨i, hi⟩ := Finite.exists_min fun j => ‖d j - μ‖
  refine ⟨i, ?_⟩
  have hx : V *ᵥ (V⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hdet, Matrix.one_mulVec]
  have hres : V⁻¹ *ᵥ (A *ᵥ x - μ • x) = fun j => (d j - μ) * (V⁻¹ *ᵥ x) j := by
    have h1 : V⁻¹ *ᵥ (A *ᵥ x) = Matrix.diagonal d *ᵥ (V⁻¹ *ᵥ x) := by
      have h2 : A *ᵥ x = (V * Matrix.diagonal d) *ᵥ (V⁻¹ *ᵥ x) := by
        rw [← hA, ← Matrix.mulVec_mulVec, hx]
      rw [h2, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul V hdet,
        Matrix.one_mul]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h1]
    funext j
    rw [Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, sub_mul]
  have h1 : ‖d i - μ‖ * ‖WithLp.toLp 2 (V⁻¹ *ᵥ x)‖ ≤
      ‖WithLp.toLp 2 (V⁻¹ *ᵥ (A *ᵥ x - μ • x))‖ := by
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
    rw [hres, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hi j) 2) (sq_nonneg _)
  calc ‖d i - μ‖ * ‖WithLp.toLp 2 x‖
      = ‖d i - μ‖ * ‖WithLp.toLp 2 (V *ᵥ (V⁻¹ *ᵥ x))‖ := by rw [hx]
    _ ≤ ‖d i - μ‖ * (specNorm V * ‖WithLp.toLp 2 (V⁻¹ *ᵥ x)‖) :=
        mul_le_mul_of_nonneg_left (norm_toLp_mulVec_le _ _) (norm_nonneg _)
    _ = specNorm V * (‖d i - μ‖ * ‖WithLp.toLp 2 (V⁻¹ *ᵥ x)‖) := by ring
    _ ≤ specNorm V * (specNorm V⁻¹ * ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖) :=
        mul_le_mul_of_nonneg_left (h1.trans (norm_toLp_mulVec_le _ _)) (specNorm_nonneg _)
    _ = pseudoConditionNumber V * ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
        rw [pseudoConditionNumber_of_isUnit hV, mul_assoc]

/-- **The Bauer–Fike theorem.** If
$\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
every eigenvalue $\mu$ in the base field of $\mathbf{A} + \mathbf{E}$ satisfies
$\lvert \mathbf{d}_i - \mu \rvert \le \kappa(\mathbf{V}) \|\mathbf{E}\|_2$ for some $i$.
[GolubVanLoan2013, Theorem 7.2.2]; [HornJohnson2013, Theorem 6.3.2].
Result: bauer-fike -/
theorem exists_norm_sub_le_pseudoConditionNumber_mul_specNorm {A V E : Matrix n n 𝕜} {d : n → 𝕜}
    (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal d) {x : n → 𝕜} (hx : x ≠ 0) {μ : 𝕜}
    (hμ : (A + E) *ᵥ x = μ • x) :
    ∃ i, ‖d i - μ‖ ≤ pseudoConditionNumber V * specNorm E := by
  have : Nonempty n := not_isEmpty_iff.mp fun h => hx (Subsingleton.elim _ _)
  obtain ⟨i, hi⟩ := exists_norm_sub_mul_norm_le_pseudoConditionNumber_mul hV hA x μ
  refine ⟨i, ?_⟩
  have hres : A *ᵥ x - μ • x = -(E *ᵥ x) := by
    rw [← hμ, Matrix.add_mulVec, sub_add_cancel_left]
  have hxpos : 0 < ‖WithLp.toLp 2 x‖ := by
    rw [norm_pos_iff]
    exact fun h => hx (congrArg WithLp.ofLp h)
  rw [hres, WithLp.toLp_neg, norm_neg] at hi
  refine le_of_mul_le_mul_right (hi.trans ?_) hxpos
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_toLp_mulVec_le _ _) (pseudoConditionNumber_nonneg _)

/-- The diagonal entries of a diagonalisation are eigenvalues: if
$\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
each $\mathbf{d}_i$ is an eigenvalue of $\mathbf{A}$. -/
theorem mem_spectrum_of_mul_eq_mul_diagonal {A V : Matrix n n 𝕜} {d : n → 𝕜} (hV : IsUnit V)
    (hA : A * V = V * Matrix.diagonal d) (i : n) : d i ∈ spectrum 𝕜 A := by
  have hcol : V.col i ≠ 0 := (Matrix.linearIndependent_cols_iff_isUnit.mpr hV).ne_zero i
  have hAi : A *ᵥ V.col i = d i • V.col i := by
    funext j
    have h := congrFun (congrFun hA j) i
    rw [Matrix.mul_diagonal] at h
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    exact h
  intro hu
  apply hcol
  have h0 : (algebraMap 𝕜 (Matrix n n 𝕜) (d i) - A) *ᵥ V.col i = 0 := by
    rw [Matrix.sub_mulVec, hAi, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_self]
  have h1 := congrArg (fun v => (algebraMap 𝕜 (Matrix n n 𝕜) (d i) - A)⁻¹ *ᵥ v) h0
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
  rwa [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu),
    Matrix.one_mulVec] at h1

/-! ### Deprecated aliases -/

@[deprecated exists_norm_sub_mul_norm_le_pseudoConditionNumber_mul (since := "2026-10-14")]
alias exists_norm_sub_mul_norm_le_conditionNumber_mul :=
  exists_norm_sub_mul_norm_le_pseudoConditionNumber_mul

@[deprecated exists_norm_sub_le_pseudoConditionNumber_mul_specNorm (since := "2026-10-14")]
alias exists_norm_sub_le_conditionNumber_mul_specNorm :=
  exists_norm_sub_le_pseudoConditionNumber_mul_specNorm

end NLAlib
