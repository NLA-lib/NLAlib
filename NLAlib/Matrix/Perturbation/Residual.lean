/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Residual bounds for eigenvalues

A posteriori bounds: from an approximate eigenpair `(μ, x)` and its residual `A x - μ x` to the
distance of `μ` from the spectrum. For Hermitian matrices the residual bounds the distance to the
nearest eigenvalue, the Rayleigh quotient minimises the residual, and with a gap the error of the
Rayleigh quotient is quadratic in the residual (Kato–Temple). For diagonalisable matrices the
bound carries the condition number of the eigenvector matrix (Bauer–Fike).

## Main results

* `Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le`: an eigenvalue within the residual.
* `Matrix.IsHermitian.norm_mulVec_sub_rayleighQuotient_smul_le`: the Rayleigh quotient minimises
  the residual.
* `Matrix.IsHermitian.abs_sub_rayleighQuotient_mul_le_norm_sq`: the quadratic residual bound.
* `Matrix.IsHermitian.rayleighQuotient_sub_le_of_lt`,
  `Matrix.IsHermitian.le_rayleighQuotient_add_of_lt`: the Kato–Temple inequalities.
* `NLAlib.exists_norm_sub_le_conditionNumber_mul_specNorm`: the Bauer–Fike theorem.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Hermitian matrices -/

/-- Coordinates in an orthonormal eigenbasis of a Hermitian matrix: a map `T` that preserves the
Euclidean norm and turns the squared norm of a shifted residual into a weighted sum. -/
private theorem exists_eigencoordinates {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
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

/-- **An eigenvalue within the residual.** For Hermitian `A`, any vector `x` and any real `μ`,
some eigenvalue satisfies `|λ_i - μ| ‖x‖ ≤ ‖A x - μ x‖`.
[Parlett1998, Theorem 4.5.1].
Port of `NLAlib.exists_eigenvalue_abs_sub_le_residual`, there over `ℝ` for unit vectors. -/
theorem _root_.Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ∃ i, i < Fintype.card n ∧
      |eigenvalue A i - μ| * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_eigencoordinates hA
  have : Nonempty (Fin (Fintype.card n)) := ⟨⟨0, Fintype.card_pos⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_min fun j : Fin (Fintype.card n) => |eigenvalue A j - μ|
  refine ⟨i, i.isLt, ?_⟩
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
  rw [mul_pow, hT₁, hT₂, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← sq_abs (eigenvalue A j - μ)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hi j) 2

/-- The residual at the Rayleigh quotient is orthogonal to the vector.
Port of `NLAlib.dotProduct_rayleigh_residual_eq_zero`. -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_mulVec_sub_rayleighQuotient_smul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x - rayleighQuotient A x • x) = 0 := by
  rw [dotProduct_sub, dotProduct_smul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
    ← quadForm_def, ← hA.coe_re_quadForm, re_quadForm_eq_rayleighQuotient_mul,
    RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul, sub_self]

/-- **Pythagoras for residuals.** For Hermitian `A` and real `μ`,
`‖A x - μ x‖² = ‖A x - ρ x‖² + (μ - ρ)² ‖x‖²` with `ρ` the Rayleigh quotient.
Port of `NLAlib.dotProduct_shifted_residual_eq_rayleigh_add_sq`. -/
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

/-- **The Rayleigh quotient minimises the residual** over real shifts.
[Parlett1998, §1.5]. Port of `NLAlib.rayleigh_residual_le_shifted_residual`. -/
theorem _root_.Matrix.IsHermitian.norm_mulVec_sub_rayleighQuotient_smul_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [hA.norm_mulVec_sub_smul_sq x μ]
  exact le_add_of_nonneg_right (by positivity)

/-- If every eigenvalue lies outside the open interval between `ℓ` and `a`, the squared residual
of a unit vector at its Rayleigh quotient `ρ` is at least `(ℓ - ρ) (ρ - a)`. -/
private theorem sub_mul_sub_le_norm_sq {A : Matrix n n 𝕜} (hA : A.IsHermitian) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) {ℓ a : ℝ}
    (hp : ∀ i, i < Fintype.card n → 0 ≤ (eigenvalue A i - ℓ) * (eigenvalue A i - a)) :
    (ℓ - rayleighQuotient A x) * (rayleighQuotient A x - a) ≤
      ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_eigencoordinates hA
  have h1 : ((ℓ - a) / 2) ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      ‖WithLp.toLp 2 (A *ᵥ x - ((ℓ + a) / 2) • x)‖ ^ 2 := by
    rw [hT₁, hT₂, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hp j j.isLt]
  have h2 := hA.norm_mulVec_sub_smul_sq x ((ℓ + a) / 2)
  rw [hx] at h1 h2
  nlinarith

/-- **The quadratic residual bound.** Let `A` be Hermitian, `x` a unit vector with Rayleigh
quotient `ρ`, and `ℓ` a number within `δ` of `ρ` such that no eigenvalue other than `ℓ` is
within `δ` of `ρ`. Then
`|ℓ - ρ| δ ≤ ‖A x - ρ x‖²`.
[Parlett1998, Theorem 11.7.1].
Port of `NLAlib.abs_eigenvalue_sub_rayleigh_le_residual_sq_div`, there over `ℝ`. -/
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

/-- The sign condition behind the Kato–Temple inequalities: if `ℓ` is the only eigenvalue in
`(α, β)`, then `(λ_i - ℓ) (λ_i - a) ≥ 0` for every eigenvalue and each endpoint `a`. -/
private theorem sub_mul_sub_nonneg_of_isolated {α β ℓ t a : ℝ} (hαℓ : α < ℓ) (hℓβ : ℓ < β)
    (ha : a = α ∨ a = β) (hiso : α < t → t < β → t = ℓ) : 0 ≤ (t - ℓ) * (t - a) := by
  by_cases h₁ : α < t
  · by_cases h₂ : t < β
    · rw [hiso h₁ h₂, sub_self, zero_mul]
    · rcases ha with rfl | rfl <;> nlinarith
  · rcases ha with rfl | rfl <;> nlinarith

/-- **Kato–Temple, lower bound.** Let `A` be Hermitian, `x` a unit vector with Rayleigh quotient
`ρ < β`, and `ℓ ∈ (α, β)` such that no eigenvalue other than `ℓ` lies in `(α, β)`. Then
`ρ - ‖A x - ρ x‖² / (β - ρ) ≤ ℓ`. The bound `α < ρ` of the classical statement is not needed.
[Parlett1998, §11.7]; [Kato1995, §I.6 context]. Port of `NLAlib.kato_temple_le_eigenvalue`. -/
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

/-- **Kato–Temple, upper bound**: `ℓ ≤ ρ + ‖A x - ρ x‖² / (ρ - α)`, for `α < ρ` and `ℓ ∈ (α, β)`
the only eigenvalue in `(α, β)`. The bound `ρ < β` of the classical statement is not needed.
Port of `NLAlib.kato_temple_eigenvalue_le`. -/
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

/-- **Bauer–Fike, residual form.** If `A * V = V * diagonal d` with `V` invertible, then for any
vector `x` and scalar `μ` some `d i` satisfies `‖d i - μ‖ ‖x‖ ≤ κ(V) ‖A x - μ x‖`.
[GolubVanLoan2013, Theorem 7.2.2]; [HornJohnson2013, Theorem 6.3.2].
Port of `NLAlib.exists_eigenvalue_distance_mul_euclidean_norm_le_residual`, there over `ℂ`. -/
theorem exists_norm_sub_mul_norm_le_conditionNumber_mul [Nonempty n] {A V : Matrix n n 𝕜}
    {d : n → 𝕜} (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal d) (x : n → 𝕜) (μ : 𝕜) :
    ∃ i, ‖d i - μ‖ * ‖WithLp.toLp 2 x‖ ≤
      conditionNumber V * ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
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
    _ = conditionNumber V * ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
        rw [conditionNumber_of_isUnit hV, mul_assoc]

/-- **The Bauer–Fike theorem.** If `A * V = V * diagonal d` with `V` invertible, every eigenvalue
`μ` of `A + E` is within `κ(V) ‖E‖₂` of some `d i`.
[GolubVanLoan2013, Theorem 7.2.2]; [HornJohnson2013, Theorem 6.3.2].
Port of `NLAlib.exists_eigenvalue_distance_le_euclidean_residual_div`, there over `ℂ`.
Result: bauer-fike -/
theorem exists_norm_sub_le_conditionNumber_mul_specNorm {A V E : Matrix n n 𝕜} {d : n → 𝕜}
    (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal d) {x : n → 𝕜} (hx : x ≠ 0) {μ : 𝕜}
    (hμ : (A + E) *ᵥ x = μ • x) :
    ∃ i, ‖d i - μ‖ ≤ conditionNumber V * specNorm E := by
  have : Nonempty n := not_isEmpty_iff.mp fun h => hx (Subsingleton.elim _ _)
  obtain ⟨i, hi⟩ := exists_norm_sub_mul_norm_le_conditionNumber_mul hV hA x μ
  refine ⟨i, ?_⟩
  have hres : A *ᵥ x - μ • x = -(E *ᵥ x) := by
    rw [← hμ, Matrix.add_mulVec, sub_add_cancel_left]
  have hxpos : 0 < ‖WithLp.toLp 2 x‖ := by
    rw [norm_pos_iff]
    exact fun h => hx (congrArg WithLp.ofLp h)
  rw [hres, WithLp.toLp_neg, norm_neg] at hi
  refine le_of_mul_le_mul_right (hi.trans ?_) hxpos
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_toLp_mulVec_le _ _) (conditionNumber_nonneg _)

/-- The diagonal entries of a diagonalisation are eigenvalues.
Port of `NLAlib.mem_spectrum_of_diagonal_intertwining`. -/
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

end NLAlib
