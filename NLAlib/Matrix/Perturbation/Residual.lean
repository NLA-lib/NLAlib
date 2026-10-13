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

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Hermitian matrices -/

/-- **An eigenvalue within the residual.** For Hermitian `A`, any vector `x` and any real `μ`,
some eigenvalue satisfies `|λ_i - μ| ‖x‖ ≤ ‖A x - μ x‖`.
[Parlett1998, Theorem 4.5.1].
Port of `NLAlib.exists_eigenvalue_abs_sub_le_residual`, there over `ℝ` for unit vectors. -/
theorem _root_.Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ∃ i, i < Fintype.card n ∧
      |eigenvalue A i - μ| * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
  sorry

/-- The residual at the Rayleigh quotient is orthogonal to the vector.
Port of `NLAlib.dotProduct_rayleigh_residual_eq_zero`. -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_mulVec_sub_rayleighQuotient_smul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x - rayleighQuotient A x • x) = 0 := by
  sorry

/-- **Pythagoras for residuals.** For Hermitian `A` and real `μ`,
`‖A x - μ x‖² = ‖A x - ρ x‖² + (μ - ρ)² ‖x‖²` with `ρ` the Rayleigh quotient.
Port of `NLAlib.dotProduct_shifted_residual_eq_rayleigh_add_sq`. -/
theorem _root_.Matrix.IsHermitian.norm_mulVec_sub_smul_sq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ ^ 2 =
      ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 +
        (μ - rayleighQuotient A x) ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

/-- **The Rayleigh quotient minimises the residual** over real shifts.
[Parlett1998, §1.5]. Port of `NLAlib.rayleigh_residual_le_shifted_residual`. -/
theorem _root_.Matrix.IsHermitian.norm_mulVec_sub_rayleighQuotient_smul_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
  sorry

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
  sorry

/-- **Kato–Temple, lower bound.** Let `A` be Hermitian, `x` a unit vector with Rayleigh quotient
`ρ ∈ (α, β)`, and `ℓ ∈ (α, β)` such that no eigenvalue other than `ℓ` lies in `(α, β)`. Then
`ρ - ‖A x - ρ x‖² / (β - ρ) ≤ ℓ`.
[Parlett1998, §11.7]; [Kato1995, §I.6 context]. Port of `NLAlib.kato_temple_le_eigenvalue`. -/
theorem _root_.Matrix.IsHermitian.rayleighQuotient_sub_le_of_lt {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) {α β ℓ : ℝ}
    (hαρ : α < rayleighQuotient A x) (hρβ : rayleighQuotient A x < β) (hαℓ : α < ℓ)
    (hℓβ : ℓ < β)
    (hiso : ∀ i, i < Fintype.card n → α < eigenvalue A i → eigenvalue A i < β →
      eigenvalue A i = ℓ) :
    rayleighQuotient A x -
        ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 / (β - rayleighQuotient A x) ≤
      ℓ := by
  sorry

/-- **Kato–Temple, upper bound**: `ℓ ≤ ρ + ‖A x - ρ x‖² / (ρ - α)`.
Port of `NLAlib.kato_temple_eigenvalue_le`. -/
theorem _root_.Matrix.IsHermitian.le_rayleighQuotient_add_of_lt {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) {α β ℓ : ℝ}
    (hαρ : α < rayleighQuotient A x) (hρβ : rayleighQuotient A x < β) (hαℓ : α < ℓ)
    (hℓβ : ℓ < β)
    (hiso : ∀ i, i < Fintype.card n → α < eigenvalue A i → eigenvalue A i < β →
      eigenvalue A i = ℓ) :
    ℓ ≤ rayleighQuotient A x +
      ‖WithLp.toLp 2 (A *ᵥ x - rayleighQuotient A x • x)‖ ^ 2 / (rayleighQuotient A x - α) := by
  sorry

/-! ### Diagonalisable matrices -/

/-- **Bauer–Fike, residual form.** If `A * V = V * diagonal d` with `V` invertible, then for any
vector `x` and scalar `μ` some `d i` satisfies `‖d i - μ‖ ‖x‖ ≤ κ(V) ‖A x - μ x‖`.
[GolubVanLoan2013, Theorem 7.2.2]; [HornJohnson2013, Theorem 6.3.2].
Port of `NLAlib.exists_eigenvalue_distance_mul_euclidean_norm_le_residual`, there over `ℂ`. -/
theorem exists_norm_sub_mul_norm_le_conditionNumber_mul [Nonempty n] {A V : Matrix n n 𝕜}
    {d : n → 𝕜} (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal d) (x : n → 𝕜) (μ : 𝕜) :
    ∃ i, ‖d i - μ‖ * ‖WithLp.toLp 2 x‖ ≤
      conditionNumber V * ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖ := by
  sorry

/-- **The Bauer–Fike theorem.** If `A * V = V * diagonal d` with `V` invertible, every eigenvalue
`μ` of `A + E` is within `κ(V) ‖E‖₂` of some `d i`.
[GolubVanLoan2013, Theorem 7.2.2]; [HornJohnson2013, Theorem 6.3.2].
Port of `NLAlib.exists_eigenvalue_distance_le_euclidean_residual_div`, there over `ℂ`.
Result: bauer-fike -/
theorem exists_norm_sub_le_conditionNumber_mul_specNorm {A V E : Matrix n n 𝕜} {d : n → 𝕜}
    (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal d) {x : n → 𝕜} (hx : x ≠ 0) {μ : 𝕜}
    (hμ : (A + E) *ᵥ x = μ • x) :
    ∃ i, ‖d i - μ‖ ≤ conditionNumber V * specNorm E := by
  sorry

/-- The diagonal entries of a diagonalisation are eigenvalues.
Port of `NLAlib.mem_spectrum_of_diagonal_intertwining`. -/
theorem mem_spectrum_of_mul_eq_mul_diagonal {A V : Matrix n n 𝕜} {d : n → 𝕜} (hV : IsUnit V)
    (hA : A * V = V * Matrix.diagonal d) (i : n) : d i ∈ spectrum 𝕜 A := by
  sorry

end NLAlib
