/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import NLAlib.Matrix.Spectral.Normal
public import NLAlib.Matrix.Spectral.Gershgorin

/-!
# The spectral radius and powers of a matrix

The spectral radius of a square matrix over `𝕜` is the largest modulus of a complex eigenvalue,
`NLAlib.specRadius A`, defined through Mathlib's `spectralRadius` of the complexification. It is
at most the spectral norm, with equality for normal matrices; it is the limit of
`‖Aᵏ‖^{1/k}` (Gelfand); the powers of `A` tend to zero exactly when it is less than one, in which
case the Neumann series converges; and the powers stay bounded exactly when it is at most one and
the eigenvalues of modulus one are semisimple.

## Main definitions

* `NLAlib.specRadius`: the spectral radius, a real number.

## Main results

* `NLAlib.specRadius_le_specNorm`, `IsStarNormal.specNorm_eq_specRadius`.
* `NLAlib.tendsto_specNorm_pow_rpow_specRadius`: Gelfand's formula.
* `NLAlib.tendsto_pow_zero_iff_specRadius_lt_one`.
* `NLAlib.hasSum_pow_inv_one_sub_of_specRadius_lt_one`: the Neumann series.
* `NLAlib.exists_forall_specNorm_pow_le_mul_pow`: growth of the powers.
* `NLAlib.exists_forall_specNorm_pow_le_iff`: power-bounded matrices.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial Filter Topology

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **spectral radius** of a square matrix: the largest modulus of a complex eigenvalue, zero
for a matrix of size zero. [HornJohnson2013, Definition 1.2.9]. -/
noncomputable def specRadius (A : Matrix n n 𝕜) : ℝ :=
  (spectralRadius ℂ (complexify A)).toReal

/-- The spectral radius is nonnegative. -/
theorem specRadius_nonneg (A : Matrix n n 𝕜) : 0 ≤ specRadius A := by
  sorry

/-- Every eigenvalue is at most the spectral radius in modulus. -/
theorem norm_le_specRadius_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A) :
    ‖μ‖ ≤ specRadius A := by
  sorry

/-- **The spectral radius through a listing of the eigenvalues.** -/
theorem specRadius_le_iff_of_charpoly_eq {A : Matrix n n 𝕜} {d : n → ℂ}
    (hd : (complexify A).charpoly = ∏ i, (X - C (d i))) {c : ℝ} (hc : 0 ≤ c) :
    specRadius A ≤ c ↔ ∀ i, ‖d i‖ ≤ c := by
  sorry

/-- The spectral radius is attained at an eigenvalue of the complexification. -/
theorem exists_mem_spectrum_norm_eq_specRadius [Nonempty n] (A : Matrix n n 𝕜) :
    ∃ μ ∈ spectrum ℂ (complexify A), ‖μ‖ = specRadius A := by
  sorry

/-- **The spectral radius is at most the spectral norm.** [HornJohnson2013, Theorem 5.6.9]. -/
theorem specRadius_le_specNorm (A : Matrix n n 𝕜) : specRadius A ≤ specNorm A := by
  sorry

/-- The spectral radius of a power. -/
theorem specRadius_pow (A : Matrix n n 𝕜) (k : ℕ) : specRadius (A ^ k) = specRadius A ^ k := by
  sorry

/-- The spectral radius is invariant under similarity. -/
theorem specRadius_inv_mul_mul (A : Matrix n n 𝕜) {S : Matrix n n 𝕜} (hS : IsUnit S.det) :
    specRadius (S⁻¹ * A * S) = specRadius A := by
  sorry

/-- `A B` and `B A` have the same spectral radius. -/
theorem specRadius_mul_comm (A B : Matrix n n 𝕜) : specRadius (A * B) = specRadius (B * A) := by
  sorry

/-- **The spectral norm of a normal matrix is its spectral radius.**
[HornJohnson2013, §5.6]. -/
theorem _root_.IsStarNormal.specNorm_eq_specRadius {A : Matrix n n 𝕜} (hA : IsStarNormal A) :
    specNorm A = specRadius A := by
  sorry

/-- The spectral radius is at most the largest row sum.
Port of `NLAlib.spectralRadius_le_max_row_sum`. -/
theorem specRadius_le_of_forall_sum_le {A : Matrix n n 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, ‖A i j‖ ≤ c) : specRadius A ≤ c := by
  sorry

/-- The spectral radius of commuting matrices is subadditive and submultiplicative. -/
theorem specRadius_add_le_of_commute {A B : Matrix n n 𝕜} (h : Commute A B) :
    specRadius (A + B) ≤ specRadius A + specRadius B := by
  sorry

/-- The spectral radius of a product of commuting matrices is at most the product. -/
theorem specRadius_mul_le_of_commute {A B : Matrix n n 𝕜} (h : Commute A B) :
    specRadius (A * B) ≤ specRadius A * specRadius B := by
  sorry

/-! ### Powers -/

/-- **Gelfand's formula**: `‖Aᵏ‖₂^{1/k}` tends to the spectral radius.
[HornJohnson2013, Corollary 5.6.14].
Port of `NLAlib.tendsto_norm_matrix_pow_rpow_spectralRadius`, there over `ℂ`.
Result: gelfand-formula -/
theorem tendsto_specNorm_pow_rpow_specRadius (A : Matrix n n 𝕜) :
    Tendsto (fun k : ℕ => specNorm (A ^ k) ^ (1 / (k : ℝ))) atTop (𝓝 (specRadius A)) := by
  sorry

/-- The spectral radius bounds the powers from below: `ρ(A)ᵏ ≤ ‖Aᵏ‖₂`. -/
theorem specRadius_pow_le_specNorm_pow (A : Matrix n n 𝕜) (k : ℕ) :
    specRadius A ^ k ≤ specNorm (A ^ k) := by
  sorry

/-- **Growth of the powers**: for every `ε > 0`, `‖Aᵏ‖₂ ≤ C (ρ(A) + ε)ᵏ` for some `C`.
[HornJohnson2013, Corollary 5.6.13].
Port of `NLAlib.exists_prefix_norm_matrix_pow_le_spectralRadius_add`. -/
theorem exists_forall_specNorm_pow_le_mul_pow (A : Matrix n n 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, specNorm (A ^ k) ≤ C * (specRadius A + ε) ^ k := by
  sorry

/-- **The powers of a matrix tend to zero exactly when its spectral radius is less than one.**
[HornJohnson2013, Theorem 5.6.12].
Port of `NLAlib.tendsto_matrix_pow_zero_iff_spectralRadius_lt_one`, there over `ℂ`.
Result: convergent-matrix -/
theorem tendsto_pow_zero_iff_specRadius_lt_one (A : Matrix n n 𝕜) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) ↔ specRadius A < 1 := by
  sorry

/-- **The Neumann series** converges to `(1 - A)⁻¹` when the spectral radius is less than one.
[HornJohnson2013, Corollary 5.6.16].
Port of `NLAlib.hasSum_matrix_pow_inv_of_spectralRadius_lt_one`. -/
theorem hasSum_pow_inv_one_sub_of_specRadius_lt_one {A : Matrix n n 𝕜}
    (hA : specRadius A < 1) : HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹ := by
  sorry

/-- `1 - A` is invertible when the spectral radius of `A` is less than one.
Port of `NLAlib.isUnit_one_sub_of_matrix_spectralRadius_lt_one`. -/
theorem isUnit_det_one_sub_of_specRadius_lt_one {A : Matrix n n 𝕜} (hA : specRadius A < 1) :
    IsUnit (1 - A).det := by
  sorry

/-- **A similarity brings the spectral norm within `ε` of the spectral radius.**
[HornJohnson2013, Lemma 5.6.10]. -/
theorem exists_specNorm_inv_mul_mul_le (A : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ specNorm (S⁻¹ * A * S) ≤ specRadius A + ε := by
  sorry

/-- **Power-bounded matrices.** The powers of `A` are bounded exactly when the spectral radius is
at most one and every eigenvalue of modulus one is semisimple.
[HornJohnson2013, Theorem 3.2.5.2].
Port of `NLAlib.exists_bound_norm_matrix_pow_iff`, there over `ℂ`. -/
theorem exists_forall_specNorm_pow_le_iff (A : Matrix n n 𝕜) :
    (∃ C : ℝ, ∀ k : ℕ, specNorm (A ^ k) ≤ C) ↔
      specRadius A ≤ 1 ∧ ∀ μ : ℂ, ‖μ‖ = 1 →
        Module.End.maxGenEigenspace (Matrix.toLin' (complexify A)) μ =
          Module.End.eigenspace (Matrix.toLin' (complexify A)) μ := by
  sorry

end NLAlib
