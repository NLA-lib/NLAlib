/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Spectral.LowRank
public import Mathlib.Tactic.Positivity.Core

/-!
# The condition number and the distance to singularity

`NLAlib.conditionNumber A` is the spectral condition number `‖A‖₂ ‖A⁺‖₂` of a matrix of any shape:
the ratio of its largest singular value to its smallest nonzero one. It is real-valued. For an
invertible matrix it is the classical `‖A‖₂ ‖A⁻¹‖₂`; for a matrix with full column rank it is
`σ_max / σ_min`; for the zero matrix it is `0`. A singular square matrix has a finite condition
number in this sense, so a theorem that needs invertibility or full column rank states it as a
hypothesis (`IsUnit A`, `Function.Injective A.mulVec`), as it would anyway.

The distance from a matrix to the nearest rank-deficient one, in spectral norm, is its smallest
singular value.

## Main definitions

* `NLAlib.conditionNumber`: `specNorm A * specNorm (pinv A)`.

## Main results

* `NLAlib.conditionNumber_eq_singularValues_div`: the ratio of extreme nonzero singular values.
* `NLAlib.one_le_conditionNumber`: at least one for a nonzero matrix.
* `NLAlib.conditionNumber_of_isUnit`: the classical formula.
* `NLAlib.singularValues_last_le_specNorm_of_not_injective_add`,
  `NLAlib.isLeast_specNorm_not_injective_add`: the distance to rank deficiency.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- The spectral **condition number** `‖A‖₂ ‖A⁺‖₂` of a matrix of any shape, real-valued: the
largest singular value over the smallest nonzero one. It is `0` for the zero matrix and equals
`‖A‖₂ ‖A⁻¹‖₂` for an invertible matrix. For a singular square matrix it is finite, not infinite:
theorems that need invertibility assume it.
[GolubVanLoan2013, §2.6.2 and §5.3.7]. Port of `NLAlib.moorePenroseConditionNumber`; the
prototype's `ℝ≥0∞`-valued `conditionNumber` of a square matrix is not reproduced. -/
noncomputable def conditionNumber (A : Matrix m n 𝕜) : ℝ :=
  specNorm A * specNorm (pinv A)

/-- `conditionNumber A` unfolds to `specNorm A * specNorm (pinv A)`. -/
theorem conditionNumber_def (A : Matrix m n 𝕜) :
    conditionNumber A = specNorm A * specNorm (pinv A) :=
  rfl

/-- The condition number is nonnegative.
Port of `NLAlib.moorePenroseConditionNumber_nonneg`. -/
theorem conditionNumber_nonneg (A : Matrix m n 𝕜) : 0 ≤ conditionNumber A := by
  exact mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)

/-- The condition number of the zero matrix is zero.
Port of `NLAlib.moorePenroseConditionNumber_zero`. -/
@[simp]
theorem conditionNumber_zero : conditionNumber (0 : Matrix m n 𝕜) = 0 := by
  rw [conditionNumber, specNorm_zero, zero_mul]

/-- **The condition number of a nonzero matrix is at least one.**
Port of `NLAlib.one_le_moorePenroseConditionNumber`. -/
theorem one_le_conditionNumber {A : Matrix m n 𝕜} (hA : A ≠ 0) : 1 ≤ conditionNumber A := by
  have hpos : 0 < specNorm A :=
    lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp hA))
  have hbound : 1 * specNorm A ≤ conditionNumber A * specNorm A := by
    calc 1 * specNorm A = specNorm (A * pinv A * A) := by rw [one_mul, mul_pinv_mul_self]
      _ ≤ specNorm (A * pinv A) * specNorm A := specNorm_mul_le _ _
      _ ≤ specNorm A * specNorm (pinv A) * specNorm A :=
        mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
  exact le_of_mul_le_mul_right hbound hpos

/-- **The condition number as a ratio of singular values**: for `k + 1 = rank A`,
`conditionNumber A = σ_0(A) / σ_k(A)`.
Port of `NLAlib.moorePenroseConditionNumber_eq_singularValues_ratio`. -/
theorem conditionNumber_eq_singularValues_div (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = A.rank) :
    conditionNumber A = singularValues A 0 / singularValues A k := by
  rw [conditionNumber, specNorm_pinv A hk, singularValues_zero_eq_specNorm, div_eq_mul_inv]

/-- With full column rank, the condition number is `specNorm A` over the smallest singular
value. Port of `NLAlib.moorePenroseConditionNumber_eq_specNorm_div_singularValues_last`. -/
theorem conditionNumber_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec)
    {k : ℕ} (hk : k + 1 = Fintype.card n) :
    conditionNumber A = specNorm A / singularValues A k := by
  rw [conditionNumber, specNorm_pinv_of_injective hA hk, div_eq_mul_inv]

/-- For an invertible matrix the condition number is `‖A‖₂ ‖A⁻¹‖₂`.
Port of `NLAlib.moorePenroseConditionNumber_eq_mul_specNorm_inv`. -/
theorem conditionNumber_of_isUnit [DecidableEq n] {A : Matrix n n 𝕜} (hA : IsUnit A) :
    conditionNumber A = specNorm A * specNorm A⁻¹ := by
  rw [conditionNumber, pinv_of_isUnit hA]

/-- For a positive definite matrix the condition number is the ratio of the extreme
eigenvalues. Port of `NLAlib.moorePenroseConditionNumber_eq_eigenvalues₀_ratio`, there over
`ℝ`. -/
theorem _root_.Matrix.PosDef.conditionNumber_eq {A : Matrix n n 𝕜} (hA : A.PosDef) {k : ℕ}
    (hk : k + 1 = Fintype.card n) : conditionNumber A = eigenvalue A 0 / eigenvalue A k := by
  classical
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hA.isUnit
  rw [conditionNumber_of_injective hinj hk, ← singularValues_zero_eq_specNorm,
    hA.posSemidef.singularValues_eq_eigenvalue]

/-- The condition number is invariant under the conjugate transpose.
Port of `NLAlib.moorePenroseConditionNumber_conjTranspose`. -/
@[simp]
theorem conditionNumber_conjTranspose (A : Matrix m n 𝕜) :
    conditionNumber Aᴴ = conditionNumber A := by
  rw [conditionNumber, pinv_conjTranspose, specNorm_conjTranspose, specNorm_conjTranspose,
    conditionNumber]

/-- The condition number of the pseudoinverse is that of the matrix. -/
@[simp]
theorem conditionNumber_pinv (A : Matrix m n 𝕜) : conditionNumber (pinv A) = conditionNumber A := by
  rw [conditionNumber, pinv_pinv, mul_comm, conditionNumber]

/-- The condition number is invariant under nonzero scaling.
Port of `NLAlib.moorePenroseConditionNumber_smul`. -/
theorem conditionNumber_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix m n 𝕜) :
    conditionNumber (c • A) = conditionNumber A := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [conditionNumber, pinv_smul, specNorm_smul, specNorm_smul, norm_inv, conditionNumber]
  field_simp

/-- The condition number of the Gram matrix is the square of the condition number.
Port of `NLAlib.moorePenroseConditionNumber_conjTranspose_mul_self`. -/
theorem conditionNumber_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    conditionNumber (Aᴴ * A) = conditionNumber A ^ 2 := by
  rw [conditionNumber, specNorm_conjTranspose_mul_self, ← specNorm_pinv_sq, conditionNumber,
    mul_pow]

/-- Left multiplication by a matrix with orthonormal columns preserves the condition number.
Port of `NLAlib.moorePenroseConditionNumber_mul_left_of_hasOrthonormalCols`. -/
theorem HasOrthonormalCols.conditionNumber_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    conditionNumber (Q * A) = conditionNumber A := by
  rw [conditionNumber, hQ.pinv_mul_left, hQ.specNorm_mul_left,
    hQ.specNorm_mul_conjTranspose_right, conditionNumber]

/-- A matrix with orthonormal columns, and at least one column, has condition number one. -/
theorem HasOrthonormalCols.conditionNumber_eq_one [DecidableEq n] [Nonempty n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : conditionNumber Q = 1 := by
  rw [conditionNumber, hQ.pinv_eq, specNorm_conjTranspose, hQ.specNorm_eq_one, mul_one]

/-- **Two-sided Gram bounds control the condition number.** If
`a • 1 ≤ Aᴴ * A ≤ b • 1` with `0 < a` and `0 ≤ b`, then `conditionNumber A ^ 2 ≤ b / a`. With
`A = S * U` this is the conditioning of a sketched orthonormal basis. -/
theorem conditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one [DecidableEq n]
    {A : Matrix m n 𝕜} {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A) (h₂ : Aᴴ * A ≤ b • (1 : Matrix n n 𝕜)) :
    conditionNumber A ^ 2 ≤ b / a := by
  rw [conditionNumber, mul_pow, div_eq_mul_inv]
  exact mul_le_mul ((specNorm_sq_le_iff_conjTranspose_mul_self_le hb).mpr h₂)
    (specNorm_pinv_sq_le_inv_of_smul_one_le ha h₁) (sq_nonneg _) hb

/-! ### Distance to rank deficiency -/

/-- **The smallest singular value is a lower bound for rank-deficient perturbations.** If
`A + E` does not have full column rank, then `σ_min(A) ≤ ‖E‖₂`.
[GolubVanLoan2013, Theorem 2.5.3 and §2.6.2].
Port of `NLAlib.inv_specNorm_inv_le_specNorm_of_not_isUnit_add`, there for square real
matrices. -/
theorem singularValues_last_le_specNorm_of_not_injective_add (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) {E : Matrix m n 𝕜}
    (hE : ¬ Function.Injective (A + E).mulVec) : singularValues A k ≤ specNorm E := by
  have h0 : singularValues (A + E) k = 0 :=
    le_antisymm (not_lt.mp ((singularValues_last_pos_iff_injective (A + E) hk).not.mpr hE))
      (singularValues_nonneg _ _)
  have h := abs_singularValues_sub_le_specNorm A (A + E) k
  rw [h0, sub_zero, sub_add_cancel_left, specNorm_neg] at h
  exact (le_abs_self _).trans h

/-- **The distance to rank deficiency is the smallest singular value.** Among perturbations `E`
for which `A + E` loses full column rank, the smallest spectral norm is `σ_min(A)`.
[GolubVanLoan2013, §2.6.2].
Port of `NLAlib.isLeast_specNorm_singular_perturbations`, there for square real matrices.
Result: distance-to-singularity -/
theorem isLeast_specNorm_not_injective_add (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    IsLeast (specNorm '' {E : Matrix m n 𝕜 | ¬ Function.Injective (A + E).mulVec})
      (singularValues A k) := by
  refine ⟨⟨truncatedSVD A k - A, ?_, ?_⟩, ?_⟩
  · rw [Set.mem_ofPred_eq, add_sub_cancel, mulVec_injective_iff_rank_eq]
    have := rank_truncatedSVD_le A k
    omega
  · rw [specNorm_sub_comm, specNorm_sub_truncatedSVD]
  · rintro _ ⟨E, hE, rfl⟩
    exact singularValues_last_le_specNorm_of_not_injective_add A hk hE

/-- **The distance from an invertible matrix to the singular matrices** is `1 / ‖A⁻¹‖₂`.
[GolubVanLoan2013, §2.6.2].
Port of `NLAlib.isLeast_specNorm_singular_perturbations`.
Result: distance-to-singularity -/
theorem isLeast_specNorm_not_isUnit_add [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : IsUnit A) :
    IsLeast (specNorm '' {E : Matrix n n 𝕜 | ¬ IsUnit (A + E)}) (specNorm A⁻¹)⁻¹ := by
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n :=
    ⟨Fintype.card n - 1, Nat.sub_add_cancel Fintype.card_pos⟩
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hA
  have hset : {E : Matrix n n 𝕜 | ¬ IsUnit (A + E)} =
      {E | ¬ Function.Injective (A + E).mulVec} := by
    ext E
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Matrix.mulVec_injective_iff_isUnit]
  rw [hset, ← pinv_of_isUnit hA, specNorm_pinv_of_injective hinj hk, inv_inv]
  exact isLeast_specNorm_not_injective_add A hk

/-- The relative distance from an invertible matrix to the singular matrices is the inverse of
the condition number. Port of `NLAlib.isLeast_relative_singular_perturbations`. -/
theorem isLeast_specNorm_div_not_isUnit_add [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : IsUnit A) :
    IsLeast ((fun E : Matrix n n 𝕜 => specNorm E / specNorm A) '' {E | ¬ IsUnit (A + E)})
      (conditionNumber A)⁻¹ := by
  have heq : (conditionNumber A)⁻¹ = (specNorm A⁻¹)⁻¹ / specNorm A := by
    rw [conditionNumber_of_isUnit hA, mul_inv, div_eq_mul_inv, mul_comm]
  obtain ⟨⟨E, hE, hEn⟩, hmin⟩ := isLeast_specNorm_not_isUnit_add hA
  rw [heq]
  refine ⟨⟨E, hE, ?_⟩, ?_⟩
  · rw [← hEn]
  · rintro _ ⟨F, hF, rfl⟩
    exact div_le_div_of_nonneg_right (hmin ⟨F, hF, rfl⟩) (specNorm_nonneg A)

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.conditionNumber A` is nonnegative. -/
@[positivity NLAlib.conditionNumber _]
meta def evalConditionNumber : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.conditionNumber_nonneg #[e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
