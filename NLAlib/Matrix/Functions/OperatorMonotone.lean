/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.Functions.Complexification
public import NLAlib.Matrix.Inequalities.Order

/-!
# Operator monotone functions

The Löwner–Heinz theorem: `t ↦ t ^ r` for `0 ≤ r ≤ 1` and the logarithm are operator monotone;
the powers are operator concave.

The results are stated over `𝕜`; they are proved over `ℂ`, where Mathlib has the corresponding
C⋆-algebra facts (`CFC.rpow_le_rpow`, `CFC.concaveOn_rpow`, `CFC.log_le_log`, in the scope
`Matrix.Norms.L2Operator`), and transferred through `NLAlib.complexify`.

## Main results

* `Matrix.PosSemidef.rpow_le_rpow`, `Matrix.PosSemidef.sqrt_le_sqrt`,
  `Matrix.PosDef.cfc_log_le_cfc_log`: Löwner–Heinz.
* `NLAlib.concaveOn_rpow`: operator concavity of the powers.
* `Matrix.PosDef.le_iff_inv_sqrt_mul_mul_inv_sqrt_le_one`: `B ≤ A` exactly when
  `A^{-1/2} B A^{-1/2} ≤ 1`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Löwner–Heinz -/

omit [Fintype n] in
/-- A matrix above a positive definite matrix is positive definite.
Port of `NLAlib.posDef_of_posDef_le`. -/
theorem _root_.Matrix.PosDef.posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B.PosDef := by
  have hB := hA.add_posSemidef (Matrix.le_iff.mp h)
  rwa [add_sub_cancel] at hB

/-- **The Löwner–Heinz theorem.** For `0 ≤ r ≤ 1`, `t ↦ t ^ r` is operator monotone on positive
semidefinite matrices. [Bhatia1997, Theorem V.1.9].
Port of `NLAlib.cfc_rpow_le_cfc_rpow`, there over `ℝ`.
Result: loewner-heinz -/
theorem _root_.Matrix.PosSemidef.rpow_le_rpow [DecidableEq n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≤ B) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) : A ^ r ≤ B ^ r := by
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hA.nonneg.trans h)
  have hAc : (0 : Matrix n n ℂ) ≤ complexify A := (posSemidef_complexify_iff.mpr hA).nonneg
  have hBc : (0 : Matrix n n ℂ) ≤ complexify B := (posSemidef_complexify_iff.mpr hB).nonneg
  rw [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hB.nonneg,
    ← complexify_le_complexify_iff, complexify_cfc hA.isHermitian, complexify_cfc hB.isHermitian,
    ← CFC.rpow_eq_cfc_real hAc, ← CFC.rpow_eq_cfc_real hBc]
  open scoped Matrix.Norms.L2Operator in
  exact CFC.rpow_le_rpow hr (complexify_le_complexify_iff.mpr h)

open scoped Classical in
/-- **The square root is operator monotone.** [Bhatia1997, Proposition V.1.8].
Port of `NLAlib.sqrt_le_sqrt_of_posSemidef_le`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.sqrt_le_sqrt {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  rw [CFC.sqrt_eq_rpow, CFC.sqrt_eq_rpow]
  exact hA.rpow_le_rpow h ⟨by norm_num, by norm_num⟩

variable [DecidableEq n]

/-- **The logarithm is operator monotone** on positive definite matrices.
[Bhatia1997, Exercise V.1.10]. Port of `NLAlib.cfc_log_le_cfc_log`, there over `ℝ`.
Result: loewner-heinz -/
theorem _root_.Matrix.PosDef.cfc_log_le_cfc_log {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (h : A ≤ B) : cfc Real.log A ≤ cfc Real.log B := by
  have hB : B.PosDef := hA.posDef_of_le h
  rw [← complexify_le_complexify_iff, complexify_cfc hA.isHermitian,
    complexify_cfc hB.isHermitian]
  open scoped Matrix.Norms.L2Operator in
  exact CFC.log_le_log (complexify_le_complexify_iff.mpr h)
    (posDef_complexify_iff.mpr hA).isStrictlyPositive

/-- **The powers `t ^ r`, `0 ≤ r ≤ 1`, are operator concave** on positive semidefinite matrices.
[Bhatia1997, Theorem V.2.5]. Port of `NLAlib.concaveOn_cfc_rpow`, there over `ℝ`. -/
theorem concaveOn_rpow {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosSemidef} fun A => A ^ r := by
  have hconv : Convex ℝ {A : Matrix n n 𝕜 | A.PosSemidef} := fun A hA B hB a b ha hb _ =>
    Matrix.nonneg_iff_posSemidef.mp
      (add_nonneg (smul_nonneg ha hA.nonneg) (smul_nonneg hb hB.nonneg))
  refine ⟨hconv, fun A hA B hB a b ha hb hab => ?_⟩
  have hAc : (0 : Matrix n n ℂ) ≤ complexify A := (posSemidef_complexify_iff.mpr hA).nonneg
  have hBc : (0 : Matrix n n ℂ) ≤ complexify B := (posSemidef_complexify_iff.mpr hB).nonneg
  change a • A ^ r + b • B ^ r ≤ (a • A + b • B) ^ r
  rw [← complexify_le_complexify_iff, complexify_add, complexify_real_smul, complexify_real_smul,
    complexify_rpow, complexify_rpow, complexify_rpow, complexify_add, complexify_real_smul,
    complexify_real_smul]
  open scoped Matrix.Norms.L2Operator in
  exact (CFC.concaveOn_rpow hr).2 hAc hBc ha hb hab

/-- The description of `B ≤ A` through a contraction: for positive definite `A`,
`B ≤ A` exactly when `A^{-1/2} B A^{-1/2} ≤ 1`.
Port of `NLAlib.le_iff_exists_sqrt_congruence_contraction`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.le_iff_inv_sqrt_mul_mul_inv_sqrt_le_one {A B : Matrix n n 𝕜}
    (hA : A.PosDef) : B ≤ A ↔ (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹ ≤ 1 := by
  have hS : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSi : ((CFC.sqrt A)⁻¹)ᴴ = (CFC.sqrt A)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hS.eq]
  have hdet : IsUnit (CFC.sqrt A).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit_sqrt
  have hone : (CFC.sqrt A)⁻¹ * A * (CFC.sqrt A)⁻¹ = 1 := by
    nth_rewrite 2 [← CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hdet]
  have h := conjTranspose_mul_mul_le_conjTranspose_mul_mul_iff (A := B) (B := A)
    (S := (CFC.sqrt A)⁻¹) ((Matrix.isUnit_nonsing_inv_iff).mpr hA.isUnit_sqrt)
  rw [hSi, hone] at h
  exact h.symm

end NLAlib
