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
public import NLAlib.Matrix.Functions.MatrixMonotone
public import NLAlib.Matrix.Inequalities.Order

/-!
# Operator monotone functions

The Löwner–Heinz theorem: $t \mapsto t^r$ for $0 \le r \le 1$ and the logarithm are operator
monotone; the powers are operator concave.

The results are stated over $\Bbbk$; they are proved over $\mathbb{C}$, where Mathlib has the
corresponding C⋆-algebra facts (`CFC.rpow_le_rpow`, `CFC.concaveOn_rpow`, `CFC.log_le_log`, in
the scope `Matrix.Norms.L2Operator`), and transferred through `NLAlib.complexify`.

## Main results

* `Matrix.PosSemidef.rpow_le_rpow`, `Matrix.PosSemidef.sqrt_le_sqrt`,
  `Matrix.PosDef.cfc_log_le_cfc_log`: Löwner–Heinz.
* `NLAlib.concaveOn_rpow`: operator concavity of the powers.
* `Matrix.PosDef.le_iff_inv_sqrt_mul_mul_inv_sqrt_le_one`: $\mathbf{B} \preceq \mathbf{A}$
  exactly when $\mathbf{A}^{-1/2}\mathbf{B}\mathbf{A}^{-1/2} \preceq \mathbf{I}$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Löwner–Heinz -/

omit [Fintype n] in
/-- A matrix above a positive definite matrix is positive definite: if $\mathbf{A}$ is positive
definite and $\mathbf{A} \preceq \mathbf{B}$, then $\mathbf{B}$ is positive definite. -/
theorem _root_.Matrix.PosDef.posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B.PosDef := by
  have hB := hA.add_posSemidef (Matrix.le_iff.mp h)
  rwa [add_sub_cancel] at hB

/-- **The Löwner–Heinz theorem.** For $0 \le r \le 1$, $t \mapsto t^r$ is operator monotone on
positive semidefinite matrices: if $\mathbf{A}$ is positive semidefinite and
$\mathbf{A} \preceq \mathbf{B}$, then $\mathbf{A}^r \preceq \mathbf{B}^r$.
[Bhatia1997, Theorem V.1.9].
Result: loewner-heinz -/
theorem _root_.Matrix.PosSemidef.rpow_le_rpow [DecidableEq n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≤ B) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) : A ^ r ≤ B ^ r := by
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hA.nonneg.trans h)
  rw [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hB.nonneg]
  exact (operatorMonotoneOn_rpow hr).cfc_le_cfc hA.isHermitian hB.isHermitian
    (fun _ hx => spectrum_nonneg_of_nonneg hA.nonneg hx)
    (fun _ hx => spectrum_nonneg_of_nonneg hB.nonneg hx) h

open scoped Classical in
/-- **The square root is operator monotone**: if $\mathbf{A}$ is positive semidefinite and
$\mathbf{A} \preceq \mathbf{B}$, then $\mathbf{A}^{1/2} \preceq \mathbf{B}^{1/2}$.
[Bhatia1997, Proposition V.1.8]. -/
theorem _root_.Matrix.PosSemidef.sqrt_le_sqrt {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  rw [CFC.sqrt_eq_rpow, CFC.sqrt_eq_rpow]
  exact hA.rpow_le_rpow h ⟨by norm_num, by norm_num⟩

variable [DecidableEq n]

/-- **The logarithm is operator monotone** on positive definite matrices: if $\mathbf{A}$ is
positive definite and $\mathbf{A} \preceq \mathbf{B}$, then
$\log(\mathbf{A}) \preceq \log(\mathbf{B})$.
[Bhatia1997, Exercise V.1.10].
Result: loewner-heinz -/
theorem _root_.Matrix.PosDef.cfc_log_le_cfc_log {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (h : A ≤ B) : cfc Real.log A ≤ cfc Real.log B := by
  have hB : B.PosDef := hA.posDef_of_le h
  rw [← complexify_le_complexify_iff, Matrix.IsHermitian.complexify_cfc hA.isHermitian,
    Matrix.IsHermitian.complexify_cfc hB.isHermitian]
  open scoped Matrix.Norms.L2Operator in
  exact CFC.log_le_log (complexify_le_complexify_iff.mpr h)
    (posDef_complexify_iff.mpr hA).isStrictlyPositive

/-- **The powers $t^r$, $0 \le r \le 1$, are operator concave** on positive semidefinite
matrices: $\mathbf{A} \mapsto \mathbf{A}^r$ is concave for the Loewner order.
[Bhatia1997, Theorem V.2.5]. -/
theorem concaveOn_rpow {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosSemidef} fun A => A ^ r := by
  refine ⟨convex_setOf_posSemidef, fun A hA B hB a b ha hb hab => ?_⟩
  have hAc : (0 : Matrix n n ℂ) ≤ complexify A := (posSemidef_complexify_iff.mpr hA).nonneg
  have hBc : (0 : Matrix n n ℂ) ≤ complexify B := (posSemidef_complexify_iff.mpr hB).nonneg
  change a • A ^ r + b • B ^ r ≤ (a • A + b • B) ^ r
  rw [← complexify_le_complexify_iff, complexify_add, complexify_real_smul, complexify_real_smul,
    complexify_rpow, complexify_rpow, complexify_rpow, complexify_add, complexify_real_smul,
    complexify_real_smul]
  open scoped Matrix.Norms.L2Operator in
  exact (CFC.concaveOn_rpow hr).2 hAc hBc ha hb hab

/-- The description of $\mathbf{B} \preceq \mathbf{A}$ through a contraction: for positive
definite $\mathbf{A}$, $\mathbf{B} \preceq \mathbf{A}$ exactly when
$\mathbf{A}^{-1/2}\mathbf{B}\mathbf{A}^{-1/2} \preceq \mathbf{I}$. -/
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
