/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import NLAlib.Matrix.Spectral.Schur

/-!
# Gershgorin discs and diagonal dominance

Mathlib has Gershgorin's circle theorem (`eigenvalue_mem_ball`) and the nonsingularity of strictly
diagonally dominant matrices (`det_ne_zero_of_sum_row_lt_diag`). This file states the circle
theorem for the spectrum, by rows and by columns, and its consequences: a Hermitian diagonally
dominant matrix with positive diagonal is positive definite, a matrix whose diagonal dominates
in real part has its eigenvalues in the right half plane, an irreducibly diagonally dominant
matrix is nonsingular (Taussky), and a union of discs disjoint from the others contains as many
eigenvalues as discs.

The off-diagonal row sum is `∑ j ∈ Finset.univ.erase i, ‖A i j‖`, as in Mathlib.

## Main results

* `NLAlib.exists_norm_sub_le_sum_of_mem_spectrum`: the circle theorem for the spectrum.
* `Matrix.IsHermitian.posDef_of_forall_sum_lt_re`: diagonal dominance gives positive
  definiteness.
* `NLAlib.re_pos_of_mem_spectrum_of_forall_sum_lt_re`.
* `NLAlib.det_ne_zero_of_isIrreducible_of_forall_sum_le`: Taussky's theorem.
* `NLAlib.countP_roots_charpoly_mem_iUnion_closedBall`: counting eigenvalues in a union of discs.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The circle theorem -/

/-- **Gershgorin's circle theorem**, by rows: every eigenvalue lies in a disc centred at a
diagonal entry with radius the off-diagonal row sum. [HornJohnson2013, Theorem 6.1.1].
Port of `NLAlib.exists_mem_gershgorinRowDisc_of_mem_spectrum`. -/
theorem exists_norm_sub_le_sum_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ i, ‖μ - A i i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by
  sorry

/-- Gershgorin's circle theorem, by columns.
Port of `NLAlib.exists_mem_gershgorinColumnDisc_of_mem_spectrum`. -/
theorem exists_norm_sub_le_sum_col_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ j, ‖μ - A j j‖ ≤ ∑ i ∈ Finset.univ.erase j, ‖A i j‖ := by
  sorry

/-- Every eigenvalue is at most a row sum in absolute value.
Port of `NLAlib.exists_norm_le_row_sum_of_mem_spectrum`. -/
theorem exists_norm_le_sum_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ i, ‖μ‖ ≤ ∑ j, ‖A i j‖ := by
  sorry

/-- Every eigenvalue is at most a weighted row sum in absolute value, for any positive weights.
[HornJohnson2013, Corollary 6.1.6].
Port of `NLAlib.spectralRadius_le_max_weighted_row_sum`. -/
theorem exists_norm_le_weighted_sum_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    ∃ i, ‖μ‖ ≤ (p i)⁻¹ * ∑ j, p j * ‖A i j‖ := by
  sorry

/-! ### Diagonal dominance -/

/-- **A Hermitian strictly diagonally dominant matrix with positive diagonal is positive
definite.** [HornJohnson2013, Theorem 6.1.10].
Port of `NLAlib.posDef_of_isHermitian_of_row_radius_lt_diag`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.posDef_of_forall_sum_lt_re {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < RCLike.re (A i i)) :
    A.PosDef := by
  sorry

/-- A Hermitian weakly diagonally dominant matrix with nonnegative diagonal is positive
semidefinite. -/
theorem _root_.Matrix.IsHermitian.posSemidef_of_forall_sum_le_re {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ RCLike.re (A i i)) :
    A.PosSemidef := by
  sorry

/-- **A matrix whose diagonal dominates in real part has its eigenvalues in the open right half
plane.** [HornJohnson2013, Theorem 6.1.10].
Port of `NLAlib.re_pos_of_mem_spectrum_of_row_radius_lt_re_diag`. -/
theorem re_pos_of_mem_spectrum_of_forall_sum_lt_re {A : Matrix n n 𝕜}
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < RCLike.re (A i i)) {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : 0 < RCLike.re μ := by
  sorry

/-- **Taussky's theorem.** An irreducible weakly diagonally dominant matrix with one strictly
dominant row is nonsingular. [HornJohnson2013, Corollary 6.2.27].
Port of `NLAlib.det_ne_zero_of_irreducible_weak_diagonal_dominance`. -/
theorem det_ne_zero_of_isIrreducible_of_forall_sum_le {A : Matrix n n 𝕜}
    (hI : (A.map fun x => ‖x‖).IsIrreducible)
    (hweak : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖)
    (hstrict : ∃ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖) : A.det ≠ 0 := by
  sorry

/-- A Hermitian irreducible weakly diagonally dominant matrix with positive diagonal and one
strictly dominant row is positive definite. [HornJohnson2013, Corollary 6.2.27].
Port of `NLAlib.posDef_of_isHermitian_of_irreducible_weak_diagonal_dominance`. -/
theorem _root_.Matrix.IsHermitian.posDef_of_isIrreducible_of_forall_sum_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hI : (A.map fun x => ‖x‖).IsIrreducible)
    (hweak : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ RCLike.re (A i i))
    (hstrict : ∃ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < RCLike.re (A i i)) : A.PosDef := by
  sorry

/-! ### Counting eigenvalues -/

/-- **A union of Gershgorin discs disjoint from the remaining discs contains exactly as many
eigenvalues, with multiplicity, as it has discs.** [HornJohnson2013, Theorem 6.1.1].
Port of `NLAlib.charpolyRootCountIn_gershgorinRowUnion_eq_card`. -/
theorem countP_roots_charpoly_mem_iUnion_closedBall (A : Matrix n n ℂ) (I : Finset n)
    (h : Disjoint
      (⋃ i ∈ I, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖))
      (⋃ i ∈ Iᶜ, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖))) :
    letI := Classical.decPred fun z : ℂ =>
      z ∈ ⋃ i ∈ I, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖)
    A.charpoly.roots.countP
      (fun z => z ∈ ⋃ i ∈ I, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖)) =
      I.card := by
  sorry

end NLAlib
