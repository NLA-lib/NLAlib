/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# The decoded backward error of a linear solve

`NLAlib.IsLinearSolveErr` states that a computed solution solves a nearby system, with an
entrywise relative perturbation of the coefficient matrix. The guarantee applies to arbitrary
real or complex matrices; triangular solve implementations supply it without introducing
separate lower and upper error predicates.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.IsLinearSolveErr`: a componentwise backward error guarantee.

## Main results

* `NLAlib.IsLinearSolveErr.mono`: increasing the error allowance preserves the guarantee.
* `NLAlib.IsLinearSolveErr.of_mulVec_eq`: exact solutions satisfy every nonnegative allowance.
* `NLAlib.IsLinearSolveErr.mulVec_eq`: zero backward error gives an exact solution.
* `NLAlib.IsLinearSolveErr.norm_sub_mulVec_le`: a componentwise solve residual bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- A computed solution $\mathbf{x}$ solves a nearby system over an `RCLike` field: for some matrix
$\Delta\mathbf{T}$ with $\|\Delta T_{ij}\| \le \eta\|T_{ij}\|$,
$(\mathbf{T}+\Delta\mathbf{T})\mathbf{x}=\mathbf{b}$.
Triangular substitution supplies this guarantee with a componentwise rounding allowance
[Higham2002, Theorem 8.5]; the predicate itself imposes no shape on $\mathbf{T}$. -/
structure IsLinearSolveErr {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] (η : ℝ)
    (T : Matrix n n 𝕜) (b x : n → 𝕜) : Prop where
  /-- A componentwise nearby coefficient matrix for which the computed solution is exact. -/
  backward : ∃ ΔT : Matrix n n 𝕜,
    (∀ i j, ‖ΔT i j‖ ≤ η * ‖T i j‖) ∧ (T + ΔT) *ᵥ x = b

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] {η η' : ℝ}
    {T : Matrix n n 𝕜} {b x : n → 𝕜}

/-- A linear solve with componentwise backward allowance $\eta$ also meets every larger
allowance $\eta'$. -/
theorem IsLinearSolveErr.mono (h : IsLinearSolveErr η T b x) (hη : η ≤ η') :
    IsLinearSolveErr η' T b x := by
  obtain ⟨ΔT, hΔ, heq⟩ := h.backward
  exact ⟨ΔT, fun i j => (hΔ i j).trans (mul_le_mul_of_nonneg_right hη (norm_nonneg _)), heq⟩

/-- Relabeling a nearby system by the same finite equivalence in rows, columns and vectors
preserves its componentwise backward error allowance. -/
theorem IsLinearSolveErr.reindex {m : Type*} [Fintype m]
    (h : IsLinearSolveErr η T b x) (e : m ≃ n) :
    IsLinearSolveErr η (T.submatrix e e) (b ∘ e) (x ∘ e) := by
  obtain ⟨ΔT, hΔ, heq⟩ := h.backward
  refine ⟨ΔT.submatrix e e, fun i j => hΔ (e i) (e j), ?_⟩
  have he : (x ∘ e) ∘ e.symm = x := by
    ext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  change (T + ΔT).submatrix e e *ᵥ (x ∘ e) = b ∘ e
  rw [Matrix.submatrix_mulVec_equiv, he, heq]

/-- An exact solution of $\mathbf{T}\mathbf{x}=\mathbf{b}$ has componentwise backward
error at most every nonnegative allowance $\eta$. -/
theorem IsLinearSolveErr.of_mulVec_eq (hη : 0 ≤ η) (h : T *ᵥ x = b) :
    IsLinearSolveErr η T b x := by
  refine ⟨0, fun i j => ?_, ?_⟩
  · simpa using mul_nonneg hη (norm_nonneg (T i j))
  · simpa using h

/-- Zero componentwise backward error means that the computed solution solves the original
system exactly. -/
theorem IsLinearSolveErr.mulVec_eq (h : IsLinearSolveErr 0 T b x) : T *ᵥ x = b := by
  obtain ⟨ΔT, hΔ, heq⟩ := h.backward
  have hzero : ΔT = 0 := by
    ext i j
    exact norm_eq_zero.mp (le_antisymm (by simpa using hΔ i j) (norm_nonneg _))
  simpa [hzero] using heq

/-- A componentwise nearby-system guarantee bounds each entry of the original system's
residual by the coefficient magnitudes weighted by the computed solution magnitudes.
No invertibility or triangular shape is required. -/
theorem IsLinearSolveErr.norm_sub_mulVec_le (h : IsLinearSolveErr η T b x) (i : n) :
    ‖(b - T *ᵥ x) i‖ ≤ η * ∑ j, ‖T i j‖ * ‖x j‖ := by
  obtain ⟨ΔT, hΔ, heq⟩ := h.backward
  have hres : b - T *ᵥ x = ΔT *ᵥ x := by
    rw [← heq, Matrix.add_mulVec]
    abel
  rw [hres]
  calc
    ‖(ΔT *ᵥ x) i‖ ≤ ∑ j, ‖ΔT i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (η * ‖T i j‖) * ‖x j‖ := by
      simp_rw [norm_mul]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hΔ i j) (norm_nonneg _)
    _ = η * ∑ j, ‖T i j‖ * ‖x j‖ := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]

end NLAlib
