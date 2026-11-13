/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Spec

/-!
# Nonbreakdown of the Hestenes–Stiefel recurrence

Positive definiteness makes the search-direction quadratic form positive before the initial
residual's Krylov grade. The direction pairs with the current residual as the residual pairs
with itself. These facts connect the existing recurrence theory to the domain of a CG round.

## Main results

* `NLAlib.Krylov.CG.iterate_cgStep_cgState` identifies repeated rounds with the recurrence.
* `Matrix.PosDef.star_cgState_p_dotProduct_r` gives the direction-residual identity.
* `Matrix.PosDef.cgState_p_ne_zero_of_r_ne_zero` excludes a zero direction at an active state.
* `Matrix.PosDef.cgState_nonbreakdown_of_r_ne_zero` certifies an active real state.
* `Matrix.PosDef.cgState_nonbreakdown` gives both nonzero denominators before the grade.
* `Matrix.PosDef.mulVec_cgIterate_eq_of_krylovGrade_le` gives the exact system solution.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Krylov.CG

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Repeated CG rounds continue the mathematical state sequence from any starting index. -/
theorem iterate_cgStep_cgState (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k j : ℕ) :
    (cgStep A)^[k] (cgState A b x₀ j) = cgState A b x₀ (j + k) := by
  induction k with
  | zero => simp only [Function.iterate_zero_apply, Nat.add_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Nat.add_succ]
    rfl

omit [DecidableEq n] in
/-- The current search direction pairs with the residual as the residual pairs with itself.
The correction from the residual to the direction is in the current Krylov space, which is
orthogonal to the residual. [HestenesStiefel1952, Theorem 5:1]. -/
theorem _root_.Matrix.PosDef.star_cgState_p_dotProduct_r {A : Matrix n n 𝕜}
    (hA : A.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    star (cgState A b x₀ k).p ⬝ᵥ (cgState A b x₀ k).r =
      star (cgState A b x₀ k).r ⬝ᵥ (cgState A b x₀ k).r := by
  classical
  have hmem : (cgState A b x₀ k).p - (cgState A b x₀ k).r ∈
      krylovSpace A (b - A *ᵥ x₀) k := by
    cases k with
    | zero => simp [cgState]
    | succ j =>
      have hp : (cgState A b x₀ j).p ∈ krylovSpace A (b - A *ᵥ x₀) (j + 1) := by
        rw [← hA.span_cgState_p (b := b) (x₀ := x₀) (j + 1)]
        exact Submodule.subset_span ⟨⟨j, Nat.lt_succ_self j⟩, rfl⟩
      change (cgStep A (cgState A b x₀ j)).p -
        (cgStep A (cgState A b x₀ j)).r ∈ _
      simp only [cgStep, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ hp
  have h := forall_mem_range_star_dotProduct_eq_zero_iff.mpr
    (hA.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero b x₀ k) _ hmem
  rwa [star_sub, sub_dotProduct, sub_eq_zero] at h

omit [DecidableEq n] in
/-- A nonzero residual in the positive-definite CG recurrence has a nonzero direction.
[HestenesStiefel1952, Theorem 5:1]. -/
theorem _root_.Matrix.PosDef.cgState_p_ne_zero_of_r_ne_zero {A : Matrix n n 𝕜}
    (hA : A.PosDef) (b x₀ : n → 𝕜) {k : ℕ} (hr : (cgState A b x₀ k).r ≠ 0) :
    (cgState A b x₀ k).p ≠ 0 := by
  intro hp
  have h := hA.star_cgState_p_dotProduct_r b x₀ k
  rw [hp, star_zero, zero_dotProduct] at h
  exact hr (dotProduct_star_self_eq_zero.1 h.symm)

omit [DecidableEq n] in
/-- A nonzero residual suffices for both nonzero denominators in the real positive-definite
CG recurrence. [HestenesStiefel1952, Theorem 5:1]. -/
theorem _root_.Matrix.PosDef.cgState_nonbreakdown_of_r_ne_zero {A : Matrix n n ℝ}
    (hA : A.PosDef) (b x₀ : n → ℝ) {k : ℕ} (hr : (cgState A b x₀ k).r ≠ 0) :
    Nonbreakdown A (cgState A b x₀ k) := by
  refine ⟨fun h => hr (dotProduct_self_eq_zero.mp h), ?_⟩
  simpa only [star_trivial] using
    (hA.dotProduct_mulVec_pos (hA.cgState_p_ne_zero_of_r_ne_zero b x₀ hr)).ne'

/-- Before the initial residual's Krylov grade, both scalar denominators of real CG are
nonzero for a positive-definite matrix. [HestenesStiefel1952, Theorem 5:1]. -/
theorem _root_.Matrix.PosDef.cgState_nonbreakdown {A : Matrix n n ℝ} (hA : A.PosDef)
    (b x₀ : n → ℝ) {k : ℕ} (hk : k < krylovGrade A (b - A *ᵥ x₀)) :
    Nonbreakdown A (cgState A b x₀ k) := by
  have hr : (cgState A b x₀ k).r ≠ 0 :=
    fun h => hk.not_ge ((hA.cgState_r_eq_zero_iff b x₀ k).mp h)
  exact hA.cgState_nonbreakdown_of_r_ne_zero b x₀ hr

/-- At or beyond the initial residual's grade, exact positive-definite CG solves the system.
The residual identity supplies this conclusion without an assumed solution vector.
[HestenesStiefel1952, Theorem 5:1]. -/
theorem _root_.Matrix.PosDef.mulVec_cgIterate_eq_of_krylovGrade_le {A : Matrix n n 𝕜}
    (hA : A.PosDef) (b x₀ : n → 𝕜) {k : ℕ} (hk : krylovGrade A (b - A *ᵥ x₀) ≤ k) :
    A *ᵥ cgIterate A b x₀ k = b := by
  have hr := (hA.cgState_r_eq_zero_iff b x₀ k).mpr hk
  rw [cgState_r_eq, hA.cgState_x_eq] at hr
  exact (sub_eq_zero.mp hr).symm

end NLAlib.Krylov.CG
