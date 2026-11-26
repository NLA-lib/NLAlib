/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU
public import NLAlib.Matrix.Perturbation.ComponentwiseBackward

/-!
# Componentwise backward error of LU factorization

`NLAlib.IsLUErr` records the triangular shape of computed factors and their componentwise
factorization residual. Row and column pivoting use the same guarantee on a reindexed input.
The solve consumer combines this residual with the residuals of two triangular solves.
[Higham2002, §9.3].

## Main results

* `NLAlib.IsLU.isLUErr`, `NLAlib.IsLUErr.isLU`: exact factorizations and zero error.
* `NLAlib.IsLUErr.mono`: increasing the error allowance.
* `NLAlib.IsLUErr.norm_mulVec_sub_le_add`: factorization and solve residuals compose.
* `NLAlib.IsLUErr.norm_mulVec_sub_le`: the residual after exact triangular solves.
* `NLAlib.IsLUErr.norm_mulVec_sub_le_of_isComponentwiseBackwardSolution`: two nearby-system
  solves compose.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [LinearOrder n]

/-- Componentwise LU backward error: the factors are unit lower and upper triangular, and
$\lvert (\mathbf{A}-\mathbf{L}\mathbf{U})_{i,j}\rvert$ is at most
$\varepsilon\sum_k\lvert\mathbf{L}_{i,k}\rvert\lvert\mathbf{U}_{k,j}\rvert$.
For pivoted factorizations the input matrix is reindexed before applying this predicate.
[Higham2002, Theorem 9.3]. -/
structure IsLUErr (ε : ℝ) (A L U : Matrix n n 𝕜) : Prop where
  /-- The left factor is unit lower triangular. -/
  isUnitLowerTriangular : IsUnitLowerTriangular L
  /-- The right factor is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- The componentwise factorization residual. -/
  residual : ∀ i j, ‖(A - L * U) i j‖ ≤ ε * ∑ k, ‖L i k‖ * ‖U k j‖

variable {A L U : Matrix n n 𝕜} {ε ε' : ℝ}

/-- An exact LU factorization has zero componentwise backward error. -/
theorem IsLU.isLUErr (h : IsLU A L U) : IsLUErr 0 A L U where
  isUnitLowerTriangular := h.isUnitLowerTriangular
  isUpperTriangular := h.isUpperTriangular
  residual i j := by simp only [h.eq_mul, sub_self, Matrix.zero_apply, norm_zero, zero_mul,
    le_refl]

/-- Zero componentwise backward error gives an exact LU factorization. -/
theorem IsLUErr.isLU (h : IsLUErr 0 A L U) : IsLU A L U where
  isUnitLowerTriangular := h.isUnitLowerTriangular
  isUpperTriangular := h.isUpperTriangular
  eq_mul := by
    apply sub_eq_zero.mp
    ext i j
    exact norm_le_zero_iff.mp (by simpa only [zero_mul] using h.residual i j)

/-- An LU backward-error guarantee persists when its error allowance increases. -/
theorem IsLUErr.mono (h : IsLUErr ε A L U) (hε : ε ≤ ε') : IsLUErr ε' A L U where
  isUnitLowerTriangular := h.isUnitLowerTriangular
  isUpperTriangular := h.isUpperTriangular
  residual i j := (h.residual i j).trans
    (mul_le_mul_of_nonneg_right hε (Finset.sum_nonneg fun _ _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)))

/-- Applying the factorization residual to a vector gives a weighted componentwise bound.
The vector is arbitrary; no invertibility or sign condition on the error allowance is needed. -/
theorem IsLUErr.norm_sub_mul_mulVec_le (h : IsLUErr ε A L U) (x : n → 𝕜) (i : n) :
    ‖((A - L * U) *ᵥ x) i‖ ≤
      ε * ∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖) := by
  classical
  calc
    ‖((A - L * U) *ᵥ x) i‖ ≤ ∑ j, ‖(A - L * U) i j * x j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, (ε * ∑ k, ‖L i k‖ * ‖U k j‖) * ‖x j‖ := by
      simp_rw [norm_mul]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (h.residual i j) (norm_nonneg _)
    _ = ε * ∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]

/-- The componentwise residual of a solve through approximate LU factors is bounded by the
factorization residual, the upper solve residual multiplied by the lower factor, and the lower
solve residual. The intermediate vector and final vector may be arbitrary computed values.
No invertibility assumption is needed. -/
theorem IsLUErr.norm_mulVec_sub_le_add (h : IsLUErr ε A L U) (x y b : n → 𝕜) (i : n) :
    ‖(A *ᵥ x - b) i‖ ≤
      ε * ∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖) +
        ∑ k, ‖L i k‖ * ‖(U *ᵥ x - y) k‖ + ‖(L *ᵥ y - b) i‖ := by
  have heq : A *ᵥ x - b =
      (A - L * U) *ᵥ x + L *ᵥ (U *ᵥ x - y) + (L *ᵥ y - b) := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  rw [heq, Pi.add_apply, Pi.add_apply]
  refine (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (h.norm_sub_mul_mulVec_le x i) ?_)) le_rfl)
  calc
    ‖(L *ᵥ (U *ᵥ x - y)) i‖ ≤ ∑ k, ‖L i k * (U *ᵥ x - y) k‖ := norm_sum_le _ _
    _ = ∑ k, ‖L i k‖ * ‖(U *ᵥ x - y) k‖ := by simp_rw [norm_mul]

/-- Exact triangular solves through approximate LU factors leave only the factorization
residual in the original system. This includes singular factors whenever the stated solves
exist. -/
theorem IsLUErr.norm_mulVec_sub_le (h : IsLUErr ε A L U) {x y b : n → 𝕜}
    (hU : U *ᵥ x = y) (hL : L *ᵥ y = b) (i : n) :
    ‖(A *ᵥ x - b) i‖ ≤ ε * ∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖) := by
  simpa only [hU, hL, sub_self, Pi.zero_apply, norm_zero, mul_zero, Finset.sum_const_zero,
    add_zero] using h.norm_mulVec_sub_le_add x y b i

/-- A componentwise LU factorization guarantee and two nearby-system solve guarantees give
an original-system residual bound. The lower solve returns the intermediate vector and the
upper solve returns the final vector. Neither the input nor the factors must be invertible.
No printed source. -/
theorem IsLUErr.norm_mulVec_sub_le_of_isComponentwiseBackwardSolution
    (h : IsLUErr ε A L U)
    {ηL ηU : ℝ} {x y b : n → 𝕜} (hL : IsComponentwiseBackwardSolution ηL 0 L b y)
    (hU : IsComponentwiseBackwardSolution ηU 0 U y x) (i : n) :
    ‖(A *ᵥ x - b) i‖ ≤
      (ε + ηU) * ∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖) +
        ηL * ∑ k, ‖L i k‖ * ‖y k‖ := by
  have hupper : (∑ k, ‖L i k‖ * ‖(U *ᵥ x - y) k‖) ≤
      ηU * ∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖) := by
    calc
      _ ≤ ∑ k, ‖L i k‖ * (ηU * ∑ j, ‖U k j‖ * ‖x j‖) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [Pi.sub_apply, norm_sub_rev, zero_mul, add_zero] using hU.norm_sub_mulVec_le k
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hlower : ‖(L *ᵥ y - b) i‖ ≤ ηL * ∑ k, ‖L i k‖ * ‖y k‖ := by
    simpa only [Pi.sub_apply, norm_sub_rev, zero_mul, add_zero] using hL.norm_sub_mulVec_le i
  calc
    _ ≤ _ := h.norm_mulVec_sub_le_add x y b i
    _ ≤ ε * (∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖)) +
        ηU * (∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖)) +
        ηL * ∑ k, ‖L i k‖ * ‖y k‖ :=
      add_le_add (add_le_add le_rfl hupper) hlower
    _ = _ := by rw [add_mul]

end NLAlib
