/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky
public import NLAlib.Matrix.Norms.Spectral

/-!
# Cholesky factors with an absolute backward error

A computed Cholesky factor represents a nearby positive definite matrix. The decoded guarantee
`NLAlib.IsCholeskyErr` keeps the triangular structure and positive diagonal exact and bounds the
spectral norm of the factorization residual by an absolute budget. This leaves a concrete
algorithm free to establish a componentwise, factor-scaled or input-scaled budget. It asserts
no execution success or arithmetic model by itself.

## Main results

* `NLAlib.isCholeskyErr_zero_iff`: zero backward error is an exact Cholesky factorization.
* `NLAlib.IsCholeskyErr.isCholesky`: the factor exactly represents a nearby positive definite
  matrix.
* `NLAlib.IsCholeskyErr.norm_sub_mulVec_le`: the residual after two inexact triangular solves.
* `NLAlib.IsCholeskyErr.norm_sub_mulVec_le_of_mulVec_eq`: the residual after exact solves.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

/-- **A Cholesky factor with absolute backward error at most $\varepsilon$**: the factor
$\mathbf{L}$ is lower triangular with positive diagonal, and
$\|\mathbf{A}-\mathbf{L}\mathbf{L}^{\mathsf{H}}\|_2\le\varepsilon$.
The budget is absolute; no positive definiteness or normalization of the input is assumed.
This is the decoded factorization guarantee, not an execution certificate.
No printed source; the absolute-budget form of the backward error in
[Higham2002, Chapter 10]. -/
structure IsCholeskyErr (ε : ℝ) (A L : Matrix n n 𝕜) : Prop where
  /-- The computed factor is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- The computed diagonal is positive. -/
  apply_self_pos : ∀ i, 0 < L i i
  /-- The absolute spectral backward error. -/
  residual : specNorm (A - L * Lᴴ) ≤ ε

variable {ε ε' : ℝ} {A L : Matrix n n 𝕜}

/-- An exact Cholesky factor has zero absolute backward error. -/
theorem IsCholesky.isCholeskyErr (h : IsCholesky A L) : IsCholeskyErr 0 A L := by
  refine ⟨h.isLowerTriangular, h.apply_self_pos, ?_⟩
  rw [h.eq_mul_conjTranspose, sub_self, specNorm_zero]

/-- Increasing the absolute error budget preserves the Cholesky guarantee. -/
theorem IsCholeskyErr.mono (h : IsCholeskyErr ε A L) (hε : ε ≤ ε') :
    IsCholeskyErr ε' A L :=
  ⟨h.isLowerTriangular, h.apply_self_pos, h.residual.trans hε⟩

/-- A Cholesky error budget is nonnegative, including for an empty matrix. -/
theorem IsCholeskyErr.nonneg (h : IsCholeskyErr ε A L) : 0 ≤ ε :=
  (specNorm_nonneg _).trans h.residual

/-- The computed factor is an exact Cholesky factor of its Gram matrix, which is therefore
positive definite. Its distance from the input is the residual in the guarantee. -/
theorem IsCholeskyErr.isCholesky (h : IsCholeskyErr ε A L) :
    IsCholesky (L * Lᴴ) L :=
  ⟨h.isLowerTriangular, h.apply_self_pos, rfl⟩

/-- Zero absolute backward error is equivalent to an exact Cholesky factorization. -/
theorem isCholeskyErr_zero_iff : IsCholeskyErr 0 A L ↔ IsCholesky A L := by
  constructor
  · intro h
    refine ⟨h.isLowerTriangular, h.apply_self_pos, ?_⟩
    exact sub_eq_zero.mp (specNorm_eq_zero_iff.mp
      (le_antisymm h.residual (specNorm_nonneg _)))
  · exact IsCholesky.isCholeskyErr

/-- If a Cholesky factor has absolute backward error at most $\varepsilon$, then any two
approximate triangular solves with intermediate vector $\mathbf{y}$ have residual bounded by
$$\|\mathbf{b}-\mathbf{A}\mathbf{x}\|\le\varepsilon\|\mathbf{x}\|
+\|\mathbf{L}\|_2\|\mathbf{y}-\mathbf{L}^{\mathsf{H}}\mathbf{x}\|
+\|\mathbf{b}-\mathbf{L}\mathbf{y}\|.$$
No assumptions on how the solves were computed are needed. No printed source. -/
theorem IsCholeskyErr.norm_sub_mulVec_le (h : IsCholeskyErr ε A L)
    (b x y : n → 𝕜) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤ ε * ‖WithLp.toLp 2 x‖ +
      specNorm L * ‖WithLp.toLp 2 (y - Lᴴ *ᵥ x)‖ +
      ‖WithLp.toLp 2 (b - L *ᵥ y)‖ := by
  have hid : b - A *ᵥ x = (b - L *ᵥ y) + L *ᵥ (y - Lᴴ *ᵥ x) -
      (A - L * Lᴴ) *ᵥ x := by
    simp only [Matrix.mulVec_sub, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    abel
  rw [hid]
  have h₁ := norm_sub_le
    (WithLp.toLp 2 ((b - L *ᵥ y) + L *ᵥ (y - Lᴴ *ᵥ x)))
    (WithLp.toLp 2 ((A - L * Lᴴ) *ᵥ x))
  have h₂ := norm_add_le (WithLp.toLp 2 (b - L *ᵥ y))
    (WithLp.toLp 2 (L *ᵥ (y - Lᴴ *ᵥ x)))
  have h₃ := norm_toLp_mulVec_le L (y - Lᴴ *ᵥ x)
  have h₄ := (norm_toLp_mulVec_le (A - L * Lᴴ) x).trans
    (mul_le_mul_of_nonneg_right h.residual (norm_nonneg _))
  simp only [WithLp.toLp_sub, WithLp.toLp_add] at h₁ h₂ h₃ ⊢
  linarith

/-- With exact forward and adjoint solves through a factor whose absolute backward error is
at most $\varepsilon$, the original-system residual is at most
$\varepsilon\|\mathbf{x}\|$. No printed source. -/
theorem IsCholeskyErr.norm_sub_mulVec_le_of_mulVec_eq (h : IsCholeskyErr ε A L)
    {b x y : n → 𝕜} (hforward : L *ᵥ y = b) (hadjoint : Lᴴ *ᵥ x = y) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤ ε * ‖WithLp.toLp 2 x‖ := by
  simpa only [hforward, hadjoint, sub_self, WithLp.toLp_zero, norm_zero, mul_zero,
    add_zero] using h.norm_sub_mulVec_le b x y

end NLAlib
