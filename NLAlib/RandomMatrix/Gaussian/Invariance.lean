/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Basic.Selection
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Orthogonal invariance of Gaussian matrices

A standard Gaussian matrix `G` keeps its law under multiplication by matrices with orthonormal
rows on the left and orthonormal columns on the right: `U G V` is a standard Gaussian matrix when
`U Uᴴ = 1` and `Vᴴ V = 1`. Special cases: `U G`, `G V`, the conjugate transpose `Gᴴ`, submatrices on
injective index maps, and `G x` for a unit vector `x`. Blocks `V₁ᴴ G` and `V₂ᴴ G` along orthogonal
frames are independent, which is how the randomized range finder splits a Gaussian test matrix.

## Main results

* `NLAlib.hasLaw_mul_mul_of_hasLaw_gaussianMatrix`: two-sided invariance.
* `NLAlib.hasLaw_const_mul_of_hasLaw_gaussianMatrix`,
  `NLAlib.hasLaw_mul_const_of_hasLaw_gaussianMatrix`.
* `NLAlib.hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`,
  `NLAlib.hasLaw_submatrix_of_hasLaw_gaussianMatrix`.
* `NLAlib.hasLaw_mulVec_of_hasLaw_gaussianMatrix`: `G x` for a unit vector `x`.
* `NLAlib.indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`: independence of orthogonal blocks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n p q : Type*} [Fintype m]
  [Fintype n] [Fintype p] [Fintype q] {X : Ω → Matrix m n ℝ}

/-- **Orthogonal invariance**: for `U` with orthonormal rows and `V` with orthonormal columns,
`U G V` is a standard Gaussian matrix. -/
theorem hasLaw_mul_mul_of_hasLaw_gaussianMatrix [DecidableEq p] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix m n) μ) {U : Matrix p m ℝ} (hU : HasOrthonormalCols Uᴴ)
    {V : Matrix n q ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => U * X ω * V) (gaussianMatrix p q) μ := by
  sorry

/-- `U G` is a standard Gaussian matrix when `U` has orthonormal rows. -/
theorem hasLaw_const_mul_of_hasLaw_gaussianMatrix [DecidableEq p]
    (hX : HasLaw X (gaussianMatrix m n) μ) {U : Matrix p m ℝ} (hU : HasOrthonormalCols Uᴴ) :
    HasLaw (fun ω => U * X ω) (gaussianMatrix p n) μ := by
  sorry

/-- `G V` is a standard Gaussian matrix when `V` has orthonormal columns. -/
theorem hasLaw_mul_const_of_hasLaw_gaussianMatrix [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix m n) μ) {V : Matrix n q ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => X ω * V) (gaussianMatrix m q) μ := by
  sorry

/-- The conjugate transpose (over `ℝ`, the transpose) of a Gaussian matrix is Gaussian. -/
theorem hasLaw_conjTranspose_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    HasLaw (fun ω => (X ω)ᴴ) (gaussianMatrix n m) μ := by
  sorry

/-- A submatrix of a Gaussian matrix on injective row and column maps is Gaussian. -/
theorem hasLaw_submatrix_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {r : p → m} (hr : Function.Injective r) {s : q → n} (hs : Function.Injective s) :
    HasLaw (fun ω => (X ω).submatrix r s) (gaussianMatrix p q) μ := by
  sorry

/-- `G x` is a standard Gaussian vector for a unit vector `x`. -/
theorem hasLaw_mulVec_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {x : n → ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    HasLaw (fun ω => X ω *ᵥ x) (gaussianVector m) μ := by
  sorry

/-- **Independence of orthogonal blocks**: for frames `V₁` and `V₂` with `V₁ᴴ V₂ = 0`, the blocks
`V₁ᴴ G` and `V₂ᴴ G` are independent (and each is a standard Gaussian matrix, by
`hasLaw_const_mul_of_hasLaw_gaussianMatrix`). -/
theorem indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix [DecidableEq p] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix m n) μ) {V₁ : Matrix m p ℝ} {V₂ : Matrix m q ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) :
    IndepFun (fun ω => V₁ᴴ * X ω) (fun ω => V₂ᴴ * X ω) μ := by
  sorry

end NLAlib
