/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Hermitian dilation

`NLAlib.dilation A` is the Hermitian block matrix with `A` and `Aᴴ` off the diagonal. It carries
statements about Hermitian matrices (eigenvalue perturbation, matrix concentration) to
rectangular matrices: its eigenvalues are plus and minus the singular values of `A`, and its
spectral norm is that of `A`. Those two facts are proved with the spectral stage; this file has
the algebra.

## Main definitions

* `NLAlib.dilation`: `fromBlocks 0 A Aᴴ 0`.

## Main results

* `NLAlib.isHermitian_dilation`: the dilation is Hermitian.
* `NLAlib.dilation_mul_dilation`: the square is block diagonal with blocks `A * Aᴴ`, `Aᴴ * A`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The **Hermitian dilation** of a rectangular matrix `A`: the block matrix with zero diagonal
blocks and off-diagonal blocks `A` and `Aᴴ`. [Tropp2015, §2.1.16]. Port of `NLAlib.dilation`. -/
def dilation (A : Matrix m n 𝕜) : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  Matrix.fromBlocks 0 A Aᴴ 0

/-- `dilation A` unfolds to `fromBlocks 0 A Aᴴ 0`. -/
theorem dilation_def (A : Matrix m n 𝕜) : dilation A = Matrix.fromBlocks 0 A Aᴴ 0 :=
  rfl

/-- The Hermitian dilation is Hermitian. Port of `NLAlib.isHermitian_dilation`. -/
theorem isHermitian_dilation (A : Matrix m n 𝕜) : (dilation A).IsHermitian := by
  sorry

/-- The dilation of the zero matrix is zero. -/
@[simp]
theorem dilation_zero : dilation (0 : Matrix m n 𝕜) = 0 := by
  sorry

/-- The dilation is additive. Port of `NLAlib.dilation_add`. -/
theorem dilation_add (A B : Matrix m n 𝕜) : dilation (A + B) = dilation A + dilation B := by
  sorry

/-- The dilation commutes with subtraction. -/
theorem dilation_sub (A B : Matrix m n 𝕜) : dilation (A - B) = dilation A - dilation B := by
  sorry

/-- The dilation commutes with negation. -/
theorem dilation_neg (A : Matrix m n 𝕜) : dilation (-A) = -dilation A := by
  sorry

/-- The dilation commutes with multiplication by a real scalar. It is not `𝕜`-linear, because
`Aᴴ` is conjugate-linear in `A`. -/
theorem dilation_smul_real (c : ℝ) (A : Matrix m n 𝕜) :
    dilation ((c : 𝕜) • A) = (c : 𝕜) • dilation A := by
  sorry

/-- The dilation commutes with finite sums. -/
theorem dilation_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n 𝕜) :
    dilation (∑ i ∈ s, A i) = ∑ i ∈ s, dilation (A i) := by
  sorry

/-- The dilation is injective. -/
theorem dilation_injective : Function.Injective (dilation : Matrix m n 𝕜 → _) := by
  sorry

/-- The square of the dilation is block diagonal, with blocks `A * Aᴴ` and `Aᴴ * A`.
[Tropp2015, (2.1.28)]. -/
theorem dilation_mul_dilation (A : Matrix m n 𝕜) :
    dilation A * dilation A = Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
  sorry

/-- The dilation acts on a pair `(y, x)` by `(A x, Aᴴ y)`. -/
theorem dilation_mulVec (A : Matrix m n 𝕜) (y : m → 𝕜) (x : n → 𝕜) :
    dilation A *ᵥ Sum.elim y x = Sum.elim (A *ᵥ x) (Aᴴ *ᵥ y) := by
  sorry

end NLAlib
