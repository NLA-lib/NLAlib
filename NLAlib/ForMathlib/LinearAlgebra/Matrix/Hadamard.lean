/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Hadamard product inside the Kronecker product

The Hadamard product of two matrices is the submatrix of their Kronecker product on the diagonal
index pairs. Inequalities for Hadamard products follow from those for Kronecker products and for
compressions.

Also the distributivity of the Hadamard product over subtraction, the companion of Mathlib's
`Matrix.add_hadamard` and `Matrix.hadamard_add`.

## Main results

* `Matrix.hadamard_eq_submatrix_kronecker`.
* `Matrix.sub_hadamard`, `Matrix.hadamard_sub`.
-/

@[expose] public section

open scoped Kronecker

namespace Matrix

variable {R : Type*} {m n : Type*}

/-- The Hadamard product is the submatrix of the Kronecker product on the diagonal index pairs.
[HornJohnson1991, Lemma 5.1.1]. Port of `NLAlib.submatrix_kronecker_diagonal`. -/
theorem hadamard_eq_submatrix_kronecker [Mul R] (A B : Matrix m n R) :
    A ⊙ B = (A ⊗ₖ B).submatrix (fun i => (i, i)) (fun j => (j, j)) :=
  rfl

/-- The Hadamard product distributes over subtraction in its second factor. -/
theorem hadamard_sub [NonUnitalNonAssocRing R] (A B C : Matrix m n R) :
    A ⊙ (B - C) = A ⊙ B - A ⊙ C :=
  ext fun _ _ => mul_sub _ _ _

/-- The Hadamard product distributes over subtraction in its first factor. -/
theorem sub_hadamard [NonUnitalNonAssocRing R] (A B C : Matrix m n R) :
    (B - C) ⊙ A = B ⊙ A - C ⊙ A :=
  ext fun _ _ => sub_mul _ _ _

end Matrix
