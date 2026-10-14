/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# Bilinear forms of a matrix as dot products of flattened matrices

The bilinear form `x ⬝ᵥ (G *ᵥ y)` is the dot product of the flattened matrix
`Function.uncurry G` with the flattened outer product `fun p => x p.1 * y p.2`, and dot products
of flattened outer products factor. Together they turn a bilinear form of a random matrix into a
linear form of its entries (Gaussian comparison for random matrices). Upstream candidates for
`Mathlib.Data.Matrix.Mul`.

## Main results

* `Matrix.dotProduct_mulVec_eq_dotProduct_uncurry`: `x ⬝ᵥ (G *ᵥ y)` as a dot product with
  `Function.uncurry G`.
* `dotProduct_mul_eq_mul_dotProduct`: the dot product of two flattened outer products is
  `(x ⬝ᵥ x') * (y ⬝ᵥ y')`.
-/

@[expose] public section

open scoped Matrix

variable {R : Type*} [CommSemiring R] {m n : Type*} [Fintype m] [Fintype n]

/-- **Dot products of flattened outer products factor**:
`(fun p => x p.1 * y p.2) ⬝ᵥ (fun p => x' p.1 * y' p.2) = (x ⬝ᵥ x') * (y ⬝ᵥ y')`. -/
theorem dotProduct_mul_eq_mul_dotProduct (x x' : m → R) (y y' : n → R) :
    (fun p : m × n => x p.1 * y p.2) ⬝ᵥ (fun p => x' p.1 * y' p.2) = (x ⬝ᵥ x') * (y ⬝ᵥ y') := by
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

namespace Matrix

/-- **A bilinear form is a linear form of the entries**: `x ⬝ᵥ (G *ᵥ y)` is the dot product of
the flattened outer product `fun p => x p.1 * y p.2` with the flattened matrix
`Function.uncurry G`. -/
theorem dotProduct_mulVec_eq_dotProduct_uncurry (x : m → R) (G : Matrix m n R) (y : n → R) :
    x ⬝ᵥ (G *ᵥ y) = (fun p : m × n => x p.1 * y p.2) ⬝ᵥ Function.uncurry G := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = _ * G i j
  ring

end Matrix
