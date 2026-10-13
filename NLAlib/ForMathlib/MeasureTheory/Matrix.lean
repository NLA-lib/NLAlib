/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Measurability of matrix-valued functions

Matrices carry the product σ-algebra. This file provides the instance, which Mathlib does not
have, the fact that it is the Borel σ-algebra of the product topology when the entries are
second countable, and measurability of the algebraic operations on matrices. Upstream candidate
for a file `Mathlib.MeasureTheory.Constructions.Matrix`.

## Main definitions

* `Matrix.instMeasurableSpace`: the product σ-algebra on matrices.

## Main results

* `Matrix.measurable_iff`: a matrix-valued function is measurable exactly when its entries are.
* `Matrix.instBorelSpace`.
* `Measurable.matrix_mul`, `Measurable.matrix_det`, `Measurable.matrix_inv`, and the other
  operations.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {α β : Type*} {l m n : Type*}

/-- The product σ-algebra on matrices. -/
instance instMeasurableSpace [MeasurableSpace α] : MeasurableSpace (Matrix m n α) :=
  MeasurableSpace.pi

/-- Matrices over a second countable Borel space, with countable index types, form a Borel
space. -/
instance instBorelSpace [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] [Countable m] [Countable n] : BorelSpace (Matrix m n α) := by
  sorry

/-- The entries of a matrix are measurable functions of the matrix. -/
theorem measurable_apply [MeasurableSpace α] (i : m) (j : n) :
    Measurable fun A : Matrix m n α => A i j := by
  sorry

/-- A matrix-valued function is measurable exactly when its entries are. -/
theorem measurable_iff [MeasurableSpace α] [MeasurableSpace β] {f : β → Matrix m n α} :
    Measurable f ↔ ∀ i j, Measurable fun x => f x i j := by
  sorry

end Matrix

variable {α β : Type*} {l m n : Type*} [MeasurableSpace β]

/-- The transpose of a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_transpose [MeasurableSpace α] {f : β → Matrix m n α}
    (hf : Measurable f) : Measurable fun x => (f x)ᵀ := by
  sorry

/-- The conjugate transpose of a measurable matrix-valued function is measurable, when `star` is
measurable on the entries (Mathlib has no class for this). -/
theorem Measurable.matrix_conjTranspose [MeasurableSpace α] [Star α]
    (hstar : Measurable (star : α → α)) {f : β → Matrix m n α} (hf : Measurable f) :
    Measurable fun x => (f x)ᴴ := by
  sorry

/-- The sum of measurable matrix-valued functions is measurable. -/
theorem Measurable.matrix_add [MeasurableSpace α] [Add α] [MeasurableAdd₂ α]
    {f g : β → Matrix m n α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x + g x := by
  sorry

/-- The product of measurable matrix-valued functions is measurable. -/
theorem Measurable.matrix_mul [MeasurableSpace α] [Fintype m] [NonUnitalNonAssocSemiring α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] {f : β → Matrix l m α} {g : β → Matrix m n α}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x * g x := by
  sorry

/-- The action of a measurable matrix-valued function on a measurable vector is measurable. -/
theorem Measurable.matrix_mulVec [MeasurableSpace α] [Fintype n] [NonUnitalNonAssocSemiring α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] {f : β → Matrix m n α} {v : β → n → α}
    (hf : Measurable f) (hv : Measurable v) : Measurable fun x => f x *ᵥ v x := by
  sorry

/-- The trace of a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_trace [MeasurableSpace α] [Fintype n] [AddCommMonoid α]
    [MeasurableAdd₂ α] {f : β → Matrix n n α} (hf : Measurable f) :
    Measurable fun x => (f x).trace := by
  sorry

/-- The determinant of a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_det [MeasurableSpace α] [Fintype n] [DecidableEq n] [CommRing α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] [MeasurableNeg α] {f : β → Matrix n n α}
    (hf : Measurable f) : Measurable fun x => (f x).det := by
  sorry

/-- The powers of a measurable matrix-valued function are measurable. -/
theorem Measurable.matrix_pow [MeasurableSpace α] [Fintype n] [DecidableEq n] [Semiring α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] {f : β → Matrix n n α}
    (hf : Measurable f) (k : ℕ) : Measurable fun x => f x ^ k := by
  sorry

/-- The inverse of a measurable matrix-valued function over a field is measurable. -/
theorem Measurable.matrix_inv [MeasurableSpace α] [Fintype n] [DecidableEq n] [Field α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] [MeasurableNeg α] [MeasurableInv α]
    {f : β → Matrix n n α} (hf : Measurable f) : Measurable fun x => (f x)⁻¹ := by
  sorry
