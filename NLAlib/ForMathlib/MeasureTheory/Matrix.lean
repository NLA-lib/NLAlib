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
* `Measurable.matrix_add`, `Measurable.matrix_sub`, `Measurable.matrix_neg`,
  `Measurable.matrix_smul`, `Measurable.matrix_const_smul`: the linear operations.
* `Measurable.matrix_mul`, `Measurable.matrix_mulVec`, `Measurable.matrix_vecMul`,
  `Measurable.matrix_det`, `Measurable.matrix_inv`, and the other operations.
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
    [SecondCountableTopology α] [Countable m] [Countable n] : BorelSpace (Matrix m n α) :=
  inferInstanceAs (BorelSpace (m → n → α))

/-- The entries of a matrix are measurable functions of the matrix. -/
theorem measurable_apply [MeasurableSpace α] (i : m) (j : n) :
    Measurable fun A : Matrix m n α => A i j :=
  (measurable_pi_apply j).comp (measurable_pi_apply (X := fun _ : m => n → α) i)

/-- A matrix-valued function is measurable exactly when its entries are. -/
theorem measurable_iff [MeasurableSpace α] [MeasurableSpace β] {f : β → Matrix m n α} :
    Measurable f ↔ ∀ i j, Measurable fun x => f x i j := by
  refine ⟨fun hf i j => (measurable_apply i j).comp hf, fun hf => ?_⟩
  exact measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hf i j

end Matrix

variable {α β : Type*} {l m n : Type*} [MeasurableSpace β]

/-- The transpose of a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_transpose [MeasurableSpace α] {f : β → Matrix m n α}
    (hf : Measurable f) : Measurable fun x => (f x)ᵀ := by
  exact Matrix.measurable_iff.2 fun i j => (Matrix.measurable_apply j i).comp hf

/-- The conjugate transpose of a measurable matrix-valued function is measurable, when `star` is
measurable on the entries (Mathlib has no class for this). -/
theorem Measurable.matrix_conjTranspose [MeasurableSpace α] [Star α]
    (hstar : Measurable (star : α → α)) {f : β → Matrix m n α} (hf : Measurable f) :
    Measurable fun x => (f x)ᴴ := by
  exact Matrix.measurable_iff.2 fun i j => hstar.comp ((Matrix.measurable_apply j i).comp hf)

/-- The sum of measurable matrix-valued functions is measurable. -/
theorem Measurable.matrix_add [MeasurableSpace α] [Add α] [MeasurableAdd₂ α]
    {f g : β → Matrix m n α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x + g x := by
  exact Matrix.measurable_iff.2 fun i j =>
    ((Matrix.measurable_apply i j).comp hf).add ((Matrix.measurable_apply i j).comp hg)

/-- The difference of measurable matrix-valued functions is measurable. -/
theorem Measurable.matrix_sub [MeasurableSpace α] [Sub α] [MeasurableSub₂ α]
    {f g : β → Matrix m n α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x - g x := by
  exact Matrix.measurable_iff.2 fun i j =>
    ((Matrix.measurable_apply i j).comp hf).sub ((Matrix.measurable_apply i j).comp hg)

/-- The negative of a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_neg [MeasurableSpace α] [Neg α] [MeasurableNeg α]
    {f : β → Matrix m n α} (hf : Measurable f) : Measurable fun x => -f x := by
  exact Matrix.measurable_iff.2 fun i j => ((Matrix.measurable_apply i j).comp hf).neg

/-- A measurable scalar function times a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_smul {γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] [SMul γ α]
    [MeasurableSMul₂ γ α] {c : β → γ} {f : β → Matrix m n α} (hc : Measurable c)
    (hf : Measurable f) : Measurable fun x => c x • f x := by
  exact Matrix.measurable_iff.2 fun i j => hc.smul ((Matrix.measurable_apply i j).comp hf)

/-- A constant scalar multiple of a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_const_smul {γ : Type*} [MeasurableSpace α] [SMul γ α]
    [MeasurableConstSMul γ α] {f : β → Matrix m n α} (hf : Measurable f) (c : γ) :
    Measurable fun x => c • f x := by
  exact Matrix.measurable_iff.2 fun i j => ((Matrix.measurable_apply i j).comp hf).const_smul c

/-- The product of measurable matrix-valued functions is measurable. -/
theorem Measurable.matrix_mul [MeasurableSpace α] [Fintype m] [NonUnitalNonAssocSemiring α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] {f : β → Matrix l m α} {g : β → Matrix m n α}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x * g x := by
  refine Matrix.measurable_iff.2 fun i k => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_fun_sum _ fun j _ =>
    ((Matrix.measurable_apply i j).comp hf).mul ((Matrix.measurable_apply j k).comp hg)

/-- The action of a measurable matrix-valued function on a measurable vector is measurable. -/
theorem Measurable.matrix_mulVec [MeasurableSpace α] [Fintype n] [NonUnitalNonAssocSemiring α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] {f : β → Matrix m n α} {v : β → n → α}
    (hf : Measurable f) (hv : Measurable v) : Measurable fun x => f x *ᵥ v x := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_fun_sum _ fun j _ =>
    ((Matrix.measurable_apply i j).comp hf).mul ((measurable_pi_apply j).comp hv)

/-- The action of a measurable matrix-valued function on a measurable row vector is
measurable. -/
theorem Measurable.matrix_vecMul [MeasurableSpace α] [Fintype m] [NonUnitalNonAssocSemiring α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] {v : β → m → α} {f : β → Matrix m n α}
    (hv : Measurable v) (hf : Measurable f) : Measurable fun x => v x ᵥ* f x := by
  refine measurable_pi_iff.2 fun j => ?_
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.measurable_fun_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hv).mul ((Matrix.measurable_apply i j).comp hf)

/-- The trace of a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_trace [MeasurableSpace α] [Fintype n] [AddCommMonoid α]
    [MeasurableAdd₂ α] {f : β → Matrix n n α} (hf : Measurable f) :
    Measurable fun x => (f x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.measurable_fun_sum _ fun i _ => (Matrix.measurable_apply i i).comp hf

/-- The determinant of a measurable matrix-valued function is measurable. -/
theorem Measurable.matrix_det [MeasurableSpace α] [Fintype n] [DecidableEq n] [CommRing α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] [MeasurableNeg α] {f : β → Matrix n n α}
    (hf : Measurable f) : Measurable fun x => (f x).det := by
  simp only [Matrix.det_apply]
  refine Finset.measurable_fun_sum _ fun σ _ => ?_
  have hprod : Measurable fun x => ∏ i, f x (σ i) i :=
    Finset.measurable_fun_prod _ fun i _ => (Matrix.measurable_apply (σ i) i).comp hf
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa only [h, one_smul] using hprod
  · simp only [h, Units.neg_smul, one_smul]
    exact hprod.neg

/-- The powers of a measurable matrix-valued function are measurable. -/
theorem Measurable.matrix_pow [MeasurableSpace α] [Fintype n] [DecidableEq n] [Semiring α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] {f : β → Matrix n n α}
    (hf : Measurable f) (k : ℕ) : Measurable fun x => f x ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using measurable_const
  | succ k ih => simpa only [pow_succ] using ih.matrix_mul hf

/-- The inverse of a measurable matrix-valued function over a field is measurable. -/
theorem Measurable.matrix_inv [MeasurableSpace α] [Fintype n] [DecidableEq n] [Field α]
    [MeasurableAdd₂ α] [MeasurableMul₂ α] [MeasurableNeg α] [MeasurableInv α]
    {f : β → Matrix n n α} (hf : Measurable f) : Measurable fun x => (f x)⁻¹ := by
  have hdet : Measurable fun x => Ring.inverse (f x).det := by
    simp only [Ring.inverse_eq_inv']
    exact hf.matrix_det.inv
  refine Matrix.measurable_iff.2 fun i j => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul]
  refine hdet.mul (Measurable.matrix_det (Matrix.measurable_iff.2 fun a b => ?_))
  simp only [Matrix.updateRow_apply, Pi.single_apply]
  split_ifs
  · exact measurable_const
  · exact measurable_const
  · exact (Matrix.measurable_apply a b).comp hf
