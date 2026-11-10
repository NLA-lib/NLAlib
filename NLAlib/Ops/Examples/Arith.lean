/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Ops.Logic
public import NLAlib.Ops.Transfer

/-!
# Example signature: scalar arithmetic

The arithmetic operations are operations like any other (`NLAlib.Ops.Examples.AOp`). Their
contract is functional: each is a function of a machine `NLAlib.Ops.Examples.Machine`
(`NLAlib.Ops.Examples.IsArith`), and the machine meets the standard model of rounded arithmetic
at a unit roundoff `u` for a decoding `dec` (`NLAlib.Ops.Examples.StdModel`). The first is about
the interpretation, the second is mathematics about functions.

Witness (`NLAlib.Ops.Examples.exists_arith`): exact real arithmetic meets both for every `u ≥ 0`.
## Main results

* `NLAlib.Ops.Examples.exists_arith`: the contracts of scalar arithmetic can be met.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

/-- The scalar operations. A literal is an operation indexed by a rational. -/
inductive AOp where
  /-- The literal `q`. -/
  | lit (q : ℚ)
  /-- Addition. -/
  | add
  /-- Subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Negation. -/
  | neg
  /-- Square root. -/
  | sqrt
  deriving DecidableEq

/-- A machine: the functions computed by the scalar operations on words. -/
structure Machine (K : Type) where
  /-- The word of a literal. -/
  lit : ℚ → K
  /-- Addition. -/
  add : K → K → K
  /-- Subtraction. -/
  sub : K → K → K
  /-- Multiplication. -/
  mul : K → K → K
  /-- Negation. -/
  neg : K → K
  /-- Square root. -/
  sqrt : K → K

variable {K : Type}

/-- The block function of each scalar operation of a machine. -/
def Machine.fn (M : Machine K) : AOp → BlockFn K
  | .lit q => .const (M.lit q)
  | .add => .bin fun a b => some (M.add a b)
  | .sub => .bin fun a b => some (M.sub a b)
  | .mul => .bin fun a b => some (M.mul a b)
  | .neg => .un fun a => some (M.neg a)
  | .sqrt => .un fun a => some (M.sqrt a)

/-- No restriction on operands: scalar operations may alias. -/
abbrev AnyOperands : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop := fun _ _ _ => True

/-- **The functional contract of scalar arithmetic**: every operation is the function of the
machine `M`, on all operands. -/
def IsArith (M : Machine K) (I : Interp AOp K) : Prop :=
  ∀ o, I.IsFn .total o (M.fn o) AnyOperands

/-- **The standard model** of rounded arithmetic at the unit roundoff `u`, for the decoding `dec`:
a property of the functions of the machine. -/
structure StdModel (u : ℝ) (dec : K → ℝ) (M : Machine K) : Prop where
  /-- Zero is exact. -/
  zero : dec (M.lit 0) = 0
  /-- Rounded addition. -/
  add : ∀ a b, |dec (M.add a b) - (dec a + dec b)| ≤ u * |dec a + dec b|
  /-- Rounded subtraction. -/
  sub : ∀ a b, |dec (M.sub a b) - (dec a - dec b)| ≤ u * |dec a - dec b|
  /-- Rounded multiplication. -/
  mul : ∀ a b, |dec (M.mul a b) - dec a * dec b| ≤ u * |dec a * dec b|
  /-- Negation is exact. -/
  neg : ∀ a, dec (M.neg a) = -dec a
  /-- Rounded square root of a nonnegative number. -/
  sqrt : ∀ a, 0 ≤ dec a → |dec (M.sqrt a) - √(dec a)| ≤ u * √(dec a)

/-- Exact real arithmetic. -/
noncomputable def exactMachine : Machine ℝ where
  lit q := q
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  neg a := -a
  sqrt a := √a

theorem stdModel_exact {u : ℝ} (hu : 0 ≤ u) : StdModel u id exactMachine where
  zero := by simp [exactMachine]
  add a b := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  sub a b := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  mul a b := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  neg a := rfl
  sqrt a _ := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (Real.sqrt_nonneg _)

/-- **Witness**: for every `u ≥ 0` there are a carrier, a decoding, a machine meeting the
standard model and an interpretation meeting the functional contract. -/
theorem exists_arith {u : ℝ} (hu : 0 ≤ u) :
    ∃ (K : Type) (dec : K → ℝ) (M : Machine K) (I : Interp AOp K),
      StdModel u dec M ∧ IsArith M I :=
  ⟨ℝ, id, exactMachine, Interp.ofFns exactMachine.fn, stdModel_exact hu,
    fun o => Interp.ofFns_isFn _ _ o _⟩

end NLAlib.Ops.Examples
