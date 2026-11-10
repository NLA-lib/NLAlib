/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Ops.Tactic
public import NLAlib.Ops.Profile

/-!
# Catalog: scalar arithmetic

The group `NLAlib.Ops.ScalarOp` of scalar operations and its two contracts.

* Functional (`NLAlib.Ops.IsScalar`): every scalar operation is the function of a machine
  `NLAlib.Ops.Machine K` on words, on all operands (scalar operations may alias).
* Mathematics (`NLAlib.Ops.StdModel`): the standard model of rounded arithmetic at the unit
  roundoff `u`, a property of the functions of the machine on decoded values. The unit roundoff
  is a parameter; nothing fixes one precision. The model is unconditional: it has no overflow or
  underflow, so a bounded format meets it only on a safe range, which is another contract.

Division is specified only for a divisor that decodes to a nonzero number, and the square root
only for a nonnegative argument: outside, the model says nothing of the result, so no theorem
can be proved through a division by zero. Every literal is rounded (`StdModel.lit`), so zero is
exact.

Witnesses: exact real arithmetic meets both for every `u ≥ 0` (`NLAlib.Ops.exists_isScalar`),
and so does the machine that inflates every result by the factor `1 + u`
(`NLAlib.Ops.stdModel_infl`), which is not exact and attains the bounds.

## Main results

* `NLAlib.Ops.exists_isScalar`: the contracts of scalar arithmetic can be met.
* `NLAlib.Ops.StdModel.abs_le`, `NLAlib.Ops.StdModel.abs_add_mul_sub_le`: one and two rounded
  operations.
-/

@[expose] public section

namespace NLAlib.Ops

/-- The scalar operations. A literal is an operation indexed by a rational. -/
inductive ScalarOp where
  /-- The literal `q`. -/
  | lit (q : ℚ)
  /-- Addition. -/
  | add
  /-- Subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Division. -/
  | div
  /-- Negation. -/
  | neg
  /-- Square root. -/
  | sqrt
  /-- Copy of a word. -/
  | copy
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
  /-- Division. -/
  div : K → K → K
  /-- Negation. -/
  neg : K → K
  /-- Square root. -/
  sqrt : K → K

variable {K Op Tst : Type}

/-- The block function of each scalar operation of a machine. -/
@[storeNF] def Machine.fn (M : Machine K) : ScalarOp → BlockFn K
  | .lit q => .const (M.lit q)
  | .add => .bin fun a b => some (M.add a b)
  | .sub => .bin fun a b => some (M.sub a b)
  | .mul => .bin fun a b => some (M.mul a b)
  | .div => .bin fun a b => some (M.div a b)
  | .neg => .un fun a => some (M.neg a)
  | .sqrt => .un fun a => some (M.sqrt a)
  | .copy => .un fun a => some a

/-- No restriction on operands: scalar operations may alias. -/
abbrev AnyOperands : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop := fun _ _ _ => True

/-- **The functional contract of scalar arithmetic**: every scalar operation of the signature is
the function of the machine `M`, on all operands. -/
def IsScalar [Has ScalarOp Op] (M : Machine K) (I : Interp Op Tst K) : Prop :=
  ∀ a : ScalarOp, I.IsFn .total (Has.inj a) (M.fn a) AnyOperands

/-- **The standard model** of rounded arithmetic at the unit roundoff `u`, for the decoding `dec`:
a property of the functions of the machine. No overflow, no underflow. -/
structure StdModel (u : ℝ) (dec : K → ℝ) (M : Machine K) : Prop where
  /-- A literal is rounded. -/
  lit : ∀ q : ℚ, |dec (M.lit q) - q| ≤ u * |(q : ℝ)|
  /-- Rounded addition. -/
  add : ∀ a b, |dec (M.add a b) - (dec a + dec b)| ≤ u * |dec a + dec b|
  /-- Rounded subtraction. -/
  sub : ∀ a b, |dec (M.sub a b) - (dec a - dec b)| ≤ u * |dec a - dec b|
  /-- Rounded multiplication. -/
  mul : ∀ a b, |dec (M.mul a b) - dec a * dec b| ≤ u * |dec a * dec b|
  /-- Rounded division, by a divisor that is not zero. Nothing is said of a division by zero. -/
  div : ∀ a b, dec b ≠ 0 → |dec (M.div a b) - dec a / dec b| ≤ u * |dec a / dec b|
  /-- Negation is exact. -/
  neg : ∀ a, dec (M.neg a) = -dec a
  /-- Rounded square root of a nonnegative number. -/
  sqrt : ∀ a, 0 ≤ dec a → |dec (M.sqrt a) - √(dec a)| ≤ u * √(dec a)

/-- Zero is exact. -/
theorem StdModel.zero {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M) :
    dec (M.lit 0) = 0 := by
  simpa using hM.lit 0

/-- A number within the relative error `e` of `x` is at most `(1 + e) |x|` in absolute value. -/
theorem abs_le_of_abs_sub_le {r x e : ℝ} (h : |r - x| ≤ e * |x|) : |r| ≤ (1 + e) * |x| := by
  have := abs_add_le x (r - x)
  rw [add_sub_cancel] at this
  linarith

/-- One rounded `y + α x`: the relative error `(1 + u) ^ 2 - 1` on `|y| + |α x|`. -/
theorem StdModel.abs_add_mul_sub_le {u : ℝ} {dec : K → ℝ} {M : Machine K}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (al x y : K) :
    |dec (M.add y (M.mul al x)) - (dec y + dec al * dec x)| ≤
      ((1 + u) ^ 2 - 1) * (|dec y| + |dec al * dec x|) := by
  have h1 := hM.mul al x
  have h2 := hM.add y (M.mul al x)
  generalize dec (M.add y (M.mul al x)) = r at h2
  generalize dec (M.mul al x) = p at h1 h2
  generalize dec al * dec x = q at h1
  generalize dec y = Y at h2
  have hp := abs_le_of_abs_sub_le h1
  have hA : |r - (Y + p)| ≤ u * (|Y| + (|q| + u * |q|)) :=
    h2.trans (mul_le_mul_of_nonneg_left ((abs_add_le Y p).trans (by linarith)) hu)
  have h3 : |r - (Y + q)| ≤ |r - (Y + p)| + |p - q| := by
    have := abs_add_le (r - (Y + p)) (p - q)
    rwa [show r - (Y + p) + (p - q) = r - (Y + q) by ring] at this
  nlinarith [abs_nonneg Y, abs_nonneg q, mul_nonneg hu (abs_nonneg Y),
    mul_nonneg (mul_nonneg hu hu) (abs_nonneg Y), mul_nonneg hu (abs_nonneg q)]

/-- Exact real arithmetic. -/
noncomputable def exactMachine : Machine ℝ where
  lit q := q
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  div a b := a / b
  neg a := -a
  sqrt a := √a

theorem stdModel_exact {u : ℝ} (hu : 0 ≤ u) : StdModel u id exactMachine where
  lit q := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  add a b := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  sub a b := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  mul a b := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  div a b _ := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (abs_nonneg _)
  neg a := rfl
  sqrt a _ := by
    simp only [exactMachine, id, sub_self, abs_zero]
    exact mul_nonneg hu (Real.sqrt_nonneg _)

/-- The machine that inflates every rounded result by the factor `1 + u`: not exact, and the
bounds of the standard model are attained. -/
noncomputable def inflMachine (u : ℝ) : Machine ℝ where
  lit q := q * (1 + u)
  add a b := (a + b) * (1 + u)
  sub a b := (a - b) * (1 + u)
  mul a b := a * b * (1 + u)
  div a b := a / b * (1 + u)
  neg a := -a
  sqrt a := √a * (1 + u)

theorem abs_mul_one_add_sub (u x : ℝ) (hu : 0 ≤ u) : |x * (1 + u) - x| ≤ u * |x| := by
  rw [show x * (1 + u) - x = u * x by ring, abs_mul, abs_of_nonneg hu]

/-- **A witness that is not exact**: the inflating machine meets the standard model at `u`. -/
theorem stdModel_infl {u : ℝ} (hu : 0 ≤ u) : StdModel u id (inflMachine u) where
  lit q := abs_mul_one_add_sub u q hu
  add a b := abs_mul_one_add_sub u (a + b) hu
  sub a b := abs_mul_one_add_sub u (a - b) hu
  mul a b := abs_mul_one_add_sub u (a * b) hu
  div a b _ := abs_mul_one_add_sub u (a / b) hu
  neg a := rfl
  sqrt a _ := by
    have := abs_mul_one_add_sub u (√a) hu
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this

/-- An interpretation given by the block functions of a machine on the scalar operations (and
anything on the others) meets the functional contract. -/
theorem isScalar_ofFns [Has ScalarOp Op] (M : Machine K) (F : Op → BlockFn K)
    (hF : ∀ a, F (Has.inj a) = M.fn a) : IsScalar M (Interp.ofFns F : Interp Op Tst K) :=
  fun a => hF a ▸ Interp.ofFns_isFn F _ _ _

/-- **Witness**: for every `u ≥ 0` there are a carrier, a decoding, a machine meeting the
standard model and an interpretation meeting the functional contract. -/
theorem exists_isScalar {u : ℝ} (hu : 0 ≤ u) :
    ∃ (K : Type) (dec : K → ℝ) (M : Machine K) (I : Interp ScalarOp Empty K),
      StdModel u dec M ∧ IsScalar M I :=
  ⟨ℝ, id, exactMachine, Interp.ofFns exactMachine.fn, stdModel_exact hu,
    isScalar_ofFns _ _ fun _ => rfl⟩

end NLAlib.Ops
