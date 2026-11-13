/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Binary operation labels in numerical error relations

These labels index operation-dependent mathematical error relations in ordered arithmetic
traces. They contain no interpreter or program syntax. The historical namespace preserves the
numerical statements independently of the retired evaluator.

## Main results

* `NLAlib.Computation.BinOp` distinguishes the mathematical operation labels.
-/

@[expose] public section

namespace NLAlib.Computation

/-- Binary operations: field arithmetic, and integer and bitwise operations on words. -/
inductive BinOp where
  /-- Addition. -/
  | add
  /-- Subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Division. -/
  | div
  /-- Shift left. -/
  | shl
  /-- Shift right. -/
  | shr
  /-- Bitwise and. -/
  | band
  /-- Bitwise or. -/
  | bor
  /-- Bitwise exclusive or. -/
  | bxor

end NLAlib.Computation
