/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Coefficients
public import NLAlib.Eigensolvers.ShiftedQR.RotationLoops
public import NLAlib.Eigensolvers.ShiftedQR.Shift
public import NLAlib.Ops.RoutineSyntax

/-!
# A scalar implementation of one shifted QR step

The working matrix is initialized to the raw matrix minus the supplied diagonal shift.
The output starts as a copy of the raw matrix. Each round computes its Givens coefficients
from the working column, rotates the working rows, and conjugates the output by the same
rotation. Coefficients and the working matrix are scoped scratch. No matrix multiplication,
QR decomposition or rotation is an operation of the emitted scalar signature.

## Main results

* `NLAlib.ShiftedQR.round`: the shared working/output state transition.
* `NLAlib.ShiftedQR.shiftedStep`: the complete single-shift implementation.
* `NLAlib.ShiftedQR.shiftedStepRoutine`: that implementation with its interface.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Compute coefficients from column `k` of W, rotate W on the left, and conjugate Z.
The supplied coefficient buffer Cf has four words; C and S are its disjoint adjacent pairs.
The interface is `[n,k] (W,Z,Cf) -> (W,Z)`. -/
def round : Stmt Op Tst :=
  .seq (.frame []
    [⟨0, .var 2 + .const 2 * (.var 1 * .var 0 + .var 1)⟩,
      ⟨0, .var 2 + .const 2 * (.var 1 * .var 0 + .var 1 + .const 1)⟩,
      ⟨2, .var 4⟩, ⟨2, .var 4 + .const 2⟩] coefficients)
    (.seq (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨2, .var 4⟩, ⟨2, .var 4 + .const 2⟩, ⟨3, .var 5⟩]
      rotateRows)
      (.seq (.frame [.var 0, .var 1]
        [⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨2, .var 4 + .const 2⟩, ⟨4, .var 6⟩]
        rotateRows)
        (.frame [.var 0, .var 1]
          [⟨4, .var 6⟩, ⟨2, .var 4⟩, ⟨2, .var 4 + .const 2⟩, ⟨4, .var 6⟩]
          rotateColumns)))

/-- Sweep the adjacent Givens rotations over initialized working and output matrices. The
coefficient arena is reused in every round. The interface is `[n] (W,Z,Cf) -> (W,Z)`. -/
def sweep : Stmt Op Tst :=
  .loop (.var 0 - .const 1)
    (.frame [.var 0, .var 6]
      [⟨0, .var 1⟩, ⟨1, .var 2⟩, ⟨2, .var 3⟩,
        ⟨3, .var 4⟩, ⟨4, .var 5⟩] round)

/-- Initialize W/Z and execute the `n-1` actual adjacent-row rotations. The matrix W and
four coefficient words are allocated once and freed on return. Inputs are A and the supplied
complex shift; the only surviving output is Z. -/
def shiftedStep : Stmt Op Tst :=
  .alloc (.const 2 * (.var 0 * .var 0))
    (.alloc (.const 4)
      (.seq (.frame [.var 0]
        [⟨0, .var 1⟩, ⟨1, .var 2⟩, ⟨3, .const 0⟩, ⟨2, .var 3⟩]
        initializeState)
        (.frame [.var 0]
          [⟨3, .const 0⟩, ⟨2, .var 3⟩, ⟨4, .const 0⟩,
            ⟨3, .const 0⟩, ⟨2, .var 3⟩] sweep)))

/-- One shifted QR step with its interface: `[n] (A : 2 n², s : 2) → (Z : 2 n²)` at order `n`,
separated by block. The result is apart from the matrix and the shift, which may overlap; the
working matrix and the coefficients are allocated inside. -/
def shiftedStepRoutine : Routine Op Tst :=
  routine% [n] (A : 2 * (n * n), s : 2) → (Z : 2 * (n * n)) by blocks := shiftedStep

end NLAlib.ShiftedQR
