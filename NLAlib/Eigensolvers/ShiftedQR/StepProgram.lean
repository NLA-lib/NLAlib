/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Alg
public import NLAlib.Eigensolvers.ShiftedQR.Problem
public import NLAlib.Matrix.QRIteration.ShiftedQRConjugation
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Single-step shifted QR program and resources

One fixed scalar tree acts on the supplied matrix and shift, with uninitialized output
capacity. Its full count includes arithmetic, comparisons, control, address evaluation and
allocation. Work, span and scratch refer to that same tree and the shared unit-work scalar
profile. Resident payload includes the supplied uninitialized output capacity.

## Main results

* `NLAlib.ShiftedQR.stepProgram`: the raw three-buffer scalar program.
* `NLAlib.ShiftedQR.wellTyped_stepProgram`: its closed scalar signature.
* `NLAlib.ShiftedQR.stepSpecification`: mathematical output and complete resource manifest.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- A fixed scalar program for a matrix of order `n+1`; its three raw buffers are the input
matrix, complex shift, and output matrix. All intermediate state is scoped scratch. -/
def stepProgram : Program ScalarOp CmpTst 1 3 :=
  ⟨.frame [.var 0 + .const 1] [⟨0, .var 1⟩, ⟨1, .var 2⟩, ⟨2, .var 3⟩]
    shiftedStep.body⟩

/-- The fixed tree uses only the declared real scalar operations and operand comparisons. -/
theorem wellTyped_stepProgram :
    stepProgram.wellTyped RoundedScalarBlas.resources stepProblem.formats = true := by
  rfl

/-- The full count manifest of the actual scalar syntax, including structural charges. -/
noncomputable def stepBudget (d : Fin 1 → ℕ) : Count (ScalarOp ⊕ Bookkeeping) CmpTst :=
  staticCost stepProgram d

/-- The exact mathematical shifted step and all resources of its actual fixed scalar program.
The output matrix is represented by its actual packed words and all scoped buffers are freed. -/
noncomputable def stepSpecification : Specification ScalarOp CmpTst stepProblem where
  budget := stepBudget
  scratch := staticPeak RoundedScalarBlas.resources stepProgram
  work d := RoundedScalarBlas.resources.work (stepBudget d)
  span d := RoundedScalarBlas.resources.span (stepBudget d)
  memory d := 4 * ((d 0 + 1) * (d 0 + 1)) + 2 +
    staticPeak RoundedScalarBlas.resources stepProgram d
  good d x _ _ m := m.pos = 0 ∧ m.store.length = 3 ∧
    HoldsMatrix (2, 0) (shiftedQRStep (stepInputMatrix d x) (stepInputShift d x)) m.store

end NLAlib.ShiftedQR
