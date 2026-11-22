/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.Standard
public import NLAlib.Ops.RoutineProblem

/-!
# The oracle of a standard model

A standard model (`NLAlib.Ops.Standard.Model`) reaches its operator only through the product
`matvec`. When the operator is an unstored input of the problem of a routine, the model is
declared to read it (`NLAlib.Ops.Standard.Model.ReadsOperator`), and the product is the one
oracle of the certificate (`NLAlib.Ops.Standard.Model.oracles`).

## Main definitions

* `NLAlib.Ops.Standard.Model.ReadsOperator`: the operator of the model is the unstored input,
  and the allowance of the product depends on the input only through it.
* `NLAlib.Ops.Standard.Model.oracles`: the product is the only operation whose contract depends
  on the input.
-/

@[expose] public section

namespace NLAlib.Ops.Standard

variable {K : Type} [Inhabited K] {r b : ℕ} {R : Routine Operation CmpTst}
  {n : (Fin r → ℕ) → ℕ}

/-- The model reads the operator `op` of the unstored input: its matrix is that operator, and
the error allowance of its product depends on the input only through the unstored part. -/
structure Model.ReadsOperator (D : R.Domain K r b) (m : Model D.problem n)
    (op : (d : Fin r → ℕ) → D.Unstored d → Matrix (Fin (n d)) (Fin (n d)) ℝ) : Prop where
  /-- The matrix of the model is the operator of the unstored input. -/
  matrix : ∀ d (X : D.problem.Input d), m.matrix d X = op d (D.unstored d X.val.1)
  /-- The allowance of the product is determined by the unstored input. -/
  allowance : ∀ d (X Y : D.problem.Input d), D.unstored d X.val.1 = D.unstored d Y.val.1 →
    m.matvecAllowance d X = m.matvecAllowance d Y

/-- The product is the oracle of a standard model that reads its operator from the unstored
input: scalar arithmetic and the vector operations have one contract at every size and input,
and the contract of the product depends on the input only through the operator. The cost of a
certificate in this model is counted in calls of the product and in vector operations. -/
def Model.oracles (D : R.Domain K r b) (m : Model D.problem n)
    (op : (d : Fin r → ℕ) → D.Unstored d → Matrix (Fin (n d)) (Fin (n d)) ℝ)
    (h : m.ReadsOperator D op) : D.Oracles m.access where
  ops := [.matvec]
  operation o ho d x d' x' := by
    cases o with
    | scalar a => rfl
    | blas a => rfl
    | matvec => exact absurd (by simp) ho
  query _ _ _ _ _ := rfl
  through o _ d X Y hXY := by
    cases o with
    | scalar a => rfl
    | blas a => rfl
    | matvec =>
      change (matvecErrorRel m.decode (m.matrix d X) _).spec _ =
        (matvecErrorRel m.decode (m.matrix d Y) _).spec _
      rw [h.matrix, h.matrix, hXY, h.allowance d X Y hXY]

end NLAlib.Ops.Standard
