/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Routine
public import NLAlib.Ops.RoutineLink

/-!
# Example: a routine implements an operation

The routine `NLAlib.Ops.Examples.Routines.sum` implements the operation contract of `sum` of
the level-one catalog: its admission, an output in a buffer different from that of the input, is
the separation of the routine. The certificate of the implementation against the contract is
then a consequence of `NLAlib.Ops.Routine.Meets`, with no second proof about the tree.

## Main results

* `NLAlib.Ops.Examples.Routines.sum_implements`: the routine implements the contract.
* `NLAlib.Ops.Examples.Routines.sum_satisfies`: the implementation satisfies the contract.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Routines

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]

/-- Sequential summation satisfies the contract of the operation `sum` with the error
`(1 + u) ^ (n - 1) - 1`, as a consequence of the judgment of the routine. -/
theorem sum_satisfies {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) (ok : ℕ → Prop) :
    ((sum (Op := Op) (Tst := Tst)).impl).Satisfies I .total
      ((sumRel dec fun n => (1 + u) ^ (n - 1) - 1).spec (OutApart ok)) :=
  (sum_meets hI hM hu).satisfies_ofRel (sumSeqRoutine_implements dec _ ok) fun _ _ _ _ => trivial

end NLAlib.Ops.Examples.Routines
