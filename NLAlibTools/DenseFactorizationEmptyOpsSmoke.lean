/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.Cholesky.PivotedRoutine
import NLAlib.Matrix.Factorizations.Cholesky.InPlace
import NLAlib.Matrix.Factorizations.LDL.Routine

/-!
# Handle-free raw empty dense factorizations

Every backend instruction rejects, and several raw operand frames have missing or invalid
handles, excessive offsets, aliases or a collision with the would-be fresh scratch handle.
At order zero all seven scalar bodies retain the entire caller memory and tape position.
Positive-order cases with valid initialized inputs reject, checking that the rejecting backend
is active. The ordinary declared input-slot domains are unchanged by this raw-body guarantee.
-/

set_option linter.hashCommand false

open NLAlib.Ops

namespace NLAlibTools.DenseFactorizationEmptyOpsSmoke

private abbrev Operation := ScalarOp ⊕ IndexOp
private abbrev Queries := CmpTst ⊕ IdxTst

private def rejecting : Interp Operation Queries Float where
  call _ _ _ _ _ _ := none
  test _ _ _ _ := none
  index _ _ _ := none

private def routines : List (Routine Operation Queries) :=
  [NLAlib.Cholesky.rightLooking, NLAlib.Cholesky.semidefiniteRightLooking,
    NLAlib.LDL.factor, NLAlib.Cholesky.pivotedRightLooking, NLAlib.Cholesky.rightLookingInPlace,
    NLAlib.Cholesky.semidefiniteRightLookingInPlace, NLAlib.Cholesky.pivotedRightLookingInPlace]

private def check (i scenario : ℕ) : Bool := Id.run do
  let some routine := routines[i]? | return false
  let buffers : Store Float := if scenario < 2 then [] else if scenario == 2 then
    [[none], [], [some 17]] else [[some 3], [some 5]]
  let args := if scenario == 0 then [] else if scenario == 1 then [(0, 0), (0, 0), (0, 0)]
    else if scenario == 2 then [(999, 1000), (1, 900), (999, 0)] else [(0, 0), (0, 0), (0, 0)]
  let initial : Mem Float := ⟨buffers, 37⟩
  let some final := NLAlib.Ops.eval rejecting (fun _ _ => 0) routine.body
    (Env.frame [0] args) initial | return false
  return final.store == initial.store && final.pos == initial.pos

private def positiveFails (i : ℕ) : Bool := Id.run do
  let some routine := routines[i]? | return false
  let args := if i < 2 then [(0, 0), (1, 0)] else if i < 4 then [(0, 0), (1, 0), (2, 0)]
    else if i < 6 then [(0, 0), (0, 0)] else [(0, 0), (0, 0), (2, 0)]
  let initial : Mem Float := ⟨[[some 9], [none], [none]], 37⟩
  return (NLAlib.Ops.eval rejecting (fun _ _ => 0) routine.body (Env.frame [1] args) initial).isNone

#guard check 0 0
#guard check 0 1
#guard check 0 2
#guard check 0 3
#guard positiveFails 0
#guard check 1 0
#guard check 1 1
#guard check 1 2
#guard check 1 3
#guard positiveFails 1
#guard check 2 0
#guard check 2 1
#guard check 2 2
#guard check 2 3
#guard positiveFails 2
#guard check 3 0
#guard check 3 1
#guard check 3 2
#guard check 3 3
#guard positiveFails 3
#guard check 4 0
#guard check 4 1
#guard check 4 2
#guard check 4 3
#guard positiveFails 4
#guard check 5 0
#guard check 5 1
#guard check 5 2
#guard check 5 3
#guard positiveFails 5
#guard check 6 0
#guard check 6 1
#guard check 6 2
#guard check 6 3
#guard positiveFails 6

end NLAlibTools.DenseFactorizationEmptyOpsSmoke
