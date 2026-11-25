/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.Cholesky.InPlace
import NLAlib.Ops.Tools.Machines

/-!
# Actual scalar Ops Cholesky regressions

The tests execute the complete scalar trees with the diagnostic Float backend. Independent
Gram reconstruction checks the factors; shape, source, sentinels, tape position and scoped
scratch are also checked. These finite tests make no universal Float accuracy claim.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.CholeskyOpsSmoke

private def interpreter : Interp ScalarOp Qry Float := withQueries floatMachine.fn

private def near (x y : Float) : Bool := (x - y).abs ≤ 1e-10

private def gram (n : ℕ) (l : List Float) (i j : ℕ) : Float :=
  ((List.range n).map fun k => l.getD (k * n + i) 0 * l.getD (k * n + j) 0).sum

private def checkFactor (n : ℕ) (a l : List Float) (strict : Bool) : Bool :=
  l.length == n * n && (List.range n).all fun i =>
    (if strict then 0 < l.getD (i * n + i) 0 else 0 ≤ l.getD (i * n + i) 0) &&
      (List.range n).all fun j =>
        near (a.getD (j * n + i) 0) (gram n l i j) &&
          (if i < j then l.getD (j * n + i) 0 == 0 else true)

private def separateCase (n : ℕ) (a : List Float) (psd : Bool) : Bool := Id.run do
  let routine : Routine ScalarOp Qry := if psd then NLAlib.Cholesky.semidefiniteRightLooking
    else NLAlib.Cholesky.rightLooking
  let source := vals ([137] ++ a ++ [149])
  let output := [some 157, some 163] ++ blank (n * n) ++ [some 167]
  let initial : Mem Float := ⟨[source, output], 7⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n] [(0, 1), (1, 2)]) initial | return false
  let some l := final.store.readBlock 1 2 (n * n) | return false
  return final.pos == 7 && final.store.length == 2 && final.store[0]? == some source &&
    final.store.len 1 == output.length && final.store.get 1 0 == some 157 &&
    final.store.get 1 1 == some 163 && final.store.get 1 (2 + n * n) == some 167 &&
    checkFactor n a l (!psd)

private def inPlaceCase (n : ℕ) (a : List Float) (psd : Bool) : Bool := Id.run do
  let routine : Routine ScalarOp Qry := if psd then
    NLAlib.Cholesky.semidefiniteRightLookingInPlace else NLAlib.Cholesky.rightLookingInPlace
  let input := vals ([173] ++ a ++ [179])
  let initial : Mem Float := ⟨[input], 11⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n] [(0, 1), (0, 1)]) initial | return false
  let some l := final.store.readBlock 0 1 (n * n) | return false
  return final.pos == 11 && final.store.length == 1 && final.store.len 0 == input.length &&
    final.store.get 0 0 == some 173 && final.store.get 0 (1 + n * n) == some 179 &&
    checkFactor n a l (!psd)

private def denseThree : List Float := [9, 3, 1.5, 3, 5, 2.5, 1.5, 2.5, 2.25]

#guard separateCase 0 [] false
#guard separateCase 0 [] true
#guard inPlaceCase 0 [] false
#guard inPlaceCase 0 [] true
#guard separateCase 1 [9] false
#guard separateCase 1 [0] true
#guard inPlaceCase 1 [9] false
#guard inPlaceCase 1 [0] true
#guard separateCase 2 [4, 2, 2, 5] false
#guard inPlaceCase 2 [4, 2, 2, 5] false
#guard separateCase 3 denseThree false
#guard inPlaceCase 3 denseThree false
#guard separateCase 2 [0, 0, 0, 9] true
#guard inPlaceCase 2 [0, 0, 0, 9] true
#guard separateCase 2 [4, 2, 2, 1] true
#guard inPlaceCase 2 [4, 2, 2, 1] true
#guard separateCase 3 (List.replicate 9 0) true
#guard inPlaceCase 3 (List.replicate 9 0) true
#guard separateCase 3 [4, 2, 0, 2, 1, 0, 0, 0, 9] true
#guard inPlaceCase 3 [4, 2, 0, 2, 1, 0, 0, 0, 9] true

end NLAlibTools.CholeskyOpsSmoke
