/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.Partial
import NLAlib.Matrix.Factorizations.LU.Threshold
import NLAlib.Ops.Tools.Machines

/-!
# Actual scalar partial and threshold LU regressions

These finite Float tests replay the actual row log independently and multiply the stored
partial and threshold factors. Threshold cases distinguish diagonal acceptance from partial
pivoting and include equality acceptance and stable fallback ties. They check singular and
zero pivot columns, initialized output words,
triangles, unit diagonal, offsets, source preservation, scope and sentinels. A backend that
rejects every division checks zero-pivot paths on nonzero strictly upper triangular inputs.
The tests assert no universal native Float rounding or range model.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.LUPartialOpsSmoke

private def interpreter (rejectDiv : Bool) : Interp (ScalarOp ⊕ IndexOp) Qry Float :=
  withQueries fun op => match op with
    | .inl o => if rejectDiv && o == .div then
        { floatMachine.fn o with fn := fun _ _ _ => none }
      else floatMachine.fn o
    | .inr .lit => floatMachine.indexFn

private def replay (n : ℕ) (history : List Float) : Option (List ℕ) := Id.run do
  let mut order := List.range n
  for k in List.range n do
    let word := history.getD k (-1)
    let chosen := word.toUInt64.toNat
    if word != Float.ofNat chosen || chosen < k || n ≤ chosen then return none
    let old := order
    order := (List.range n).map fun i =>
      old.getD (if i == k then chosen else if i == chosen then k else i) 0
  return some order

private def product (n : ℕ) (l u : List Float) (i j : ℕ) : Float :=
  ((List.range n).map fun k => l.getD (k * n + i) 0 * u.getD (j * n + k) 0).sum

private def check (n : ℕ) (a : List Float) (expected : List ℕ)
    (rejectDiv : Bool := false) (threshold : Option ℚ := none) : Bool := Id.run do
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry :=
    threshold.elim NLAlib.LU.factorPartial NLAlib.LU.factorThreshold
  let source := vals ([211] ++ a ++ [223])
  let lower := vals [227, 229] ++ blank (n * n) ++ vals [233]
  let upper := vals [239] ++ blank (n * n) ++ vals [241]
  let history := vals [251, 257, 263] ++ blank n ++ vals [269]
  let initial : Mem Float := ⟨[source, lower, upper, history], 17⟩
  let some final := NLAlib.Ops.eval (interpreter rejectDiv) (fun _ _ => 0) routine.body
    (Env.frame [n] [(0, 1), (1, 2), (2, 1), (3, 3)]) initial | return false
  let some l := final.store.readBlock 1 2 (n * n) | return false
  let some u := final.store.readBlock 2 1 (n * n) | return false
  let some h := final.store.readBlock 3 3 n | return false
  let some order := replay n h | return false
  return final.pos == 17 && final.store.length == 4 && final.store[0]? == some source &&
    final.store.shape == initial.store.shape && final.store.get 1 0 == some 227 &&
    final.store.get 1 1 == some 229 && final.store.get 1 (2 + n * n) == some 233 &&
    final.store.get 2 0 == some 239 && final.store.get 2 (1 + n * n) == some 241 &&
    final.store.get 3 0 == some 251 && final.store.get 3 1 == some 257 &&
    final.store.get 3 2 == some 263 && final.store.get 3 (3 + n) == some 269 &&
    h == expected.map Float.ofNat && (List.range n).all fun i =>
      l.getD (i * n + i) 0 == 1 && (List.range n).all fun j =>
        (a.getD (j * n + order.getD i 0) 0 - product n l u i j).abs ≤ 1e-10 &&
          (if i < j then l.getD (j * n + i) 0 == 0 else true) &&
          (if j < i then u.getD (j * n + i) 0 == 0 else true) &&
          (l.getD (j * n + i) 0).abs ≤
            (threshold.map (fun q => 1 / ratToFloat q)).getD 1 + 1e-12

private def emptyInvalid (threshold : Option ℚ := none) : Bool :=
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry :=
    threshold.elim NLAlib.LU.factorPartial NLAlib.LU.factorThreshold
  let initial : Mem Float := ⟨[], 17⟩
  match NLAlib.Ops.eval (interpreter true) (fun _ _ => 0) routine.body
      (Env.frame [0] [(11, 0), (13, 0), (17, 0), (19, 0)]) initial with
  | some final => final.store.isEmpty && final.pos == 17
  | none => false

#guard check 0 [] []
#guard emptyInvalid
#guard check 1 [3] [0]
#guard check 1 [-3] [0]
#guard check 1 [0] [0] true
#guard check 2 [0, 0, 0, 0] [0, 1] true
#guard check 2 [2, -2, 1, 3] [0, 1]
#guard check 2 [1, 9, -9, 2] [1, 1]
#guard check 2 [0, 0, 1, 2] [0, 1]
#guard check 3 [1, 4, 7, 2, 5, 8, 3, 6, 9] [2, 2, 2]
#guard check 3 [1, 2, 3, 2, 4, 6, 3, 6, 9] [2, 1, 2]
#guard check 3 [0, 0, 0, 1, 0, 0, 0, 1, 0] [0, 1, 2] true

#guard check 0 [] [] false (some (1 / 2))
#guard emptyInvalid (some (1 / 2))
#guard check 1 [0] [0] true (some (1 / 2))
#guard check 2 [0, 0, 0, 0] [0, 1] true (some (1 / 2))
#guard check 2 [1, 2, 0, 3] [0, 1] false (some (1 / 2))
#guard check 2 [0.9, 2, 1, 3] [1, 1] false (some (1 / 2))
#guard check 2 [-1, 2, 0, 3] [0, 1] false (some (1 / 2))
#guard check 2 [1, 2, 0, 3] [1, 1] false (some 1)
#guard check 3 [0, 2, -2, 1, 3, 4, 2, 5, 6] [1, 2, 2] false (some (1 / 2))

end NLAlibTools.LUPartialOpsSmoke
