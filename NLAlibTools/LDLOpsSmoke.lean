/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LDL.Routine
import NLAlib.Ops.Tools.Machines

/-!
# Actual scalar Ops LDL regressions

These diagnostic Float tests execute LU materialization and the final scalar diagonal copy.
Independent diagonal-weighted Gram reconstruction checks positive and indefinite inputs with
nonzero canonical pivots. Frames, initialized outputs, unit diagonal and scoped scratch are
also checked. The finite tests make no universal Float accuracy assertion.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.LDLOpsSmoke

private def interpreter : Interp ScalarOp Qry Float := withQueries floatMachine.fn

private def gram (n : ℕ) (l d : List Float) (i j : ℕ) : Float :=
  ((List.range n).map fun k =>
    l.getD (k * n + i) 0 * d.getD k 0 * l.getD (k * n + j) 0).sum

private def check (n : ℕ) (a : List Float) : Bool := Id.run do
  let routine : Routine ScalarOp Qry := NLAlib.LDL.factor
  let source := vals ([211] ++ a ++ [223])
  let lower := [some 227, some 229] ++ blank (n * n) ++ [some 233]
  let diagonal := [some 239] ++ blank n ++ [some 241]
  let initial : Mem Float := ⟨[source, lower, diagonal], 17⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n] [(0, 1), (1, 2), (2, 1)]) initial | return false
  let some l := final.store.readBlock 1 2 (n * n) | return false
  let some d := final.store.readBlock 2 1 n | return false
  return final.pos == 17 && final.store.length == 3 && final.store[0]? == some source &&
    final.store.len 1 == lower.length && final.store.len 2 == diagonal.length &&
    final.store.get 1 0 == some 227 && final.store.get 1 1 == some 229 &&
    final.store.get 1 (2 + n * n) == some 233 && final.store.get 2 0 == some 239 &&
    final.store.get 2 (1 + n) == some 241 && l.length == n * n && d.length == n &&
    (List.range n).all fun i => l.getD (i * n + i) 0 == 1 &&
      (List.range n).all fun j =>
        (a.getD (j * n + i) 0 - gram n l d i j).abs ≤ 1e-10 &&
          (if i < j then l.getD (j * n + i) 0 == 0 else true)

#guard check 0 []
#guard check 1 [9]
#guard check 1 [-3]
#guard check 2 [4, 2, 2, 5]
#guard check 2 [2, 1, 1, -1]
#guard check 3 [2, 2, -1, 2, -1, -7, -1, -7, -7.5]

end NLAlibTools.LDLOpsSmoke
