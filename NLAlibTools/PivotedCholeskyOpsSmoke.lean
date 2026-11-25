/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.Cholesky.PivotedRoutine
import NLAlib.Ops.Tools.Machines

/-!
# Actual diagonal-pivoted PSD Cholesky regressions

The tests read the actual stored absolute log, independently replay its exchanges and
reconstruct the permuted source Gram matrix. A nontrivial three-cycle detects permutation
orientation and a late full-factor-row exchange. Singular cases, first ties, initialized
outputs, offsets, tape position and scratch cleanup are covered, including source/factor and
source/history overlap. These finite diagnostic Float tests assert no universal error model.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.PivotedCholeskyOpsSmoke

private abbrev Operation := ScalarOp ⊕ IndexOp

private def interpreter : Interp Operation Qry Float :=
  withQueries (fun op => op.elim floatMachine.fn (fun _ => floatMachine.indexFn))

private def replay (n : ℕ) (hs : List Float) : List ℕ :=
  (List.range n).foldl (fun order k =>
    let r := (hs.getD k 0).toUInt64.toNat
    order.mapIdx fun i a => if i == k then order.getD r n
      else if i == r then order.getD k n else a) (List.range n)

private def gram (n : ℕ) (l : List Float) (i j : ℕ) : Float :=
  ((List.range n).map fun k => l.getD (k * n + i) 0 * l.getD (k * n + j) 0).sum

private def factorCheck (n : ℕ) (a l hs : List Float) : Bool :=
  let order := replay n hs
  l.length == n * n && hs.length == n && (List.range n).all fun i =>
    let r := (hs.getD i 0).toUInt64.toNat
    i ≤ r && r < n && hs.getD i 0 == Float.ofNat r && 0 ≤ l.getD (i * n + i) 0 &&
      (List.range n).all fun j =>
        (a.getD (order.getD j n * n + order.getD i n) 0 - gram n l i j).abs ≤ 1e-10 &&
          (if i < j then l.getD (j * n + i) 0 == 0 else true)

private def check (n : ℕ) (a : List Float) (expected : List ℕ) (mode : ℕ) : Bool := Id.run do
  let source := vals ([251] ++ a ++ [257])
  let lower := [some 263, some 269] ++ blank (n * n) ++ [some 271]
  let history := [some 277] ++ blank n ++ [some 281]
  let buffers := if mode == 1 then [source, history]
    else if mode == 2 then [source, lower] else [source, lower, history]
  let statement : Stmt Operation Qry := if mode == 1 then
    NLAlib.Cholesky.pivotedRightLookingInPlace.body else NLAlib.Cholesky.pivotedRightLooking.body
  let environment := if mode == 1 then Env.frame [n] [(0, 1), (0, 1), (1, 1)]
    else if mode == 2 then Env.frame [n] [(0, 1), (1, 2), (0, 1)]
    else Env.frame [n] [(0, 1), (1, 2), (2, 1)]
  let lb := if mode == 1 then 0 else 1
  let lo := if mode == 1 then 1 else 2
  let hb := if mode == 1 then 1 else if mode == 2 then 0 else 2
  let initial : Mem Float := ⟨buffers, 19⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) statement environment initial
    | return false
  let some l := final.store.readBlock lb lo (n * n) | return false
  let some hs := final.store.readBlock hb 1 n | return false
  let shape := final.store.length == buffers.length && (List.range buffers.length).all
    fun b => final.store.len b == (buffers.getD b []).length
  let sourceFrame := if mode == 0 then final.store[0]? == some source else if mode == 1 then
    final.store.get 0 0 == some 251 && final.store.get 0 (1 + n * n) == some 257 else
      final.store.get 0 0 == some 251 && (List.range (source.length - (1 + n))).all
        fun i => final.store.get 0 (1 + n + i) == source[1 + n + i]?
  let lowerFrame := if mode == 1 then true else final.store.get 1 0 == some 263 &&
    final.store.get 1 1 == some 269 && final.store.get 1 (2 + n * n) == some 271
  let historyFrame := if mode == 2 then true else final.store.get hb 0 == some 277 &&
    final.store.get hb (1 + n) == some 281
  return shape && sourceFrame && lowerFrame && historyFrame && final.pos == 19 &&
    hs == expected.map Float.ofNat && factorCheck n a l hs

private def cycleMatrix : List Float := [2.25, 1.5, 2.5, 1.5, 9, 3, 2.5, 3, 5]

#guard check 0 [] [] 0
#guard check 0 [] [] 1
#guard check 0 [] [] 2
#guard check 1 [9] [0] 0
#guard check 1 [9] [0] 1
#guard check 1 [9] [0] 2
#guard check 1 [0] [0] 0
#guard check 1 [0] [0] 1
#guard check 1 [0] [0] 2
#guard check 2 [0, 0, 0, 9] [1, 1] 0
#guard check 2 [0, 0, 0, 9] [1, 1] 1
#guard check 2 [0, 0, 0, 9] [1, 1] 2
#guard check 3 cycleMatrix [1, 2, 2] 0
#guard check 3 cycleMatrix [1, 2, 2] 1
#guard check 3 cycleMatrix [1, 2, 2] 2
#guard check 3 [1, 0, 0, 0, 1, 0, 0, 0, 1] [0, 1, 2] 0
#guard check 3 [1, 0, 0, 0, 1, 0, 0, 0, 1] [0, 1, 2] 1
#guard check 3 [1, 0, 0, 0, 1, 0, 0, 0, 1] [0, 1, 2] 2
#guard check 3 (List.replicate 9 0) [0, 1, 2] 0
#guard check 3 (List.replicate 9 0) [0, 1, 2] 1
#guard check 3 (List.replicate 9 0) [0, 1, 2] 2
#guard check 3 [4, 2, 0, 2, 1, 0, 0, 0, 0] [0, 1, 2] 0
#guard check 3 [4, 2, 0, 2, 1, 0, 0, 0, 0] [0, 1, 2] 1
#guard check 3 [4, 2, 0, 2, 1, 0, 0, 0, 0] [0, 1, 2] 2

end NLAlibTools.PivotedCholeskyOpsSmoke
