/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.CompleteChoice
import NLAlib.Ops.Tools.Machines

/-!
# Actual complete-pivot selector regressions

Independent column-major replay checks the actual stored pair, including first ties, signs,
late columns, active suffixes, offsets and same-buffer nonoverlapping input/output regions.
Every source word, output sentinel, tape position and scoped allocation is checked. These
finite Float diagnostics assert no universal Float arithmetic model.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.CompletePivotOpsSmoke

private abbrev Operation := ScalarOp ⊕ IndexOp

private def interpreter : Interp Operation Qry Float :=
  withQueries (fun op => op.elim floatMachine.fn (fun _ => floatMachine.indexFn))

private def first (n k : ℕ) (rs : List Float) : ℕ :=
  ((List.range (n * n)).filter fun t => k ≤ t % n && k ≤ t / n).foldl
    (fun best t => if (rs.getD best 0).abs < (rs.getD t 0).abs then t else best) (k * n + k)

private def check (n k : ℕ) (rs : List Float) (same : Bool) : Bool := Id.run do
  let source := vals ([307, 311] ++ rs ++ [313])
  let output := [some 317] ++ blank 2 ++ [some 331]
  let buffers := if same then [source ++ output] else [source, output]
  let p := if same then (0, source.length + 1) else (1, 1)
  let initial : Mem Float := ⟨buffers, 23⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0)
      (NLAlib.LU.completeChoice : Routine Operation Qry).body
      (Env.frame [n, k] [(0, 2), p]) initial | return false
  let some pair := final.store.readBlock p.1 p.2 2 | return false
  let selected := first n k rs
  let expected := [Float.ofNat (selected % n), Float.ofNat (selected / n)]
  let shape := final.store.length == buffers.length && (List.range buffers.length).all
    fun b => final.store.len b == (buffers.getD b []).length
  let frame := (List.range buffers.length).all fun b =>
    (List.range (buffers.getD b []).length).all fun i =>
      if b == p.1 && p.2 ≤ i && i < p.2 + 2 then true
      else final.store.get b i == (buffers.getD b [])[i]?
  return pair == expected && shape && frame && final.pos == 23

private def sweep (n seed : ℕ) : Bool :=
  let rs := (List.range (n * n)).map fun t =>
    (Float.ofNat ((13 * t + seed * 17) % 19) - 9) / 2
  (List.range n).all fun k => check n k rs false && check n k rs true

#guard check 1 0 [0] false
#guard check 1 0 [-9] true
#guard check 2 0 [1, 2, -8, 3] false
#guard check 2 0 [1, 2, -8, 8] true
#guard check 2 1 [100, 200, 300, -4] false
#guard check 3 0 [0, -9, 9, 9, 0, 0, 0, 0, 9] false
#guard check 3 1 [99, 99, 99, 99, 2, 3, 99, -12, 4] true
#guard check 3 2 (List.replicate 9 0) false
#guard check 4 1 (List.replicate 16 0) true
#guard sweep 1 0
#guard sweep 2 1
#guard sweep 3 2
#guard sweep 4 3
#guard sweep 5 4
#guard sweep 6 5

end NLAlibTools.CompletePivotOpsSmoke
