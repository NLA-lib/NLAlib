/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.RookChoice
import NLAlib.Ops.Tools.Machines

/-!
# Actual bounded rook-selector regressions

The stored pair is checked independently against both active row and column maxima. A tied
earlier column with a larger entry elsewhere detects an invalid tie move without a new
column scan. Triangular chains require every available continuation, checking the finite cap.
Offsets, source retention, same-buffer disjoint regions, tape and scoped scratch are checked.
These finite Float diagnostics assert no universal Float error model.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.RookPivotOpsSmoke

private abbrev Operation := ScalarOp ⊕ IndexOp

private def interpreter : Interp Operation Qry Float :=
  withQueries (fun op => op.elim floatMachine.fn (fun _ => floatMachine.indexFn))

private def check (n k : ℕ) (rs : List Float) (same : Bool)
    (expected : Option (ℕ × ℕ) := none) : Bool := Id.run do
  let source := vals ([409, 419] ++ rs ++ [421])
  let output := [some 431] ++ blank 2 ++ [some 433]
  let buffers := if same then [source ++ output] else [source, output]
  let p := if same then (0, source.length + 1) else (1, 1)
  let initial : Mem Float := ⟨buffers, 37⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0)
      (NLAlib.LU.rookChoice : Routine Operation Qry).body
      (Env.frame [n, k] [(0, 2), p]) initial | return false
  let some pair := final.store.readBlock p.1 p.2 2 | return false
  let r := (pair.getD 0 0).toUInt64.toNat
  let c := (pair.getD 1 0).toUInt64.toNat
  let score := (rs.getD (c * n + r) 0).abs
  let indices := pair == [Float.ofNat r, Float.ofNat c] && k ≤ r && r < n && k ≤ c && c < n
  let maxima := (List.range (n - k)).all fun t =>
    (rs.getD (c * n + (k + t)) 0).abs ≤ score &&
      (rs.getD ((k + t) * n + r) 0).abs ≤ score &&
      (if k + t < r then (rs.getD (c * n + (k + t)) 0).abs < score else true)
  let expectedPair := match expected with | some q => r == q.1 && c == q.2 | none => true
  let shape := final.store.length == buffers.length && (List.range buffers.length).all
    fun b => final.store.len b == (buffers.getD b []).length
  let frame := (List.range buffers.length).all fun b =>
    (List.range (buffers.getD b []).length).all fun i =>
      if b == p.1 && p.2 ≤ i && i < p.2 + 2 then true
      else final.store.get b i == (buffers.getD b []).getD i none
  return indices && maxima && expectedPair && shape && frame && final.pos == 37

private def sweep (n seed : ℕ) : Bool :=
  let rs := (List.range (n * n)).map fun t =>
    (Float.ofNat ((13 * t + seed * 17) % 19) - 9) / 2
  (List.range n).all fun k => check n k rs false && check n k rs true

#guard check 1 0 [0] false (some (0, 0))
#guard check 1 0 [-9] true (some (0, 0))
#guard check 2 0 [1, 2, -8, 3] false
#guard check 2 0 [1, 2, -8, 8] true
#guard check 2 1 [100, 200, 300, -4] false (some (1, 1))
#guard check 3 0 (List.replicate 9 0) false (some (0, 0))
#guard check 3 1 (List.replicate 9 0) true (some (1, 1))
#guard check 3 0 [1, 2, 0, 9, 3, 5, 0, 4, 5] false (some (2, 2))
#guard check 3 0 [1, 2, 0, 9, 3, 5, 0, 4, 5] true (some (2, 2))
#guard check 3 0 [1, 0, 0, 2, 3, 0, 0, 4, 5] false (some (2, 2))
#guard check 4 0 [1, 0, 0, 0, 2, 3, 0, 0, 0, 4, 5, 0, 0, 0, 6, 7]
  true (some (3, 3))
#guard sweep 1 0
#guard sweep 2 1
#guard sweep 3 2
#guard sweep 4 3
#guard sweep 5 4
#guard sweep 6 5

end NLAlibTools.RookPivotOpsSmoke
