/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.Complete
import NLAlib.Ops.Tools.Machines

/-!
# Actual complete-pivot LU regressions

Both actual current-position logs are replayed independently before comparing the permuted
source with the reported lower-upper product. Checks cover triangle/unit-diagonal shape,
unit multiplier bounds, singular inputs, offsets, source/output overlaps, initialized output,
all off-output cells, tape and scratch restoration. Float diagnostics do not assert an
arithmetic model for every execution.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.CompleteLUOpsSmoke

private abbrev Operation := ScalarOp ⊕ IndexOp

private def interpreter : Interp Operation Qry Float :=
  withQueries (fun op => op.elim floatMachine.fn (fun _ => floatMachine.indexFn))

private def replay (n : ℕ) (hs : List Float) : List ℕ :=
  (List.range n).foldl (fun order k =>
    let r := (hs.getD k 0).toUInt64.toNat
    order.mapIdx fun i a => if i == k then order.getD r n
      else if i == r then order.getD k n else a) (List.range n)

private def check (n : ℕ) (a : List Float) (mode : ℕ) : Bool := Id.run do
  let buffers := [vals ([347, 349] ++ a ++ [353]),
    [some 359] ++ blank (n * n) ++ [some 367],
    [some 373] ++ blank (n * n) ++ [some 379],
    [some 383] ++ blank n ++ [some 389], [some 397] ++ blank n ++ [some 401]]
  let L := if mode == 1 then (0, 2) else (1, 1)
  let U := if mode == 2 then (0, 2) else (2, 1)
  let H := if mode == 3 then (0, 2) else (3, 1)
  let Q := if mode == 4 then (0, 2) else (4, 1)
  let initial : Mem Float := ⟨buffers, 29⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0)
      (NLAlib.LU.factorComplete : Routine Operation Qry).body
      (Env.frame [n] [(0, 2), L, U, H, Q]) initial | return false
  let some ls := final.store.readBlock L.1 L.2 (n * n) | return false
  let some us := final.store.readBlock U.1 U.2 (n * n) | return false
  let some hs := final.store.readBlock H.1 H.2 n | return false
  let some qs := final.store.readBlock Q.1 Q.2 n | return false
  let rows := replay n hs
  let cols := replay n qs
  let logs := (List.range n).all fun k =>
    [hs.getD k 0, qs.getD k 0].all fun w =>
      let r := w.toUInt64.toNat
      k ≤ r && r < n && w == Float.ofNat r
  let factors := (List.range n).all fun i => (List.range n).all fun j =>
    let product := ((List.range n).map fun k =>
      ls.getD (k * n + i) 0 * us.getD (j * n + k) 0).sum
    let source := a.getD (cols.getD j n * n + rows.getD i n) 0
    (source - product).abs ≤ 1e-9 * (1 + source.abs) &&
      (ls.getD (j * n + i) 0).abs ≤ 1 + 1e-12 &&
      (if i < j then ls.getD (j * n + i) 0 == 0 else true) &&
      (if j < i then us.getD (j * n + i) 0 == 0 else true) &&
      (if i == j then ls.getD (j * n + i) 0 == 1 else true)
  let shape := final.store.length == buffers.length && (List.range buffers.length).all
    fun b => final.store.len b == (buffers.getD b []).length
  let frame := (List.range buffers.length).all fun b =>
    (List.range (buffers.getD b []).length).all fun i =>
      if [(L, n * n), (U, n * n), (H, n), (Q, n)].any
        (fun z => b == z.1.1 && z.1.2 ≤ i && i < z.1.2 + z.2) then true
      else final.store.get b i == (buffers.getD b []).getD i none
  return logs && factors && shape && frame && final.pos == 29

private def allModes (n : ℕ) (a : List Float) : Bool :=
  (List.range 5).all fun mode => check n a mode

private def checkRecorded (n : ℕ) (a hs qs : List Float)
    (upperCells : List (ℕ × Float)) : Bool := Id.run do
  let initial : Mem Float := ⟨[vals a, blank (n * n), blank (n * n), blank n, blank n], 31⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0)
      (NLAlib.LU.factorComplete : Routine Operation Qry).body
      (Env.frame [n] [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]) initial | return false
  return final.store.readBlock 3 0 n == some hs && final.store.readBlock 4 0 n == some qs &&
    upperCells.all fun z => final.store.get 2 z.1 == some z.2

#guard allModes 0 []
#guard allModes 1 [0]
#guard allModes 1 [-9]
#guard allModes 2 [1, 2, -8, 3]
#guard allModes 2 [1, 2, -8, 8]
#guard allModes 2 [0, 2, 0, 4]
#guard allModes 3 (List.replicate 9 0)
#guard allModes 3 [1, 2, 3, 2, 4, 6, 3, 6, 9]
#guard allModes 3 [1, 4, 2, 2, 0, 9, 8, 3, 0]
#guard allModes 3 [0, 0, 4, 0, 8, 0, -9, 0, 0]
#guard allModes 4 [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]

#guard allModes 3 [0, 3, 5, 1, 4, 6, 2, 12, 7]
#guard allModes 4 [1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 4, 8, 12, 32]
#guard checkRecorded 3 [0, 3, 5, 1, 4, 6, 2, 12, 7] [1, 2, 2] [2, 1, 2] []
#guard checkRecorded 4 [1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 4, 8, 12, 32]
  [3, 2, 3, 3] [3, 2, 3, 3] [(0, 32), (4, 15), (8, 13), (12, 14), (9, 4.125), (13, 4.75)]

end NLAlibTools.CompleteLUOpsSmoke
