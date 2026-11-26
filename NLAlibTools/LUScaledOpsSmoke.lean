/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.RowScales
import NLAlib.Matrix.Factorizations.LU.ScaledScan
import NLAlib.Matrix.Factorizations.LU.ScaledAlg
import NLAlib.Ops.Tools.Machines

/-!
# Actual fixed-scale initialization and selection regressions

These finite Float executions check rectangular row maxima, shared-arena windows, stable
ratio ties and zero-scale branches. Rejected multiplication and division instrumentation
checks the intended zero-scale paths. They assert no universal native arithmetic model.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.LUScaledOpsSmoke

private def interpreter (rejectMul : Bool) : Interp (ScalarOp ⊕ IndexOp) Qry Float :=
  withQueries fun op => match op with
    | .inl o => if o == .div || (rejectMul && o == .mul) then
        {floatMachine.fn o with fn := fun _ _ _ => none}
      else floatMachine.fn o
    | .inr .lit => floatMachine.indexFn

private def scales (m n : ℕ) (a expected : List Float) : Bool := Id.run do
  let cells := vals ([11] ++ a ++ [13, 17]) ++ blank m ++ vals [19]
  let initial : Mem Float := ⟨[cells], 23⟩
  let some final := NLAlib.Ops.eval (interpreter true) (fun _ _ => 0)
    (NLAlib.LU.rowScales (Op := ScalarOp ⊕ IndexOp) (Tst := Qry)).body
    (Env.frame [m, n] [(0, 1), (0, 3 + m * n)]) initial | return false
  return final.store.readBlock 0 1 (m * n) == some a &&
    final.store.readBlock 0 (3 + m * n) m == some expected &&
    final.store.get 0 0 == some 11 && final.store.get 0 (1 + m * n) == some 13 &&
    final.store.get 0 (2 + m * n) == some 17 &&
    final.store.get 0 (3 + m * n + m) == some 19 &&
    final.store.shape == initial.store.shape && final.store.length == 1 && final.pos == 23

private def emptyScales : Bool :=
  let initial : Mem Float := ⟨[], 23⟩
  match NLAlib.Ops.eval (interpreter true) (fun _ _ => 0)
      (NLAlib.LU.rowScales (Op := ScalarOp ⊕ IndexOp) (Tst := Qry)).body
      (Env.frame [0, 3] [(11, 0), (13, 0)]) initial with
  | some final => final.store.isEmpty && final.pos == 23
  | none => false

private def emptyColumns : Bool :=
  let initial : Mem Float := ⟨[blank 2], 23⟩
  match NLAlib.Ops.eval (interpreter true) (fun _ _ => 0)
      (NLAlib.LU.rowScales (Op := ScalarOp ⊕ IndexOp) (Tst := Qry)).body
      (Env.frame [2, 0] [(11, 0), (0, 0)]) initial with
  | some final => final.store.readBlock 0 0 2 == some [0, 0] &&
      final.store.length == 1 && final.pos == 23
  | none => false

private def select (xs ss : List Float) (expected : ℕ) (rejectMul : Bool := false) : Bool :=
  Id.run do
    let n := xs.length
    let source := vals ([29] ++ xs ++ [31] ++ ss ++ [37])
    let initial : Mem Float := ⟨[source, vals [41] ++ blank 1 ++ vals [43]], 47⟩
    let some final := NLAlib.Ops.eval (interpreter rejectMul) (fun _ _ => 0)
      (NLAlib.LU.argmaxScaledAbs (Op := ScalarOp ⊕ IndexOp) (Tst := Qry)).body
      (Env.frame [n] [(0, 1), (0, n + 2), (1, 1)]) initial | return false
    return final.store.get 1 1 == some (Float.ofNat expected) &&
      final.store[0]? == some source && final.store.get 1 0 == some 41 &&
      final.store.get 1 2 == some 43 && final.store.shape == initial.store.shape &&
      final.store.length == 2 && final.pos == 47

#guard scales 0 0 [] []
#guard scales 2 0 [] [0, 0]
#guard scales 0 3 [] []
#guard emptyScales
#guard emptyColumns
#guard scales 2 3 [1, -4, -5, 2, 3, -6] [5, 6]
#guard scales 3 2 [-1, 0, 3, 2, 0, -4] [2, 0, 4]
#guard scales 1 1 [-3] [3]
#guard select [100, 2] [10000, 2] 1
#guard select [1, 2] [2, 4] 0
#guard select [0, 1] [0, 2] 1 true
#guard select [0, 0] [0, 1] 0 true
#guard select [0, 0, 0] [0, 0, 0] 0 true
#guard select [-3] [3] 0 true
#guard select [1, -2, 3] [1, 2, 3] 0
#guard select [1, 2, -9] [10, 2, 3] 2


private def factorInterpreter (rejectMulDiv : Bool := false) :
    Interp (ScalarOp ⊕ IndexOp) Qry Float :=
  withQueries fun op => match op with
    | .inl o => if rejectMulDiv && (o == .div || o == .mul) then
        {floatMachine.fn o with fn := fun _ _ _ => none} else floatMachine.fn o
    | .inr .lit => floatMachine.indexFn

private def replay (n : ℕ) (hs : List Float) : List ℕ :=
  (List.range n).foldl (fun order k =>
    let r := (hs.getD k 0).toUInt64.toNat
    order.mapIdx fun i a => if i == k then order.getD r n
      else if i == r then order.getD k n else a) (List.range n)

private def factorWords (n : ℕ) (a ls us hs : List Float) : Bool :=
  let rows := replay n hs
  let logs := (List.range n).all fun k =>
    let r := (hs.getD k 0).toUInt64.toNat
    k ≤ r && r < n && hs.getD k 0 == Float.ofNat r
  logs && (List.range n).all fun i => (List.range n).all fun j =>
    let product := ((List.range n).map fun k =>
      ls.getD (k * n + i) 0 * us.getD (j * n + k) 0).sum
    let source := a.getD (j * n + rows.getD i n) 0
    (source - product).abs ≤ 1e-8 * (1 + source.abs) &&
      (if i < j then ls.getD (j * n + i) 0 == 0 else true) &&
      (if j < i then us.getD (j * n + i) 0 == 0 else true) &&
      (if i == j then ls.getD (j * n + i) 0 == 1 else true)

private def factorCase (n : ℕ) (a : List Float) (mode : ℕ)
    (rejectMulDiv : Bool := false) : Bool := Id.run do
  let buffers := [vals ([503, 509] ++ a ++ [521]),
    [some 523] ++ blank (n * n) ++ [some 541],
    [some 547] ++ blank (n * n) ++ [some 557], [some 563] ++ blank n ++ [some 569]]
  let L := if mode == 1 then (0, 2) else (1, 1)
  let U := if mode == 2 then (0, 2) else (2, 1)
  let H := if mode == 3 then (0, 2) else (3, 1)
  let initial : Mem Float := ⟨buffers, 59⟩
  let some final := NLAlib.Ops.eval (factorInterpreter rejectMulDiv) (fun _ _ => 0)
      (NLAlib.LU.factorScaled : Routine (ScalarOp ⊕ IndexOp) Qry).body
      (Env.frame [n] [(0, 2), L, U, H]) initial | return false
  let some ls := final.store.readBlock L.1 L.2 (n * n) | return false
  let some us := final.store.readBlock U.1 U.2 (n * n) | return false
  let some hs := final.store.readBlock H.1 H.2 n | return false
  let shape := final.store.length == buffers.length && (List.range buffers.length).all
    fun b => final.store.len b == (buffers.getD b []).length
  let frame := (List.range buffers.length).all fun b =>
    (List.range (buffers.getD b []).length).all fun i =>
      if [(L, n * n), (U, n * n), (H, n)].any
        (fun z => b == z.1.1 && z.1.2 ≤ i && i < z.1.2 + z.2) then true
      else final.store.get b i == (buffers.getD b []).getD i none
  return factorWords n a ls us hs && shape && frame && final.pos == 59

private def allModes (n : ℕ) (a : List Float) : Bool :=
  (List.range 4).all fun mode => factorCase n a mode

private def originalScales (n : ℕ) (a : List Float) : List Float :=
  (List.range n).map fun i => (List.range n).foldl (fun best j =>
    let value := (a.getD (j * n + i) 0).abs
    if best < value then value else best) 0

private def cachedScales (n : ℕ) (a : List Float) : Bool := Id.run do
  let ss := originalScales n a
  let buffers := [vals ([571] ++ a ++ ss ++ [577]),
    vals ([587] ++ List.replicate (n * n) 0 ++ [593]),
    vals ([599] ++ List.replicate (n * n) 0 ++ [601]),
    [some 607] ++ blank n ++ [some 613], [some 617, none, some 619]]
  let initial : Mem Float := ⟨buffers, 61⟩
  let some final := NLAlib.Ops.eval (factorInterpreter false) (fun _ _ => 0)
      (NLAlib.LU.scaledLoop : Routine (ScalarOp ⊕ IndexOp) Qry).body
      (Env.frame [n] [(0, 1), (1, 1), (2, 1), (0, 1), (1, 1), (2, 1), (3, 1), (4, 1)])
      initial | return false
  let some ls := final.store.readBlock 1 1 (n * n) | return false
  let some us := final.store.readBlock 2 1 (n * n) | return false
  let some hs := final.store.readBlock 3 1 n | return false
  let some actualScales := final.store.readBlock 0 (1 + n * n) n | return false
  let expectedScales := (replay n hs).map fun i => ss.getD i 0
  let shape := final.store.length == buffers.length && (List.range buffers.length).all
    fun b => final.store.len b == (buffers.getD b []).length
  let sentinels := (List.range buffers.length).all fun b =>
    final.store.get b 0 == (buffers.getD b []).getD 0 none &&
      final.store.get b ((buffers.getD b []).length - 1) == (buffers.getD b []).getLast!
  return actualScales == expectedScales && factorWords n a ls us hs && shape && sentinels &&
    final.pos == 61

private def reported (n : ℕ) (a : List Float) : Option (List Float × List Float) := do
  let initial : Mem Float := ⟨[vals a, blank (n * n), blank (n * n), blank n], 0⟩
  let final ← NLAlib.Ops.eval (factorInterpreter false) (fun _ _ => 0)
    (NLAlib.LU.factorScaled : Routine (ScalarOp ⊕ IndexOp) Qry).body
    (Env.frame [n] [(0, 0), (1, 0), (2, 0), (3, 0)]) initial
  let ls ← final.store.readBlock 1 0 (n * n)
  let hs ← final.store.readBlock 3 0 n
  return (ls, hs)

private def emptyFactor (args : List (ℕ × ℕ)) : Bool :=
  let reject : Interp (ScalarOp ⊕ IndexOp) Qry Float :=
    ⟨fun _ _ _ _ _ _ => none, fun _ _ _ _ => none, fun _ _ _ => none⟩
  match NLAlib.Ops.eval reject (fun _ _ => 0)
      (NLAlib.LU.factorScaled : Routine (ScalarOp ⊕ IndexOp) Qry).body
      (Env.frame [0] args) (⟨[], 67⟩ : Mem Float) with
  | some final => final.store == [] && final.pos == 67
  | none => false

#guard allModes 0 []
#guard allModes 1 [0]
#guard allModes 1 [-3]
#guard allModes 2 [1, 0, 0, 1]
#guard allModes 2 [0, 1, 0, 2]
#guard allModes 2 [100, 1, 1000, 2]
#guard allModes 3 (List.replicate 9 0)
#guard allModes 3 [1, 2, 3, 2, 4, 6, 3, 6, 9]
#guard allModes 3 [1, 4, 2, 2, 0, 9, 8, 3, 0]
#guard allModes 3 [1, 1000, 0, 1, 1001, 2, 1, 1000, 10]
#guard allModes 4 [1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 4, 8, 12, 32]
#guard cachedScales 0 []
#guard cachedScales 2 [0, 1, 0, 2]
#guard cachedScales 2 [100, 1, 1000, 2]
#guard cachedScales 3 [1, 1000, 0, 1, 1001, 2, 1, 1000, 10]
#guard cachedScales 3 [1, 4, 2, 2, 0, 9, 8, 3, 0]
#guard cachedScales 4 [1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 4, 8, 12, 32]
#guard (reported 2 [100, 1, 1000, 2]).map
  (fun z => z.1 == [1, 100, 0, 1] && z.2 == [1, 1]) == some true
#guard (reported 3 [1, 1000, 0, 1, 1001, 2, 1, 1000, 10]).map
  (fun z => z.2 == [0, 2, 2]) == some true
#guard factorCase 2 (List.replicate 4 0) 0 true
#guard !(factorCase 2 [1, 0, 0, 1] 0 true)
#guard emptyFactor []
#guard emptyFactor [(0, 0), (0, 0), (0, 0), (0, 0)]
#guard emptyFactor [(999, 100), (999, 100), (999, 100), (999, 100)]

end NLAlibTools.LUScaledOpsSmoke
