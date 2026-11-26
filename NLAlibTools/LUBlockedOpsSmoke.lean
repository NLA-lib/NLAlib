/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.BlockedRoutine
import NLAlib.Ops.Tools.Machines
import NLAlib.Ops.Catalog.Index

/-!
# Actual clipped blocked LU regressions

These finite Float runs exercise the actual scalar panels, packed scalar GEMM corrections,
final clipped blocks, source/output overlap, offsets, sentinels and handle-free empty guard.
Reference multiplication checks the stored factors independently of the elimination steps.
The tests assert no universal native Float accuracy or finite-range model.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.LUBlockedOpsSmoke

private def interpreter (rejectAll : Bool := false) : Interp (ScalarOp ⊕ IndexOp) Qry Float :=
  withQueries fun op => match op with
    | .inl o => if rejectAll then { floatMachine.fn o with fn := fun _ _ _ => none }
      else floatMachine.fn o
    | .inr .lit => floatMachine.indexFn

private def product (n : ℕ) (l u : List Float) (i j : ℕ) : Float :=
  ((List.range n).map fun k => l.getD (k * n + i) 0 * u.getD (j * n + k) 0).sum

private def lower (n : ℕ) : List Float :=
  (List.range (n * n)).map fun t =>
    let i := t % n
    let j := t / n
    if i < j then 0 else if i == j then 1 else Float.ofNat (i - j)

private def upper (n : ℕ) : List Float :=
  (List.range (n * n)).map fun t =>
    let i := t % n
    let j := t / n
    if j < i then 0 else if i == j then Float.ofNat (2 ^ (i + 1)) else Float.ofNat (i + j + 1)

private def matrix (n : ℕ) : List Float :=
  (List.range (n * n)).map fun t => product n (lower n) (upper n) (t % n) (t / n)

private def check (n block : ℕ) : Bool := Id.run do
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry := NLAlib.LU.factorBlocked
  let a := matrix n
  let source := vals ([101] ++ a ++ [103])
  let lowerStore := vals [107, 109] ++ blank (n * n) ++ vals [113]
  let upperStore := vals [127] ++ blank (n * n) ++ vals [131]
  let initial : Mem Float := ⟨[source, lowerStore, upperStore], 17⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n, block, (n + block - 1) / block] [(0, 1), (1, 2), (2, 1)]) initial
    | return false
  let some l := final.store.readBlock 1 2 (n * n) | return false
  let some u := final.store.readBlock 2 1 (n * n) | return false
  return final.pos == 17 && final.store.length == 3 && final.store.shape == initial.store.shape &&
    final.store[0]? == some source && l == lower n && u == upper n &&
    final.store.get 1 0 == some 107 && final.store.get 1 1 == some 109 &&
    final.store.get 1 (2 + n * n) == some 113 && final.store.get 2 0 == some 127 &&
    final.store.get 2 (1 + n * n) == some 131 && (List.range n).all fun i =>
      (List.range n).all fun j => (a.getD (j * n + i) 0 - product n l u i j).abs ≤ 1e-10

private def overlap (n block : ℕ) (upperAlias : Bool) (shift : ℕ) : Bool := Id.run do
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry := NLAlib.LU.factorBlocked
  let a := matrix n
  let source := vals ([137] ++ a ++ List.replicate shift 139 ++ [149])
  let other := vals [151, 157] ++ blank (n * n) ++ vals [163]
  let initial : Mem Float := ⟨[source, other], 19⟩
  let l := if upperAlias then (1, 2) else (0, 1 + shift)
  let u := if upperAlias then (0, 1 + shift) else (1, 2)
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n, block, (n + block - 1) / block] [(0, 1), l, u]) initial | return false
  let some ls := final.store.readBlock l.1 l.2 (n * n) | return false
  let some us := final.store.readBlock u.1 u.2 (n * n) | return false
  return final.pos == 19 && final.store.shape == initial.store.shape &&
    final.store.length == 2 && ls == lower n && us == upper n &&
    final.store.get 0 0 == some 137 && final.store.get 0 (1 + n * n + shift) == some 149 &&
    final.store.get 1 0 == some 151 && final.store.get 1 1 == some 157 &&
    final.store.get 1 (2 + n * n) == some 163 &&
    (if shift == 0 then true else final.store.get 0 1 == some (a.headD 0))

private def emptyInvalid (args : List (ℕ × ℕ)) : Bool :=
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry := NLAlib.LU.factorBlocked
  let initial : Mem Float := ⟨[], 23⟩
  match NLAlib.Ops.eval (interpreter true) (fun _ _ => 0) routine.body
      (Env.frame [0, 3, 0] args) initial with
  | some final => final.store.isEmpty && final.pos == 23
  | none => false

#guard check 0 1
#guard check 1 1
#guard check 1 7
#guard check 3 1
#guard check 3 2
#guard check 3 3
#guard check 3 7
#guard check 5 1
#guard check 5 2
#guard check 5 3
#guard check 5 4
#guard check 5 5
#guard check 5 9
#guard overlap 3 1 false 0
#guard overlap 3 2 false 1
#guard overlap 3 2 true 0
#guard overlap 5 3 true 1
#guard emptyInvalid [(11, 91), (13, 17), (19, 42)]
#guard emptyInvalid [(0, 0), (0, 0), (0, 0)]
#guard emptyInvalid [(17, 99), (0, 0), (29, 8)]

end NLAlibTools.LUBlockedOpsSmoke
