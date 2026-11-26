/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.Cholesky.Blocked
import NLAlib.Ops.Tools.Machines
import NLAlib.Ops.Catalog.Index

/-!
# Actual blocked Cholesky regressions

Finite Float checks exercise clipped scalar panels, packed scalar GEMM, root scaling,
offsets, source overlap and handle-free empty execution. Reference Gram multiplication is
independent of the elimination steps. No universal native Float accuracy law is asserted.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.CholeskyBlockedOpsSmoke

private def interpreter (rejectAll : Bool := false) : Interp (ScalarOp ⊕ IndexOp) Qry Float :=
  withQueries fun op => match op with
    | .inl o => if rejectAll then { floatMachine.fn o with fn := fun _ _ _ => none }
      else floatMachine.fn o
    | .inr .lit => floatMachine.indexFn

private def lower (n : ℕ) : List Float :=
  (List.range (n * n)).map fun t =>
    let i := t % n
    let j := t / n
    if i < j then 0 else if i == j then Float.ofNat (2 ^ (i + 1)) else Float.ofNat (i - j)

private def gram (n : ℕ) (l : List Float) (i j : ℕ) : Float :=
  ((List.range n).map fun k => l.getD (k * n + i) 0 * l.getD (k * n + j) 0).sum

private def matrix (n : ℕ) : List Float :=
  (List.range (n * n)).map fun t => gram n (lower n) (t % n) (t / n)

private def check (n block : ℕ) : Bool := Id.run do
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry := NLAlib.Cholesky.factorBlocked
  let a := matrix n
  let source := vals ([101] ++ a ++ [103])
  let output := vals [107, 109] ++ blank (n * n) ++ vals [113]
  let initial : Mem Float := ⟨[source, output], 17⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n, block, (n + block - 1) / block] [(0, 1), (1, 2)]) initial | return false
  let some l := final.store.readBlock 1 2 (n * n) | return false
  return final.pos == 17 && final.store.length == 2 && final.store.shape == initial.store.shape &&
    final.store[0]? == some source && l == lower n &&
    final.store.get 1 0 == some 107 && final.store.get 1 1 == some 109 &&
    final.store.get 1 (2 + n * n) == some 113 && (List.range n).all fun i =>
      (List.range n).all fun j => (a.getD (j * n + i) 0 - gram n l i j).abs ≤ 1e-10

private def overlap (n block shift : ℕ) : Bool := Id.run do
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry := NLAlib.Cholesky.factorBlocked
  let a := matrix n
  let source := vals ([137] ++ a ++ List.replicate shift 139 ++ [149])
  let initial : Mem Float := ⟨[source], 19⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n, block, (n + block - 1) / block] [(0, 1), (0, 1 + shift)]) initial
    | return false
  let some l := final.store.readBlock 0 (1 + shift) (n * n) | return false
  return final.pos == 19 && final.store.shape == initial.store.shape &&
    final.store.length == 1 && l == lower n && final.store.get 0 0 == some 137 &&
    final.store.get 0 (1 + n * n + shift) == some 149 &&
    (if shift == 0 then true else final.store.get 0 1 == some (a.headD 0))

private def emptyInvalid (args : List (ℕ × ℕ)) : Bool :=
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry := NLAlib.Cholesky.factorBlocked
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
#guard overlap 3 1 0
#guard overlap 3 2 1
#guard overlap 5 3 0
#guard overlap 5 3 2
#guard emptyInvalid [(11, 91), (13, 17)]
#guard emptyInvalid [(0, 0), (0, 0)]
#guard emptyInvalid [(17, 99), (0, 0)]

end NLAlibTools.CholeskyBlockedOpsSmoke
