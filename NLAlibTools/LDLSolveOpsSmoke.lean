/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LDL.Solve
import NLAlib.Ops.Tools.Machines
import NLAlib.Ops.Catalog.Index

/-!
# Actual LDL factor-and-solve regressions

These finite runs exercise the full actual factorization, forward substitution, stored
diagonal divisions and transposed-lower substitution on definite and indefinite systems.
The fixture constructs a Gram-with-signed-diagonal input and RHS by independent sums.
Native Float observations assert no universal rounding law.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.LDLSolveOpsSmoke

private def interpreter (rejectAll : Bool := false) : Interp (ScalarOp ⊕ IndexOp) Qry Float :=
  withQueries fun op => match op with
    | .inl o => if rejectAll then { floatMachine.fn o with fn := fun _ _ _ => none }
      else floatMachine.fn o
    | .inr .lit => floatMachine.indexFn

private def lower (i j : ℕ) : Float :=
  if i < j then 0 else if i == j then 1 else Float.ofNat (i - j)

private def diagonal (signed : Bool) (k : ℕ) : Float :=
  (if signed && k % 2 == 1 then -1 else 1) * Float.ofNat (2 ^ (k + 1))

private def matrix (n : ℕ) (signed : Bool) (i j : ℕ) : Float :=
  ((List.range n).map fun k => lower i k * diagonal signed k * lower j k).sum

private def solution (i : ℕ) : Float :=
  (if i % 2 == 1 then -1 else 1) * Float.ofNat (i + 1)

private def check (n : ℕ) (signed : Bool) (aliasKind : ℕ) : Bool := Id.run do
  let a := (List.range (n * n)).map fun t => matrix n signed (t % n) (t / n)
  let b := (List.range n).map fun i =>
    ((List.range n).map fun j => matrix n signed i j * solution j).sum
  let source := vals ([101] ++ a ++ [103])
  let rhs := vals ([107, 109] ++ b ++ [113])
  let output := vals [127] ++ blank n ++ vals [131]
  let initial : Mem Float := ⟨[source, rhs, output], 17⟩
  let x := if aliasKind == 1 then (1, 2) else if aliasKind == 2 then (0, 1) else (2, 1)
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry := NLAlib.LDL.solve
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n] [(0, 1), (1, 2), x]) initial | return false
  let some xs := final.store.readBlock x.1 x.2 n | return false
  return xs == (List.range n).map solution && final.pos == 17 &&
    final.store.shape == initial.store.shape && final.store.length == 3 &&
    final.store.get 0 0 == some 101 && final.store.get 0 (1 + n * n) == some 103 &&
    final.store.get 1 0 == some 107 && final.store.get 1 1 == some 109 &&
    final.store.get 1 (2 + n) == some 113 &&
    (if aliasKind == 2 then true else final.store[0]? == some source) &&
    (if aliasKind == 1 then true else final.store[1]? == some rhs)

private def emptyInvalid (args : List (ℕ × ℕ)) : Bool :=
  let routine : Routine (ScalarOp ⊕ IndexOp) Qry := NLAlib.LDL.solve
  let initial : Mem Float := ⟨[], 23⟩
  match NLAlib.Ops.eval (interpreter true) (fun _ _ => 0) routine.body
      (Env.frame [0] args) initial with
  | some final => final.store.isEmpty && final.pos == 23
  | none => false

#guard check 0 false 0
#guard check 1 false 0
#guard check 1 true 0
#guard check 3 false 0
#guard check 3 true 0
#guard check 4 true 0
#guard check 3 true 1
#guard check 4 true 1
#guard check 3 true 2
#guard check 4 false 2
#guard emptyInvalid [(17, 90), (23, 17), (29, 42)]
#guard emptyInvalid [(0, 0), (0, 0), (0, 0)]
#guard emptyInvalid [(17, 99), (23, 42), (0, 0)]

end NLAlibTools.LDLSolveOpsSmoke
