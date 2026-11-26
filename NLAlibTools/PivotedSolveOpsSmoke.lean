/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.PivotedSolve
import NLAlib.Matrix.Factorizations.LU.CompleteSolve
import NLAlib.Ops.Profiles.ScalarIndex
import NLAlib.Ops.Tools.Machines

/-!
# Actual partial- and complete-pivot factor-and-solve regressions

The actual stored factorization, log replay, triangular solves and inverse column replay are
executed on nonsingular matrices. Independent multiplication supplies each RHS and checks the
original-system residual. Unequal row/column histories include two three-cycles and a dense
late column exchange. Layouts cover separate buffers, exact RHS aliases, disjoint shifted
vectors in one buffer, source/output overlap and a shared source/RHS/output first column.
A slightly biased scalar diagnostic uses a separate residual tolerance. These finite native
observations are not a universal Float rounding theorem.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.PivotedSolveOpsSmoke

private def biasedMachine : Machine Float := { floatMachine with
  add := fun a b => (a + b) * (1 + 1e-8)
  sub := fun a b => (a - b) * (1 + 1e-8)
  mul := fun a b => (a * b) * (1 + 1e-8)
  div := fun a b => (a / b) * (1 + 1e-8) }

private def signed (i : ℕ) : Float := Float.ofInt ((Int.ofNat (i % 5)) - 2) / 4

private def base (n i j : ℕ) : Float :=
  ((List.range n).map fun k =>
    (if i < k then 0 else if i == k then 1 else signed (i + 2 * k)) *
      (if j < k then 0 else if j == k then Float.ofNat (2 ^ (k + 1))
        else signed (2 * k + j))).sum

private def matrix (n fixture : ℕ) : List Float :=
  if fixture == 1 then [0, 1, 2, 1]
  else if fixture == 2 then [0, 0, 8, 4, 0, 0, 0, 16, 0]
  else if fixture == 3 then [2, 1, 4, 0, 1, 2, 1, 2, 3]
  else (List.range (n * n)).map fun t => base n ((t % n + 1) % n) ((t / n + 2) % n)

private def product (n : ℕ) (a x : List Float) : List Float :=
  (List.range n).map fun i =>
    ((List.range n).map fun j => a.getD (j * n + i) 0 * x.getD j 0).sum

private def maxAbs (xs : List Float) : Float :=
  xs.foldl (fun a b => if a < b.abs then b.abs else a) 0

private def framed (initial final : Mem Float) (x : ℕ × ℕ) (n : ℕ) : Bool :=
  final.pos == initial.pos && final.store.shape == initial.store.shape &&
    (List.range initial.store.length).all fun b => (List.range (initial.store.len b)).all fun j =>
      (b == x.1 && x.2 ≤ j && j < x.2 + n) || final.store.get b j == initial.store.get b j

private def runCase (n fixture mode : ℕ) (complete biased : Bool) : Bool := Id.run do
  let a := matrix n fixture
  let known := (List.range n).map fun i =>
    if mode == 2 || mode == 4 then (if i == 0 then 1 else 0)
    else Float.ofInt (if i % 2 == 0 then Int.ofNat (i + 1) else -(Int.ofNat (i + 1)))
  let b := product n a known
  let source := vals ([101] ++ a ++ List.replicate (n + 1) 103 ++ [107])
  let rhs := vals ([109, 113] ++ b ++ [127, 131])
  let output := vals [137, 139, 149] ++ blank n ++ vals [151]
  let shifted := rhs ++ blank n ++ vals [157]
  let buffers := if mode == 0 then [source, rhs, output]
    else if mode == 2 then [source, output] else if mode == 4 then [source]
    else if mode == 5 then [source, shifted] else [source, rhs]
  let bp := if mode == 2 || mode == 4 then (0, 1) else (1, 2)
  let xp := if mode == 0 then (2, 3) else if mode == 1 then (1, 2)
    else if mode == 2 then (1, 3) else if mode == 5 then (1, n + 4)
    else if mode == 6 then (0, 2) else (0, 1)
  let initial : Mem Float := ⟨buffers, 29⟩
  let interp : Interp ScalarIndex.Operation ScalarIndex.Queries Float :=
    withQueries (ScalarIndex.functions (if biased then biasedMachine else floatMachine))
  let routine : Routine ScalarIndex.Operation ScalarIndex.Queries :=
    if complete then NLAlib.LU.solveComplete else NLAlib.LU.solvePartial
  let some final := NLAlib.Ops.eval interp (fun _ _ => 0) routine.body
    (Env.frame [n] [(0, 1), bp, xp]) initial | return false
  let some xs := final.store.readBlock xp.1 xp.2 n | return false
  let residual := maxAbs (List.zipWith (· - ·) (product n a xs) b)
  let error := maxAbs (List.zipWith (· - ·) xs known)
  let scale := maxAbs a * Float.ofNat n * maxAbs xs + maxAbs b + 1
  let tolerance := (if biased then 1e-5 else 1e-10) * Float.ofNat (n + 1) * scale
  return framed initial final xp n && residual ≤ tolerance && error ≤ tolerance

private def grid (n fixture mode : ℕ) : Bool :=
  [false, true].all fun complete => [false, true].all fun biased =>
    runCase n fixture mode complete biased

private def logs (a expectedRows expectedCols : List Float) : Bool := Id.run do
  let initial : Mem Float := ⟨[vals a, blank 9, blank 9, blank 3, blank 3], 31⟩
  let interp : Interp ScalarIndex.Operation ScalarIndex.Queries Float :=
    withQueries (ScalarIndex.functions floatMachine)
  let routine : Routine ScalarIndex.Operation ScalarIndex.Queries := NLAlib.LU.factorComplete
  let some final := NLAlib.Ops.eval interp (fun _ _ => 0) routine.body
    (Env.frame [3] [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]) initial | return false
  return final.store.readBlock 3 0 3 == some expectedRows &&
    final.store.readBlock 4 0 3 == some expectedCols

private def closedInPlace (complete : Bool) : Bool := Id.run do
  let a := matrix 3 2
  let known : List Float := [1, -2, 3]
  let initial : Mem Float := ⟨[vals a, vals (product 3 a known)], 37⟩
  let routine : Routine ScalarIndex.Operation ScalarIndex.Queries :=
    if complete then NLAlib.LU.solveCompleteInPlace else NLAlib.LU.solvePartialInPlace
  let program := routine.close 1 2
  let interp : Interp ScalarIndex.Operation ScalarIndex.Queries Float :=
    withQueries (ScalarIndex.functions floatMachine)
  let some final := NLAlib.Ops.eval interp (fun _ _ => 0) program.body
    (Program.environment (b := 2) (fun _ : Fin 1 => 3)) initial | return false
  let some xs := final.store.readBlock 1 0 3 | return false
  return maxAbs (List.zipWith (· - ·) xs known) < 1e-10 && framed initial final (1, 0) 3

private def emptyInvalid (kind : ℕ) (args : List (ℕ × ℕ)) : Bool :=
  let routine : Routine ScalarIndex.Operation ScalarIndex.Queries :=
    if kind == 0 then NLAlib.LU.solvePartial else if kind == 1 then NLAlib.LU.solveComplete
    else if kind == 2 then NLAlib.LU.solvePartialInPlace else NLAlib.LU.solveCompleteInPlace
  let interp : Interp ScalarIndex.Operation ScalarIndex.Queries Float :=
    withQueries fun op => { ScalarIndex.functions floatMachine op with fn := fun _ _ _ => none }
  let initial : Mem Float := ⟨[], 41⟩
  match NLAlib.Ops.eval interp (fun _ _ => 0) routine.body (Env.frame [0] args) initial with
  | some final => final.store.isEmpty && final.pos == 41
  | none => false

#guard grid 0 0 0
#guard grid 0 0 1
#guard grid 0 0 2
#guard grid 0 0 3
#guard grid 0 0 4
#guard grid 0 0 5
#guard grid 0 0 6
#guard grid 1 0 0
#guard grid 1 0 1
#guard grid 1 0 2
#guard grid 1 0 3
#guard grid 1 0 4
#guard grid 1 0 5
#guard grid 1 0 6
#guard grid 2 0 0
#guard grid 2 0 1
#guard grid 2 0 2
#guard grid 2 0 3
#guard grid 2 0 4
#guard grid 2 0 5
#guard grid 2 0 6
#guard grid 3 0 0
#guard grid 3 0 1
#guard grid 3 0 2
#guard grid 3 0 3
#guard grid 3 0 4
#guard grid 3 0 5
#guard grid 3 0 6
#guard grid 4 0 0
#guard grid 4 0 1
#guard grid 4 0 2
#guard grid 4 0 3
#guard grid 4 0 4
#guard grid 4 0 5
#guard grid 4 0 6
#guard grid 5 0 0
#guard grid 5 0 1
#guard grid 5 0 2
#guard grid 5 0 3
#guard grid 5 0 4
#guard grid 5 0 5
#guard grid 5 0 6
#guard grid 8 0 0
#guard grid 8 0 1
#guard grid 8 0 2
#guard grid 8 0 3
#guard grid 8 0 4
#guard grid 8 0 5
#guard grid 8 0 6
#guard grid 2 1 0
#guard grid 2 1 1
#guard grid 2 1 2
#guard grid 2 1 3
#guard grid 2 1 4
#guard grid 2 1 5
#guard grid 2 1 6
#guard grid 3 2 0
#guard grid 3 2 1
#guard grid 3 2 2
#guard grid 3 2 3
#guard grid 3 2 4
#guard grid 3 2 5
#guard grid 3 2 6
#guard grid 3 3 0
#guard grid 3 3 1
#guard grid 3 3 2
#guard grid 3 3 3
#guard grid 3 3 4
#guard grid 3 3 5
#guard grid 3 3 6

#guard logs (matrix 3 2) [1, 2, 2] [2, 2, 2]
#guard logs (matrix 3 3) [2, 1, 2] [0, 2, 2]
#guard closedInPlace false
#guard closedInPlace true
#guard emptyInvalid 0 []
#guard emptyInvalid 0 [(17, 91), (23, 41), (29, 83)]
#guard emptyInvalid 0 [(0, 0), (0, 0), (0, 0)]
#guard emptyInvalid 1 []
#guard emptyInvalid 1 [(17, 91), (23, 41), (29, 83)]
#guard emptyInvalid 1 [(0, 0), (0, 0), (0, 0)]
#guard emptyInvalid 2 []
#guard emptyInvalid 2 [(17, 91), (23, 41), (29, 83)]
#guard emptyInvalid 2 [(0, 0), (0, 0), (0, 0)]
#guard emptyInvalid 3 []
#guard emptyInvalid 3 [(17, 91), (23, 41), (29, 83)]
#guard emptyInvalid 3 [(0, 0), (0, 0), (0, 0)]

end NLAlibTools.PivotedSolveOpsSmoke
