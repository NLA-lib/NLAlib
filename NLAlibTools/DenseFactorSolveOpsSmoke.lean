/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.Cholesky.Solve
import NLAlib.Matrix.Factorizations.LU.Solve
import NLAlib.Ops.Tools.Machines
import NLAlib.Ops.Profiles.ScalarIndex

/-!
# Broad actual factor-and-solve numerical regressions

Dyadic lower/upper products supply nonsymmetric and indefinite LU cases; lower Gram products
supply SPD cases. The complete actual factorization and substitutions are executed under the
native diagnostic Float backend and an instrumented backend biasing arithmetic, roots and
negative literals. Independent residuals and known solutions are checked with every source,
right-hand-side and output alias pattern supported by the copy-first scalar execution.
Frames include uninitialized words, offsets, all extents, tape position and scoped scratch.
These finite regressions do not assert a universal Float or artificial-backend error model.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.DenseFactorSolveOpsSmoke

private def biasedMachine : Machine Float := { floatMachine with
  lit := fun q => ratToFloat q * (if q < 0 then 1.001 else 1)
  add := fun a b => (a + b) * 1.001
  sub := fun a b => (a - b) * 1.001
  mul := fun a b => (a * b) * 1.001
  div := fun a b => (a / b) * 1.001
  sqrt := fun a => a.sqrt * 1.001 }

private def signed (i : ℕ) : Float := Float.ofInt ((Int.ofNat (i % 5)) - 2) / 4

private def lower (seed i j : ℕ) (chol : Bool) : Float :=
  if i < j then 0 else if i == j then
    (if chol then Float.ofNat (3 + seed + i) else 1) else signed (i + 2 * j + seed)

private def upper (seed i j : ℕ) : Float :=
  if j < i then 0 else if i == j then
    Float.ofNat (3 + seed + i) * (if (i + seed) % 2 == 0 then 1 else -1)
  else 1 + signed (2 * i + j + seed)

private def matrix (n seed : ℕ) (chol : Bool) : List Float :=
  (List.range (n * n)).map fun q =>
    ((List.range n).map fun k => lower seed (q % n) k chol *
      (if chol then lower seed (q / n) k true else upper seed k (q / n))).sum

private def product (n : ℕ) (a x : List Float) : List Float :=
  (List.range n).map fun i =>
    ((List.range n).map fun j => a.getD (j * n + i) 0 * x.getD j 0).sum

private def absMax (xs : List Float) : Float :=
  xs.foldl (fun a b => if a < b.abs then b.abs else a) 0

private def residual (n : ℕ) (a b x : List Float) : Float :=
  absMax (List.zipWith (· - ·) (product n a x) b)

private def matrixNorm (n : ℕ) (a : List Float) : Float :=
  absMax ((List.range n).map fun i =>
    ((List.range n).map fun j => (a.getD (j * n + i) 0).abs).sum)

private def framed (initial final : Mem Float) (xb xo n : ℕ) : Bool :=
  initial.pos == final.pos && initial.store.length == final.store.length &&
    (List.range initial.store.length).all fun b =>
      final.store.len b == initial.store.len b && (List.range (initial.store.len b)).all fun i =>
        if b == xb && xo ≤ i && i < xo + n then true
        else final.store.get b i == initial.store.get b i

private def runCase (n seed mode : ℕ) (chol biased : Bool) : Option Float := do
  let a := matrix n seed chol
  let known := (List.range n).map fun i => if mode == 2 || mode == 4 then
    (if i == 0 then 1 else 0) else 2 * signed (i + seed)
  let b := product n a known
  let source := vals ([307] ++ a ++ [311])
  let rhs := vals ([313, 317] ++ b ++ [331])
  let output := [some 337, some 347, some 349] ++ blank n ++ [some 353]
  let buffers := if mode == 0 then [source, rhs, output]
    else if mode == 1 || mode == 3 then [source, rhs]
    else if mode == 2 then [source, output] else [source]
  let bp := if mode == 2 || mode == 4 then (0, 1) else (1, 2)
  let xp := if mode == 1 then (1, 2) else if mode == 2 then (1, 3)
    else if mode == 3 || mode == 4 then (0, 1) else (2, 3)
  let initial : Mem Float := ⟨buffers, 41⟩
  let m := if biased then biasedMachine else floatMachine
  let interp : Interp ScalarIndex.Operation ScalarIndex.Queries Float :=
    withQueries (ScalarIndex.functions m)
  let routine : Routine ScalarIndex.Operation ScalarIndex.Queries :=
    if chol then NLAlib.Cholesky.solve else NLAlib.LU.solve
  let final ← NLAlib.Ops.eval interp (fun _ _ => 0) routine.body
    (Env.frame [n] [(0, 1), bp, xp]) initial
  let x ← final.store.readBlock xp.1 xp.2 n
  let r := residual n a b x
  let scale := matrixNorm n a * absMax x + absMax b + 1
  let tolerance := if biased then 0.01 * Float.ofNat (n + 1) * scale else 1e-9
  if framed initial final xp.1 xp.2 n && r ≤ tolerance &&
      (biased || absMax (List.zipWith (· - ·) x known) ≤ 1e-9) then some r else none

private def grid (n seed mode : ℕ) : Bool :=
  [false, true].all fun chol => [false, true].all fun biased =>
    (runCase n seed mode chol biased).isSome

#guard grid 0 0 0
#guard grid 0 0 1
#guard grid 0 0 2
#guard grid 0 0 3
#guard grid 0 0 4
#guard grid 0 1 0
#guard grid 0 1 1
#guard grid 0 1 2
#guard grid 0 1 3
#guard grid 0 1 4
#guard grid 0 3 0
#guard grid 0 3 1
#guard grid 0 3 2
#guard grid 0 3 3
#guard grid 0 3 4
#guard grid 1 0 0
#guard grid 1 0 1
#guard grid 1 0 2
#guard grid 1 0 3
#guard grid 1 0 4
#guard grid 1 1 0
#guard grid 1 1 1
#guard grid 1 1 2
#guard grid 1 1 3
#guard grid 1 1 4
#guard grid 1 3 0
#guard grid 1 3 1
#guard grid 1 3 2
#guard grid 1 3 3
#guard grid 1 3 4
#guard grid 2 0 0
#guard grid 2 0 1
#guard grid 2 0 2
#guard grid 2 0 3
#guard grid 2 0 4
#guard grid 2 1 0
#guard grid 2 1 1
#guard grid 2 1 2
#guard grid 2 1 3
#guard grid 2 1 4
#guard grid 2 3 0
#guard grid 2 3 1
#guard grid 2 3 2
#guard grid 2 3 3
#guard grid 2 3 4
#guard grid 3 0 0
#guard grid 3 0 1
#guard grid 3 0 2
#guard grid 3 0 3
#guard grid 3 0 4
#guard grid 3 1 0
#guard grid 3 1 1
#guard grid 3 1 2
#guard grid 3 1 3
#guard grid 3 1 4
#guard grid 3 3 0
#guard grid 3 3 1
#guard grid 3 3 2
#guard grid 3 3 3
#guard grid 3 3 4
#guard grid 4 0 0
#guard grid 4 0 1
#guard grid 4 0 2
#guard grid 4 0 3
#guard grid 4 0 4
#guard grid 4 1 0
#guard grid 4 1 1
#guard grid 4 1 2
#guard grid 4 1 3
#guard grid 4 1 4
#guard grid 4 3 0
#guard grid 4 3 1
#guard grid 4 3 2
#guard grid 4 3 3
#guard grid 4 3 4
#guard grid 6 0 0
#guard grid 6 0 1
#guard grid 6 0 2
#guard grid 6 0 3
#guard grid 6 0 4
#guard grid 6 1 0
#guard grid 6 1 1
#guard grid 6 1 2
#guard grid 6 1 3
#guard grid 6 1 4
#guard grid 6 3 0
#guard grid 6 3 1
#guard grid 6 3 2
#guard grid 6 3 3
#guard grid 6 3 4
#guard grid 8 0 0
#guard grid 8 0 1
#guard grid 8 0 2
#guard grid 8 0 3
#guard grid 8 0 4
#guard grid 8 1 0
#guard grid 8 1 1
#guard grid 8 1 2
#guard grid 8 1 3
#guard grid 8 1 4
#guard grid 8 3 0
#guard grid 8 3 1
#guard grid 8 3 2
#guard grid 8 3 3
#guard grid 8 3 4

#guard (runCase 3 1 0 false true).map (fun r => decide (1e-4 < r)) == some true
#guard (runCase 3 1 0 true true).map (fun r => decide (1e-4 < r)) == some true

private def emptyInvalid (kind : ℕ) (args : List (ℕ × ℕ)) : Bool :=
  let routine : Routine ScalarIndex.Operation ScalarIndex.Queries :=
    if kind == 0 then NLAlib.LU.solve else if kind == 1 then NLAlib.Cholesky.solve
    else if kind == 2 then NLAlib.TriangularSolve.factors else NLAlib.TriangularSolve.cholesky
  let interp : Interp ScalarIndex.Operation ScalarIndex.Queries Float :=
    withQueries fun op => { ScalarIndex.functions floatMachine op with fn := fun _ _ _ => none }
  let initial : Mem Float := ⟨[], 43⟩
  match NLAlib.Ops.eval interp (fun _ _ => 0) routine.body (Env.frame [0] args) initial with
  | some final => final.store.isEmpty && final.pos == 43
  | none => false

#guard emptyInvalid 0 []
#guard emptyInvalid 1 []
#guard emptyInvalid 2 []
#guard emptyInvalid 3 []
#guard emptyInvalid 0 [(17, 91), (23, 41), (29, 83)]
#guard emptyInvalid 1 [(17, 91), (23, 41), (29, 83)]
#guard emptyInvalid 2 [(17, 91), (23, 41), (29, 83), (31, 89)]
#guard emptyInvalid 3 [(17, 91), (23, 41), (29, 83)]
#guard emptyInvalid 0 [(0, 0), (0, 0), (0, 0)]
#guard emptyInvalid 1 [(0, 0), (0, 0), (0, 0)]
#guard emptyInvalid 2 [(0, 0), (0, 0), (0, 0), (0, 0)]
#guard emptyInvalid 3 [(0, 0), (0, 0), (0, 0)]

end NLAlibTools.DenseFactorSolveOpsSmoke
