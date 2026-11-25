/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.CholeskyFactorization
import NLAlib.Matrix.Computation.LU
import NLAlib.Matrix.Computation.PartialPivot
import NLAlib.Matrix.Computation.FactorizationSolve
import NLAlib.Matrix.Computation.TriangularSolve

/-!
# Runtime checks for stored dense factorizations

These run the actual instruction builders under the existing tool Float interpreter. Known
factors, reconstructed matrices, solve residuals, offset aliases and scratch release provide
regression checks independent of the formal proof scripts. No floating-point accuracy theorem
is inferred from these examples.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private def denseRun (routine : Builder Unit Unit ℕ ℕ Unit)
    (buffers : List (Array (Option Float))) : Option (St Unit Float (ℕ × ℕ × ℕ)) :=
  exec (floatInterp #[] []) routine.run (initState buffers)

private def closeVector (actual expected : List Float) : Bool :=
  actual.length == expected.length && (actual.zip expected).all fun (x, y) =>
    (x - y).abs ≤ 1e-10

private def matchesBuffer (result : Option (St Unit Float (ℕ × ℕ × ℕ))) (b : ℕ)
    (expected : List Float) (buffers : ℕ) : Bool :=
  match result with
  | none => false
  | some st => st.store.size == buffers && closeVector (showBuf st b) expected

private def spdInput : Array Float := #[4, 12, -16, 12, 37, -43, -16, -43, 98]
private def lowerExpected : List Float := [2, 6, -8, 0, 1, 5, 0, 0, 3]

-- The classic 3-by-3 SPD example, including unchanged source and unrelated sentinel data.
private def choleskySeparate := denseRun (cholesky () 3 0 0 1 0)
  [spdInput.map some, Array.replicate 9 none, #[some 101, some 909]]
#guard matchesBuffer choleskySeparate 1 lowerExpected 3
#guard matchesBuffer choleskySeparate 0 spdInput.toList 3
#guard matchesBuffer choleskySeparate 2 [101, 909] 3

-- Source and destination overlap at different offsets; outside cells retain their values.
private def choleskyOverlap := denseRun (cholesky () 3 0 1 0 2)
  [((#[101] ++ spdInput ++ #[303, 909]).map some)]
#guard matchesBuffer choleskyOverlap 0 ([101, 4] ++ lowerExpected ++ [909]) 1
#guard matchesBuffer (denseRun (cholesky () 1 0 0 0 0) [#[some 4]]) 0 [2] 1
#guard (denseRun (cholesky () 0 17 9 23 11) []).isSome

-- The exact-SPD theorem deliberately excludes this zero-pivot breakdown input.
#guard (denseRun (cholesky () 1 0 0 1 0) [#[some 0], #[none]]).isNone

private def upperInput : Array Float := #[2, 0, 0, 1, -8, 0, 1, -2, 1]
private def lowerInput : Array Float := lowerExpected.toArray

#guard matchesBuffer
  (denseRun (trsvUpper () 3 0 0 1 0) [upperInput.map some, (#[7, -22, 3]).map some])
  1 [1, 2, 3] 2
#guard matchesBuffer
  (denseRun (trsvLowerAdjoint () 3 0 0 1 0) [lowerInput.map some, (#[-10, 17, 9]).map some])
  1 [1, 2, 3] 2
#guard matchesBuffer
  (denseRun (trsvUpperAdjoint () 3 0 0 1 0) [upperInput.map some, (#[2, -15, 0]).map some])
  1 [1, 2, 3] 2

-- Packing consumes both operands before copy-back, even when they occupy the same cells.
#guard matchesBuffer
  (denseRun (trsvUpper () 2 0 0 0 0) [(#[2, 0, 1, 3]).map some]) 0 [1, 0, 1, 3] 1
#guard (denseRun (trsvUpper () 0 17 9 23 11) []).isSome
#guard (denseRun (trsvLowerAdjoint () 0 17 9 23 11) []).isSome
#guard (denseRun (trsvUpperAdjoint () 0 17 9 23 11) []).isSome

private def luInput : Array Float := #[2, 4, -2, 1, -6, 7, 1, 0, 2]
private def luLowerExpected : List Float := [1, 2, -1, 0, 1, -1, 0, 0, 1]

private def luSeparate := denseRun (luFactor () 3 0 1 2 0 0 0)
  [luInput.map some, Array.replicate 9 none, Array.replicate 9 none, #[some 909]]
#guard matchesBuffer luSeparate 0 luInput.toList 4
#guard matchesBuffer luSeparate 1 luLowerExpected 4
#guard matchesBuffer luSeparate 2 upperInput.toList 4
#guard matchesBuffer luSeparate 3 [909] 4

-- Independently multiply the computed factors; do not compare an execution trace to itself.
private def productClose (L U A : List Float) (n : ℕ) : Bool :=
  (List.range (n * n)).all fun t =>
    let i := t % n
    let j := t / n
    let v := (List.range n).foldl (fun v k => v + L[i + n * k]?.getD 0 * U[k + n * j]?.getD 0) 0
    (v - A[t]?.getD 0).abs ≤ 1e-10
#guard match luSeparate with
  | none => false
  | some st => productClose (showBuf st 1) (showBuf st 2) luInput.toList 3

private def luOffsets := denseRun (luFactor () 3 0 1 2 1 2 1)
  [((#[101] ++ luInput ++ #[909]).map some),
    #[some 101, some 303] ++ Array.replicate 9 none ++ #[some 909],
    #[some 303] ++ Array.replicate 9 none ++ #[some 909]]
#guard matchesBuffer luOffsets 1 ([101, 303] ++ luLowerExpected ++ [909]) 3
#guard matchesBuffer luOffsets 2 ([303] ++ upperInput.toList ++ [909]) 3
#guard (denseRun (luFactor () 0 17 23 29 9 11 13) []).isSome
#guard (denseRun (luFactor () 2 0 1 2 0 0 0)
  [(#[0, 1, 1, 0]).map some, Array.replicate 4 none, Array.replicate 4 none]).isNone

-- The original tool interpreter predates dynamic index binders. Supply nonnegative finite
-- conversion within binary64's exact-integer range for these pivot runtime tests. This
-- exercises the binder; it is not a proof of the interpreter's arithmetic contracts.
private def pivotRun (n k R off : ℕ) (index : Cell ℕ ℕ)
    (buffers : List (Array (Option Float))) : Option (St Unit Float (ℕ × ℕ × ℕ)) :=
  let I := floatIndexedInterp #[] []
  exec I (partialPivot () (.const n) (.const k) R (.const off) index).run (initState buffers)

private def pivotOffsets := pivotRun 2 0 0 1 ⟨1, 1⟩
  [(#[101, 0, 2, 1, 3, 909]).map some, #[some 101, none, some 909]]
#guard matchesBuffer pivotOffsets 0 [101, 2, 0, 3, 1, 909] 2
#guard matchesBuffer pivotOffsets 1 [101, 1, 909] 2

private def pivotTiesInput : Array Float := #[1, 2, 3, 4, -7, 7, 8, 9, 10]
private def pivotTies := pivotRun 3 1 0 0 ⟨1, 0⟩ [pivotTiesInput.map some, #[none]]
#guard matchesBuffer pivotTies 0 pivotTiesInput.toList 2
#guard matchesBuffer pivotTies 1 [1] 2
#guard matchesBuffer
  (pivotRun 3 2 0 0 ⟨1, 0⟩ [pivotTiesInput.map some, #[none]]) 1 [2] 2
#guard matchesBuffer
  (pivotRun 3 1 0 0 ⟨1, 0⟩ [Array.replicate 9 (some 0), #[none]]) 1 [1] 2

-- Execute factorization and both solves, rather than starting with supplied factors.
#guard matchesBuffer
  (denseRun (choleskySolve () 3 0 0 1 0)
    [spdInput.map some, (#[-20, -43, 192]).map some]) 1 [1, 2, 3] 2
#guard matchesBuffer
  (denseRun (luSolve () 3 0 0 1 0)
    [luInput.map some, (#[7, -8, 18]).map some]) 1 [1, 2, 3] 2

-- The right-hand side is the first input column, so the exact solution is the first basis
-- vector. Other matrix cells stay unchanged even though matrix/RHS storage overlaps.
#guard matchesBuffer
  (denseRun (choleskySolve () 2 0 0 0 0) [(#[4, 2, 2, 3]).map some]) 0 [1, 0, 2, 3] 1
#guard matchesBuffer
  (denseRun (luSolve () 2 0 0 0 0) [(#[2, 4, 1, -6]).map some]) 0 [1, 0, 1, -6] 1
#guard (denseRun (choleskySolve () 0 17 9 23 11) []).isSome
#guard (denseRun (luSolve () 0 17 9 23 11) []).isSome

-- Deliberately perturb multiplications so exact Schur cancellation fails. The factor must
-- still have literal zeros in its upper triangle; a tolerance-only residual check misses this.
private def perturbedInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatInterp #[] [] with
    sem := { floatSem with
      bin := fun p op x y => match op with
        | .mul => some (x * y * 1.0001)
        | _ => floatSem.bin p op x y } }

private def noisySchur := exec perturbedInterp (schurStep () 2 0 0 0).run
  (initState [(#[4, 1, 1, 3]).map some])
private def noisyCholesky := exec perturbedInterp (cholesky () 2 0 0 1 0).run
  (initState [(#[4, 1, 1, 3]).map some, Array.replicate 4 none])
#guard match noisySchur with
  | none => false
  | some st => (showBuf st 0)[2]?.getD 0 != 0
#guard match noisyCholesky with
  | none => false
  | some st => st.store.size == 2 && (showBuf st 1)[2]?.getD 1 == 0

end NLAlibTools
