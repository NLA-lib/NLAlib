/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.BlockSchurUpdate
import NLAlib.Matrix.Computation.MatrixBlockCopy

/-!
# Runtime checks for rectangular copies and block Schur updates

Actual copy loops retain gaps and offsets even with all scalar operations disabled. Actual
GEMM-backed updates are checked against independently computed products, including input/output
overlap, zero panel width and empty dimensions. These examples do not certify Float accuracy.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private def blockRun (I : Interp Unit Unit Float (ℕ × ℕ × ℕ))
    (b : Builder Unit Unit ℕ ℕ Unit) (buffers : List (Array (Option Float))) :=
  exec I b.run (initState buffers)

private def blockMatches (result : Option (St Unit Float (ℕ × ℕ × ℕ)))
    (buf : ℕ) (expected : List Float) (count : ℕ) : Bool :=
  match result with
  | none => false
  | some st => st.store.size == count && showBuf st buf == expected

private def copyOnlyBlocks : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatInterp #[] [] with sem := failSem }

private def blockSource : Array Float :=
  #[0, 1, 2, 3, 10, 11, 12, 13, 20, 21, 22, 23, 30, 31, 32, 33]
private def gatheredBlock := blockRun copyOnlyBlocks
  (gatherMatrixBlock () 2 2 4 0 1 1 1 1 1)
  [((#[303] ++ blockSource ++ #[909]).map some),
    #[some 101] ++ Array.replicate 4 none ++ #[some 909]]
#guard blockMatches gatheredBlock 1 [101, 11, 12, 21, 22, 909] 2
#guard blockMatches gatheredBlock 0 ([303] ++ blockSource.toList ++ [909]) 2

private def scatteredBlock := blockRun copyOnlyBlocks
  (scatterMatrixBlock () 2 2 4 0 0 1 1 1 1)
  [(#[11, 12, 21, 22]).map some,
    #[some 101] ++ Array.replicate 16 (some 77) ++ #[some 909]]
#guard blockMatches scatteredBlock 1
  [101, 77, 77, 77, 77, 77, 11, 12, 77, 77, 21, 22, 77, 77, 77, 77, 77, 909] 2
#guard blockMatches scatteredBlock 0 [11, 12, 21, 22] 2

private def stridedBlock := blockRun copyOnlyBlocks
  (copyMatrixBlock () 1 3 0 1 0 4 0 0 0 5 2 1)
  [blockSource.map some, Array.replicate 22 (some 77)]
#guard match stridedBlock with
  | none => false
  | some st => st.store.size == 2 && (showBuf st 1).toArray ==
    Array.ofFn (fun i : Fin 22 => if i.val == 7 then 0 else if i.val == 12 then 10
      else if i.val == 17 then 20 else 77)
#guard blockMatches stridedBlock 0 blockSource.toList 2
#guard (blockRun copyOnlyBlocks (gatherMatrixBlock () 0 3 4 17 9 11 13 23 29) []).isSome
#guard (blockRun copyOnlyBlocks (gatherMatrixBlock () 3 0 4 17 9 11 13 17 29) []).isSome
#guard (blockRun copyOnlyBlocks (scatterMatrixBlock () 0 3 4 17 9 17 11 13 29) []).isSome
#guard (blockRun copyOnlyBlocks (scatterMatrixBlock () 3 0 4 17 9 17 11 13 29) []).isSome

private def schurBlock := blockRun (floatInterp #[] [])
  (blockSchurUpdate () 2 1 2 0 1 2 0 0 0)
  [(#[1, 2]).map some, (#[3, 4]).map some, (#[10, 30, 20, 40]).map some, #[some 909]]
#guard blockMatches schurBlock 2 [7, 24, 16, 32] 4
#guard blockMatches schurBlock 0 [1, 2] 4
#guard blockMatches schurBlock 1 [3, 4] 4
#guard blockMatches schurBlock 3 [909] 4

private def blockAliasA := blockRun (floatInterp #[] [])
  (blockSchurUpdate () 2 1 2 0 1 0 0 0 0)
  [(#[10, 30, 20, 40]).map some, (#[3, 4]).map some]
#guard blockMatches blockAliasA 0 [-20, -60, -20, -80] 2
#guard blockMatches blockAliasA 1 [3, 4] 2
private def blockAliasB := blockRun (floatInterp #[] [])
  (blockSchurUpdate () 2 1 2 1 0 0 0 0 0)
  [(#[10, 30, 20, 40]).map some, (#[1, 2]).map some]
#guard blockMatches blockAliasB 0 [0, 10, -10, -20] 2
private def blockAliasAll := blockRun (floatInterp #[] [])
  (blockSchurUpdate () 2 1 2 0 0 0 0 0 0) [(#[10, 30, 20, 40]).map some]
#guard blockMatches blockAliasAll 0 [-90, -270, -280, -860] 1

private def blockOffsets := blockRun (floatInterp #[] [])
  (blockSchurUpdate () 2 1 2 0 1 2 1 1 2)
  [(#[101, 1, 2, 909]).map some, (#[303, 3, 4, 909]).map some,
    (#[101, 303, 10, 30, 20, 40, 909]).map some]
#guard blockMatches blockOffsets 2 [101, 303, 7, 24, 16, 32, 909] 3
#guard blockMatches
  (blockRun copyOnlyBlocks (blockSchurUpdate () 2 0 2 17 23 0 9 11 0)
    [(#[10, 30, 20, 40]).map some]) 0 [10, 30, 20, 40] 1
#guard (blockRun copyOnlyBlocks (blockSchurUpdate () 2 0 3 17 23 29 9 11 13) []).isSome
#guard blockMatches
  (blockRun (floatInterp #[] []) (blockSchurUpdate () 0 2 2 1 0 1 11 0 13)
    [(#[1, 2, 3, 4]).map some]) 0 [1, 2, 3, 4] 1
#guard (blockRun (floatInterp #[] []) (blockSchurUpdate () 2 2 0 17 23 29 9 11 13) []).isSome
#guard (blockRun (floatInterp #[] []) (blockSchurUpdate () 1 1 1 0 1 2 0 0 0)
  [#[some 1], #[some 2], #[none]]).isNone

end NLAlibTools
