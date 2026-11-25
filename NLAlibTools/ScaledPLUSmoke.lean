/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.ScaledPLU
import NLAlib.Matrix.Computation.GuardedElimination

/-!
# Runtime checks for fixed-scale pivoted LU

These tests execute the actual stored factorization under the tool Float interpreter. They
independently replay the recorded row-position swaps and multiply the computed factors to
check the permuted input. Every output cell is read as an option so uninitialized zeros cannot
pass a factor or pivot-log check. These examples are regression evidence, not a theorem about
floating-point error or the tool interpreter's contracts.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev PLUState := St Unit Float (ℕ × ℕ × ℕ)

-- Dynamic index binders require a tool conversion. Reject nonfinite, negative and excessively
-- large words before converting, within binary64's exact-integer range. Test dimensions are
-- tiny. This shim executes the binder; it does not prove any accuracy contract for Float.
private def pluFloatInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  floatIndexedInterp #[] []

private def runPLU (n A L U H ao lo uo ho : ℕ)
    (buffers : List (Array (Option Float))) : Option PLUState :=
  exec pluFloatInterp
    (scaledPluFactor () (.const n) A L U H (.const ao) (.const lo) (.const uo) (.const ho)).run
    (initState buffers)

private def packRows (rows : Array (Array Float)) : Array Float :=
  let n := rows.size
  (List.range (n * n)).toArray.map fun t => (rows[t % n]!)[t / n]!

private def readCells (st : PLUState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

-- Replay the actual log without calling the library's luPivotPermutation decoder. Each entry
-- names an absolute CURRENT row position, not an original matrix row number.
private def replayLog (n : ℕ) (history : Array Float) : Option (Array ℕ) := do
  if history.size != n then none else
    (List.range n).foldlM (fun order k => do
      let word ← history[k]?
      if word.isFinite && decide (0 ≤ word) && decide (word ≤ 9007199254740992) then
        let row := word.toUInt64.toNat
        if row < n && k ≤ row && word == Float.ofNat row then
          let oldK ← order[k]?
          let oldRow ← order[row]?
          some ((order.set! k oldRow).set! row oldK)
        else none
      else none) (List.range n).toArray

private def closeArray (actual expected : Array Float) : Bool :=
  actual.size == expected.size && (List.range actual.size).all fun i =>
    actual[i]!.isFinite && (actual[i]! - expected[i]!).abs ≤ 1e-10

private def validFactors (n : ℕ) (A L U : Array Float) (history : Array Float) : Bool :=
  match replayLog n history with
  | none => false
  | some order =>
    A.size == n * n && L.size == n * n && U.size == n * n &&
      (List.range n).all (fun i => order.toList.count i == 1) &&
      L.all Float.isFinite && U.all Float.isFinite &&
      (List.range n).all (fun i => L[i + n * i]! == 1) &&
      (List.range (n * n)).all fun t =>
        let i := t % n
        let j := t / n
        let product := (List.range n).foldl
          (fun acc k => acc + L[i + n * k]! * U[k + n * j]!) 0
        let expected := A[order[i]! + n * j]!
        (product - expected).abs ≤ 1e-10 &&
          (if i < j then L[t]! == 0 else true) &&
          (if j < i then U[t]! == 0 else true)

private def checkRun (n : ℕ) (A : Array Float) (result : Option PLUState)
    (lo uo ho : ℕ) (buffers : ℕ) : Bool :=
  match result with
  | none => false
  | some st =>
    match readCells st 1 lo (n * n), readCells st 2 uo (n * n), readCells st 3 ho n with
    | some L, some U, some history => st.store.size == buffers && validFactors n A L U history
    | _, _, _ => false

private def logMatches (result : Option PLUState) (off : ℕ) (expected : Array Float) : Bool :=
  match result with
  | none => false
  | some st => (readCells st 3 off expected.size).any fun history => closeArray history expected

private def orderMatches (result : Option PLUState) (n off : ℕ) (expected : Array ℕ) : Bool :=
  match result with
  | none => false
  | some st => ((readCells st 3 off n).bind (replayLog n)).any fun order => order == expected

private def standardRun (n : ℕ) (A : Array Float) : Option PLUState :=
  runPLU n 0 1 2 3 0 0 0 0 [A.map some, Array.replicate (n * n) none,
    Array.replicate (n * n) none, Array.replicate n none, #[some 701, some 709]]

-- Raw column magnitudes prefer row 0; fixed original scales prefer row 1. The lower
-- multiplier becomes two, deliberately exercising the absence of an unweighted bound.
private def differs := packRows #[#[4, 100], #[2, 2]]
private def differsRun := standardRun 2 differs
#guard checkRun 2 differs differsRun 0 0 0 5
#guard logMatches differsRun 0 #[1, 1]
#guard orderMatches differsRun 2 0 #[1, 0]
#guard differsRun.any fun st => st.store.read () 1 1 == some 2

-- Original scales follow both row exchanges. They are never recomputed from the active rows.
private def scalesFollow := packRows #[#[1, 20, 3], #[8, 8, 4], #[2, 1, 2]]
private def scalesFollowRun := standardRun 3 scalesFollow
#guard checkRun 3 scalesFollow scalesFollowRun 0 0 0 5
#guard logMatches scalesFollowRun 0 #[1, 1, 2]

-- Recomputing active row scales would choose row 2 at the second step. Fixed initial
-- scales choose row 1, with separated ratios 7/13 and 22/65.
private def fixedScales := packRows #[#[13, 6, 3], #[1, 1, 1], #[5, 4, 1]]
private def fixedScalesRun := standardRun 3 fixedScales
#guard checkRun 3 fixedScales fixedScalesRun 0 0 0 5
#guard logMatches fixedScalesRun 0 #[0, 1, 2]

private def zeroRows := packRows #[#[0, 0, 0], #[1, 2, 4], #[2, 4, 8]]
private def zeroRowsRun := standardRun 3 zeroRows
#guard checkRun 3 zeroRows zeroRowsRun 0 0 0 5
#guard logMatches zeroRowsRun 0 #[1, 1, 2]
private def zeroColumn := packRows #[#[0, 2, 1], #[0, 0, 3], #[0, 4, 2]]
private def zeroColumnRun := standardRun 3 zeroColumn
#guard checkRun 3 zeroColumn zeroColumnRun 0 0 0 5
#guard logMatches zeroColumnRun 0 #[0, 2, 2]
private def allZeroRun := standardRun 3 (Array.replicate 9 0)
#guard checkRun 3 (Array.replicate 9 0) allZeroRun 0 0 0 5
#guard logMatches allZeroRun 0 #[0, 1, 2]

-- Equal scaled ratios retain the first row even when raw magnitudes differ.
private def tie := packRows #[#[1, 2], #[-4, 8]]
private def tieRun := standardRun 2 tie
#guard checkRun 2 tie tieRun 0 0 0 5
#guard logMatches tieRun 0 #[0, 1]
#guard checkRun 1 #[-7] (standardRun 1 #[-7]) 0 0 0 5
#guard checkRun 1 #[0] (standardRun 1 #[0]) 0 0 0 5

private def offsetBuffers : List (Array (Option Float)) :=
  [((#[101] ++ differs ++ #[109]).map some),
    #[some 201, some 203] ++ Array.replicate 4 none ++ #[some 209],
    #[some 301] ++ Array.replicate 4 none ++ #[some 309],
    #[some 401, some 403, some 407] ++ Array.replicate 2 none ++ #[some 409],
    #[some 701, some 709]]
private def offsetsRun := runPLU 2 0 1 2 3 1 2 1 3 offsetBuffers
#guard checkRun 2 differs offsetsRun 2 1 3 5
#guard logMatches offsetsRun 3 #[1, 1]
#guard offsetsRun.any fun st =>
  (readCells st 0 0 6).any (fun source => closeArray source (#[101] ++ differs ++ #[109])) &&
    st.store.read () 1 0 == some 201 && st.store.read () 1 1 == some 203 &&
    st.store.read () 1 6 == some 209 && st.store.read () 2 0 == some 301 &&
    st.store.read () 2 5 == some 309 && st.store.read () 3 0 == some 401 &&
    st.store.read () 3 1 == some 403 && st.store.read () 3 2 == some 407 &&
    st.store.read () 3 5 == some 409 && st.store.read () 4 0 == some 701 &&
    st.store.read () 4 1 == some 709
#guard offsetsRun.any fun st =>
  st.cur () == (initState offsetBuffers).cur () && st.curW == (initState offsetBuffers).curW &&
    st.pos .gaussian == 0 && st.pos .rademacher == 0 && st.pos .uniform == 0

-- Every matrix and scale window inside the driver uses the same scoped buffer. Dimension
-- zero deliberately passes invalid distinct handles, checking absence of phantom capacity.
private def emptyRun := runPLU 0 17 23 29 31 9 11 13 15 []
#guard emptyRun.any fun st => st.store.size == 0 && st.cur () == 0 && st.curW == 0

end NLAlibTools
