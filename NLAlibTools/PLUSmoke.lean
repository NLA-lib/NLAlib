/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.PLU
import NLAlib.Matrix.Computation.GuardedElimination

/-!
# Runtime checks for stored partial-pivoted LU

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
    (pluFactor () (.const n) A L U H (.const ao) (.const lo) (.const uo) (.const ho)).run
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
          (if j < i then U[t]! == 0 else true) && L[t]!.abs ≤ 1.0000000001

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

-- Decoder sanity checks are independent of factorization execution and reject malformed logs.
#guard replayLog 4 #[1, 2, 3, 3] == some #[1, 2, 3, 0]
#guard replayLog 3 #[0, 1, 2] == some #[0, 1, 2]
#guard (replayLog 2 #[2, 1]).isNone
#guard (replayLog 2 #[0, 0]).isNone
#guard (replayLog 2 #[0.5, 1]).isNone

private def firstSwap := packRows #[#[0, 1], #[2, 3]]
private def firstSwapRun := standardRun 2 firstSwap
#guard checkRun 2 firstSwap firstSwapRun 0 0 0 5
#guard logMatches firstSwapRun 0 #[1, 1]
#guard orderMatches firstSwapRun 2 0 #[1, 0]

private def negativePivot := packRows #[#[1, 3], #[-8, 2]]
private def negativePivotRun := standardRun 2 negativePivot
#guard checkRun 2 negativePivot negativePivotRun 0 0 0 5
#guard logMatches negativePivotRun 0 #[1, 1]

-- A four-cycle requires three distinct exchanges. Reversing the decoder's composition order
-- produces the wrong input permutation here, even though a single-swap test would pass.
private def cycle := packRows #[#[0, 0, 0, 1], #[1, 0, 0, 0], #[0, 1, 0, 0], #[0, 0, 1, 0]]
private def cycleRun := standardRun 4 cycle
#guard checkRun 4 cycle cycleRun 0 0 0 5
#guard logMatches cycleRun 0 #[1, 2, 3, 3]
#guard orderMatches cycleRun 4 0 #[1, 2, 3, 0]

-- The second exchange must also swap the distinct, nonzero multipliers already committed in
-- the first lower-factor column. Permutation matrices alone would not detect that mistake.
private def denseSwaps := packRows #[#[2, 0, 1], #[1, 1, 2], #[4, 2, 3]]
private def denseSwapsRun := standardRun 3 denseSwaps
#guard checkRun 3 denseSwaps denseSwapsRun 0 0 0 5
#guard logMatches denseSwapsRun 0 #[2, 2, 2]
#guard orderMatches denseSwapsRun 3 0 #[2, 0, 1]

-- Equal magnitudes with opposite signs choose the first eligible position, at both the first
-- pivot and a later active suffix.
private def firstTie := packRows #[#[-2, 0, 1], #[2, 3, 0], #[1, 1, 4]]
private def firstTieRun := standardRun 3 firstTie
#guard checkRun 3 firstTie firstTieRun 0 0 0 5
#guard logMatches firstTieRun 0 #[0, 1, 2]
private def laterTie := packRows #[#[1, 0, 0], #[0, -4, 2], #[0, 4, 3]]
private def laterTieRun := standardRun 3 laterTie
#guard checkRun 3 laterTie laterTieRun 0 0 0 5
#guard logMatches laterTieRun 0 #[0, 1, 2]

-- A zero first active column does not imply a zero pivot row. Later pivots must still process
-- that matrix correctly; a proof or implementation assuming all earlier rows are cleared fails.
private def zeroFirst := packRows #[#[0, 2, 1], #[0, 0, 3], #[0, 4, 2]]
private def zeroFirstRun := standardRun 3 zeroFirst
#guard checkRun 3 zeroFirst zeroFirstRun 0 0 0 5
#guard logMatches zeroFirstRun 0 #[0, 2, 2]

private def zeroMiddle := packRows #[#[2, 4, 1], #[1, 2, 3], #[0, 0, 5]]
private def zeroMiddleRun := standardRun 3 zeroMiddle
#guard checkRun 3 zeroMiddle zeroMiddleRun 0 0 0 5
#guard logMatches zeroMiddleRun 0 #[0, 1, 2]

-- Dyadic multiples make the rank-one cancellation exact in binary64, exercising two guarded
-- zero Schur pivots after a nontrivial initial swap.
private def rankOne := packRows #[#[1, 2, 4], #[2, 4, 8], #[4, 8, 16]]
private def rankOneRun := standardRun 3 rankOne
#guard checkRun 3 rankOne rankOneRun 0 0 0 5
#guard logMatches rankOneRun 0 #[2, 1, 2]
private def allZeroRun := standardRun 3 (Array.replicate 9 0)
#guard checkRun 3 (Array.replicate 9 0) allZeroRun 0 0 0 5
#guard logMatches allZeroRun 0 #[0, 1, 2]

private def singletonRun := standardRun 1 #[-7]
#guard checkRun 1 #[-7] singletonRun 0 0 0 5
#guard logMatches singletonRun 0 #[0]
private def singletonZeroRun := standardRun 1 #[0]
#guard checkRun 1 #[0] singletonZeroRun 0 0 0 5
#guard logMatches singletonZeroRun 0 #[0]

private def offsetBuffers : List (Array (Option Float)) :=
  [((#[101] ++ zeroFirst ++ #[109]).map some),
    #[some 201, some 203] ++ Array.replicate 9 none ++ #[some 209],
    #[some 301] ++ Array.replicate 9 none ++ #[some 309],
    #[some 401, some 403, some 407] ++ Array.replicate 3 none ++ #[some 409],
    #[some 701, some 709]]
private def offsetsRun := runPLU 3 0 1 2 3 1 2 1 3 offsetBuffers
#guard checkRun 3 zeroFirst offsetsRun 2 1 3 5
#guard logMatches offsetsRun 3 #[0, 2, 2]
#guard offsetsRun.any fun st =>
  (readCells st 0 0 11).any (fun source => closeArray source (#[101] ++ zeroFirst ++ #[109])) &&
    st.store.read () 1 0 == some 201 && st.store.read () 1 1 == some 203 &&
    st.store.read () 1 11 == some 209 && st.store.read () 2 0 == some 301 &&
    st.store.read () 2 10 == some 309 && st.store.read () 3 0 == some 401 &&
    st.store.read () 3 1 == some 403 && st.store.read () 3 2 == some 407 &&
    st.store.read () 3 6 == some 409 && st.store.read () 4 0 == some 701 &&
    st.store.read () 4 1 == some 709
#guard offsetsRun.any fun st =>
  st.cur () == (initState offsetBuffers).cur () && st.curW == (initState offsetBuffers).curW &&
    st.pos .gaussian == 0 && st.pos .rademacher == 0 && st.pos .uniform == 0

-- No matrix, factor or history entry exists at dimension zero. Deliberately invalid handles
-- and offsets verify that empty writes and loops impose no phantom capacity requirement.
private def emptyRun := runPLU 0 17 23 29 31 9 11 13 15 []
#guard emptyRun.any fun st => st.store.size == 0 && st.cur () == 0 && st.curW == 0

-- Reject EVERY division, not just division by zero. The zero guards must still succeed on
-- a matrix with a zero diagonal and a nonzero entry below it. This tests the guard itself;
-- this matrix is not claimed to be an admissible unpivoted LU factorization input.
private def noDivisionInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { pluFloatInterp with
    sem := { pluFloatInterp.sem with
      bin := fun p op x y => match op with
        | .div => none
        | _ => floatSem.bin p op x y } }

private def zeroGuardBuffers : List (Array (Option Float)) :=
  [(#[101, 0, 7, 2, 3, 109]).map some, (#[201, 99, 98, 97, 96, 209]).map some,
    (#[301, 88, 87, 86, 85, 309]).map some, (#[701, 709]).map some]
private def zeroGuardColumn := exec noDivisionInterp
  (luColumnTotal () 2 0 0 1 2 1 1 1).run (initState zeroGuardBuffers)
#guard zeroGuardColumn.any fun st =>
  st.store.size == 4 &&
    (readCells st 0 0 6).any (fun a => closeArray a #[101, 0, 7, 2, 3, 109]) &&
    (readCells st 1 0 6).any (fun a => closeArray a #[201, 1, 0, 97, 96, 209]) &&
    (readCells st 2 0 6).any (fun a => closeArray a #[301, 0, 87, 2, 85, 309]) &&
    (readCells st 3 0 2).any (fun a => closeArray a #[701, 709])
private def zeroGuardSchur := exec noDivisionInterp
  (schurStepTotal () 2 0 1 0).run (initState zeroGuardBuffers)
#guard zeroGuardSchur.any fun st => st.store == (initState zeroGuardBuffers).store

-- The rejected-division interpretation really detects the nonzero branch's division.
#guard (exec noDivisionInterp (schurStepTotal () 2 0 0 0).run
  (initState [(#[2, 7, 2, 3]).map some])).isNone
#guard (exec noDivisionInterp (luColumnTotal () 2 0 0 1 2 0 0 0).run
  (initState [(#[2, 7, 2, 3]).map some, Array.replicate 4 (some 0),
    Array.replicate 4 (some 0)])).isNone

end NLAlibTools
