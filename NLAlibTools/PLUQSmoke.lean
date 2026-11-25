/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.PLUQ
import NLAlib.Matrix.Computation.PLUQRounding

/-!
# Runtime checks for stored complete-pivoted LU

The actual `pluqFactor` runs under the tool Float interpreter with bounded dynamic-index
conversion. Both recorded current-position logs are replayed independently, and the computed
factor product is compared with the input permuted along both axes. Every factor and log cell
must be initialized. Examples cover stable column-major ties, singular inputs, moving already
committed upper rows during later column swaps, offsets, frames and released scratch.
These small finite regressions do not assert a formal Float arithmetic or range contract.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev PLUQState := St Unit Float (ℕ × ℕ × ℕ)

private def runPLUQWith (I : Interp Unit Unit Float (ℕ × ℕ × ℕ))
    (n A L U Hr Hc ao lo uo hro hco : ℕ)
    (buffers : List (Array (Option Float))) : Option PLUQState :=
  exec I
    (pluqFactor () (.const n) A L U Hr Hc
      (.const ao) (.const lo) (.const uo) (.const hro) (.const hco)).run
    (initState buffers)

private def runPLUQ (n A L U Hr Hc ao lo uo hro hco : ℕ)
    (buffers : List (Array (Option Float))) : Option PLUQState :=
  runPLUQWith (floatIndexedInterp #[] []) n A L U Hr Hc ao lo uo hro hco buffers

private def packRows (rows : Array (Array Float)) : Array Float :=
  let n := rows.size
  (List.range (n * n)).toArray.map fun t => (rows[t % n]!)[t / n]!

private def readCells (st : PLUQState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

-- This decoder uses only the ACTUAL recorded words, never either library permutation decoder.
-- Each log entry names an absolute current position. Fractional, out-of-range and past-prefix
-- positions are rejected before applying the swap to an independently maintained order array.
private def replayLog (n : ℕ) (history : Array Float) : Option (Array ℕ) := do
  if history.size != n then none else
    (List.range n).foldlM (fun order k => do
      let word ← history[k]?
      let position ← boundedFloatToNat word
      if position < n && k ≤ position && word == Float.ofNat position then
        let oldK ← order[k]?
        let oldPosition ← order[position]?
        some ((order.set! k oldPosition).set! position oldK)
      else none) (List.range n).toArray

private def residualAt (n : ℕ) (A L U : Array Float) (rowOrder colOrder : Array ℕ)
    (t : ℕ) : Float × Float :=
  let i := t % n
  let j := t / n
  let product := (List.range n).foldl
    (fun acc k => acc + L[i + n * k]! * U[k + n * j]!) 0
  let weight := (List.range n).foldl
    (fun acc k => acc + L[i + n * k]!.abs * U[k + n * j]!.abs) 0
  ((product - A[rowOrder[i]! + n * colOrder[j]!]!).abs, weight)

private def validFactorsWith (n : ℕ) (A L U rowLog colLog : Array Float)
    (multiplierBound : Float) (residualBound : Float → Float) : Bool :=
  match replayLog n rowLog, replayLog n colLog with
  | some rowOrder, some colOrder =>
    A.size == n * n && L.size == n * n && U.size == n * n &&
      (List.range n).all (fun i => rowOrder.toList.count i == 1) &&
      (List.range n).all (fun i => colOrder.toList.count i == 1) &&
      L.all Float.isFinite && U.all Float.isFinite &&
      (List.range n).all (fun i => L[i + n * i]! == 1) &&
      (List.range (n * n)).all fun t =>
        let i := t % n
        let j := t / n
        let residual := residualAt n A L U rowOrder colOrder t
        residual.1 ≤ residualBound residual.2 &&
          (if i < j then L[t]! == 0 else true) &&
          (if j < i then U[t]! == 0 else true) && L[t]!.abs ≤ multiplierBound
  | _, _ => false

private def validFactors (n : ℕ) (A L U rowLog colLog : Array Float) : Bool :=
  validFactorsWith n A L U rowLog colLog 1.0000000001 (fun _ => 1e-10)

private def checkRun (n : ℕ) (A : Array Float) (result : Option PLUQState)
    (lo uo hro hco buffers : ℕ) : Bool :=
  match result with
  | none => false
  | some st =>
    match readCells st 1 lo (n * n), readCells st 2 uo (n * n),
        readCells st 3 hro n, readCells st 4 hco n with
    | some L, some U, some rowLog, some colLog =>
      st.store.size == buffers && validFactors n A L U rowLog colLog
    | _, _, _, _ => false

private def logMatches (result : Option PLUQState) (b off : ℕ) (expected : Array Float) : Bool :=
  result.any fun st => readCells st b off expected.size == some expected

private def orderMatches (result : Option PLUQState) (b n off : ℕ) (expected : Array ℕ) : Bool :=
  result.any fun st =>
    ((readCells st b off n).bind (replayLog n)).any fun order => order == expected

private def rowMatches (result : Option PLUQState) (n off row : ℕ)
    (expected : Array Float) : Bool :=
  result.any fun st => expected.size == n && (List.range n).all fun j =>
    st.store.read () 2 (off + row + n * j) == expected[j]?

private def scopeRestored (result : Option PLUQState)
    (buffers : List (Array (Option Float))) : Bool :=
  result.any fun st => st.store.shape == (initState buffers).store.shape &&
    st.cur () == (initState buffers).cur () && st.curW == (initState buffers).curW &&
    st.pos .gaussian == 0 && st.pos .rademacher == 0 && st.pos .uniform == 0

private def standardBuffers (n : ℕ) (A : Array Float) : List (Array (Option Float)) :=
  [A.map some, Array.replicate (n * n) none, Array.replicate (n * n) none,
    Array.replicate n none, Array.replicate n none, #[some 701, some 709]]

private def standardRun (n : ℕ) (A : Array Float) : Option PLUQState :=
  runPLUQ n 0 1 2 3 4 0 0 0 0 0 (standardBuffers n A)

private def checkStandard (n : ℕ) (A : Array Float) (result : Option PLUQState) : Bool :=
  checkRun n A result 0 0 0 0 6 && scopeRestored result (standardBuffers n A) &&
    result.any fun st => readCells st 0 0 A.size == some A &&
      readCells st 5 0 2 == some #[701, 709]

-- Decoder sanity checks reject malformed actual logs independently of factorization.
#guard replayLog 3 #[2, 2, 2] == some #[2, 0, 1]
#guard replayLog 4 #[3, 2, 3, 3] == some #[3, 2, 0, 1]
#guard (replayLog 2 #[2, 1]).isNone
#guard (replayLog 2 #[0, 0]).isNone
#guard (replayLog 2 #[0.5, 1]).isNone
#guard (replayLog 2 #[-1, 1]).isNone

-- The late column exchange must move the ALREADY COMMITTED first upper row.
private def dense := packRows #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]
private def denseRun := standardRun 3 dense
#guard checkStandard 3 dense denseRun
#guard logMatches denseRun 3 0 #[2, 2, 2]
#guard logMatches denseRun 4 0 #[2, 2, 2]
#guard orderMatches denseRun 3 3 0 #[2, 0, 1]
#guard orderMatches denseRun 4 3 0 #[2, 0, 1]
#guard rowMatches denseRun 3 0 0 #[9, 7, 8]

-- Different final row and column orders catch accidentally decoding or applying one log twice.
private def asymmetric := packRows #[#[0, 1, 2], #[3, 4, 12], #[5, 6, 7]]
private def asymmetricRun := standardRun 3 asymmetric
#guard checkStandard 3 asymmetric asymmetricRun
#guard logMatches asymmetricRun 3 0 #[1, 2, 2]
#guard logMatches asymmetricRun 4 0 #[2, 1, 2]
#guard orderMatches asymmetricRun 3 3 0 #[1, 2, 0]
#guard orderMatches asymmetricRun 4 3 0 #[2, 1, 0]
#guard asymmetricRun.any fun st =>
  ((readCells st 3 0 3).bind (replayLog 3)) != ((readCells st 4 0 3).bind (replayLog 3))

-- A third pivot exchanges columns after TWO upper rows have been committed. Both must move.
private def four := packRows
  #[#[1, 2, 3, 4], #[5, 6, 7, 8], #[9, 10, 11, 12], #[13, 14, 15, 32]]
private def fourRun := standardRun 4 four
#guard checkStandard 4 four fourRun
#guard logMatches fourRun 3 0 #[3, 2, 3, 3]
#guard logMatches fourRun 4 0 #[3, 2, 3, 3]
#guard orderMatches fourRun 3 4 0 #[3, 2, 0, 1]
#guard orderMatches fourRun 4 4 0 #[3, 2, 0, 1]
#guard rowMatches fourRun 4 0 0 #[32, 15, 13, 14]
#guard fourRun.any fun st => st.store.read () 2 (1 + 4 * 2) == some 4.125 &&
  st.store.read () 2 (1 + 4 * 3) == some 4.75

-- Stable tie order is column-major: the positive 9 in column zero precedes negative −9.
private def signedTie := packRows #[#[1, -9], #[9, 2]]
private def signedTieRun := standardRun 2 signedTie
#guard checkStandard 2 signedTie signedTieRun
#guard logMatches signedTieRun 3 0 #[1, 1]
#guard logMatches signedTieRun 4 0 #[0, 1]
#guard rowMatches signedTieRun 2 0 0 #[9, 2]

-- All-zero active blocks are legal, including after a nonzero pivot and exact dyadic rank-one
-- cancellation. Structural zeros must be actual initialized cells, rather than default reads.
private def allZero := Array.replicate 9 (0 : Float)
private def allZeroRun := standardRun 3 allZero
#guard checkStandard 3 allZero allZeroRun
#guard logMatches allZeroRun 3 0 #[0, 1, 2]
#guard logMatches allZeroRun 4 0 #[0, 1, 2]
private def zeroActive := packRows #[#[8, 0, 0], #[0, 0, 0], #[0, 0, 0]]
private def zeroActiveRun := standardRun 3 zeroActive
#guard checkStandard 3 zeroActive zeroActiveRun
#guard logMatches zeroActiveRun 3 0 #[0, 1, 2]
#guard logMatches zeroActiveRun 4 0 #[0, 1, 2]
private def rankOne := packRows #[#[1, 2, 4], #[2, 4, 8], #[4, 8, 16]]
private def rankOneRun := standardRun 3 rankOne
#guard checkStandard 3 rankOne rankOneRun
#guard logMatches rankOneRun 3 0 #[2, 1, 2]
#guard logMatches rankOneRun 4 0 #[2, 1, 2]

private def singletonPositive := standardRun 1 #[7]
#guard checkStandard 1 #[7] singletonPositive
#guard logMatches singletonPositive 3 0 #[0]
#guard logMatches singletonPositive 4 0 #[0]
private def singletonNegative := standardRun 1 #[-7]
#guard checkStandard 1 #[-7] singletonNegative
#guard logMatches singletonNegative 3 0 #[0]
#guard logMatches singletonNegative 4 0 #[0]
private def singletonZero := standardRun 1 #[0]
#guard checkStandard 1 #[0] singletonZero
#guard logMatches singletonZero 3 0 #[0]
#guard logMatches singletonZero 4 0 #[0]

-- Distinct nonzero offsets and sentinels surround all FOUR output windows. Input and unrelated
-- buffers remain exact, and all scratch allocation is released before the routine returns.
private def offsetBuffers : List (Array (Option Float)) :=
  [(#[101] ++ asymmetric ++ #[109]).map some,
    #[some 201, some 203] ++ Array.replicate 9 none ++ #[some 209],
    #[some 301] ++ Array.replicate 9 none ++ #[some 309],
    #[some 401, some 403, some 407] ++ Array.replicate 3 none ++ #[some 409],
    #[some 501, some 503, some 507, some 509] ++ Array.replicate 3 none ++ #[some 521],
    #[some 701, some 709]]
private def offsetsRun := runPLUQ 3 0 1 2 3 4 1 2 1 3 4 offsetBuffers
#guard checkRun 3 asymmetric offsetsRun 2 1 3 4 6
#guard logMatches offsetsRun 3 3 #[1, 2, 2]
#guard logMatches offsetsRun 4 4 #[2, 1, 2]
#guard orderMatches offsetsRun 3 3 3 #[1, 2, 0]
#guard orderMatches offsetsRun 4 3 4 #[2, 1, 0]
#guard offsetsRun.any fun st =>
  readCells st 0 0 11 == some (#[101] ++ asymmetric ++ #[109]) &&
    st.store.read () 1 0 == some 201 && st.store.read () 1 1 == some 203 &&
    st.store.read () 1 11 == some 209 && st.store.read () 2 0 == some 301 &&
    st.store.read () 2 10 == some 309 && st.store.read () 3 0 == some 401 &&
    st.store.read () 3 1 == some 403 && st.store.read () 3 2 == some 407 &&
    st.store.read () 3 6 == some 409 && st.store.read () 4 0 == some 501 &&
    st.store.read () 4 1 == some 503 && st.store.read () 4 2 == some 507 &&
    st.store.read () 4 3 == some 509 && st.store.read () 4 7 == some 521 &&
    readCells st 5 0 2 == some #[701, 709]
#guard scopeRestored offsetsRun offsetBuffers

-- Invalid distinct handles and offsets require no phantom capacities in dimension zero.
private def emptyRun := runPLUQ 0 17 23 29 31 37 9 11 13 15 17 []
#guard scopeRestored emptyRun []
#guard emptyRun.any fun st => st.store.size == 0 && st.cur () == 0 && st.curW == 0

-- Artificial relative perturbations exercise nonzero backward error on the actual driver.
-- Index controls, comparisons, copies, signs and literals remain exact. These finite examples
-- are regressions, not a proof that this Float interpreter satisfies the abstract scalar model.
private def perturbedInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  let original := floatIndexedInterp #[] []
  { original with sem := { original.sem with
      bin := fun tag op x y => (original.sem.bin tag op x y).map (fun z => z * 1.001) } }

private def roundedRun (n : ℕ) (A : Array Float) : Option PLUQState :=
  runPLUQWith perturbedInterp n 0 1 2 3 4 0 0 0 0 0 (standardBuffers n A)

private def roundedBudget (n : ℕ) : Float :=
  1 / (List.range (n + 4)).foldl (fun product _ => product * 0.999) 1 - 1

private def checkRounded (n : ℕ) (A : Array Float) (result : Option PLUQState) : Bool :=
  scopeRestored result (standardBuffers n A) && result.any fun st =>
    readCells st 0 0 A.size == some A && readCells st 5 0 2 == some #[701, 709] &&
      match readCells st 1 0 (n * n), readCells st 2 0 (n * n),
          readCells st 3 0 n, readCells st 4 0 n with
      | some L, some U, some rowLog, some colLog =>
        validFactorsWith n A L U rowLog colLog 1.0010000001
          (fun weight => roundedBudget n * weight + 1e-10)
      | _, _, _, _ => false

private def nonzeroResidual (n : ℕ) (A : Array Float) (result : Option PLUQState) : Bool :=
  result.any fun st =>
    match readCells st 1 0 (n * n), readCells st 2 0 (n * n),
        readCells st 3 0 n, readCells st 4 0 n with
    | some L, some U, some rowLog, some colLog =>
      match replayLog n rowLog, replayLog n colLog with
      | some rows, some cols =>
        (List.range (n * n)).any fun t => (residualAt n A L U rows cols t).1 > 1e-5
      | _, _ => false
    | _, _, _, _ => false

private def perturbedAsymmetric := roundedRun 3 asymmetric
#guard checkRounded 3 asymmetric perturbedAsymmetric
#guard nonzeroResidual 3 asymmetric perturbedAsymmetric
#guard logMatches perturbedAsymmetric 3 0 #[1, 2, 2]
#guard logMatches perturbedAsymmetric 4 0 #[2, 1, 2]
#guard orderMatches perturbedAsymmetric 3 3 0 #[1, 2, 0]
#guard orderMatches perturbedAsymmetric 4 3 0 #[2, 1, 0]
#guard checkRounded 3 dense (roundedRun 3 dense)
#guard checkRounded 3 rankOne (roundedRun 3 rankOne)
#guard checkRounded 3 zeroActive (roundedRun 3 zeroActive)
#guard checkRounded 3 allZero (roundedRun 3 allZero)
#guard checkRounded 1 #[-7] (roundedRun 1 #[-7])
#guard checkRounded 1 #[0] (roundedRun 1 #[0])
#guard checkRounded 0 #[] (roundedRun 0 #[])

-- Reject every division. The complete all-zero factorization must execute only zero-safe
-- branches and still produce initialized factors and both actual log arrays.
private def rejectDivisionInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  let original := floatIndexedInterp #[] []
  { original with sem := { original.sem with
      bin := fun tag op x y => match op with
        | .div => none
        | _ => original.sem.bin tag op x y } }
private def rejectDivisionRun :=
  runPLUQWith rejectDivisionInterp 3 0 1 2 3 4 0 0 0 0 0 (standardBuffers 3 allZero)
#guard checkStandard 3 allZero rejectDivisionRun
#guard logMatches rejectDivisionRun 3 0 #[0, 1, 2]
#guard logMatches rejectDivisionRun 4 0 #[0, 1, 2]

end NLAlibTools
