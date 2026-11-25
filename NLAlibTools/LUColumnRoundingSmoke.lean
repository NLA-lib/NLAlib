/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.GuardedElimination

/-!
# Executable checks for rounded LU columns

These run the unchanged LU column builders with biased divisions and exact structural/index
literals. Complete initialized outputs and outside-cell frames are checked independently.
A backend rejecting every division distinguishes guarded zero pivots from actual nonzero
quotient instructions. These finite examples make no universal Float-model claim.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev ColumnState := St Unit Float (ℕ × ℕ × ℕ)

private def divisionBias : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := { floatSem with
      toNat := fun _ => boundedFloatToNat
      bin := fun p op x y => match op with
        | .div => (floatSem.bin p op x y).map fun z => z * 1.001
        | _ => floatSem.bin p op x y } }

private def rejectDivision : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { divisionBias with sem := { divisionBias.sem with
      bin := fun p op x y => match op with
        | .div => none
        | _ => floatSem.bin p op x y } }

private def packRows (rows : Array (Array Float)) : Array Float :=
  let n := rows.size
  (List.range (n * n)).toArray.map fun t => (rows[t % n]!)[t / n]!

private def inputBuffers (n : ℕ) (M : Array Float) : List (Array (Option Float)) :=
  [#[some 101] ++ M.map some ++ #[some 109],
    #[some 201, some 203] ++ Array.replicate (n * n) (some 99) ++ #[some 209],
    #[some 301] ++ Array.replicate (n * n) (some 88) ++ #[some 309],
    #[some 701, none, some 709]]

private def runColumn (total : Bool) (I : Interp Unit Unit Float (ℕ × ℕ × ℕ))
    (n k : ℕ) (M : Array Float) : Option ColumnState :=
  let routine := if total then luColumnTotal () (.const n) (.const k) 0 1 2 1 2 1
    else luColumn () (.const n) (.const k) 0 1 2 1 2 1
  exec I routine.run (initState (inputBuffers n M))

private def readCells (st : ColumnState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def closeArray (actual expected : Array Float) : Bool :=
  actual.size == expected.size && (List.range actual.size).all fun i =>
    actual[i]!.isFinite && (actual[i]! - expected[i]!).abs ≤ 1e-12

private def expectedLower (total : Bool) (n k : ℕ) (M : Array Float) : Array Float :=
  (List.range (n * n)).toArray.map fun t =>
    let i := t % n
    let j := t / n
    if j != k then 99 else
      if i < k then 0 else if i == k then 1 else
        if total && M[k + n * k]! == 0 then 0 else M[i + n * k]! / M[k + n * k]! * 1.001

private def expectedUpper (n k : ℕ) (M : Array Float) : Array Float :=
  (List.range (n * n)).toArray.map fun t =>
    let i := t % n
    let j := t / n
    if i != k then 88 else if j < k then 0 else M[k + n * j]!

private def frameOK (before after : ColumnState) (n k : ℕ) : Bool :=
  before.store.size == after.store.size && before.store.shape == after.store.shape &&
    before.cur () == after.cur () && before.curW == after.curW &&
    before.pos .gaussian == after.pos .gaussian &&
    before.pos .rademacher == after.pos .rademacher &&
    before.pos .uniform == after.pos .uniform &&
    (List.range before.store.size).all fun b =>
      (List.range ((before.store[b]!).2.size)).all fun j =>
        if (b == 1 && 2 ≤ j && j < 2 + n * n && (j - 2) / n == k) ||
            (b == 2 && 1 ≤ j && j < 1 + n * n && (j - 1) % n == k) then true
        else after.store.read () b j == before.store.read () b j

private def checkColumn (total : Bool) (I : Interp Unit Unit Float (ℕ × ℕ × ℕ))
    (n k : ℕ) (M : Array Float) : Bool :=
  (runColumn total I n k M).any fun st =>
    match readCells st 1 2 (n * n), readCells st 2 1 (n * n) with
    | some L, some U => closeArray L (expectedLower total n k M) &&
        closeArray U (expectedUpper n k M) && frameOK (initState (inputBuffers n M)) st n k &&
        L[k + n * k]! == 1 &&
        (List.range k).all (fun i => L[i + n * k]! == 0 && U[k + n * i]! == 0)
    | _, _ => false

private def dense := packRows #[#[2, -1, 3], #[4, 2, -2], #[1, 5, 1]]
private def signed := packRows #[#[-4, 3], #[2, 1]]
private def zeroBelow := packRows #[#[0, 2], #[7, 3]]
private def zeroMiddle := packRows #[#[2, 3, 4], #[1, 0, 6], #[7, 5, 8]]

#guard checkColumn false divisionBias 3 0 dense
#guard checkColumn false divisionBias 3 1 dense
#guard checkColumn false divisionBias 3 2 dense
#guard checkColumn false divisionBias 2 0 signed
#guard checkColumn false divisionBias 1 0 #[-7]
#guard checkColumn true divisionBias 2 0 zeroBelow
#guard checkColumn true divisionBias 3 1 zeroMiddle

-- A last column has no below-diagonal quotient, so rejecting all divisions still succeeds.
#guard checkColumn false rejectDivision 3 2 dense
#guard checkColumn true rejectDivision 2 0 zeroBelow
#guard checkColumn true rejectDivision 3 1 zeroMiddle
#guard (runColumn false rejectDivision 2 0 signed).isNone
#guard (runColumn true rejectDivision 2 0 signed).isNone

-- Biased division is observable, while the actual unit-diagonal literal stays exactly one.
#guard (runColumn false divisionBias 3 0 dense).any fun st =>
  st.store.read () 1 2 == some 1 && (st.store.read () 1 3).any fun x => (x - 2).abs > 1e-4

end NLAlibTools
