/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.PLU
import NLAlib.Matrix.Computation.GuardedElimination

/-!
# Executable checks for rounded partial-pivoted LU

The actual unchanged builders run with deliberately perturbed scalar instructions: negative
literals and every addition, multiplication and division are multiplied by 1.001. Nonnegative
integer literals remain exact, so index controls and the unit diagonal are not perturbed.
The checker independently replays the actual log and evaluates the componentwise factor
residual against the saved-pivot gamma allowance. Every output word must be initialized.
These finite regression examples do not establish a universal Float accuracy model.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev RoundedState := St Unit Float (ℕ × ℕ × ℕ)

private def roundedInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := { floatSem with
      toNat := fun _ => boundedFloatToNat
      lit := fun p q => (floatSem.lit p q).map fun x => if q < 0 then x * 1.001 else x
      bin := fun p op x y => match op with
        | .add | .mul | .div => (floatSem.bin p op x y).map fun z => z * 1.001
        | _ => floatSem.bin p op x y } }

private def readCells (st : RoundedState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def packRows (rows : Array (Array Float)) : Array Float :=
  let n := rows.size
  (List.range (n * n)).toArray.map fun t => (rows[t % n]!)[t / n]!

-- This decoder never calls the library's permutation decoder. It swaps CURRENT positions.
private def replayLog (n : ℕ) (history : Array Float) : Option (Array ℕ) := do
  if history.size != n then none else
    (List.range n).foldlM (fun order k => do
      let word ← history[k]?
      let row ← boundedFloatToNat word
      if row < n && k ≤ row && word == Float.ofNat row then
        let oldK ← order[k]?
        let oldRow ← order[row]?
        some ((order.set! k oldRow).set! row oldK)
      else none) (List.range n).toArray

private def roundoff : Float := 0.0010001

private def gamma (n : ℕ) : Float :=
  1 / ((List.range n).foldl (fun product _ => product * (1 - roundoff)) 1) - 1

private def residual (n : ℕ) (A L U : Array Float) (order : Array ℕ) (i j : ℕ) : Float :=
  A[order[i]! + n * j]! - (List.range n).foldl
    (fun acc k => acc + L[i + n * k]! * U[k + n * j]!) 0

private def validFactors (n : ℕ) (A L U history : Array Float) : Bool :=
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
        let scale := (List.range n).foldl
          (fun acc k => acc + L[i + n * k]!.abs * U[k + n * j]!.abs) 0
        (residual n A L U order i j).abs ≤ gamma (n + 4) * scale + 1e-12 &&
          (if i < j then L[t]! == 0 else true) &&
          (if j < i then U[t]! == 0 else true) && L[t]!.abs ≤ 1 + roundoff

private def buffers (n : ℕ) (A : Array Float) (ao lo uo ho : ℕ) :
    List (Array (Option Float)) :=
  [Array.replicate ao (some 101) ++ A.map some ++ #[some 109],
    Array.replicate lo (some 201) ++ Array.replicate (n * n) none ++ #[some 209],
    Array.replicate uo (some 301) ++ Array.replicate (n * n) none ++ #[some 309],
    Array.replicate ho (some 401) ++ Array.replicate n none ++ #[some 409],
    #[some 701, none, some 709]]

private def runRounded (n : ℕ) (A : Array Float) (ao lo uo ho : ℕ) : Option RoundedState :=
  exec roundedInterp (pluFactor () (.const n) 0 1 2 3
    (.const ao) (.const lo) (.const uo) (.const ho)).run (initState (buffers n A ao lo uo ho))

-- Check the complete outside-cell frame, including initialized sentinels and unrelated none.
private def frameOK (before after : RoundedState) (n lo uo ho : ℕ) : Bool :=
  before.store.size == after.store.size && before.cur () == after.cur () &&
    before.curW == after.curW && before.store.shape == after.store.shape &&
    before.pos .gaussian == after.pos .gaussian &&
    before.pos .rademacher == after.pos .rademacher &&
    before.pos .uniform == after.pos .uniform &&
    (List.range before.store.size).all fun b =>
      (List.range ((before.store[b]!).2.size)).all fun j =>
        if (b == 1 && lo ≤ j && j < lo + n * n) ||
            (b == 2 && uo ≤ j && j < uo + n * n) ||
            (b == 3 && ho ≤ j && j < ho + n) then true
        else after.store.read () b j == before.store.read () b j

private def checkRun (n : ℕ) (A : Array Float) (ao lo uo ho : ℕ) : Bool :=
  (runRounded n A ao lo uo ho).any fun st =>
    match readCells st 1 lo (n * n), readCells st 2 uo (n * n), readCells st 3 ho n with
    | some L, some U, some history => validFactors n A L U history &&
        frameOK (initState (buffers n A ao lo uo ho)) st n lo uo ho &&
        readCells st 0 ao (n * n) == some A
    | _, _, _ => false

private def dense := packRows #[#[2, -1, 3], #[4, 2, -2], #[1, 5, 1]]
private def denseSwaps := packRows #[#[2, 0, 1], #[1, 1, 2], #[4, 2, 3]]
private def signed := packRows #[#[1, 3], #[-8, 2]]
private def cycle := packRows #[#[0, 0, 0, 1], #[1, 0, 0, 0], #[0, 1, 0, 0], #[0, 0, 1, 0]]
private def tie := packRows #[#[-2, 0, 1], #[2, 3, 0], #[1, 1, 4]]
private def zeroFirst := packRows #[#[0, 2, 1], #[0, 0, 3], #[0, 4, 2]]
private def zeroMiddle := packRows #[#[2, 4, 1], #[1, 2, 3], #[0, 0, 5]]
private def rankOne := packRows #[#[1, 2, 4], #[2, 4, 8], #[4, 8, 16]]

#guard checkRun 3 dense 0 0 0 0
#guard checkRun 3 denseSwaps 0 0 0 0
#guard checkRun 2 signed 0 0 0 0
#guard checkRun 4 cycle 0 0 0 0
#guard checkRun 3 tie 0 0 0 0
#guard checkRun 3 zeroFirst 0 0 0 0
#guard checkRun 3 zeroMiddle 0 0 0 0
#guard checkRun 3 rankOne 0 0 0 0
#guard checkRun 3 (Array.replicate 9 0) 0 0 0 0
#guard checkRun 1 #[-7] 0 0 0 0
#guard checkRun 1 #[0] 0 0 0 0
#guard checkRun 0 #[] 0 0 0 0
#guard checkRun 3 dense 2 3 1 4
#guard checkRun 3 zeroFirst 1 2 1 3

-- Repeated swaps exercise composition orientation rather than only a single involution.
#guard (runRounded 4 cycle 0 0 0 0).any fun st =>
  (readCells st 3 0 4).any fun h => replayLog 4 h == some #[1, 2, 3, 0]
#guard (runRounded 3 denseSwaps 0 0 0 0).any fun st =>
  (readCells st 3 0 3).any fun h => replayLog 3 h == some #[2, 0, 1]

-- The numerical check is not accidentally exercising an exact-arithmetic backend.
#guard (runRounded 3 dense 0 0 0 0).any fun st =>
  match readCells st 1 0 9, readCells st 2 0 9, readCells st 3 0 3 with
  | some L, some U, some h => (replayLog 3 h).any fun order =>
      (List.range 9).any fun t => (residual 3 dense L U order (t % 3) (t / 3)).abs > 1e-4
  | _, _, _ => false

-- Invalid handles and offsets verify the explicit zero-dimensional no-read path.
#guard (exec roundedInterp (pluFactor () 0 17 23 29 31 9 11 13 15).run
  (initState [])).any fun st => st.store.size == 0 && st.cur () == 0 && st.curW == 0

end NLAlibTools
