/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.ThresholdPivot
import NLAlib.Matrix.Computation.StridedPivotScan
import NLAlib.Matrix.Computation.RookPivot

/-!
# Executable threshold and rook policy checks

Actual Float/index execution checks quality decisions, equality, signs, active suffixes,
offsets, source retention and scratch release. The backend with division disabled checks
that the selectors execute no division. These supplement the exact library contracts.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private def noDivInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem :=
    { (floatIndexedInterp #[] []).sem with bin := fun p op a b =>
        match op with
        | .div => none
        | _ => (floatIndexedInterp #[] []).sem.bin p op a b } }

private def runChoice (b : Builder Unit Unit ℕ ℕ Unit) (a : Array Float) :=
  exec noDivInterp b.run (initState [a.map some, #[some 701, none, none, some 709]])

private def outputMatches (s : Option (St Unit Float (ℕ × ℕ × ℕ)))
    (a : Array Float) (indices : List Float) : Bool :=
  s.any fun st => st.store.size == 2 && showBuf st 0 == a.toList &&
    showBuf st 1 == 701 :: indices ++ [709]

private def a : Array Float := #[2,-4,3, 1,2,3, 2,1,1]
#guard outputMatches (runChoice (thresholdPivotChoice () 3 0 0 0 (1/2) ⟨1,1⟩) a) a [0,0]

#guard outputMatches (runChoice (thresholdPivotChoice () 3 0 0 0 (3/4) ⟨1,1⟩) a) a [1,0]
#guard outputMatches (runChoice (thresholdPivotChoice () 3 0 0 0 1 ⟨1,1⟩) a) a [1,0]
private def ties : Array Float := #[4,-4,3, 1,2,3, 2,1,1]
#guard outputMatches (runChoice (thresholdPivotChoice () 3 0 0 0 1 ⟨1,1⟩) ties) ties [0,0]
private def zeros : Array Float := Array.replicate 9 0
#guard outputMatches (runChoice (thresholdPivotChoice () 3 0 0 0 (1/2) ⟨1,1⟩) zeros) zeros [0,0]
private def inactive : Array Float := #[1000,2000,3000, 4000,2,-8, 5000,3,1]
#guard outputMatches (runChoice (thresholdPivotChoice () 3 1 0 0 (1/2) ⟨1,1⟩) inactive)
  inactive [2,0]
#guard outputMatches (runChoice (thresholdPivotChoice () 3 2 0 0 1 ⟨1,1⟩) inactive)
  inactive [2,0]
private def offset : Array Float := #[101] ++ a ++ #[109]
#guard outputMatches (runChoice (thresholdPivotChoice () 3 0 0 1 (1/2) ⟨1,1⟩) offset)
  offset [0,0]
#guard outputMatches (runChoice (thresholdPivotChoice () 1 0 0 1 1 ⟨1,1⟩) #[101,-7,109])
  #[101,-7,109] [0,0]
#guard outputMatches (runChoice (argmaxStridedAbs () 3 0 0 3 ⟨1,1⟩) a) a [0,0]
#guard outputMatches (runChoice (argmaxStridedAbs () 3 0 1 3 ⟨1,1⟩) a) a [0,0]
#guard outputMatches (runChoice (argmaxStridedAbs () 3 0 2 3 ⟨1,1⟩) a) a [0,0]
private def strided : Array Float := #[2,101,-7,109,4]
#guard outputMatches (runChoice (argmaxStridedAbs () 3 0 0 2 ⟨1,1⟩) strided) strided [1,0]
-- Packing finishes before the output write, so the source/output alias is executable.
#guard (exec noDivInterp (argmaxStridedAbs () 3 0 0 2 ⟨0,1⟩).run
  (initState [strided.map some])).any (fun st => st.store.size == 1 &&
    showBuf st 0 == [2,1,-7,109,4])

private def rook (n k off : ℕ) : Builder Unit Unit ℕ ℕ Unit :=
  rookPivotChoice () (.const n) (.const k) 0 (.const off) ⟨1,1⟩ ⟨1,2⟩
-- Current column maxima strictly increase from 3 to 7 before equality finishes the search;
-- the final row scan prefers column 1, but equality must retain current column 2.
private def tieCycle : Array Float := #[3,2,0, 0,7,0, 5,7,0]
#guard outputMatches (runChoice (rook 3 0 0) tieCycle) tieCycle [1,2]
private def growth : Array Float := #[1,2,0, 9,0,10, 0,5,6]
#guard outputMatches (runChoice (rook 3 0 0) growth) growth [2,1]
#guard outputMatches (runChoice (rook 3 0 0) zeros) zeros [0,0]
#guard outputMatches (runChoice (rook 3 1 0) inactive) inactive [2,1]
#guard outputMatches (runChoice (rook 3 2 0) inactive) inactive [2,2]
#guard outputMatches (runChoice (rook 1 0 1) #[101,-7,109]) #[101,-7,109] [0,0]
#guard outputMatches (runChoice (rook 3 0 1) (#[101] ++ growth ++ #[109]))
  (#[101] ++ growth ++ #[109]) [2,1]
private def firstTie : Array Float := #[1,-5,5, 0,1,1, 0,1,1]
#guard outputMatches (runChoice (rook 3 0 0) firstTie) firstTie [1,0]
-- A zero rook pivot certifies its row and column, even with a nonzero disjoint active entry.
#guard outputMatches (runChoice (rook 2 0 0) #[0,0,0,5]) #[0,0,0,5] [0,0]
#guard outputMatches (runChoice (rook 2 0 0) #[0,0,5,4]) #[0,0,5,4] [0,1]
#guard (exec noDivInterp (rookPivotChoice () 3 0 0 0 ⟨1,1⟩ ⟨2,1⟩).run
  (initState [growth.map some, #[some 101, none, some 109],
    #[some 701, none, some 709]])).any (fun st => st.store.size == 3 &&
      showBuf st 0 == growth.toList && showBuf st 1 == [101,2,109] &&
        showBuf st 2 == [701,1,709])
#guard (runChoice (rook 0 0 0) #[]).isNone

end NLAlibTools
