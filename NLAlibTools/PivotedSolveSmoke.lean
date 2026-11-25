/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.PivotedSolve

/-!
# Runtime checks for actual pivoted factor-then-solve

These execute the actual stored builders with the tool Float/index interpretation. Three-cycle
logs, different row/column orders, overlapping RHS windows, empty invalid handles and scope
release exercise orientation and framing. They supplement the exact theorems and make no
claim that this tool interpretation satisfies the library's arithmetic contracts.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private def runSolve (b : Builder Unit Unit ℕ ℕ Unit) (buffers : List (Array (Option Float))) :=
  exec (floatIndexedInterp #[] []) b.run (initState buffers)

private def close (a b : List Float) : Bool :=
  a.length == b.length && (a.zip b).all fun (x,y) => x.isFinite && (x-y).abs ≤ 1e-9

private def bufferMatches (s : Option (St Unit Float (ℕ × ℕ × ℕ))) (buf : ℕ)
    (wanted : List Float) (buffers : ℕ) : Bool :=
  s.any fun st => st.store.size == buffers && close (showBuf st buf) wanted

private def a : Array Float := #[2,1,4, 0,1,2, 1,2,3]
private def c : Array Float := #[1,4,7, 2,5,8, 3,6,10]
private def asymmetric : Array Float := #[0,3,5, 1,4,6, 2,12,7]

-- The partialRun pivot log is a three-cycle, so using original row labels or inverse order fails.
private def partialRun := runSolve (pluSolve () 3 0 0 1 0)
  [a.map some, (#[5,9,17] : Array Float).map some, #[some 701, some 709]]
#guard bufferMatches partialRun 1 [1,2,3] 3
#guard bufferMatches partialRun 0 a.toList 3
#guard bufferMatches partialRun 2 [701,709] 3

-- Both complete-pivot logs are three-cycles. Undoing column swaps forward gives the wrong x.
private def complete := runSolve (pluqSolve () 3 0 0 1 0)
  [c.map some, (#[14,32,53] : Array Float).map some, #[some 701, some 709]]
#guard bufferMatches complete 1 [1,2,3] 3
#guard bufferMatches complete 0 c.toList 3
#guard bufferMatches complete 2 [701,709] 3

-- Different row and column logs catch reusing the row log to restore the solution.
private def different := runSolve (pluqSolve () 3 0 0 1 0)
  [asymmetric.map some, (#[8,47,38] : Array Float).map some]
#guard bufferMatches different 1 [1,2,3] 2
#guard bufferMatches different 0 asymmetric.toList 2

-- Matrix and RHS share exact words: b is the first column, so x must be the first basis vector.
private def partialOverlap := runSolve (pluSolve () 3 0 1 0 1)
  [((#[101] ++ a ++ #[109]) : Array Float).map some, #[some 809]]
#guard bufferMatches partialOverlap 0 [101,1,0,0,0,1,2,1,2,3,109] 2
#guard bufferMatches partialOverlap 1 [809] 2

-- Offset overlap with the second source column; factorization must consume A before RHS swaps.
private def completeOverlap := runSolve (pluqSolve () 3 0 1 0 4)
  [((#[101] ++ c ++ #[109]) : Array Float).map some, #[some 809]]
#guard bufferMatches completeOverlap 0 [101,1,4,7,0,1,0,3,6,10,109] 2
#guard bufferMatches completeOverlap 1 [809] 2

#guard bufferMatches (runSolve (pluSolve () 1 0 0 1 1)
  [#[some (-7)], #[some 101, some 21, some 109]]) 1 [101,-3,109] 2
#guard bufferMatches (runSolve (pluqSolve () 1 0 0 1 1)
  [#[some (-7)], #[some 101, some 21, some 109]]) 1 [101,-3,109] 2
#guard bufferMatches (runSolve (pluSolve () 0 19 23 37 101) []) 0 [] 0
#guard bufferMatches (runSolve (pluqSolve () 0 19 23 37 101) []) 0 [] 0
#guard (runSolve (pluSolve () 2 0 0 1 0)
  [(#[1,2,2,4] : Array Float).map some, #[some 1,some 2]]).isNone
#guard (runSolve (pluqSolve () 2 0 0 1 0)
  [(#[1,2,2,4] : Array Float).map some, #[some 1,some 2]]).isNone

-- Independently expose forward versus inverse orientation of a non-involutive stored log.
#guard bufferMatches (runSolve (applyPivotLog () 3 0 0 1 0)
  [(#[2,2,2] : Array Float).map some, (#[1,2,3] : Array Float).map some]) 1 [3,1,2] 2
#guard bufferMatches (runSolve (applyPivotLogReverse () 3 0 0 1 0)
  [(#[2,2,2] : Array Float).map some, (#[1,2,3] : Array Float).map some]) 1 [2,3,1] 2
#guard bufferMatches (runSolve (applyPivotLogReverse () 3 0 0 1 0)
  [(#[2,2,2] : Array Float).map some, (#[3,1,2] : Array Float).map some]) 1 [1,2,3] 2
#guard bufferMatches (runSolve (applyPivotLog () 0 19 23 37 101) []) 0 [] 0
#guard bufferMatches (runSolve (applyPivotLogReverse () 0 19 23 37 101) []) 0 [] 0

end NLAlibTools
