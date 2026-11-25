/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.SemidefiniteCholesky

/-!
# Runtime checks for zero-safe semidefinite Cholesky

Run the actual stored routine on rank-deficient matrices, with independent Gram reconstruction,
exact structural checks, overlapping buffers, and rejected arithmetic on zero branches.
These finite examples supplement the exact theorem and do not certify Float accuracy.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private def runPSD (n : ℕ) (input : Array Float) :=
  exec (floatInterp #[] []) (semidefiniteCholesky () (.const n) 0 0 1 0).run
    (initState [input.map some, Array.replicate (n * n) none, #[some 909]])

private def matchesPSD (result : Option (St Unit Float (ℕ × ℕ × ℕ)))
    (expected : List Float) : Bool :=
  match result with
  | none => false
  | some st => st.store.size == 3 && showBuf st 1 == expected && showBuf st 2 == [909]

private def gramPSD (result : Option (St Unit Float (ℕ × ℕ × ℕ)))
    (n : ℕ) (input : Array Float) : Bool :=
  match result with
  | none => false
  | some st =>
    let L := showBuf st 1
    (List.range (n * n)).all fun t =>
      let i := t % n
      let j := t / n
      let v := (List.range n).foldl
        (fun acc k => acc + L[i + n * k]?.getD 0 * L[j + n * k]?.getD 0) 0
      (v - input[t]!).abs ≤ 1e-10 &&
        (if i < j then L[t]?.getD 1 == 0 else true) &&
        (if i == j then L[t]?.getD (-1) ≥ 0 else true)

private def rankOnePSD : Array Float := #[4, 6, 0, 6, 9, 0, 0, 0, 0]
private def middleZeroPSD : Array Float := #[4, 6, 8, 6, 9, 12, 8, 12, 41]
private def firstZeroPSD : Array Float := #[0, 0, 0, 0, 4, 0, 0, 0, 9]

#guard matchesPSD (runPSD 3 rankOnePSD) [2, 3, 0, 0, 0, 0, 0, 0, 0]
#guard matchesPSD (runPSD 3 middleZeroPSD) [2, 3, 4, 0, 0, 0, 0, 0, 5]
#guard matchesPSD (runPSD 3 firstZeroPSD) [0, 0, 0, 0, 2, 0, 0, 0, 3]
#guard gramPSD (runPSD 3 rankOnePSD) 3 rankOnePSD
#guard gramPSD (runPSD 3 middleZeroPSD) 3 middleZeroPSD
#guard gramPSD (runPSD 3 firstZeroPSD) 3 firstZeroPSD
#guard matchesPSD (runPSD 3 (Array.replicate 9 0)) (List.replicate 9 0)
#guard matchesPSD (runPSD 1 #[0]) [0]
#guard matchesPSD (runPSD 1 #[4]) [2]
#guard match runPSD 3 middleZeroPSD with
  | none => false
  | some st => showBuf st 0 == middleZeroPSD.toList

private def psdOverlap := exec (floatInterp #[] [])
  (semidefiniteCholesky () 3 0 1 0 2).run
  (initState [((#[101] ++ middleZeroPSD ++ #[303, 909]).map some)])
#guard match psdOverlap with
  | none => false
  | some st => st.store.size == 1 &&
    showBuf st 0 == [101, 4, 2, 3, 4, 0, 0, 0, 0, 0, 5, 909]

private def psdInPlace := exec (floatInterp #[] []) (semidefiniteCholesky () 3 0 0 0 0).run
  (initState [firstZeroPSD.map some])
#guard match psdInPlace with
  | none => false
  | some st => st.store.size == 1 && showBuf st 0 == [0, 0, 0, 0, 2, 0, 0, 0, 3]

private def noRootOrDivision : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatInterp #[] [] with
    sem := { floatSem with
      bin := fun p op x y => match op with
        | .div => none
        | _ => floatSem.bin p op x y
      un := fun p op x => match op with
        | .sqrt => none
        | _ => floatSem.un p op x } }
#guard (exec noRootOrDivision (semidefiniteCholesky () 3 0 0 1 0).run
  (initState [Array.replicate 9 (some 0), Array.replicate 9 none])).isSome
#guard (exec (floatInterp #[] []) (semidefiniteCholesky () 0 17 9 23 11).run
  (initState [])).isSome
#guard (runPSD 1 #[-1]).isNone

end NLAlibTools
