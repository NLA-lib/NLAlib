/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.LDL

/-!
# Runtime checks for stored LDL factorization

These execute the actual LU-backed LDL routine on indefinite and negative definite inputs,
independently reconstruct the matrix, check structural entries and signs, and exercise
output offsets, diagonal/source overlap, empty matrices and rejected square roots.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private def ldlRun (n : ℕ) (A : Array Float) :=
  exec (floatInterp #[] []) (ldlFactor () (.const n) 0 1 2 0 0 0).run
    (initState [A.map some, Array.replicate (n * n) none,
      Array.replicate n none, #[some 909]])

private def ldlMatches (result : Option (St Unit Float (ℕ × ℕ × ℕ)))
    (L D : List Float) : Bool :=
  match result with
  | none => false
  | some st => st.store.size == 4 && showBuf st 1 == L && showBuf st 2 == D &&
    showBuf st 3 == [909]

private def ldlReconstructs (result : Option (St Unit Float (ℕ × ℕ × ℕ)))
    (n : ℕ) (A : Array Float) : Bool :=
  match result with
  | none => false
  | some st =>
    let L := showBuf st 1
    let D := showBuf st 2
    (List.range (n * n)).all fun t =>
      let i := t % n
      let j := t / n
      let v := (List.range n).foldl (fun acc k =>
        acc + L[i + n * k]?.getD 0 * D[k]?.getD 0 * L[j + n * k]?.getD 0) 0
      (v - A[t]!).abs ≤ 1e-10 &&
        (if i < j then L[t]?.getD 1 == 0 else true) &&
        (if i == j then L[t]?.getD 0 == 1 else true)

private def indefiniteLDL : Array Float := #[2, 4, -2, 4, 5, -13, -2, -13, -21]
#guard ldlMatches (ldlRun 3 indefiniteLDL) [1, 2, -1, 0, 1, 3, 0, 0, 1] [2, -3, 4]
#guard ldlReconstructs (ldlRun 3 indefiniteLDL) 3 indefiniteLDL
#guard ldlMatches (ldlRun 2 #[2, 4, 4, 3]) [1, 2, 0, 1] [2, -5]
#guard ldlReconstructs (ldlRun 2 #[2, 4, 4, 3]) 2 #[2, 4, 4, 3]
#guard ldlMatches (ldlRun 2 #[-1, 0, 0, -4]) [1, 0, 0, 1] [-1, -4]
#guard ldlMatches (ldlRun 1 #[-4]) [1] [-4]
#guard match ldlRun 3 indefiniteLDL with
  | none => false
  | some st => showBuf st 0 == indefiniteLDL.toList

private def ldlOffsets := exec (floatInterp #[] []) (ldlFactor () 2 0 1 2 1 2 1).run
  (initState [(#[101, 2, 4, 4, 3, 909]).map some,
    #[some 101, some 303] ++ Array.replicate 4 none ++ #[some 909],
    #[some 303] ++ Array.replicate 2 none ++ #[some 909]])
#guard match ldlOffsets with
  | none => false
  | some st => st.store.size == 3 && showBuf st 1 == [101, 303, 1, 2, 0, 1, 909] &&
    showBuf st 2 == [303, 2, -5, 909]

private def ldlDiagonalOverlap := exec (floatInterp #[] []) (ldlFactor () 2 0 1 0 0 0 0).run
  (initState [(#[2, 4, 4, 3]).map some, Array.replicate 4 none])
#guard match ldlDiagonalOverlap with
  | none => false
  | some st => st.store.size == 2 && showBuf st 0 == [2, -5, 4, 3] &&
    showBuf st 1 == [1, 2, 0, 1]

private def ldlNoRoot : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatInterp #[] [] with sem := { floatSem with
    un := fun p op x => match op with
      | .sqrt => none
      | _ => floatSem.un p op x } }
#guard (exec ldlNoRoot (ldlFactor () 3 0 1 2 0 0 0).run
  (initState [indefiniteLDL.map some, Array.replicate 9 none,
    Array.replicate 3 none])).isSome
#guard (exec (floatInterp #[] []) (ldlFactor () 0 17 23 29 9 11 13).run (initState [])).isSome
#guard (ldlRun 1 #[0]).isNone
#guard (ldlRun 2 #[0, 1, 1, 0]).isNone

end NLAlibTools
