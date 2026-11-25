/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.CompletePivot
import NLAlib.Matrix.Computation.RowScales
import NLAlib.Matrix.Computation.ScaledPivot

/-!
# Executable checks for complete and scaled pivot policies

The checks independently inspect initialized outputs, active-block maxima, stable ties,
row norms, scaled ratios, frames and released workspace. Inputs use small exactly represented
values. These examples do not prove a formal Float arithmetic or range contract.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev PolicyState := St Unit Float (ℕ × ℕ × ℕ)

private def cells (st : PolicyState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def containsCells (result : Option PolicyState) (b off : ℕ)
    (expected : Array Float) : Bool :=
  result.any fun st => cells st b off expected.size == some expected

private def choiceRun (n k : ℕ) (A : Array Float) : Option PolicyState :=
  exec (floatIndexedInterp #[] [])
    (completePivotChoice () (.const n) (.const k) 0 0 ⟨1, 0⟩ ⟨1, 1⟩).run
    (initState [A.map some, #[none, none], #[some 701, some 709]])

-- Recompute all active magnitudes directly from the original packed input, including the
-- strict column-major tie condition. No scan-prefix or library selector theorem is used.
private def validChoice (A : Array Float) (n k r c : ℕ) : Bool :=
  decide (k ≤ r ∧ r < n ∧ k ≤ c ∧ c < n) &&
    (A[r + n * c]?).any fun pivot =>
      (List.range (n * n)).all fun t =>
        let i := t % n
        let j := t / n
        if k ≤ i ∧ k ≤ j then
          (A[t]?).any fun x => decide (x.abs ≤ pivot.abs) &&
            (if j < c ∨ (j = c ∧ i < r) then decide (x.abs < pivot.abs) else true)
        else true

private def checkChoice (result : Option PolicyState) (A : Array Float) (n k r c : ℕ) : Bool :=
  containsCells result 1 0 #[Float.ofNat r, Float.ofNat c] && validChoice A n k r c &&
    containsCells result 0 0 A && containsCells result 2 0 #[701, 709] &&
    result.any fun st => st.store.size == 3 && st.cur () == A.size + 4 &&
      st.curW == 64 * (A.size + 4)

private def denseChoice : Array Float := #[1, 2, -3, 4, -9, 5, 6, 7, 8]
#guard checkChoice (choiceRun 3 0 denseChoice) denseChoice 3 0 1 1

-- Equal maxima in different columns select the earlier column, then its first row.
private def tieChoice : Array Float := #[1, -9, 9, 9, 2, 3, 4, 5, 6]
#guard checkChoice (choiceRun 3 0 tieChoice) tieChoice 3 0 1 0

-- Huge entries outside the active block cannot win.
private def activeChoice : Array Float := #[999, 999, 999, 999, -4, 4, 999, 4, 1]
#guard checkChoice (choiceRun 3 1 activeChoice) activeChoice 3 1 1 1
#guard checkChoice (choiceRun 3 2 activeChoice) activeChoice 3 2 2 2
#guard checkChoice (choiceRun 3 1 (Array.replicate 9 0)) (Array.replicate 9 0) 3 1 1 1
#guard checkChoice (choiceRun 1 0 #[-7]) #[-7] 1 0 0 0

private def offsetChoice := exec (floatIndexedInterp #[] [])
  (completePivotChoice () 2 0 0 1 ⟨1, 1⟩ ⟨1, 3⟩).run
  (initState [(#[101, 1, -7, 3, 4, 109]).map some,
    #[some 201, none, some 203, none, some 209], #[some 701]])
#guard containsCells offsetChoice 0 0 #[101, 1, -7, 3, 4, 109]
#guard containsCells offsetChoice 1 0 #[201, 1, 203, 0, 209]
#guard containsCells offsetChoice 2 0 #[701]
#guard offsetChoice.any fun st => st.store.size == 3 && st.cur () == 12

private def scalesRun (m n : ℕ) (A : Array Float) : Option PolicyState :=
  exec (floatIndexedInterp #[] [])
    (rowScales () (.const m) (.const n) 0 0 1 0).run
    (initState [A.map some, Array.replicate m none, #[some 701]])

#guard containsCells (scalesRun 3 2 #[1, -2, 0, 4, 1, -5]) 1 0 #[4, 2, 5]
#guard containsCells (scalesRun 2 3 #[-1, 0, 3, -7, 2, 4]) 1 0 #[3, 7]
#guard containsCells (scalesRun 2 2 (Array.replicate 4 0)) 1 0 #[0, 0]
#guard containsCells (scalesRun 3 0 #[]) 1 0 #[0, 0, 0]
#guard (scalesRun 0 3 #[]).any fun st => st.store.size == 3 && st.cur () == 1

private def offsetScales := exec (floatIndexedInterp #[] [])
  (rowScales () 2 3 0 1 1 2).run
  (initState [(#[101, -1, 0, 3, -7, 2, 4, 109]).map some,
    #[some 201, some 203, none, none, some 209], #[some 701]])
#guard containsCells offsetScales 0 0 #[101, -1, 0, 3, -7, 2, 4, 109]
#guard containsCells offsetScales 1 0 #[201, 203, 3, 7, 209]
#guard containsCells offsetScales 2 0 #[701]
#guard offsetScales.any fun st => st.store.size == 3 && st.cur () == 14

-- Empty matrix storage can share the scale output; no source entry may be read.
private def emptyColumns := exec (floatIndexedInterp #[] [])
  (rowScales () 3 0 0 99 0 1).run
  (initState [#[some 101, none, none, none, some 109]])
#guard containsCells emptyColumns 0 0 #[101, 0, 0, 0, 109]
#guard (exec (floatIndexedInterp #[] []) (rowScales () 0 3 17 99 23 77).run
  (initState [])).isSome

private def scaledRunWith (I : Interp Unit Unit Float (ℕ × ℕ × ℕ))
    (x scales : Array Float) : Option PolicyState :=
  exec I (argmaxScaledAbs () (.const x.size) 0 0 1 0 ⟨2, 1⟩).run
    (initState [x.map some, scales.map some, #[some 101, none, some 109], #[some 701]])

private def scaledRun := scaledRunWith (floatIndexedInterp #[] [])

private def checkScaled (result : Option PolicyState) (x scales : Array Float) (r : ℕ) : Bool :=
  let ratio : ℕ → Float := fun i => if scales[i]! = 0 then 0 else x[i]!.abs / scales[i]!
  containsCells result 2 0 #[101, Float.ofNat r, 109] &&
    containsCells result 0 0 x && containsCells result 1 0 scales &&
    containsCells result 3 0 #[701] && decide (r < x.size) &&
    (List.range x.size).all (fun i => decide (ratio i ≤ ratio r) &&
      (if i < r then decide (ratio i < ratio r) else true)) &&
    result.any fun st => st.store.size == 4 && st.cur () == x.size + scales.size + 4

-- The raw-magnitude winner differs from the scaled winner.
#guard checkScaled (scaledRun #[-6, 3] #[10, 1]) #[-6, 3] #[10, 1] 1
#guard checkScaled (scaledRun #[-6, 3] #[2, 1]) #[-6, 3] #[2, 1] 0
#guard checkScaled (scaledRun #[0, 2] #[0, 1]) #[0, 2] #[0, 1] 1
#guard checkScaled (scaledRun #[1, 0] #[2, 0]) #[1, 0] #[2, 0] 0
#guard checkScaled (scaledRun #[0, 0, 0] #[0, 2, 0]) #[0, 0, 0] #[0, 2, 0] 0
#guard checkScaled (scaledRun #[-1, -6, 0] #[1, 2, 0]) #[-1, -6, 0] #[1, 2, 0] 1
#guard checkScaled (scaledRun #[-7] #[2]) #[-7] #[2] 0
#guard checkScaled (scaledRun #[0] #[0]) #[0] #[0] 0

private def rejectDivision : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := { floatSem with
      toNat := fun _ => boundedFloatToNat
      bin := fun p op x y => match op with
        | .div => none
        | _ => floatSem.bin p op x y } }

#guard checkScaled (scaledRunWith rejectDivision #[0, 2] #[0, 1]) #[0, 2] #[0, 1] 1
#guard checkScaled (scaledRunWith rejectDivision #[-6, 3] #[2, 1]) #[-6, 3] #[2, 1] 0

end NLAlibTools
