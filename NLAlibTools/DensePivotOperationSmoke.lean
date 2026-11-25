/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Computation.SwapCells
import NLAlib.Matrix.Computation.RowSwap
import NLAlib.Matrix.Computation.ColumnSwap
import NLAlib.Matrix.Computation.ScaledPartialPivot

/-!
# Executable exchanges and scaled pivot operations

These run actual builders and inspect initialized matrix, scale and index outputs, including
shared-buffer disjoint windows. A scalar interpretation rejecting every operation checks that
the exchange kernels need only copies. This is tool regression evidence, not a Float model.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev ExchangeState := St Unit Float (ℕ × ℕ × ℕ)

private def readWords (st : ExchangeState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def bufferEquals (result : Option ExchangeState) (b : ℕ) (a : Array Float) : Bool :=
  result.any fun st => readWords st b 0 a.size == some a

private def copyOnly : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := failSem }

private def cellsExchanged := exec copyOnly (swapCells () ⟨0, 0⟩ ⟨0, 1⟩ ⟨0, 2⟩).run
  (initState [#[none, some 11, some 22, some 99]])
#guard bufferEquals cellsExchanged 0 #[11, 22, 11, 99]
#guard cellsExchanged.any fun st => st.store.size == 1 && st.cur () == 4
#guard bufferEquals (exec copyOnly (swapCells () ⟨0, 0⟩ ⟨0, 1⟩ ⟨0, 1⟩).run
  (initState [#[none, some 11, some 22, some 99]])) 0 #[11, 11, 22, 99]

private def rowsExchanged := exec copyOnly (swapRows () 2 3 0 1 0 1).run
  (initState [(#[101, 1, 2, 3, 4, 5, 6, 109]).map some])
#guard bufferEquals rowsExchanged 0 #[101, 2, 1, 4, 3, 6, 5, 109]
#guard rowsExchanged.any fun st => st.store.size == 1 && st.cur () == 8
#guard (exec copyOnly (swapRows () 2 0 17 99 0 1).run (initState [])).isSome

private def columnsExchanged := exec copyOnly (swapColumns () 2 3 0 1 0 2).run
  (initState [(#[101, 1, 2, 3, 4, 5, 6, 109]).map some])
#guard bufferEquals columnsExchanged 0 #[101, 5, 6, 3, 4, 1, 2, 109]
#guard columnsExchanged.any fun st => st.store.size == 1 && st.cur () == 8
#guard bufferEquals (exec copyOnly (swapColumns () 3 2 0 1 0 1).run
  (initState [(#[101, 1, 2, 3, 4, 5, 6, 109]).map some]))
  0 #[101, 4, 5, 6, 1, 2, 3, 109]
#guard bufferEquals (exec copyOnly (swapColumns () 2 3 0 1 1 1).run
  (initState [(#[101, 1, 2, 3, 4, 5, 6, 109]).map some]))
  0 #[101, 1, 2, 3, 4, 5, 6, 109]
#guard (exec copyOnly (swapColumns () 0 3 17 99 0 2).run (initState [])).isSome
#guard (exec copyOnly (swapColumns () 0 0 17 99 77 88).run (initState [])).any fun st =>
  st.store.size == 0 && st.cur () == 0 && st.curW == 0

private def scaledShared := exec (floatIndexedInterp #[] [])
  (scaledPartialPivot () 2 0 0 1 0 6 ⟨1, 1⟩).run
  (initState [(#[101, 6, 3, 2, 4, 105, 10, 1, 109]).map some,
    #[some 201, none, some 209], #[some 701, some 709]])
#guard bufferEquals scaledShared 0 #[101, 3, 6, 4, 2, 105, 1, 10, 109]
#guard bufferEquals scaledShared 1 #[201, 1, 209]
#guard bufferEquals scaledShared 2 #[701, 709]
#guard scaledShared.any fun st => st.store.size == 3 && st.cur () == 14

private def scaledRun (n k : ℕ) (a scales : Array Float) : Option ExchangeState :=
  exec (floatIndexedInterp #[] [])
    (scaledPartialPivot () (.const n) (.const k) 0 0 1 0 ⟨2, 0⟩).run
    (initState [a.map some, scales.map some, #[none], #[some 701]])

-- Compatibility concerns only the active column: the zero-scale row may have a nonzero
-- entry in another column. The operation must still swap its entire row and scale.
private def zeroScale := scaledRun 2 0 #[0, 2, 9, 1] #[0, 1]
#guard bufferEquals zeroScale 0 #[2, 0, 1, 9]
#guard bufferEquals zeroScale 1 #[1, 0]
#guard bufferEquals zeroScale 2 #[1]

private def activeScaled := scaledRun 3 1 #[99, 2, 3, 50, 6, 3, 70, 8, 9] #[1, 10, 1]
#guard bufferEquals activeScaled 0 #[99, 3, 2, 50, 3, 6, 70, 9, 8]
#guard bufferEquals activeScaled 1 #[1, 1, 10]
#guard bufferEquals activeScaled 2 #[2]
#guard bufferEquals activeScaled 3 #[701]
#guard activeScaled.any fun st => st.store.size == 4 && st.cur () == 14

private def signedTie := scaledRun 2 0 #[6, -3, 2, 4] #[2, 1]
#guard bufferEquals signedTie 0 #[6, -3, 2, 4]
#guard bufferEquals signedTie 1 #[2, 1]
#guard bufferEquals signedTie 2 #[0]
#guard bufferEquals (scaledRun 1 0 #[-7] #[2]) 0 #[-7]
#guard bufferEquals (scaledRun 1 0 #[0] #[0]) 2 #[0]

private def noDivision : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := { floatSem with
      toNat := fun _ => boundedFloatToNat
      bin := fun p op x y => match op with
        | .div => none
        | _ => floatSem.bin p op x y } }

#guard bufferEquals (exec noDivision (scaledPartialPivot () 2 0 0 0 1 0 ⟨2, 0⟩).run
  (initState [(#[0, 2, 9, 1]).map some, (#[0, 1]).map some, #[none]])) 0 #[2, 0, 1, 9]

end NLAlibTools
