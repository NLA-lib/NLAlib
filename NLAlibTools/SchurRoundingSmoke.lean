/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.SchurUpdate

/-!
# Executable rank-one and Schur rounding checks

These check the actual kernels, shared-buffer disjoint operands, degenerate dimensions,
scratch release and the proposed local rounding budget under deliberately perturbed scalar
operations. They do not prove that the tool Float interpreter satisfies a scalar model.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev RoundingState := St Unit Float (ℕ × ℕ × ℕ)

private def readArray (st : RoundingState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def bufferIs (result : Option RoundingState) (b : ℕ) (expected : Array Float) : Bool :=
  result.any fun st => readArray st b 0 expected.size == some expected

private def gerShared := exec (floatIndexedInterp #[] [])
  (ger () 2 3 ⟨0, 1⟩ 0 2 0 4 0 7).run
  (initState [(#[101, 2, 1, 2, 3, -4, 0, 4, 5, 6, 7, 8, 9, 109]).map some])
#guard bufferIs gerShared 0 #[101, 2, 1, 2, 3, -4, 0, 10, 17, -2, -9, 8, 9, 109]
#guard gerShared.any fun st => st.store.size == 1 && st.cur () == 14 && st.curW == 896

-- No columns means no operand reads, even when every handle is invalid.
private def gerEmptyColumns := exec (floatIndexedInterp #[] [])
  (ger () 2 0 ⟨17, 99⟩ 23 77 29 55 31 33).run (initState [])
#guard gerEmptyColumns.any fun st => st.store.size == 0 && st.cur () == 0

-- With columns but no rows, coefficient/right-vector instructions still execute.
private def gerEmptyRows := exec (floatIndexedInterp #[] [])
  (ger () 0 2 ⟨0, 0⟩ 17 99 1 0 23 77).run
  (initState [#[some 2], #[some 3, some (-4)]])
#guard bufferIs gerEmptyRows 0 #[2]
#guard bufferIs gerEmptyRows 1 #[3, -4]
#guard gerEmptyRows.any fun st => st.store.size == 2 && st.cur () == 3
#guard (exec (floatIndexedInterp #[] []) (ger () 0 2 ⟨17, 99⟩ 19 77 0 0 23 55).run
  (initState [#[some 3, some (-4)]])).isNone

private def schurExact := exec (floatIndexedInterp #[] [])
  (schurStep () 2 0 1 0).run (initState [(#[101, 4, 2, 1, 3, 109]).map some])
#guard bufferIs schurExact 0 #[101, 0, 0, 0, 2.5, 109]
#guard schurExact.any fun st => st.store.size == 1 && st.cur () == 6

-- Every arithmetic result and every nonzero literal receives a relative perturbation.
-- In particular, -1 is perturbed; omitting that factor understates the actual trace.
private def perturbed : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := { floatSem with
      toNat := fun _ => boundedFloatToNat
      lit := fun p q => (floatSem.lit p q).map fun x => x * 1.001
      bin := fun p op x y => (floatSem.bin p op x y).map fun z => z * 1.001 } }

private def original : Array Float := #[4, 2, 1, 0]
private def schurPerturbed := exec perturbed (schurStep () 2 0 1 0).run
  (initState [(#[101] ++ original ++ #[109]).map some])

-- Independently evaluate elimination and the five-factor absolute defect allowance.
private def localBudgetHolds : Bool :=
  schurPerturbed.any fun st => (readArray st 0 1 4).any fun actual =>
    let u : Float := 0.001
    let gamma5 := 1 / ((1-u) * (1-u) * (1-u) * (1-u) * (1-u)) - 1
    (List.range 4).all fun t =>
      let i := t % 2
      let j := t / 2
      let term := original[i]! * original[2*j]! / original[0]!
      let exactEntry := original[t]! - term
      (actual[t]! - exactEntry).abs ≤ u * original[t]!.abs + gamma5 * term.abs + 1e-12

#guard localBudgetHolds
-- A zero old active entry isolates the product error. Four factors are insufficient for
-- this actual run, so the literal's contribution is observable rather than just documented.
#guard schurPerturbed.any fun st => (readArray st 0 1 4).any fun a =>
  let u : Float := 0.001
  let gamma4 := 1 / ((1-u) * (1-u) * (1-u) * (1-u)) - 1
  (a[3]! + 0.5).abs > gamma4 * 0.5 + 1e-12
#guard schurPerturbed.any fun st =>
  (readArray st 0 1 1).any fun a => a[0]! != 0
#guard schurPerturbed.any fun st => st.store.size == 1 && st.cur () == 6
#guard schurPerturbed.any fun st => st.store.read () 0 0 == some 101 &&
  st.store.read () 0 5 == some 109

end NLAlibTools
