/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.BlockedLU

/-!
# Runtime checks for blocked LU

The actual blocked driver runs under the ordinary tool Float interpreter. Independent matrix
multiplication checks its factors, with exact triangular zeros/unit diagonal and optional
cells read explicitly. Cases cover varied block widths, final partial panels, input/output
overlap, offsets, sentinels and handle-free dimension zero. The dyadic fixtures have known
nonzero canonical pivots. These regressions do not assert a formal Float error model.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev BlockState := St Unit Float (ℕ × ℕ × ℕ)

private def runWith (I : Interp Unit Unit Float (ℕ × ℕ × ℕ))
    (n b A L U ao lo uo : ℕ) (buffers : List (Array (Option Float))) : Option BlockState :=
  exec I (blockedLuFactor () (.const n) (.const b) (.const ((n + b - 1) / b)) A L U
    (.const ao) (.const lo) (.const uo)).run (initState buffers)

private def run (n b A L U ao lo uo : ℕ)
    (buffers : List (Array (Option Float))) : Option BlockState :=
  runWith (floatIndexedInterp #[] []) n b A L U ao lo uo buffers

private def packRows (rows : Array (Array Float)) : Array Float :=
  let n := rows.size
  (List.range (n * n)).toArray.map fun t => (rows[t % n]!)[t / n]!

private def readCells (st : BlockState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def closeArray (actual expected : Array Float) : Bool :=
  actual.size == expected.size && (List.range actual.size).all fun i =>
    actual[i]!.isFinite && (actual[i]! - expected[i]!).abs ≤ 1e-10

private def multiply (n : ℕ) (L U : Array Float) : Array Float :=
  (List.range (n * n)).toArray.map fun t =>
    let i := t % n
    let j := t / n
    (List.range n).foldl (fun sum k => sum + L[i + n * k]! * U[k + n * j]!) 0

private def checkFactors (n : ℕ) (A : Array Float) (L U lo uo : ℕ)
    (result : Option BlockState) : Bool :=
  result.any fun st =>
    match readCells st L lo (n * n), readCells st U uo (n * n) with
    | some lower, some upper =>
      closeArray (multiply n lower upper) A && lower.all Float.isFinite &&
        upper.all Float.isFinite && (List.range n).all (fun i => lower[i + n * i]! == 1) &&
        (List.range (n * n)).all fun t =>
          (if t % n < t / n then lower[t]! == 0 else true) &&
            (if t / n < t % n then upper[t]! == 0 else true)
    | _, _ => false

private def factorMatches (result : Option BlockState) (b off : ℕ)
    (expected : Array Float) : Bool :=
  result.any fun st =>
    (readCells st b off expected.size).any fun actual => closeArray actual expected

private def scopeRestored (result : Option BlockState)
    (buffers : List (Array (Option Float))) : Bool :=
  result.any fun st => st.store.shape == (initState buffers).store.shape &&
    st.cur () == (initState buffers).cur () && st.curW == (initState buffers).curW &&
    st.pos .gaussian == 0 && st.pos .rademacher == 0 && st.pos .uniform == 0

private def standardBuffers (n : ℕ) (A : Array Float) : List (Array (Option Float)) :=
  [A.map some, Array.replicate (n * n) none, Array.replicate (n * n) none, #[some 701, some 709]]

private def standardRun (n b : ℕ) (A : Array Float) : Option BlockState :=
  run n b 0 1 2 0 0 0 (standardBuffers n A)

private def checkStandard (n b : ℕ) (A : Array Float) : Bool :=
  let result := standardRun n b A
  checkFactors n A 1 2 0 0 result && scopeRestored result (standardBuffers n A) &&
    result.any fun st => readCells st 0 0 A.size == some A &&
      readCells st 3 0 2 == some #[701, 709]

private def lower5 := packRows #[#[1, 0, 0, 0, 0], #[2, 1, 0, 0, 0],
  #[-1, 0.5, 1, 0, 0], #[0.5, -2, 1.5, 1, 0], #[-1.5, 1, 0.25, -0.5, 1]]
private def upper5 := packRows #[#[2, 1, -1, 3, 1], #[0, 4, 2, -1, 2],
  #[0, 0, 8, 2, -3], #[0, 0, 0, 16, 4], #[0, 0, 0, 0, 32]]
private def matrix5 := packRows #[#[2, 1, -1, 3, 1], #[4, 6, 0, 5, 4],
  #[-2, 1, 10, -1.5, -3], #[1, -7.5, 7.5, 22.5, -4], #[-3, 2.5, 5.5, -13, 29.75]]
#guard closeArray (multiply 5 lower5 upper5) matrix5

-- Widths two and three leave partial last panels; widths one/five/eight exercise the
-- scalar-width, one-full-panel and larger-than-matrix boundaries with the same canonical factors.
#guard checkStandard 5 1 matrix5
#guard checkStandard 5 2 matrix5
#guard checkStandard 5 3 matrix5
#guard checkStandard 5 5 matrix5
#guard checkStandard 5 8 matrix5
#guard factorMatches (standardRun 5 1 matrix5) 1 0 lower5
#guard factorMatches (standardRun 5 1 matrix5) 2 0 upper5
#guard factorMatches (standardRun 5 2 matrix5) 1 0 lower5
#guard factorMatches (standardRun 5 2 matrix5) 2 0 upper5
#guard factorMatches (standardRun 5 3 matrix5) 1 0 lower5
#guard factorMatches (standardRun 5 3 matrix5) 2 0 upper5
#guard factorMatches (standardRun 5 5 matrix5) 1 0 lower5
#guard factorMatches (standardRun 5 5 matrix5) 2 0 upper5
#guard factorMatches (standardRun 5 8 matrix5) 1 0 lower5
#guard factorMatches (standardRun 5 8 matrix5) 2 0 upper5

private def lower4 := packRows #[#[1, 0, 0, 0], #[2, 1, 0, 0],
  #[-1, 0.5, 1, 0], #[0.5, -2, 1.5, 1]]
private def upper4 := packRows #[#[2, 1, -1, 3], #[0, 4, 2, -1],
  #[0, 0, 8, 2], #[0, 0, 0, 16]]
private def matrix4 := packRows #[#[2, 1, -1, 3], #[4, 6, 0, 5],
  #[-2, 1, 10, -1.5], #[1, -7.5, 7.5, 22.5]]
#guard checkStandard 4 2 matrix4
#guard factorMatches (standardRun 4 2 matrix4) 1 0 lower4
#guard factorMatches (standardRun 4 2 matrix4) 2 0 upper4
#guard checkStandard 1 1 #[7]
#guard checkStandard 1 3 #[-7]

private def offsetBuffers : List (Array (Option Float)) :=
  [(#[101, 103] ++ matrix5 ++ #[109]).map some,
    #[some 201, some 203] ++ Array.replicate 25 none ++ #[some 209],
    #[some 301] ++ Array.replicate 25 none ++ #[some 309], #[some 701, some 709]]
private def offsetsRun := run 5 2 0 1 2 2 2 1 offsetBuffers
#guard checkFactors 5 matrix5 1 2 2 1 offsetsRun
#guard factorMatches offsetsRun 1 2 lower5
#guard factorMatches offsetsRun 2 1 upper5
#guard scopeRestored offsetsRun offsetBuffers
#guard offsetsRun.any fun st =>
  readCells st 0 0 28 == some (#[101, 103] ++ matrix5 ++ #[109]) &&
    st.store.read () 1 0 == some 201 && st.store.read () 1 1 == some 203 &&
    st.store.read () 1 27 == some 209 && st.store.read () 2 0 == some 301 &&
    st.store.read () 2 26 == some 309 && readCells st 3 0 2 == some #[701, 709]

-- Input is copied before either output is cleared. The first case has a shifted overlapping
-- source/lower window; the second has a source/upper window with the same offset.
private def aliasLowerBuffers : List (Array (Option Float)) :=
  [(#[101] ++ matrix4 ++ #[107, 109]).map some,
    #[some 301] ++ Array.replicate 16 none ++ #[some 309], #[some 701, some 709]]
private def aliasLowerRun := run 4 2 0 0 1 1 2 1 aliasLowerBuffers
#guard checkFactors 4 matrix4 0 1 2 1 aliasLowerRun
#guard factorMatches aliasLowerRun 0 2 lower4
#guard factorMatches aliasLowerRun 1 1 upper4
#guard scopeRestored aliasLowerRun aliasLowerBuffers
#guard aliasLowerRun.any fun st =>
  st.store.read () 0 0 == some 101 && st.store.read () 0 1 == some 2 &&
    st.store.read () 0 18 == some 109 && st.store.read () 1 0 == some 301 &&
    st.store.read () 1 17 == some 309 && readCells st 2 0 2 == some #[701, 709]

private def aliasUpperBuffers : List (Array (Option Float)) :=
  [(#[101] ++ matrix4 ++ #[109]).map some,
    #[some 201] ++ Array.replicate 16 none ++ #[some 209], #[some 701, some 709]]
private def aliasUpperRun := run 4 2 0 1 0 1 1 1 aliasUpperBuffers
#guard checkFactors 4 matrix4 1 0 1 1 aliasUpperRun
#guard factorMatches aliasUpperRun 1 1 lower4
#guard factorMatches aliasUpperRun 0 1 upper4
#guard scopeRestored aliasUpperRun aliasUpperBuffers
#guard aliasUpperRun.any fun st =>
  st.store.read () 0 0 == some 101 && st.store.read () 0 17 == some 109 &&
    st.store.read () 1 0 == some 201 && st.store.read () 1 17 == some 209 &&
    readCells st 2 0 2 == some #[701, 709]

-- Nonzero canonical pivots are needed even when the input is nonsingular.
#guard (standardRun 2 1 (packRows #[#[0, 1], #[1, 0]])).isNone
#guard (standardRun 1 2 #[0]).isNone

-- Zero dimension restores the store even with coincident invalid source/output handles and
-- an interpreter that rejects every scalar operation.
private def noScalarInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  let I := floatIndexedInterp #[] []
  { I with sem := { I.sem with
      lit := fun _ _ => none
      bin := fun _ _ _ _ => none
      un := fun _ _ _ => none
      cmp := fun _ _ _ _ => none
      convert := fun _ _ _ => none
      toNat := fun _ _ => none } }
private def emptyRun := runWith noScalarInterp 0 3 0 0 0 17 19 23 []
#guard scopeRestored emptyRun []
#guard emptyRun.any fun st => st.store.size == 0
#guard scopeRestored (run 0 2 17 23 29 31 37 41 []) []

end NLAlibTools
