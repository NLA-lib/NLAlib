/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.PivotedCholesky

/-!
# Executable checks of pivoted semidefinite Cholesky

The actual stored pivot log is independently replayed on both axes, and the decoded factor's
Gram matrix is compared with that permuted source snapshot. Exact dyadic fixtures cover late
factor-row swaps, nontrivial cycles, ties, singular inputs, zero-pivot guards, offsets, overlap
and empty invalid handles. These are finite Float tests, not a universal Float accuracy model.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev PivotCholState := St Unit Float (ℕ × ℕ × ℕ)

private def pivotCholRunWith (I : Interp Unit Unit Float (ℕ × ℕ × ℕ))
    (n A ao L lo H ho : ℕ) (bufs : List (Array (Option Float))) : Option PivotCholState :=
  exec I (pivotedCholesky () (.const n) A (.const ao) L (.const lo) H (.const ho)).run
    (initState bufs)

private def pivotCholRun (n A ao L lo H ho : ℕ)
    (bufs : List (Array (Option Float))) : Option PivotCholState :=
  pivotCholRunWith (floatIndexedInterp #[] []) n A ao L lo H ho bufs

private def pivotCholRead (st : PivotCholState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

-- The log records absolute CURRENT positions; replay it without the library permutation decoder.
private def pivotCholOrder (n : ℕ) (history : Array Float) : Option (Array ℕ) := do
  if history.size != n then none else
    (List.range n).foldlM (fun order k => do
      let word ← history[k]?
      let row ← boundedFloatToNat word
      if row < n && k ≤ row && word == Float.ofNat row then
        let oldK ← order[k]?
        let oldRow ← order[row]?
        some ((order.set! k oldRow).set! row oldK)
      else none) (List.range n).toArray

private def pivotCholGram (n : ℕ) (L : Array Float) (i j : ℕ) : Float :=
  (List.range n).foldl (fun sum k => sum + L[i + n * k]! * L[j + n * k]!) 0

private def pivotCholFrame (before after : PivotCholState) (n L lo H ho : ℕ) : Bool :=
  before.store.size == after.store.size && before.store.shape == after.store.shape &&
    before.cur () == after.cur () && before.curW == after.curW &&
    before.pos .gaussian == after.pos .gaussian &&
    before.pos .rademacher == after.pos .rademacher && before.pos .uniform == after.pos .uniform &&
    (List.range before.store.size).all fun b =>
      (List.range ((before.store[b]!).2.size)).all fun i =>
        if (b == L && lo ≤ i && i < lo + n * n) || (b == H && ho ≤ i && i < ho + n) then true
        else after.store.read () b i == before.store.read () b i

private def pivotCholCheck (n A ao L lo H ho : ℕ)
    (bufs : List (Array (Option Float))) : Bool :=
  let before := initState bufs
  match pivotCholRead before A ao (n * n), pivotCholRun n A ao L lo H ho bufs with
  | some M, some out =>
    match pivotCholRead out L lo (n * n), pivotCholRead out H ho n with
    | some factor, some history => (pivotCholOrder n history).any fun order =>
      factor.all Float.isFinite && (List.range n).all (fun i => 0 ≤ factor[i + n * i]!) &&
        (List.range (n * n)).all (fun t =>
          let i := t % n
          let j := t / n
          (if i < j then factor[t]! == 0 else true) &&
            (pivotCholGram n factor i j - M[order[i]! + n * order[j]!]!).abs ≤ 1e-10) &&
        pivotCholFrame before out n L lo H ho
    | _, _ => false
  | _, _ => false

private def pivotCholPack (rows : Array (Array Float)) : Array Float :=
  let n := rows.size
  (List.range (n * n)).toArray.map fun t => (rows[t % n]!)[t / n]!

private def pivotCholStandard (n : ℕ) (M : Array Float) : List (Array (Option Float)) :=
  [M.map some, Array.replicate (n * n) none, Array.replicate n none, #[some 701, none, some 709]]

private def pivotCholSeparate (n : ℕ) (M : Array Float) : Bool :=
  pivotCholCheck n 0 0 1 0 2 0 (pivotCholStandard n M)

private def pivotCholCycle := pivotCholPack #[#[2.25, 1.5, 2.5], #[1.5, 9, 3], #[2.5, 3, 5]]
private def pivotCholRankOne := pivotCholPack #[#[1, 2, 4], #[2, 4, 8], #[4, 8, 16]]
private def pivotCholRankTwo := pivotCholPack #[#[16, 4, 2], #[4, 5, 2.5], #[2, 2.5, 1.25]]
private def pivotCholDiagonal := pivotCholPack #[#[0, 0, 0], #[0, 4, 0], #[0, 0, 1]]
private def pivotCholTies := pivotCholPack #[#[4, 0, 0], #[0, 4, 0], #[0, 0, 1]]

#guard pivotCholSeparate 3 pivotCholCycle
#guard pivotCholSeparate 3 pivotCholRankOne
#guard pivotCholSeparate 3 pivotCholRankTwo
#guard pivotCholSeparate 3 pivotCholDiagonal
#guard pivotCholSeparate 3 pivotCholTies
#guard pivotCholSeparate 3 (Array.replicate 9 0)
#guard pivotCholSeparate 4 (pivotCholPack
  #[#[1, 0, 0, 0], #[0, 16, 0, 0], #[0, 0, 4, 0], #[0, 0, 0, 0]])
#guard pivotCholSeparate 2 (pivotCholPack #[#[4, 2], #[2, 1]])
#guard pivotCholSeparate 1 #[9]
#guard pivotCholSeparate 1 #[0]
#guard pivotCholSeparate 0 #[]

private def pivotCholMatches (M expectedL expectedLog : Array Float) : Bool :=
  (pivotCholRun 3 0 0 1 0 2 0 (pivotCholStandard 3 M)).any fun out =>
    pivotCholRead out 1 0 9 == some expectedL && pivotCholRead out 2 0 3 == some expectedLog
#guard pivotCholMatches pivotCholCycle #[3, 1, 0.5, 0, 2, 1, 0, 0, 1] #[1, 2, 2]
#guard pivotCholMatches pivotCholRankOne #[4, 2, 1, 0, 0, 0, 0, 0, 0] #[2, 1, 2]
#guard pivotCholMatches pivotCholDiagonal #[2, 0, 0, 0, 1, 0, 0, 0, 0] #[1, 2, 2]
#guard pivotCholMatches pivotCholTies #[2, 0, 0, 0, 2, 0, 0, 0, 1] #[0, 1, 2]
#guard pivotCholOrder 3 #[1, 2, 2] == some #[1, 2, 0]
#guard (pivotCholOrder 3 #[1, 0, 2]).isNone
#guard (pivotCholOrder 3 #[1, 1.5, 2]).isNone
#guard (pivotCholOrder 3 #[1, 2, 3]).isNone

private def pivotCholOffsets : List (Array (Option Float)) :=
  [(#[101, 103] ++ pivotCholCycle ++ #[109]).map some,
    #[some 201] ++ Array.replicate 9 none ++ #[some 209],
    #[some 301, some 303] ++ Array.replicate 3 none ++ #[some 309],
    #[some 701, none, some 709]]
#guard pivotCholCheck 3 0 2 1 1 2 2 pivotCholOffsets
#guard pivotCholCheck 3 0 1 0 2 1 1
  [(#[101] ++ pivotCholCycle ++ #[107, 109]).map some,
    #[some 301] ++ Array.replicate 3 none ++ #[some 309], #[some 701, none, some 709]]
#guard pivotCholCheck 3 0 1 1 2 0 2
  [(#[101] ++ pivotCholCycle ++ #[109]).map some,
    #[some 201, some 203] ++ Array.replicate 9 none ++ #[some 209],
    #[some 701, none, some 709]]
#guard pivotCholCheck 3 0 0 0 0 1 0
  [pivotCholCycle.map some, Array.replicate 3 none, #[some 701, none, some 709]]
#guard pivotCholCheck 3 0 0 1 0 0 0
  [pivotCholCycle.map some, Array.replicate 9 none, #[some 701, none, some 709]]

private def pivotCholNoDivSqrt : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  let I := floatIndexedInterp #[] []
  { I with sem := { I.sem with
      bin := fun p op x y => match op with
        | .div => none
        | _ => I.sem.bin p op x y
      un := fun p op x => match op with
        | .sqrt => none
        | _ => I.sem.un p op x } }
#guard (pivotCholRunWith pivotCholNoDivSqrt 3 0 0 1 0 2 0
  (pivotCholStandard 3 (Array.replicate 9 0))).isSome
#guard (pivotCholRunWith pivotCholNoDivSqrt 3 0 0 1 0 2 0
  (pivotCholStandard 3 pivotCholCycle)).isNone

private def pivotCholNoScalar : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  let I := floatIndexedInterp #[] []
  { I with sem := { I.sem with
      lit := fun _ _ => none
      bin := fun _ _ _ _ => none
      un := fun _ _ _ => none
      cmp := fun _ _ _ _ => none
      convert := fun _ _ _ => none
      toNat := fun _ _ => none } }
#guard (pivotCholRunWith pivotCholNoScalar 0 0 17 0 19 0 23 []).any fun st => st.store.size == 0
#guard (pivotCholRunWith pivotCholNoScalar 0 17 23 0 29 1 31 []).any fun st => st.store.size == 0
#guard (pivotCholRunWith pivotCholNoScalar 0 17 23 1 29 1 31 [#[some 701, none, some 709]]).any
  fun st => st.store.read () 0 0 == some 701 && st.store.read () 0 1 == none &&
    st.store.read () 0 2 == some 709 && st.store.size == 1
#guard (pivotCholRun 1 0 0 1 0 2 0 [#[some (-1)], #[none], #[none]]).isNone

end NLAlibTools
