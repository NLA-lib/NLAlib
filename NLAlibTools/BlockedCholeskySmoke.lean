/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.BlockedCholesky

/-!
# Executable checks of blocked Cholesky

Actual blocked LU, pivot square roots and lower-column scaling are tested against independent
Gram reconstruction. Fixtures cover block widths, partial panels, offsets, source/output
overlap and handle-free empty execution. These finite Float regressions do not certify a
universal floating-point accuracy model.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev CholState := St Unit Float (ℕ × ℕ × ℕ)

private def cholRunWith (I : Interp Unit Unit Float (ℕ × ℕ × ℕ))
    (n b A ao L lo : ℕ) (bufs : List (Array (Option Float))) : Option CholState :=
  exec I (blockedCholesky () (.const n) (.const b) (.const ((n + b - 1) / b)) A
    (.const ao) L (.const lo)).run (initState bufs)

private def cholRun (n b A ao L lo : ℕ)
    (bufs : List (Array (Option Float))) : Option CholState :=
  cholRunWith (floatIndexedInterp #[] []) n b A ao L lo bufs

private def cholRead (st : CholState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def cholGram (n : ℕ) (L : Array Float) : Array Float :=
  (List.range (n * n)).toArray.map fun t =>
    let i := t % n
    let j := t / n
    (List.range n).foldl (fun sum k => sum + L[i + n * k]! * L[j + n * k]!) 0

private def cholClose (actual expected : Array Float) : Bool :=
  actual.size == expected.size && (List.range actual.size).all fun i =>
    actual[i]!.isFinite && (actual[i]! - expected[i]!).abs ≤ 1e-9

private def cholFrame (before after : CholState) (n L lo : ℕ) : Bool :=
  before.store.size == after.store.size && before.store.shape == after.store.shape &&
    before.cur () == after.cur () && before.curW == after.curW &&
    before.pos .gaussian == after.pos .gaussian &&
    before.pos .rademacher == after.pos .rademacher && before.pos .uniform == after.pos .uniform &&
    (List.range before.store.size).all fun b =>
      (List.range ((before.store[b]!).2.size)).all fun i =>
        if b == L && lo ≤ i && i < lo + n * n then true
        else after.store.read () b i == before.store.read () b i

private def cholCheck (n b A ao L lo : ℕ) (bufs : List (Array (Option Float))) : Bool :=
  let before := initState bufs
  match cholRead before A ao (n * n), cholRun n b A ao L lo bufs with
  | some M, some out => (cholRead out L lo (n * n)).any fun factor =>
    cholClose (cholGram n factor) M && factor.all Float.isFinite &&
      (List.range n).all (fun j => 0 < factor[j + n * j]!) &&
      (List.range (n * n)).all (fun t => if t % n < t / n then factor[t]! == 0 else true) &&
      cholFrame before out n L lo
  | _, _ => false

private def cholLower (n : ℕ) : Array Float :=
  (List.range (n * n)).toArray.map fun t =>
    let i := t % n
    let j := t / n
    if i < j then 0 else if i == j then Float.ofNat (j + 2)
    else Float.ofInt (Int.ofNat ((2 * i + j) % 7) - 3) / 2

private def cholSeparate (n b ao lo : ℕ) : Bool :=
  let M := cholGram n (cholLower n)
  cholCheck n b 0 ao 1 lo
    [Array.replicate ao (some 101) ++ M.map some ++ #[some 109],
      Array.replicate lo (some 201) ++ Array.replicate (n * n) none ++ #[some 209],
      #[some 701, none, some 709]]

#guard cholSeparate 5 1 0 0
#guard cholSeparate 5 2 0 0
#guard cholSeparate 5 3 0 0
#guard cholSeparate 5 5 0 0
#guard cholSeparate 5 8 0 0
#guard cholSeparate 4 2 0 0
#guard cholSeparate 3 2 0 0
#guard cholSeparate 2 1 0 0
#guard cholSeparate 1 1 0 0
#guard cholSeparate 1 3 0 0
#guard cholSeparate 0 3 0 0
#guard cholSeparate 5 2 2 3
#guard cholSeparate 4 3 1 2
#guard cholSeparate 3 8 3 1
#guard cholSeparate 5 2 2 1

private def cholMatches (n b : ℕ) : Bool :=
  (cholRun n b 0 0 1 0 [(cholGram n (cholLower n)).map some,
    Array.replicate (n * n) none]).any fun st =>
      (cholRead st 1 0 (n * n)).any fun L => cholClose L (cholLower n)
#guard cholMatches 5 1
#guard cholMatches 5 2
#guard cholMatches 5 3
#guard cholMatches 5 8
#guard cholMatches 1 3

private def cholOverlap (n b ao lo : ℕ) : Bool :=
  let M := cholGram n (cholLower n)
  let extra := lo + n * n - (ao + n * n)
  let buf := Array.replicate ao (some 101) ++ M.map some ++
    Array.replicate extra none ++ #[some 109]
  cholCheck n b 0 ao 0 lo [buf, #[some 701, none, some 709]]
#guard cholOverlap 5 2 0 0
#guard cholOverlap 5 3 1 2
#guard cholOverlap 4 2 3 1
#guard cholOverlap 3 8 2 2
#guard cholOverlap 1 2 0 1

private def cholNoScalar : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  let I := floatIndexedInterp #[] []
  { I with sem := { I.sem with
      lit := fun _ _ => none
      bin := fun _ _ _ _ => none
      un := fun _ _ _ => none
      cmp := fun _ _ _ _ => none
      convert := fun _ _ _ => none
      toNat := fun _ _ => none } }
#guard (cholRunWith cholNoScalar 0 3 0 17 0 19 []).any fun st => st.store.size == 0
#guard (cholRunWith cholNoScalar 0 3 17 23 0 29 []).any fun st => st.store.size == 0
#guard (cholRun 0 8 23 29 37 41 []).any fun st => st.store.size == 0
#guard (cholRun 1 2 0 0 1 0 [#[some (-1)], #[none]]).isNone
#guard (cholRun 1 2 0 0 1 0 [#[some 0], #[none]]).isNone
#guard (cholRun 2 1 0 0 1 0 [#[some 0, some 1, some 1, some 0],
  Array.replicate 4 none]).isNone

end NLAlibTools
