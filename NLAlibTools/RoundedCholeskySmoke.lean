/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.CholeskyFactorization

/-!
# Executable checks for input-margin rounded Cholesky

The actual stored builder runs with biased square roots, divisions, products, sums and negative
literals. Zero literals stay exact. Independent Gram reconstruction checks the quantitative
input-margin allowance, triangular zeros and positive diagonal. Complete original-buffer frames
cover offsets, overlapping input/output and released scratch. These finite examples do not
assert a universal accuracy theorem for native Float operations.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev CholState := St Unit Float (ℕ × ℕ × ℕ)

private def perturbedCholeskyInterp : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := { floatSem with
      lit := fun p q => (floatSem.lit p q).map fun x => if q < 0 then x * 1.000001 else x
      bin := fun p op x y => match op with
        | .add | .mul | .div => (floatSem.bin p op x y).map fun z => z * 1.000001
        | _ => floatSem.bin p op x y
      un := fun p op x => match op with
        | .sqrt => (floatSem.un p op x).map fun z => z * 1.000001
        | _ => floatSem.un p op x } }

private def readCholCells (st : CholState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def cholPackRows (rows : Array (Array Float)) : Array Float :=
  let n := rows.size
  (List.range (n * n)).toArray.map fun t => (rows[t % n]!)[t / n]!

private def cholRoundoff : Float := 0.0000010001

private def terminalError (n : ℕ) (scale margin : Float) : Float :=
  let ratio := scale / margin
  let c := 1 + 6 * ratio + 2 * ratio * ratio
  let d := cholRoundoff * scale * (2 + 80 * ratio)
  (List.range n).foldl (fun old _ => c * old + d) 0

private def backwardBudget (n : ℕ) (scale margin : Float) : Float :=
  let e := (2 * (1 + scale / margin) * terminalError n scale margin +
    16 * cholRoundoff * scale) / margin.sqrt
  let δ := Float.ofNat n * e
  δ * (2 * scale.sqrt + δ)

-- Gershgorin row intervals independently check the chosen spectral input band in these cases.
private def spectralBand (n : ℕ) (A : Array Float) (scale margin : Float) : Bool :=
  0 < margin && margin ≤ scale && (List.range n).all fun i =>
    let off := (List.range n).foldl
      (fun sum j => if i == j then sum else sum + A[i + n * j]!.abs) 0
    margin ≤ A[i + n * i]! - off && A[i + n * i]! + off ≤ scale &&
      (List.range n).all fun j => A[i + n * j]! == A[j + n * i]!

private def cholResidual (n : ℕ) (A L : Array Float) (i j : ℕ) : Float :=
  A[i + n * j]! - (List.range n).foldl
    (fun sum k => sum + L[i + n * k]! * L[j + n * k]!) 0

private def cholResidualFrob (n : ℕ) (A L : Array Float) : Float :=
  ((List.range (n * n)).foldl (fun sum t =>
    let r := cholResidual n A L (t % n) (t / n)
    sum + r * r) 0).sqrt

private def cholFrameOK (before after : CholState) (n L lo : ℕ) : Bool :=
  before.store.size == after.store.size && before.store.shape == after.store.shape &&
    before.cur () == after.cur () && before.curW == after.curW &&
    before.pos .gaussian == after.pos .gaussian &&
    before.pos .rademacher == after.pos .rademacher &&
    before.pos .uniform == after.pos .uniform &&
    (List.range before.store.size).all fun b =>
      (List.range ((before.store[b]!).2.size)).all fun i =>
        if b == L && lo ≤ i && i < lo + n * n then true
        else after.store.read () b i == before.store.read () b i

private def checkRoundedChol (n : ℕ) (A : Array Float) (scale margin : Float)
    (bufs : List (Array (Option Float))) (Ab ao L lo : ℕ) : Bool :=
  let before := initState bufs
  spectralBand n A scale margin && terminalError n scale margin < margin / 2 &&
    (exec perturbedCholeskyInterp (cholesky () (.const n) Ab (.const ao) L (.const lo)).run
      before).any fun out =>
      (readCholCells out L lo (n * n)).any fun words =>
        words.size == n * n && words.all Float.isFinite &&
          (List.range n).all (fun i => (0 : Float) < words[i + n * i]!) &&
          (List.range (n * n)).all (fun t => if t % n < t / n then words[t]! == 0 else true) &&
          cholResidualFrob n A words ≤ backwardBudget n scale margin + 1e-10 &&
          cholFrameOK before out n L lo

private def separate (n : ℕ) (A : Array Float) (scale margin : Float) (ao lo : ℕ) : Bool :=
  checkRoundedChol n A scale margin
    [Array.replicate ao (some 101) ++ A.map some ++ #[some 109],
      Array.replicate lo (some 201) ++ Array.replicate (n * n) none ++ #[some 209],
      #[some 701, none, some 709]] 0 ao 1 lo

private def denseChol := cholPackRows #[#[5, 1], #[1, 5]]
private def signedChol := cholPackRows #[#[5, -1], #[-1, 5]]
private def threeChol := cholPackRows #[#[5, 1, 0], #[1, 5, 1], #[0, 1, 5]]
private def fourChol := cholPackRows
  #[#[5, 0.25, -0.25, 0.25], #[0.25, 5, 0.25, -0.25],
    #[-0.25, 0.25, 5, 0.25], #[0.25, -0.25, 0.25, 5]]

#guard separate 2 denseChol 6 4 0 0
#guard separate 2 signedChol 6 4 0 0
#guard separate 3 threeChol 7 3 0 0
#guard separate 4 fourChol 5.75 4.25 0 0
#guard separate 1 #[4] 4 4 0 0
#guard separate 1 #[0.25] 0.25 0.25 0 0
#guard separate 0 #[] 1 1 0 0
#guard separate 2 denseChol 6 4 2 3
#guard separate 3 threeChol 7 3 1 4
#guard separate 4 fourChol 5.75 4.25 3 2
#guard checkRoundedChol 2 denseChol 6 4 [denseChol.map some] 0 0 0 0
#guard checkRoundedChol 3 threeChol 7 3 [threeChol.map some] 0 0 0 0
#guard checkRoundedChol 2 denseChol 6 4
  [((#[101] ++ denseChol ++ #[303, 909]).map some)] 0 1 0 2
#guard checkRoundedChol 2 signedChol 6 4
  [((#[101, 303] ++ signedChol ++ #[909]).map some)] 0 2 0 1
#guard checkRoundedChol 0 #[] 1 1 [] 17 9 23 11

-- A detectable nonzero Gram residual confirms that the arithmetic instrumentation is active.
#guard (exec perturbedCholeskyInterp (cholesky () 2 0 0 1 0).run
  (initState [denseChol.map some, Array.replicate 4 none])).any fun st =>
    (readCholCells st 1 0 4).any fun L => cholResidualFrob 2 denseChol L > 1e-6
#guard (exec perturbedCholeskyInterp (cholesky () 1 0 0 1 0).run
  (initState [#[some (-1)], #[none]])).isNone
#guard (exec perturbedCholeskyInterp (cholesky () 2 0 0 1 0).run
  (initState [#[some 1, some 2, some 2, some 1], Array.replicate 4 none])).isNone

end NLAlibTools
