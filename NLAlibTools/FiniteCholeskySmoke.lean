/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.CholeskyFactorization

/-!
# Executable finite-range and additive-error Cholesky checks

The unchanged builder runs under a bounded tool backend with relative bias and a nonzero
additive floor, including nonzero results from exact zero arithmetic. Each exact native scalar
result is checked against a cap before perturbation. Independent input envelopes and Gram
reconstruction verify the mixed-error allowance on finite examples, with overlap, complete
store frames and failure cases for reciprocal overflow and square-root range.
These guards are executable regressions, not a universal native Float accuracy certificate or
an identification of the tool backend with the mathematical binary-format quantizer.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev RangeState := St Unit Float (ℕ × ℕ × ℕ)

private def rangeRounded (cap : Float) (x : Float) : Option Float :=
  if x.isFinite && decide (x.abs ≤ cap) then
    let z := x * 1.000001 + 0.0000001
    some (if cap < z then cap else if z < -cap then -cap else z)
  else none

private def rangeCholInterp (cap : Float) : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := { floatSem with
      lit := fun p q => if q == 0 then some 0 else
        (floatSem.lit p q).bind (rangeRounded cap)
      bin := fun p op x y => (floatSem.bin p op x y).bind (rangeRounded cap)
      un := fun p op x => match op with
        | .sqrt => (floatSem.un p op x).bind (rangeRounded cap)
        | _ => floatSem.un p op x } }

private def rangeRead (st : RangeState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def rangePack (rows : Array (Array Float)) : Array Float :=
  let n := rows.size
  (List.range (n * n)).toArray.map fun t => (rows[t % n]!)[t / n]!

private def rangeU : Float := 0.0000010001
private def rangeTau : Float := 0.00000010001

private def rangeLocalError (H m : Float) : Float :=
  let ell := 1 + rangeU + rangeTau
  let c := (1 + rangeU) * ell / m + rangeTau
  let t := (1 + rangeU) * c * H + rangeTau
  let q := (1 + rangeU) * H * t + rangeTau
  let ec := (rangeU + rangeTau) / m + rangeU * ell / m + rangeTau
  let et := H * ec + rangeU * c * H + rangeTau
  let eq := H * et + rangeU * H * t + rangeTau
  eq + rangeU * (H + q) + rangeTau

private def rangeTerminal (n : ℕ) (B μ : Float) : Float :=
  let ratio := B / μ
  (List.range n).foldl
    (fun old _ => (1 + 6 * ratio + 2 * ratio * ratio) * old + rangeLocalError (2 * B) (μ / 2)) 0

private def rangeAdmissible (n : ℕ) (B μ Ω : Float) : Bool :=
  let m := μ / 2
  let H := 2 * B
  let ell := 1 + rangeU + rangeTau
  let c := (1 + rangeU) * ell / m + rangeTau
  let t := (1 + rangeU) * c * H + rangeTau
  let q := (1 + rangeU) * H * t + rangeTau
  let d := (1 - rangeU) * m.sqrt - rangeTau
  0 < μ && μ ≤ B && rangeTerminal n B μ < μ / 2 && 0 < d && 1 ≤ Ω &&
    ell / m ≤ Ω && c * H ≤ Ω && H * t ≤ Ω && H + q ≤ Ω && H.sqrt ≤ Ω && H / d ≤ Ω

private def rangeBudget (n : ℕ) (B μ : Float) : Float :=
  let H := 2 * B
  let m := μ / 2
  let d := (1 - rangeU) * m.sqrt - rangeTau
  let e := 2 * (1 + B / μ) * rangeTerminal n B μ / μ.sqrt +
    (rangeU * H.sqrt + rangeTau) * (1 + H / (d * m.sqrt)) + rangeU * H / d + rangeTau
  let δ := Float.ofNat n * e
  δ * (2 * B.sqrt + δ)

private def rangeBand (n : ℕ) (A : Array Float) (B μ : Float) : Bool :=
  (List.range n).all fun i =>
    let off := (List.range n).foldl
      (fun sum j => if i == j then sum else sum + A[i + n * j]!.abs) 0
    μ ≤ A[i + n * i]! - off && A[i + n * i]! + off ≤ B &&
      (List.range n).all fun j => A[i + n * j]! == A[j + n * i]!

private def rangeResidual (n : ℕ) (A L : Array Float) : Float :=
  ((List.range (n * n)).foldl (fun sum t =>
    let i := t % n
    let j := t / n
    let r := A[t]! - (List.range n).foldl
      (fun value k => value + L[i + n * k]! * L[j + n * k]!) 0
    sum + r * r) 0).sqrt

private def rangeFrame (before after : RangeState) (n L lo : ℕ) : Bool :=
  before.store.size == after.store.size && before.store.shape == after.store.shape &&
    before.cur () == after.cur () && before.curW == after.curW &&
    before.pos .gaussian == after.pos .gaussian &&
    before.pos .rademacher == after.pos .rademacher && before.pos .uniform == after.pos .uniform &&
    (List.range before.store.size).all fun b =>
      (List.range ((before.store[b]!).2.size)).all fun i =>
        if b == L && lo ≤ i && i < lo + n * n then true
        else after.store.read () b i == before.store.read () b i

private def rangeCheck (n : ℕ) (A : Array Float) (B μ Ω : Float)
    (bufs : List (Array (Option Float))) (Ab ao L lo : ℕ) : Bool :=
  let before := initState bufs
  A.all (fun x => x.isFinite && decide (x.abs ≤ Ω)) && rangeBand n A B μ &&
    rangeAdmissible n B μ Ω &&
    (exec (rangeCholInterp Ω) (cholesky () (.const n) Ab (.const ao) L (.const lo)).run before).any
      fun out => (rangeRead out L lo (n * n)).any fun words =>
        words.all (fun x => x.isFinite && decide (x.abs ≤ Ω)) &&
          (List.range n).all (fun i => (0 : Float) < words[i + n * i]!) &&
          (List.range (n * n)).all (fun t => if t % n < t / n then words[t]! == 0 else true) &&
          rangeResidual n A words ≤ rangeBudget n B μ + 1e-10 && rangeFrame before out n L lo

private def rangeSeparate (n : ℕ) (A : Array Float) (B μ Ω : Float) (ao lo : ℕ) : Bool :=
  rangeCheck n A B μ Ω
    [Array.replicate ao (some 101) ++ A.map some ++ #[some 109],
      Array.replicate lo (some 201) ++ Array.replicate (n * n) none ++ #[some 209],
      #[some 701, none, some 709]] 0 ao 1 lo

private def rangeDense := rangePack #[#[5, 1], #[1, 5]]
private def rangeSigned := rangePack #[#[5, -1], #[-1, 5]]
private def rangeThree := rangePack #[#[5, 1, 0], #[1, 5, 1], #[0, 1, 5]]
private def rangeDiagonal : Array Float := #[4, 0, 0, 4]

#guard rangeSeparate 2 rangeDense 6 4 1000 0 0
#guard rangeSeparate 2 rangeSigned 6 4 1000 0 0
#guard rangeSeparate 3 rangeThree 7 3 1000 0 0
#guard rangeSeparate 2 rangeDiagonal 4 4 128 0 0
#guard rangeSeparate 1 #[4] 4 4 128 0 0
#guard rangeSeparate 1 #[0.25] 0.25 0.25 128 0 0
#guard rangeSeparate 0 #[] 1 1 128 0 0
#guard rangeSeparate 2 rangeDense 6 4 1000 2 3
#guard rangeSeparate 3 rangeThree 7 3 1000 1 4
#guard rangeCheck 2 rangeDense 6 4 1000 [rangeDense.map some] 0 0 0 0
#guard rangeCheck 2 rangeSigned 6 4 1000
  [((#[101] ++ rangeSigned ++ #[303, 909]).map some)] 0 1 0 2
#guard (exec (rangeCholInterp 128) (cholesky () 2 0 0 1 0).run
  (initState [rangeDiagonal.map some, Array.replicate 4 none])).any fun out =>
    out.store.read () 1 1 == some 0.0000001 && out.store.read () 1 2 == some 0 &&
      (rangeRead out 1 0 4).any fun words => rangeResidual 2 rangeDiagonal words > 1e-6
#guard !(rangeAdmissible 1 0.00000001 0.00000001 64)
#guard (exec (rangeCholInterp 64) (cholesky () 1 0 0 1 0).run
  (initState [#[some 0.00000001], #[none]])).isNone
#guard (exec (rangeCholInterp 0.25) (cholesky () 1 0 0 1 0).run
  (initState [#[some 0.25], #[none]])).isNone
#guard (exec (rangeCholInterp 128) (cholesky () 1 0 0 1 0).run
  (initState [#[some (-1)], #[none]])).isNone
#guard (exec (rangeCholInterp 128) (cholesky () 1 0 0 1 0).run
  (initState [#[some 0], #[none]])).isNone
#guard (exec (rangeCholInterp 0) (cholesky () 0 17 9 23 11).run (initState [])).isSome

end NLAlibTools
