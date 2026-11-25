/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.TrailingSchurUpdate

/-!
# Executable checks of the packed trailing Schur update

The actual builder is checked against an independent sum over original source snapshots.
Full buffers may alias or overlap at different offsets. Every output cell is initialized,
every exterior matrix entry and outside store cell is retained, and scoped scratch is released.
Observed arithmetic counts distinguish one bulk GEMM from repeated rank-one updates.
These finite Float regressions do not certify a universal scalar accuracy or cost model.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private abbrev TrailingState := St Unit Float (ℕ × ℕ × ℕ)

private def trailingRead (st : TrailingState) (b off len : ℕ) : Option (Array Float) :=
  (List.range len).toArray.mapM fun i => st.store.read () b (off + i)

private def trailingRun (n start width L U R lo uo ro : ℕ)
    (bufs : List (Array (Option Float))) : Option TrailingState :=
  exec (floatIndexedInterp #[] [])
    (trailingSchurUpdate () (.const n) (.const start) (.const width) L U R
      (.const lo) (.const uo) (.const ro)).run (initState bufs)

private def trailingReference (n start width : ℕ) (F G M : Array Float) (i j : ℕ) : Float :=
  if start + width ≤ i && start + width ≤ j then
    M[i + n * j]! - (List.range width).foldl
      (fun sum t => sum + F[i + n * (start + t)]! * G[start + t + n * j]!) 0
  else M[i + n * j]!

private def trailingFrame (before after : TrailingState) (n R ro : ℕ) : Bool :=
  before.store.size == after.store.size && before.store.shape == after.store.shape &&
    before.cur () == after.cur () && before.curW == after.curW &&
    before.pos .gaussian == after.pos .gaussian &&
    before.pos .rademacher == after.pos .rademacher && before.pos .uniform == after.pos .uniform &&
    (List.range before.store.size).all fun b =>
      (List.range ((before.store[b]!).2.size)).all fun i =>
        if b == R && ro ≤ i && i < ro + n * n then true
        else after.store.read () b i == before.store.read () b i

private def trailingCheck (n start width L U R lo uo ro : ℕ)
    (bufs : List (Array (Option Float))) : Bool :=
  let before := initState bufs
  let m := n - (start + width)
  match trailingRead before L lo (n * n), trailingRead before U uo (n * n),
      trailingRead before R ro (n * n), trailingRun n start width L U R lo uo ro bufs with
  | some F, some G, some M, some out =>
    start + width ≤ n && (trailingRead out R ro (n * n)).any fun M' =>
      M'.size == n * n && M'.all Float.isFinite &&
        (List.range (n * n)).all (fun t =>
          let i := t % n
          let j := t / n
          (M'[t]! - trailingReference n start width F G M i j).abs ≤ 1e-10 &&
            (if i < start + width || j < start + width then M'[t]! == M[t]! else true)) &&
        trailingFrame before out n R ro &&
        out.cnt.1 == (if width == 0 then 0 else m * m * (2 * width + 1)) &&
        before.peak () + (m * width + width * m + m * m) ≤ out.peak ()
  | _, _, _, _ => false

private def trailingF (n : ℕ) : Array Float :=
  (List.range (n * n)).toArray.map fun t => Float.ofInt (Int.ofNat ((t % n + 3 * (t / n)) % 7) - 3)
private def trailingG (n : ℕ) : Array Float :=
  (List.range (n * n)).toArray.map fun t => Float.ofInt (Int.ofNat ((2 * (t % n) + t / n) % 5) - 2)
private def trailingM (n : ℕ) : Array Float :=
  (List.range (n * n)).toArray.map fun t => Float.ofInt (Int.ofNat (t + 1) - 4)

private def trailingSeparate (n start width lo uo ro : ℕ) : Bool :=
  trailingCheck n start width 0 1 2 lo uo ro
    [Array.replicate lo (some 101) ++ (trailingF n).map some ++ #[some 109],
      Array.replicate uo (some 201) ++ (trailingG n).map some ++ #[some 209],
      Array.replicate ro (some 301) ++ (trailingM n).map some ++ #[some 309],
      #[some 701, none, some 709]]

#guard trailingSeparate 2 0 1 0 0 0
#guard trailingSeparate 3 0 1 0 0 0
#guard trailingSeparate 3 1 1 0 0 0
#guard trailingSeparate 4 0 2 0 0 0
#guard trailingSeparate 5 1 2 0 0 0
#guard trailingSeparate 5 2 1 0 0 0
#guard trailingSeparate 1 0 0 0 0 0
#guard trailingSeparate 1 0 1 0 0 0
#guard trailingSeparate 3 0 0 0 0 0
#guard trailingSeparate 3 3 0 0 0 0
#guard trailingSeparate 3 1 2 0 0 0
#guard trailingSeparate 0 0 0 0 0 0
#guard trailingSeparate 3 0 1 2 1 3
#guard trailingSeparate 5 1 2 1 2 4
#guard trailingCheck 3 0 1 0 0 1 0 0 0 [(trailingF 3).map some, (trailingM 3).map some]
#guard trailingCheck 3 0 1 0 1 0 0 0 0 [(trailingF 3).map some, (trailingG 3).map some]
#guard trailingCheck 3 0 1 0 1 1 0 0 0 [(trailingF 3).map some, (trailingG 3).map some]
#guard trailingCheck 3 0 1 0 0 0 0 0 0 [(trailingF 3).map some]
#guard trailingCheck 3 0 1 0 0 0 0 1 2
  [((List.range 15).toArray.map fun i => some (Float.ofNat (i + 1)))]
#guard trailingCheck 0 0 0 17 23 42 9 11 13 []

private def trailingNoArithmetic : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem := { floatSem with bin := fun _ _ _ _ => none } }
private def trailingNoArithmeticRun (n start width : ℕ) : Option TrailingState :=
  exec trailingNoArithmetic (trailingSchurUpdate () (.const n) (.const start) (.const width)
    0 1 2 0 0 0).run (initState [(trailingF n).map some, (trailingG n).map some,
      (trailingM n).map some])
#guard (trailingNoArithmeticRun 3 0 0).isSome
#guard (trailingNoArithmeticRun 3 1 2).isSome
#guard (trailingNoArithmeticRun 3 0 1).isNone
#guard (trailingRun 5 1 2 0 1 2 0 0 0
  [(trailingF 5).map some, (trailingG 5).map some, (trailingM 5).map some]).any fun out =>
    out.cnt.1 == 20
#guard (trailingRun 2 0 1 0 0 0 0 0 0 [#[some 11, some 12, some 13, some 14]]).any fun out =>
  trailingRead out 0 0 4 == some #[11, 12, 13, -142]

end NLAlibTools
