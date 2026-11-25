/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.FloatIndex
import NLAlib.Matrix.Computation.PivotedLUFactors

/-!
# Runtime checks for actual rook and threshold LU

These execute the shared factorization engine and independently reconstruct both permutation
axes from the stored current-position swap logs. Matrix residuals, factor structure, sentinels,
workspace release, zero-safe division and invalid empty handles exercise the actual builders.
The Float example backend is not asserted to satisfy a formal arithmetic-error contract.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

private def word (st : St Unit Float (ℕ × ℕ × ℕ)) (b i : ℕ) : Float :=
  (st.store.read () b i).getD (0/0)

private def close (a b : Float) : Bool := a.isFinite && b.isFinite && (a-b).abs ≤ 1e-8

private def order (st : St Unit Float (ℕ × ℕ × ℕ)) (n b off : ℕ) : Option (Array ℕ) := do
  let mut a := Array.range n
  for i in [:n] do
    let w ← st.store.read () b (off+i)
    let j ← boundedFloatToNat w
    if j < i || n ≤ j || !close w j.toFloat then none
    else a := a.swapIfInBounds i j
  pure a

private def buffers (a : Array Float) (n : ℕ) : List (Array (Option Float)) :=
  [((#[101] ++ a ++ #[109]) : Array Float).map some,
    #[some 211] ++ Array.replicate (n*n) none ++ #[some 223],
    #[some 307] ++ Array.replicate (n*n) none ++ #[some 311],
    #[some 401] ++ Array.replicate n none ++ #[some 409],
    #[some 503] ++ Array.replicate n none ++ #[some 509]]

private def rook (n : ℕ) : Builder Unit Unit ℕ ℕ Unit :=
  rookPluqFactor () (.const n) 0 1 2 3 4 1 1 1 1 1

private def threshold (τ : ℚ) (n : ℕ) : Builder Unit Unit ℕ ℕ Unit :=
  thresholdPluqFactor () τ (.const n) 0 1 2 3 4 1 1 1 1 1

private def thresholdRow (τ : ℚ) (n : ℕ) : Builder Unit Unit ℕ ℕ Unit :=
  thresholdPluFactor () τ (.const n) 0 1 2 3 1 1 1 1

private def run (b : Builder Unit Unit ℕ ℕ Unit) (a : Array Float) (n : ℕ) :=
  exec (floatIndexedInterp #[] []) b.run (initState (buffers a n))

private def valid (a : Array Float) (n : ℕ) (rowOnly : Bool)
    (result : Option (St Unit Float (ℕ × ℕ × ℕ))) : Bool := result.any fun st => Id.run do
  if st.store.size != 5 || showBuf st 0 != (#[101] ++ a ++ #[109]).toList then return false
  if !close (word st 1 0) 211 || !close (word st 1 (n*n+1)) 223 ||
      !close (word st 2 0) 307 || !close (word st 2 (n*n+1)) 311 ||
      !close (word st 3 0) 401 || !close (word st 3 (n+1)) 409 ||
      !close (word st 4 0) 503 || !close (word st 4 (n+1)) 509 then return false
  let some rows := order st n 3 1 | return false
  let some cols := if rowOnly then some (Array.range n) else order st n 4 1 | return false
  for i in [:n] do
    if !close (word st 1 (1+i+n*i)) 1 then return false
    for j in [:n] do
      if i < j && !close (word st 1 (1+i+n*j)) 0 then return false
      if j < i && !close (word st 2 (1+i+n*j)) 0 then return false
      let mut v : Float := 0
      for k in [:n] do v := v + word st 1 (1+i+n*k) * word st 2 (1+k+n*j)
      if !close v (a[rows[i]! + n*cols[j]!]!) then return false
  return true

private def logEq (result : Option (St Unit Float (ℕ × ℕ × ℕ))) (b : ℕ)
    (expected : List Float) : Bool := result.any fun st =>
  (List.range expected.length).all fun i => close (word st b (1+i)) expected[i]!

private def growth : Array Float := #[1,2,0, 9,0,10, 0,5,6]
private def dense : Array Float := #[2,1,4, 0,1,2, 1,2,3]
private def singular : Array Float := #[1,2,3, 2,4,6, 3,6,9]
private def zeroColumn : Array Float := #[0,0,0, 1,2,3, 2,1,4]
private def activeZero : Array Float := #[0,0,0,0,5,0,0,0,0]
private def ties : Array Float := #[3,2,0, 0,7,0, 5,7,0]

#guard valid growth 3 false (run (rook 3) growth 3)
#guard logEq (run (rook 3) growth 3) 3 [2,2,2]
#guard logEq (run (rook 3) growth 3) 4 [1,2,2]
#guard valid dense 3 false (run (rook 3) dense 3)
#guard valid singular 3 false (run (rook 3) singular 3)
#guard valid zeroColumn 3 false (run (rook 3) zeroColumn 3)
#guard valid activeZero 3 false (run (rook 3) activeZero 3)
#guard valid ties 3 false (run (rook 3) ties 3)
#guard valid #[0,0,0,0] 2 false (run (rook 2) #[0,0,0,0] 2)
#guard valid #[-7] 1 false (run (rook 1) #[-7] 1)
#guard valid #[] 0 false (run (rook 0) #[] 0)

private def equality : Array Float := #[1,2,1,3]
#guard valid equality 2 false (run (threshold (1/2) 2) equality 2)
#guard logEq (run (threshold (1/2) 2) equality 2) 3 [0,1]
#guard (run (threshold (1/2) 2) equality 2).any (fun st => close (word st 1 2) 2)
#guard valid equality 2 false (run (threshold (3/4) 2) equality 2)
#guard logEq (run (threshold (3/4) 2) equality 2) 3 [1,1]
#guard logEq (run (threshold (1/2) 2) equality 2) 4 [0,1]
#guard valid dense 3 false (run (threshold 1 3) dense 3)
#guard valid singular 3 false (run (threshold (1/2) 3) singular 3)
#guard valid zeroColumn 3 false (run (threshold (1/2) 3) zeroColumn 3)
#guard valid activeZero 3 false (run (threshold (1/2) 3) activeZero 3)
#guard valid equality 2 true (run (thresholdRow (1/2) 2) equality 2)
#guard valid dense 3 true (run (thresholdRow 1 3) dense 3)
#guard valid singular 3 true (run (thresholdRow (1/2) 3) singular 3)
#guard valid zeroColumn 3 true (run (thresholdRow (1/2) 3) zeroColumn 3)
#guard valid #[] 0 true (run (thresholdRow (1/2) 0) #[] 0)

private def noDiv : Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatIndexedInterp #[] [] with sem :=
    { (floatIndexedInterp #[] []).sem with bin := fun p op a b => match op with
      | .div => none
      | _ => (floatIndexedInterp #[] []).sem.bin p op a b } }
#guard valid #[0,0,0,0] 2 false
  (exec noDiv (rook 2).run (initState (buffers #[0,0,0,0] 2)))
#guard valid #[0,0,0,0] 2 true
  (exec noDiv (thresholdRow (1/2) 2).run (initState (buffers #[0,0,0,0] 2)))

-- Invalid external outputs coincide with the fresh scoped Hc=0 on the first empty call.
#guard (exec (floatIndexedInterp #[] [])
  (thresholdPluFactor () (1/2) 0 17 0 23 29 101 103 107 109).run (initState [])).any
  (fun st => st.store.isEmpty)
#guard (exec (floatIndexedInterp #[] [])
  (thresholdPluFactor () (1/2) 0 19 17 23 29 101 103 107 109).run (initState [])).any
  (fun st => st.store.isEmpty)
#guard (exec (floatIndexedInterp #[] [])
  (rookPluqFactor () 0 11 17 23 29 31 101 103 107 109 113).run (initState [])).any
  (fun st => st.store.isEmpty)

end NLAlibTools
