/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Tools.Run
public meta import NLAlib.Ops.Tools.Run
public import NLAlib.Ops.Tools.Tables
public meta import NLAlib.Ops.Tools.Tables
public import NLAlib.Ops.Tools.Machines
public meta import NLAlib.Ops.Tools.Machines
public import NLAlib.Ops.Link
public meta import NLAlib.Ops.Link
public import NLAlib.Ops.Examples.Noisy
public meta import NLAlib.Ops.Examples.Noisy
public import NLAlib.Ops.Examples.Hutch
public meta import NLAlib.Ops.Examples.Hutch
public import NLAlib.Ops.Examples.CgsLinked
public meta import NLAlib.Ops.Examples.CgsLinked
public import NLAlib.Ops.Examples.Control
public meta import NLAlib.Ops.Examples.Control
public import NLAlib.Ops.Examples.Gemm
public meta import NLAlib.Ops.Examples.Gemm
public import NLAlib.Ops.Examples.GramSchmidt
public meta import NLAlib.Ops.Examples.GramSchmidt
public import NLAlib.Ops.Examples.HutchLinked
public meta import NLAlib.Ops.Examples.HutchLinked

/-!
# Tools: the evaluator on the test cases

Diagnostic and compute support; formal guarantees are independent of this output.
Each `#eval` runs a program of `NLAlib/Ops/Examples` on a small input
and prints the final memory, the counts per (operation, dimensions) of the run, its peak of
scratch payload bytes, and the static bounds `stmtCost`/`stmtPeak` of the tree. Programs are run at
the level of their algorithm (the operations of the catalog interpreted by
`NLAlib.Ops.Tools.blasFn` or `NLAlib.Ops.Tools.randFn`) and linked through the tables of the
profiles (`NLAlib.Ops.Tools.seqTable`, …), down to scalar operations and scalar draws.

Run with `lake env lean NLAlib/Ops/Tools/Demo.lean` (after building the imports).

## Main results

The executable examples replay raw conditional programs and display their diagnostic reports.
-/

@[expose] public section

namespace NLAlib.Ops.Tools.Demo

open NLAlib.Ops NLAlib.Ops.Examples NLAlib.Ops.Tools

/-- The signature of the BLAS profiles. -/
abbrev BOp := Blas1Op ⊕ ScalarOp

/-- The interpretation of the BLAS signature over a concrete carrier. -/
def blasI (K : Type) [Concrete K] : Interp BOp Qry K := withQueries blasFn

-- A comparison writes the flag and the branch reads it. The profiler counts both uses.
#eval profileFrame (withFlagTest (Interp.ofFns (Tst := FlagTst) (cmpOpFn (K := ℚ))))
  (fun _ _ => 0) (signTape 0) branchOnPositive [] [0] [[some 3, none]]

/-! ### `gemm`: `C = A B`, `A` 2 × 3 by rows, `B` 3 × 2 by columns -/

/-- `gemm` in the BLAS signature. -/
def gemmB : Stmt BOp Qry := gemm

/-- The buffers of `gemm`: `A`, `B`, and four cells for `C`. -/
def gemmBufs (K : Type) [Concrete K] : List (List (Option K)) :=
  [vals ((([1, 2, 3, 4, 5, 6] : List ℚ)).map (mach K).lit),
   vals (([1, 0, 1, 2, 1, 0] : List ℚ).map (mach K).lit), blank 4]

-- The algorithm: four calls of `dot` at the length 3.
#eval profileFrame (blasI ℚ) (fun _ _ => 0) (signTape 0) gemmB [2, 3, 2] [0, 1, 2] (gemmBufs ℚ)

-- Linked through `Blas.seq`: `m p n = 12` products and `m p (n - 1) = 8` additions
-- (`push_seq_gemmCount`), workspace `Blas.ws 0 dot [3] = 3`.
#eval profileFrame (blasI ℚ) (Blas.ws 0) (signTape 0) (gemmB.link seqTable) [2, 3, 2] [0, 1, 2]
  (gemmBufs ℚ)

-- Linked through `Blas.pairwise 3` (`⌈log₂ 3⌉ < 3`), in `Float`: 12 products, 8 additions,
-- 12 copies (`push_pairwise_gemmCount`).
#eval profileFrame (blasI Float) (Blas.ws Blas.pairWs) (signTape 0)
  (gemmB.link (pairwiseTable 3)) [2, 3, 2] [0, 1, 2] (gemmBufs Float)

/-! ### Pairwise summation: one call of `sum` at the length 8 -/

/-- `z := sum x` at the length `n` (the variable 0). -/
def sumCall : Stmt BOp Qry :=
  .call (Has.inj Blas1Op.sum) [.var 0] [⟨0, .const 0⟩] [⟨1, .const 0⟩]

/-- Eight numbers whose sequential sum in `Float` loses the small terms. -/
def sumBufs : List (List (Option Float)) :=
  [vals [1e16, 1, 1, 1, 1, 1, 1, -1e16], blank 1]

-- Depth 4 (`⌈log₂ 8⌉ < 4`): only scalar operations are left; 7 additions, 8 copies. The exact
-- sum is 6; pairwise summation gives 4.
#eval profileFrame (blasI Float) (Blas.ws Blas.pairWs) (signTape 0)
  (sumCall.link (pairwiseTable 4)) [8] [0, 1] sumBufs

-- Depth 1: one level, then the two halves are calls of `sum` interpreted directly.
#eval profileFrame (blasI Float) (Blas.ws Blas.pairWs) (signTape 0)
  (sumCall.link (pairwiseTable 1)) [8] [0, 1] sumBufs

-- Sequential, for comparison: every one is absorbed by `1e16`, the result is 0.
#eval profileFrame (blasI Float) (Blas.ws 0) (signTape 0) (sumCall.link seqTable) [8] [0, 1] sumBufs

/-! ### Modified Gram–Schmidt: `w` against two orthonormal columns -/

/-- `mgs` in the BLAS signature. -/
def mgsB : Stmt BOp Qry := mgs

/-- `Q = [e₁, e₂]` in `ℚ³` by columns, `w = (1, 2, 2)`, three cells for `R`. -/
def mgsBufs : List (List (Option ℚ)) := [vals [1, 0, 0, 0, 1, 0], vals [1, 2, 2], blank 3]

-- `w ↦ (0, 0, 2)`, `R = (1, 2, 2)`: two `dot`, two `neg`, two `axpy`, one `nrm2`.
#eval profileFrame (blasI ℚ) (fun _ _ => 0) (signTape 0) mgsB [3, 2] [0, 1, 1, 2] mgsBufs

#eval profileFrame (blasI ℚ) (Blas.ws 0) (signTape 0) (mgsB.link seqTable) [3, 2] [0, 1, 1, 2]
  mgsBufs

/-! ### Classical Gram–Schmidt: `A = [(3, 4, 0), (4, 3, 0)]` -/

/-- `cgs` in the BLAS signature. -/
def cgsB : Stmt BOp Qry := cgs

/-- `A` by columns, `R` (2 × 2, read and written), `Q`. Every norm is rational. -/
def cgsBufs : List (List (Option ℚ)) := [vals [3, 4, 0, 4, 3, 0], vals [0, 0, 0, 0], blank 6]

-- `Q = [(3/5, 4/5, 0), (4/5, -3/5, 0)]`, `R = [[5, 24/5], [0, 7/5]]` (by columns).
#eval profileFrame (blasI ℚ) (fun _ _ => 0) (signTape 0) cgsB [3, 2] [0, 1, 2, 1] cgsBufs

#eval profileFrame (blasI ℚ) (Blas.ws 0) (signTape 0) (cgsB.link seqTable) [3, 2] [0, 1, 2, 1]
  cgsBufs

/-! ### Rectangular matrix-vector products -/

private def runMatvec (A : List (List ℚ)) (m n : ℕ) (x : List ℚ) : Option (Mem ℚ) :=
  eval (withQueries (operatorFn A)) (fun _ _ => 0)
    (.call .matvec [.const m, .const n] [⟨0, .const 0⟩] [⟨1, .const 0⟩])
    (frameOf [] [0, 1]) (memOf [vals x, blank m])

example : runMatvec [[1, 2, 3], [4, 5, 6]] 2 3 [1, 2, 3] =
    some (memOf [vals [1, 2, 3], vals [14, 32]]) := by
  with_unfolding_all rfl

example : runMatvec [] 0 2 [1, 2] = some (memOf [vals [1, 2], []]) := rfl

example : runMatvec [[], []] 2 0 [] = some (memOf [[], vals [0, 0]]) := rfl

example : runMatvec [[1, 2], [3]] 2 2 [1, 2] = none := rfl

/-! ### Girard–Hutchinson with a fixed tape of signs -/

/-- A symmetric matrix of trace 9, by rows. -/
def hutchA : List (List ℚ) := [[2, 1, 0], [1, 3, 1], [0, 1, 4]]

/-- `hutch` over the random signature with the queries. -/
def hutchR : Stmt ROp Qry := hutch

-- Four probes of signs: the cell holds the sum of `gᵀ A g` (the estimate times `N`).
#eval profileFrame (withQueries (randFn hutchA)) (fun _ _ => 0) (signTape 7) hutchR [4, 3] [0, 0]
  [vals [0]]

-- Linked through `Rand.gaussLoop`: `N n = 12` scalar draws, tape position 12.
#eval profileFrame (withQueries (randFn hutchA)) (fun _ _ => 0) (signTape 7)
  (hutchR.link gaussTable) [4, 3] [0, 0] [vals [0]]

/-! ### The noisy power iteration -/

instance : ShowKey NOp := ⟨fun | .nmv => "nmv"⟩

/-- `npow` with the queries. -/
def npowR : Stmt NOp Qry := npow

/-- The noisy product `A x + σ ‖x‖ g` as an operation: the interpretation induced by its
implementation (`Interp.link`). -/
def nmvI (σ : ℚ) : Interp NOp Qry ℚ := (withQueries (randFn hutchA)).link (noisyTable σ)

-- The algorithm: `2 k = 4` noisy products; each reads a window of 3 signs.
#eval profileFrame (nmvI (1 / 10)) (fun _ _ => 4) (signTape 3) npowR [2, 3] [0, 0]
  [vals [1, 0, 0]]

-- Linked through `noisyDraws σ` (the noisy product, then the draws one by one).
#eval profileFrame (withQueries (randFn hutchA)) (fun _ _ => 0) (signTape 3)
  (npowR.link (noisyDrawsTable (1 / 10))) [2, 3] [0, 0] [vals [1, 0, 0]]

end NLAlib.Ops.Tools.Demo
