/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public meta import NLAlib.Ops.Tools.Lint
public import NLAlib.Ops.Attr
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Blas.Dot
public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Blas.Sum
public import NLAlib.Ops.BlockRel
public import NLAlib.Ops.Blocks
public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Catalog.Isotropic
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Catalog.Random
public import NLAlib.Ops.Catalog.Scalar
public import NLAlib.Ops.Catalog.Tagged
public import NLAlib.Ops.Cert
public import NLAlib.Ops.Contract
public import NLAlib.Ops.Counted
public import NLAlib.Ops.Examples.Bilinear
public import NLAlib.Ops.Examples.Certification
public import NLAlib.Ops.Examples.Resources
public import NLAlib.Ops.Examples.Bits
public import NLAlib.Ops.Examples.Built
public import NLAlib.Ops.Examples.Cgs
public import NLAlib.Ops.Examples.CgsLinked
public import NLAlib.Ops.Examples.CgsMath
public import NLAlib.Ops.Examples.CgsQR
public import NLAlib.Ops.Examples.CgsWrites
public import NLAlib.Ops.Examples.Control
public import NLAlib.Ops.Examples.Dot
public import NLAlib.Ops.Examples.Gemm
public import NLAlib.Ops.Examples.GramSchmidt
public import NLAlib.Ops.Examples.Hutch
public import NLAlib.Ops.Examples.HutchLinked
public import NLAlib.Ops.Examples.Liberal
public import NLAlib.Ops.Examples.Loops
public import NLAlib.Ops.Examples.MatMul
public import NLAlib.Ops.Examples.Mixed
public import NLAlib.Ops.Examples.Noisy
public import NLAlib.Ops.Examples.NoisyLinked
public import NLAlib.Ops.Examples.NoisyMath
public import NLAlib.Ops.Examples.RandomWitness
public import NLAlib.Ops.Examples.Split
public import NLAlib.Ops.Examples.StochRound
public import NLAlib.Ops.Exec
public import NLAlib.Ops.Frame
public import NLAlib.Ops.Law
public import NLAlib.Ops.Link
public import NLAlib.Ops.Logic
public import NLAlib.Ops.Profile
public import NLAlib.Ops.Profiles.Blas
public import NLAlib.Ops.Profiles.BlasCert
public import NLAlib.Ops.Profiles.Random
public import NLAlib.Ops.Rules
public import NLAlib.Ops.Static
public import NLAlib.Ops.Store
public import NLAlib.Ops.StoreSimp
public import NLAlib.Ops.Stream
public import NLAlib.Ops.Syntax
public import NLAlib.Ops.Tactic
public import NLAlib.Ops.Tape
public import NLAlib.Ops.TapeLaw
public import NLAlib.Ops.Transfer
public import NLAlib.Ops.Window

/-!
# Conditional headline guidance over imported Ops modules

The core and logic rules are excluded from headline selection. The scan reports conditional
guidance separately from canonical and refinement schemas that these heuristics do not inspect.

## Main results

`#ops_lint_scan` prints one diagnostic line per recognized headline.
-/

@[expose] public section

#ops_lint_scan

-- Module export views must not silently erase conditional or canonical headline coverage.
open Lean Elab Command in
run_cmd liftTermElabM do
  let targets ← NLAlib.Ops.Tools.Lint.scanTargets
  for n in [``NLAlib.Ops.Examples.runs_gemm_rounded,
      ``NLAlib.Ops.Examples.Certification.certifies_repeatProgram,
      ``NLAlib.Ops.Blas.seq_certifies] do
    unless targets.contains n do throwError "headline scan lost {n} under the module system"
