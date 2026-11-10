/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Ops.Tools.Lint
import NLAlib.Ops.Attr
import NLAlib.Ops.Blas.Dot
import NLAlib.Ops.Blas.Level1
import NLAlib.Ops.Blas.Sum
import NLAlib.Ops.BlockRel
import NLAlib.Ops.Blocks
import NLAlib.Ops.Catalog.Blas1
import NLAlib.Ops.Catalog.Compare
import NLAlib.Ops.Catalog.Isotropic
import NLAlib.Ops.Catalog.Random
import NLAlib.Ops.Catalog.Scalar
import NLAlib.Ops.Catalog.Tagged
import NLAlib.Ops.Cert
import NLAlib.Ops.Contract
import NLAlib.Ops.Counted
import NLAlib.Ops.Examples.Bits
import NLAlib.Ops.Examples.Cgs
import NLAlib.Ops.Examples.CgsLinked
import NLAlib.Ops.Examples.CgsMath
import NLAlib.Ops.Examples.CgsQR
import NLAlib.Ops.Examples.Control
import NLAlib.Ops.Examples.Dot
import NLAlib.Ops.Examples.Gemm
import NLAlib.Ops.Examples.GramSchmidt
import NLAlib.Ops.Examples.Hutch
import NLAlib.Ops.Examples.HutchLinked
import NLAlib.Ops.Examples.Liberal
import NLAlib.Ops.Examples.Loops
import NLAlib.Ops.Examples.MatMul
import NLAlib.Ops.Examples.Mixed
import NLAlib.Ops.Examples.Noisy
import NLAlib.Ops.Examples.NoisyLinked
import NLAlib.Ops.Examples.NoisyMath
import NLAlib.Ops.Examples.RandomWitness
import NLAlib.Ops.Examples.Split
import NLAlib.Ops.Examples.StochRound
import NLAlib.Ops.Exec
import NLAlib.Ops.Frame
import NLAlib.Ops.Law
import NLAlib.Ops.Link
import NLAlib.Ops.Logic
import NLAlib.Ops.Profile
import NLAlib.Ops.Profiles.Blas
import NLAlib.Ops.Profiles.BlasCert
import NLAlib.Ops.Profiles.Random
import NLAlib.Ops.Rules
import NLAlib.Ops.Static
import NLAlib.Ops.Store
import NLAlib.Ops.StoreSimp
import NLAlib.Ops.Stream
import NLAlib.Ops.Syntax
import NLAlib.Ops.Tactic
import NLAlib.Ops.Tape
import NLAlib.Ops.TapeLaw
import NLAlib.Ops.Transfer
import NLAlib.Ops.Window

/-! Run the target linter over every headline of the library modules of `NLAlib.Ops` (the core
files and the tools excepted). The result is an information message, one line per theorem. -/

#ops_lint_scan
