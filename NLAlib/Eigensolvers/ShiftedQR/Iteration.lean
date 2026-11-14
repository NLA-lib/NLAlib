/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.IterationAlg
public import NLAlib.Eigensolvers.ShiftedQR.FindRitzAlg

/-!
# Concrete scalar shifted QR strategy iteration

The fixed iteration substitutes the actual scalar promising-Ritz search into the composed
strategy tree. Ritz extraction remains the declared local spectral kernel. Matrix copies,
Givens QR steps, candidate acceptance, promising search and streaming grid are implemented
by scalar/index operations. There is no whole-iteration primitive.

The enclosing decoupling program initializes its two constant words once and provides
`[τ,B,θ,α,γ]` as actual prepared parameter words. All iteration workspace is allocated and
freed inside the fixed tree.

## Main results

* `NLAlib.ShiftedQR.iteration`: the concrete fixed scalar strategy tree.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- The fixed scalar strategy iteration, including actual promising-Ritz binary search and
three-phase candidate selection. Its interface is `[n,m,k,D] (W,Params,Constants) -> W`. -/
def iteration : Impl O Q := iterationWith findRitzSearch

end NLAlib.ShiftedQR
