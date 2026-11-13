/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Specification
public import NLAlib.Ops.Profiles.DenseWork
public import NLAlib.Ops.Catalog.MatrixWorkspace

/-!
# Spectral bisection with independent storage and partition-sensitive work

The full instruction budget remains the conservative static count. Work charges the actual
matrix calls using the disjoint node partition, separately from scalar and structural charges.
Storage uses the independent allocation polynomial and a finite matrix-workspace envelope.

## Main results

* `NLAlib.SpectralBisection.workSpecification`: the resulting raw-word resource claim.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Raw-word output, exact tape use and scratch cleanup, with a full static instruction
budget, independent allocation polynomial, and matrix-work charge
`(L + 1) * (2 * cap + 11) * T n`. Scalar, sampling, literal, query and structural work retain
their full static charges. Scratch adds the finite matrix-workspace envelope; memory includes
the supplied capacities. The dense profile is sequential, so work and span have the same bound. -/
noncomputable def workSpecification {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWorkspace : MatrixOp → List ℕ → ℕ) (T : ℕ → ℕ) :
    Specification DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted) :=
  let scratch := fun d : Fin 3 → ℕ =>
    6 * (d 0 * d 0) * d 1 + 32 * (d 0 * d 0) + 4 * d 0 * d 1 +
      7 * d 0 + 2 * d 1 + 24 + MatrixOp.workspaceEnvelope matrixWorkspace (d 0)
  let work := fun d : Fin 3 → ℕ =>
    (Dense.resources (fun _ _ => 0) matrixWorkspace).work (staticBudget d) +
      (d 1 + 1) * (2 * d 2 + 11) * T (d 0)
  wordSpecification M dec mm qr domain admitted staticBudget scratch work work
    (fun d => 4 * (d 0 * d 0) + d 0 + 3 + scratch d)

end NLAlib.SpectralBisection
