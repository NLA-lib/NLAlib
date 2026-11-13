/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Resources
public import NLAlib.Eigensolvers.SpectralBisection.Result
public import NLAlib.Eigensolvers.SpectralBisection.TapeMachine

/-!
# Word output and independent resource claims for spectral bisection

The output specification uses the existing mathematical algorithm on the supplied word
matrix and the indexed actual tape. It also records the exact tape advance and release of
all scoped buffers. Counts, work, span and memory bounds are independently supplied functions
of dimensions; defining this specification does not prove any of those bounds.

## Main results

* `NLAlib.SpectralBisection.wordSpecification`: stored output of the actual word routines.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The solver returns the existing word-level mathematical eigensolver result, consumes the
prescribed batches and frees its scoped storage. Independent resource claims are explicit
arguments. This functional specification does not assert numerical accuracy or a probability
law for arbitrary word routines and tapes. -/
noncomputable def wordSpecification {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (budget : (Fin 3 → ℕ) → Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst))
    (scratch work span memory : (Fin 3 → ℕ) → ℕ) :
    Specification DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted) where
  budget := budget
  scratch := scratch
  work := work
  span := span
  memory := memory
  good d x τ _ m :=
    let n := d 0
    let L := d 1
    let fuel := d 2
    let R0 := vec x.val.1.2 0
    let eps := vec x.val.1.2 1
    let beta := vec x.val.1.2 2
    let A := inputMatrix d x
    let F := tapeMachine M dec mm qr n 0 τ
    let root := EighNode.mk n A R0 eps L
    let result := eigh F fuel L A R0 eps beta (eighSlotTree F n fuel R0 beta 0 0 root)
    StoresResult n 0 0 (2, 0) (3, 0) result m.store ∧
      m.pos = (L + 1) * levelSampleSize n ∧ m.store.length = 4

end NLAlib.SpectralBisection
