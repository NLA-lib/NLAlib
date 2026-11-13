/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeBlas

/-!
# Exact scalar conjugation

Conjugation is a scalar operation over a real or complex word carrier. It is separate
from the field-operation catalog so real models can implement it by copying and complex
models can retain explicit conjugation counts. No vector operation is hidden here.

## Main definitions

* `NLAlib.Ops.StarOp.conj` names one scalar conjugation.
* `NLAlib.Ops.RCLikeStar.IsExact` is its local functional contract.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Scalar involution, distinct from field arithmetic. -/
inductive StarOp where
  /-- Conjugate one scalar word, permitting exact input/output alias. -/
  | conj
  deriving DecidableEq

namespace RCLikeStar

variable {𝕜 Op Tst : Type} [RCLike 𝕜]

/-- The scalar operation reads one word and writes its conjugate. -/
def functions : StarOp → BlockFn 𝕜
  | .conj => .un fun x => some (star x)

/-- Exact scalar conjugation, independently of any vector algorithm or rounding theorem. -/
def IsExact [Has StarOp Op] (I : Interp Op Tst 𝕜) : Prop :=
  I.IsFn .total (Has.inj StarOp.conj) (functions .conj) AnyOperands

/-- One scalar signature combining exact field arithmetic and explicit conjugation. -/
abbrev Operation := ScalarOp ⊕ StarOp

/-- Exhaustive local functions for exact real or complex scalar arithmetic. -/
noncomputable def operationFunctions : Operation → BlockFn 𝕜
  | .inl o => RCLikeBlas.machine.fn o
  | .inr o => functions o

/-- The functional reference interpreter jointly realizes all scalar local contracts. -/
theorem interp_contracts :
    IsScalar (RCLikeBlas.machine : Machine 𝕜)
        (Interp.ofFns (Tst := Tst) operationFunctions) ∧
      IsExact (Interp.ofFns (Tst := Tst) (operationFunctions (𝕜 := 𝕜))) := by
  refine ⟨fun o => Interp.ofFns_isFn operationFunctions .total (.inl o) AnyOperands,
    Interp.ofFns_isFn operationFunctions .total (.inr .conj) AnyOperands⟩

end RCLikeStar
end NLAlib.Ops
