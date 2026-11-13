/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeStar
public import NLAlib.Ops.Catalog.Functional
public import NLAlib.Ops.Catalog.Sampling
public import NLAlib.Ops.Catalog.Index

/-!
# Scalar operation model without vector or matrix primitives

The collection contains field arithmetic, scalar conjugation, sampling and dimension
literals. Vector and matrix operations enter through fixed implementations over these
primitives. No vector or matrix operation name belongs to this signature.

## Main results

* `NLAlib.Ops.ScalarOnly.Operation` is the scalar implementation signature.
* `NLAlib.Ops.ScalarOnly.model` generates the jointly realized local contracts.
* `NLAlib.Ops.ScalarOnly.laws` recovers scalar arithmetic, conjugation and other groups.
-/

@[expose] public section

namespace NLAlib.Ops.ScalarOnly

/-- Scalar field operations and conjugation, sampling and dimension literals. -/
abbrev Operation := RCLikeStar.Operation ⊕ (SampleOp ⊕ IndexOp)

instance : Has ScalarOp Operation := Has.sumLeft _ RCLikeStar.Operation _ inferInstance
instance : Has StarOp Operation := Has.sumLeft _ RCLikeStar.Operation _ inferInstance
instance : Has SampleOp Operation := Has.sumRight _ RCLikeStar.Operation _ inferInstance
instance : Has IndexOp Operation := Has.sumRight _ RCLikeStar.Operation _ inferInstance

variable {𝕜 : Type} [RCLike 𝕜]

/-- Exhaustive local meanings of the scalar collection. Primitive functions read only
their declared blocks and sample windows. -/
noncomputable def functions : Operation → BlockFn 𝕜
  | .inl (.inl o) => RCLikeBlas.machine.fn o
  | .inl (.inr o) => RCLikeStar.functions o
  | .inr (.inl (.draw stream)) => .draw stream
  | .inr (.inr _) => RCLikeBlas.machine.indexFn

/-- Scalar storage shapes of the exact scalar collection. -/
def signature : Operation → OperandSignature
  | .inl (.inl (.lit _)) => ⟨[], [.cell]⟩
  | .inl (.inl .add) | .inl (.inl .sub) | .inl (.inl .mul) | .inl (.inl .div) =>
      ⟨[.cell, .cell], [.cell]⟩
  | .inl (.inl .neg) | .inl (.inl .sqrt) | .inl (.inl .copy) | .inl (.inr _) =>
      ⟨[.cell], [.cell]⟩
  | .inr _ => ⟨[], [.cell]⟩

/-- Complete sequential accounting with independently supplied primitive costs and scratch. -/
def resources (work workspace : Operation → List ℕ → ℕ) : ResourceModel Operation CmpTst :=
  Functional.cellResources signature work workspace

/-- All local contracts and one joint reference realization are generated exhaustively.
Scalar operations read their operands before writing, so exact alias is admitted. -/
noncomputable def model [Inhabited 𝕜] {r b : ℕ} (P : Problem 𝕜 r b)
    (work workspace : Operation → List ℕ → ℕ) : AccessModel Operation CmpTst P :=
  Functional.model P RCLike.re (fun _ _ => functions) (resources work workspace)

/-- Scalar arithmetic, conjugation, draws, index literals and comparisons hold jointly. -/
theorem laws [Inhabited 𝕜] {r b : ℕ} {P : Problem 𝕜 r b}
    {work workspace : Operation → List ℕ → ℕ} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Operation CmpTst 𝕜}
    (h : (model P work workspace).contracts d x I) :
    IsScalar RCLikeBlas.machine I ∧ RCLikeStar.IsExact I ∧ IsSample I ∧
      IsIndexLit RCLikeBlas.machine I ∧ IsCmp RCLike.re I := by
  refine ⟨?_, ?_, ?_, ?_, Functional.isCmp h⟩
  · intro o
    exact Functional.isFn h (.inl (.inl o))
  · exact Functional.isFn h (.inl (.inr .conj))
  · intro stream
    exact Functional.isFn h (.inr (.inl (.draw stream)))
  · exact Functional.isFn h (.inr (.inr .lit))

end NLAlib.Ops.ScalarOnly
