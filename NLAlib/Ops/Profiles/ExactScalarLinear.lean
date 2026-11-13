/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeStar
public import NLAlib.Ops.Profiles.ExactLinear

/-!
# Exact scalar operation model for linear-algebra implementations

This collection replaces the level-one vector group by explicit scalar conjugation.
Matrix-vector application, sampling and dimension literals retain their declared groups.
There are no BLAS operation names in this signature. Dense and sparse matvec profiles can
further lower its stored-operator group to scalar arithmetic.

## Main results

* `NLAlib.Ops.ExactScalarLinear.Operation` is the scalar implementation signature.
* `NLAlib.Ops.ExactScalarLinear.model` generates the jointly realized local contracts.
* `NLAlib.Ops.ExactScalarLinear.laws` recovers scalar arithmetic, conjugation and other groups.
-/

@[expose] public section

namespace NLAlib.Ops.ExactScalarLinear

/-- Scalar field operations and conjugation, stored matvec, sampling and dimension literals. -/
abbrev Operation := RCLikeStar.Operation ⊕ (StoredOperatorOp ⊕ (SampleOp ⊕ IndexOp))

instance : Has ScalarOp Operation := Has.sumLeft _ RCLikeStar.Operation _ inferInstance
instance : Has StarOp Operation := Has.sumLeft _ RCLikeStar.Operation _ inferInstance
instance : Has StoredOperatorOp Operation := Has.sumRight _ RCLikeStar.Operation _ inferInstance

instance : Has SampleOp Operation :=
  Has.sumRight _ RCLikeStar.Operation _ (Has.sumRight _ StoredOperatorOp _ inferInstance)

instance : Has IndexOp Operation :=
  Has.sumRight _ RCLikeStar.Operation _ (Has.sumRight _ StoredOperatorOp _ inferInstance)

instance : Apart StoredOperatorOp ScalarOp Operation := ⟨fun _ => rfl⟩
instance : Apart StoredOperatorOp StarOp Operation := ⟨fun _ => rfl⟩
instance : Apart StoredOperatorOp SampleOp Operation := ⟨fun _ => rfl⟩
instance : Apart StoredOperatorOp IndexOp Operation := ⟨fun _ => rfl⟩

variable {𝕜 : Type} [RCLike 𝕜]

/-- Exhaustive local meanings of the scalar collection. Primitive functions read only
their declared blocks and sample windows. -/
noncomputable def functions (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜) : Operation → BlockFn 𝕜
  | .inl (.inl o) => RCLikeBlas.machine.fn o
  | .inl (.inr o) => RCLikeStar.functions o
  | .inr (.inl o) => StoredOperator.functions dataLength matrix o
  | .inr (.inr (.inl (.draw stream))) => .draw stream
  | .inr (.inr (.inr _)) => RCLikeBlas.machine.indexFn

/-- Scalar storage shapes of the exact scalar collection. -/
def signature : Operation → OperandSignature
  | .inl (.inl (.lit _)) => ⟨[], [.cell]⟩
  | .inl (.inl .add) | .inl (.inl .sub) | .inl (.inl .mul) | .inl (.inl .div) =>
      ⟨[.cell, .cell], [.cell]⟩
  | .inl (.inl .neg) | .inl (.inl .sqrt) | .inl (.inl .copy) | .inl (.inr _) =>
      ⟨[.cell], [.cell]⟩
  | .inr (.inl _) => ⟨[.cell, .cell], [.cell]⟩
  | .inr (.inr _) => ⟨[], [.cell]⟩

/-- Stored matvec output is disjoint from data and vector inputs. Scalar operations may
alias: each reads all its operands before writing its single result. -/
def admissible (dataLength : ℕ → ℕ → ℕ) :
    Operation → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | .inr (.inl _) => StoredOperator.OutApart dataLength
  | _ => AnyOperands

/-- Complete sequential accounting with independently supplied primitive costs and scratch. -/
def resources (work workspace : Operation → List ℕ → ℕ) : ResourceModel Operation CmpTst :=
  Functional.cellResources signature work workspace

/-- The exact scalar model has no abstract vector primitive. Every contract and one joint
reference interpretation are generated from the exhaustive local-function assignment. -/
noncomputable def model [Inhabited 𝕜] {r b : ℕ} (P : Problem 𝕜 r b)
    (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (work workspace : Operation → List ℕ → ℕ) : AccessModel Operation CmpTst P :=
  Functional.modelWithAdm P RCLike.re (fun _ _ => functions dataLength matrix)
    (admissible dataLength) (resources work workspace)

/-- Scalar field arithmetic, conjugation, explicit-data matvec, draws, dimension literals
and comparisons hold jointly for every interpretation of the generated model. -/
theorem laws [Inhabited 𝕜] {r b : ℕ} {P : Problem 𝕜 r b}
    {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    {work workspace : Operation → List ℕ → ℕ} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Operation CmpTst 𝕜}
    (h : (model P dataLength matrix work workspace).contracts d x I) :
    IsScalar RCLikeBlas.machine I ∧ RCLikeStar.IsExact I ∧
      StoredOperator.IsExact dataLength matrix I ∧ IsSample I ∧
        IsIndexLit RCLikeBlas.machine I ∧ IsCmp RCLike.re I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, Functional.isCmpWithAdm h⟩
  · intro o
    exact Functional.isFnWithAdm h (.inl (.inl o))
  · exact Functional.isFnWithAdm h (.inl (.inr .conj))
  · exact Functional.isFnWithAdm h (.inr (.inl .matvec))
  · intro stream
    exact Functional.isFnWithAdm h (.inr (.inr (.inl (.draw stream))))
  · exact Functional.isFnWithAdm h (.inr (.inr (.inr .lit)))

end NLAlib.Ops.ExactScalarLinear
