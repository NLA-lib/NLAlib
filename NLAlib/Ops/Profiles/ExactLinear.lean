/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Functional
public import NLAlib.Ops.Catalog.RCLikeBlas
public import NLAlib.Ops.Catalog.StoredOperator
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Sampling

/-!
# Exact real or complex linear-algebra operation model

One standardized collection combines field arithmetic, Hermitian level-one operations,
explicit-data matrix-vector application, scalar sampling and dimension literals. The
closed model is generated from its local functions. No algorithm or whole-program
correctness predicate is included in a primitive contract.

## Main results

* `NLAlib.Ops.ExactLinear.Operation` is the fixed composable operation signature.
* `NLAlib.Ops.ExactLinear.functions` declares every primitive's local meaning.
* `NLAlib.Ops.ExactLinear.resources` declares full sequential accounting.
* `NLAlib.Ops.ExactLinear.model` jointly realizes the generated operation model.
* `NLAlib.Ops.ExactLinear.laws` recovers its standardized contract groups.
-/

@[expose] public section

namespace NLAlib.Ops.ExactLinear

/-- Exact scalar/vector arithmetic, explicit-data matvec, sampling and dimension literals. -/
abbrev Operation := RCLikeBlas.Operation ⊕ (StoredOperatorOp ⊕ (SampleOp ⊕ IndexOp))

instance : Has ScalarOp Operation :=
  Has.sumLeft _ RCLikeBlas.Operation _ inferInstance

instance : Has Blas1Op Operation :=
  Has.sumLeft _ RCLikeBlas.Operation _ inferInstance

instance : Has StoredOperatorOp Operation :=
  Has.sumRight _ RCLikeBlas.Operation _ inferInstance

instance : Has SampleOp Operation :=
  Has.sumRight _ RCLikeBlas.Operation _
    (Has.sumRight _ StoredOperatorOp _ inferInstance)

instance : Has IndexOp Operation :=
  Has.sumRight _ RCLikeBlas.Operation _
    (Has.sumRight _ StoredOperatorOp _ inferInstance)

instance : Apart Blas1Op ScalarOp Operation := ⟨fun _ => rfl⟩
instance : Apart ScalarOp Blas1Op Operation := ⟨fun _ => rfl⟩

variable {𝕜 : Type} [RCLike 𝕜]

/-- One exhaustive local-function assignment. A stored matvec reads the explicit data
operand; an oracle model can instead declare an empty data block and a fixed matrix. -/
noncomputable def functions (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜) : Operation → BlockFn 𝕜
  | .inl (.inl o) => RCLikeBlas.machine.fn o
  | .inl (.inr o) => RCLikeBlas.functions o
  | .inr (.inl o) => StoredOperator.functions dataLength matrix o
  | .inr (.inr (.inl (.draw stream))) => .draw stream
  | .inr (.inr (.inr _)) => RCLikeBlas.machine.indexFn

/-- The allowed scalar-cell storage shapes of every operation in the collection. A complex
field entry is one abstract cell here; no physical encoding or byte width is asserted. -/
def signature : Operation → OperandSignature
  | .inl (.inl (.lit _)) => ⟨[], [.cell]⟩
  | .inl (.inl .add) | .inl (.inl .sub) | .inl (.inl .mul) | .inl (.inl .div) =>
      ⟨[.cell, .cell], [.cell]⟩
  | .inl (.inl .neg) | .inl (.inl .sqrt) | .inl (.inl .copy) => ⟨[.cell], [.cell]⟩
  | .inl (.inr .sum) | .inl (.inr .nrm2) | .inl (.inr .copy) => ⟨[.cell], [.cell]⟩
  | .inl (.inr .dot) | .inl (.inr .scal) => ⟨[.cell, .cell], [.cell]⟩
  | .inl (.inr .axpy) => ⟨[.cell, .cell, .cell], [.cell]⟩
  | .inr (.inl _) => ⟨[.cell, .cell], [.cell]⟩
  | .inr (.inr _) => ⟨[], [.cell]⟩

/-- Matrix-vector and BLAS operations use their declared spatial admissions. Scalar
cell functions admit arbitrary operands. Geometry is an explicit operation-model choice. -/
def admissible (dataLength : ℕ → ℕ → ℕ) :
    Operation → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | .inl (.inr o) => RCLikeBlas.admissible o
  | .inr (.inl _) => StoredOperator.OutApart dataLength
  | _ => AnyOperands

/-- Explicit primitive work and workspace with unit query/core costs. Span equals the
sequential work in this configuration. Every structural instruction is charged separately. -/
def resources (work workspace : Operation → List ℕ → ℕ) : ResourceModel Operation CmpTst :=
  Functional.cellResources signature work workspace

/-- Generate the complete exact operation model from the standardized local functions.
Only primitive work/workspace, matrix representation and supplied problem remain choices. -/
noncomputable def model [Inhabited 𝕜] {r b : ℕ} (P : Problem 𝕜 r b)
    (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (work workspace : Operation → List ℕ → ℕ) : AccessModel Operation CmpTst P :=
  Functional.modelWithAdm P RCLike.re (fun _ _ => functions dataLength matrix)
    (admissible dataLength) (resources work workspace)

/-- Every interpreter of the generated model meets the scalar, Hermitian BLAS, explicit
matvec, sampling, dimension-literal and comparison contracts jointly. -/
theorem laws [Inhabited 𝕜] {r b : ℕ} {P : Problem 𝕜 r b}
    {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    {work workspace : Operation → List ℕ → ℕ} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Operation CmpTst 𝕜}
    (h : (model P dataLength matrix work workspace).contracts d x I) :
    IsScalar RCLikeBlas.machine I ∧ RCLikeBlas.IsExact I ∧
      StoredOperator.IsExact dataLength matrix I ∧ IsSample I ∧
        IsIndexLit RCLikeBlas.machine I ∧ IsCmp RCLike.re I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, Functional.isCmpWithAdm h⟩
  · intro o
    exact Functional.isFnWithAdm h (.inl (.inl o))
  · intro o
    exact Functional.isFnWithAdm h (.inl (.inr o))
  · exact Functional.isFnWithAdm h (.inr (.inl .matvec))
  · intro stream
    exact Functional.isFnWithAdm h (.inr (.inr (.inl (.draw stream))))
  · exact Functional.isFnWithAdm h (.inr (.inr (.inr .lit)))

end NLAlib.Ops.ExactLinear
