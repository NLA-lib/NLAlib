/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Dense

/-!
# Declared resources for the standard dense signature

Scalar arithmetic, size literals, samples and queries cost one abstract unit each. Matrix
multiplication and QR retain explicitly supplied work and workspace functions. Structural
instructions cost one unit as well. Span is sequential in this configuration; no parallel
scheduler or finite encoding of the opaque word carrier is asserted.

## Main results

* `NLAlib.Ops.Dense.signature` fixes the storage formats of every primitive group.
* `NLAlib.Ops.Dense.resources` supplies an explicit sequential resource configuration.
-/

@[expose] public section

namespace NLAlib.Ops.Dense

/-- The scalar, index, matrix and sample groups use abstract scalar cells. A complex pair
uses two such words; the codec's positive width specifies its actual number of words. -/
def signature : DenseOp → OperandSignature
  | .scalar (.lit _) | .index _ | .sample _ => ⟨[], [.cell]⟩
  | .scalar .add | .scalar .sub | .scalar .mul | .scalar .div => ⟨[.cell, .cell], [.cell]⟩
  | .scalar .neg | .scalar .sqrt | .scalar .copy => ⟨[.cell], [.cell]⟩
  | .matrix .mul => ⟨[.cell, .cell], [.cell]⟩
  | .matrix .qr => ⟨[.cell], [.cell, .cell]⟩

/-- Explicit sequential resources for dense numerical programs. The matrix-kernel functions
supply their work and temporary payload at the actual dimensions. Primitive scalar/sample
work and all query/core work are charged separately; resident supplied buffers belong to the
problem definition. Every buffer uses abstract cells, rather than a physical real encoding. -/
def resources (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    ResourceModel DenseOp (CmpTst ⊕ IdxTst) where
  formats := [.cell]
  operation := signature
  testInputs q := match q with
    | .inl c => c.lens.map (fun _ => .cell)
    | .inr _ => []
  indexInputs q := match q with
    | .inl _ => []
    | .inr _ => [.cell]
  workspace o d := match o with
    | .matrix m => matrixWorkspace m d
    | _ => 0
  queryWorkspace _ _ := 0
  operationWork o d := match o with
    | .matrix m => matrixWork m d
    | _ => 1
  operationSpan o d := match o with
    | .matrix m => matrixWork m d
    | _ => 1
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

variable {K E : Type} [Inhabited K]

/-- Exact comparison and floor-query contracts. A comparison name cannot supply an index,
and an index name cannot answer a Boolean query. Readable operands determine the actual result. -/
noncomputable def queryContract (dec : K → ℝ) : (CmpTst ⊕ IdxTst) → QueryContract K
  | .inl c => {
      test _ a m result := ∀ xs, m.readBlocks a c.lens = some xs → result = some (c.fn dec xs)
      index _ _ result := result = none }
  | .inr .toNat => {
      test _ _ _ result := result = none
      index a m result := ∀ xs, m.readBlocks a (a.map fun _ => 1) = some xs →
        result = toNatFn dec xs.flatten }

/-- A canonical functional access model for the standard dense signature. Every operation
contract is generated from its declared local block function. A single reference interpretation
realizes all operations and queries at every supplied input. Numerical accuracy of these same
functions is supplied by separate mathematical hypotheses; no whole-program predicate appears. -/
noncomputable def functionalModel {r b : ℕ} (P : Problem K r b)
    (M : Machine K) (dec : K → ℝ) (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E)
    (R : ResourceModel DenseOp (CmpTst ⊕ IdxTst)) : AccessModel DenseOp (CmpTst ⊕ IdxTst) P where
  word := default
  operation _ _ o := ((denseFunctions M C mm qr) o).rel.spec AnyOperands
  query _ _ := queryContract dec
  resources := R
  realize _ _ _ := by
    let I := denseInterp M dec C mm qr
    refine ⟨I, ?_, ?_⟩
    · intro o
      exact Interp.ofFns_isFn (Tst := CmpTst ⊕ IdxTst)
        (denseFunctions M C mm qr) .total o AnyOperands
    · intro q
      rcases q with c | q
      · exact ⟨fun d a m xs h => (denseInterp_contracts M dec C mm qr).2.2.2.2.2.1 c d a m xs h,
          fun _ _ => rfl⟩
      · cases q
        exact ⟨fun _ _ _ => rfl,
          fun a m xs h => (denseInterp_contracts M dec C mm qr).2.2.2.2.2.2 a m xs h⟩

/-- Satisfying the generated access model supplies precisely the scalar, literal, matrix,
sampling and query contracts used by algorithm proofs, on the same interpretation. -/
theorem laws_functionalModel {r b : ℕ} {P : Problem K r b}
    (M : Machine K) (dec : K → ℝ) (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E)
    (R : ResourceModel DenseOp (CmpTst ⊕ IdxTst)) (d : Fin r → ℕ) (x : P.Input d)
    (I : Interp DenseOp (CmpTst ⊕ IdxTst) K)
    (h : (functionalModel P M dec C mm qr R).contracts d x I) :
    IsScalar M I ∧ IsIndexLit M I ∧ IsMatrixMul C mm I ∧ IsMatrixQR C qr I ∧
      IsSample I ∧ IsCmp dec I ∧ IsToNat dec I := by
  refine ⟨fun o => h.1 (.scalar o), h.1 (.index .lit), h.1 (.matrix .mul),
    h.1 (.matrix .qr), fun stream => h.1 (.sample (.draw stream)), ?_, ?_⟩
  · intro c ds a m xs hr
    exact (h.2 (.inl c)).1 ds a m xs hr
  · intro a m xs hr
    exact (h.2 (.inr .toNat)).2 a m xs hr

end NLAlib.Ops.Dense
