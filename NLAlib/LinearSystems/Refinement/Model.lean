/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Ops.Catalog.Refinement
public import NLAlib.Ops.Confined

/-!
# The operation model of iterative refinement

The model has the three operations of `NLAlib.Ops.RefinementOp` and no query. The residual and
the correction solve are oracles for the matrix of the input: their contracts name it and
nothing else of the input. The update has one contract at every size and input. The accuracies
$\theta$ (correction), $\eta$, $\zeta$ (residual) and $\varepsilon$ (update) are parameters of
the model, and the matrix-norm allowance of the residual is the spectral norm.

## Main results

* `NLAlib.LinearSystems.Refinement.Model.model`: the jointly realized operation model.
* `NLAlib.LinearSystems.Refinement.Model.laws`: exactly the declared contracts.
* `NLAlib.LinearSystems.Refinement.Model.confined_model`: the model is confined.
-/

@[expose] public section

namespace NLAlib.LinearSystems.Refinement.Model

open Ops

/-- The storage arities of the three operations, in abstract cells. -/
def signature : RefinementOp → OperandSignature
  | .residual | .update => ⟨[.cell, .cell], [.cell]⟩
  | .solve => ⟨[.cell], [.cell]⟩

/-- The work and the workspace of each operation are explicit. Span is sequential; every
structural instruction keeps its own charge. -/
noncomputable def resources (work space : RefinementOp → List ℕ → ℕ) :
    ResourceModel RefinementOp Empty where
  formats := [.cell]
  operation := signature
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace := space
  queryWorkspace q := nomatch q
  operationWork := work
  operationSpan := work
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- Jointly realized contracts of the residual, the correction solve and the update, with
nonnegative accuracies. The matrix function gives the matrix of the system at the supplied
problem instance. No property of the whole solver is part of the operation model. -/
noncomputable def model {r b : ℕ} (P : Problem ℝ r b) (n : (Fin r → ℕ) → ℕ)
    (A : (d : Fin r → ℕ) → P.Input d → Matrix (Fin (n d)) (Fin (n d)) ℝ) {θ η ζ ε : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hε : 0 ≤ ε)
    (R : ResourceModel RefinementOp Empty) : AccessModel RefinementOp Empty P where
  word := 0
  operation d x o := match o with
    | .residual =>
        (residualRel id (A d x) ζ η (specNorm (A d x))).spec (RefinementOperands (n d))
    | .solve => (solveRel id (A d x) θ).spec (RefinementOperands (n d))
    | .update => (updateRel id ε).spec RefinementUpdateOperands
  query _ _ q := nomatch q
  resources := R
  realize d _ x := by
    obtain ⟨I, h⟩ := exists_isRefinement (Tst := Empty) (A d x) hθ hη hζ hε
      (specNorm_nonneg (A d x))
    refine ⟨I, ?_, fun q => nomatch q⟩
    intro o
    cases o with
    | residual => exact h.residual
    | solve => exact h.solve
    | update => exact h.update

/-- Exactly the declared contracts follow from model satisfaction. -/
theorem laws {r b : ℕ} {P : Problem ℝ r b} {n : (Fin r → ℕ) → ℕ}
    {A : (d : Fin r → ℕ) → P.Input d → Matrix (Fin (n d)) (Fin (n d)) ℝ} {θ η ζ ε : ℝ}
    {hθ : 0 ≤ θ} {hη : 0 ≤ η} {hζ : 0 ≤ ζ} {hε : 0 ≤ ε} {R : ResourceModel RefinementOp Empty}
    {d : Fin r → ℕ} {x : P.Input d} {I : Interp RefinementOp Empty ℝ}
    (h : (model P n A hθ hη hζ hε R).contracts d x I) :
    IsRefinement id (A d x) θ η ζ ε (specNorm (A d x)) I :=
  ⟨h.1 .residual, h.1 .solve, h.1 .update⟩

/-- **The model of iterative refinement is confined**: every contract is in operand form. -/
instance confined_model {r b : ℕ} (P : Problem ℝ r b) (n : (Fin r → ℕ) → ℕ)
    (A : (d : Fin r → ℕ) → P.Input d → Matrix (Fin (n d)) (Fin (n d)) ℝ) {θ η ζ ε : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hε : 0 ≤ ε)
    (R : ResourceModel RefinementOp Empty) : (model P n A hθ hη hζ hε R).Confined :=
  ⟨fun d x o => by
    cases o with
    | residual => exact BlockRel.confined_spec _ _
    | solve => exact BlockRel.confined_spec _ _
    | update => exact BlockRel.confined_spec _ _,
    fun _ _ q => nomatch q⟩

end NLAlib.LinearSystems.Refinement.Model
