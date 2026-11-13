/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ExactLinearScalar
public import NLAlib.Ops.Profiles.ScalarOnly
public import NLAlib.Ops.Profiles.StoredDense
public import NLAlib.Ops.Profiles.StoredCOO

/-!
# Dense and coordinate implementations over scalar-only primitives

These tables eliminate the stored-operator group as well as the BLAS group. Matrix words
are declared operands of the scalar loops. The target model contains neither matrix-vector
nor vector primitive names. Dense storage and a fixed coordinate pattern are explicit
implementation choices, independently of the mathematical algorithm.

## Main results

* `NLAlib.Ops.StoredScalar.denseTable` eliminates stored dense matvec calls.
* `NLAlib.Ops.StoredScalar.cooTable` eliminates coordinate matvec calls.
* `NLAlib.Ops.StoredScalar.fullDenseTable` also eliminates the higher BLAS calls.
-/

@[expose] public section

namespace NLAlib.Ops.StoredScalar

/-- Keep scalar groups and lower every explicit-data product to its supplied fixed leaf. -/
def table (leaf : Impl ScalarOnly.Operation CmpTst) :
    Table ExactScalarLinear.Operation ScalarOnly.Operation CmpTst
  | .inl o => .inr (.inl o)
  | .inr (.inl _) => .inl leaf
  | .inr (.inr o) => .inr (.inr o)

/-- Stream column-major matrix words using one scalar temporary. -/
def denseTable : Table ExactScalarLinear.Operation ScalarOnly.Operation CmpTst :=
  table StoredDense.impl

/-- Expand a fixed public coordinate pattern using one scalar temporary. -/
def cooTable (pattern : List (ℕ × ℕ)) :
    Table ExactScalarLinear.Operation ScalarOnly.Operation CmpTst :=
  table (StoredCOO.matvec pattern)

/-- Eliminate both vector and dense matrix-vector groups from the exact linear collection. -/
def fullDenseTable : Table ExactLinear.Operation ScalarOnly.Operation CmpTst :=
  ExactLinearScalar.table.comp denseTable

/-- Eliminate both vector and coordinate matrix-vector groups from the exact collection. -/
def fullCOOTable (pattern : List (ℕ × ℕ)) :
    Table ExactLinear.Operation ScalarOnly.Operation CmpTst :=
  ExactLinearScalar.table.comp (cooTable pattern)

variable {𝕜 : Type} [RCLike 𝕜] {I : Interp ScalarOnly.Operation CmpTst 𝕜}

/-- Dense words are multiplied by the actual scalar leaf, without an abstract matvec law. -/
theorem isDense (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    StoredOperator.IsExact (fun m n => m * n) StoredOperator.denseMatrix
      (I.link denseTable) :=
  Interp.link_meets rfl (StoredDense.meets_impl hS)

/-- Coordinate words are multiplied by the scalar leaf for the selected public pattern. -/
theorem isCOO (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (pattern : List (ℕ × ℕ)) :
    StoredOperator.IsExact (fun _ _ => pattern.length) (StoredOperator.cooMatrix pattern)
      (I.link (cooTable pattern)) :=
  Interp.link_meets rfl (StoredCOO.meets_matvec hS pattern)

/-- Non-matrix groups retain their local contracts through the storage lowering. -/
theorem scalar_laws (leaf : Impl ScalarOnly.Operation CmpTst)
    (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) (hDraw : IsSample I)
    (hIndex : IsIndexLit RCLikeBlas.machine I) (hCmp : IsCmp RCLike.re I) :
    IsScalar RCLikeBlas.machine (I.link (table leaf)) ∧
      RCLikeStar.IsExact (I.link (table leaf)) ∧ IsSample (I.link (table leaf)) ∧
        IsIndexLit RCLikeBlas.machine (I.link (table leaf)) ∧
          IsCmp RCLike.re (I.link (table leaf)) := by
  refine ⟨?_, Interp.link_meets_kept rfl hStar, ?_,
    Interp.link_meets_kept rfl hIndex, hCmp⟩
  · intro o
    exact Interp.link_meets_kept rfl (hS o)
  · intro stream
    exact Interp.link_meets_kept rfl (hDraw stream)

/-- The composed lowering supplies every higher primitive law from a scalar-only model
and the checked local storage implementation. No whole-program execution is a premise. -/
theorem full_laws {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    (leaf : Impl ScalarOnly.Operation CmpTst)
    (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) (hDraw : IsSample I)
    (hIndex : IsIndexLit RCLikeBlas.machine I) (hCmp : IsCmp RCLike.re I)
    (hLeaf : leaf.Triple I .total
      ((StoredOperator.functions dataLength matrix .matvec).rel.spec
        (StoredOperator.OutApart dataLength))) :
    let J := I.link (ExactLinearScalar.table.comp (table leaf))
    IsScalar RCLikeBlas.machine J ∧ RCLikeBlas.IsExact J ∧
      StoredOperator.IsExact dataLength matrix J ∧ IsSample J ∧
        IsIndexLit RCLikeBlas.machine J ∧ IsCmp RCLike.re J := by
  obtain ⟨hS', hStar', hDraw', hIndex', hCmp'⟩ :=
    scalar_laws leaf hS hStar hDraw hIndex hCmp
  have hA : StoredOperator.IsExact dataLength matrix (I.link (table leaf)) :=
    Interp.link_meets rfl hLeaf
  simpa only [Interp.link_comp] using
    ExactLinearScalar.laws hS' hStar' hA hDraw' hIndex' hCmp'

end NLAlib.Ops.StoredScalar
