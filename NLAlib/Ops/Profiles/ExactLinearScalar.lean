/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ExactScalarLinear
public import NLAlib.Ops.Profiles.RCLikeScalar

/-!
# Scalar implementation of the exact linear operation collection

The table expands every level-one vector call into scalar instructions and renames the
remaining groups. Its target signature contains no BLAS names. The induced interpretation
therefore satisfies the higher vector contracts by the checked implementations, rather
than by an additional vector primitive assumption.

## Main results

* `NLAlib.Ops.ExactLinearScalar.table` is the fixed scalar implementation table.
* `NLAlib.Ops.ExactLinearScalar.laws` transfers the primitive contract groups.
-/

@[expose] public section

namespace NLAlib.Ops.ExactLinearScalar

/-- Expand vector operations; preserve scalar, stored-operator, sampling and index calls. -/
def table : Table ExactLinear.Operation ExactScalarLinear.Operation CmpTst
  | .inl (.inl o) => .inr (.inl (.inl o))
  | .inl (.inr o) => RCLikeScalar.table o
  | .inr o => .inr (.inr o)

variable {𝕜 : Type} [RCLike 𝕜] {I : Interp ExactScalarLinear.Operation CmpTst 𝕜}

/-- All six vector contracts follow from scalar arithmetic and conjugation alone. -/
theorem isExact (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) : RCLikeBlas.IsExact (I.link table) := by
  intro o
  cases o
  · exact Interp.link_meets rfl (RCLikeScalar.meets_sum hS)
  · exact Interp.link_meets rfl (RCLikeScalar.meets_dot hS hStar)
  · exact Interp.link_meets rfl (RCLikeScalar.meets_axpy hS)
  · exact Interp.link_meets rfl (RCLikeScalar.meets_nrm2 hS hStar)
  · exact Interp.link_meets rfl (RCLikeScalar.meets_scal hS)
  · exact Interp.link_meets rfl (RCLikeScalar.meets_copy hS)

/-- Renaming preserves scalar field arithmetic without adding a lower vector assumption. -/
theorem isScalar (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    IsScalar (RCLikeBlas.machine : Machine 𝕜) (I.link table) := by
  intro o
  exact Interp.link_meets_kept rfl (hS o)

/-- The scalar implementation preserves every other declared group and supplies all vector
contracts through actual scalar executions. Matrix representation remains a local choice. -/
theorem laws {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) (hA : StoredOperator.IsExact dataLength matrix I)
    (hDraw : IsSample I) (hIndex : IsIndexLit RCLikeBlas.machine I)
    (hCmp : IsCmp RCLike.re I) :
    IsScalar RCLikeBlas.machine (I.link table) ∧ RCLikeBlas.IsExact (I.link table) ∧
      StoredOperator.IsExact dataLength matrix (I.link table) ∧ IsSample (I.link table) ∧
        IsIndexLit RCLikeBlas.machine (I.link table) ∧ IsCmp RCLike.re (I.link table) := by
  refine ⟨isScalar hS, isExact hS hStar, ?_, ?_, ?_, hCmp⟩
  · exact Interp.link_meets_kept rfl hA
  · intro stream
    exact Interp.link_meets_kept rfl (hDraw stream)
  · exact Interp.link_meets_kept rfl hIndex

end NLAlib.Ops.ExactLinearScalar
