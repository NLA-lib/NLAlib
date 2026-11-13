/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.DenseWeight

/-!
# Separating matrix work from the full dense instruction count

The zero-matrix-work profile still charges every scalar, sample, literal, query and structural
instruction. Matrix work is added from the actual original-operation count of that same run.
The instruction budget can therefore stay conservative while the matrix-work estimate uses
the algorithm's mathematical invariant.

## Main results

* `NLAlib.Ops.Dense.work_eq_nonmatrix_add_matrix`: exact full-count decomposition.
* `NLAlib.Ops.Dense.work_le_of_kernelWeight_le`: combine independent counter and kernel bounds.
-/

@[expose] public section

namespace NLAlib.Ops.Dense

local notation "Queries" => CmpTst ⊕ IdxTst

/-- The dense profile's full work splits into its nonmatrix instruction charges and the
actual supplied matrix costs. Structural work is retained in the first summand. -/
theorem work_eq_nonmatrix_add_matrix (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (c : Count (DenseOp ⊕ Bookkeeping) Queries) :
    (resources matrixWork matrixWorkspace).work c =
      (resources (fun _ _ => 0) matrixWorkspace).work c +
        Count.weight (matrixWeight matrixWork) (fun (_ : Queries) _ => 0)
          (Count.original c) := by
  classical
  have h : (resources matrixWork matrixWorkspace).work =
      (resources (fun _ _ => 0) matrixWorkspace).work +
        (Count.weight (matrixWeight matrixWork) (fun (_ : Queries) _ => 0)).comp
          Count.original := by
    apply Finsupp.addHom_ext
    rintro ⟨(o | q), ds⟩ n
    · rcases o with op | core
      · cases op <;>
          simp [ResourceModel.work, resources, Count.lift_single, Count.original,
            Count.push, Count.one, matrixWeight]
      · simp [ResourceModel.work, resources, Count.lift_single, Count.original,
          Count.push, Count.one]
    · simp [ResourceModel.work, resources, Count.lift_single, Count.original,
        Count.push, Count.one, Count.test]
  exact DFunLike.congr_fun h c

/-- Pointwise matrix costs bounded by a largest-dimension cost give the corresponding
actual kernel-weight bound. No monotonicity of the dimension cost is needed here. -/
theorem matrixWeight_le_kernelWeight {Tst : Type}
    (matrixWork : MatrixOp → List ℕ → ℕ) (T : ℕ → ℕ)
    (hWork : ∀ o ds, matrixWork o ds ≤ T (ds.foldr max 0)) (c : Count DenseOp Tst) :
    Count.weight (matrixWeight matrixWork) (fun (_ : Tst) _ => 0) c ≤ kernelWeight T c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add k n c hk hn ih =>
    rw [map_add, map_add]
    apply add_le_add _ ih
    rcases k with ⟨o | q, ds⟩
    · cases o <;>
        simp only [Count.weight, kernelWeight, Count.lift_single, Sum.elim_inl,
          matrixWeight, MatrixOp.dimensionWeight, smul_eq_mul, le_refl]
      exact Nat.mul_le_mul_left n (hWork _ ds)
    · simp [Count.weight, kernelWeight, Count.lift_single]

/-- A full instruction budget and an independently proved actual matrix-kernel bound
combine into total work. The matrix bound may be sharper than weighting the count budget. -/
theorem work_le_of_kernelWeight_le (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (T : ℕ → ℕ) (hWork : ∀ o ds, matrixWork o ds ≤ T (ds.foldr max 0))
    {c budget : Count (DenseOp ⊕ Bookkeeping) Queries} {kernel : ℕ}
    (hCount : c ≤ budget) (hKernel : kernelWeight T (Count.original c) ≤ kernel) :
    (resources matrixWork matrixWorkspace).work c ≤
      (resources (fun _ _ => 0) matrixWorkspace).work budget + kernel := by
  rw [work_eq_nonmatrix_add_matrix]
  exact add_le_add ((resources (fun _ _ => 0) matrixWorkspace).work_mono hCount)
    ((matrixWeight_le_kernelWeight matrixWork T hWork _).trans hKernel)

/-- This dense configuration charges the same sequential span and work to every instruction. -/
theorem span_eq_work (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (c : Count (DenseOp ⊕ Bookkeeping) Queries) :
    (resources matrixWork matrixWorkspace).span c =
      (resources matrixWork matrixWorkspace).work c := rfl

end NLAlib.Ops.Dense
