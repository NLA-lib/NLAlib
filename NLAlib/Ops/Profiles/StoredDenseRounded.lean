/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.StoredDense
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Blas.ScalarProductsRounded

/-!
# Rowwise rounding error of stored dense scalar products

The decoded matrix is formed from the actual column-major input words. Each output row is
the machine recurrence returned by the stored dense implementation. Its error follows from
local scalar laws, with no matrix-vector accuracy premise or assumption of successful execution.

## Main results

* `NLAlib.Ops.StoredDense.abs_mulVec_sub_rowWord_le`: the actual scalar row error.
* `NLAlib.Ops.StoredDense.abs_mulVec_sub_output_le`: the same bound on the stored output list.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Ops.StoredDense

/-- The exact real matrix-vector row minus the actual streamed word is bounded by the scalar
rounding envelope times the sum of absolute input products. The matrix and vector are decoded
from their actual raw words; empty columns are included. [Higham2002, §3.5]. -/
theorem abs_mulVec_sub_rowWord_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (m n : ℕ) (raw xs : List ℝ) (i : Fin m) :
    |(StoredOperator.denseMatrix m n raw *ᵥ decv id n xs) i - rowWord M m n raw xs i| ≤
      ScalarProducts.roundoff u n *
        ((StoredOperator.denseMatrix m n raw).map abs *ᵥ fun j => |decv id n xs j|) i := by
  have h := hM.abs_sum_mul_sub_sumWord_le hu
    (fun j => raw.getD (j * m + i) 0) (fun j => xs.getD j 0) n
  have hrow : (StoredOperator.denseMatrix m n raw *ᵥ decv id n xs) i =
      ∑ j ∈ Finset.range n, raw.getD (j * m + i) 0 * xs.getD j 0 :=
    Fin.sum_univ_eq_sum_range
      (fun j => raw.getD (j * m + i) 0 * xs.getD j 0) n
  have habs : ((StoredOperator.denseMatrix m n raw).map abs *ᵥ
      fun j => |decv id n xs j|) i =
        ∑ j ∈ Finset.range n, |raw.getD (j * m + i) 0 * xs.getD j 0| := by
    change (∑ j : Fin n, |raw.getD (j * m + i) 0| * |xs.getD j 0|) = _
    simpa only [abs_mul] using Fin.sum_univ_eq_sum_range
      (fun j => |raw.getD (j * m + i) 0 * xs.getD j 0|) n
  rw [hrow, habs]
  exact h

/-- Decoding the raw row output at a valid row returns exactly its computed word. -/
theorem decv_map_rowWord (M : Machine ℝ) (m n : ℕ) (raw xs : List ℝ) (i : Fin m) :
    decv id m ((List.range m).map (rowWord M m n raw xs)) i = rowWord M m n raw xs i := by
  simp [decv, vec, List.getD_eq_getElem?_getD, i.isLt]

/-- The actual output list of the stored dense implementation satisfies the rowwise bound
from local standard scalar rounding. No numerical matvec contract is assumed. -/
theorem abs_mulVec_sub_output_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (m n : ℕ) (raw xs : List ℝ) (i : Fin m) :
    |(StoredOperator.denseMatrix m n raw *ᵥ decv id n xs -
      decv id m ((List.range m).map (rowWord M m n raw xs))) i| ≤
        ScalarProducts.roundoff u n *
          ((StoredOperator.denseMatrix m n raw).map abs *ᵥ fun j => |decv id n xs j|) i := by
  simpa only [Pi.sub_apply, decv_map_rowWord] using
    abs_mulVec_sub_rowWord_le hM hu m n raw xs i

end NLAlib.Ops.StoredDense
