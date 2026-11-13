/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.ScalarProducts
public import NLAlib.Ops.Blas.DotMixed

/-!
# Rounding error of streamed scalar products

The stored dense scalar kernel starts from literal zero and performs one multiplication and
one addition for every entry. This module connects its actual word recurrence to the existing
local error trace, including the first addition to zero. Neither successful execution nor a
bound on an observed trajectory is assumed.

## Main results

* `NLAlib.Ops.StdModel.isDotTrace_sumWord`: scalar laws imply the actual local trace.
* `NLAlib.Ops.StdModel.abs_sum_mul_sub_sumWord_le`: a rowwise error bound with two rounded
  operations per entry, including empty rows.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Conservative error envelope for the streamed product loop's two operations per entry. -/
def ScalarProducts.roundoff (u : ℝ) (n : ℕ) : ℝ := (1 + u) ^ (2 * n) - 1

/-- Nonnegative unit roundoff gives a nonnegative streamed-product error envelope. -/
theorem ScalarProducts.roundoff_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ roundoff u n := by
  exact sub_nonneg.mpr (one_le_pow₀ (by linarith))

/-- Each product and addition in the actual streamed recurrence satisfies the standard scalar
error law. Literal zero is exact; no step is omitted from the trace. -/
theorem StdModel.isDotTrace_sumWord {K : Type} {u : ℝ} {dec : K → ℝ} {M : Machine K}
    (hM : StdModel u dec M) (xs ys : ℕ → K) (n : ℕ) :
    IsDotTrace (Computation.AbsRelErr u 0) (fun j => dec (xs j)) (fun j => dec (ys j)) n
      (fun k => dec (ScalarProducts.sumWord M xs ys k)) := by
  refine ⟨hM.zero, fun k _ => ⟨dec (M.mul (xs k) (ys k)), ?_, ?_⟩⟩
  · simpa only [Computation.AbsRelErr, add_zero, abs_sub_comm] using hM.mul (xs k) (ys k)
  · simpa only [Computation.AbsRelErr, add_zero, abs_sub_comm, ScalarProducts.sumWord] using
      hM.add (ScalarProducts.sumWord M xs ys k) (M.mul (xs k) (ys k))

/-- The exact dot product minus the actual streamed scalar word is bounded by
$((1+u)^{2n}-1)\sum_{j<n}\lvert x_j y_j\rvert$ for nonnegative unit roundoff $u$.
The bound counts every multiplication and addition, including addition to initial zero.
[Higham2002, §2.2 and §3.1]; conservative without a smallness assumption. -/
theorem StdModel.abs_sum_mul_sub_sumWord_le {K : Type} {u : ℝ} {dec : K → ℝ}
    {M : Machine K} (hM : StdModel u dec M) (hu : 0 ≤ u) (xs ys : ℕ → K) (n : ℕ) :
    |(∑ j ∈ Finset.range n, dec (xs j) * dec (ys j)) -
      dec (ScalarProducts.sumWord M xs ys n)| ≤
        ScalarProducts.roundoff u n * ∑ j ∈ Finset.range n, |dec (xs j) * dec (ys j)| := by
  simpa only [ScalarProducts.roundoff, mul_zero, add_zero] using
    (hM.isDotTrace_sumWord xs ys n).abs_sum_mul_sub_le_of_absRelErr hu le_rfl

end NLAlib.Ops
