/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.StoredDenseRounded
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normwise error of the stored dense scalar implementation

Local scalar rounding gives a componentwise error dominated by the absolute matrix applied
to the absolute input vector. The existing matrix norm comparison converts this to an absolute
operator allowance for the actual streamed output, including empty matrices and vectors.

## Main results

* `NLAlib.Ops.StdModel.norm_mulVec_sub_rowWord_le`: the actual stored scalar matvec has
  error at most the streamed rounding envelope times the square root of the column count,
  the matrix spectral norm and the input Euclidean norm.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Ops

/-- Under nonnegative standard scalar roundoff, the actual stored dense scalar output has
Euclidean error at most $((1+u)^{2n}-1)\sqrt{n}\|\mathbf{A}\|_2\|\mathbf{x}\|$.
The matrix and vector are the raw stored inputs; no accuracy property of a matvec primitive
or assumption of successful execution is required. [Higham2002, §3.5]. -/
theorem StdModel.norm_mulVec_sub_rowWord_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (m n : ℕ) (raw xs : List ℝ) :
    ‖WithLp.toLp 2 (StoredOperator.denseMatrix m n raw *ᵥ decv id n xs -
      decv id m ((List.range m).map (StoredDense.rowWord M m n raw xs)))‖ ≤
        (ScalarProducts.roundoff u n * √(n : ℝ) *
          specNorm (StoredOperator.denseMatrix m n raw)) * ‖WithLp.toLp 2 (decv id n xs)‖ := by
  let A := StoredOperator.denseMatrix m n raw
  let x := decv id n xs
  let y := decv id m ((List.range m).map (StoredDense.rowWord M m n raw xs))
  let c := ScalarProducts.roundoff u n
  have hc : 0 ≤ c := ScalarProducts.roundoff_nonneg hu n
  have hdom := EuclideanSpace.norm_toLp_le_norm_toLp (x := A *ᵥ x - y)
    (y := c • (A.map abs *ᵥ fun j => |x j|)) fun i => by
      have hpos : 0 ≤ (A.map abs *ᵥ fun j => |x j|) i := by
        change 0 ≤ ∑ j, |A i j| * |x j|
        exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hpos]
      exact StoredDense.abs_mulVec_sub_output_le hM hu m n raw xs i
  have hnorm : ‖WithLp.toLp 2 (A *ᵥ x - y)‖ ≤
      c * (√(n : ℝ) * specNorm A * ‖WithLp.toLp 2 x‖) := by
    refine hdom.trans ?_
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Fintype.card_fin] using norm_toLp_map_abs_mulVec_abs_le A x) hc
  calc
    _ ≤ c * (√(n : ℝ) * specNorm A * ‖WithLp.toLp 2 x‖) := hnorm
    _ = _ := by ring

end NLAlib.Ops
