/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.PowerBounds
import Mathlib.Tactic.NoncommRing

/-!
# Newton–Schulz refinement of an approximate inverse

The update squares the right residual, even when the two input matrices do not commute.
[Higham2008, §5.3].

## Main results

* `NLAlib.one_sub_mul_inverseSchulzIterate`: the exact residual power.
* `NLAlib.tendsto_inverseSchulzIterate`: convergence under spectral stability.
* `NLAlib.specNorm_sub_inverseSchulzIterate_le`: an explicit error estimate.
-/

@[expose] public section
open Filter
open scoped Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Newton–Schulz inverse iteration, initialized at the supplied approximation.
[Higham2008, §5.3]. -/
def inverseSchulzIterate {R : Type*} [Ring R] (A X : Matrix n n R) : ℕ → Matrix n n R
  | 0 => X
  | k + 1 => let Y := inverseSchulzIterate A X k; Y * (2 • 1 - A * Y)

/-- **Residual squaring.** After $k$ inverse refinements the right residual is exactly the
$2^k$-th power of the initial residual. [Higham2008, §5.3].
Result: matrix-inverse-newton-schulz -/
theorem one_sub_mul_inverseSchulzIterate {R : Type*} [Ring R] (A X : Matrix n n R) (k : ℕ) :
    1 - A * inverseSchulzIterate A X k = (1 - A * X) ^ (2 ^ k) := by
  induction k with
  | zero => simp [inverseSchulzIterate]
  | succ k ih =>
    rw [pow_succ 2 k, pow_mul, ← ih, inverseSchulzIterate, two_smul]
    noncomm_ring

variable {𝕜 : Type*} [RCLike 𝕜]

/-- For an invertible input, multiplying the residual by the exact inverse gives the error.
[Higham2008, §5.3]. -/
theorem sub_inverseSchulzIterate {A : Matrix n n 𝕜} (hA : IsUnit A) (X : Matrix n n 𝕜)
    (k : ℕ) : A⁻¹ - inverseSchulzIterate A X k = A⁻¹ * (1 - A * X) ^ (2 ^ k) := by
  rw [← one_sub_mul_inverseSchulzIterate, mul_sub, mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA), one_mul]

/-- **Convergence of inverse refinement.** A right residual with spectral radius less than
one gives convergence to the inverse, for real or complex square matrices. [Higham2008, §5.3].
Result: matrix-inverse-newton-schulz -/
theorem tendsto_inverseSchulzIterate {A X : Matrix n n 𝕜} (h : specRadius (1 - A * X) < 1) :
    Tendsto (inverseSchulzIterate A X) atTop (𝓝 A⁻¹) := by
  have hu := isUnit_det_one_sub_of_specRadius_lt_one h
  rw [sub_sub_cancel, Matrix.det_mul] at hu
  have hA := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_of_mul_isUnit_left hu)
  have hp := ((tendsto_pow_zero_iff_specRadius_lt_one _).mpr h).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have he (k : ℕ) : inverseSchulzIterate A X k = A⁻¹ - A⁻¹ * (1 - A * X) ^ (2 ^ k) := by
    rw [← sub_inverseSchulzIterate hA, sub_sub_cancel]
  simp_rw [show inverseSchulzIterate A X = _ from funext he]
  simpa using tendsto_const_nhds.sub (hp.const_mul A⁻¹)

/-- **Inverse refinement error.** For an invertible real or complex matrix, the spectral norm
of the inverse error is bounded by the inverse norm times the $2^k$-th power of the initial
right residual norm. [Higham2008, §5.3].
Result: matrix-inverse-newton-schulz -/
theorem specNorm_sub_inverseSchulzIterate_le {A : Matrix n n 𝕜} (hA : IsUnit A)
    (X : Matrix n n 𝕜) (k : ℕ) :
    specNorm (A⁻¹ - inverseSchulzIterate A X k) ≤ specNorm A⁻¹ * specNorm (1 - A * X) ^ (2 ^ k) :=
  (sub_inverseSchulzIterate hA X k ▸ specNorm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (specNorm_pow_le _ _) (specNorm_nonneg _))

end NLAlib
