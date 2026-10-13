/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Schatten

/-!
# Schatten norms with natural exponents

For a natural exponent `p ≠ 0`, the `p`-th power of the Schatten `p`-norm is the sum of the
`p`-th powers of the singular values, with `ℕ` powers, and for even exponents it is the trace of a
matrix power: `‖A‖_{2p}^{2p} = re tr ((Aᴴ A)^p)`. These are the forms used by the moment method,
which then never meets `ENNReal.toReal` or `Real.rpow`.

## Main results

* `NLAlib.schattenNorm_natCast_pow`: the power-sum formula with natural-number powers.
* `NLAlib.schattenNorm_two_mul_natCast_pow`,
  `Matrix.IsHermitian.schattenNorm_two_mul_natCast_pow`: even Schatten norms as traces of powers.
* `NLAlib.specNorm_pow_le_re_trace_pow`: the moment bound for the spectral norm.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- For a natural exponent `p ≠ 0`, the `p`-th power of the Schatten `p`-norm is the sum of the
`p`-th powers of the singular values, with natural-number powers. -/
theorem schattenNorm_natCast_pow {p : ℕ} (hp : p ≠ 0) (A : Matrix m n 𝕜) {N : ℕ}
    (hN : A.rank ≤ N) :
    schattenNorm p A ^ p = ∑ i ∈ Finset.range N, singularValues A i ^ p := by
  have h := schattenNorm_rpow (Nat.cast_ne_zero.mpr hp) (ENNReal.natCast_ne_top p) A hN
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using h

/-- **Even Schatten norms as traces.** For a natural number `p ≠ 0`,
`‖A‖_{2p}^{2p} = re tr ((Aᴴ A)^p)`. This is the form used by the moment method.
[Bhatia1997, §IV.2]. -/
theorem schattenNorm_two_mul_natCast_pow [DecidableEq n] {p : ℕ} (hp : p ≠ 0)
    (A : Matrix m n 𝕜) :
    schattenNorm (2 * p) A ^ (2 * p) = RCLike.re ((Aᴴ * A) ^ p).trace := by
  have h := schattenNorm_natCast_pow (p := 2 * p) (mul_ne_zero two_ne_zero hp) A
    A.rank_le_card_width
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [h, (Matrix.isHermitian_conjTranspose_mul_self A).re_trace_pow_eq_sum_range_eigenvalue_pow]
  exact Finset.sum_congr rfl fun i _ => by rw [pow_mul, sq_singularValues]

/-- For a Hermitian matrix and a natural number `p ≠ 0`, `‖A‖_{2p}^{2p} = re tr (A^{2p})`. -/
theorem _root_.Matrix.IsHermitian.schattenNorm_two_mul_natCast_pow [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {p : ℕ} (hp : p ≠ 0) :
    schattenNorm (2 * p) A ^ (2 * p) = RCLike.re (A ^ (2 * p)).trace := by
  rw [NLAlib.schattenNorm_two_mul_natCast_pow hp, hA.eq, ← pow_two, ← pow_mul]

/-- **The moment bound for the spectral norm**: `‖A‖₂^{2p} ≤ re tr ((Aᴴ A)^p)`. -/
theorem specNorm_pow_le_re_trace_pow [DecidableEq n] (A : Matrix m n 𝕜) {p : ℕ} (hp : p ≠ 0) :
    specNorm A ^ (2 * p) ≤ RCLike.re ((Aᴴ * A) ^ p).trace := by
  have h := specNorm_le_schattenNorm (q := ((2 * p : ℕ) : ℝ≥0∞))
    (Nat.cast_ne_zero.mpr (mul_ne_zero two_ne_zero hp)) A
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [← schattenNorm_two_mul_natCast_pow hp]
  exact pow_le_pow_left₀ (specNorm_nonneg A) h _

end NLAlib
