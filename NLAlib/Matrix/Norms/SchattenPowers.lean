/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.TracePowers
public import NLAlib.Matrix.Norms.Schatten

/-!
# Powers of Schatten norms

For a natural exponent $p \ne 0$, the $p$-th power of the Schatten $p$-norm is the sum of the
$p$-th powers of the singular values, with natural-number powers, and for even exponents it is the
trace of a matrix power:
$\|\mathbf{A}\|_{S_{2p}}^{2p} = \operatorname{Re}
\operatorname{tr}\bigl((\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\bigr)$. These are the forms used by the
moment method, which then never meets `ENNReal.toReal` or `Real.rpow`.

## Main results

* `Matrix.PosSemidef.schattenNorm_rpow_eq_re_trace_rpow`: positive real powers as traces.
* `Matrix.PosSemidef.schattenNorm_sub_rpow_le`: the ordered Schatten trace-deficit bound.
* `NLAlib.schattenNorm_natCast_pow`: the power-sum formula with natural-number powers.
* `NLAlib.schattenNorm_two_mul_natCast_pow`,
  `Matrix.IsHermitian.schattenNorm_two_mul_natCast_pow`: even Schatten norms as traces of powers.
* `NLAlib.specNorm_pow_le_re_trace_pow`: the moment bound for the spectral norm.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- For a natural exponent $p \ne 0$, the $p$-th power of the Schatten $p$-norm is the sum of the
$p$-th powers of the singular values, with natural-number powers:
$\|\mathbf{A}\|_{S_p}^p = \sum_{i < N} \sigma_i(\mathbf{A})^p$ for any
$N \ge \operatorname{rank} \mathbf{A}$. -/
theorem schattenNorm_natCast_pow {p : ℕ} (hp : p ≠ 0) (A : Matrix m n 𝕜) {N : ℕ}
    (hN : A.rank ≤ N) :
    schattenNorm p A ^ p = ∑ i ∈ Finset.range N, singularValues A i ^ p := by
  have h := schattenNorm_rpow (Nat.cast_ne_zero.mpr hp) (ENNReal.natCast_ne_top p) A hN
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using h

/-- **Even Schatten norms as traces.** For a natural number $p \ne 0$,
$$\|\mathbf{A}\|_{S_{2p}}^{2p}
  = \operatorname{Re} \operatorname{tr}\bigl((\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\bigr)\,.$$
This is the form used by the moment method.
[Bhatia1997, §IV.2]. -/
theorem schattenNorm_two_mul_natCast_pow [DecidableEq n] {p : ℕ} (hp : p ≠ 0)
    (A : Matrix m n 𝕜) :
    schattenNorm (2 * p) A ^ (2 * p) = RCLike.re ((Aᴴ * A) ^ p).trace := by
  have h := schattenNorm_natCast_pow (p := 2 * p) (mul_ne_zero two_ne_zero hp) A
    A.rank_le_card_width
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [h, (Matrix.isHermitian_conjTranspose_mul_self A).re_trace_pow_eq_sum_range_eigenvalue_pow]
  exact Finset.sum_congr rfl fun i _ => by rw [pow_mul, singularValues_sq]

/-- For a Hermitian matrix and a natural number $p \ne 0$,
$\|\mathbf{A}\|_{S_{2p}}^{2p} = \operatorname{Re} \operatorname{tr}(\mathbf{A}^{2p})$. -/
theorem _root_.Matrix.IsHermitian.schattenNorm_two_mul_natCast_pow [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {p : ℕ} (hp : p ≠ 0) :
    schattenNorm (2 * p) A ^ (2 * p) = RCLike.re (A ^ (2 * p)).trace := by
  rw [NLAlib.schattenNorm_two_mul_natCast_pow hp, hA.eq, ← pow_two, ← pow_mul]

/-- The moment bound for the spectral norm: for a natural number $p \ne 0$,
$\|\mathbf{A}\|_2^{2p} \le \operatorname{Re}
\operatorname{tr}\bigl((\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\bigr)$.
-/
theorem specNorm_pow_le_re_trace_pow [DecidableEq n] (A : Matrix m n 𝕜) {p : ℕ} (hp : p ≠ 0) :
    specNorm A ^ (2 * p) ≤ RCLike.re ((Aᴴ * A) ^ p).trace := by
  have h := specNorm_le_schattenNorm (q := ((2 * p : ℕ) : ℝ≥0∞))
    (Nat.cast_ne_zero.mpr (mul_ne_zero two_ne_zero hp)) A
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [← schattenNorm_two_mul_natCast_pow hp]
  exact pow_le_pow_left₀ (specNorm_nonneg A) h _

section Positive

open scoped MatrixOrder ComplexOrder

/-- The $p$-th power of the Schatten $p$-norm of a positive semidefinite matrix equals
$\operatorname{Re} \operatorname{tr}(\mathbf{A}^p)$ for every real $p>0$. -/
theorem _root_.Matrix.PosSemidef.schattenNorm_rpow_eq_re_trace_rpow [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {p : ℝ} (hp : 0 < p) :
    schattenNorm (ENNReal.ofReal p) A ^ p = RCLike.re (A ^ p).trace := by
  rw [CFC.rpow_eq_cfc_real hA.nonneg, hA.isHermitian.re_trace_cfc]
  have h := schattenNorm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top A
    A.rank_le_card_width
  simpa only [ENNReal.toReal_ofReal hp.le, hA.singularValues_eq_eigenvalue] using h

/-- **Ordered Schatten trace-deficit bound.** For $\mathbf{A} \succeq \mathbf{B} \succeq \mathbf{0}$
and finite real $p \ge 1$,
$$\|\mathbf{A} - \mathbf{B}\|_{S_p}^p \le
  \|\mathbf{A}\|_{S_p}^p - \|\mathbf{B}\|_{S_p}^p.$$
[PerssonMeyerMusco2025, Lemma 2.3]. At $p=1$, see `Matrix.PosSemidef.nuclearNorm_sub_of_le`.
Result: ordered-schatten-trace-deficit -/
theorem _root_.Matrix.PosSemidef.schattenNorm_sub_rpow_le {A B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (h : B ≤ A) {p : ℝ} (hp : 1 ≤ p) :
    schattenNorm (ENNReal.ofReal p) (A - B) ^ p ≤
      schattenNorm (ENNReal.ofReal p) A ^ p - schattenNorm (ENNReal.ofReal p) B ^ p := by
  classical
  have hD := Matrix.le_iff.mp h
  have hA : A.PosSemidef := by simpa using hD.add hB
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  rw [hD.schattenNorm_rpow_eq_re_trace_rpow hp₀, hA.schattenNorm_rpow_eq_re_trace_rpow hp₀,
    hB.schattenNorm_rpow_eq_re_trace_rpow hp₀, le_sub_iff_add_le]
  simpa only [sub_add_cancel] using hD.re_trace_rpow_add_le hB hp

end Positive

end NLAlib
