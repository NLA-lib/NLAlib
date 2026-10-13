/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Positivity.Core
public import NLAlib.Matrix.Majorization.Basic
public import NLAlib.Matrix.Spectral.SVD
public import NLAlib.Matrix.Spectral.Interlacing

/-!
# Ky Fan's maximum principles and the Ky Fan norms

The sum of the `k` largest eigenvalues of a Hermitian matrix is the largest trace of a
compression to `k` orthonormal directions, and the sum of the `k` largest singular values of a
matrix is the largest modulus of the trace of `Uᴴ * A * V` over pairs of `k` orthonormal
directions. Both partial sums are therefore subadditive in the matrix.

The singular value partial sum is the Ky Fan `k`-norm `NLAlib.kyFanNorm k A`. Eigenvalue partial
sums are written `∑ i ∈ Finset.range k, eigenvalue A i` and have no name.

## Main definitions

* `NLAlib.kyFanNorm`: the sum of the `k` largest singular values.

## Main results

* `Matrix.IsHermitian.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue`: Ky Fan's maximum
  principle for eigenvalues, and
  `Matrix.IsHermitian.exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue`: attainment.
* `NLAlib.sum_range_eigenvalue_add_le`: subadditivity of eigenvalue partial sums.
* `NLAlib.norm_trace_conjTranspose_mul_mul_le_kyFanNorm`: the principle for singular values.
* `NLAlib.kyFanNorm_add_le`: the triangle inequality of the Ky Fan norms.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-! ### Eigenvalues -/

/-- **Ky Fan's maximum principle.** For Hermitian `A` and `Q` with orthonormal columns indexed by
`p`, the trace of the compression `Qᴴ * A * Q` is at most the sum of the `card p` largest
eigenvalues of `A`.
[HornJohnson2013, Corollary 4.3.39]; stated there for the smallest eigenvalues and increasing
order. Port of `NLAlib.trace_compression_le_eigenvaluePrefix`.
Result: ky-fan-maximum-principle -/
theorem _root_.Matrix.IsHermitian.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue
    [DecidableEq p] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) :
    RCLike.re (Qᴴ * A * Q).trace ≤ ∑ i ∈ Finset.range (Fintype.card p), eigenvalue A i := by
  sorry

/-- The maximum in Ky Fan's principle is attained by the leading eigenvectors.
Port of `NLAlib.exists_trace_compression_eq_eigenvaluePrefix`, there over `ℝ`.
Result: ky-fan-maximum-principle -/
theorem _root_.Matrix.IsHermitian.exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ} (hk : k ≤ Fintype.card n) :
    ∃ Q : Matrix n (Fin k) 𝕜, HasOrthonormalCols Q ∧
      RCLike.re (Qᴴ * A * Q).trace = ∑ i ∈ Finset.range k, eigenvalue A i := by
  sorry

/-- **Ky Fan's minimum principle.** The trace of a compression to `card p` orthonormal
directions is at least the sum of the `card p` smallest eigenvalues: with
`card p + d = card n`, `∑ i ∈ [d, card n), λ_i(A) ≤ re tr (Qᴴ A Q)`.
[HornJohnson2013, Corollary 4.3.39].
Port of `NLAlib.sum_bottom_eigenvalues_le_trace_compression`. -/
theorem _root_.Matrix.IsHermitian.sum_Ico_eigenvalue_le_re_trace_conjTranspose_mul_mul
    [DecidableEq p] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) {d : ℕ} (hd : Fintype.card p + d = Fintype.card n) :
    ∑ i ∈ Finset.Ico d (Fintype.card n), eigenvalue A i ≤ RCLike.re (Qᴴ * A * Q).trace := by
  sorry

/-- **Subadditivity of eigenvalue partial sums.** For Hermitian `A` and `B`, the sum of the `k`
largest eigenvalues of `A + B` is at most the sums for `A` and `B`.
[HornJohnson2013, Corollary 4.3.39 and Theorem 4.3.47].
Port of `NLAlib.eigenvaluePrefix_add_le`, there over `ℝ`.
Result: ky-fan-eigenvalue-sums -/
theorem sum_range_eigenvalue_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : ℕ) :
    ∑ i ∈ Finset.range k, eigenvalue (A + B) i ≤
      ∑ i ∈ Finset.range k, eigenvalue A i + ∑ i ∈ Finset.range k, eigenvalue B i := by
  sorry

/-- The eigenvalues of `A + B` are majorized by the sums of the sorted eigenvalues of `A` and
`B`. [HornJohnson2013, Theorem 4.3.47].
Port of `NLAlib.majorized_eigenvalues₀_add`, there over `ℝ`.
Result: ky-fan-eigenvalue-sums -/
theorem majorized_eigenvalue_add {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Majorized (fun i : Fin (Fintype.card n) => eigenvalue (A + B) i)
      (fun i : Fin (Fintype.card n) => eigenvalue A i + eigenvalue B i) := by
  sorry

/-! ### The Ky Fan norms -/

/-- The **Ky Fan `k`-norm**: the sum of the `k` largest singular values. `kyFanNorm 1` is the
spectral norm, and `kyFanNorm k` for `k` at least the smaller dimension is the nuclear norm.
[HornJohnson2013, §7.4.8]. Port of `NLAlib.kyFanNorm`, with the arguments in the other order. -/
noncomputable def kyFanNorm (k : ℕ) (A : Matrix m n 𝕜) : ℝ :=
  ∑ i ∈ Finset.range k, singularValues A i

/-- The Ky Fan `k`-norm is the sum of the first `k` singular values.
Port of `NLAlib.kyFanNorm_eq_sum_range`. -/
theorem kyFanNorm_eq_sum_range (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k A = ∑ i ∈ Finset.range k, singularValues A i :=
  rfl

/-- Ky Fan norms are nonnegative. Port of `NLAlib.kyFanNorm_nonneg`. -/
theorem kyFanNorm_nonneg (k : ℕ) (A : Matrix m n 𝕜) : 0 ≤ kyFanNorm k A := by
  sorry

/-- The Ky Fan `0`-norm vanishes. Port of `NLAlib.kyFanNorm_zero`. -/
@[simp]
theorem kyFanNorm_zero_left (A : Matrix m n 𝕜) : kyFanNorm 0 A = 0 := by
  sorry

/-- The Ky Fan `1`-norm is the spectral norm. Port of `NLAlib.kyFanNorm_one_eq_specNorm`. -/
@[simp]
theorem kyFanNorm_one (A : Matrix m n 𝕜) : kyFanNorm 1 A = specNorm A := by
  sorry

/-- Ky Fan norms increase with `k`. -/
theorem kyFanNorm_mono_left (A : Matrix m n 𝕜) {k l : ℕ} (h : k ≤ l) :
    kyFanNorm k A ≤ kyFanNorm l A := by
  sorry

/-- The Ky Fan `k`-norm is at most `k` times the spectral norm. -/
theorem kyFanNorm_le_mul_specNorm (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k A ≤ k * specNorm A := by
  sorry

/-- **Ky Fan's maximum principle for singular values.** For `U` and `V` with orthonormal columns
indexed by `p`, the modulus of the trace of `Uᴴ * A * V` is at most the Ky Fan `card p`-norm
of `A`.
[HornJohnson1991, Theorem 3.4.1].
Port of `NLAlib.trace_twoSided_compression_le_kyFanNorm`, there over `ℝ` without the modulus.
Result: ky-fan-singular-values -/
theorem norm_trace_conjTranspose_mul_mul_le_kyFanNorm [DecidableEq p] (A : Matrix m n 𝕜)
    {U : Matrix m p 𝕜} {V : Matrix n p 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) :
    ‖(Uᴴ * A * V).trace‖ ≤ kyFanNorm (Fintype.card p) A := by
  sorry

/-- The maximum in Ky Fan's principle for singular values is attained by the leading singular
vectors, with a real nonnegative trace.
Port of `NLAlib.exists_trace_twoSided_compression_eq_kyFanNorm`, there over `ℝ`.
Result: ky-fan-singular-values -/
theorem exists_trace_conjTranspose_mul_mul_eq_kyFanNorm (A : Matrix m n 𝕜) {k : ℕ}
    (hkm : k ≤ Fintype.card m) (hkn : k ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin k) 𝕜) (V : Matrix n (Fin k) 𝕜), HasOrthonormalCols U ∧
      HasOrthonormalCols V ∧ (Uᴴ * A * V).trace = ((kyFanNorm k A : ℝ) : 𝕜) := by
  sorry

/-- **The triangle inequality of the Ky Fan norms**:
`∑ i < k, σ_i(A + B) ≤ ∑ i < k, σ_i(A) + ∑ i < k, σ_i(B)`.
[HornJohnson1991, Corollary 3.4.3].
Port of `NLAlib.kyFanNorm_add_le`, there over `ℝ`.
Result: ky-fan-singular-values -/
theorem kyFanNorm_add_le (k : ℕ) (A B : Matrix m n 𝕜) :
    kyFanNorm k (A + B) ≤ kyFanNorm k A + kyFanNorm k B := by
  sorry

/-- The Frobenius inner product with a matrix of rank at most `k` and spectral norm at most one
is at most the Ky Fan `k`-norm.
Port of `NLAlib.frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one`, there over `ℝ`. -/
theorem frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one (A : Matrix m n 𝕜)
    {P : Matrix m n 𝕜} {k : ℕ} (hP : P.rank ≤ k) (hPn : specNorm P ≤ 1) :
    frobInner A P ≤ kyFanNorm k A := by
  sorry

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.kyFanNorm k A` is nonnegative. -/
@[positivity NLAlib.kyFanNorm _ _]
meta def evalKyFanNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.kyFanNorm_nonneg #[e.appFn!.appArg!, e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
