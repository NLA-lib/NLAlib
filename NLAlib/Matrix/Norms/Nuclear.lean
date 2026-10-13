/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.Lidskii
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Ky Fan norms and the nuclear norm

The Ky Fan `k`-norm `NLAlib.kyFanNorm k A` (defined with Ky Fan's maximum principle in
`NLAlib.Matrix.Majorization.KyFan`) is the sum of the `k` largest singular values. The nuclear
norm `NLAlib.nuclearNorm A` is the sum of all of them. This file gives their norm properties,
their invariance, the comparisons with the spectral and Frobenius norms, and the duality between
the nuclear and the spectral norm under the Frobenius inner product.

## Main definitions

* `NLAlib.nuclearNorm`: the sum of the singular values.

## Main results

* `NLAlib.kyFanNorm_of_rank_le`: Ky Fan norms beyond the rank are the nuclear norm.
* `NLAlib.nuclearNorm_add_le`: the triangle inequality.
* `NLAlib.norm_trace_conjTranspose_mul_le_nuclearNorm_mul_specNorm`,
  `NLAlib.isGreatest_frobInner_nuclearNorm`: duality with the spectral norm.
* `NLAlib.nuclearNorm_mul_le_frobNorm_mul_frobNorm`: the factorisation bound.
* `Matrix.PosSemidef.nuclearNorm_eq_re_trace`, `Matrix.IsHermitian.nuclearNorm_eq_sum_abs_eigenvalue`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Ky Fan norms -/

/-- The Ky Fan norms of the zero matrix vanish. Port of `NLAlib.kyFanNorm_zero_matrix`. -/
@[simp]
theorem kyFanNorm_zero (k : ℕ) : kyFanNorm k (0 : Matrix m n 𝕜) = 0 := by
  sorry

/-- For `k ≠ 0` the Ky Fan `k`-norm is definite. Port of `NLAlib.kyFanNorm_eq_zero_iff`. -/
theorem kyFanNorm_eq_zero_iff {k : ℕ} (hk : k ≠ 0) {A : Matrix m n 𝕜} :
    kyFanNorm k A = 0 ↔ A = 0 := by
  sorry

/-- Ky Fan norms are absolutely homogeneous. Port of `NLAlib.kyFanNorm_smul`. -/
theorem kyFanNorm_smul (k : ℕ) (c : 𝕜) (A : Matrix m n 𝕜) :
    kyFanNorm k (c • A) = ‖c‖ * kyFanNorm k A := by
  sorry

/-- Ky Fan norms are even. -/
@[simp]
theorem kyFanNorm_neg (k : ℕ) (A : Matrix m n 𝕜) : kyFanNorm k (-A) = kyFanNorm k A := by
  sorry

/-- Ky Fan norms are invariant under the conjugate transpose. -/
@[simp]
theorem kyFanNorm_conjTranspose (k : ℕ) (A : Matrix m n 𝕜) : kyFanNorm k Aᴴ = kyFanNorm k A := by
  sorry

/-- Ky Fan norms are invariant under the transpose. Port of `NLAlib.kyFanNorm_transpose`. -/
@[simp]
theorem kyFanNorm_transpose (k : ℕ) (A : Matrix m n 𝕜) : kyFanNorm k Aᵀ = kyFanNorm k A := by
  sorry

/-- Ky Fan norms are invariant under relabelling rows and columns. -/
@[simp]
theorem kyFanNorm_submatrix_equiv (k : ℕ) (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    kyFanNorm k (A.submatrix e₁ e₂) = kyFanNorm k A := by
  sorry

/-- Ky Fan norms are invariant under left multiplication by a matrix with orthonormal columns.
Port of `NLAlib.kyFanNorm_orthogonal_mul`. -/
theorem HasOrthonormalCols.kyFanNorm_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k (Q * A) = kyFanNorm k A := by
  sorry

/-- Ky Fan norms are invariant under right multiplication by the conjugate transpose of a matrix
with orthonormal columns. Port of `NLAlib.kyFanNorm_mul_orthogonal`. -/
theorem HasOrthonormalCols.kyFanNorm_mul_conjTranspose_right [DecidableEq n] {Q : Matrix p n 𝕜}
    (hQ : HasOrthonormalCols Q) (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k (A * Qᴴ) = kyFanNorm k A := by
  sorry

/-- The spectral norm is at most every Ky Fan `k`-norm with `k ≠ 0`.
Port of `NLAlib.specNorm_le_kyFanNorm`. -/
theorem specNorm_le_kyFanNorm {k : ℕ} (hk : k ≠ 0) (A : Matrix m n 𝕜) :
    specNorm A ≤ kyFanNorm k A := by
  sorry

/-- The Ky Fan `k`-norm is at most `√k` times the Frobenius norm. -/
theorem kyFanNorm_le_sqrt_mul_frobNorm (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k A ≤ √(k : ℝ) * frobNorm A := by
  sorry

/-- Ky Fan norms are submultiplicative against the spectral norm of a left factor. -/
theorem kyFanNorm_mul_le_specNorm_mul (k : ℕ) (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    kyFanNorm k (A * B) ≤ specNorm A * kyFanNorm k B := by
  sorry

/-- Ky Fan norms are submultiplicative against the spectral norm of a right factor. -/
theorem kyFanNorm_mul_le_mul_specNorm (k : ℕ) (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    kyFanNorm k (A * B) ≤ kyFanNorm k A * specNorm B := by
  sorry

/-- The reverse triangle inequality for Ky Fan norms. -/
theorem abs_kyFanNorm_sub_kyFanNorm_le (k : ℕ) (A B : Matrix m n 𝕜) :
    |kyFanNorm k A - kyFanNorm k B| ≤ kyFanNorm k (A - B) := by
  sorry

/-- The Ky Fan `k`-norm is attained as a Frobenius inner product with a matrix of rank at most
`k` and spectral norm at most one; with `frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one` this
is its variational characterisation. [HornJohnson1991, Theorem 3.4.1]. -/
theorem exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm (k : ℕ) (A : Matrix m n 𝕜) :
    ∃ P : Matrix m n 𝕜, P.rank ≤ k ∧ specNorm P ≤ 1 ∧ frobInner A P = kyFanNorm k A := by
  sorry

/-! ### The nuclear norm -/

/-- The **nuclear norm** (trace norm): the sum of the singular values.
[HornJohnson2013, §7.4.7]. Port of `NLAlib.nuclearNorm`. -/
noncomputable def nuclearNorm (A : Matrix m n 𝕜) : ℝ :=
  ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), singularValues A i

/-- The nuclear norm is the sum of the first `N` singular values for any `N` at least the rank.
Port of `NLAlib.nuclearNorm_eq_sum_rank_singularValues`. -/
theorem nuclearNorm_eq_sum_range (A : Matrix m n 𝕜) {N : ℕ} (hN : A.rank ≤ N) :
    nuclearNorm A = ∑ i ∈ Finset.range N, singularValues A i := by
  sorry

/-- Ky Fan norms beyond the rank are the nuclear norm. Port of `NLAlib.kyFanNorm_eq_min`. -/
theorem kyFanNorm_of_rank_le {k : ℕ} {A : Matrix m n 𝕜} (h : A.rank ≤ k) :
    kyFanNorm k A = nuclearNorm A := by
  sorry

/-- Every Ky Fan norm is at most the nuclear norm. -/
theorem kyFanNorm_le_nuclearNorm (k : ℕ) (A : Matrix m n 𝕜) : kyFanNorm k A ≤ nuclearNorm A := by
  sorry

/-- The nuclear norm is nonnegative. Port of `NLAlib.nuclearNorm_nonneg`. -/
theorem nuclearNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ nuclearNorm A := by
  sorry

/-- The nuclear norm of the zero matrix vanishes. -/
@[simp]
theorem nuclearNorm_zero : nuclearNorm (0 : Matrix m n 𝕜) = 0 := by
  sorry

/-- The nuclear norm is definite. Port of `NLAlib.nuclearNorm_eq_zero_iff`. -/
@[simp]
theorem nuclearNorm_eq_zero_iff {A : Matrix m n 𝕜} : nuclearNorm A = 0 ↔ A = 0 := by
  sorry

/-- The nuclear norm is absolutely homogeneous. Port of `NLAlib.nuclearNorm_smul`. -/
theorem nuclearNorm_smul (c : 𝕜) (A : Matrix m n 𝕜) :
    nuclearNorm (c • A) = ‖c‖ * nuclearNorm A := by
  sorry

/-- The nuclear norm is even. -/
@[simp]
theorem nuclearNorm_neg (A : Matrix m n 𝕜) : nuclearNorm (-A) = nuclearNorm A := by
  sorry

/-- The nuclear norm is invariant under the conjugate transpose. -/
@[simp]
theorem nuclearNorm_conjTranspose (A : Matrix m n 𝕜) : nuclearNorm Aᴴ = nuclearNorm A := by
  sorry

/-- The nuclear norm is invariant under the transpose. Port of `NLAlib.nuclearNorm_transpose`. -/
@[simp]
theorem nuclearNorm_transpose (A : Matrix m n 𝕜) : nuclearNorm Aᵀ = nuclearNorm A := by
  sorry

/-- The nuclear norm is invariant under relabelling rows and columns.
Port of `NLAlib.nuclearNorm_reindex`. -/
@[simp]
theorem nuclearNorm_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    nuclearNorm (A.submatrix e₁ e₂) = nuclearNorm A := by
  sorry

/-- The nuclear norm is invariant under left multiplication by a matrix with orthonormal columns.
Port of `NLAlib.nuclearNorm_orthogonal_mul`. -/
theorem HasOrthonormalCols.nuclearNorm_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : nuclearNorm (Q * A) = nuclearNorm A := by
  sorry

/-- The nuclear norm is invariant under right multiplication by the conjugate transpose of a
matrix with orthonormal columns. Port of `NLAlib.nuclearNorm_mul_orthogonal`. -/
theorem HasOrthonormalCols.nuclearNorm_mul_conjTranspose_right [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    nuclearNorm (A * Qᴴ) = nuclearNorm A := by
  sorry

/-- **The triangle inequality for the nuclear norm.**
[HornJohnson2013, §7.4.7]. Port of `NLAlib.nuclearNorm_add_le`, there over `ℝ`. -/
theorem nuclearNorm_add_le (A B : Matrix m n 𝕜) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  sorry

/-- The spectral norm is at most the nuclear norm. Port of `NLAlib.specNorm_le_nuclearNorm`. -/
theorem specNorm_le_nuclearNorm (A : Matrix m n 𝕜) : specNorm A ≤ nuclearNorm A := by
  sorry

/-- The Frobenius norm is at most the nuclear norm. Port of `NLAlib.frobNorm_le_nuclearNorm`. -/
theorem frobNorm_le_nuclearNorm (A : Matrix m n 𝕜) : frobNorm A ≤ nuclearNorm A := by
  sorry

/-- The nuclear norm is at most `√rank` times the Frobenius norm.
Port of `NLAlib.nuclearNorm_le_sqrt_rank_mul_frobNorm`. -/
theorem nuclearNorm_le_sqrt_rank_mul_frobNorm (A : Matrix m n 𝕜) :
    nuclearNorm A ≤ √(A.rank : ℝ) * frobNorm A := by
  sorry

/-- The nuclear norm is at most the rank times the spectral norm.
Port of `NLAlib.nuclearNorm_le_rank_mul_specNorm`. -/
theorem nuclearNorm_le_rank_mul_specNorm (A : Matrix m n 𝕜) :
    nuclearNorm A ≤ A.rank * specNorm A := by
  sorry

/-- The nuclear norm is submultiplicative against the spectral norm of a left factor. -/
theorem nuclearNorm_mul_le_specNorm_mul (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    nuclearNorm (A * B) ≤ specNorm A * nuclearNorm B := by
  sorry

/-- The nuclear norm is submultiplicative against the spectral norm of a right factor. -/
theorem nuclearNorm_mul_le_mul_specNorm (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    nuclearNorm (A * B) ≤ nuclearNorm A * specNorm B := by
  sorry

/-- **The factorisation bound**: `‖A B‖_* ≤ ‖A‖_F ‖B‖_F`. Equality is attained by the balanced
factorisation from the SVD, which makes the nuclear norm the convex surrogate of the rank in
factored low-rank models. [HornJohnson1991, Theorem 3.3.14(c)]. -/
theorem nuclearNorm_mul_le_frobNorm_mul_frobNorm (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    nuclearNorm (A * B) ≤ frobNorm A * frobNorm B := by
  sorry

/-! ### Duality with the spectral norm -/

/-- **Trace duality of the nuclear and spectral norms**: `|tr (Aᴴ B)| ≤ ‖A‖_* ‖B‖₂`.
[HornJohnson2013, Theorem 7.4.1.1 and §5.6]. -/
theorem norm_trace_conjTranspose_mul_le_nuclearNorm_mul_specNorm (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤ nuclearNorm A * specNorm B := by
  sorry

/-- `|⟨A, B⟩_F| ≤ ‖A‖_* ‖B‖₂`.
Port of `NLAlib.abs_frobInner_le_nuclearNorm_mul_specNorm`, there over `ℝ`. -/
theorem abs_frobInner_le_nuclearNorm_mul_specNorm (A B : Matrix m n 𝕜) :
    |frobInner A B| ≤ nuclearNorm A * specNorm B := by
  sorry

/-- The modulus of the trace of a square matrix is at most its nuclear norm. -/
theorem norm_trace_le_nuclearNorm (A : Matrix n n 𝕜) : ‖A.trace‖ ≤ nuclearNorm A := by
  sorry

/-- The nuclear norm is attained as a Frobenius inner product with a matrix of spectral norm at
most one. Port of `NLAlib.exists_specNorm_le_one_frobInner_eq_nuclearNorm`, there over `ℝ`. -/
theorem exists_specNorm_le_one_frobInner_eq_nuclearNorm (A : Matrix m n 𝕜) :
    ∃ B : Matrix m n 𝕜, specNorm B ≤ 1 ∧ frobInner A B = nuclearNorm A := by
  sorry

/-- **The nuclear norm is the dual of the spectral norm**: it is the largest Frobenius inner
product with a matrix of spectral norm at most one.
[HornJohnson2013, §5.6 and Theorem 7.4.1.1].
Port of `NLAlib.isGreatest_nuclearNorm_frobInner`, there over `ℝ`.
Result: nuclear-spectral-duality -/
theorem isGreatest_frobInner_nuclearNorm (A : Matrix m n 𝕜) :
    IsGreatest ((fun B : Matrix m n 𝕜 => frobInner A B) '' {B | specNorm B ≤ 1})
      (nuclearNorm A) := by
  sorry

/-- **The spectral norm is the dual of the nuclear norm**: it is the largest Frobenius inner
product with a matrix of nuclear norm at most one.
Port of `NLAlib.exists_nuclearNorm_le_one_frobInner_eq_specNorm`, there over `ℝ`.
Result: nuclear-spectral-duality -/
theorem isGreatest_frobInner_specNorm (A : Matrix m n 𝕜) :
    IsGreatest ((fun B : Matrix m n 𝕜 => frobInner A B) '' {B | nuclearNorm B ≤ 1})
      (specNorm A) := by
  sorry

/-! ### Hermitian and positive semidefinite matrices -/

/-- The nuclear norm of a positive semidefinite matrix is its trace.
Port of `NLAlib.nuclearNorm_eq_trace_of_posSemidef`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.nuclearNorm_eq_re_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    nuclearNorm A = RCLike.re A.trace := by
  sorry

/-- The nuclear norm of a Hermitian matrix is the sum of the absolute values of its eigenvalues.
Port of `NLAlib.nuclearNorm_eq_sum_abs_eigenvalues₀`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.nuclearNorm_eq_sum_abs_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    nuclearNorm A = ∑ i ∈ Finset.range (Fintype.card n), |eigenvalue A i| := by
  sorry

/-- For Hermitian matrices, the sorted eigenvalues are `1`-Lipschitz in the nuclear norm, as
vectors: `∑ i ∈ S, |λ_i(A) - λ_i(B)| ≤ ‖A - B‖_*`.
Port of `NLAlib.sum_abs_eigenvalues₀_add_sub_le_nuclearNorm`, there over `ℝ`. -/
theorem sum_abs_eigenvalue_sub_le_nuclearNorm_sub {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (S : Finset ℕ) :
    ∑ i ∈ S, |eigenvalue A i - eigenvalue B i| ≤ nuclearNorm (A - B) := by
  sorry

/-- The sorted singular values are `1`-Lipschitz in the nuclear norm, as vectors:
`∑ i ∈ S, |σ_i(A) - σ_i(B)| ≤ ‖A - B‖_*`. [HornJohnson1991, Theorem 3.4.5]. -/
theorem sum_abs_singularValues_sub_le_nuclearNorm_sub (A B : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, |singularValues A i - singularValues B i| ≤ nuclearNorm (A - B) := by
  sorry

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.nuclearNorm A` is nonnegative. -/
@[positivity NLAlib.nuclearNorm _]
meta def evalNuclearNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.nuclearNorm_nonneg #[e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
