/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Positivity.Core
public import NLAlib.Matrix.Majorization.Basic
public import NLAlib.Matrix.Spectral.Dilation
public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Matrix.Spectral.SVD

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
* `NLAlib.norm_trace_conjTranspose_mul_mul_le_kyFanNorm`,
  `NLAlib.re_trace_conjTranspose_mul_mul_le_kyFanNorm`: the principle for singular values.
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
  rw [(Matrix.isHermitian_conjTranspose_mul_mul Q hA).re_trace_eq_sum_range_eigenvalue]
  exact Finset.sum_le_sum fun i hi =>
    hA.eigenvalue_conjTranspose_mul_mul_le hQ (Finset.mem_range.mp hi)

/-- The maximum in Ky Fan's principle is attained by the leading eigenvectors.
Port of `NLAlib.exists_trace_compression_eq_eigenvaluePrefix`, there over `ℝ`.
Result: ky-fan-maximum-principle -/
theorem _root_.Matrix.IsHermitian.exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ} (hk : k ≤ Fintype.card n) :
    ∃ Q : Matrix n (Fin k) 𝕜, HasOrthonormalCols Q ∧
      RCLike.re (Qᴴ * A * Q).trace = ∑ i ∈ Finset.range k, eigenvalue A i := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_mul_eq_mul_diagonal
  refine ⟨U.submatrix id (Fin.castLE hk),
    hU.submatrix (Equiv.refl n) (Fin.castLE_injective hk), ?_⟩
  rw [conjTranspose_submatrix_mul_mul_submatrix, Matrix.mul_assoc, hAU,
    hU.conjTranspose_mul_cancel_left, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hk),
    Matrix.trace_diagonal, ← Fin.sum_univ_eq_sum_range (fun i => eigenvalue A i) k, map_sum]
  exact Finset.sum_congr rfl fun i _ => RCLike.ofReal_re _

/-- **Ky Fan's minimum principle.** The trace of a compression to `card p` orthonormal
directions is at least the sum of the `card p` smallest eigenvalues: with
`card p + d = card n`, `∑ i ∈ [d, card n), λ_i(A) ≤ re tr (Qᴴ A Q)`.
[HornJohnson2013, Corollary 4.3.39].
Port of `NLAlib.sum_bottom_eigenvalues_le_trace_compression`. -/
theorem _root_.Matrix.IsHermitian.sum_Ico_eigenvalue_le_re_trace_conjTranspose_mul_mul
    [DecidableEq p] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) {d : ℕ} (hd : Fintype.card p + d = Fintype.card n) :
    ∑ i ∈ Finset.Ico d (Fintype.card n), eigenvalue A i ≤ RCLike.re (Qᴴ * A * Q).trace := by
  rw [(Matrix.isHermitian_conjTranspose_mul_mul Q hA).re_trace_eq_sum_range_eigenvalue,
    Finset.sum_Ico_eq_sum_range, show Fintype.card n - d = Fintype.card p by omega]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [add_comm]
  exact hA.eigenvalue_le_eigenvalue_conjTranspose_mul_mul hQ (Finset.mem_range.mp hi) hd

/-- Eigenvalue partial sums stop growing at the size of the matrix: the sum of the first
`min k (card n)` values of `eigenvalue A` is the sum of the first `k`. It reduces a statement
about the `k` leading eigenvalues to the case `k ≤ card n`. -/
theorem sum_range_min_card_eigenvalue (A : Matrix n n 𝕜) (k : ℕ) :
    ∑ i ∈ Finset.range (min k (Fintype.card n)), eigenvalue A i =
      ∑ i ∈ Finset.range k, eigenvalue A i := by
  refine Finset.sum_subset (Finset.range_mono (min_le_left _ _)) fun i hik hi => ?_
  rw [Finset.mem_range] at hik hi
  exact eigenvalue_of_card_le A (by omega)

/-- **Subadditivity of eigenvalue partial sums.** For Hermitian `A` and `B`, the sum of the `k`
largest eigenvalues of `A + B` is at most the sums for `A` and `B`.
[HornJohnson2013, Corollary 4.3.39 and Theorem 4.3.47].
Port of `NLAlib.eigenvaluePrefix_add_le`, there over `ℝ`.
Result: ky-fan-eigenvalue-sums -/
theorem sum_range_eigenvalue_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : ℕ) :
    ∑ i ∈ Finset.range k, eigenvalue (A + B) i ≤
      ∑ i ∈ Finset.range k, eigenvalue A i + ∑ i ∈ Finset.range k, eigenvalue B i := by
  rw [← sum_range_min_card_eigenvalue (A + B), ← sum_range_min_card_eigenvalue A,
    ← sum_range_min_card_eigenvalue B]
  obtain ⟨Q, hQ, hQe⟩ := (hA.add hB).exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue
    (min_le_right k (Fintype.card n))
  have h1 := hA.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue hQ
  have h2 := hB.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue hQ
  rw [Fintype.card_fin] at h1 h2
  rw [← hQe, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, map_add]
  exact add_le_add h1 h2

/-- The eigenvalues of `A + B` are majorized by the sums of the sorted eigenvalues of `A` and
`B`. [HornJohnson2013, Theorem 4.3.47].
Port of `NLAlib.majorized_eigenvalues₀_add`, there over `ℝ`.
Result: ky-fan-eigenvalue-sums -/
theorem majorized_eigenvalue_add {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Majorized (fun i : Fin (Fintype.card n) => eigenvalue (A + B) i)
      (fun i : Fin (Fintype.card n) => eigenvalue A i + eigenvalue B i) := by
  refine ⟨?_, ?_⟩
  · refine (weaklyMajorized_fin_iff_sum_range_le (f := eigenvalue (A + B))
      (g := fun i => eigenvalue A i + eigenvalue B i) ?_ ?_).mpr fun k _ => ?_
    · exact fun i _ j hj hij => (hA.add hB).eigenvalue_le_eigenvalue hij hj
    · exact fun i _ j hj hij =>
        add_le_add (hA.eigenvalue_le_eigenvalue hij hj) (hB.eigenvalue_le_eigenvalue hij hj)
    · rw [Finset.sum_add_distrib]
      exact sum_range_eigenvalue_add_le hA hB k
  · rw [Fin.sum_univ_eq_sum_range (fun i => eigenvalue (A + B) i),
      Fin.sum_univ_eq_sum_range (fun i => eigenvalue A i + eigenvalue B i),
      Finset.sum_add_distrib, ← (hA.add hB).re_trace_eq_sum_range_eigenvalue,
      ← hA.re_trace_eq_sum_range_eigenvalue, ← hB.re_trace_eq_sum_range_eigenvalue,
      Matrix.trace_add, map_add]

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
  exact Finset.sum_nonneg fun i _ => singularValues_nonneg A i

/-- The Ky Fan `0`-norm vanishes. Port of `NLAlib.kyFanNorm_zero`. -/
@[simp]
theorem kyFanNorm_zero_left (A : Matrix m n 𝕜) : kyFanNorm 0 A = 0 := by
  rw [kyFanNorm, Finset.range_zero, Finset.sum_empty]

/-- The Ky Fan `1`-norm is the spectral norm. Port of `NLAlib.kyFanNorm_one_eq_specNorm`. -/
@[simp]
theorem kyFanNorm_one (A : Matrix m n 𝕜) : kyFanNorm 1 A = specNorm A := by
  rw [kyFanNorm, Finset.sum_range_one, singularValues_zero_eq_specNorm]

/-- Ky Fan norms increase with `k`. -/
theorem kyFanNorm_mono_left (A : Matrix m n 𝕜) {k l : ℕ} (h : k ≤ l) :
    kyFanNorm k A ≤ kyFanNorm l A := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ =>
    singularValues_nonneg A i

/-- The Ky Fan `k`-norm is at most `k` times the spectral norm. -/
theorem kyFanNorm_le_mul_specNorm (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k A ≤ k * specNorm A := by
  have h := Finset.sum_le_card_nsmul (Finset.range k) (singularValues A) (specNorm A)
    fun i _ => singularValues_le_specNorm A i
  rwa [Finset.card_range, nsmul_eq_mul] at h

/-- Ky Fan norms stop growing at the smaller dimension of the matrix:
`kyFanNorm (min k (min (card m) (card n))) A = kyFanNorm k A`. It reduces a statement about
`kyFanNorm k` to the case where `k` is at most both dimensions. -/
theorem kyFanNorm_min_card (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm (min k (min (Fintype.card m) (Fintype.card n))) A = kyFanNorm k A := by
  refine Finset.sum_subset (Finset.range_mono (min_le_left _ _)) fun i hik hi => ?_
  rw [Finset.mem_range] at hik hi
  rcases Nat.lt_or_ge i (Fintype.card m) with him | him
  · exact singularValues_of_card_cols_le A (by omega)
  · exact singularValues_of_card_rows_le A him

/-- **Ky Fan's maximum principle for singular values**, real-part form. For `U` and `V` with
orthonormal columns indexed by `p`, the real part of the trace of `Uᴴ * A * V` is at most the
Ky Fan `card p`-norm of `A`. The proof applies the eigenvalue principle to the Hermitian
dilation, compressed to the columns of `(U; V) / √2`; the modulus form is
`NLAlib.norm_trace_conjTranspose_mul_mul_le_kyFanNorm`.
[HornJohnson1991, Theorem 3.4.1]. -/
theorem re_trace_conjTranspose_mul_mul_le_kyFanNorm [DecidableEq p] (A : Matrix m n 𝕜)
    {U : Matrix m p 𝕜} {V : Matrix n p 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) :
    RCLike.re (Uᴴ * A * V).trace ≤ kyFanNorm (Fintype.card p) A := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c * c = 2⁻¹ :=
    ⟨(√2)⁻¹, by rw [← mul_inv, Real.mul_self_sqrt zero_le_two]⟩
  have hc' : star (c : 𝕜) * (c : 𝕜) = 2⁻¹ := by
    rw [RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, hc, RCLike.ofReal_inv,
      RCLike.ofReal_ofNat]
  have hW : HasOrthonormalCols ((c : 𝕜) • Matrix.fromRows U V) := by
    rw [HasOrthonormalCols, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hc', Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, hU.conjTranspose_mul_self, hV.conjTranspose_mul_self,
      ← two_smul 𝕜 (1 : Matrix p p 𝕜), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hD : ((c : 𝕜) • Matrix.fromRows U V)ᴴ * dilation A * ((c : 𝕜) • Matrix.fromRows U V) =
      (2⁻¹ : 𝕜) • ((Uᴴ * A * V)ᴴ + Uᴴ * A * V) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hc', Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, dilation,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows, Matrix.mul_zero,
      Matrix.mul_zero, zero_add, add_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc Vᴴ]
  have h := (isHermitian_dilation A).re_trace_conjTranspose_mul_mul_le_sum_eigenvalue hW
  rw [hD, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, smul_eq_mul,
    RCLike.star_def, add_comm, RCLike.add_conj, ← mul_assoc, inv_mul_cancel₀ two_ne_zero,
    one_mul, RCLike.ofReal_re] at h
  refine h.trans_eq (Finset.sum_congr rfl fun i hi => eigenvalue_dilation A ?_)
  exact lt_max_of_lt_left ((Finset.mem_range.mp hi).trans_le hU.card_le)

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
  obtain ⟨c, hc, hct⟩ := RCLike.exists_norm_eq_mul_self (Uᴴ * A * V).trace
  have hV' : HasOrthonormalCols (c • V) := by
    rw [HasOrthonormalCols, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hV.conjTranspose_mul_self, RCLike.star_def, RCLike.conj_mul, hc,
      RCLike.ofReal_one, one_pow, one_smul]
  have h := re_trace_conjTranspose_mul_mul_le_kyFanNorm A hU hV'
  rwa [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← hct, RCLike.ofReal_re] at h

/-- The maximum in Ky Fan's principle for singular values is attained by the leading singular
vectors, with a real nonnegative trace.
Port of `NLAlib.exists_trace_twoSided_compression_eq_kyFanNorm`, there over `ℝ`.
Result: ky-fan-singular-values -/
theorem exists_trace_conjTranspose_mul_mul_eq_kyFanNorm (A : Matrix m n 𝕜) {k : ℕ}
    (hkm : k ≤ Fintype.card m) (hkn : k ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin k) 𝕜) (V : Matrix n (Fin k) 𝕜), HasOrthonormalCols U ∧
      HasOrthonormalCols V ∧ (Uᴴ * A * V).trace = ((kyFanNorm k A : ℝ) : 𝕜) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A (le_min A.rank_le_card_height A.rank_le_card_width)
    (min_le_left _ _) (min_le_right _ _)
  have hk : k ≤ min (Fintype.card m) (Fintype.card n) := le_min hkm hkn
  refine ⟨U.submatrix id (Fin.castLE hk), V.submatrix id (Fin.castLE hk),
    h.hasOrthonormalCols_left.submatrix (Equiv.refl m) (Fin.castLE_injective hk),
    h.hasOrthonormalCols_right.submatrix (Equiv.refl n) (Fin.castLE_injective hk), ?_⟩
  rw [conjTranspose_submatrix_mul_mul_submatrix, h.conjTranspose_mul_mul_eq,
    Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hk), Matrix.trace_diagonal, kyFanNorm,
    ← Fin.sum_univ_eq_sum_range (fun i => singularValues A i) k, RCLike.ofReal_sum]
  rfl

/-- **The triangle inequality of the Ky Fan norms**:
`∑ i < k, σ_i(A + B) ≤ ∑ i < k, σ_i(A) + ∑ i < k, σ_i(B)`.
[HornJohnson1991, Corollary 3.4.3].
Port of `NLAlib.kyFanNorm_add_le`, there over `ℝ`.
Result: ky-fan-singular-values -/
theorem kyFanNorm_add_le (k : ℕ) (A B : Matrix m n 𝕜) :
    kyFanNorm k (A + B) ≤ kyFanNorm k A + kyFanNorm k B := by
  rw [← kyFanNorm_min_card k (A + B), ← kyFanNorm_min_card k A, ← kyFanNorm_min_card k B]
  obtain ⟨U, V, hU, hV, h⟩ := exists_trace_conjTranspose_mul_mul_eq_kyFanNorm (A + B)
    ((min_le_right k _).trans (min_le_left _ _)) ((min_le_right k _).trans (min_le_right _ _))
  have hA := norm_trace_conjTranspose_mul_mul_le_kyFanNorm A hU hV
  have hB := norm_trace_conjTranspose_mul_mul_le_kyFanNorm B hU hV
  rw [Fintype.card_fin] at hA hB
  rw [← abs_of_nonneg (kyFanNorm_nonneg _ (A + B)), ← RCLike.norm_ofReal (K := 𝕜), ← h,
    Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  exact (norm_add_le _ _).trans (add_le_add hA hB)

/-- The Frobenius inner product with a matrix of rank at most `k` and spectral norm at most one
is at most the Ky Fan `k`-norm.
Port of `NLAlib.frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one`, there over `ℝ`. -/
theorem frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one (A : Matrix m n 𝕜)
    {P : Matrix m n 𝕜} {k : ℕ} (hP : P.rank ≤ k) (hPn : specNorm P ≤ 1) :
    frobInner A P ≤ kyFanNorm k A := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD P le_rfl P.rank_le_card_height P.rank_le_card_width
  have hsum : frobInner A P =
      ∑ i : Fin P.rank, singularValues P i * RCLike.re ((Uᴴ * A * V) i i) := by
    rw [frobInner_comm, frobInner_eq_re_trace, h.conjTranspose.eq, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᴴ, Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.diagonal_mul, RCLike.re_ofReal_mul]
  let S : Finset (Fin P.rank) := Finset.univ.filter fun i => 0 ≤ RCLike.re ((Uᴴ * A * V) i i)
  have hS : ∑ i ∈ S, RCLike.re ((Uᴴ * A * V) i i) =
      RCLike.re ((U.submatrix id (Subtype.val : S → Fin P.rank))ᴴ * A *
        V.submatrix id (Subtype.val : S → Fin P.rank)).trace := by
    rw [conjTranspose_submatrix_mul_mul_submatrix, Matrix.trace, map_sum,
      ← Finset.sum_coe_sort S]
    rfl
  have hle := norm_trace_conjTranspose_mul_mul_le_kyFanNorm A
    (h.hasOrthonormalCols_left.submatrix (Equiv.refl m)
      (Subtype.val_injective : Function.Injective (Subtype.val : S → Fin P.rank)))
    (h.hasOrthonormalCols_right.submatrix (Equiv.refl n) Subtype.val_injective)
  have hcard : Fintype.card S ≤ k := by
    rw [Fintype.card_coe]
    exact (S.card_le_univ.trans_eq (Fintype.card_fin _)).trans hP
  calc frobInner A P
      = ∑ i : Fin P.rank, singularValues P i * RCLike.re ((Uᴴ * A * V) i i) := hsum
    _ ≤ ∑ i, if 0 ≤ RCLike.re ((Uᴴ * A * V) i i) then RCLike.re ((Uᴴ * A * V) i i) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with hi
        · exact mul_le_of_le_one_left hi ((singularValues_le_specNorm P i).trans hPn)
        · exact mul_nonpos_of_nonneg_of_nonpos (singularValues_nonneg P i) (not_le.mp hi).le
    _ = ∑ i ∈ S, RCLike.re ((Uᴴ * A * V) i i) := (Finset.sum_filter _ _).symm
    _ ≤ kyFanNorm (Fintype.card S) A := hS ▸ (RCLike.re_le_norm _).trans hle
    _ ≤ kyFanNorm k A := kyFanNorm_mono_left A hcard

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
