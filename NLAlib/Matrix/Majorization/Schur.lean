/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.DoublyStochastic
public import NLAlib.Matrix.Majorization.KyFan

/-!
# Schur's theorem: the diagonal is majorized by the eigenvalues

The squared moduli of the entries of a unitary matrix form a doubly stochastic matrix, and the
diagonal of a unitarily diagonalised matrix is the image of the diagonal factor under such a
matrix. Hence the diagonal of a Hermitian matrix is majorized by its eigenvalues.

The majorization statement compares two vectors on the index type `n`. It is stated for any
unitary diagonalisation `A * U = U * diagonal d`; the form with Mathlib's `hA.eigenvalues` and
the partial-sum form with `NLAlib.eigenvalue` are corollaries.

## Main results

* `NLAlib.HasOrthonormalCols.norm_sq_mem_doublyStochastic`: orthostochastic matrices.
* `NLAlib.majorized_re_diag_of_mul_eq_mul_diagonal`: Schur's theorem.
* `Matrix.IsHermitian.sumLargest_re_diag_le_sum_eigenvalue`: the same as partial sums.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared moduli of the entries of a unitary matrix is doubly stochastic.
[HornJohnson2013, §8.7]. Port of
`NLAlib.norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols`. -/
theorem HasOrthonormalCols.norm_sq_mem_doublyStochastic {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) :
    (Matrix.of fun i j => ‖U i j‖ ^ 2) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h := congrArg (fun M : Matrix n n 𝕜 => RCLike.re (M i i)) hU.mul_conjTranspose_self
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, RCLike.star_def,
      RCLike.mul_conj, map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.one_re] at h
    simpa only [Matrix.of_apply] using h
  · have h := congrArg (fun M : Matrix n n 𝕜 => RCLike.re (M j j)) hU.conjTranspose_mul_self
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, RCLike.star_def,
      RCLike.conj_mul, map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.one_re] at h
    simpa only [Matrix.of_apply] using h

/-- The diagonal of a unitarily diagonalised matrix is the image of the diagonal factor under the
matrix of squared moduli of the unitary. -/
private theorem re_apply_self_eq_sum_norm_sq_mul {A U : Matrix n n 𝕜} {d : n → ℝ}
    (hU : HasOrthonormalCols U) (h : A * U = U * Matrix.diagonal fun i => ((d i : ℝ) : 𝕜))
    (i : n) : RCLike.re (A i i) = ∑ j, ‖U i j‖ ^ 2 * d j := by
  have hA : A = U * (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) * Uᴴ := by
    rw [← h, Matrix.mul_assoc, hU.mul_conjTranspose_self, Matrix.mul_one]
  rw [hA, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_right_comm, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

/-- **Schur's theorem.** If `A * U = U * diagonal d` for a unitary `U` and real `d`, the diagonal
of `A` is majorized by `d`: the diagonal of a Hermitian matrix is majorized by its eigenvalues,
in any enumeration.
[HornJohnson2013, Theorem 4.3.45].
Port of `NLAlib.majorized_diagonal_eigenvalues`.
Result: schur-majorization -/
theorem majorized_re_diag_of_mul_eq_mul_diagonal {A U : Matrix n n 𝕜} {d : n → ℝ}
    (hU : HasOrthonormalCols U) (h : A * U = U * Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) :
    Majorized (fun i => RCLike.re (A i i)) d := by
  have hx : (fun i => RCLike.re (A i i)) = (Matrix.of fun i j => ‖U i j‖ ^ 2) *ᵥ d :=
    funext fun i => re_apply_self_eq_sum_norm_sq_mul hU h i
  rw [hx]
  exact majorized_mulVec_of_mem_doublyStochastic d hU.norm_sq_mem_doublyStochastic

/-- Schur's theorem for Mathlib's enumeration of the eigenvalues.
[HornJohnson2013, Theorem 4.3.45].
Result: schur-majorization -/
theorem _root_.Matrix.IsHermitian.majorized_re_diag_eigenvalues {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : Majorized (fun i => RCLike.re (A i i)) hA.eigenvalues := by
  refine majorized_re_diag_of_mul_eq_mul_diagonal hA.hasOrthonormalCols_eigenvectorUnitary ?_
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  refine (congrArg (· * (hA.eigenvectorUnitary : Matrix n n 𝕜)) h).trans ?_
  rw [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  rfl

omit [DecidableEq n] in
/-- Schur's theorem as partial sums: the sum of the `k` largest diagonal entries of a Hermitian
matrix is at most the sum of its `k` largest eigenvalues.
[HornJohnson2013, Theorem 4.3.45].
Result: schur-majorization -/
theorem _root_.Matrix.IsHermitian.sumLargest_re_diag_le_sum_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) :
    sumLargest (fun i => RCLike.re (A i i)) k ≤ ∑ i ∈ Finset.range k, eigenvalue A i := by
  classical
  refine sumLargest_le fun s hs => ?_
  have hQ : HasOrthonormalCols (selectionMatrix (Subtype.val : s → n) : Matrix n s 𝕜) :=
    hasOrthonormalCols_selectionMatrix Subtype.val_injective
  have h := hA.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue hQ
  have htr : RCLike.re (A.submatrix (Subtype.val : s → n) Subtype.val).trace =
      ∑ i ∈ s, RCLike.re (A i i) := by
    rw [Matrix.trace, map_sum]
    exact Finset.sum_coe_sort s fun i => RCLike.re (A i i)
  rw [conjTranspose_selectionMatrix_mul_mul_selectionMatrix, Fintype.card_coe, hs, htr] at h
  refine h.trans_eq (Finset.sum_subset (Finset.range_mono (min_le_left _ _)) fun i hik hi => ?_)
  rw [Finset.mem_range] at hik hi
  exact eigenvalue_of_card_le A (by omega)

omit [DecidableEq n] in
/-- Each diagonal entry of a Hermitian matrix lies between its extreme eigenvalues.
Port of `NLAlib.re_diagonal_mem_Icc_eigenvalues₀`. -/
theorem _root_.Matrix.IsHermitian.re_apply_self_mem_Icc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (i : n) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    RCLike.re (A i i) ∈ Set.Icc (eigenvalue A k) (eigenvalue A 0) := by
  classical
  have key : ∀ {B : Matrix n n 𝕜}, B.IsHermitian → RCLike.re (B i i) ≤ eigenvalue B 0 := by
    intro B hB
    have h := (sum_le_sumLargest (fun j => RCLike.re (B j j)) {i}).trans
      (hB.sumLargest_re_diag_le_sum_eigenvalue _)
    rwa [Finset.sum_singleton, Finset.card_singleton, Finset.sum_range_one] at h
  refine ⟨?_, key hA⟩
  have h := key hA.neg
  rw [eigenvalue_neg A (show 0 + k + 1 = Fintype.card n by omega), Matrix.neg_apply, map_neg]
    at h
  exact neg_le_neg_iff.mp h

omit [DecidableEq n] in
/-- For a convex function, the sum over the diagonal is at most the sum over the eigenvalues.
[HornJohnson2013, Theorem 4.3.50 with 4.3.45]. -/
theorem _root_.Matrix.IsHermitian.sum_convex_re_diag_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ∑ i, φ (RCLike.re (A i i)) ≤ ∑ k ∈ Finset.range (Fintype.card n), φ (eigenvalue A k) := by
  classical
  obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
  refine (hA.majorized_re_diag_eigenvalues.sum_convex_le hφ).trans_eq ?_
  rw [← Fin.sum_univ_eq_sum_range (fun k => φ (eigenvalue A k)), ← e.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by rw [he]

end NLAlib
