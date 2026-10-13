/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SingularValues

/-!
# Eigenvalues of the Hermitian dilation

The Hermitian dilation `NLAlib.dilation A = fromBlocks 0 A Aᴴ 0` of a matrix `A` of any shape has
eigenvalues `± σ_i(A)` and zeros. Its leading eigenvalues are therefore the singular values of
`A`, and its largest eigenvalue is the spectral norm of `A`. This is how statements about
eigenvalues of Hermitian matrices, in particular matrix concentration inequalities, are
transferred to singular values of rectangular matrices.

## Main results

* `NLAlib.eigenvalue_dilation`: `eigenvalue (dilation A) k = singularValues A k` below the larger
  dimension of `A`.
* `NLAlib.eigenvalue_dilation_of_add_add_one_eq`: the trailing eigenvalues are the negated
  singular values.
* `NLAlib.eigenvalue_zero_dilation`: `eigenvalue (dilation A) 0 = specNorm A`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The quadratic form of the dilation at `(y, x)` is twice the real part of the pairing of `y`
with `A x`. -/
private theorem re_quadForm_dilation (A : Matrix m n 𝕜) (y : m → 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm (dilation A) (Sum.elim y x)) = 2 * RCLike.re (star y ⬝ᵥ (A *ᵥ x)) := by
  have h : star x ⬝ᵥ (Aᴴ *ᵥ y) = star (star y ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Matrix.star_dotProduct]
  rw [quadForm_def, dilation_mulVec, Function.star_sumElim, sumElim_dotProduct_sumElim, h,
    map_add, RCLike.star_def, RCLike.conj_re, two_mul]

/-- The eigenvalues of the dilation are bounded above by the singular values. -/
private theorem eigenvalue_dilation_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < Fintype.card m + Fintype.card n) :
    eigenvalue (dilation A) k ≤ singularValues A k := by
  obtain ⟨W, hW, hWle⟩ := exists_submodule_norm_mulVec_le A k
  let f : (m ⊕ n → 𝕜) →ₗ[𝕜] (n → 𝕜) ⧸ W := W.mkQ ∘ₗ LinearMap.funLeft 𝕜 𝕜 Sum.inr
  refine (isHermitian_dilation A).eigenvalue_le_of_forall_mem (by rwa [Fintype.card_sum])
    (LinearMap.ker f) ?_ fun z hz => ?_
  · have h1 := f.finrank_range_add_finrank_ker
    have h2 : Module.finrank 𝕜 (LinearMap.range f) ≤ Module.finrank 𝕜 ((n → 𝕜) ⧸ W) :=
      Submodule.finrank_le _
    have h3 := W.finrank_quotient_add_finrank
    rw [Module.finrank_fintype_fun_eq_card] at h1 h3
    omega
  · have hx : z ∘ Sum.inr ∈ W := (Submodule.Quotient.mk_eq_zero W).mp (LinearMap.mem_ker.mp hz)
    have h1 := re_inner_le_norm (𝕜 := 𝕜) (WithLp.toLp 2 (z ∘ Sum.inl))
      (WithLp.toLp 2 (A *ᵥ (z ∘ Sum.inr)))
    have h2 := mul_le_mul_of_nonneg_left (hWle _ hx) (norm_nonneg (WithLp.toLp 2 (z ∘ Sum.inl)))
    have h3 := mul_nonneg (singularValues_nonneg A k)
      (sq_nonneg (‖WithLp.toLp 2 (z ∘ Sum.inl)‖ - ‖WithLp.toLp 2 (z ∘ Sum.inr)‖))
    rw [← Sum.elim_comp_inl_inr z, re_quadForm_dilation, EuclideanSpace.norm_toLp_sumElim_sq,
      ← EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct]
    linarith

/-- The spectrum of the dilation is symmetric about zero: negating the dilation does not change
its eigenvalue sequence. -/
private theorem eigenvalue_neg_dilation (A : Matrix m n 𝕜) (k : ℕ) :
    eigenvalue (-dilation A) k = eigenvalue (dilation A) k := by
  classical
  have hJ : HasOrthonormalCols
      (Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 (-1 : Matrix n n 𝕜)) := by
    rw [hasOrthonormalCols_iff, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_neg,
      Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, neg_mul_neg]
  have hE : (Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 (-1 : Matrix n n 𝕜))ᴴ * dilation A *
      Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 (-1 : Matrix n n 𝕜) = -dilation A := by
    simp only [dilation, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_neg, Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_neg, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_zero]
  rw [← hE]
  exact eigenvalue_conjTranspose_mul_mul_of_card_eq (dilation A) hJ rfl k

/-- A real sequence that is antisymmetric under reversal of its first `N` indices, is bounded
above by a nonnegative sequence `s`, and whose squares sum to twice those of `s`, has positive
part `s`. -/
private theorem max_zero_eq_of_sum_sq_eq {e s : ℕ → ℝ} {N : ℕ}
    (hsym : ∀ k < N, e (N - 1 - k) = -e k) (hs : ∀ k, 0 ≤ s k) (hle : ∀ k < N, e k ≤ s k)
    (hsum : ∑ k ∈ Finset.range N, e k ^ 2 = 2 * ∑ k ∈ Finset.range N, s k ^ 2) {k : ℕ}
    (hk : k < N) : max (e k) 0 = s k := by
  have hsplit : ∀ x : ℝ, x ^ 2 = max x 0 ^ 2 + max (-x) 0 ^ 2 := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
  have h1 : ∑ k ∈ Finset.range N, e k ^ 2 = 2 * ∑ k ∈ Finset.range N, max (e k) 0 ^ 2 := by
    rw [two_mul]
    nth_rw 3 [← Finset.sum_range_reflect]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hsym k (Finset.mem_range.mp hk)]
    exact hsplit (e k)
  have h2 : ∀ j ∈ Finset.range N, max (e j) 0 ^ 2 ≤ s j ^ 2 := fun j hj =>
    pow_le_pow_left₀ (le_max_right _ _) (max_le (hle j (Finset.mem_range.mp hj)) (hs j)) 2
  have h3 : ∑ j ∈ Finset.range N, max (e j) 0 ^ 2 = ∑ j ∈ Finset.range N, s j ^ 2 := by
    linarith
  exact (sq_eq_sq₀ (le_max_right _ _) (hs k)).mp
    ((Finset.sum_eq_sum_iff_of_le h2).mp h3 k (Finset.mem_range.mpr hk))

/-- The leading eigenvalues of the Hermitian dilation are the singular values of the matrix.
The dilation has eigenvalues `± σ_i` and zeros, so the statement holds below the larger
dimension. [HornJohnson2013, Theorem 7.3.3]. -/
theorem eigenvalue_dilation (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < max (Fintype.card m) (Fintype.card n)) :
    eigenvalue (dilation A) k = singularValues A k := by
  have hcard : Fintype.card (m ⊕ n) = Fintype.card m + Fintype.card n := Fintype.card_sum
  have hkN : k < Fintype.card m + Fintype.card n :=
    hk.trans_le (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
  have hsym : ∀ j < Fintype.card m + Fintype.card n,
      eigenvalue (dilation A) (Fintype.card m + Fintype.card n - 1 - j) =
        -eigenvalue (dilation A) j := fun j hj => by
    rw [← eigenvalue_neg_dilation A (Fintype.card m + Fintype.card n - 1 - j)]
    exact eigenvalue_neg (dilation A) (by omega)
  have hsum : ∑ j ∈ Finset.range (Fintype.card m + Fintype.card n),
      eigenvalue (dilation A) j ^ 2 =
        2 * ∑ j ∈ Finset.range (Fintype.card m + Fintype.card n), singularValues A j ^ 2 := by
    rw [← hcard, ← (isHermitian_dilation A).frobNorm_sq_eq_sum_eigenvalue_sq,
      frobNorm_dilation_sq, hcard, frobNorm_sq_eq_sum_range_singularValues_sq A
        (A.rank_le_card_width.trans (Nat.le_add_left _ _))]
  have hmax := max_zero_eq_of_sum_sq_eq hsym (singularValues_nonneg A)
    (fun j hj => eigenvalue_dilation_le A hj) hsum hkN
  have hj : Fintype.card m + Fintype.card n - 1 - k < Fintype.card m + Fintype.card n := by
    omega
  have h0 : 0 ≤ eigenvalue (dilation A) k := by
    have h1 := hsym _ hj
    rw [show Fintype.card m + Fintype.card n - 1 -
      (Fintype.card m + Fintype.card n - 1 - k) = k by omega] at h1
    rw [h1, neg_nonneg]
    refine (eigenvalue_dilation_le A hj).trans_eq ?_
    rcases lt_max_iff.mp hk with h | h
    · exact singularValues_of_card_cols_le A (by omega)
    · exact singularValues_of_card_rows_le A (by omega)
  rw [← hmax, max_eq_left h0]

/-- The trailing eigenvalues of the Hermitian dilation are the negated singular values of the
matrix: `eigenvalue (dilation A) j = -singularValues A k` for the mirror index `j` of `k`, that
is `k + j + 1 = card m + card n`, with `k` below the larger dimension. Together with
`NLAlib.eigenvalue_dilation` this describes the whole spectrum `± σ_i(A)` and zeros.
[HornJohnson2013, Theorem 7.3.3]. -/
theorem eigenvalue_dilation_of_add_add_one_eq (A : Matrix m n 𝕜) {k j : ℕ}
    (hk : k < max (Fintype.card m) (Fintype.card n))
    (h : k + j + 1 = Fintype.card m + Fintype.card n) :
    eigenvalue (dilation A) j = -singularValues A k := by
  have h' := eigenvalue_neg (dilation A) (k := k) (j := j) (by rw [Fintype.card_sum]; exact h)
  rw [← dilation_neg, eigenvalue_dilation _ hk, singularValues_neg] at h'
  linarith

/-- The largest eigenvalue of the Hermitian dilation is the spectral norm of the matrix.
[Tropp2015, (2.1.28)]. -/
theorem eigenvalue_zero_dilation (A : Matrix m n 𝕜) : eigenvalue (dilation A) 0 = specNorm A := by
  rw [← singularValues_zero_eq_specNorm]
  by_cases h : 0 < max (Fintype.card m) (Fintype.card n)
  · exact eigenvalue_dilation A h
  · rw [lt_max_iff, not_or, not_lt, not_lt] at h
    rw [eigenvalue_of_card_le _ (by rw [Fintype.card_sum]; omega),
      singularValues_of_card_cols_le A h.2]

end NLAlib
