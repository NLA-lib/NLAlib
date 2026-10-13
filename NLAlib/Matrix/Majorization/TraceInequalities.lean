/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import NLAlib.ForMathlib.Algebra.BigOperators.AbelSummation
public import NLAlib.Matrix.Majorization.Schur

/-!
# Trace inequalities of von Neumann type

The trace of a product is bounded by the sum of the products of the sorted eigenvalues (for
Hermitian matrices) or singular values (in general). From these follow the Hoffman–Wielandt
inequality for Hermitian matrices and Mirsky's inequality in the Frobenius norm: sorted
eigenvalues and sorted singular values are `1`-Lipschitz in the Frobenius norm, as vectors.

## Main results

* `Matrix.IsHermitian.re_trace_mul_le_sum_eigenvalue_mul`: the Hermitian trace inequality.
* `NLAlib.norm_trace_conjTranspose_mul_le_sum_singularValues_mul`: von Neumann's trace inequality.
* `NLAlib.sum_sq_eigenvalue_sub_le_frobNorm_sub_sq`: Hoffman–Wielandt for Hermitian matrices.
* `NLAlib.sum_sq_singularValues_sub_le_frobNorm_sub_sq`: Mirsky's inequality.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- Abel summation for the trace of a product with a real diagonal matrix whose diagonal is
non-increasing: bounds on the traces of the leading principal blocks of `C` give a bound on
`re tr (C * diagonal μ)`. -/
private theorem re_trace_mul_diagonal_add_le {N : ℕ} (C : Matrix (Fin N) (Fin N) 𝕜)
    {μ g : ℕ → ℝ} (hμ : ∀ i j, i ≤ j → j < N → μ j ≤ μ i)
    (h : ∀ k (hk : k ≤ N), RCLike.re (C.submatrix (Fin.castLE hk) (Fin.castLE hk)).trace ≤
      ∑ i ∈ Finset.range k, g i)
    {c : ℝ} (hc : ∀ i < N, c ≤ μ i) :
    RCLike.re (C * Matrix.diagonal fun i : Fin N => ((μ i : ℝ) : 𝕜)).trace +
        c * (∑ i ∈ Finset.range N, g i - RCLike.re C.trace) ≤
      ∑ i ∈ Finset.range N, μ i * g i := by
  let f : ℕ → ℝ := fun i => if hi : i < N then RCLike.re (C ⟨i, hi⟩ ⟨i, hi⟩) else 0
  have hf : ∀ i : Fin N, f i = RCLike.re (C i i) := fun i => dif_pos i.isLt
  have hpart : ∀ k (hk : k ≤ N), ∑ i ∈ Finset.range k, f i =
      RCLike.re (C.submatrix (Fin.castLE hk) (Fin.castLE hk)).trace := by
    intro k hk
    rw [← Fin.sum_univ_eq_sum_range, Matrix.trace, map_sum]
    exact Finset.sum_congr rfl fun i _ => hf (Fin.castLE hk i)
  have htot : ∑ i ∈ Finset.range N, f i = RCLike.re C.trace := by
    rw [← Fin.sum_univ_eq_sum_range, Matrix.trace, map_sum]
    exact Finset.sum_congr rfl fun i _ => hf i
  have hμf : ∑ i ∈ Finset.range N, μ i * f i =
      RCLike.re (C * Matrix.diagonal fun i : Fin N => ((μ i : ℝ) : 𝕜)).trace := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => μ i * f i), Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_diagonal, RCLike.re_mul_ofReal, hf, mul_comm]
  have key := Finset.sum_range_mul_add_le_sum_range_mul_of_antitoneOn (a := μ) (b := f) (c := g)
    (fun i _ j hj hij => hμ i j hij hj) (fun k hk => (hpart k hk).trans_le (h k hk)) hc
  rwa [hμf, htot] at key

/-- A sum of nonnegative terms that vanish from index `N` on is at most the sum over
`Finset.range N`. -/
private theorem sum_le_sum_range_of_forall_eq_zero {t : ℕ → ℝ} {N : ℕ} (h0 : ∀ i, 0 ≤ t i)
    (hz : ∀ i, N ≤ i → t i = 0) (S : Finset ℕ) : ∑ i ∈ S, t i ≤ ∑ i ∈ Finset.range N, t i := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left (s₂ := Finset.range N))
    fun i _ _ => h0 i).trans_eq (Finset.sum_subset Finset.subset_union_right fun i _ hi => ?_).symm
  exact hz i (not_lt.mp fun hlt => hi (Finset.mem_range.mpr hlt))

/-- **The trace inequality for Hermitian matrices.** `re tr (A B) ≤ ∑ λ_i(A) λ_i(B)`, the
eigenvalues of each matrix in non-increasing order.
[HornJohnson2013, Theorem 4.3.53].
Port of `NLAlib.trace_mul_le_sum_eigenvalues₀_mul`, there over `ℝ`.
Result: von-neumann-trace-inequality -/
theorem _root_.Matrix.IsHermitian.re_trace_mul_le_sum_eigenvalue_mul {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace ≤
      ∑ i ∈ Finset.range (Fintype.card n), eigenvalue A i * eigenvalue B i := by
  classical
  obtain ⟨V, hV, hBV⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  have hμ : ∀ i j, i ≤ j → j < Fintype.card n → eigenvalue B j ≤ eigenvalue B i :=
    fun i j hij hj => hB.eigenvalue_le_eigenvalue hij hj
  have hpart : ∀ k (hk : k ≤ Fintype.card n),
      RCLike.re ((Vᴴ * A * V).submatrix (Fin.castLE hk) (Fin.castLE hk)).trace ≤
        ∑ i ∈ Finset.range k, eigenvalue A i := by
    intro k hk
    have h := hA.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue
      (hV.submatrix (Equiv.refl n) (Fin.castLE_injective hk))
    rwa [Equiv.coe_refl, conjTranspose_submatrix_mul_mul_submatrix, Fintype.card_fin] at h
  have htr : RCLike.re (Vᴴ * A * V).trace =
      ∑ i ∈ Finset.range (Fintype.card n), eigenvalue A i := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hV.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm, Matrix.one_mul,
      hA.re_trace_eq_sum_range_eigenvalue]
  have key := re_trace_mul_diagonal_add_le (Vᴴ * A * V) hμ hpart
    (c := eigenvalue B (Fintype.card n - 1)) fun i hi => hμ i _ (by omega) (by omega)
  rw [htr, sub_self, mul_zero, add_zero] at key
  have hAB : (A * B).trace = (Vᴴ * A * V *
      Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue B i : ℝ) : 𝕜)).trace := by
    conv_lhs => rw [hBV, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hAB]
  exact key.trans_eq (Finset.sum_congr rfl fun i _ => mul_comm _ _)

/-- The lower trace inequality for Hermitian matrices: `∑ λ_i(A) λ_{n-1-i}(B) ≤ re tr (A B)`,
the eigenvalues of `A` in non-increasing and those of `B` in non-decreasing order.
[HornJohnson2013, Theorem 4.3.53]. -/
theorem _root_.Matrix.IsHermitian.sum_eigenvalue_mul_rev_le_re_trace_mul {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ i : Fin (Fintype.card n), eigenvalue A i * eigenvalue B (Fin.rev i) ≤
      RCLike.re (A * B).trace := by
  have h := hA.re_trace_mul_le_sum_eigenvalue_mul hB.neg
  rw [Matrix.mul_neg, Matrix.trace_neg, map_neg,
    ← Fin.sum_univ_eq_sum_range (fun i => eigenvalue A i * eigenvalue (-B) i)] at h
  have h' : ∑ i : Fin (Fintype.card n), eigenvalue A i * eigenvalue (-B) i =
      -∑ i : Fin (Fintype.card n), eigenvalue A i * eigenvalue B (Fin.rev i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [eigenvalue_neg B (j := Fin.rev i) (by rw [Fin.val_rev]; omega), mul_neg]
  rw [h'] at h
  exact neg_le_neg_iff.mp h

/-- von Neumann's trace inequality for the real part of the trace. -/
private theorem re_trace_conjTranspose_mul_le_sum_singularValues_mul (A B : Matrix m n 𝕜) :
    RCLike.re (Aᴴ * B).trace ≤
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD B (le_min B.rank_le_card_height B.rank_le_card_width)
    (min_le_left _ _) (min_le_right _ _)
  have hpart : ∀ k (hk : k ≤ min (Fintype.card m) (Fintype.card n)),
      RCLike.re ((Vᴴ * Aᴴ * U).submatrix (Fin.castLE hk) (Fin.castLE hk)).trace ≤
        ∑ i ∈ Finset.range k, singularValues A i := by
    intro k hk
    have h1 := norm_trace_conjTranspose_mul_mul_le_kyFanNorm Aᴴ
      (h.hasOrthonormalCols_right.submatrix (Equiv.refl n) (Fin.castLE_injective hk))
      (h.hasOrthonormalCols_left.submatrix (Equiv.refl m) (Fin.castLE_injective hk))
    rw [Equiv.coe_refl, Equiv.coe_refl, conjTranspose_submatrix_mul_mul_submatrix,
      Fintype.card_fin, kyFanNorm, singularValues_conjTranspose] at h1
    exact (RCLike.re_le_norm _).trans h1
  have key := re_trace_mul_diagonal_add_le (Vᴴ * Aᴴ * U)
    (fun i j hij _ => singularValues_antitone B hij) hpart (c := 0)
    fun i _ => singularValues_nonneg B i
  rw [zero_mul, add_zero] at key
  have hAB : (Aᴴ * B).trace = (Vᴴ * Aᴴ * U * Matrix.diagonal
      fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
        ((singularValues B i : ℝ) : 𝕜)).trace := by
    conv_lhs => rw [h.eq, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hAB]
  exact key.trans_eq (Finset.sum_congr rfl fun i _ => mul_comm _ _)

/-- **von Neumann's trace inequality.** `|tr (Aᴴ B)| ≤ ∑ σ_i(A) σ_i(B)`.
[HornJohnson2013, Theorem 7.4.1.1].
Port of `NLAlib.frobInner_le_sum_singularValues_mul`, there over `ℝ` and for the real part.
Result: von-neumann-trace-inequality -/
theorem norm_trace_conjTranspose_mul_le_sum_singularValues_mul (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i := by
  obtain ⟨c, hc, hct⟩ := RCLike.exists_norm_eq_mul_self (Aᴴ * B).trace
  have h := re_trace_conjTranspose_mul_le_sum_singularValues_mul A (c • B)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← hct, RCLike.ofReal_re] at h
  simpa only [singularValues_smul, hc, one_mul] using h

/-- von Neumann's trace inequality for the Frobenius inner product:
`|⟨A, B⟩_F| ≤ ∑ σ_i(A) σ_i(B)`.
[HornJohnson2013, Theorem 7.4.1.1].
Port of `NLAlib.abs_frobInner_le_sum_singularValues_mul`, there over `ℝ`.
Result: von-neumann-trace-inequality -/
theorem abs_frobInner_le_sum_singularValues_mul (A B : Matrix m n 𝕜) :
    |frobInner A B| ≤
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i := by
  exact (RCLike.abs_re_le_norm _).trans
    (norm_trace_conjTranspose_mul_le_sum_singularValues_mul A B)

/-- **Hoffman–Wielandt for Hermitian matrices.** The sorted eigenvalues are `1`-Lipschitz in the
Frobenius norm: `∑ (λ_i(A) - λ_i(B))² ≤ ‖A - B‖_F²`, over any set of indices.
[HornJohnson2013, Corollary 6.3.8].
Port of `NLAlib.sum_sq_eigenvalues₀_sub_le_frobSq_sub`, there over `ℝ`.
Result: hoffman-wielandt -/
theorem sum_sq_eigenvalue_sub_le_frobNorm_sub_sq {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (S : Finset ℕ) :
    ∑ i ∈ S, (eigenvalue A i - eigenvalue B i) ^ 2 ≤ frobNorm (A - B) ^ 2 := by
  refine (sum_le_sum_range_of_forall_eq_zero (N := Fintype.card n) (fun i => sq_nonneg _)
    (fun i hi => ?_) S).trans ?_
  · rw [eigenvalue_of_card_le A hi, eigenvalue_of_card_le B hi, sub_self, zero_pow two_ne_zero]
  · have h := hA.re_trace_mul_le_sum_eigenvalue_mul hB
    have hsq : ∑ i ∈ Finset.range (Fintype.card n), (eigenvalue A i - eigenvalue B i) ^ 2 =
        ∑ i ∈ Finset.range (Fintype.card n), eigenvalue A i ^ 2 -
          2 * ∑ i ∈ Finset.range (Fintype.card n), eigenvalue A i * eigenvalue B i +
          ∑ i ∈ Finset.range (Fintype.card n), eigenvalue B i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [frobNorm_sub_sq, hA.frobNorm_sq_eq_sum_eigenvalue_sq, hB.frobNorm_sq_eq_sum_eigenvalue_sq,
      frobInner, hA.eq, hsq]
    linarith

/-- **Mirsky's inequality** in the Frobenius norm. The sorted singular values are `1`-Lipschitz:
`∑ (σ_i(A) - σ_i(B))² ≤ ‖A - B‖_F²`, over any set of indices.
[HornJohnson2013, Corollary 7.4.1.3].
Port of `NLAlib.sum_sq_singularValues_add_sub_le_frobSq`, there over `ℝ`.
Result: mirsky-inequality -/
theorem sum_sq_singularValues_sub_le_frobNorm_sub_sq (A B : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, (singularValues A i - singularValues B i) ^ 2 ≤ frobNorm (A - B) ^ 2 := by
  refine (sum_le_sum_range_of_forall_eq_zero (N := min (Fintype.card m) (Fintype.card n))
    (fun i => sq_nonneg _) (fun i hi => ?_) S).trans ?_
  · rw [(singularValues_eq_zero_iff A).mpr
        ((le_min A.rank_le_card_height A.rank_le_card_width).trans hi),
      (singularValues_eq_zero_iff B).mpr
        ((le_min B.rank_le_card_height B.rank_le_card_width).trans hi),
      sub_self, zero_pow two_ne_zero]
  · have h := (le_abs_self _).trans (abs_frobInner_le_sum_singularValues_mul A B)
    have hsq : ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
          (singularValues A i - singularValues B i) ^ 2 =
        ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 -
          2 * ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
            singularValues A i * singularValues B i +
          ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
            singularValues B i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [frobNorm_sub_sq,
      frobNorm_sq_eq_sum_range_singularValues_sq A
        (le_min A.rank_le_card_height A.rank_le_card_width),
      frobNorm_sq_eq_sum_range_singularValues_sq B
        (le_min B.rank_le_card_height B.rank_le_card_width), hsq]
    linarith

/-- The Frobenius inner product with a matrix of rank at most `r` is bounded through the
spectral norm: `⟨X, E⟩_F ≤ √r ‖X‖_F ‖E‖₂`.
Port of `NLAlib.frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le`, there over `ℝ`. -/
theorem frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le {X : Matrix m n 𝕜} {r : ℕ}
    (hX : X.rank ≤ r) (E : Matrix m n 𝕜) :
    frobInner X E ≤ √(r : ℝ) * frobNorm X * specNorm E := by
  have h1 := (le_abs_self _).trans (abs_frobInner_le_sum_singularValues_mul X E)
  have h2 : ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues X i * singularValues E i ≤
      ∑ i ∈ Finset.range r, singularValues X i * singularValues E i :=
    sum_le_sum_range_of_forall_eq_zero
      (fun i => mul_nonneg (singularValues_nonneg X i) (singularValues_nonneg E i))
      (fun i hi => by rw [(singularValues_eq_zero_iff X).mpr (hX.trans hi), zero_mul]) _
  have h3 : ∑ i ∈ Finset.range r, singularValues X i * singularValues E i ≤
      (∑ i ∈ Finset.range r, singularValues X i) * specNorm E := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (singularValues_le_specNorm E i)
      (singularValues_nonneg X i)
  have h4 : ∑ i ∈ Finset.range r, singularValues X i ≤ √(r : ℝ) * frobNorm X := by
    refine (sq_le_sq₀ (Finset.sum_nonneg fun i _ => singularValues_nonneg X i)
      (mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg X))).mp ?_
    have h5 := sq_sum_le_card_mul_sum_sq (s := Finset.range r) (f := singularValues X)
    rwa [Finset.card_range, ← frobNorm_sq_eq_sum_range_singularValues_sq X hX,
      ← Real.sq_sqrt (Nat.cast_nonneg r), ← mul_pow] at h5
  exact h1.trans (h2.trans (h3.trans (mul_le_mul_of_nonneg_right h4 (specNorm_nonneg E))))

end NLAlib
