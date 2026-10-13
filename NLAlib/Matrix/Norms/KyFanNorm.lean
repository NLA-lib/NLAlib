/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import NLAlib.Matrix.Majorization.DoublyStochastic
public import NLAlib.Matrix.Majorization.Lidskii

/-!
# Ky Fan norms

The Ky Fan `k`-norm `NLAlib.kyFanNorm k A` is the sum of the `k` largest singular values. Its
definition, Ky Fan's maximum principle and the triangle inequality are in
`NLAlib.Matrix.Majorization.KyFan`. This file gives the rest of its API: definiteness and
homogeneity, invariance, the comparisons with the spectral and Frobenius norms, the perturbation
bounds for singular values and for eigenvalues of Hermitian matrices, and attainment as a Frobenius
inner product. The relation to the nuclear norm is in `NLAlib.Matrix.Norms.Nuclear`.

## Main results

* `NLAlib.kyFanNorm_eq_zero_iff`, `NLAlib.kyFanNorm_smul`: definiteness and homogeneity.
* `NLAlib.HasOrthonormalCols.kyFanNorm_mul_left`,
  `NLAlib.HasOrthonormalCols.kyFanNorm_mul_conjTranspose_right`: invariance.
* `NLAlib.specNorm_le_kyFanNorm`, `NLAlib.kyFanNorm_le_sqrt_mul_frobNorm`,
  `NLAlib.kyFanNorm_mul_le_specNorm_mul`: comparison and products.
* `NLAlib.sum_abs_singularValues_sub_le_kyFanNorm_sub`,
  `NLAlib.sum_abs_eigenvalue_sub_le_kyFanNorm_sub`: perturbation of singular values and of
  eigenvalues in the Ky Fan norms.
* `Matrix.IsHermitian.sumLargest_abs_eigenvalue`: for a Hermitian matrix, the Ky Fan norms are the
  sums of the largest absolute values of the eigenvalues.
* `NLAlib.exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm`: attainment in the variational
  characterisation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Norm properties and invariance -/

/-- The Ky Fan norms of the zero matrix vanish. Port of `NLAlib.kyFanNorm_zero_matrix`. -/
@[simp]
theorem kyFanNorm_zero (k : ℕ) : kyFanNorm k (0 : Matrix m n 𝕜) = 0 := by
  simp only [kyFanNorm, singularValues_zero, Pi.zero_apply, Finset.sum_const_zero]

/-- For `k ≠ 0` the Ky Fan `k`-norm is definite. Port of `NLAlib.kyFanNorm_eq_zero_iff`. -/
theorem kyFanNorm_eq_zero_iff {k : ℕ} (hk : k ≠ 0) {A : Matrix m n 𝕜} :
    kyFanNorm k A = 0 ↔ A = 0 := by
  refine ⟨fun h => specNorm_eq_zero_iff.mp (le_antisymm ?_ (specNorm_nonneg A)), fun h => ?_⟩
  · rw [← kyFanNorm_one, ← h]
    exact kyFanNorm_mono_left A (Nat.one_le_iff_ne_zero.mpr hk)
  · rw [h, kyFanNorm_zero]

/-- Ky Fan norms are absolutely homogeneous. Port of `NLAlib.kyFanNorm_smul`. -/
theorem kyFanNorm_smul (k : ℕ) (c : 𝕜) (A : Matrix m n 𝕜) :
    kyFanNorm k (c • A) = ‖c‖ * kyFanNorm k A := by
  rw [kyFanNorm, kyFanNorm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => singularValues_smul c A i

/-- Ky Fan norms are even. -/
@[simp]
theorem kyFanNorm_neg (k : ℕ) (A : Matrix m n 𝕜) : kyFanNorm k (-A) = kyFanNorm k A := by
  simp only [kyFanNorm, singularValues_neg]

/-- Ky Fan norms are invariant under the conjugate transpose. -/
@[simp]
theorem kyFanNorm_conjTranspose (k : ℕ) (A : Matrix m n 𝕜) : kyFanNorm k Aᴴ = kyFanNorm k A := by
  simp only [kyFanNorm, singularValues_conjTranspose]

/-- Ky Fan norms are invariant under the transpose. Port of `NLAlib.kyFanNorm_transpose`. -/
@[simp]
theorem kyFanNorm_transpose (k : ℕ) (A : Matrix m n 𝕜) : kyFanNorm k Aᵀ = kyFanNorm k A := by
  simp only [kyFanNorm, singularValues_transpose]

/-- Ky Fan norms are invariant under relabelling rows and columns. -/
@[simp]
theorem kyFanNorm_submatrix_equiv (k : ℕ) (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    kyFanNorm k (A.submatrix e₁ e₂) = kyFanNorm k A := by
  simp only [kyFanNorm, singularValues_submatrix_equiv]

/-- Ky Fan norms are invariant under left multiplication by a matrix with orthonormal columns.
Port of `NLAlib.kyFanNorm_orthogonal_mul`. -/
theorem HasOrthonormalCols.kyFanNorm_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k (Q * A) = kyFanNorm k A := by
  simp only [kyFanNorm, hQ.singularValues_mul_left]

/-- Ky Fan norms are invariant under right multiplication by the conjugate transpose of a matrix
with orthonormal columns. Port of `NLAlib.kyFanNorm_mul_orthogonal`. -/
theorem HasOrthonormalCols.kyFanNorm_mul_conjTranspose_right [DecidableEq n] {Q : Matrix p n 𝕜}
    (hQ : HasOrthonormalCols Q) (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k (A * Qᴴ) = kyFanNorm k A := by
  simp only [kyFanNorm, hQ.singularValues_mul_conjTranspose_right]

/-! ### Comparison and products -/

/-- The spectral norm is at most every Ky Fan `k`-norm with `k ≠ 0`.
Port of `NLAlib.specNorm_le_kyFanNorm`. -/
theorem specNorm_le_kyFanNorm {k : ℕ} (hk : k ≠ 0) (A : Matrix m n 𝕜) :
    specNorm A ≤ kyFanNorm k A := by
  rw [← kyFanNorm_one]
  exact kyFanNorm_mono_left A (Nat.one_le_iff_ne_zero.mpr hk)

/-- The Ky Fan `k`-norm is at most `√k` times the Frobenius norm. -/
theorem kyFanNorm_le_sqrt_mul_frobNorm (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k A ≤ √(k : ℝ) * frobNorm A := by
  refine (sq_le_sq₀ (kyFanNorm_nonneg k A) (by positivity)).mp ?_
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range k) (f := singularValues A)
  have h2 : ∑ i ∈ Finset.range k, singularValues A i ^ 2 ≤ frobNorm A ^ 2 := by
    rw [frobNorm_sq_eq_sum_range_singularValues_sq A (le_max_right k A.rank)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
      fun i _ _ => sq_nonneg _
  rw [Finset.card_range] at h1
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k))

/-- Ky Fan norms are submultiplicative against the spectral norm of a left factor. -/
theorem kyFanNorm_mul_le_specNorm_mul (k : ℕ) (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    kyFanNorm k (A * B) ≤ specNorm A * kyFanNorm k B := by
  rw [kyFanNorm, kyFanNorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => singularValues_mul_le_specNorm_mul A B i

/-- Ky Fan norms are submultiplicative against the spectral norm of a right factor. -/
theorem kyFanNorm_mul_le_mul_specNorm (k : ℕ) (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    kyFanNorm k (A * B) ≤ kyFanNorm k A * specNorm B := by
  rw [kyFanNorm, kyFanNorm, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => singularValues_mul_le_mul_specNorm A B i

/-! ### Perturbation of singular values and eigenvalues -/

/-- The reverse triangle inequality for Ky Fan norms. -/
theorem abs_kyFanNorm_sub_kyFanNorm_le (k : ℕ) (A B : Matrix m n 𝕜) :
    |kyFanNorm k A - kyFanNorm k B| ≤ kyFanNorm k (A - B) := by
  have h1 := kyFanNorm_add_le k (A - B) B
  have h2 := kyFanNorm_add_le k (B - A) A
  rw [sub_add_cancel] at h1 h2
  rw [← neg_sub A B, kyFanNorm_neg] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- **Singular value perturbation in the Ky Fan norms.** For any set `S` of indices,
`∑ i ∈ S, |σ_i(A) - σ_i(B)| ≤ ‖A - B‖_(|S|)`.
[HornJohnson1991, Theorem 3.4.5]. The form of
`sum_abs_singularValues_add_sub_le_kyFanNorm` for a difference. -/
theorem sum_abs_singularValues_sub_le_kyFanNorm_sub (A B : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, |singularValues A i - singularValues B i| ≤ kyFanNorm S.card (A - B) := by
  have h := sum_abs_singularValues_add_sub_le_kyFanNorm B (A - B) S
  rwa [add_sub_cancel] at h

/-- For a Hermitian matrix, the sum of the `k` largest absolute values of the eigenvalues is the
Ky Fan `k`-norm. This is the bridge from majorization statements about eigenvalues to Ky Fan
norms. -/
theorem _root_.Matrix.IsHermitian.sumLargest_abs_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) :
    sumLargest (fun i : Fin (Fintype.card n) => |eigenvalue A i|) k = kyFanNorm k A := by
  obtain ⟨e, he⟩ := hA.exists_equiv_abs_eigenvalue_eq_singularValues
  have h : (fun i : Fin (Fintype.card n) => |eigenvalue A i|) =
      (fun i : Fin (Fintype.card n) => singularValues A i) ∘ e := funext he
  rw [h, sumLargest_comp_equiv,
    sumLargest_fin_eq_sum_range ((singularValues_antitone A).antitoneOn _),
    ← kyFanNorm_min_card k A, min_self, kyFanNorm]

/-- **Eigenvalue perturbation in the Ky Fan norms.** For Hermitian `A`, `B` and any set `S` of
indices, `∑ i ∈ S, |λ_i(A) - λ_i(B)| ≤ ‖A - B‖_(|S|)`. [Bhatia1997, Theorem III.4.4]. -/
theorem sum_abs_eigenvalue_sub_le_kyFanNorm_sub {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (S : Finset ℕ) :
    ∑ i ∈ S, |eigenvalue A i - eigenvalue B i| ≤ kyFanNorm S.card (A - B) := by
  classical
  let d : Fin (Fintype.card n) → ℝ := fun i => eigenvalue A i - eigenvalue B i
  have hmaj : Majorized d fun i : Fin (Fintype.card n) => eigenvalue (A - B) i := by
    have h := majorized_eigenvalue_add_sub hB (hA.sub hB)
    rwa [add_sub_cancel] at h
  let T : Finset (Fin (Fintype.card n)) := Finset.univ.filter fun i => (i : ℕ) ∈ S
  have hsub : T.map Fin.valEmbedding ⊆ S := fun j hj => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact (Finset.mem_filter.mp hi).2
  have hT : ∑ i ∈ S, |eigenvalue A i - eigenvalue B i| = ∑ i ∈ T, |d i| := by
    refine (Finset.sum_subset hsub fun i hiS hi => ?_).symm.trans (Finset.sum_map _ _ _)
    have hle : Fintype.card n ≤ i := not_lt.mp fun hlt => hi <| Finset.mem_map.mpr
      ⟨⟨i, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩, rfl⟩
    rw [eigenvalue_of_card_le A hle, eigenvalue_of_card_le B hle, sub_self, abs_zero]
  have hcard : T.card ≤ S.card := (Finset.card_map _).symm.trans_le (Finset.card_le_card hsub)
  calc ∑ i ∈ S, |eigenvalue A i - eigenvalue B i|
      = ∑ i ∈ T, |d i| := hT
    _ ≤ sumLargest (fun i => |d i|) T.card := sum_le_sumLargest _ T
    _ ≤ sumLargest (fun i : Fin (Fintype.card n) => |eigenvalue (A - B) i|) T.card :=
        hmaj.le_of_convexOn_of_comp_perm (convexOn_sumLargest_abs T.card) fun z σ =>
          sumLargest_comp_equiv (fun i => |z i|) σ T.card
    _ = kyFanNorm T.card (A - B) := (hA.sub hB).sumLargest_abs_eigenvalue _
    _ ≤ kyFanNorm S.card (A - B) := kyFanNorm_mono_left _ hcard

/-! ### Attainment -/

/-- The Ky Fan `k`-norm is attained as a Frobenius inner product with a matrix of rank at most
`k` and spectral norm at most one; with `frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one` this
is its variational characterisation. [HornJohnson1991, Theorem 3.4.1]. -/
theorem exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm (k : ℕ) (A : Matrix m n 𝕜) :
    ∃ P : Matrix m n 𝕜, P.rank ≤ k ∧ specNorm P ≤ 1 ∧ frobInner A P = kyFanNorm k A := by
  classical
  obtain ⟨U, V, hU, hV, h⟩ := exists_trace_conjTranspose_mul_mul_eq_kyFanNorm A
    ((min_le_right k _).trans (min_le_left _ _)) ((min_le_right k _).trans (min_le_right _ _))
  refine ⟨U * Vᴴ, ?_, ?_, ?_⟩
  · refine (Matrix.rank_mul_le_left U Vᴴ).trans ((Matrix.rank_le_card_width U).trans ?_)
    rw [Fintype.card_fin]
    exact min_le_left _ _
  · rw [hV.specNorm_mul_conjTranspose_right]
    exact hU.specNorm_le_one
  · rw [frobInner_comm, frobInner_eq_re_trace, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm, h,
      RCLike.ofReal_re, kyFanNorm_min_card]

end NLAlib
