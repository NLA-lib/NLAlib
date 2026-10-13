/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.Lidskii
public import NLAlib.Matrix.Majorization.TraceInequalities
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
* `Matrix.PosSemidef.nuclearNorm_eq_re_trace`,
  `Matrix.IsHermitian.nuclearNorm_eq_sum_abs_eigenvalue`.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Ky Fan norms -/

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

/-- The absolute values of the eigenvalues of a Hermitian matrix are its singular values, up to a
permutation: the eigendecomposition is a singular value decomposition once the signs of the
eigenvalues are moved into the left factor. -/
private theorem exists_equiv_abs_eigenvalue_eq_singularValues {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    ∃ e : Fin (Fintype.card n) ≃ Fin (Fintype.card n),
      ∀ i : Fin (Fintype.card n), |eigenvalue A i| = singularValues A (e i) := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  let s : Fin (Fintype.card n) → ℝ := fun i => if 0 ≤ eigenvalue A i then 1 else -1
  have hs : ∀ i, s i * s i = 1 := fun i => by
    simp only [s]
    split_ifs <;> norm_num
  have hsa : ∀ i, s i * |eigenvalue A i| = eigenvalue A i := fun i => by
    simp only [s]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h), neg_mul_neg, one_mul]
  have hD : HasOrthonormalCols (Matrix.diagonal fun i => ((s i : ℝ) : 𝕜)) := by
    rw [HasOrthonormalCols, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, hs,
      RCLike.ofReal_one]
  have h : IsSVD A (U * Matrix.diagonal fun i => ((s i : ℝ) : 𝕜))
      (fun i => |eigenvalue A i|) U := by
    refine ⟨hU.mul hD, hU, fun i => abs_nonneg _, ?_⟩
    rw [Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
    simp only [← RCLike.ofReal_mul, hsa]
    exact hAU
  obtain ⟨e, he⟩ := h.exists_equiv_singularValues_eq
  exact ⟨e.trans (finCongr (Fintype.card_fin _)), fun i => he i⟩

/-- For a Hermitian matrix, the sum of the `k` largest absolute values of the eigenvalues is the
Ky Fan `k`-norm. -/
private theorem sumLargest_abs_eigenvalue {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    sumLargest (fun i : Fin (Fintype.card n) => |eigenvalue A i|) k = kyFanNorm k A := by
  obtain ⟨e, he⟩ := exists_equiv_abs_eigenvalue_eq_singularValues hA
  have h : (fun i : Fin (Fintype.card n) => |eigenvalue A i|) =
      (fun i : Fin (Fintype.card n) => singularValues A i) ∘ e := funext he
  rw [h, sumLargest_comp_equiv,
    sumLargest_fin_eq_sum_range ((singularValues_antitone A).antitoneOn _),
    ← kyFanNorm_min_card k A, min_self, kyFanNorm]

/-- The sum of the `k` largest absolute values of the entries is a convex function of a real
vector. -/
private theorem convexOn_sumLargest_abs {ι : Type*} [Fintype ι] (k : ℕ) :
    ConvexOn ℝ Set.univ fun z : ι → ℝ => sumLargest (fun i => |z i|) k := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  have h : (fun i => |(a • x + b • y) i|) ≤ (a • fun i => |x i|) + b • fun i => |y i| := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
      _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc sumLargest (fun i => |(a • x + b • y) i|) k
      ≤ sumLargest ((a • fun i => |x i|) + b • fun i => |y i|) k := sumLargest_mono h k
    _ ≤ sumLargest (a • fun i => |x i|) k + sumLargest (b • fun i => |y i|) k :=
        sumLargest_add_le _ _ k
    _ = a • sumLargest (fun i => |x i|) k + b • sumLargest (fun i => |y i|) k := by
        rw [sumLargest_smul ha, sumLargest_smul hb, smul_eq_mul, smul_eq_mul]

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
    _ = kyFanNorm T.card (A - B) := sumLargest_abs_eigenvalue (hA.sub hB) _
    _ ≤ kyFanNorm S.card (A - B) := kyFanNorm_mono_left _ hcard

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

/-! ### The nuclear norm -/

/-- The **nuclear norm** (trace norm): the sum of the singular values.
[HornJohnson2013, §7.4.7]. Port of `NLAlib.nuclearNorm`. -/
noncomputable def nuclearNorm (A : Matrix m n 𝕜) : ℝ :=
  ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), singularValues A i

/-- The nuclear norm is the sum of the first `N` singular values for any `N` at least the rank.
Port of `NLAlib.nuclearNorm_eq_sum_rank_singularValues`. -/
theorem nuclearNorm_eq_sum_range (A : Matrix m n 𝕜) {N : ℕ} (hN : A.rank ≤ N) :
    nuclearNorm A = ∑ i ∈ Finset.range N, singularValues A i := by
  have key : ∀ {M : ℕ}, A.rank ≤ M → ∑ i ∈ Finset.range M, singularValues A i =
      ∑ i ∈ Finset.range A.rank, singularValues A i := fun hM =>
    (Finset.sum_subset (Finset.range_mono hM) fun i _ hi =>
      (singularValues_eq_zero_iff A).mpr (not_lt.mp fun h => hi (Finset.mem_range.mpr h))).symm
  rw [nuclearNorm, key hN, key (le_min A.rank_le_card_height A.rank_le_card_width)]

/-- Ky Fan norms beyond the rank are the nuclear norm. Port of `NLAlib.kyFanNorm_eq_min`. -/
theorem kyFanNorm_of_rank_le {k : ℕ} {A : Matrix m n 𝕜} (h : A.rank ≤ k) :
    kyFanNorm k A = nuclearNorm A := by
  exact (nuclearNorm_eq_sum_range A h).symm

/-- Every Ky Fan norm is at most the nuclear norm. -/
theorem kyFanNorm_le_nuclearNorm (k : ℕ) (A : Matrix m n 𝕜) : kyFanNorm k A ≤ nuclearNorm A := by
  rw [← kyFanNorm_min_card]
  exact kyFanNorm_mono_left A (min_le_right _ _)

/-- The nuclear norm is nonnegative. Port of `NLAlib.nuclearNorm_nonneg`. -/
theorem nuclearNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ nuclearNorm A := by
  exact Finset.sum_nonneg fun i _ => singularValues_nonneg A i

/-- The nuclear norm of the zero matrix vanishes. -/
@[simp]
theorem nuclearNorm_zero : nuclearNorm (0 : Matrix m n 𝕜) = 0 := by
  exact kyFanNorm_zero _

/-- The nuclear norm is definite. Port of `NLAlib.nuclearNorm_eq_zero_iff`. -/
@[simp]
theorem nuclearNorm_eq_zero_iff {A : Matrix m n 𝕜} : nuclearNorm A = 0 ↔ A = 0 := by
  refine ⟨fun h => specNorm_eq_zero_iff.mp (le_antisymm ?_ (specNorm_nonneg A)), fun h => ?_⟩
  · exact ((kyFanNorm_one A).symm.trans_le (kyFanNorm_le_nuclearNorm 1 A)).trans_eq h
  · rw [h, nuclearNorm_zero]

/-- The nuclear norm is absolutely homogeneous. Port of `NLAlib.nuclearNorm_smul`. -/
theorem nuclearNorm_smul (c : 𝕜) (A : Matrix m n 𝕜) :
    nuclearNorm (c • A) = ‖c‖ * nuclearNorm A := by
  exact kyFanNorm_smul _ c A

/-- The nuclear norm is even. -/
@[simp]
theorem nuclearNorm_neg (A : Matrix m n 𝕜) : nuclearNorm (-A) = nuclearNorm A := by
  exact kyFanNorm_neg _ A

/-- The nuclear norm is invariant under the conjugate transpose. -/
@[simp]
theorem nuclearNorm_conjTranspose (A : Matrix m n 𝕜) : nuclearNorm Aᴴ = nuclearNorm A := by
  rw [nuclearNorm, nuclearNorm, singularValues_conjTranspose, min_comm]

/-- The nuclear norm is invariant under the transpose. Port of `NLAlib.nuclearNorm_transpose`. -/
@[simp]
theorem nuclearNorm_transpose (A : Matrix m n 𝕜) : nuclearNorm Aᵀ = nuclearNorm A := by
  rw [nuclearNorm, nuclearNorm, singularValues_transpose, min_comm]

/-- The nuclear norm is invariant under relabelling rows and columns.
Port of `NLAlib.nuclearNorm_reindex`. -/
@[simp]
theorem nuclearNorm_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    nuclearNorm (A.submatrix e₁ e₂) = nuclearNorm A := by
  rw [nuclearNorm, nuclearNorm, singularValues_submatrix_equiv, Fintype.card_congr e₁,
    Fintype.card_congr e₂]

/-- The nuclear norm is invariant under left multiplication by a matrix with orthonormal columns.
Port of `NLAlib.nuclearNorm_orthogonal_mul`. -/
theorem HasOrthonormalCols.nuclearNorm_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : nuclearNorm (Q * A) = nuclearNorm A := by
  rw [nuclearNorm_eq_sum_range (Q * A) ((Matrix.rank_mul_le_right Q A).trans
    (le_min A.rank_le_card_height A.rank_le_card_width)), hQ.singularValues_mul_left, nuclearNorm]

/-- The nuclear norm is invariant under right multiplication by the conjugate transpose of a
matrix with orthonormal columns. Port of `NLAlib.nuclearNorm_mul_orthogonal`. -/
theorem HasOrthonormalCols.nuclearNorm_mul_conjTranspose_right [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    nuclearNorm (A * Qᴴ) = nuclearNorm A := by
  rw [nuclearNorm_eq_sum_range (A * Qᴴ) ((Matrix.rank_mul_le_left A Qᴴ).trans
    (le_min A.rank_le_card_height A.rank_le_card_width)),
    hQ.singularValues_mul_conjTranspose_right, nuclearNorm]

/-- **The triangle inequality for the nuclear norm.**
[HornJohnson2013, §7.4.7]. Port of `NLAlib.nuclearNorm_add_le`, there over `ℝ`. -/
theorem nuclearNorm_add_le (A B : Matrix m n 𝕜) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  exact kyFanNorm_add_le _ A B

/-- The spectral norm is at most the nuclear norm. Port of `NLAlib.specNorm_le_nuclearNorm`. -/
theorem specNorm_le_nuclearNorm (A : Matrix m n 𝕜) : specNorm A ≤ nuclearNorm A := by
  exact (kyFanNorm_one A).symm.trans_le (kyFanNorm_le_nuclearNorm 1 A)

/-- The Frobenius norm is at most the nuclear norm. Port of `NLAlib.frobNorm_le_nuclearNorm`. -/
theorem frobNorm_le_nuclearNorm (A : Matrix m n 𝕜) : frobNorm A ≤ nuclearNorm A := by
  refine (sq_le_sq₀ (frobNorm_nonneg A) (nuclearNorm_nonneg A)).mp ?_
  rw [frobNorm_sq_eq_sum_range_singularValues_sq A
    (le_min A.rank_le_card_height A.rank_le_card_width)]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => singularValues_nonneg A i

/-- The nuclear norm is at most `√rank` times the Frobenius norm.
Port of `NLAlib.nuclearNorm_le_sqrt_rank_mul_frobNorm`. -/
theorem nuclearNorm_le_sqrt_rank_mul_frobNorm (A : Matrix m n 𝕜) :
    nuclearNorm A ≤ √(A.rank : ℝ) * frobNorm A := by
  exact (kyFanNorm_of_rank_le le_rfl).symm.trans_le (kyFanNorm_le_sqrt_mul_frobNorm _ A)

/-- The nuclear norm is at most the rank times the spectral norm.
Port of `NLAlib.nuclearNorm_le_rank_mul_specNorm`. -/
theorem nuclearNorm_le_rank_mul_specNorm (A : Matrix m n 𝕜) :
    nuclearNorm A ≤ A.rank * specNorm A := by
  exact (kyFanNorm_of_rank_le le_rfl).symm.trans_le (kyFanNorm_le_mul_specNorm _ A)

/-- The nuclear norm is submultiplicative against the spectral norm of a left factor. -/
theorem nuclearNorm_mul_le_specNorm_mul (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    nuclearNorm (A * B) ≤ specNorm A * nuclearNorm B := by
  rw [← kyFanNorm_of_rank_le ((Matrix.rank_mul_le_right A B).trans
    (le_min B.rank_le_card_height B.rank_le_card_width))]
  exact kyFanNorm_mul_le_specNorm_mul _ A B

/-- The nuclear norm is submultiplicative against the spectral norm of a right factor. -/
theorem nuclearNorm_mul_le_mul_specNorm (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    nuclearNorm (A * B) ≤ nuclearNorm A * specNorm B := by
  rw [← kyFanNorm_of_rank_le ((Matrix.rank_mul_le_left A B).trans
    (le_min A.rank_le_card_height A.rank_le_card_width))]
  exact kyFanNorm_mul_le_mul_specNorm _ A B

/-- **The factorisation bound**: `‖A B‖_* ≤ ‖A‖_F ‖B‖_F`. Equality is attained by the balanced
factorisation from the SVD, which makes the nuclear norm the convex surrogate of the rank in
factored low-rank models. [HornJohnson1991, Theorem 3.3.14(c)]. -/
theorem nuclearNorm_mul_le_frobNorm_mul_frobNorm (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    nuclearNorm (A * B) ≤ frobNorm A * frobNorm B := by
  obtain ⟨W, -, hW, hWe⟩ := exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm
    (min (Fintype.card m) (Fintype.card n)) (A * B)
  calc nuclearNorm (A * B) = frobInner (A * B) W := hWe.symm
    _ = frobInner B (Aᴴ * W) := frobInner_mul_left A B W
    _ ≤ frobNorm B * frobNorm (Aᴴ * W) := frobInner_le _ _
    _ ≤ frobNorm B * (frobNorm Aᴴ * specNorm W) :=
        mul_le_mul_of_nonneg_left (frobNorm_mul_le_frobNorm_mul_specNorm _ _) (frobNorm_nonneg B)
    _ ≤ frobNorm B * (frobNorm A * 1) := by
        rw [frobNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (frobNorm_nonneg A))
          (frobNorm_nonneg B)
    _ = frobNorm A * frobNorm B := by rw [mul_one, mul_comm]

/-! ### Duality with the spectral norm -/

/-- **Trace duality of the nuclear and spectral norms**: `|tr (Aᴴ B)| ≤ ‖A‖_* ‖B‖₂`.
[HornJohnson2013, Theorem 7.4.1.1 and §5.6]. -/
theorem norm_trace_conjTranspose_mul_le_nuclearNorm_mul_specNorm (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤ nuclearNorm A * specNorm B := by
  refine (norm_trace_conjTranspose_mul_le_sum_singularValues_mul A B).trans ?_
  rw [nuclearNorm, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (singularValues_le_specNorm B i) (singularValues_nonneg A i)

/-- `|⟨A, B⟩_F| ≤ ‖A‖_* ‖B‖₂`.
Port of `NLAlib.abs_frobInner_le_nuclearNorm_mul_specNorm`, there over `ℝ`. -/
theorem abs_frobInner_le_nuclearNorm_mul_specNorm (A B : Matrix m n 𝕜) :
    |frobInner A B| ≤ nuclearNorm A * specNorm B := by
  exact (RCLike.abs_re_le_norm _).trans
    (norm_trace_conjTranspose_mul_le_nuclearNorm_mul_specNorm A B)

/-- The modulus of the trace of a square matrix is at most its nuclear norm. -/
theorem norm_trace_le_nuclearNorm (A : Matrix n n 𝕜) : ‖A.trace‖ ≤ nuclearNorm A := by
  classical
  have h := norm_trace_conjTranspose_mul_le_nuclearNorm_mul_specNorm A (1 : Matrix n n 𝕜)
  rw [Matrix.mul_one, Matrix.trace_conjTranspose, norm_star] at h
  exact h.trans (mul_le_of_le_one_right (nuclearNorm_nonneg A) specNorm_one_le)

/-- The nuclear norm is attained as a Frobenius inner product with a matrix of spectral norm at
most one. Port of `NLAlib.exists_specNorm_le_one_frobInner_eq_nuclearNorm`, there over `ℝ`. -/
theorem exists_specNorm_le_one_frobInner_eq_nuclearNorm (A : Matrix m n 𝕜) :
    ∃ B : Matrix m n 𝕜, specNorm B ≤ 1 ∧ frobInner A B = nuclearNorm A := by
  obtain ⟨W, -, hW, hWe⟩ := exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm
    (min (Fintype.card m) (Fintype.card n)) A
  exact ⟨W, hW, hWe⟩

/-- **The nuclear norm is the dual of the spectral norm**: it is the largest Frobenius inner
product with a matrix of spectral norm at most one.
[HornJohnson2013, §5.6 and Theorem 7.4.1.1].
Port of `NLAlib.isGreatest_nuclearNorm_frobInner`, there over `ℝ`.
Result: nuclear-spectral-duality -/
theorem isGreatest_frobInner_nuclearNorm (A : Matrix m n 𝕜) :
    IsGreatest ((fun B : Matrix m n 𝕜 => frobInner A B) '' {B | specNorm B ≤ 1})
      (nuclearNorm A) := by
  refine ⟨exists_specNorm_le_one_frobInner_eq_nuclearNorm A, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact (le_abs_self _).trans ((abs_frobInner_le_nuclearNorm_mul_specNorm A B).trans
    (mul_le_of_le_one_right (nuclearNorm_nonneg A) hB))

/-- **The spectral norm is the dual of the nuclear norm**: it is the largest Frobenius inner
product with a matrix of nuclear norm at most one.
Port of `NLAlib.exists_nuclearNorm_le_one_frobInner_eq_specNorm`, there over `ℝ`.
Result: nuclear-spectral-duality -/
theorem isGreatest_frobInner_specNorm (A : Matrix m n 𝕜) :
    IsGreatest ((fun B : Matrix m n 𝕜 => frobInner A B) '' {B | nuclearNorm B ≤ 1})
      (specNorm A) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hr, hP, hPe⟩ := exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm 1 A
    refine ⟨P, ?_, hPe.trans (kyFanNorm_one A)⟩
    calc nuclearNorm P ≤ P.rank * specNorm P := nuclearNorm_le_rank_mul_specNorm P
      _ ≤ 1 * 1 := mul_le_mul (mod_cast hr) hP (specNorm_nonneg P) zero_le_one
      _ = 1 := one_mul 1
  · rintro _ ⟨B, hB, rfl⟩
    have h := abs_frobInner_le_nuclearNorm_mul_specNorm B A
    rw [frobInner_comm] at h
    exact (le_abs_self _).trans (h.trans (mul_le_of_le_one_left (specNorm_nonneg A) hB))

/-! ### Hermitian and positive semidefinite matrices -/

/-- The nuclear norm of a positive semidefinite matrix is its trace.
Port of `NLAlib.nuclearNorm_eq_trace_of_posSemidef`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.nuclearNorm_eq_re_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    nuclearNorm A = RCLike.re A.trace := by
  rw [nuclearNorm, min_self, hA.singularValues_eq_eigenvalue,
    hA.isHermitian.re_trace_eq_sum_range_eigenvalue]

/-- The nuclear norm of a Hermitian matrix is the sum of the absolute values of its eigenvalues.
Port of `NLAlib.nuclearNorm_eq_sum_abs_eigenvalues₀`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.nuclearNorm_eq_sum_abs_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    nuclearNorm A = ∑ i ∈ Finset.range (Fintype.card n), |eigenvalue A i| := by
  obtain ⟨e, he⟩ := exists_equiv_abs_eigenvalue_eq_singularValues hA
  calc nuclearNorm A = ∑ i : Fin (Fintype.card n), singularValues A i := by
        rw [nuclearNorm, min_self, Fin.sum_univ_eq_sum_range]
    _ = ∑ i : Fin (Fintype.card n), singularValues A (e i) :=
        (Equiv.sum_comp e fun i => singularValues A i).symm
    _ = ∑ i : Fin (Fintype.card n), |eigenvalue A i| :=
        Finset.sum_congr rfl fun i _ => (he i).symm
    _ = ∑ i ∈ Finset.range (Fintype.card n), |eigenvalue A i| :=
        Fin.sum_univ_eq_sum_range (fun i => |eigenvalue A i|) _

/-- For Hermitian matrices, the sorted eigenvalues are `1`-Lipschitz in the nuclear norm, as
vectors: `∑ i ∈ S, |λ_i(A) - λ_i(B)| ≤ ‖A - B‖_*`.
Port of `NLAlib.sum_abs_eigenvalues₀_add_sub_le_nuclearNorm`, there over `ℝ`. -/
theorem sum_abs_eigenvalue_sub_le_nuclearNorm_sub {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (S : Finset ℕ) :
    ∑ i ∈ S, |eigenvalue A i - eigenvalue B i| ≤ nuclearNorm (A - B) := by
  exact (sum_abs_eigenvalue_sub_le_kyFanNorm_sub hA hB S).trans (kyFanNorm_le_nuclearNorm _ _)

/-- The sorted singular values are `1`-Lipschitz in the nuclear norm, as vectors:
`∑ i ∈ S, |σ_i(A) - σ_i(B)| ≤ ‖A - B‖_*`. [HornJohnson1991, Theorem 3.4.5]. -/
theorem sum_abs_singularValues_sub_le_nuclearNorm_sub (A B : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, |singularValues A i - singularValues B i| ≤ nuclearNorm (A - B) := by
  exact (sum_abs_singularValues_sub_le_kyFanNorm_sub A B S).trans (kyFanNorm_le_nuclearNorm _ _)

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
