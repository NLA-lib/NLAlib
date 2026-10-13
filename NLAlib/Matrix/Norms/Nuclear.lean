/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.TraceInequalities
public import NLAlib.Matrix.Norms.KyFanNorm

/-!
# The nuclear norm

The nuclear norm `NLAlib.nuclearNorm A` is the sum of the singular values of `A`, the Ky Fan
`k`-norm (`NLAlib.Matrix.Norms.KyFanNorm`) for every `k` at least the rank. This file gives its
norm properties, its invariance, the comparisons with the spectral and Frobenius norms, the
factorisation bound, and the duality between the nuclear and the spectral norm under the Frobenius
inner product.

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
  obtain ⟨e, he⟩ := hA.exists_equiv_abs_eigenvalue_eq_singularValues
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
