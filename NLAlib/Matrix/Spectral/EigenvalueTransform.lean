/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Spectral.Eigenvalues

/-!
# Eigenvalues: sums, products and transformations

How the eigenvalue sequence `NLAlib.eigenvalue` of a Hermitian matrix determines its trace,
determinant, Frobenius norm and rank, and how it behaves under negation, scaling, shifts, unitary
similarity and relabelling. Positive semidefiniteness and definiteness in terms of eigenvalues.

## Main results

* `Matrix.IsHermitian.trace_eq_sum_range_eigenvalue`,
  `Matrix.IsHermitian.det_eq_prod_range_eigenvalue`,
  `Matrix.IsHermitian.frobNorm_sq_eq_sum_eigenvalue_sq`,
  `Matrix.IsHermitian.rank_eq_card_eigenvalue_ne_zero`.
* `Matrix.IsHermitian.eigenvalue_neg`, `Matrix.IsHermitian.eigenvalue_real_smul`,
  `Matrix.IsHermitian.eigenvalue_add_smul_one`.
* `NLAlib.eigenvalue_conjTranspose_mul_mul_of_card_eq`: invariance under unitary similarity.
* `Matrix.IsHermitian.posSemidef_iff_eigenvalue_nonneg`,
  `Matrix.PosSemidef.eigenvalue_antitone`.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n] [Fintype p]

/-! ### Transport from Mathlib's unsorted eigenvalues -/

/-- A product over Mathlib's unsorted eigenvalues is the product over the sorted sequence. -/
@[to_additive /-- A sum over Mathlib's unsorted eigenvalues is the sum over the sorted
sequence. -/]
private theorem prod_eigenvalues_eq_prod_range [DecidableEq n] {M : Type*} [CommMonoid M]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (g : ℝ → M) :
    ∏ i, g (hA.eigenvalues i) = ∏ k ∈ Finset.range (Fintype.card n), g (eigenvalue A k) := by
  obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
  rw [← Fin.prod_univ_eq_prod_range (fun k => g (eigenvalue A k)), ← e.prod_comp]
  exact Finset.prod_congr rfl fun i _ => by rw [he]

/-- A property of all of Mathlib's unsorted eigenvalues is a property of the sorted sequence on
the valid range. -/
private theorem forall_eigenvalues_iff [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (P : ℝ → Prop) : (∀ i, P (hA.eigenvalues i)) ↔ ∀ k < Fintype.card n, P (eigenvalue A k) := by
  obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
  constructor
  · intro h k hk
    have := h (e.symm ⟨k, hk⟩)
    rwa [he, Equiv.apply_symm_apply] at this
  · intro h i
    rw [he]
    exact h _ (e i).isLt

/-- The eigenvalue sequence restricted to the valid range is non-increasing. -/
private theorem antitone_eigenvalue_coe {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Antitone fun i : Fin (Fintype.card n) => eigenvalue A i :=
  fun _ b hab => hA.eigenvalue_le_eigenvalue hab b.isLt

/-! ### Trace, determinant, Frobenius norm, rank -/

/-- The trace of a Hermitian matrix is the sum of its eigenvalues. Mathlib's
`Matrix.IsHermitian.trace_eq_sum_eigenvalues` is the same fact for the unsorted `hA.eigenvalues`.
[HornJohnson2013, Theorem 1.2.16]. -/
theorem _root_.Matrix.IsHermitian.trace_eq_sum_range_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    A.trace = ((∑ k ∈ Finset.range (Fintype.card n), eigenvalue A k : ℝ) : 𝕜) := by
  classical
  rw [hA.trace_eq_sum_eigenvalues, sum_eigenvalues_eq_sum_range hA fun x => (x : 𝕜),
    RCLike.ofReal_sum]

/-- The real part of the trace of a Hermitian matrix is the sum of its eigenvalues. -/
theorem _root_.Matrix.IsHermitian.re_trace_eq_sum_range_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    RCLike.re A.trace = ∑ k ∈ Finset.range (Fintype.card n), eigenvalue A k := by
  rw [hA.trace_eq_sum_range_eigenvalue, RCLike.ofReal_re]

/-- The determinant of a Hermitian matrix is the product of its eigenvalues. Mathlib's
`Matrix.IsHermitian.det_eq_prod_eigenvalues` is the same fact for the unsorted `hA.eigenvalues`.
[HornJohnson2013, Theorem 1.2.16]. -/
theorem _root_.Matrix.IsHermitian.det_eq_prod_range_eigenvalue [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    A.det = ((∏ k ∈ Finset.range (Fintype.card n), eigenvalue A k : ℝ) : 𝕜) := by
  rw [hA.det_eq_prod_eigenvalues, prod_eigenvalues_eq_prod_range hA fun x => (x : 𝕜),
    RCLike.ofReal_prod]

/-- The squared Frobenius norm of a Hermitian matrix is the sum of its squared eigenvalues.
Port of `NLAlib.frobSq_eq_sum_sq_eigenvalues`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.frobNorm_sq_eq_sum_eigenvalue_sq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    frobNorm A ^ 2 = ∑ k ∈ Finset.range (Fintype.card n), eigenvalue A k ^ 2 := by
  classical
  obtain ⟨U, hU, h⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hAA : Aᴴ * A = U * Matrix.diagonal (fun i : Fin (Fintype.card n) =>
      ((eigenvalue A i : ℝ) : 𝕜) * ((eigenvalue A i : ℝ) : 𝕜)) * Uᴴ := by
    rw [hA.eq]
    conv_lhs => rw [h]
    simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
    rw [← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  rw [frobNorm_sq_eq_re_trace, hAA, Matrix.trace_mul_cycle, hU.conjTranspose_mul_self,
    Matrix.one_mul, Matrix.trace_diagonal, ← Fin.sum_univ_eq_sum_range fun k => eigenvalue A k ^ 2]
  simp only [← RCLike.ofReal_mul, ← RCLike.ofReal_sum, RCLike.ofReal_re, sq]

/-- The rank of a Hermitian matrix is the number of its nonzero eigenvalues. -/
theorem _root_.Matrix.IsHermitian.rank_eq_card_eigenvalue_ne_zero {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    A.rank = ((Finset.range (Fintype.card n)).filter fun k => eigenvalue A k ≠ 0).card := by
  classical
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype, Finset.card_filter,
    Finset.card_filter, sum_eigenvalues_eq_sum_range hA fun x => if x ≠ 0 then 1 else 0]

/-! ### Special matrices -/

/-- The eigenvalues of the zero matrix are zero. -/
@[simp]
theorem eigenvalue_zero (k : ℕ) : eigenvalue (0 : Matrix n n 𝕜) k = 0 := by
  by_cases hk : k < Fintype.card n
  · obtain ⟨u, hu, h⟩ :=
      (Matrix.isHermitian_zero (n := n) (α := 𝕜)).exists_norm_eq_one_and_mulVec_eq hk
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    rw [Matrix.zero_mulVec] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hu0
  · exact eigenvalue_of_card_le _ (not_lt.mp hk)

/-- The eigenvalues of the identity are one on the valid range. -/
theorem eigenvalue_one [DecidableEq n] {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue (1 : Matrix n n 𝕜) k = 1 := by
  obtain ⟨u, hu, h⟩ :=
    (Matrix.isHermitian_one (n := n) (α := 𝕜)).exists_norm_eq_one_and_mulVec_eq hk
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  rw [Matrix.one_mulVec] at h
  have h1 : (1 - eigenvalue (1 : Matrix n n 𝕜) k) • u = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hu0)).symm

/-- The eigenvalues of a real diagonal matrix with non-increasing diagonal are the diagonal
entries. -/
theorem eigenvalue_diagonal {q : ℕ} {d : Fin q → ℝ} (hd : Antitone d) (i : Fin q) :
    eigenvalue (Matrix.diagonal fun j => ((d j : ℝ) : 𝕜)) i = d i := by
  refine eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose
    (U := (1 : Matrix (Fin q) (Fin q) 𝕜)) hasOrthonormalCols_one (Fintype.card_fin q) hd ?_ i
  rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

/-! ### Transformations -/

/-- Negation reverses and negates the eigenvalues. The index reversal is written with an
equation, `k + j + 1 = Fintype.card n`, so that no subtraction appears.
Port of `NLAlib.eigenvalues₀_neg`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_neg {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k j : ℕ} (h : k + j + 1 = Fintype.card n) : eigenvalue (-A) k = -eigenvalue A j := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hμ : Antitone fun i : Fin (Fintype.card n) => -eigenvalue A (Fin.rev i) := fun a b hab =>
    neg_le_neg (hA.eigenvalue_le_eigenvalue (Fin.rev_le_rev.mpr hab) (Fin.rev a).isLt)
  have hU' : HasOrthonormalCols (U.submatrix id Fin.revPerm) :=
    hU.submatrix (Equiv.refl n) Fin.revPerm.injective
  have hd : (Matrix.diagonal fun i : Fin (Fintype.card n) =>
        ((-eigenvalue A (Fin.rev i) : ℝ) : 𝕜)) =
      (-Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)).submatrix
        Fin.revPerm Fin.revPerm := by
    rw [Matrix.diagonal_neg, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    rw [Function.comp_apply, Fin.revPerm_apply, RCLike.ofReal_neg]
  have hA' : -A = U.submatrix id Fin.revPerm *
      (Matrix.diagonal fun i : Fin (Fintype.card n) => ((-eigenvalue A (Fin.rev i) : ℝ) : 𝕜)) *
        (U.submatrix id Fin.revPerm)ᴴ := by
    rw [hd, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_neg, Matrix.neg_mul, ← hAU]
  have hk : k < Fintype.card n := by omega
  have h1 := eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU' rfl hμ hA' ⟨k, hk⟩
  have h2 : ((Fin.rev ⟨k, hk⟩ : Fin (Fintype.card n)) : ℕ) = j := by
    rw [Fin.val_rev]
    change Fintype.card n - (k + 1) = j
    omega
  rw [h2] at h1
  exact h1

/-- Scaling by a nonnegative real scales the eigenvalues. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_real_smul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {c : ℝ} (hc : 0 ≤ c) (k : ℕ) : eigenvalue (c • A) k = c * eigenvalue A k := by
  classical
  by_cases hk : k < Fintype.card n
  · obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
    have hμ : Antitone fun i : Fin (Fintype.card n) => c * eigenvalue A i := fun a b hab =>
      mul_le_mul_of_nonneg_left (hA.eigenvalue_le_eigenvalue hab b.isLt) hc
    have hd : (Matrix.diagonal fun i : Fin (Fintype.card n) =>
          ((c * eigenvalue A i : ℝ) : 𝕜)) =
        c • Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜) := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      rw [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul]
    refine eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU rfl hμ ?_ ⟨k, hk⟩
    rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← hAU]
  · rw [eigenvalue_of_card_le _ (not_lt.mp hk), eigenvalue_of_card_le _ (not_lt.mp hk), mul_zero]

/-- Adding a real multiple of the identity shifts the eigenvalues, on the valid range. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_add_smul_one [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (c : ℝ) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue (A + c • (1 : Matrix n n 𝕜)) k = eigenvalue A k + c := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hμ : Antitone fun i : Fin (Fintype.card n) => eigenvalue A i + c := fun a b hab =>
    add_le_add_left (hA.eigenvalue_le_eigenvalue hab b.isLt) c
  have hd : (Matrix.diagonal fun i : Fin (Fintype.card n) =>
        ((eigenvalue A i + c : ℝ) : 𝕜)) =
      (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) +
        c • (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    congr 1
    funext i
    rw [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, mul_one, RCLike.ofReal_add]
  refine eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU rfl hμ ?_ ⟨k, hk⟩
  rw [hd, Matrix.mul_add, Matrix.add_mul, ← hAU, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm]

/-- **Invariance under unitary similarity.** If `U` has orthonormal columns and as many columns
as rows, `Uᴴ * A * U` has the eigenvalues of `A`. No hypothesis on `A` is needed: both sides are
zero when `A` is not Hermitian. -/
theorem eigenvalue_conjTranspose_mul_mul_of_card_eq [DecidableEq p] (A : Matrix n n 𝕜)
    {U : Matrix n p 𝕜} (hU : HasOrthonormalCols U) (h : Fintype.card n = Fintype.card p) (k : ℕ) :
    eigenvalue (Uᴴ * A * U) k = eigenvalue A k := by
  classical
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq h
  by_cases hA : A.IsHermitian
  · by_cases hk : k < Fintype.card n
    · obtain ⟨V, hV, hAV⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
      refine eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose
        ((hU.conjTranspose_of_card_eq h).mul hV) h.symm (antitone_eigenvalue_coe hA) ?_ ⟨k, hk⟩
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      conv_lhs => rw [hAV]
      simp only [Matrix.mul_assoc]
    · rw [eigenvalue_of_card_le _ (not_lt.mp hk), eigenvalue_of_card_le _ (h ▸ not_lt.mp hk)]
  · rw [eigenvalue_of_not_isHermitian hA, eigenvalue_of_not_isHermitian]
    intro hB
    apply hA
    have hAB : A = U * (Uᴴ * A * U) * Uᴴ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU,
        Matrix.one_mul]
    rw [hAB]
    exact Matrix.isHermitian_mul_mul_conjTranspose U hB

/-- The eigenvalues are invariant under relabelling the index type. -/
@[simp]
theorem eigenvalue_submatrix_equiv (A : Matrix n n 𝕜) (e : p ≃ n) (k : ℕ) :
    eigenvalue (A.submatrix e e) k = eigenvalue A k := by
  classical
  have hU : HasOrthonormalCols ((1 : Matrix n n 𝕜).submatrix (Equiv.refl n) e) :=
    hasOrthonormalCols_one.submatrix (Equiv.refl n) e.injective
  have hE : ((1 : Matrix n n 𝕜).submatrix (Equiv.refl n) e)ᴴ * A *
      (1 : Matrix n n 𝕜).submatrix (Equiv.refl n) e = A.submatrix e e := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one, Matrix.one_submatrix_mul,
      Matrix.mul_submatrix_one, Matrix.submatrix_submatrix]
    rfl
  rw [← hE]
  exact eigenvalue_conjTranspose_mul_mul_of_card_eq A hU (Fintype.card_congr e).symm k

/-! ### Positive semidefinite and positive definite matrices -/

/-- The eigenvalues of a positive semidefinite matrix are nonnegative. -/
theorem _root_.Matrix.PosSemidef.eigenvalue_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (k : ℕ) : 0 ≤ eigenvalue A k := by
  classical
  by_cases hk : k < Fintype.card n
  · exact (forall_eigenvalues_iff hA.isHermitian (0 ≤ ·)).mp hA.eigenvalues_nonneg k hk
  · rw [eigenvalue_of_card_le _ (not_lt.mp hk)]

/-- The eigenvalue sequence of a positive semidefinite matrix is non-increasing on all of `ℕ`:
the zero padding is at the bottom. -/
theorem _root_.Matrix.PosSemidef.eigenvalue_antitone {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    Antitone (eigenvalue A) := by
  intro i j hij
  by_cases hj : j < Fintype.card n
  · exact hA.isHermitian.eigenvalue_le_eigenvalue hij hj
  · rw [eigenvalue_of_card_le _ (not_lt.mp hj)]
    exact hA.eigenvalue_nonneg i

/-- A Hermitian matrix is positive semidefinite exactly when its eigenvalues are nonnegative.
[HornJohnson2013, Theorem 4.1.8]. -/
theorem _root_.Matrix.IsHermitian.posSemidef_iff_eigenvalue_nonneg {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosSemidef ↔ ∀ k, 0 ≤ eigenvalue A k := by
  classical
  refine ⟨fun h => h.eigenvalue_nonneg, fun h => ?_⟩
  rw [hA.posSemidef_iff_eigenvalues_nonneg]
  exact (forall_eigenvalues_iff hA (0 ≤ ·)).mpr fun k _ => h k

/-- A Hermitian matrix is positive definite exactly when its eigenvalues on the valid range are
positive. [HornJohnson2013, Theorem 4.1.8]. -/
theorem _root_.Matrix.IsHermitian.posDef_iff_eigenvalue_pos {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosDef ↔ ∀ k < Fintype.card n, 0 < eigenvalue A k := by
  classical
  rw [hA.posDef_iff_eigenvalues_pos, forall_eigenvalues_iff hA (0 < ·)]

end NLAlib
