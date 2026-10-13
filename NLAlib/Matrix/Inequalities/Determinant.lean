/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Matrix.Basic.SchurComplement

/-!
# Determinant inequalities for positive semidefinite matrices

Hadamard's inequality (in its positive semidefinite form and in its column-norm form), Fischer's
inequality for a block matrix, the Hadamard–Fischer (Koteljanskii) inequality for principal
minors on overlapping index sets, and Minkowski's inequality: `A ↦ (det A)^(1/n)` is concave on
positive definite matrices. Determinants of Hermitian matrices are real; the inequalities are
stated for `RCLike.re (det A)`.

## Main results

* `Matrix.PosSemidef.re_det_le_prod_re_diag`, `NLAlib.norm_det_le_prod_norm_col`: Hadamard.
* `NLAlib.re_det_fromBlocks_le_of_posSemidef`: Fischer.
* `NLAlib.principalMinor`, `NLAlib.sum_principalMinor`: principal minors.
* `Matrix.PosSemidef.re_principalMinor_union_mul_inter_le`: Hadamard–Fischer (Koteljanskii).
* `Matrix.PosDef.re_det_rpow_add_le`, `NLAlib.concaveOn_re_det_rpow`: Minkowski.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Fischer's inequality -/

/-- The real part of a product of determinants whose first factor is the determinant of a
Hermitian matrix. -/
private theorem re_det_mul {A : Matrix m m 𝕜} (hA : A.IsHermitian) (z : 𝕜) :
    RCLike.re (A.det * z) = RCLike.re A.det * RCLike.re z := by
  conv_lhs => rw [hA.det_eq_re_det, RCLike.re_ofReal_mul]

/-- **Fischer's inequality.** The determinant of a positive semidefinite block matrix is at most
the product of the determinants of its diagonal blocks.
[HornJohnson2013, Theorem 7.8.5].
Port of `NLAlib.det_fromBlocks_le_mul_det_of_posSemidef`, there over `ℝ`.
Result: fischer-inequality -/
theorem re_det_fromBlocks_le_of_posSemidef {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    RCLike.re (Matrix.fromBlocks A B Bᴴ C).det ≤ RCLike.re A.det * RCLike.re C.det := by
  have hA : A.PosSemidef := h.submatrix Sum.inl
  have hC : C.PosSemidef := h.submatrix Sum.inr
  by_cases hdet : A.det = 0
  · have h0 : (Matrix.fromBlocks A B Bᴴ C).det = 0 := by
      by_contra hne
      have hPD : (Matrix.fromBlocks A B Bᴴ C).PosDef :=
        h.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ hne))
      have hAPD : A.PosDef := hPD.submatrix Sum.inl_injective
      exact hAPD.det_pos.ne' hdet
    rw [h0, hdet, map_zero, zero_mul]
  · have hAPD : A.PosDef :=
      hA.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ hdet))
    let : Invertible A := hAPD.isUnit.invertible
    have hS : (C - Bᴴ * A⁻¹ * B).PosSemidef := (Matrix.PosDef.fromBlocks₁₁ B C hAPD).mp h
    have hle : C - Bᴴ * A⁻¹ * B ≤ C := sub_conjTranspose_mul_mul_le hAPD.inv.posSemidef B C
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, re_det_mul hA.isHermitian]
    exact mul_le_mul_of_nonneg_left (hS.re_det_le_re_det_of_le hle)
      (RCLike.nonneg_iff.mp hA.det_nonneg).1

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- A congruence of a positive definite matrix vanishes only for the zero matrix. -/
private theorem eq_zero_of_conjTranspose_mul_mul_eq_zero [Finite n] {A : Matrix m m 𝕜}
    (hA : A.PosDef) {B : Matrix m n 𝕜} (h : Bᴴ * A * B = 0) : B = 0 := by
  classical
  have := Fintype.ofFinite n
  ext i j
  have hq : quadForm A (B *ᵥ Pi.single j 1) = 0 := by
    rw [← quadForm_conjTranspose_mul_mul, h, quadForm_zero_left]
  have hz : B *ᵥ Pi.single j 1 = 0 := by
    by_contra hne
    exact (hA.quadForm_pos hne).ne' hq
  simpa using congrFun hz i

/-- Equality in Fischer's inequality for a positive definite block matrix holds exactly when the
off-diagonal block vanishes.
Port of `NLAlib.det_fromBlocks_eq_mul_det_iff_of_posDef`, there over `ℝ`. -/
theorem re_det_fromBlocks_eq_iff_of_posDef {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosDef) :
    RCLike.re (Matrix.fromBlocks A B Bᴴ C).det = RCLike.re A.det * RCLike.re C.det ↔ B = 0 := by
  have hA : A.PosDef := h.submatrix Sum.inl_injective
  have hC : C.PosDef := h.submatrix Sum.inr_injective
  let : Invertible A := hA.isUnit.invertible
  have hS : (C - Bᴴ * A⁻¹ * B).PosDef := (posDef_fromBlocks_iff.mp h).2
  have hle : C - Bᴴ * A⁻¹ * B ≤ C := sub_conjTranspose_mul_mul_le hA.inv.posSemidef B C
  constructor
  · intro heq
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, re_det_mul hA.isHermitian] at heq
    have h1 : RCLike.re (C - Bᴴ * A⁻¹ * B).det = RCLike.re C.det :=
      mul_left_cancel₀ (RCLike.pos_iff.mp hA.det_pos).1.ne' heq
    have h2 : (C - Bᴴ * A⁻¹ * B).det = C.det := by
      rw [hS.isHermitian.det_eq_re_det, hC.isHermitian.det_eq_re_det, h1]
    have h3 := hC.eq_of_le_of_det_eq hS.posSemidef hle h2
    exact eq_zero_of_conjTranspose_mul_mul_eq_zero hA.inv (sub_eq_self.mp h3)
  · rintro rfl
    rw [Matrix.conjTranspose_zero, Matrix.det_fromBlocks_zero₂₁, re_det_mul hA.isHermitian]

/-- Fischer's inequality for a positive semidefinite matrix indexed by a sum type. -/
private theorem re_det_le_re_det_inl_mul_re_det_inr {M : Matrix (m ⊕ n) (m ⊕ n) 𝕜}
    (hM : M.PosSemidef) :
    RCLike.re M.det ≤ RCLike.re (M.submatrix Sum.inl Sum.inl).det *
      RCLike.re (M.submatrix Sum.inr Sum.inr).det := by
  have hM' : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    ext (i | i) (j | j) <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, hM.isHermitian.apply]
  have h := re_det_fromBlocks_le_of_posSemidef (A := M.toBlocks₁₁) (B := M.toBlocks₁₂)
    (C := M.toBlocks₂₂) (by rwa [← hM'])
  rwa [← hM'] at h

/-- Equality in Fischer's inequality for a positive definite matrix indexed by a sum type. -/
private theorem re_det_eq_re_det_inl_mul_re_det_inr_iff {M : Matrix (m ⊕ n) (m ⊕ n) 𝕜}
    (hM : M.PosDef) :
    RCLike.re M.det = RCLike.re (M.submatrix Sum.inl Sum.inl).det *
      RCLike.re (M.submatrix Sum.inr Sum.inr).det ↔ ∀ i j, M (Sum.inl i) (Sum.inr j) = 0 := by
  have hM' : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    ext (i | i) (j | j) <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, hM.isHermitian.apply]
  have h := re_det_fromBlocks_eq_iff_of_posDef (A := M.toBlocks₁₁) (B := M.toBlocks₁₂)
    (C := M.toBlocks₂₂) (by rwa [← hM'])
  rw [← hM'] at h
  exact h.trans ⟨fun h0 i j => congrFun (congrFun h0 i) j, fun h0 => Matrix.ext h0⟩

/-! ### Hadamard's inequality -/

omit [Fintype n] in
/-- The determinant of a submatrix along an injective map is the principal minor on its image. -/
private theorem det_submatrix_eq_det_submatrix_val {R ι : Type*} [CommRing R] [Fintype ι]
    [DecidableEq ι] (A : Matrix n n R) {f : ι → n} (hf : Function.Injective f) {s : Finset n}
    (hs : ∀ x, x ∈ s ↔ x ∈ Set.range f) :
    (A.submatrix f f).det = (A.submatrix (Subtype.val : s → n) Subtype.val).det := by
  let e : ι ≃ s := Equiv.ofBijective (fun i => ⟨f i, (hs _).mpr ⟨i, rfl⟩⟩)
    ⟨fun i j h => hf (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨i, rfl⟩ := (hs x).mp hx
      exact ⟨i, rfl⟩⟩
  rw [← Matrix.det_submatrix_equiv_self e (A.submatrix Subtype.val Subtype.val)]
  rfl

omit [Fintype n] [DecidableEq n] in
/-- Adjoining one index to a principal submatrix, as a map from a sum type. -/
private theorem injective_sumElim_val {s : Finset n} {a : n} (ha : a ∉ s) :
    Function.Injective (Sum.elim (Subtype.val : s → n) fun _ : Unit => a) :=
  Subtype.val_injective.sumElim (Function.injective_of_subsingleton _)
    fun i _ h => ha (h ▸ i.2)

omit [Fintype n] in
private theorem mem_insert_iff_mem_range_sumElim {s : Finset n} {a : n} (x : n) :
    x ∈ insert a s ↔ x ∈ Set.range (Sum.elim (Subtype.val : s → n) fun _ : Unit => a) := by
  simp [Set.Sum.elim_range, eq_comm]

omit [Fintype n] in
/-- Fischer's inequality for a principal submatrix with one index adjoined. -/
private theorem re_det_submatrix_sumElim_le {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (s : Finset n) (a : n) :
    RCLike.re (A.submatrix (Sum.elim (Subtype.val : s → n) fun _ : Unit => a)
      (Sum.elim (Subtype.val : s → n) fun _ : Unit => a)).det ≤
      RCLike.re (A.submatrix (Subtype.val : s → n) Subtype.val).det * RCLike.re (A a a) := by
  have h := re_det_le_re_det_inl_mul_re_det_inr
    (hA.submatrix (Sum.elim (Subtype.val : s → n) fun _ : Unit => a))
  rw [Matrix.det_unique (Matrix.submatrix _ Sum.inr Sum.inr)] at h
  exact h

omit [Fintype n] in
/-- Equality in Fischer's inequality for a principal submatrix with one index adjoined. -/
private theorem re_det_submatrix_sumElim_eq_iff {A : Matrix n n 𝕜} (hA : A.PosDef)
    {s : Finset n} {a : n} (ha : a ∉ s) :
    RCLike.re (A.submatrix (Sum.elim (Subtype.val : s → n) fun _ : Unit => a)
      (Sum.elim (Subtype.val : s → n) fun _ : Unit => a)).det =
      RCLike.re (A.submatrix (Subtype.val : s → n) Subtype.val).det * RCLike.re (A a a) ↔
      ∀ i ∈ s, A i a = 0 := by
  have h := re_det_eq_re_det_inl_mul_re_det_inr_iff (hA.submatrix (injective_sumElim_val ha))
  rw [Matrix.det_unique (Matrix.submatrix _ Sum.inr Sum.inr)] at h
  exact h.trans ⟨fun h0 i hi => h0 ⟨i, hi⟩ (), fun h0 i _ => h0 i i.2⟩

omit [Fintype n] in
/-- Hadamard's inequality for every principal submatrix. -/
private theorem re_det_submatrix_val_le_prod {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (s : Finset n) :
    RCLike.re (A.submatrix (Subtype.val : s → n) Subtype.val).det ≤
      ∏ i ∈ s, RCLike.re (A i i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← det_submatrix_eq_det_submatrix_val A (injective_sumElim_val ha)
      mem_insert_iff_mem_range_sumElim, mul_comm]
    exact (re_det_submatrix_sumElim_le hA s a).trans
      (mul_le_mul_of_nonneg_right ih (RCLike.nonneg_iff.mp hA.diag_nonneg).1)

omit [Fintype n] in
/-- Equality in Hadamard's inequality on a principal submatrix of a positive definite matrix
forces its off-diagonal entries to vanish. -/
private theorem apply_eq_zero_of_re_det_submatrix_val_eq_prod {A : Matrix n n 𝕜} (hA : A.PosDef)
    (s : Finset n)
    (h : RCLike.re (A.submatrix (Subtype.val : s → n) Subtype.val).det =
      ∏ i ∈ s, RCLike.re (A i i)) :
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j → A i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← det_submatrix_eq_det_submatrix_val A (injective_sumElim_val ha)
      mem_insert_iff_mem_range_sumElim, mul_comm] at h
    have h1 := re_det_submatrix_sumElim_le hA.posSemidef s a
    have h2 := re_det_submatrix_val_le_prod hA.posSemidef s
    have hq : 0 < RCLike.re (A a a) := (RCLike.pos_iff.mp hA.diag_pos).1
    have h3 : RCLike.re (A.submatrix (Subtype.val : s → n) Subtype.val).det =
        ∏ i ∈ s, RCLike.re (A i i) :=
      le_antisymm h2 (le_of_mul_le_mul_right (h ▸ h1) hq)
    have h5 := (re_det_submatrix_sumElim_eq_iff hA ha).mp (by rw [h, h3])
    intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with rfl | hi' <;>
      rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact absurd rfl hij
    · rw [← hA.isHermitian.apply, h5 j hj', star_zero]
    · exact h5 i hi'
    · exact ih h3 i hi' j hj' hij

/-- **Hadamard's inequality.** The determinant of a positive semidefinite matrix is at most the
product of its diagonal entries.
[HornJohnson2013, Theorem 7.8.1]. Port of `NLAlib.det_le_prod_diag_of_posSemidef`, there over
`ℝ`.
Result: hadamard-determinant-inequality -/
theorem _root_.Matrix.PosSemidef.re_det_le_prod_re_diag {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    RCLike.re A.det ≤ ∏ i, RCLike.re (A i i) := by
  have h := re_det_submatrix_val_le_prod hA Finset.univ
  rwa [← det_submatrix_eq_det_submatrix_val A Function.injective_id (by simp),
    Matrix.submatrix_id_id] at h

/-- Equality in Hadamard's inequality for a positive definite matrix holds exactly for diagonal
matrices. [HornJohnson2013, Theorem 7.8.1].
Port of `NLAlib.det_eq_prod_diag_iff_isDiag_of_posDef`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.re_det_eq_prod_re_diag_iff {A : Matrix n n 𝕜} (hA : A.PosDef) :
    RCLike.re A.det = ∏ i, RCLike.re (A i i) ↔ A.IsDiag := by
  constructor
  · intro h
    rw [← Matrix.submatrix_id_id A,
      det_submatrix_eq_det_submatrix_val A Function.injective_id (s := Finset.univ) (by simp)]
      at h
    exact fun i j hij => apply_eq_zero_of_re_det_submatrix_val_eq_prod hA Finset.univ h i
      (Finset.mem_univ i) j (Finset.mem_univ j) hij
  · intro h
    have hd : A.det = ∏ i, ((RCLike.re (A i i) : ℝ) : 𝕜) := by
      conv_lhs => rw [← h.diagonal_diag, Matrix.det_diagonal]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact (hA.isHermitian.coe_re_apply_self i).symm
    rw [hd, ← RCLike.ofReal_prod, RCLike.ofReal_re]

/-- **Hadamard's inequality, column form.** The modulus of the determinant of a square matrix is
at most the product of the Euclidean norms of its columns.
[HornJohnson2013, Corollary 7.8.3]. Port of `NLAlib.abs_det_le_prod_column_norm`, there over `ℝ`.
Result: hadamard-determinant-inequality -/
theorem norm_det_le_prod_norm_col (B : Matrix n n 𝕜) :
    ‖B.det‖ ≤ ∏ i, ‖WithLp.toLp 2 (B.col i)‖ := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self B).re_det_le_prod_re_diag
  have hdet : RCLike.re (Bᴴ * B).det = ‖B.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, RCLike.star_def, RCLike.conj_mul,
      ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hdiag : ∀ i, RCLike.re ((Bᴴ * B) i i) = ‖WithLp.toLp 2 (B.col i)‖ ^ 2 := by
    intro i
    rw [EuclideanSpace.norm_sq_eq, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
    rfl
  rw [hdet, Finset.prod_congr rfl fun i _ => hdiag i, Finset.prod_pow] at h
  exact le_of_sq_le_sq h (Finset.prod_nonneg fun i _ => norm_nonneg _)

/-! ### Principal minors and the Hadamard–Fischer inequality -/

/-- The **principal minor** of a square matrix on an index set: the determinant of the principal
submatrix with rows and columns in `s`. The minor on the empty set is `1`.
[HornJohnson2013, §0.7.1]. Port of `NLAlib.principalMinor`, there for real matrices. -/
def principalMinor {R : Type*} [CommRing R] (A : Matrix n n R) (s : Finset n) : R :=
  (A.submatrix (Subtype.val : ↥s → n) Subtype.val).det

omit [Fintype n] in
/-- The principal minor on the empty set is one. -/
@[simp]
theorem principalMinor_empty {R : Type*} [CommRing R] (A : Matrix n n R) :
    principalMinor A ∅ = 1 :=
  Matrix.det_isEmpty

omit [Fintype n] in
/-- The principal minor on a single index is the diagonal entry. -/
@[simp]
theorem principalMinor_singleton {R : Type*} [CommRing R] (A : Matrix n n R) (i : n) :
    principalMinor A {i} = A i i :=
  Matrix.det_eq_elem_of_subsingleton _ (⟨i, Finset.mem_singleton_self i⟩ : ↥({i} : Finset n))

/-- The principal minor on all indices is the determinant. -/
@[simp]
theorem principalMinor_univ {R : Type*} [CommRing R] (A : Matrix n n R) :
    principalMinor A Finset.univ = A.det := by
  rw [principalMinor,
    ← det_submatrix_eq_det_submatrix_val A Function.injective_id (s := Finset.univ) (by simp),
    Matrix.submatrix_id_id]

/-- **The sum of all principal minors is `det (1 + A)`.** This is the normalising constant of a
determinantal point process with kernel `A`. [HornJohnson2013, §1.2 context]. -/
theorem sum_principalMinor {R : Type*} [CommRing R] (A : Matrix n n R) :
    ∑ s : Finset n, principalMinor A s = (1 + A).det := by
  have h := (Matrix.detRowAlternating (R := R) (n := n)).map_add_univ A (1 : Matrix n n R)
  rw [add_comm]
  refine Eq.trans ?_ h.symm
  exact Finset.sum_congr rfl fun s _ => (Matrix.det_piecewise_one_eq_submatrix_det A s).symm

omit [Fintype n] in
/-- The principal minors of a positive semidefinite matrix are nonnegative.
Port of `NLAlib.principalMinor_nonneg`. -/
theorem _root_.Matrix.PosSemidef.re_principalMinor_nonneg {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (s : Finset n) : 0 ≤ RCLike.re (principalMinor A s) :=
  (RCLike.nonneg_iff.mp (hA.submatrix (Subtype.val : s → n)).det_nonneg).1

omit [Fintype n] in
/-- The principal minors of a positive definite matrix are positive.
Port of `NLAlib.principalMinor_pos`. -/
theorem _root_.Matrix.PosDef.re_principalMinor_pos {A : Matrix n n 𝕜} (hA : A.PosDef)
    (s : Finset n) : 0 < RCLike.re (principalMinor A s) :=
  (RCLike.pos_iff.mp (hA.submatrix (Subtype.val_injective (p := (· ∈ s)))).det_pos).1

/-- The determinant of a principal submatrix that contains the leading block, through the Schur
complement of that block. -/
private theorem det_submatrix_sumMap_id {ι κ κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ']
    [DecidableEq κ'] (H : Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜) (hP : IsUnit H.toBlocks₁₁) (g : κ' → κ) :
    (H.submatrix (Sum.map id g) (Sum.map id g)).det = H.toBlocks₁₁.det *
      ((H.toBlocks₂₂ - H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂).submatrix g g).det := by
  let : Invertible H.toBlocks₁₁ := hP.invertible
  have h : H.submatrix (Sum.map id g) (Sum.map id g) =
      Matrix.fromBlocks H.toBlocks₁₁ (H.toBlocks₁₂.submatrix id g) (H.toBlocks₂₁.submatrix g id)
        (H.toBlocks₂₂.submatrix g g) := by
    ext (i | i) (j | j) <;> rfl
  rw [h, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  rfl

/-- The Hadamard–Fischer inequality for a positive definite matrix in three blocks, the first
being the common one. -/
private theorem re_det_mul_re_det_inl_le_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix (ι ⊕ (m ⊕ n)) (ι ⊕ (m ⊕ n)) 𝕜} (hH : H.PosDef) :
    RCLike.re H.det * RCLike.re (H.submatrix Sum.inl Sum.inl).det ≤
      RCLike.re (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det *
        RCLike.re (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det := by
  have hP : H.toBlocks₁₁.PosDef := hH.submatrix Sum.inl_injective
  have h21 : H.toBlocks₂₁ = H.toBlocks₁₂ᴴ := by
    ext i j
    simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, hH.isHermitian.apply]
  have hH' : H = Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₁₂ᴴ H.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hS : (H.toBlocks₂₂ - H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂).PosDef := by
    rw [h21]
    exact (posDef_fromBlocks_iff.mp (hH' ▸ hH)).2
  have h0 := det_submatrix_sumMap_id H hP.isUnit id
  rw [Sum.map_id_id, Matrix.submatrix_id_id, Matrix.submatrix_id_id] at h0
  have hF := re_det_le_re_det_inl_mul_re_det_inr hS.posSemidef
  have hp : 0 ≤ RCLike.re H.toBlocks₁₁.det := (RCLike.pos_iff.mp hP.det_pos).1.le
  rw [det_submatrix_sumMap_id H hP.isUnit Sum.inl, det_submatrix_sumMap_id H hP.isUnit Sum.inr,
    h0, re_det_mul hP.isHermitian, re_det_mul hP.isHermitian, re_det_mul hP.isHermitian]
  change _ * RCLike.re H.toBlocks₁₁.det ≤ _
  calc RCLike.re H.toBlocks₁₁.det * _ * RCLike.re H.toBlocks₁₁.det
      ≤ RCLike.re H.toBlocks₁₁.det * (_ * _) * RCLike.re H.toBlocks₁₁.det :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hp) hp
    _ = _ := by ring

/-- The Hadamard–Fischer inequality for a positive semidefinite matrix in three blocks. -/
private theorem re_det_mul_re_det_inl_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix (ι ⊕ (m ⊕ n)) (ι ⊕ (m ⊕ n)) 𝕜} (hH : H.PosSemidef) :
    RCLike.re H.det * RCLike.re (H.submatrix Sum.inl Sum.inl).det ≤
      RCLike.re (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det *
        RCLike.re (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det :=
  Matrix.PosSemidef.le_of_forall_posDef_le
    (f := fun H : Matrix (ι ⊕ (m ⊕ n)) (ι ⊕ (m ⊕ n)) 𝕜 =>
      RCLike.re H.det * RCLike.re (H.submatrix Sum.inl Sum.inl).det)
    (g := fun H : Matrix (ι ⊕ (m ⊕ n)) (ι ⊕ (m ⊕ n)) 𝕜 =>
      RCLike.re (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det *
        RCLike.re (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det)
    (by fun_prop) (by fun_prop) (fun _ hM => re_det_mul_re_det_inl_le_of_posDef hM) hH

omit [Fintype n] in
/-- **The Hadamard–Fischer inequality** (Koteljanskii). For a positive semidefinite matrix and
index sets `s`, `t`, `A[s ∪ t] · A[s ∩ t] ≤ A[s] · A[t]` for the principal minors.
[HornJohnson2013, Theorem 7.8.9].
Port of `NLAlib.det_principal_union_mul_inter_le_of_posSemidef`, there over `ℝ`.
Result: koteljanskii-inequality -/
theorem _root_.Matrix.PosSemidef.re_principalMinor_union_mul_inter_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (s t : Finset n) :
    RCLike.re (principalMinor A (s ∪ t)) * RCLike.re (principalMinor A (s ∩ t)) ≤
      RCLike.re (principalMinor A s) * RCLike.re (principalMinor A t) := by
  have hJ : Function.Injective
      (Sum.elim (Subtype.val : ↥(s ∩ t) → n) (Subtype.val : ↥(s \ t) → n)) :=
    Subtype.val_injective.sumElim Subtype.val_injective fun i j h =>
      (Finset.mem_sdiff.mp j.2).2 (h ▸ (Finset.mem_inter.mp i.2).2)
  have hK : Function.Injective
      (Sum.elim (Subtype.val : ↥(s ∩ t) → n) (Subtype.val : ↥(t \ s) → n)) :=
    Subtype.val_injective.sumElim Subtype.val_injective fun i j h =>
      (Finset.mem_sdiff.mp j.2).2 (h ▸ (Finset.mem_inter.mp i.2).1)
  have hJK : Function.Injective
      (Sum.elim (Subtype.val : ↥(s \ t) → n) (Subtype.val : ↥(t \ s) → n)) :=
    Subtype.val_injective.sumElim Subtype.val_injective fun i j h =>
      (Finset.mem_sdiff.mp j.2).2 (h ▸ (Finset.mem_sdiff.mp i.2).1)
  have hf : Function.Injective (Sum.elim (Subtype.val : ↥(s ∩ t) → n)
      (Sum.elim (Subtype.val : ↥(s \ t) → n) (Subtype.val : ↥(t \ s) → n))) :=
    Subtype.val_injective.sumElim hJK fun i j h => by
      rcases j with j | j
      · exact (Finset.mem_sdiff.mp j.2).2 ((show (i : n) = j from h) ▸ (Finset.mem_inter.mp i.2).2)
      · exact (Finset.mem_sdiff.mp j.2).2 ((show (i : n) = j from h) ▸ (Finset.mem_inter.mp i.2).1)
  have h := re_det_mul_re_det_inl_le (hA.submatrix (Sum.elim (Subtype.val : ↥(s ∩ t) → n)
    (Sum.elim (Subtype.val : ↥(s \ t) → n) (Subtype.val : ↥(t \ s) → n))))
  simp only [Matrix.submatrix_submatrix, Sum.elim_comp_map, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Function.comp_id] at h
  rw [det_submatrix_eq_det_submatrix_val A hf (s := s ∪ t)
    (by simp [Set.Sum.elim_range]; tauto)] at h
  have hs := det_submatrix_eq_det_submatrix_val A hJ (s := s) (by simp [Set.Sum.elim_range]; tauto)
  have ht := det_submatrix_eq_det_submatrix_val A hK (s := t) (by simp [Set.Sum.elim_range]; tauto)
  rw [principalMinor, principalMinor, principalMinor, principalMinor, ← hs, ← ht]
  exact h

/-! ### Minkowski's inequality -/

/-- Superadditivity of the geometric mean against the constant sequence `1`. -/
private theorem one_add_prod_rpow_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {μ : ι → ℝ}
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    1 + (∏ i ∈ s, μ i) ^ (s.card : ℝ)⁻¹ ≤ (∏ i ∈ s, (μ i + 1)) ^ (s.card : ℝ)⁻¹ := by
  have hw : 0 ≤ (s.card : ℝ)⁻¹ := by positivity
  have hsum : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs))]
  have hz : ∀ i ∈ s, 0 < μ i + 1 := fun i hi => by linarith [hμ i hi]
  have hz' : 0 ≤ ∏ i ∈ s, (μ i + 1) := Finset.prod_nonneg fun i hi => (hz i hi).le
  have h1 := Real.geom_mean_le_arith_mean_weighted s (fun _ => (s.card : ℝ)⁻¹)
    (fun i => (μ i + 1)⁻¹) (fun _ _ => hw) hsum fun i hi => (inv_pos.mpr (hz i hi)).le
  have h2 := Real.geom_mean_le_arith_mean_weighted s (fun _ => (s.card : ℝ)⁻¹)
    (fun i => μ i / (μ i + 1)) (fun _ _ => hw) hsum fun i hi => div_nonneg (hμ i hi) (hz i hi).le
  have h3 : ∑ i ∈ s, (s.card : ℝ)⁻¹ * (μ i + 1)⁻¹ + ∑ i ∈ s, (s.card : ℝ)⁻¹ * (μ i / (μ i + 1)) =
      1 := by
    rw [← Finset.sum_add_distrib]
    refine Eq.trans (Finset.sum_congr rfl fun i hi => ?_) hsum
    rw [← mul_add, inv_eq_one_div (μ i + 1), ← add_div, add_comm 1, div_self (hz i hi).ne',
      mul_one]
  have hG : 0 < (∏ i ∈ s, (μ i + 1)) ^ (s.card : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (Finset.prod_pos hz) _
  rw [Real.finsetProd_rpow _ _ fun i hi => (inv_pos.mpr (hz i hi)).le, Finset.prod_inv_distrib,
    Real.inv_rpow hz'] at h1
  rw [Real.finsetProd_rpow _ _ fun i hi => div_nonneg (hμ i hi) (hz i hi).le,
    Finset.prod_div_distrib, Real.div_rpow (Finset.prod_nonneg hμ) hz'] at h2
  have h4 := mul_le_mul_of_nonneg_right (h3 ▸ add_le_add h1 h2) hG.le
  rwa [add_mul, inv_mul_cancel₀ hG.ne', div_mul_cancel₀ _ hG.ne', one_mul] at h4

/-- Minkowski's inequality against the identity. -/
private theorem one_add_re_det_rpow_le [Nonempty n] {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    1 + RCLike.re M.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (M + (1 : ℝ) • (1 : Matrix n n 𝕜)).det ^ (Fintype.card n : ℝ)⁻¹ := by
  have h := one_add_prod_rpow_le (s := Finset.range (Fintype.card n))
    (Finset.nonempty_range_iff.mpr Fintype.card_ne_zero) (μ := eigenvalue M)
    fun i _ => hM.eigenvalue_nonneg i
  rw [Finset.card_range] at h
  rw [hM.isHermitian.det_eq_prod_range_eigenvalue, RCLike.ofReal_re,
    (hM.isHermitian.add (isHermitian_real_smul_one 1)).det_eq_prod_range_eigenvalue,
    RCLike.ofReal_re,
    Finset.prod_congr rfl fun k hk =>
      hM.isHermitian.eigenvalue_add_smul_one 1 (Finset.mem_range.mp hk)]
  exact h

/-- A positive definite matrix is congruent to the identity. -/
private theorem exists_conjTranspose_mul_mul_eq_one {A : Matrix n n 𝕜} (hA : A.PosDef) :
    ∃ C : Matrix n n 𝕜, Cᴴ * A * C = 1 := by
  have hS : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSu : IsUnit (CFC.sqrt A) := by
    refine IsUnit.of_mul_eq_one (CFC.sqrt A * A⁻¹) ?_
    rw [← Matrix.mul_assoc, hSS,
      Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)]
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hSu
  refine ⟨(CFC.sqrt A)⁻¹, ?_⟩
  calc (CFC.sqrt A)⁻¹ᴴ * A * (CFC.sqrt A)⁻¹
      = (CFC.sqrt A)⁻¹ * (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A)⁻¹ := by rw [hS.inv.eq, hSS]
    _ = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
        Matrix.nonsing_inv_mul _ hdet]

/-- The determinant of a congruence. -/
private theorem re_det_conjTranspose_mul_mul (X C : Matrix n n 𝕜) :
    RCLike.re (Cᴴ * X * C).det = ‖C.det‖ ^ 2 * RCLike.re X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_right_comm, RCLike.star_def,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

/-- Minkowski's inequality when the first matrix is positive definite. -/
private theorem re_det_rpow_add_le_of_posDef [Nonempty n] {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosSemidef) :
    RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ + RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (A + B).det ^ (Fintype.card n : ℝ)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_conjTranspose_mul_mul_eq_one hA
  have h := one_add_re_det_rpow_le (hB.conjTranspose_mul_mul_same C)
  have hsum : Cᴴ * B * C + (1 : ℝ) • (1 : Matrix n n 𝕜) = Cᴴ * (A + B) * C := by
    rw [one_smul, ← hC, Matrix.mul_add, Matrix.add_mul, add_comm]
  have h1 : ‖C.det‖ ^ 2 * RCLike.re A.det = 1 := by
    rw [← re_det_conjTranspose_mul_mul, hC, Matrix.det_one, RCLike.one_re]
  have hc : 0 ≤ ‖C.det‖ ^ 2 := sq_nonneg _
  have hc' : 0 < (‖C.det‖ ^ 2) ^ (Fintype.card n : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (lt_of_le_of_ne hc fun h0 => by simp [← h0] at h1) _
  have ha : 0 ≤ RCLike.re A.det := (RCLike.nonneg_iff.mp hA.posSemidef.det_nonneg).1
  have hb : 0 ≤ RCLike.re B.det := (RCLike.nonneg_iff.mp hB.det_nonneg).1
  have hab : 0 ≤ RCLike.re (A + B).det :=
    (RCLike.nonneg_iff.mp (hA.posSemidef.add hB).det_nonneg).1
  rw [hsum, re_det_conjTranspose_mul_mul, re_det_conjTranspose_mul_mul, Real.mul_rpow hc hb,
    Real.mul_rpow hc hab] at h
  have h2 : (‖C.det‖ ^ 2) ^ (Fintype.card n : ℝ)⁻¹ * RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ =
      1 := by
    rw [← Real.mul_rpow hc ha, h1, Real.one_rpow]
  refine le_of_mul_le_mul_left ?_ hc'
  rw [mul_add, h2]
  exact h

/-- **Minkowski's determinant inequality.** For positive semidefinite `A`, `B` of size `N ≥ 1`,
`(det A)^(1/N) + (det B)^(1/N) ≤ (det (A + B))^(1/N)`.
[HornJohnson2013, Theorem 7.8.21].
Port of `NLAlib.det_rpow_inv_card_add_le`, there over `ℝ` for positive definite matrices.
Result: minkowski-determinant-inequality -/
theorem _root_.Matrix.PosSemidef.re_det_rpow_add_le [Nonempty n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ + RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (A + B).det ^ (Fintype.card n : ℝ)⁻¹ := by
  have hw : 0 ≤ (Fintype.card n : ℝ)⁻¹ := by positivity
  have hcont : Continuous fun X : Matrix n n 𝕜 => RCLike.re X.det ^ (Fintype.card n : ℝ)⁻¹ :=
    (Real.continuous_rpow_const hw).comp (RCLike.continuous_re.comp (continuous_id.matrix_det))
  exact Matrix.PosSemidef.le_of_forall_posDef_le
    (f := fun X : Matrix n n 𝕜 =>
      RCLike.re X.det ^ (Fintype.card n : ℝ)⁻¹ + RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹)
    (g := fun X : Matrix n n 𝕜 => RCLike.re (X + B).det ^ (Fintype.card n : ℝ)⁻¹)
    (hcont.add continuous_const) (hcont.comp (continuous_id.add continuous_const))
    (fun _ hM => re_det_rpow_add_le_of_posDef hM hB) hA

/-- The determinant root is positively homogeneous of degree one. -/
private theorem re_det_real_smul_rpow [Nonempty n] {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {a : ℝ} (ha : 0 ≤ a) :
    RCLike.re (a • A).det ^ (Fintype.card n : ℝ)⁻¹ =
      a * RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), Matrix.det_smul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul, Real.mul_rpow (pow_nonneg ha _) (RCLike.nonneg_iff.mp hA.det_nonneg).1,
    Real.pow_rpow_inv_natCast ha Fintype.card_ne_zero]

/-- `A ↦ (det A)^(1/N)` is concave on the positive definite matrices.
[HornJohnson2013, Theorem 7.8.21]. Port of `NLAlib.concaveOn_det_rpow_inv_card`. -/
theorem concaveOn_re_det_rpow [Nonempty n] :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      fun A => RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ := by
  refine ⟨fun A hA B hB a b ha hb hab => ?_, fun A hA B hB a b ha hb _ => ?_⟩
  · rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      simpa [hab] using hB
    · exact (Matrix.PosDef.smul hA ha').add_posSemidef (hB.posSemidef.smul hb)
  · have h := (hA.posSemidef.smul ha).re_det_rpow_add_le (hB.posSemidef.smul hb)
    rwa [re_det_real_smul_rpow hA.posSemidef ha, re_det_real_smul_rpow hB.posSemidef hb] at h

/-- The determinant is superadditive on positive semidefinite matrices of positive size:
`det A + det B ≤ det (A + B)`. [HornJohnson2013, §7.8]. -/
theorem _root_.Matrix.PosSemidef.re_det_add_le [Nonempty n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef)
    (hB : B.PosSemidef) : RCLike.re A.det + RCLike.re B.det ≤ RCLike.re (A + B).det := by
  have hN : Fintype.card n ≠ 0 := Fintype.card_ne_zero
  have ha : 0 ≤ RCLike.re A.det := (RCLike.nonneg_iff.mp hA.det_nonneg).1
  have hb : 0 ≤ RCLike.re B.det := (RCLike.nonneg_iff.mp hB.det_nonneg).1
  have hab : 0 ≤ RCLike.re (A + B).det := (RCLike.nonneg_iff.mp (hA.add hB).det_nonneg).1
  have h := pow_le_pow_left₀ (add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))
    (hA.re_det_rpow_add_le hB) (Fintype.card n)
  rw [Real.rpow_inv_natCast_pow hab hN] at h
  refine le_trans ?_ ((pow_add_pow_le (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _) hN).trans h)
  rw [Real.rpow_inv_natCast_pow ha hN, Real.rpow_inv_natCast_pow hb hN]

end NLAlib
