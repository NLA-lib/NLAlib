/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Matrix.Basic.SchurComplement

/-!
# Determinant inequalities for positive semidefinite matrices

Hadamard's inequality (in its positive semidefinite form and in its column-norm form), Fischer's
inequality for a block matrix, principal minors, and the Hadamard–Fischer (Koteljanskii)
inequality for principal minors on overlapping index sets. Determinants of Hermitian matrices are
real; the inequalities are stated for `RCLike.re (det A)`. Minkowski's inequality is in
`NLAlib.Matrix.Inequalities.Minkowski`.

## Main results

* `Matrix.IsHermitian.re_det_mul`, `NLAlib.det_eq_det_toBlocks₁₁_mul_det`: the determinant of a
  Hermitian matrix inside a real part, and the Schur determinant formula on a sum type.
* `Matrix.PosSemidef.re_det_le_prod_re_diag`, `NLAlib.norm_det_le_prod_norm_col`: Hadamard.
* `NLAlib.re_det_fromBlocks_le_of_posSemidef`: Fischer.
* `NLAlib.principalMinor`, `NLAlib.det_submatrix_eq_principalMinor`,
  `NLAlib.sum_principalMinor`: principal minors.
* `Matrix.PosSemidef.re_principalMinor_union_mul_inter_le`: Hadamard–Fischer (Koteljanskii).
* `Matrix.PosSemidef.re_principalMinor_union_le_of_disjoint`: Fischer for principal minors.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Fischer's inequality -/

/-- The determinant of a Hermitian matrix is real, so it comes out of a real part:
`re (det A · z) = re (det A) · re z`. -/
theorem _root_.Matrix.IsHermitian.re_det_mul {A : Matrix m m 𝕜} (hA : A.IsHermitian) (z : 𝕜) :
    RCLike.re (A.det * z) = RCLike.re A.det * RCLike.re z := by
  conv_lhs => rw [hA.det_eq_re_det, RCLike.re_ofReal_mul]

/-- **The Schur determinant formula** for a matrix indexed by a sum type whose leading block is
invertible: `det M = det M₁₁ · det (M₂₂ - M₂₁ M₁₁⁻¹ M₁₂)`. This is Mathlib's
`Matrix.det_fromBlocks₁₁` for a matrix that is not written as `Matrix.fromBlocks`, with `⁻¹` in
place of `⅟`. [HornJohnson2013, §0.8.5]. -/
theorem det_eq_det_toBlocks₁₁_mul_det {R : Type*} [CommRing R] (M : Matrix (m ⊕ n) (m ⊕ n) R)
    (h : IsUnit M.toBlocks₁₁) : M.det = M.toBlocks₁₁.det *
      (M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det := by
  let : Invertible M.toBlocks₁₁ := h.invertible
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]

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
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hA.isHermitian.re_det_mul]
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
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hA.isHermitian.re_det_mul] at heq
    have h1 : RCLike.re (C - Bᴴ * A⁻¹ * B).det = RCLike.re C.det :=
      mul_left_cancel₀ (RCLike.pos_iff.mp hA.det_pos).1.ne' heq
    have h2 : (C - Bᴴ * A⁻¹ * B).det = C.det := by
      rw [hS.isHermitian.det_eq_re_det, hC.isHermitian.det_eq_re_det, h1]
    have h3 := hC.eq_of_le_of_det_eq hS.posSemidef hle h2
    exact eq_zero_of_conjTranspose_mul_mul_eq_zero hA.inv (sub_eq_self.mp h3)
  · rintro rfl
    rw [Matrix.conjTranspose_zero, Matrix.det_fromBlocks_zero₂₁, hA.isHermitian.re_det_mul]

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

omit [Fintype n] in
/-- **A principal minor as the determinant of a submatrix along an injective map.** If `f` is
injective with image the index set `s`, the determinant of `A.submatrix f f` is the principal
minor of `A` on `s`: a principal minor does not depend on how its index set is enumerated. -/
theorem det_submatrix_eq_principalMinor {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix n n R) {f : ι → n} (hf : Function.Injective f) {s : Finset n}
    (hs : Set.range f = s) : (A.submatrix f f).det = principalMinor A s :=
  det_submatrix_eq_det_submatrix_val A hf fun x => by rw [← Finset.mem_coe, ← hs]

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
    h0, hP.isHermitian.re_det_mul, hP.isHermitian.re_det_mul, hP.isHermitian.re_det_mul]
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

omit [Fintype n] in
/-- **Fischer's inequality for principal minors.** For a positive semidefinite matrix and
disjoint index sets `s`, `t`, `A[s ∪ t] ≤ A[s] · A[t]`: the case `s ∩ t = ∅` of the
Hadamard–Fischer inequality. [HornJohnson2013, Theorem 7.8.5].
Result: fischer-inequality -/
theorem _root_.Matrix.PosSemidef.re_principalMinor_union_le_of_disjoint {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {s t : Finset n} (hst : Disjoint s t) :
    RCLike.re (principalMinor A (s ∪ t)) ≤
      RCLike.re (principalMinor A s) * RCLike.re (principalMinor A t) := by
  have h := hA.re_principalMinor_union_mul_inter_le s t
  rwa [Finset.disjoint_iff_inter_eq_empty.mp hst, principalMinor_empty, RCLike.one_re,
    mul_one] at h

end NLAlib
