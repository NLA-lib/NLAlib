/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
public import NLAlib.Matrix.Functions.Complexification

/-!
# Operator convex functions

Operator convexity of `f` on an interval is the predicate `NLAlib.OperatorConvexOn s f`. Operator
convex functions satisfy the operator Jensen inequality `f(Kᴴ A K) ≤ Kᴴ f(A) K` for an isometry
`K` (Hansen–Pedersen), proved by dilating the isometry to a unitary and pinching. `-log t` and
`t⁻¹` are operator convex by Mathlib's C⋆-algebra facts; `t log t` is `t f(1/t)` for `f = -log`.

## Main definitions

* `NLAlib.OperatorConvexOn`: operator convexity on a set, for Hermitian matrices of every size.

## Main results

* `NLAlib.operatorConvexOn_neg_log`, `NLAlib.operatorConvexOn_inv`, `NLAlib.operatorConvexOn_sq`,
  `NLAlib.operatorConvexOn_mul_log`.
* `NLAlib.OperatorConvexOn.cfc_conjTranspose_mul_mul_le`,
  `NLAlib.OperatorConvexOn.cfc_sum_conjTranspose_mul_mul_le`: the operator Jensen inequality.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- A function is **operator convex** on a convex set `s` of reals if
`f(a A + b B) ≤ a f(A) + b f(B)` for all weights `a + b = 1` and all Hermitian matrices `A`, `B`
of every size with spectrum in `s`. It is stated for complex matrices indexed by `Fin d`; the
consequences below hold over any `RCLike` field and any index type.
[Bhatia1997, §V.1]; [Tropp2015, Definition 8.4.1]. Port of `NLAlib.OperatorConvexOn`. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ), A.IsHermitian → B.IsHermitian →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      cfc f (a • A + b • B) ≤ a • cfc f A + b • cfc f B

/-- An operator convex function is convex. -/
theorem OperatorConvexOn.convexOn {s : Set ℝ} {f : ℝ → ℝ} (hf : OperatorConvexOn s f) :
    ConvexOn ℝ s f := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  let ι : ℝ →+* Matrix (Fin 1) (Fin 1) ℂ := algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℂ)
  have hι : ∀ z : ℝ, (ι z).IsHermitian := fun z => (IsSelfAdjoint.all z).algebraMap _
  have hs : ∀ z ∈ s, spectrum ℝ (ι z) ⊆ s := fun z hz => by
    rw [spectrum.scalar_eq]
    exact Set.singleton_subset_iff.mpr hz
  have h := hf.2 1 (ι x) (ι y) (hι x) (hι y) (hs x hx) (hs y hy) a b ha hb hab
  have hsum : ∀ u v : ℝ, a • ι u + b • ι v = ι (a * u + b * v) := fun u v => by
    rw [map_add, map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
  rw [hsum, cfc_algebraMap, cfc_algebraMap, cfc_algebraMap, hsum] at h
  exact algebraMap_le_algebraMap.mp h

/-- **Operator convexity for matrices over any field and index type.** -/
theorem OperatorConvexOn.cfc_smul_add_smul_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorConvexOn s f) {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAs : spectrum ℝ A ⊆ s) (hBs : spectrum ℝ B ⊆ s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : cfc f (a • A + b • B) ≤ a • cfc f A + b • cfc f B := by
  let e := (Fintype.equivFin n).symm
  let R : Matrix n n 𝕜 → Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ := fun M =>
    (complexify M).submatrix e e
  have hR : ∀ M : Matrix n n 𝕜, M.IsHermitian → (R M).IsHermitian := fun M hM =>
    (isHermitian_complexify_iff.mpr hM).submatrix e
  have hcfc : ∀ M : Matrix n n 𝕜, M.IsHermitian → cfc f (R M) = R (cfc f M) := fun M hM => by
    change cfc f ((complexify M).submatrix e e) = (complexify (cfc f M)).submatrix e e
    rw [cfc_submatrix_equiv (isHermitian_complexify_iff.mpr hM) f e, complexify_cfc hM]
  have hsp : ∀ M : Matrix n n 𝕜, spectrum ℝ (R M) = spectrum ℝ M := fun M => by
    rw [← spectrum_complexify M]
    exact AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℂ e.symm) (complexify M)
  have hadd : ∀ M N : Matrix n n 𝕜, a • R M + b • R N = R (a • M + b • N) := fun M N => by
    simp only [R, complexify_add, complexify_real_smul, Matrix.submatrix_add,
      Matrix.submatrix_smul, Pi.add_apply, Pi.smul_apply]
  have hAB : (a • A + b • B).IsHermitian :=
    (hA.smul (IsSelfAdjoint.all a)).add (hB.smul (IsSelfAdjoint.all b))
  have h := hf.2 _ (R A) (R B) (hR A hA) (hR B hB) (by rw [hsp]; exact hAs)
    (by rw [hsp]; exact hBs) a b ha hb hab
  have hle : ∀ M N : Matrix n n 𝕜, R M ≤ R N → M ≤ N := fun M N hMN => by
    rw [Matrix.le_iff] at hMN ⊢
    change ((complexify N - complexify M).submatrix e e).PosSemidef at hMN
    rwa [Matrix.posSemidef_submatrix_equiv, ← complexify_sub, posSemidef_complexify_iff] at hMN
  rw [hadd, hcfc _ hAB, hcfc _ hA, hcfc _ hB, hadd] at h
  exact hle _ _ h

/-- `t ↦ t²` is operator convex on `ℝ`. [Bhatia1997, Example V.1.3]. -/
theorem operatorConvexOn_sq : OperatorConvexOn Set.univ fun x : ℝ => x ^ 2 := by
  refine ⟨convex_univ, fun d A B hA hB _ _ a b ha hb hab => ?_⟩
  have hAB : (a • A + b • B).IsHermitian :=
    (hA.smul (IsSelfAdjoint.all a)).add (hB.smul (IsSelfAdjoint.all b))
  rw [cfc_pow_id A 2 hA.isSelfAdjoint, cfc_pow_id B 2 hB.isSelfAdjoint,
    cfc_pow_id _ 2 hAB.isSelfAdjoint, ← sub_nonneg]
  have hid : a • A ^ 2 + b • B ^ 2 - (a • A + b • B) ^ 2 = (a * b) • ((A - B)ᴴ * (A - B)) := by
    obtain rfl : b = 1 - a := by linarith
    rw [Matrix.conjTranspose_sub, hA.eq, hB.eq]
    simp only [pow_two, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      smul_smul, sub_smul, one_smul, smul_sub, smul_add]
    module
  rw [hid]
  exact smul_nonneg (mul_nonneg ha hb) (Matrix.posSemidef_conjTranspose_mul_self _).nonneg

/-- `t ↦ t⁻¹` is operator convex on `(0, ∞)`. [Bhatia1997, §V.1]. -/
theorem operatorConvexOn_inv : OperatorConvexOn (Set.Ioi 0) fun x : ℝ => x⁻¹ := by
  refine ⟨convex_Ioi 0, fun d A B hA hB hAs hBs a b ha hb hab => ?_⟩
  open scoped Matrix.Norms.L2Operator in
  have hAp : IsStrictlyPositive A :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr ⟨hA, hAs⟩
  open scoped Matrix.Norms.L2Operator in
  have hBp : IsStrictlyPositive B :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr ⟨hB, hBs⟩
  open scoped Matrix.Norms.L2Operator in
  have hc := CStarAlgebra.convexOn_ringInverse (A := Matrix (Fin d) (Fin d) ℂ)
  have hABp : IsStrictlyPositive (a • A + b • B) := hc.1 hAp hBp ha hb hab
  rw [cfc_ringInverse_id A hAp.isUnit hA.isSelfAdjoint,
    cfc_ringInverse_id B hBp.isUnit hB.isSelfAdjoint,
    cfc_ringInverse_id _ hABp.isUnit hABp.isSelfAdjoint]
  exact hc.2 hAp hBp ha hb hab

/-- **`t ↦ -log t` is operator convex on `(0, ∞)`.**
[Bhatia1997, §V.2]; [Tropp2015, §8.4].
Port of `NLAlib.operatorConvexOn_neg_log`. -/
theorem operatorConvexOn_neg_log : OperatorConvexOn (Set.Ioi 0) fun x : ℝ => -Real.log x := by
  refine ⟨convex_Ioi 0, fun d A B hA hB hAs hBs a b ha hb hab => ?_⟩
  open scoped Matrix.Norms.L2Operator in
  have hAp : IsStrictlyPositive A :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr ⟨hA, hAs⟩
  open scoped Matrix.Norms.L2Operator in
  have hBp : IsStrictlyPositive B :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr ⟨hB, hBs⟩
  open scoped Matrix.Norms.L2Operator in
  have hc := (CFC.concaveOn_log (A := Matrix (Fin d) (Fin d) ℂ)).2 hAp hBp ha hb hab
  simp only [cfc_neg, smul_neg, ← neg_add]
  exact neg_le_neg hc

/-! ### The operator Jensen inequality -/

/-- The functional calculus of the indicator of `sᶜ` vanishes on a matrix with spectrum in
`s`. -/
private theorem cfc_indicator_compl_eq_zero {A : Matrix n n 𝕜} {s : Set ℝ}
    (hAs : spectrum ℝ A ⊆ s) : cfc (sᶜ.indicator (1 : ℝ → ℝ)) A = 0 := by
  rw [← cfc_zero ℝ A]
  exact cfc_congr fun x hx => Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (hAs hx)) _

/-- The spectrum of a Hermitian matrix lies in `s` when the functional calculus of the
indicator of `sᶜ` vanishes on it. This locates spectra from identities for `cfc`. -/
private theorem spectrum_subset_of_cfc_indicator_compl_eq_zero {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : Set ℝ} (h : cfc (sᶜ.indicator (1 : ℝ → ℝ)) A = 0) :
    spectrum ℝ A ⊆ s := by
  intro x hx
  by_contra hxs
  have h0 := eqOn_of_cfc_eq_cfc (a := A) (f := sᶜ.indicator (1 : ℝ → ℝ)) (g := 0)
    (h.trans (cfc_zero ℝ A).symm) (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint hx
  rw [Set.indicator_of_mem (Set.mem_compl hxs)] at h0
  exact one_ne_zero h0

/-- Unitary conjugation keeps the spectrum of a Hermitian matrix in `s`. -/
private theorem spectrum_mul_mul_conjTranspose_subset {U A : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) (hA : A.IsHermitian) {s : Set ℝ} (hAs : spectrum ℝ A ⊆ s) :
    spectrum ℝ (U * A * Uᴴ) ⊆ s := by
  refine spectrum_subset_of_cfc_indicator_compl_eq_zero
    (Matrix.isHermitian_mul_mul_conjTranspose U hA) ?_
  rw [cfc_mul_mul_conjTranspose hU rfl hA, cfc_indicator_compl_eq_zero hAs, Matrix.mul_zero,
    Matrix.zero_mul]

/-- Averaging a block matrix with its conjugate by the reflection `1 ⊕ (-1)` removes the
off-diagonal blocks. -/
private theorem half_smul_add_half_smul_reflection (Y : Matrix (m ⊕ n) (m ⊕ n) 𝕜) :
    (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • (Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 (-1 : Matrix n n 𝕜) *
      Y * (Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 (-1 : Matrix n n 𝕜))ᴴ) =
      Matrix.fromBlocks Y.toBlocks₁₁ 0 0 Y.toBlocks₂₂ := by
  nth_rewrite 1 2 [← Matrix.fromBlocks_toBlocks Y]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_neg, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_add, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_neg,
    add_neg_cancel, ← add_smul]
  norm_num

/-- **Pinching.** For an operator convex `f`, `f` of a diagonal block is below the diagonal
block of `f`. -/
private theorem OperatorConvexOn.cfc_toBlocks₂₂_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorConvexOn s f) {X : Matrix (m ⊕ n) (m ⊕ n) 𝕜} (hX : X.IsHermitian)
    (hXs : spectrum ℝ X ⊆ s) : cfc f X.toBlocks₂₂ ≤ (cfc f X).toBlocks₂₂ := by
  have hV : HasOrthonormalCols (Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 (-1 : Matrix n n 𝕜)) := by
    rw [HasOrthonormalCols, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_neg,
      Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, neg_zero]
    exact Matrix.fromBlocks_one
  have h := hf.cfc_smul_add_smul_le hX (Matrix.isHermitian_mul_mul_conjTranspose _ hX) hXs
    (spectrum_mul_mul_conjTranspose_subset hV hX hXs) (a := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  have h11 : X.toBlocks₁₁.IsHermitian := hX.submatrix Sum.inl
  have h22 : X.toBlocks₂₂.IsHermitian := hX.submatrix Sum.inr
  rw [cfc_mul_mul_conjTranspose hV rfl hX, half_smul_add_half_smul_reflection,
    half_smul_add_half_smul_reflection, cfc_fromBlocks_diagonal h11 h22, Matrix.le_iff] at h
  rw [Matrix.le_iff]
  exact h.submatrix (Sum.inr : n → m ⊕ n)

/-- The dilation `[[1 - K Kᴴ, K], [Kᴴ, 0]]` of an isometry `K` is unitary. -/
private theorem hasOrthonormalCols_fromBlocks_one_sub {K : Matrix m n 𝕜}
    (hK : HasOrthonormalCols K) :
    HasOrthonormalCols (Matrix.fromBlocks (1 - K * Kᴴ) K Kᴴ 0) := by
  have hKK : Kᴴ * K = 1 := hK
  have hPK : (1 - K * Kᴴ) * K = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hKK, Matrix.mul_one, sub_self]
  have hKP : Kᴴ * (1 - K * Kᴴ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hKK, Matrix.one_mul, sub_self]
  have hPP : (1 - K * Kᴴ) * (1 - K * Kᴴ) + K * Kᴴ = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPK, Matrix.zero_mul, sub_zero,
      sub_add_cancel]
  rw [HasOrthonormalCols, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, hPP, hPK, hKP, hKK]
  exact Matrix.fromBlocks_one

omit [DecidableEq n] in
/-- The lower right block of the conjugation of a block diagonal matrix by the dilation of
`K` is the compression by `K`. -/
private theorem toBlocks₂₂_fromBlocks_one_sub_mul_mul (K : Matrix m n 𝕜) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) :
    (Matrix.fromBlocks (1 - K * Kᴴ) K Kᴴ 0 * Matrix.fromBlocks A 0 0 B *
      (Matrix.fromBlocks (1 - K * Kᴴ) K Kᴴ 0)ᴴ).toBlocks₂₂ = Kᴴ * A * K := by
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- **The operator Jensen inequality for an isometry** (Hansen–Pedersen). If `f` is operator
convex on `s`, `A` is Hermitian with spectrum in `s`, and `K` has orthonormal columns, then
`f(Kᴴ A K) ≤ Kᴴ f(A) K`.
[Tropp2015, Theorem 8.5.2]; [Bhatia1997, Theorem V.2.3].
Port of `NLAlib.OperatorConvexOn.cfc_conjTranspose_mul_mul_le`, there over `ℂ`.
Result: operator-jensen -/
theorem OperatorConvexOn.cfc_conjTranspose_mul_mul_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorConvexOn s f) {A : Matrix m m 𝕜} (hA : A.IsHermitian)
    (hAs : spectrum ℝ A ⊆ s) {K : Matrix m n 𝕜} (hK : HasOrthonormalCols K) :
    cfc f (Kᴴ * A * K) ≤ Kᴴ * cfc f A * K := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨j⟩⟩
  · exact le_of_eq (Subsingleton.elim _ _)
  have hm : 0 < Fintype.card m := by
    rw [Fintype.card_pos_iff]
    by_contra hm
    rw [not_nonempty_iff] at hm
    have h1 : (Kᴴ * K) j j = 1 := by rw [hK.conjTranspose_mul_self, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have hc : eigenvalue A 0 ∈ s := hAs (hA.eigenvalue_mem_spectrum hm)
  have hU := hasOrthonormalCols_fromBlocks_one_sub hK
  have hB : (algebraMap ℝ (Matrix n n 𝕜) (eigenvalue A 0)).IsHermitian :=
    (IsSelfAdjoint.all _).algebraMap _
  have hD := hA.fromBlocks (Matrix.conjTranspose_zero (m := m) (n := n) (α := 𝕜)) hB
  have hDcfc : ∀ g : ℝ → ℝ, cfc g (Matrix.fromBlocks A 0 0
      (algebraMap ℝ (Matrix n n 𝕜) (eigenvalue A 0))) =
        Matrix.fromBlocks (cfc g A) 0 0 (algebraMap ℝ (Matrix n n 𝕜) (g (eigenvalue A 0))) :=
    fun g => by rw [cfc_fromBlocks_diagonal hA hB, cfc_algebraMap]
  have hDs : spectrum ℝ (Matrix.fromBlocks A 0 0
      (algebraMap ℝ (Matrix n n 𝕜) (eigenvalue A 0))) ⊆ s := by
    refine spectrum_subset_of_cfc_indicator_compl_eq_zero hD ?_
    rw [hDcfc, cfc_indicator_compl_eq_zero hAs,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hc), map_zero, Matrix.fromBlocks_zero]
  have h := hf.cfc_toBlocks₂₂_le (Matrix.isHermitian_mul_mul_conjTranspose _ hD)
    (spectrum_mul_mul_conjTranspose_subset hU hD hDs)
  rwa [cfc_mul_mul_conjTranspose hU rfl hD, hDcfc, toBlocks₂₂_fromBlocks_one_sub_mul_mul,
    toBlocks₂₂_fromBlocks_one_sub_mul_mul] at h

/-- `f` of a block diagonal matrix with Hermitian blocks is the block diagonal matrix of the
`f(A i)`. -/
private theorem cfc_blockDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Matrix m m 𝕜} (hA : ∀ i, (A i).IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.blockDiagonal A) = Matrix.blockDiagonal fun i => cfc f (A i) := by
  choose U hU hAU using fun i => (hA i).exists_eq_mul_diagonal_mul_conjTranspose
  have hW : HasOrthonormalCols (Matrix.blockDiagonal U) := by
    rw [HasOrthonormalCols, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [(hU _).conjTranspose_mul_self]
    exact Matrix.blockDiagonal_one
  have hr : Fintype.card (Fin (Fintype.card m) × ι) = Fintype.card (m × ι) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  have hdiag : ∀ g : ℝ → ℝ, (Matrix.blockDiagonal fun i => U i *
      (Matrix.diagonal fun k : Fin (Fintype.card m) => ((g (eigenvalue (A i) k) : ℝ) : 𝕜)) *
        (U i)ᴴ) = Matrix.blockDiagonal U *
      (Matrix.diagonal fun p : Fin (Fintype.card m) × ι =>
        ((g (eigenvalue (A p.2) p.1) : ℝ) : 𝕜)) * (Matrix.blockDiagonal U)ᴴ := fun g => by
    rw [Matrix.blockDiagonal_mul, Matrix.blockDiagonal_mul, Matrix.blockDiagonal_conjTranspose,
      Matrix.blockDiagonal_diagonal]
  have hA' : Matrix.blockDiagonal A = Matrix.blockDiagonal U *
      (Matrix.diagonal fun p : Fin (Fintype.card m) × ι =>
        ((eigenvalue (A p.2) p.1 : ℝ) : 𝕜)) * (Matrix.blockDiagonal U)ᴴ := by
    exact (congrArg _ (funext hAU)).trans (hdiag id)
  rw [cfc_eq_mul_diagonal_mul_conjTranspose hW hr hA' f, ← hdiag f]
  exact congrArg _ (funext fun i =>
    (cfc_eq_mul_diagonal_mul_conjTranspose (hU i) (Fintype.card_fin _) (hAU i) f).symm)

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- A block diagonal matrix times a stack of blocks is the stack of the products. -/
private theorem blockDiagonal_mul_of {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Matrix m m 𝕜) (K : ι → Matrix m n 𝕜) :
    Matrix.blockDiagonal B * (Matrix.of fun (p : m × ι) (j : n) => K p.2 p.1 j) =
      Matrix.of fun (p : m × ι) (j : n) => (B p.2 * K p.2) p.1 j := by
  ext ⟨x, i⟩ j
  rw [Matrix.mul_apply, Fintype.sum_prod_type_right, Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal_apply, Matrix.of_apply, if_true, Matrix.mul_apply]
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun y _ => by
      rw [Matrix.blockDiagonal_apply, if_neg (Ne.symm hi'), zero_mul]
  · exact fun h => absurd (Finset.mem_univ i) h

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The Gram product of two stacks of blocks is the sum of the Gram products of the blocks. -/
private theorem conjTranspose_of_mul_of {ι : Type*} [Fintype ι] (K L : ι → Matrix m n 𝕜) :
    (Matrix.of fun (p : m × ι) (j : n) => K p.2 p.1 j)ᴴ *
      (Matrix.of fun (p : m × ι) (j : n) => L p.2 p.1 j) = ∑ i, (K i)ᴴ * L i := by
  ext j j'
  rw [Matrix.mul_apply, Fintype.sum_prod_type_right, Matrix.sum_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.mul_apply]

/-- **The operator Jensen inequality.** If `f` is operator convex on `s`, the `A i` are Hermitian
with spectrum in `s`, and `∑ i, (K i)ᴴ * K i = 1`, then
`f(∑ Kᵢᴴ Aᵢ Kᵢ) ≤ ∑ Kᵢᴴ f(Aᵢ) Kᵢ`.
[Tropp2015, Theorem 8.5.2]. Port of `NLAlib.operator_jensen`, there for two terms over `ℂ`.
Result: operator-jensen -/
theorem OperatorConvexOn.cfc_sum_conjTranspose_mul_mul_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorConvexOn s f) {ι : Type*} [Fintype ι] {A : ι → Matrix m m 𝕜}
    (hA : ∀ i, (A i).IsHermitian) (hAs : ∀ i, spectrum ℝ (A i) ⊆ s) {K : ι → Matrix m n 𝕜}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    cfc f (∑ i, (K i)ᴴ * A i * K i) ≤ ∑ i, (K i)ᴴ * cfc f (A i) * K i := by
  classical
  have hS : HasOrthonormalCols (Matrix.of fun (p : m × ι) (j : n) => K p.2 p.1 j) := by
    rw [HasOrthonormalCols, conjTranspose_of_mul_of, hK]
  have hD : (Matrix.blockDiagonal A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.blockDiagonal_conjTranspose]
    exact congrArg _ (funext hA)
  have hDs : spectrum ℝ (Matrix.blockDiagonal A) ⊆ s := by
    refine spectrum_subset_of_cfc_indicator_compl_eq_zero hD ?_
    rw [cfc_blockDiagonal hA]
    simp only [cfc_indicator_compl_eq_zero (hAs _)]
    exact Matrix.blockDiagonal_zero
  have hsum : ∀ B : ι → Matrix m m 𝕜,
      (Matrix.of fun (p : m × ι) (j : n) => K p.2 p.1 j)ᴴ * Matrix.blockDiagonal B *
        (Matrix.of fun (p : m × ι) (j : n) => K p.2 p.1 j) = ∑ i, (K i)ᴴ * B i * K i :=
    fun B => by
      rw [Matrix.mul_assoc, blockDiagonal_mul_of]
      exact (conjTranspose_of_mul_of K fun i => B i * K i).trans
        (Finset.sum_congr rfl fun i _ => (Matrix.mul_assoc _ _ _).symm)
  have h := hf.cfc_conjTranspose_mul_mul_le hD hDs hS
  rwa [cfc_blockDiagonal hA, hsum, hsum] at h

/-! ### Operator convexity of `t log t`

`t log t = t f(1/t)` for `f = -log`, and `X ↦ X^{1/2} f(X⁻¹) X^{1/2}` is convex whenever `f` is
operator convex, by the operator Jensen inequality with `K i = √(a i) • X i^{1/2} X^{-1/2}`. -/

/-- Products of functions of one matrix. -/
private theorem cfc_mul_cfc (X : Matrix n n 𝕜) (φ ψ : ℝ → ℝ) :
    cfc φ X * cfc ψ X = cfc (fun x => φ x * ψ x) X :=
  (cfc_mul φ ψ X (X.finite_real_spectrum.continuousOn _)
    (X.finite_real_spectrum.continuousOn _)).symm

/-- `X^{1/2} φ(X) X^{1/2} = (t φ(t))(X)` for positive definite `X`. -/
private theorem cfc_sqrt_mul_cfc_mul_cfc_sqrt {X : Matrix n n 𝕜} (hX : X.PosDef) (φ : ℝ → ℝ) :
    cfc Real.sqrt X * cfc φ X * cfc Real.sqrt X = cfc (fun x => x * φ x) X := by
  rw [cfc_mul_cfc, cfc_mul_cfc]
  refine cfc_congr fun x hx => ?_
  rw [mul_right_comm, Real.mul_self_sqrt (le_of_lt (hX.spectrum_subset_Ioi hx))]

/-- A function equal to `1` on the positive reals gives `1` on a positive definite matrix. -/
private theorem cfc_eq_one_of_forall_pos {X : Matrix n n 𝕜} (hX : X.PosDef) {φ : ℝ → ℝ}
    (h : ∀ x : ℝ, 0 < x → φ x = 1) : cfc φ X = 1 := by
  rw [← cfc_const_one ℝ X hX.isHermitian.isSelfAdjoint]
  exact cfc_congr fun x hx => h x (hX.spectrum_subset_Ioi hx)

/-- `-log` of the inverse is the logarithm. -/
private theorem cfc_neg_log_cfc_inv {X : Matrix n n 𝕜} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => -Real.log x) (cfc (fun x : ℝ => x⁻¹) X) = cfc Real.log X := by
  rw [← cfc_comp' (fun x : ℝ => -Real.log x) (fun x : ℝ => x⁻¹) X
    ((X.finite_real_spectrum.image _).continuousOn _) (X.finite_real_spectrum.continuousOn _)
    hX.isSelfAdjoint]
  exact cfc_congr fun x _ => by simp only [Real.log_inv, neg_neg]

omit [DecidableEq n] in
/-- The congruence by `√c • X^{1/2} r` in terms of the congruence by `r`. -/
private theorem conjTranspose_smul_mul_mul_smul {c : ℝ} (hc : 0 ≤ c) {S r : Matrix n n 𝕜}
    (hS : Sᴴ = S) (hr : rᴴ = r) (N : Matrix n n 𝕜) :
    (√c • (S * r))ᴴ * N * (√c • (S * r)) = c • (r * (S * N * S) * r) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hr, hS, star_trivial]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hc,
    Matrix.mul_assoc]

/-- `X^{1/2} X^{1/2} = X` for positive definite `X`, in terms of `cfc`. -/
private theorem cfc_sqrt_mul_cfc_sqrt {X : Matrix n n 𝕜} (hX : X.PosDef) :
    cfc Real.sqrt X * cfc Real.sqrt X = X := by
  rw [cfc_mul_cfc]
  refine (cfc_congr fun x hx => ?_).trans (cfc_id' ℝ X hX.isHermitian.isSelfAdjoint)
  exact Real.mul_self_sqrt (le_of_lt (hX.spectrum_subset_Ioi hx))

/-- The inverse square root `r` of a positive definite `X`, with the identities used in the
proof of operator convexity of `t log t`. -/
private theorem exists_inv_sqrt {X : Matrix n n 𝕜} (hX : X.PosDef) :
    ∃ r : Matrix n n 𝕜, rᴴ = r ∧ cfc Real.sqrt X * r = 1 ∧ r * cfc Real.sqrt X = 1 ∧
      r * X * r = 1 ∧ cfc (fun x : ℝ => -Real.log x) (r * r) = cfc Real.log X := by
  have hsr : cfc Real.sqrt X * cfc (fun x : ℝ => (√x)⁻¹) X = 1 := by
    rw [cfc_mul_cfc]
    exact cfc_eq_one_of_forall_pos hX fun x hx => mul_inv_cancel₀ (Real.sqrt_pos.mpr hx).ne'
  have hrs : cfc (fun x : ℝ => (√x)⁻¹) X * cfc Real.sqrt X = 1 := by
    rw [cfc_mul_cfc]
    exact cfc_eq_one_of_forall_pos hX fun x hx => inv_mul_cancel₀ (Real.sqrt_pos.mpr hx).ne'
  have hrr : cfc (fun x : ℝ => (√x)⁻¹) X * cfc (fun x : ℝ => (√x)⁻¹) X =
      cfc (fun x : ℝ => x⁻¹) X := by
    rw [cfc_mul_cfc]
    refine cfc_congr fun x hx => ?_
    rw [← mul_inv, Real.mul_self_sqrt (le_of_lt (hX.spectrum_subset_Ioi hx))]
  refine ⟨cfc (fun x : ℝ => (√x)⁻¹) X, (cfc_predicate _ X : IsSelfAdjoint _), hsr, hrs, ?_, ?_⟩
  · nth_rewrite 2 [← cfc_sqrt_mul_cfc_sqrt hX]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hsr, Matrix.mul_one, hrs]
  · rw [hrr, cfc_neg_log_cfc_inv hX.isHermitian]

/-- Convexity of `X ↦ X log X` on positive definite matrices over any field. -/
private theorem cfc_mul_log_smul_add_smul_le {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hX : (a • A + b • B).PosDef) :
    cfc (fun x : ℝ => x * Real.log x) (a • A + b • B) ≤
      a • cfc (fun x : ℝ => x * Real.log x) A + b • cfc (fun x : ℝ => x * Real.log x) B := by
  have hH : ∀ (φ : ℝ → ℝ) (Y : Matrix n n 𝕜), (cfc φ Y)ᴴ = cfc φ Y := fun φ Y =>
    (cfc_predicate φ Y : IsSelfAdjoint (cfc φ Y))
  have hinv : ∀ Y : Matrix n n 𝕜, Y.PosDef →
      cfc Real.sqrt Y * cfc (fun x : ℝ => x⁻¹) Y * cfc Real.sqrt Y = 1 := fun Y hY => by
    rw [cfc_sqrt_mul_cfc_mul_cfc_sqrt hY]
    exact cfc_eq_one_of_forall_pos hY fun x hx => mul_inv_cancel₀ hx.ne'
  obtain ⟨r, hrH, hsr, hrs, hrXr, hlogX⟩ := exists_inv_sqrt hX
  have hsp : ∀ Y : Matrix n n 𝕜, Y.PosDef →
      spectrum ℝ (cfc (fun x : ℝ => x⁻¹) Y) ⊆ Set.Ioi 0 := fun Y hY => by
    rw [cfc_map_spectrum (fun x : ℝ => x⁻¹) Y hY.isHermitian.isSelfAdjoint
      (Y.finite_real_spectrum.continuousOn _)]
    rintro _ ⟨x, hx, rfl⟩
    exact inv_pos.mpr (Set.mem_Ioi.mp (hY.spectrum_subset_Ioi hx))
  have hK : ∑ i : Fin 2, ((![√a • (cfc Real.sqrt A * r), √b • (cfc Real.sqrt B * r)] :
      Fin 2 → Matrix n n 𝕜) i)ᴴ *
        (![√a • (cfc Real.sqrt A * r), √b • (cfc Real.sqrt B * r)] : Fin 2 → Matrix n n 𝕜) i =
          1 := by
    have h1 := conjTranspose_smul_mul_mul_smul ha (hH Real.sqrt A) hrH 1
    have h2 := conjTranspose_smul_mul_mul_smul hb (hH Real.sqrt B) hrH 1
    rw [Matrix.mul_one, Matrix.mul_one, cfc_sqrt_mul_cfc_sqrt hA] at h1
    rw [Matrix.mul_one, Matrix.mul_one, cfc_sqrt_mul_cfc_sqrt hB] at h2
    rw [Fin.sum_univ_two]
    change (√a • (cfc Real.sqrt A * r))ᴴ * (√a • (cfc Real.sqrt A * r)) +
      (√b • (cfc Real.sqrt B * r))ᴴ * (√b • (cfc Real.sqrt B * r)) = 1
    have e : ∀ (c : ℝ) (Y : Matrix n n 𝕜), c • (r * Y * r) = r * (c • Y) * r := fun c Y => by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, h2, e, e, ← Matrix.add_mul, ← Matrix.mul_add]
    exact hrXr
  have hJ := operatorConvexOn_neg_log.cfc_sum_conjTranspose_mul_mul_le
    (A := ![cfc (fun x : ℝ => x⁻¹) A, cfc (fun x : ℝ => x⁻¹) B])
    (Fin.forall_fin_two.mpr ⟨hH _ A, hH _ B⟩) (Fin.forall_fin_two.mpr ⟨hsp A hA, hsp B hB⟩) hK
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hJ
  change cfc (fun x : ℝ => -Real.log x)
      ((√a • (cfc Real.sqrt A * r))ᴴ * cfc (fun x : ℝ => x⁻¹) A * (√a • (cfc Real.sqrt A * r)) +
        (√b • (cfc Real.sqrt B * r))ᴴ * cfc (fun x : ℝ => x⁻¹) B *
          (√b • (cfc Real.sqrt B * r))) ≤
    (√a • (cfc Real.sqrt A * r))ᴴ * cfc (fun x : ℝ => -Real.log x) (cfc (fun x : ℝ => x⁻¹) A) *
        (√a • (cfc Real.sqrt A * r)) +
      (√b • (cfc Real.sqrt B * r))ᴴ * cfc (fun x : ℝ => -Real.log x) (cfc (fun x : ℝ => x⁻¹) B) *
        (√b • (cfc Real.sqrt B * r)) at hJ
  have hKa := conjTranspose_smul_mul_mul_smul ha (hH Real.sqrt A) hrH
  have hKb := conjTranspose_smul_mul_mul_smul hb (hH Real.sqrt B) hrH
  rw [hKa, hKb, hKa, hKb, hinv A hA, hinv B hB, Matrix.mul_one, ← add_smul, hab, one_smul, hlogX,
    cfc_neg_log_cfc_inv hA.isHermitian, cfc_neg_log_cfc_inv hB.isHermitian,
    cfc_sqrt_mul_cfc_mul_cfc_sqrt hA, cfc_sqrt_mul_cfc_mul_cfc_sqrt hB] at hJ
  have h2 := star_left_conjugate_le_conjugate hJ (cfc Real.sqrt (a • A + b • B))
  have hR : ∀ N : Matrix n n 𝕜, cfc Real.sqrt (a • A + b • B) * (r * N * r) *
      cfc Real.sqrt (a • A + b • B) = N := fun N => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hsr, Matrix.one_mul, Matrix.mul_assoc, hrs,
      Matrix.mul_one]
  rwa [Matrix.star_eq_conjTranspose, hH, cfc_sqrt_mul_cfc_mul_cfc_sqrt hX, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hR,
    hR] at h2

/-- `t ↦ t log t` is operator convex on `(0, ∞)`. [Bhatia1997, §V.2]. -/
theorem operatorConvexOn_mul_log : OperatorConvexOn (Set.Ioi 0) fun x : ℝ => x * Real.log x := by
  refine ⟨convex_Ioi 0, fun d A B hA hB hAs hBs a b ha hb hab => ?_⟩
  have hAp : A.PosDef := hA.posDef_iff_eigenvalue_pos.mpr (hA.spectrum_subset_iff.mp hAs)
  have hBp : B.PosDef := hB.posDef_iff_eigenvalue_pos.mpr (hB.spectrum_subset_iff.mp hBs)
  open scoped Matrix.Norms.L2Operator in
  have hX : IsStrictlyPositive (a • A + b • B) :=
    (CStarAlgebra.convexOn_ringInverse (A := Matrix (Fin d) (Fin d) ℂ)).1 hAp.isStrictlyPositive
      hBp.isStrictlyPositive ha hb hab
  exact cfc_mul_log_smul_add_smul_le hAp hBp ha hb hab (Matrix.isStrictlyPositive_iff_posDef.mp hX)

end NLAlib
