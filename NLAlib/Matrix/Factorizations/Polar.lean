/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import NLAlib.Matrix.Functions.AbsoluteValue
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Majorization.TraceInequalities

/-!
# The polar decomposition

Every matrix is `A = U |A|` with `|A| = (Aᴴ A)^{1/2}`, spelled `CFC.sqrt (Aᴴ * A)`, and `U` a
partial isometry. The canonical choice is `NLAlib.polarFactor A = A |A|⁺`, which is `U Vᴴ` for a
thin SVD `A = U Σ Vᴴ` with positive singular values; it has orthonormal columns exactly when `A`
has full column rank. The positive semidefinite factor is unique, and the isometric factor is
unique exactly at full column rank.

The polar factor is the nearest matrix with orthonormal columns in every unitarily invariant
norm. The Procrustes problems it solves are in `NLAlib.Matrix.Factorizations.Procrustes`.

## Main definitions

* `NLAlib.polarFactor`: the partial isometry `A * pinv (CFC.sqrt (Aᴴ * A))`.

## Main results

* `NLAlib.polarFactor_mul_sqrt`, `NLAlib.sqrt_mul_polarFactor`: the two polar decompositions.
* `NLAlib.IsSVD.polarFactor_eq`: the polar factor through an SVD.
* `NLAlib.conjTranspose_polarFactor_mul_self`, `NLAlib.polarFactor_mul_conjTranspose_self`: the
  polar factor is a partial isometry from the row space onto the range.
* `NLAlib.hasOrthonormalCols_polarFactor_iff`, `NLAlib.mul_polarFactor_eq_polarFactor_mul`.
* `NLAlib.exists_hasOrthonormalCols_mul_sqrt_eq`, `NLAlib.eq_sqrt_of_hasOrthonormalCols_mul_eq`,
  `NLAlib.forall_eq_of_mul_sqrt_eq_iff`: existence and uniqueness.
* `NLAlib.SymmetricGauge.matrixNorm_sub_le_matrixNorm_sub_of_mul_sqrt_eq`: the nearest isometry.
* `NLAlib.trace_eq_nuclearNorm_iff_posSemidef`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n r : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype r]

/-! ### Diagonal forms over a frame -/

omit [Fintype l] [Fintype n] in
/-- A product of two matrices in diagonal form over a common frame. -/
private theorem mul_diagonal_mul_mul [DecidableEq r] {X : Matrix l r 𝕜} {Y : Matrix m r 𝕜}
    {Z : Matrix n r 𝕜} (hY : HasOrthonormalCols Y) {a b c : r → 𝕜} (h : ∀ i, a i * b i = c i) :
    X * Matrix.diagonal a * Yᴴ * (Y * Matrix.diagonal b * Zᴴ) = X * Matrix.diagonal c * Zᴴ := by
  rw [← funext h, ← Matrix.diagonal_mul_diagonal, Matrix.mul_assoc Y, ← Matrix.mul_assoc _ Y,
    hY.mul_conjTranspose_mul_cancel_right]
  simp only [Matrix.mul_assoc]

open scoped Classical in
/-- The absolute value through an SVD: `(Aᴴ A)^{1/2} = V Σ Vᴴ`. -/
private theorem IsSVD.sqrt_eq [DecidableEq r] {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {σ : r → ℝ} {V : Matrix n r 𝕜} (h : IsSVD A U σ V) :
    CFC.sqrt (Aᴴ * A) = V * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ := by
  refine CFC.sqrt_unique ?_ (Matrix.PosSemidef.nonneg ?_)
  · rw [h.conjTranspose_mul_self_eq]
    exact mul_diagonal_mul_mul h.hasOrthonormalCols_right fun i => by
      rw [sq, RCLike.ofReal_mul]
  · exact (Matrix.PosSemidef.diagonal fun i => RCLike.ofReal_nonneg.mpr (h.nonneg i))
      |>.mul_mul_conjTranspose_same V

/-- Every matrix has an SVD with as many columns as its rank. -/
private theorem exists_isSVD_rank (A : Matrix m n 𝕜) :
    ∃ (k : ℕ) (U : Matrix m (Fin k) 𝕜) (σ : Fin k → ℝ) (V : Matrix n (Fin k) 𝕜),
      IsSVD A U σ V :=
  ⟨A.rank, _, _, _,
    (exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width).choose_spec.choose_spec⟩

/-- A matrix that commutes with a Hermitian matrix commutes with its pseudoinverse. -/
private theorem mul_pinv_eq_pinv_mul_of_mul_eq {S B : Matrix n n 𝕜} (hS : S.IsHermitian)
    (h : B * S = S * B) : B * pinv S = pinv S * B := by
  have hSX : S * pinv S = pinv S * S := by
    rw [mul_pinv, pinv_mul, hS.eq]
  have hP : (S * pinv S).IsHermitian := by
    rw [mul_pinv]
    exact conjTranspose_rangeProjector S
  have h' : Bᴴ * S = S * Bᴴ := by
    have := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq] at this
    exact this.symm
  -- `P = S S⁺` satisfies `P B P = B P` and `P Bᴴ P = Bᴴ P`, so `P B = B P`.
  have key (C : Matrix n n 𝕜) (hC : C * S = S * C) :
      S * pinv S * (C * (S * pinv S)) = C * (S * pinv S) := by
    rw [← Matrix.mul_assoc C, hC, Matrix.mul_assoc S C, ← Matrix.mul_assoc (S * pinv S),
      mul_pinv_mul_self]
  have hPB : S * pinv S * B = B * (S * pinv S) := by
    rw [← key B h]
    have := congrArg Matrix.conjTranspose (key Bᴴ h')
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP.eq] at this
    rw [← this]
    simp only [Matrix.mul_assoc]
  calc B * pinv S = B * (S * pinv S) * pinv S := by
        rw [hSX, Matrix.mul_assoc, pinv_mul_mul_pinv]
    _ = pinv S * (S * B) * pinv S := by rw [← hPB, hSX]; simp only [Matrix.mul_assoc]
    _ = pinv S * B * (S * pinv S) := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = pinv S * B := by
        rw [Matrix.mul_assoc, ← hPB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, pinv_mul_mul_pinv]

variable [DecidableEq n]

/-! ### The polar factor -/

/-- The **polar factor** of a matrix: the partial isometry `A |A|⁺`, where `|A| = (Aᴴ A)^{1/2}`.
[HornJohnson2013, Theorem 7.3.1]; [Higham2008, Theorem 8.1].
Port of `NLAlib.polarFrame`, there for real matrices of full column rank. -/
noncomputable def polarFactor (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  A * pinv (CFC.sqrt (Aᴴ * A))

/-- **The polar factor through an SVD**: for `A = U Σ Vᴴ`, the polar factor is `U E Vᴴ` with
`E` the diagonal indicator of the positive singular values. -/
theorem IsSVD.polarFactor_eq [DecidableEq r] {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ}
    {V : Matrix n r 𝕜} (h : IsSVD A U σ V) :
    polarFactor A = U * Matrix.diagonal (fun i => if σ i = 0 then (0 : 𝕜) else 1) * Vᴴ := by
  have hS : IsSVD (CFC.sqrt (Aᴴ * A)) V σ V :=
    ⟨h.hasOrthonormalCols_right, h.hasOrthonormalCols_right, h.nonneg, h.sqrt_eq⟩
  rw [polarFactor, hS.pinv_eq]
  refine (congrArg (· * _) h.eq).trans (mul_diagonal_mul_mul h.hasOrthonormalCols_right fun i => ?_)
  by_cases hi : σ i = 0 <;> simp [hi]

/-- **The polar decomposition** `A = U |A|`.
Port of `NLAlib.exists_isometry_mul_sqrt_gram_eq`, for the canonical factor. -/
theorem polarFactor_mul_sqrt (A : Matrix m n 𝕜) :
    polarFactor A * CFC.sqrt (Aᴴ * A) = A := by
  obtain ⟨k, U, σ, V, h⟩ := exists_isSVD_rank A
  rw [h.polarFactor_eq, h.sqrt_eq]
  refine (mul_diagonal_mul_mul h.hasOrthonormalCols_right fun i => ?_).trans h.eq.symm
  by_cases hi : σ i = 0 <;> simp [hi]

open scoped Classical in
/-- **The left polar decomposition** `A = |Aᴴ| U`, with the same factor `U`.
Port of `NLAlib.sqrt_rowGram_mul_eq_of_isometry_mul_sqrt_gram_eq`. -/
theorem sqrt_mul_polarFactor (A : Matrix m n 𝕜) :
    CFC.sqrt (A * Aᴴ) * polarFactor A = A := by
  obtain ⟨k, U, σ, V, h⟩ := exists_isSVD_rank A
  have hS := h.conjTranspose.sqrt_eq
  rw [Matrix.conjTranspose_conjTranspose] at hS
  rw [h.polarFactor_eq, hS]
  refine (mul_diagonal_mul_mul h.hasOrthonormalCols_left fun i => ?_).trans h.eq.symm
  by_cases hi : σ i = 0 <;> simp [hi]

open scoped Classical in
/-- The polar factor from the left absolute value: `U = |Aᴴ|⁺ A`. -/
theorem polarFactor_eq_pinv_sqrt_mul (A : Matrix m n 𝕜) :
    polarFactor A = pinv (CFC.sqrt (A * Aᴴ)) * A := by
  obtain ⟨k, U, σ, V, h⟩ := exists_isSVD_rank A
  have hS := h.conjTranspose.sqrt_eq
  rw [Matrix.conjTranspose_conjTranspose] at hS
  have hS' : IsSVD (CFC.sqrt (A * Aᴴ)) U σ U :=
    ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_left, h.nonneg, hS⟩
  rw [h.polarFactor_eq, hS'.pinv_eq]
  refine ((congrArg (_ * ·) h.eq).trans
    (mul_diagonal_mul_mul h.hasOrthonormalCols_left fun i => ?_)).symm
  by_cases hi : σ i = 0 <;> simp [hi]

/-- The polar factor of the conjugate transpose. -/
theorem polarFactor_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) :
    polarFactor Aᴴ = (polarFactor A)ᴴ := by
  obtain ⟨k, U, σ, V, h⟩ := exists_isSVD_rank A
  rw [h.polarFactor_eq, h.conjTranspose.polarFactor_eq, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext i
  by_cases hi : σ i = 0 <;> simp [hi]

/-- The polar factor is a partial isometry with initial space the row space of `A`. -/
theorem conjTranspose_polarFactor_mul_self (A : Matrix m n 𝕜) :
    (polarFactor A)ᴴ * polarFactor A = rangeProjector Aᴴ := by
  classical
  obtain ⟨k, U, σ, V, h⟩ := exists_isSVD_rank A
  rw [← polarFactor_conjTranspose, ← pinv_mul, h.conjTranspose.polarFactor_eq, h.polarFactor_eq,
    h.pinv_eq, mul_diagonal_mul_mul h.hasOrthonormalCols_left fun i => rfl]
  refine ((congrArg (_ * ·) h.eq).trans
    (mul_diagonal_mul_mul h.hasOrthonormalCols_left fun i => ?_)).symm
  by_cases hi : σ i = 0 <;> simp [hi]

/-- The polar factor is a partial isometry with final space the range of `A`. -/
theorem polarFactor_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    polarFactor A * (polarFactor A)ᴴ = rangeProjector A := by
  classical
  have h := conjTranspose_polarFactor_mul_self Aᴴ
  rwa [polarFactor_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h

/-- The polar factor has orthonormal columns exactly when the matrix has full column rank.
Port of `NLAlib.hasOrthonormalCols_polarFrame`. -/
theorem hasOrthonormalCols_polarFactor_iff {A : Matrix m n 𝕜} :
    HasOrthonormalCols (polarFactor A) ↔ Function.Injective A.mulVec := by
  rw [hasOrthonormalCols_iff, conjTranspose_polarFactor_mul_self, ← pinv_mul]
  refine ⟨fun h => Function.LeftInverse.injective (g := (pinv A).mulVec) fun x => ?_,
    pinv_mul_self_of_injective⟩
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- The polar factor commutes with a unitary factor on the left. -/
theorem polarFactor_mul_left [DecidableEq m] {W : Matrix l m 𝕜} (hW : HasOrthonormalCols W)
    (A : Matrix m n 𝕜) : polarFactor (W * A) = W * polarFactor A := by
  rw [polarFactor, polarFactor, hW.conjTranspose_mul_mul, Matrix.mul_assoc]

/-- The polar factor of a positive definite matrix is the identity. -/
theorem _root_.Matrix.PosDef.polarFactor_eq_one {A : Matrix n n 𝕜} (hA : A.PosDef) :
    polarFactor A = 1 := by
  rw [polarFactor, hA.isHermitian.eq, CFC.sqrt_mul_self A hA.posSemidef.nonneg,
    pinv_of_isUnit hA.isUnit,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)]

/-- **The polar factor intertwines.** If `A T = T B` and `Aᴴ T = T Bᴴ`, then
`A U = U B` for the polar factor `U` of `T`.
Port of `NLAlib.mul_polarFrame_eq_polarFrame_mul_of_intertwining`, there for `T` of full column
rank. -/
theorem mul_polarFactor_eq_polarFactor_mul {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    {T : Matrix m n 𝕜} (h : A * T = T * B) (h' : Aᴴ * T = T * Bᴴ) :
    A * polarFactor T = polarFactor T * B := by
  have h'' : Tᴴ * A = B * Tᴴ := by
    have := congrArg Matrix.conjTranspose h'
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose] at this
  have hG : Commute (Tᴴ * T) B := by
    rw [Commute, SemiconjBy, Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, h'', Matrix.mul_assoc]
  have hS : Commute (CFC.sqrt (Tᴴ * T)) B := by
    rw [CFC.sqrt_eq_cfc]
    exact Commute.cfc_nnreal hG _
  have hH : (CFC.sqrt (Tᴴ * T)).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  rw [polarFactor, ← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.mul_assoc,
    mul_pinv_eq_pinv_mul_of_mul_eq hH hS.eq.symm]

/-! ### Existence and uniqueness -/

/-- **A matrix with at least as many rows as columns is an isometry times its absolute value.**
[HornJohnson2013, Theorem 7.3.1]. Port of `NLAlib.exists_isometry_mul_sqrt_gram_eq`.
Result: polar-decomposition -/
theorem exists_hasOrthonormalCols_mul_sqrt_eq (A : Matrix m n 𝕜)
    (h : Fintype.card n ≤ Fintype.card m) :
    ∃ U : Matrix m n 𝕜, HasOrthonormalCols U ∧ U * CFC.sqrt (Aᴴ * A) = A := by
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A A.rank_le_card_width h le_rfl
  have hV : V * Vᴴ = 1 :=
    hSVD.hasOrthonormalCols_right.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  refine ⟨U * Vᴴ, ?_, ?_⟩
  · rw [hasOrthonormalCols_iff, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, hSVD.hasOrthonormalCols_left.conjTranspose_mul_cancel_left, hV]
  · rw [hSVD.sqrt_eq, Matrix.mul_assoc V, Matrix.mul_assoc U,
      hSVD.hasOrthonormalCols_right.conjTranspose_mul_cancel_left, ← Matrix.mul_assoc]
    exact hSVD.eq.symm

/-- **The positive semidefinite polar factor is unique**: if `A = U P` with `U` having
orthonormal columns and `P` positive semidefinite, then `P = (Aᴴ A)^{1/2}`.
Port of `NLAlib.eq_sqrt_gram_of_isometry_mul_eq`. -/
theorem eq_sqrt_of_hasOrthonormalCols_mul_eq {A U : Matrix m n 𝕜} {P : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) (hP : P.PosSemidef) (h : U * P = A) :
    P = CFC.sqrt (Aᴴ * A) := by
  refine (CFC.sqrt_unique ?_ hP.nonneg).symm
  rw [← h, hU.conjTranspose_mul_mul, hP.isHermitian.eq]

/-- For a matrix of full column rank, the isometric polar factor is the polar factor.
Port of `NLAlib.eq_polarFrame_of_isometry_mul_sqrt_gram_eq`. -/
theorem eq_polarFactor_of_mul_sqrt_eq {A U : Matrix m n 𝕜} (hA : Function.Injective A.mulVec)
    (h : U * CFC.sqrt (Aᴴ * A) = A) : U = polarFactor A := by
  have hS : IsUnit (CFC.sqrt (Aᴴ * A)) := (Matrix.PosDef.conjTranspose_mul_self A hA).isUnit_sqrt
  calc U = U * (CFC.sqrt (Aᴴ * A) * pinv (CFC.sqrt (Aᴴ * A))) := by
        rw [pinv_of_isUnit hS, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS),
          Matrix.mul_one]
    _ = polarFactor A := by rw [← Matrix.mul_assoc, h, polarFactor]

/-- **The isometric polar factor is unique exactly when the matrix has full column rank.**
Port of `NLAlib.polar_isometry_unique_iff_rank_eq_card`. -/
theorem forall_eq_of_mul_sqrt_eq_iff {A U : Matrix m n 𝕜} (hU : HasOrthonormalCols U)
    (h : U * CFC.sqrt (Aᴴ * A) = A) :
    (∀ V : Matrix m n 𝕜, HasOrthonormalCols V → V * CFC.sqrt (Aᴴ * A) = A → V = U) ↔
      Function.Injective A.mulVec := by
  refine ⟨fun hall => ?_, fun hA V _ hV =>
    (eq_polarFactor_of_mul_sqrt_eq hA hV).trans (eq_polarFactor_of_mul_sqrt_eq hA h).symm⟩
  have hS : (CFC.sqrt (Aᴴ * A)).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  obtain ⟨S, hSdef⟩ : ∃ S, S = CFC.sqrt (Aᴴ * A) := ⟨_, rfl⟩
  rw [← hSdef] at h hall hS
  -- The reflection `2 R - 1` through the range of `|A|` gives a second isometric factor.
  have hRR : rangeProjector S * rangeProjector S = rangeProjector S :=
    rangeProjector_mul_rangeProjector S
  have hV := hall (U * (rangeProjector S + rangeProjector S - 1)) ?_ ?_
  · have h2 : rangeProjector S + rangeProjector S - 1 = 1 := by
      rw [← hU.mul_right_inj, hV, Matrix.mul_one]
    have h3 : (2 : 𝕜) • rangeProjector S = (2 : 𝕜) • (1 : Matrix n n 𝕜) := by
      rw [two_smul, two_smul]
      exact sub_eq_iff_eq_add.mp h2
    have hXS : pinv S * S = 1 := by
      rw [pinv_mul, hS.eq, smul_right_injective _ (two_ne_zero (α := 𝕜)) h3]
    refine Function.LeftInverse.injective (g := (pinv S * Uᴴ).mulVec) fun x => ?_
    rw [Matrix.mulVec_mulVec, ← h, Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left, hXS,
      Matrix.one_mulVec]
  · rw [hasOrthonormalCols_iff, hU.conjTranspose_mul_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_add, conjTranspose_rangeProjector, Matrix.conjTranspose_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hRR]
    abel
  · rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.add_mul, rangeProjector_mul_self, Matrix.one_mul,
      add_sub_cancel_right, h]

/-! ### The nearest isometry -/

omit [DecidableEq n] in
/-- The norm of a Hermitian matrix is the gauge of any sequence that has the absolute values of
its eigenvalues. -/
private theorem SymmetricGauge.matrixNorm_eq_of_abs_eq_abs_eigenvalue (Φ : SymmetricGauge)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {y : ℕ →₀ ℝ}
    (hy : ∀ i, i < Fintype.card n → |y i| = |eigenvalue H i|)
    (hy0 : ∀ i, Fintype.card n ≤ i → y i = 0) : Φ.matrixNorm H = Φ y := by
  obtain ⟨e, he⟩ := hH.exists_equiv_abs_eigenvalue_eq_singularValues
  let τ : Equiv.Perm ℕ := Equiv.Perm.extendDomain e Fin.equivSubtype
  rw [Φ.matrixNorm_def, ← Φ.map_equivMapDomain τ.symm]
  refine Φ.eq_of_abs_eq fun i => ?_
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm, coe_singularValuesFinsupp]
  obtain hi | hi := lt_or_ge i (Fintype.card n)
  · have h' : τ i = (e ⟨i, hi⟩ : ℕ) :=
      Equiv.Perm.extendDomain_apply_image e Fin.equivSubtype ⟨i, hi⟩
    rw [h', ← he ⟨i, hi⟩, abs_abs, hy i hi]
  · have h' : τ i = i :=
      Equiv.Perm.extendDomain_apply_not_subtype e Fin.equivSubtype (b := i) (not_lt.mpr hi)
    rw [h', singularValues_of_card_cols_le H hi, hy0 i hi]

/-- **The polar factor is the nearest matrix with orthonormal columns** in every unitarily
invariant norm (Fan and Hoffman). [Higham2008, Theorem 8.4]; [HornJohnson2013, §7.4.9 context].
Port of `NLAlib.invariantNorm_sub_polar_le_sub_isometry`, there over `ℝ`.
Result: nearest-unitary -/
theorem SymmetricGauge.matrixNorm_sub_le_matrixNorm_sub_of_mul_sqrt_eq (Φ : SymmetricGauge)
    {A U V : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (hA : U * CFC.sqrt (Aᴴ * A) = A)
    (hV : HasOrthonormalCols V) : Φ.matrixNorm (A - U) ≤ Φ.matrixNorm (A - V) := by
  classical
  have hS : (CFC.sqrt (Aᴴ * A)).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hsub : CFC.sqrt (Aᴴ * A) - 1 = CFC.sqrt (Aᴴ * A) + (-1 : ℝ) • (1 : Matrix n n 𝕜) := by
    rw [neg_one_smul, sub_eq_add_neg]
  have hH : (CFC.sqrt (Aᴴ * A) - 1).IsHermitian := hS.sub Matrix.isHermitian_one
  have h1 : A - U = U * (CFC.sqrt (Aᴴ * A) - 1) := by rw [Matrix.mul_sub, hA, Matrix.mul_one]
  have key : Φ.matrixNorm (CFC.sqrt (Aᴴ * A) - 1) =
      Φ (singularValuesFinsupp A - singularValuesFinsupp V) := by
    refine Φ.matrixNorm_eq_of_abs_eq_abs_eigenvalue hH (fun i hi => ?_) fun i hi => ?_
    · rw [Finsupp.sub_apply, coe_singularValuesFinsupp, coe_singularValuesFinsupp,
        hV.singularValues_eq_one hi, hsub, hS.eigenvalue_add_smul_one (-1) hi,
        eigenvalue_sqrt_conjTranspose_mul_self A hi, sub_eq_add_neg]
    · rw [Finsupp.sub_apply, coe_singularValuesFinsupp, coe_singularValuesFinsupp,
        singularValues_of_card_cols_le A hi, singularValues_of_card_cols_le V hi, sub_zero]
  rw [h1, Φ.matrixNorm_mul_left_of_hasOrthonormalCols hU, key]
  exact Φ.apply_singularValuesFinsupp_sub_le A V

omit [DecidableEq n] in
/-- The trace of a square matrix equals its nuclear norm exactly when it is positive
semidefinite. Port of `NLAlib.trace_eq_nuclearNorm_iff_posSemidef`, there over `ℝ`. -/
theorem trace_eq_nuclearNorm_iff_posSemidef {M : Matrix n n 𝕜} :
    M.trace = (nuclearNorm M : 𝕜) ↔ M.PosSemidef := by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- With `M = U S` and `S = T²`, the hypothesis says `‖T - U T‖_F = 0`.
    obtain ⟨U, hU, hUS⟩ := exists_hasOrthonormalCols_mul_sqrt_eq M le_rfl
    have htr : RCLike.re M.trace = RCLike.re (CFC.sqrt (Mᴴ * M)).trace := by
      rw [h, RCLike.ofReal_re, nuclearNorm_eq_re_trace_sqrt]
    have hS0 : (0 : Matrix n n 𝕜) ≤ CFC.sqrt (Mᴴ * M) := CFC.sqrt_nonneg _
    obtain ⟨S, hSdef⟩ : ∃ S, S = CFC.sqrt (Mᴴ * M) := ⟨_, rfl⟩
    rw [← hSdef] at hUS htr hS0
    have hT : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
    have hTT : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS0
    have e1 : frobInner (CFC.sqrt S) (U * CFC.sqrt S) = RCLike.re M.trace := by
      rw [frobInner_eq_re_trace, hT.eq, Matrix.trace_mul_comm, Matrix.mul_assoc, hTT, hUS]
    have e2 : frobNorm (CFC.sqrt S) ^ 2 = RCLike.re S.trace := by
      rw [frobNorm_sq_eq_re_trace, hT.eq, hTT]
    have hZ : frobNorm (CFC.sqrt S - U * CFC.sqrt S) ^ 2 = 0 := by
      rw [frobNorm_sub_sq, hU.frobNorm_mul_left, e1, e2, htr]
      ring
    have hTU : CFC.sqrt S = U * CFC.sqrt S :=
      sub_eq_zero.mp (frobNorm_eq_zero_iff.mp ((pow_eq_zero_iff two_ne_zero).mp hZ))
    have hMS : M = S := by
      rw [← hUS]
      nth_rw 1 [← hTT]
      rw [← Matrix.mul_assoc, ← hTU, hTT]
    rw [hMS]
    exact Matrix.nonneg_iff_posSemidef.mp hS0
  · rw [h.nuclearNorm_eq_re_trace]
    have hstar : star M.trace = M.trace := by
      rw [← Matrix.trace_conjTranspose, h.isHermitian.eq]
    exact (RCLike.conj_eq_iff_re.mp hstar).symm

end NLAlib
