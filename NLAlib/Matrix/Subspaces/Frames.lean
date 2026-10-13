/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Norms.Spectral

/-!
# Orthonormal frames of a subspace

Matrices with orthonormal columns as bases of subspaces: two frames of the same subspace differ
by a unitary factor, two matrices with the same Gram matrix differ by an isometry, a unitary
matrix is determined by its first block of columns up to a unitary factor on the complement, and
the set of frames is compact.

## Main results

* `NLAlib.HasOrthonormalCols.conjTranspose_mul_of_range_le`,
  `NLAlib.HasOrthonormalCols.mul_conjTranspose_mul_of_range_le`: change of frame.
* `NLAlib.conjTranspose_mul_self_eq_iff_exists_mul`: equal Gram matrices.
* `NLAlib.isCompact_setOf_hasOrthonormalCols`: compactness of the set of frames.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-! ### Change of frame -/

/-- If the column space of `V` lies in that of the frame `U`, then `V = U * (Uᴴ * V)`. -/
theorem HasOrthonormalCols.mul_conjTranspose_mul_of_range_le [DecidableEq p] {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) {V : Matrix n q 𝕜}
    (h : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) : U * (Uᴴ * V) = V := by
  rw [← Matrix.mul_assoc, ← hU.rangeProjector_eq]
  exact rangeProjector_mul_eq_self_iff.mpr h

/-- If the column space of the frame `V` lies in that of the frame `U`, the transition matrix
`Uᴴ * V` has orthonormal columns. -/
theorem HasOrthonormalCols.conjTranspose_mul_of_range_le [DecidableEq p] [DecidableEq q]
    {U : Matrix n p 𝕜} (hU : HasOrthonormalCols U) {V : Matrix n q 𝕜}
    (hV : HasOrthonormalCols V)
    (h : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    HasOrthonormalCols (Uᴴ * V) := by
  rw [HasOrthonormalCols, ← hU.conjTranspose_mul_mul, hU.mul_conjTranspose_mul_of_range_le h]
  exact hV

/-- **Two frames of the same subspace differ by a unitary factor.**
[HornJohnson2013, Theorem 2.1.4 context].
Port of `NLAlib.exists_orthogonal_frame_transition`, there over `ℝ`. -/
theorem HasOrthonormalCols.exists_mul_eq_of_range_eq [DecidableEq p] {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (h : LinearMap.range U.mulVecLin = LinearMap.range V.mulVecLin) :
    ∃ T : Matrix p p 𝕜, HasOrthonormalCols T ∧ U * T = V :=
  ⟨Uᴴ * V, hU.conjTranspose_mul_of_range_le hV h.ge, hU.mul_conjTranspose_mul_of_range_le h.ge⟩

/-- There are orthonormal frames with `card p` columns in a space of dimension at least
`card p`. Port of `NLAlib.exists_hasOrthonormalCols_of_card_le`. -/
theorem exists_hasOrthonormalCols_of_card_le [DecidableEq p] (𝕜 : Type*) [RCLike 𝕜]
    (h : Fintype.card p ≤ Fintype.card n) : ∃ J : Matrix n p 𝕜, HasOrthonormalCols J := by
  classical
  obtain ⟨e⟩ : Nonempty (p ↪ n) := Function.Embedding.nonempty_of_card_le h
  exact ⟨(1 : Matrix n n 𝕜).submatrix (Equiv.refl n) e,
    hasOrthonormalCols_one.submatrix (Equiv.refl n) e.injective⟩

/-! ### Equal Gram matrices -/

/-- Matrices with the same Gram matrix have the same action on norms.
Port of `NLAlib.norm_toEuclideanLin_apply_eq_of_gram_eq`. -/
theorem norm_mulVec_eq_of_conjTranspose_mul_self_eq {A : Matrix m n 𝕜} {B : Matrix p n 𝕜}
    (h : Aᴴ * A = Bᴴ * B) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ = ‖WithLp.toLp 2 (B *ᵥ x)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct,
    EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct, Matrix.star_mulVec, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

/-- Two linear maps into a finite-dimensional inner product space with the same action on norms
differ by a linear isometry of the target. -/
private theorem exists_linearIsometry_apply_eq {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] (f g : E →ₗ[𝕜] F)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : ∃ u : F →ₗᵢ[𝕜] F, ∀ x, u (g x) = f x := by
  have hker : LinearMap.ker g ≤ LinearMap.ker f := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← norm_eq_zero, h x, hx, norm_zero]
  let L₁ : LinearMap.range g →ₗ[𝕜] F :=
    ((LinearMap.ker g).liftQ f hker).comp g.quotKerEquivRange.symm.toLinearMap
  have happly (x : E) : L₁ ⟨g x, LinearMap.mem_range_self g x⟩ = f x := by
    change (LinearMap.ker g).liftQ f hker (g.quotKerEquivRange.symm ⟨g x, _⟩) = f x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range g →ₗᵢ[𝕜] F :=
    { toLinearMap := L₁
      norm_map' := by
        rintro ⟨_, x, rfl⟩
        rw [happly]
        exact h x }
  exact ⟨L.extend, fun x =>
    (L.extend_apply ⟨g x, LinearMap.mem_range_self g x⟩).trans (happly x)⟩

omit [Fintype n] in
/-- **Equal Gram matrices.** `Aᴴ * A = Bᴴ * B` exactly when `A = W * B` for some `W` with
orthonormal columns, provided `A` has at least as many rows as `B`.
[HornJohnson2013, Theorem 7.3.11].
Port of `NLAlib.gram_eq_iff_exists_isometry_mul_eq`, there over `ℝ`.
Result: gram-isometry -/
theorem conjTranspose_mul_self_eq_iff_exists_mul [Finite n] [DecidableEq p] {A : Matrix m n 𝕜}
    {B : Matrix p n 𝕜} (hcard : Fintype.card p ≤ Fintype.card m) :
    Aᴴ * A = Bᴴ * B ↔ ∃ W : Matrix m p 𝕜, HasOrthonormalCols W ∧ A = W * B := by
  classical
  have := Fintype.ofFinite n
  constructor
  · intro h
    obtain ⟨J, hJ⟩ := exists_hasOrthonormalCols_of_card_le (n := m) (p := p) 𝕜 hcard
    have hJB : Aᴴ * A = (J * B)ᴴ * (J * B) := by rw [hJ.conjTranspose_mul_mul, h]
    let toE : (m → 𝕜) →ₗ[𝕜] EuclideanSpace 𝕜 m :=
      (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap
    obtain ⟨u, hu⟩ := exists_linearIsometry_apply_eq (toE ∘ₗ A.mulVecLin)
      (toE ∘ₗ (J * B).mulVecLin) (norm_mulVec_eq_of_conjTranspose_mul_self_eq hJB)
    let W₀ : Matrix m m 𝕜 :=
      (Matrix.toEuclideanCLM (n := m) (𝕜 := 𝕜)).symm u.toContinuousLinearMap
    have hW₀ : HasOrthonormalCols W₀ := by
      rw [HasOrthonormalCols, ← Matrix.star_eq_conjTranspose, ← map_star, ← map_mul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
        (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp u.norm_map, map_one]
    refine ⟨W₀ * J, hW₀.mul hJ, ?_⟩
    rw [Matrix.mul_assoc, Matrix.ext_iff_mulVec]
    intro x
    refine WithLp.toLp_injective 2 ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.toEuclideanCLM_toLp, StarAlgEquiv.apply_symm_apply]
    exact (hu x).symm
  · rintro ⟨W, hW, rfl⟩
    rw [hW.conjTranspose_mul_mul]

/-! ### Completion -/

/-- Two unitary matrices with the same first block of columns differ by a unitary factor on the
remaining columns. [HornJohnson2013, Theorem 2.7.1, completion step].
Port of `NLAlib.exists_unitary_right_block_of_first_columns_eq`. -/
theorem HasOrthonormalCols.exists_mul_fromBlocks_one_eq [DecidableEq p] [DecidableEq q]
    {X Y : Matrix (p ⊕ q) (p ⊕ q) 𝕜} (hX : HasOrthonormalCols X) (hY : HasOrthonormalCols Y)
    (h : X.submatrix id Sum.inl = Y.submatrix id Sum.inl) :
    ∃ W : Matrix q q 𝕜, HasOrthonormalCols W ∧ X * Matrix.fromBlocks 1 0 0 W = Y := by
  have hcard : Fintype.card p + Fintype.card q = Fintype.card (p ⊕ q) := Fintype.card_sum.symm
  obtain ⟨X₁, X₂, rfl⟩ : ∃ X₁ X₂, X = Matrix.fromCols X₁ X₂ :=
    ⟨_, _, (Matrix.fromCols_toCols X).symm⟩
  obtain ⟨Y₁, Y₂, rfl⟩ : ∃ Y₁ Y₂, Y = Matrix.fromCols Y₁ Y₂ :=
    ⟨_, _, (Matrix.fromCols_toCols Y).symm⟩
  obtain rfl : X₁ = Y₁ := Matrix.ext fun i j => congrFun (congrFun h i) j
  have hY₂ : HasOrthonormalCols Y₂ := (hasOrthonormalCols_fromCols_iff.mp hY).2.1
  have hXY : X₂ * X₂ᴴ = Y₂ * Y₂ᴴ :=
    add_left_cancel ((hX.mul_conjTranspose_add_mul_conjTranspose hcard).trans
      (hY.mul_conjTranspose_add_mul_conjTranspose hcard).symm)
  refine ⟨X₂ᴴ * Y₂, ?_, ?_⟩
  · rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc X₂, hXY, Matrix.mul_assoc,
      hY₂.conjTranspose_mul_self, Matrix.mul_one, hY₂.conjTranspose_mul_self]
  · rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, add_zero,
      Matrix.mul_zero, zero_add, ← Matrix.mul_assoc, hXY, Matrix.mul_assoc,
      hY₂.conjTranspose_mul_self, Matrix.mul_one]

omit [Fintype p] [Fintype q] in
/-- A block-diagonal matrix of two frames is a frame.
Port of `NLAlib.HasOrthonormalCols.fromBlocks_diagonal`. -/
theorem HasOrthonormalCols.fromBlocks_diagonal [DecidableEq p] [DecidableEq q]
    {A : Matrix m p 𝕜} {B : Matrix n q 𝕜} (hA : HasOrthonormalCols A)
    (hB : HasOrthonormalCols B) : HasOrthonormalCols (Matrix.fromBlocks A 0 0 B) := by
  rw [HasOrthonormalCols, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [hA.conjTranspose_mul_self, hB.conjTranspose_mul_self, Matrix.conjTranspose_zero,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.fromBlocks_one]

/-! ### Topology -/

omit [Fintype p] in
/-- The set of matrices with orthonormal columns is closed. Port of `NLAlib.isClosed_stiefel`. -/
theorem isClosed_setOf_hasOrthonormalCols [DecidableEq p] :
    IsClosed {Q : Matrix n p 𝕜 | HasOrthonormalCols Q} :=
  isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const

omit [Fintype p] in
/-- **The set of matrices with orthonormal columns (the Stiefel manifold) is compact.**
Port of `NLAlib.stiefelCompactSpace`, there for `Fin` indices over `ℝ`. -/
theorem isCompact_setOf_hasOrthonormalCols [DecidableEq p] :
    IsCompact {Q : Matrix n p 𝕜 | HasOrthonormalCols Q} := by
  have hbox := isCompact_univ_pi fun _ : n => isCompact_univ_pi fun _ : p =>
    isCompact_closedBall (0 : 𝕜) 1
  refine hbox.of_isClosed_subset isClosed_setOf_hasOrthonormalCols
    fun (Q : Matrix n p 𝕜) hQ i _ j _ => mem_closedBall_zero_iff.mpr ?_
  exact (PiLp.norm_apply_le (WithLp.toLp 2 (Q.col j)) i).trans_eq
    ((hasOrthonormalCols_iff_orthonormal.mp hQ).1 j)

/-- A continuous real function on matrices attains its minimum over the frames, when there is at
least one. Port of `NLAlib.exists_orthogonal_isMinOn_of_continuous`. -/
theorem exists_isMinOn_setOf_hasOrthonormalCols [DecidableEq p] {f : Matrix n p 𝕜 → ℝ}
    (hf : Continuous f) (h : Fintype.card p ≤ Fintype.card n) :
    ∃ Q : Matrix n p 𝕜, HasOrthonormalCols Q ∧
      IsMinOn f {Q : Matrix n p 𝕜 | HasOrthonormalCols Q} Q :=
  isCompact_setOf_hasOrthonormalCols.exists_isMinOn (exists_hasOrthonormalCols_of_card_le 𝕜 h)
    hf.continuousOn

end NLAlib
