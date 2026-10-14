/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.ComplementaryProjector
public import NLAlib.Matrix.Basic.Projector

/-!
# Orthonormal bases of column spaces and orthonormal completion

Every column space has an orthonormal basis, given as a matrix `Q` with `HasOrthonormalCols Q`,
and every matrix with orthonormal columns extends to a larger one. The new columns are indexed by
an arbitrary type, constrained by a cardinality hypothesis.

## Main results

* `NLAlib.exists_hasOrthonormalCols_range_eq`: an orthonormal basis of a column space.
* `NLAlib.exists_hasOrthonormalCols_range_le`: orthonormal columns whose span contains a column
  space.
* `NLAlib.HasOrthonormalCols.exists_fromCols_of_card_le`,
  `NLAlib.HasOrthonormalCols.exists_fromCols`: orthonormal completion.
* `IsStarProjection.exists_hasOrthonormalCols_mul_conjTranspose_eq`: every star projection is
  `Q * Qᴴ` for a `Q` with orthonormal columns.
* `NLAlib.HasOrthonormalCols.mul_conjTranspose_add_mul_conjTranspose`: the two blocks of a
  completed matrix give complementary projectors.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}

/-- The column space of `A` as a subspace of `EuclideanSpace 𝕜 m`. -/
private noncomputable abbrev euclideanRange [Fintype n] (A : Matrix m n 𝕜) :
    Submodule 𝕜 (EuclideanSpace 𝕜 m) :=
  (LinearMap.range A.mulVecLin).map (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap

/-- **Orthonormal basis of a column space.** For any column index type `p` with as many elements
as the rank of `A`, there is a `Q` with orthonormal columns indexed by `p` and the same column
space as `A`. Port of `NLAlib.hasOrthonormalCols_orthonormalBasisMatrix` and
`NLAlib.range_orthonormalBasisMatrix`, there a definition indexed by `Fin (finrank S)`. -/
theorem exists_hasOrthonormalCols_range_eq [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n 𝕜) (h : Fintype.card p = A.rank) :
    ∃ Q : Matrix m p 𝕜, HasOrthonormalCols Q ∧
      LinearMap.range Q.mulVecLin = LinearMap.range A.mulVecLin := by
  classical
  have hS : Module.finrank 𝕜 (euclideanRange A) = Fintype.card p := by
    rw [h]
    exact LinearEquiv.finrank_map_eq _ _
  let b : OrthonormalBasis p 𝕜 (euclideanRange A) :=
    (stdOrthonormalBasis 𝕜 (euclideanRange A)).reindex
      (Fintype.equivOfCardEq (by rw [Fintype.card_fin, hS]))
  refine ⟨Matrix.of fun i j => (b j : EuclideanSpace 𝕜 m).ofLp i, ?_, ?_⟩
  · rw [hasOrthonormalCols_iff_orthonormal]
    exact b.orthonormal.comp_linearIsometry (euclideanRange A).subtypeₗᵢ
  · have hcols : Set.range (Matrix.of fun i j => (b j : EuclideanSpace 𝕜 m).ofLp i).col =
        ⇑((WithLp.linearEquiv 2 𝕜 (m → 𝕜)).toLinearMap ∘ₗ (euclideanRange A).subtype) ''
          Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [Matrix.range_mulVecLin, hcols, ← Submodule.map_span, ← b.coe_toBasis,
      Module.Basis.span_eq, Submodule.map_comp, Submodule.map_subtype_top, ← Submodule.map_comp,
      LinearEquiv.comp_symm, Submodule.map_id]

/-- **Orthonormal completion** by any number of columns that fits. A matrix `Q` with orthonormal
columns indexed by `n` extends, by columns indexed by any type `p` with
`card n + card p ≤ card m`, to a matrix `fromCols Q Q'` with orthonormal columns.
`NLAlib.HasOrthonormalCols.exists_fromCols` is the case of equality, where the completed matrix is
unitary up to relabelling. -/
theorem HasOrthonormalCols.exists_fromCols_of_card_le [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (h : Fintype.card n + Fintype.card p ≤ Fintype.card m) :
    ∃ Q' : Matrix m p 𝕜, HasOrthonormalCols (Matrix.fromCols Q Q') := by
  classical
  have hrank : Fintype.card (Fin (Fintype.card m - Fintype.card n)) =
      (1 - rangeProjector Q).rank := by
    have hadd := rank_one_sub_rangeProjector_add_rank Q
    rw [hQ.rank_eq] at hadd
    rw [Fintype.card_fin]
    omega
  obtain ⟨Q₀, hQ₀, hrange⟩ := exists_hasOrthonormalCols_range_eq (1 - rangeProjector Q) hrank
  have h0 : Qᴴ * Q₀ = 0 := by
    have hfix : (1 - rangeProjector Q) * Q₀ = Q₀ :=
      (isStarProjection_one_sub_rangeProjector Q).mul_eq_self_iff.mpr hrange.le
    rw [← hfix, ← Matrix.mul_assoc, conjTranspose_mul_one_sub_rangeProjector, Matrix.zero_mul]
  obtain ⟨g⟩ : Nonempty (p ↪ Fin (Fintype.card m - Fintype.card n)) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin]; omega)
  refine ⟨Q₀.submatrix (Equiv.refl m) g, hasOrthonormalCols_fromCols_iff.mpr
    ⟨hQ, hQ₀.submatrix (Equiv.refl m) g.injective, ?_⟩⟩
  ext i j
  exact congrFun (congrFun h0 i) (g j)

/-- For any column index type `p` with at least `rank A` and at most `card m` elements, there is a
`Q` with orthonormal columns indexed by `p` whose column space contains that of `A`. -/
theorem exists_hasOrthonormalCols_range_le [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n 𝕜) (h : A.rank ≤ Fintype.card p) (hp : Fintype.card p ≤ Fintype.card m) :
    ∃ Q : Matrix m p 𝕜, HasOrthonormalCols Q ∧
      LinearMap.range A.mulVecLin ≤ LinearMap.range Q.mulVecLin := by
  classical
  obtain ⟨Q₁, hQ₁, hrange⟩ :=
    exists_hasOrthonormalCols_range_eq (p := Fin A.rank) A (Fintype.card_fin _)
  obtain ⟨Q₂, hQ₂⟩ := hQ₁.exists_fromCols_of_card_le (p := Fin (Fintype.card p - A.rank))
    (by rw [Fintype.card_fin, Fintype.card_fin]; omega)
  obtain ⟨e⟩ : Nonempty (p ≃ Fin A.rank ⊕ Fin (Fintype.card p - A.rank)) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; omega)⟩
  refine ⟨(Matrix.fromCols Q₁ Q₂).submatrix (Equiv.refl m) e,
    hQ₂.submatrix (Equiv.refl m) e.injective, ?_⟩
  rw [← hrange, Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  refine Submodule.span_mono ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨e.symm (Sum.inl k), funext fun i => ?_⟩
  simp only [Equiv.coe_refl, Matrix.col_apply, Matrix.submatrix_apply, id_eq,
    Equiv.apply_symm_apply, Matrix.fromCols_apply_inl]

/-- Every star projection is `Q * Qᴴ` for a `Q` with orthonormal columns, indexed by any type
with `rank P` elements. -/
theorem _root_.IsStarProjection.exists_hasOrthonormalCols_mul_conjTranspose_eq [Fintype m]
    [Fintype p] [DecidableEq p] {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (h : Fintype.card p = P.rank) :
    ∃ Q : Matrix m p 𝕜, HasOrthonormalCols Q ∧ Q * Qᴴ = P := by
  obtain ⟨Q, hQ, hrange⟩ := exists_hasOrthonormalCols_range_eq P h
  exact ⟨Q, hQ, by rw [← hQ.rangeProjector_eq, rangeProjector_inj.mpr hrange,
    hP.rangeProjector_eq]⟩

/-- **Orthonormal completion.** A matrix `Q` with orthonormal columns extends, by columns indexed
by any type `p` of the complementary size, to a matrix `fromCols Q Q'` with orthonormal columns.
That matrix has as many rows as columns, so it is unitary up to relabelling:
`HasOrthonormalCols.mul_conjTranspose_self_of_card_eq` gives `Q * Qᴴ + Q' * Q'ᴴ = 1`.
Port of `NLAlib.exists_unitary_complement`. -/
theorem HasOrthonormalCols.exists_fromCols [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    [DecidableEq p] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (h : Fintype.card n + Fintype.card p = Fintype.card m) :
    ∃ Q' : Matrix m p 𝕜, HasOrthonormalCols (Matrix.fromCols Q Q') :=
  hQ.exists_fromCols_of_card_le h.le

/-- If `fromCols Q Q'` has orthonormal columns and is square up to relabelling, the two
projectors are complementary: `Q * Qᴴ + Q' * Q'ᴴ = 1`. -/
theorem HasOrthonormalCols.mul_conjTranspose_add_mul_conjTranspose [Fintype m] [Fintype n]
    [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] {Q : Matrix m n 𝕜}
    {Q' : Matrix m p 𝕜} (hQ : HasOrthonormalCols (Matrix.fromCols Q Q'))
    (h : Fintype.card n + Fintype.card p = Fintype.card m) : Q * Qᴴ + Q' * Q'ᴴ = 1 := by
  have h1 := hQ.mul_conjTranspose_self_of_card_eq (by rw [Fintype.card_sum, h])
  rwa [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
    at h1

end NLAlib
