/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Basic.OrthonormalBasis

/-!
# Polar factors and frames under unitary maps

Facts about the polar factor and about matrices with orthonormal columns that the Haar frame law
(`NLAlib/RandomMatrix/Haar/`) is built on: the polar factor commutes with a coisometry on the
right, has the range of its matrix and spectral norm at most one, and normalises a column; two
frames with the same number of columns differ by a unitary on the left; and a matrix that every
unitary conjugation fixes is a multiple of the identity.

This file collects the Matrix-layer additions of `docs/design/RandomMatrix-R5.md` §1 while they are
proved. At the wrap-up, the polar-factor statements join `NLAlib/Matrix/Factorizations/Polar.lean`
and the frame statements join `NLAlib/Matrix/Basic/OrthonormalBasis.lean`.

## Main results

* `NLAlib.polarFactor_mul_right`: `polarFactor (A V) = polarFactor A * V` for a coisometry `V`.
* `NLAlib.rangeProjector_mul_polarFactor`: `range (A * polarFactor B) = range (A * B)`.
* `NLAlib.specNorm_polarFactor_le_one`.
* `NLAlib.polarFactor_replicateCol`: the polar factor of a column is the normalised column.
* `NLAlib.HasOrthonormalCols.exists_mul_eq`: unitaries act transitively on frames.
* `NLAlib.eq_smul_one_of_forall_mul_mul_conjTranspose_eq`: a matrix commuting with every unitary
  is scalar.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n q : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype q]

/-! ### The polar factor -/

/-- **The polar factor commutes with a coisometry on the right**: for `V` with orthonormal rows
(`V Vᴴ = 1`; in particular any unitary), `polarFactor (A V) = polarFactor A * V`. The right-hand
twin of `polarFactor_mul_left`. -/
theorem polarFactor_mul_right [DecidableEq n] [DecidableEq q] {V : Matrix n q 𝕜}
    (hV : HasOrthonormalCols Vᴴ) (A : Matrix m n 𝕜) :
    polarFactor (A * V) = polarFactor A * V := by
  classical
  have h := polarFactor_mul_left hV Aᴴ
  rw [polarFactor_conjTranspose, ← Matrix.conjTranspose_mul, polarFactor_conjTranspose] at h
  have h' := congrArg Matrix.conjTranspose h
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at h'

/-- **Right multiplication by a polar factor keeps the range**: the range projector of
`A * polarFactor B` is that of `A * B`, for every shape and rank. The column spaces agree because
`polarFactor B = B * pinv (CFC.sqrt (Bᴴ * B))` and `B = polarFactor B * CFC.sqrt (Bᴴ * B)`. -/
theorem rangeProjector_mul_polarFactor [DecidableEq n] (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    rangeProjector (A * polarFactor B) = rangeProjector (A * B) := by
  rw [rangeProjector_inj]
  refine le_antisymm (range_mulVecLin_le_iff_exists_mul.mpr ⟨pinv (CFC.sqrt (Bᴴ * B)), ?_⟩)
    (range_mulVecLin_le_iff_exists_mul.mpr ⟨CFC.sqrt (Bᴴ * B), ?_⟩)
  · rw [polarFactor, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, polarFactor_mul_sqrt]

/-- The polar factor of `B` has the range of `B`: `rangeProjector (polarFactor B) =
rangeProjector B` (the case `A = 1` of `rangeProjector_mul_polarFactor`). -/
theorem rangeProjector_polarFactor [DecidableEq n] (B : Matrix m n 𝕜) :
    rangeProjector (polarFactor B) = rangeProjector B := by
  classical
  simpa only [Matrix.one_mul] using rangeProjector_mul_polarFactor (1 : Matrix m m 𝕜) B

/-- **The polar factor has spectral norm at most one**: it is a partial isometry, with norm `1`
unless the matrix is `0`. -/
theorem specNorm_polarFactor_le_one [DecidableEq n] (A : Matrix m n 𝕜) :
    specNorm (polarFactor A) ≤ 1 := by
  have h : specNorm (polarFactor A) ^ 2 ≤ 1 ^ 2 := by
    rw [← specNorm_conjTranspose_mul_self, conjTranspose_polarFactor_mul_self, one_pow]
    exact (isStarProjection_rangeProjector Aᴴ).specNorm_le_one
  exact (pow_le_pow_iff_left₀ (specNorm_nonneg _) zero_le_one two_ne_zero).mp h

/-- **The polar factor of a column is the normalised column**: `polarFactor [x] = [x / ‖x‖]`, the
real scalar `‖x‖⁻¹` acting on `x`. True at `x = 0`, where both sides are `0` (`0⁻¹ = 0`). -/
theorem polarFactor_replicateCol (x : m → 𝕜) :
    polarFactor (Matrix.replicateCol Unit x) =
      Matrix.replicateCol Unit ((‖WithLp.toLp 2 x‖⁻¹ : ℝ) • x) := by
  set c : ℝ := ‖WithLp.toLp 2 x‖ with hc
  have hG : (Matrix.replicateCol Unit x)ᴴ * Matrix.replicateCol Unit x =
      ((c : 𝕜) • (1 : Matrix Unit Unit 𝕜)) * ((c : 𝕜) • (1 : Matrix Unit Unit 𝕜)) := by
    ext i j
    rw [Matrix.conjTranspose_replicateCol, Matrix.replicateRow_mul_replicateCol_apply,
      smul_mul_smul_comm, Matrix.one_mul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one, ← sq, hc, ← inner_self_eq_norm_sq_to_K, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hS : CFC.sqrt ((Matrix.replicateCol Unit x)ᴴ * Matrix.replicateCol Unit x) =
      (c : 𝕜) • (1 : Matrix Unit Unit 𝕜) :=
    CFC.sqrt_unique hG.symm
      (Matrix.PosSemidef.one.smul (RCLike.ofReal_nonneg.mpr (norm_nonneg _))).nonneg
  rw [polarFactor, hS, pinv_smul, pinv_of_isUnit isUnit_one, inv_one, Matrix.mul_smul,
    Matrix.mul_one, Matrix.replicateCol_smul, ← RCLike.ofReal_inv]
  exact (RCLike.real_smul_eq_coe_smul _ _).symm

/-! ### Frames under unitary maps -/

/-- **Unitaries act transitively on frames**: two matrices with orthonormal columns and the same
column index differ by a unitary factor on the left. Used by the two-sided Procrustes problem
(`NLAlib.isLeast_frobNorm_sub_mul_mul_sq`) and the Haar frame law
(`docs/design/RandomMatrix-R5.md` §1, addition 5). -/
theorem HasOrthonormalCols.exists_mul_eq [DecidableEq m] {r : Type*} [Finite r] [DecidableEq r]
    {X Y : Matrix m r 𝕜} (hX : HasOrthonormalCols X) (hY : HasOrthonormalCols Y) :
    ∃ U : Matrix m m 𝕜, HasOrthonormalCols U ∧ U * X = Y := by
  cases nonempty_fintype r
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hX.card_le
  have hcard : Fintype.card r + Fintype.card (Fin d) = Fintype.card m := by
    rw [Fintype.card_fin]
    exact hd.symm
  obtain ⟨X', hX'⟩ := hX.exists_fromCols (p := Fin d) hcard
  obtain ⟨Y', hY'⟩ := hY.exists_fromCols (p := Fin d) hcard
  have hc : Fintype.card m = Fintype.card (r ⊕ Fin d) := by
    rw [Fintype.card_sum]
    exact hcard.symm
  refine ⟨Matrix.fromCols Y Y' * (Matrix.fromCols X X')ᴴ,
    hY'.mul (hX'.conjTranspose_of_card_eq hc), ?_⟩
  have h1 : Matrix.fromCols Y Y' * (Matrix.fromCols X X')ᴴ * Matrix.fromCols X X' =
      Matrix.fromCols Y Y' := by
    rw [Matrix.mul_assoc, hX'.conjTranspose_mul_self, Matrix.mul_one]
  rw [Matrix.mul_fromCols] at h1
  exact (Matrix.fromCols_inj.eq_iff.mp h1).1

/-- **A matrix fixed by every unitary conjugation is scalar**: if `U M Uᴴ = M` for every unitary
`U`, then `M = (tr M / card n) • 1`. For empty `n` both sides are `0`. Unlike Mathlib's
`Matrix.mem_range_scalar_of_commute_single`, the hypothesis quantifies over unitaries only
(signed permutation matrices suffice). -/
theorem eq_smul_one_of_forall_mul_mul_conjTranspose_eq [DecidableEq n] {M : Matrix n n 𝕜}
    (h : ∀ U : Matrix n n 𝕜, HasOrthonormalCols U → U * M * Uᴴ = M) :
    M = (M.trace / Fintype.card n) • (1 : Matrix n n 𝕜) := by
  -- Diagonal sign changes kill the off-diagonal entries.
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    let d : n → 𝕜 := fun l => if l = i then -1 else 1
    have hd : HasOrthonormalCols (Matrix.diagonal d) := by
      rw [hasOrthonormalCols_iff, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext l
      by_cases hl : l = i <;> simp [d, hl]
    have hij' := congrFun (congrFun (h _ hd) i) j
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij'
    simp only [d, Pi.star_apply, if_pos rfl, if_neg (Ne.symm hij), star_one, mul_one] at hij'
    linear_combination (-1 / 2 : 𝕜) * hij'
  -- Transpositions equate the diagonal entries.
  have hdiag : ∀ i j, M i i = M j j := by
    intro i j
    let σ := Equiv.swap i j
    have hU : HasOrthonormalCols ((1 : Matrix n n 𝕜).submatrix (Equiv.refl n) σ) :=
      hasOrthonormalCols_one.submatrix (Equiv.refl n) σ.injective
    have hE := h _ hU
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one, Matrix.one_submatrix_mul,
      Matrix.mul_submatrix_one, Matrix.submatrix_submatrix] at hE
    have := congrFun (congrFun hE i) i
    simpa [σ] using this.symm
  ext i j
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact (IsEmpty.false i).elim
  have hcard : (Fintype.card n : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨i₀⟩).ne'
  have htr : M.trace = Fintype.card n * M i₀ i₀ := by
    rw [Matrix.trace, Finset.sum_congr rfl fun l _ => show M.diag l = M i₀ i₀ from hdiag l i₀,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Matrix.smul_apply, Matrix.one_apply, htr, mul_div_cancel_left₀ _ hcard]
  by_cases hij : i = j
  · subst hij
    simp [hdiag i i₀]
  · simp [hij, hoff i j hij]

end NLAlib
