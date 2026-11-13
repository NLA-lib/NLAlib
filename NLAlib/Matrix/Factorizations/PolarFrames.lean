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

These are the Matrix-layer facts the Haar frame law needs. They stay in their own
file: `Procrustes.lean` imports it, and it imports both `Polar.lean` and `OrthonormalBasis.lean`.

## Main results

* `NLAlib.HasOrthonormalCols.polarFactor_mul_right`: the polar factor of $\mathbf{A}\mathbf{V}$ is
  $\mathbf{U}\mathbf{V}$ for a coisometry $\mathbf{V}$, $\mathbf{U}$ the polar factor of
  $\mathbf{A}$.
* `NLAlib.rangeProjector_mul_polarFactor`: $\mathbf{A}\mathbf{U}$ and $\mathbf{A}\mathbf{B}$ have
  the same range, $\mathbf{U}$ the polar factor of $\mathbf{B}$.
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

/-- The polar factor commutes with a coisometry on the right: for $\mathbf{V}$ with
orthonormal rows ($\mathbf{V}\mathbf{V}^{\mathsf{H}} = \mathbf{I}$; in particular any unitary), the
polar factor of $\mathbf{A}\mathbf{V}$ is $\mathbf{U}\mathbf{V}$, with $\mathbf{U}$ the polar
factor of $\mathbf{A}$. The right-hand twin of `HasOrthonormalCols.polarFactor_mul_left`. -/
theorem HasOrthonormalCols.polarFactor_mul_right [DecidableEq n] [DecidableEq q] {V : Matrix n q 𝕜}
    (hV : HasOrthonormalCols Vᴴ) (A : Matrix m n 𝕜) :
    polarFactor (A * V) = polarFactor A * V := by
  classical
  have h := HasOrthonormalCols.polarFactor_mul_left hV Aᴴ
  rw [polarFactor_conjTranspose, ← Matrix.conjTranspose_mul, polarFactor_conjTranspose] at h
  have h' := congrArg Matrix.conjTranspose h
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at h'

/-- Right multiplication by a polar factor keeps the range: for $\mathbf{U}$ the polar factor
of $\mathbf{B}$, $\mathbf{P}_{\mathbf{A}\mathbf{U}} = \mathbf{P}_{\mathbf{A}\mathbf{B}}$, for every
shape and rank. The column spaces agree because
$\mathbf{U} = \mathbf{B}\bigl((\mathbf{B}^{\mathsf{H}}\mathbf{B})^{1/2}\bigr)^{+}$ and
$\mathbf{B} = \mathbf{U}(\mathbf{B}^{\mathsf{H}}\mathbf{B})^{1/2}$. -/
theorem rangeProjector_mul_polarFactor [DecidableEq n] (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    rangeProjector (A * polarFactor B) = rangeProjector (A * B) := by
  rw [rangeProjector_inj]
  refine le_antisymm (range_le_iff_exists_mul.mpr ⟨pinv (CFC.sqrt (Bᴴ * B)), ?_⟩)
    (range_le_iff_exists_mul.mpr ⟨CFC.sqrt (Bᴴ * B), ?_⟩)
  · rw [polarFactor, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, polarFactor_mul_sqrt]

/-- The polar factor $\mathbf{U}$ of $\mathbf{B}$ has the range of $\mathbf{B}$:
$\mathbf{P}_{\mathbf{U}} = \mathbf{P}_{\mathbf{B}}$ (the case $\mathbf{A} = \mathbf{I}$ of
`rangeProjector_mul_polarFactor`). -/
theorem rangeProjector_polarFactor [DecidableEq n] (B : Matrix m n 𝕜) :
    rangeProjector (polarFactor B) = rangeProjector B := by
  classical
  simpa only [Matrix.one_mul] using rangeProjector_mul_polarFactor (1 : Matrix m m 𝕜) B

/-- The polar factor has spectral norm at most one: it is a partial isometry, with norm $1$
unless the matrix is $\mathbf{0}$. -/
theorem specNorm_polarFactor_le_one [DecidableEq n] (A : Matrix m n 𝕜) :
    specNorm (polarFactor A) ≤ 1 := by
  have h : specNorm (polarFactor A) ^ 2 ≤ 1 ^ 2 := by
    rw [← specNorm_conjTranspose_mul_self, conjTranspose_polarFactor_mul_self, one_pow]
    exact (isStarProjection_rangeProjector Aᴴ).specNorm_le_one
  exact (pow_le_pow_iff_left₀ (specNorm_nonneg _) zero_le_one two_ne_zero).mp h

/-- The polar factor of a column is the normalised column: the polar factor of the
one-column matrix $\mathbf{x}$ is the one-column matrix $\|\mathbf{x}\|^{-1}\mathbf{x}$. True at
$\mathbf{x} = \mathbf{0}$, where both sides are $\mathbf{0}$ ($0^{-1} = 0$). -/
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

/-- Unitaries act transitively on frames: two matrices $\mathbf{X}$, $\mathbf{Y}$ with
orthonormal columns and the same column index differ by a unitary factor on the left,
$\mathbf{U}\mathbf{X} = \mathbf{Y}$. Used by the two-sided Procrustes problem
(`NLAlib.isLeast_frobNorm_sub_mul_mul_sq`) and the Haar frame law. -/
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

/-- A matrix fixed by every unitary conjugation is scalar: if
$\mathbf{U}\mathbf{M}\mathbf{U}^{\mathsf{H}} = \mathbf{M}$ for every unitary $\mathbf{U}$, then
$\mathbf{M} = (\operatorname{tr} \mathbf{M} / \lvert n \rvert) \mathbf{I}$. For empty $n$ both
sides are $\mathbf{0}$. Unlike Mathlib's
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

private theorem circlePoint_mul_star (s : ℝ) (hs : |s| ≤ 1) :
    ((s : ℂ) + Complex.I * Real.sqrt (1 - s ^ 2)) *
      star ((s : ℂ) + Complex.I * Real.sqrt (1 - s ^ 2)) = 1 := by
  have ht : (Real.sqrt (1 - s ^ 2)) ^ 2 = 1 - s ^ 2 :=
    Real.sq_sqrt (by
      have hs' := abs_le.mp hs
      nlinarith [mul_nonneg (sub_nonneg.mpr hs'.2) (by linarith : 0 ≤ 1 + s)])
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Every square complex contraction is the arithmetic mean of two unitary matrices.
For each singular value $s$, the diagonal factors use the conjugate unit phases
$s\pm i\sqrt{1-s^2}$. [Tropp2022, §12]. -/
theorem exists_eq_smul_add_of_specNorm_le_one [DecidableEq n] (A : Matrix n n ℂ)
    (hA : specNorm A ≤ 1) :
    ∃ U V : Matrix n n ℂ, HasOrthonormalCols U ∧ HasOrthonormalCols V ∧
      A = (2 : ℂ)⁻¹ • (U + V) := by
  obtain ⟨L, R, h⟩ := exists_isSVD A A.rank_le_card_width le_rfl le_rfl
  let s (i : Fin (Fintype.card n)) := singularValues A i
  let z (i : Fin (Fintype.card n)) : ℂ := (s i : ℂ) + Complex.I * √(1 - s i ^ 2)
  have hz (i) : z i * star (z i) = 1 := circlePoint_mul_star (s i) (by
    rw [abs_of_nonneg (singularValues_nonneg A i)]
    exact (singularValues_le_specNorm A i).trans hA)
  have hd : HasOrthonormalCols (Matrix.diagonal z) := by
    rw [HasOrthonormalCols, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    exact (mul_comm _ _).trans (hz i)
  have hr : HasOrthonormalCols Rᴴ := by
    rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose]
    exact h.hasOrthonormalCols_right.mul_conjTranspose_self_of_card_eq (by simp)
  refine ⟨L * Matrix.diagonal z * Rᴴ, L * (Matrix.diagonal z)ᴴ * Rᴴ,
    (h.hasOrthonormalCols_left.mul hd).mul hr,
    (h.hasOrthonormalCols_left.mul hd.conjTranspose).mul hr,
    ?_⟩
  rw [← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.smul_mul, ← Matrix.mul_smul]
  rw [h.eq]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst j
    simp [z, s]
    ring
  · simp [Matrix.diagonal, hij, Ne.symm hij]

end NLAlib
