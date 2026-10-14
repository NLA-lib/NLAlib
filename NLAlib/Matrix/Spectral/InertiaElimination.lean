/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Inertia
public import NLAlib.Matrix.Factorizations.GaussState

/-!
# Inertia through elimination

The inertia of a Hermitian block matrix is that of a block plus that of its Schur complement
(Haynsworth). Elimination at nonzero pivots writes a Hermitian matrix as `L D Lᴴ` with the
inverses of the pivots on the diagonal of `D`, so by Sylvester's law the signs of the pivots of
`A - x • 1` count the eigenvalues of `A` below `x`, which is what the bisection method uses.

## Main results

* `Matrix.IsHermitian.inertiaPos_fromBlocks`, `Matrix.IsHermitian.inertiaNeg_fromBlocks`:
  Haynsworth additivity.
* `Matrix.PosDef.inertiaPos_fromBlocks_zero`, `Matrix.PosDef.inertiaNeg_fromBlocks_zero`: the
  inertia of a saddle-point matrix.
* `Matrix.IsHermitian.inertiaNeg_sub_smul_one`: the negative index of `A - x • 1` counts the
  eigenvalues below `x`.
* `Matrix.IsHermitian.inertiaNeg_sub_smul_one_eq_card_gaussState_re_neg`: counting eigenvalues by
  pivots.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Congruence to a diagonal matrix -/

/-- The inertia of `L D Lᴴ` for an invertible `L` and a real diagonal `D` is read off `D`. -/
private theorem inertia_mul_diagonal_mul_conjTranspose [DecidableEq n] {L : Matrix n n 𝕜}
    (hL : IsUnit L.det) (d : n → ℝ) :
    inertiaPos (L * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Lᴴ) =
        (Finset.univ.filter fun i => 0 < d i).card ∧
      inertiaNeg (L * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Lᴴ) =
        (Finset.univ.filter fun i => d i < 0).card := by
  have hD : (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (funext fun i => RCLike.conj_ofReal (d i))
  have hL' : IsUnit Lᴴ.det := by rw [Matrix.det_conjTranspose]; exact hL.star
  have h1 := hD.inertiaPos_conjTranspose_mul_mul hL'
  have h2 := hD.inertiaNeg_conjTranspose_mul_mul hL'
  rw [Matrix.conjTranspose_conjTranspose] at h1 h2
  exact ⟨h1.trans (inertiaPos_diagonal d), h2.trans (inertiaNeg_diagonal d)⟩

/-- A Hermitian matrix is `P D Pᴴ` with `P` invertible and `D` real diagonal, both indexed by the
index type of the matrix. -/
private theorem exists_eq_mul_diagonal_mul_conjTranspose [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    ∃ (P : Matrix n n 𝕜) (d : n → ℝ), IsUnit P.det ∧
      A = P * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Pᴴ := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues,
    (Matrix.isUnit_iff_isUnit_det _).mp hA.hasOrthonormalCols_eigenvectorUnitary.isUnit, ?_⟩
  have h := hA.spectral_theorem
  rwa [Unitary.conjStarAlgAut_apply] at h

/-! ### Blocks -/

/-- The inertia of a block diagonal matrix, both indices at once. -/
private theorem inertia_fromBlocks_diagonal {A : Matrix m m 𝕜} {C : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    inertiaPos (Matrix.fromBlocks A 0 0 C) = inertiaPos A + inertiaPos C ∧
      inertiaNeg (Matrix.fromBlocks A 0 0 C) = inertiaNeg A + inertiaNeg C := by
  classical
  obtain ⟨P, a, hP, rfl⟩ := exists_eq_mul_diagonal_mul_conjTranspose hA
  obtain ⟨R, c, hR, rfl⟩ := exists_eq_mul_diagonal_mul_conjTranspose hC
  have hQ : IsUnit (Matrix.fromBlocks P 0 0 R).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    exact hP.mul hR
  have hM : Matrix.fromBlocks (P * Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * Pᴴ) 0 0
      (R * Matrix.diagonal (fun i => ((c i : ℝ) : 𝕜)) * Rᴴ) =
      Matrix.fromBlocks P 0 0 R * Matrix.diagonal (fun i => ((Sum.elim a c i : ℝ) : 𝕜)) *
        (Matrix.fromBlocks P 0 0 R)ᴴ := by
    have hd : (fun i => ((Sum.elim a c i : ℝ) : 𝕜)) =
        Sum.elim (fun i => ((a i : ℝ) : 𝕜)) fun i => ((c i : ℝ) : 𝕜) := by
      funext i
      cases i <;> rfl
    rw [hd, ← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hsum : ∀ (P : ℝ → Prop) [DecidablePred P],
      (Finset.univ.filter fun i : m ⊕ n => P (Sum.elim a c i)).card =
        (Finset.univ.filter fun i => P (a i)).card +
          (Finset.univ.filter fun i => P (c i)).card := by
    intro P _
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    rfl
  rw [hM, (inertia_mul_diagonal_mul_conjTranspose hQ _).1,
    (inertia_mul_diagonal_mul_conjTranspose hQ _).2,
    (inertia_mul_diagonal_mul_conjTranspose hP a).1,
    (inertia_mul_diagonal_mul_conjTranspose hP a).2,
    (inertia_mul_diagonal_mul_conjTranspose hR c).1,
    (inertia_mul_diagonal_mul_conjTranspose hR c).2]
  exact ⟨hsum fun x => 0 < x, hsum fun x => x < 0⟩

/-- The positive index of a block diagonal matrix is the sum of those of the blocks.
Port of `NLAlib.inertiaPos_fromBlocks_zero`. -/
theorem _root_.Matrix.IsHermitian.inertiaPos_fromBlocks_diagonal
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    inertiaPos (Matrix.fromBlocks A 0 0 C) = inertiaPos A + inertiaPos C :=
  (inertia_fromBlocks_diagonal hA hC).1

/-- The negative index of a block diagonal matrix is the sum of those of the blocks.
Port of `NLAlib.inertiaNeg_fromBlocks_zero`. -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_fromBlocks_diagonal
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    inertiaNeg (Matrix.fromBlocks A 0 0 C) = inertiaNeg A + inertiaNeg C :=
  (inertia_fromBlocks_diagonal hA hC).2

/-- The block factorization behind the Schur complement, as a congruence. -/
private theorem fromBlocks_eq_conjTranspose_mul_fromBlocks_mul [DecidableEq m] [DecidableEq n]
    {A : Matrix m m 𝕜}
    (hA : A.IsHermitian) (hAu : IsUnit A.det) (B : Matrix m n 𝕜) (C : Matrix n n 𝕜) :
    Matrix.fromBlocks A B Bᴴ C =
      (Matrix.fromBlocks 1 (A⁻¹ * B) 0 1)ᴴ * Matrix.fromBlocks A 0 0 (C - Bᴴ * A⁻¹ * B) *
        Matrix.fromBlocks 1 (A⁻¹ * B) 0 1 := by
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_mul,
    hA.inv.eq, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hAu,
    Matrix.nonsing_inv_mul _ hAu, add_sub_cancel]

/-- **Haynsworth inertia additivity**, positive index: for an invertible Hermitian block `A`,
the inertia of the block matrix is that of `A` plus that of the Schur complement.
[HornJohnson2013, §4.5].
Port of `NLAlib.inertiaPos_fromBlocks_eq_add_schur`, there over `ℝ`.
Result: haynsworth -/
theorem _root_.Matrix.IsHermitian.inertiaPos_fromBlocks [DecidableEq m]
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hAu : IsUnit A.det) (hC : C.IsHermitian) (B : Matrix m n 𝕜) :
    inertiaPos (Matrix.fromBlocks A B Bᴴ C) = inertiaPos A + inertiaPos (C - Bᴴ * A⁻¹ * B) := by
  classical
  have hS : (C - Bᴴ * A⁻¹ * B).IsHermitian :=
    hC.sub (Matrix.isHermitian_conjTranspose_mul_mul B hA.inv)
  have hD : (Matrix.fromBlocks A 0 0 (C - Bᴴ * A⁻¹ * B)).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hA (by rw [Matrix.conjTranspose_zero]) hS
  rw [fromBlocks_eq_conjTranspose_mul_fromBlocks_mul hA hAu B C,
    hD.inertiaPos_conjTranspose_mul_mul (by rw [Matrix.det_fromBlocks_zero₂₁]; simp),
    hA.inertiaPos_fromBlocks_diagonal hS]

/-- **Haynsworth inertia additivity**, negative index.
Port of `NLAlib.inertiaNeg_fromBlocks_eq_add_schur`.
Result: haynsworth -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_fromBlocks [DecidableEq m]
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hAu : IsUnit A.det) (hC : C.IsHermitian) (B : Matrix m n 𝕜) :
    inertiaNeg (Matrix.fromBlocks A B Bᴴ C) = inertiaNeg A + inertiaNeg (C - Bᴴ * A⁻¹ * B) := by
  classical
  have hS : (C - Bᴴ * A⁻¹ * B).IsHermitian :=
    hC.sub (Matrix.isHermitian_conjTranspose_mul_mul B hA.inv)
  have hD : (Matrix.fromBlocks A 0 0 (C - Bᴴ * A⁻¹ * B)).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hA (by rw [Matrix.conjTranspose_zero]) hS
  rw [fromBlocks_eq_conjTranspose_mul_fromBlocks_mul hA hAu B C,
    hD.inertiaNeg_conjTranspose_mul_mul (by rw [Matrix.det_fromBlocks_zero₂₁]; simp),
    hA.inertiaNeg_fromBlocks_diagonal hS]

/-- For `A` positive definite, `Bᴴ A⁻¹ B` has the rank of `B`. -/
private theorem rank_conjTranspose_mul_inv_mul [DecidableEq m] {A : Matrix m m 𝕜} (hA : A.PosDef)
    (B : Matrix m n 𝕜) : (Bᴴ * A⁻¹ * B).rank = B.rank := by
  have hker : LinearMap.ker (Bᴴ * A⁻¹ * B).mulVecLin = LinearMap.ker B.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · by_contra hx
      have h1 := hA.inv.re_quadForm_pos hx
      rw [← quadForm_conjTranspose_mul_mul, quadForm_def, h, dotProduct_zero, map_zero] at h1
      exact lt_irrefl _ h1
    · rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  have h1 := Matrix.finrank_ker_mulVecLin_add_rank (Bᴴ * A⁻¹ * B)
  have h2 := Matrix.finrank_ker_mulVecLin_add_rank B
  rw [hker] at h1
  omega

/-- **The inertia of a saddle-point matrix.** For `A` positive definite, the matrix
`[[A, B], [Bᴴ, 0]]` has as many positive eigenvalues as `A` has rows.
[GolubVanLoan2013, §4.4 context]. -/
theorem _root_.Matrix.PosDef.inertiaPos_fromBlocks_zero {A : Matrix m m 𝕜} (hA : A.PosDef)
    (B : Matrix m n 𝕜) :
    inertiaPos (Matrix.fromBlocks A B Bᴴ 0) = Fintype.card m := by
  classical
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hX : (Bᴴ * A⁻¹ * B).PosSemidef := hA.inv.posSemidef.conjTranspose_mul_mul_same B
  rw [hA.isHermitian.inertiaPos_fromBlocks hAu Matrix.isHermitian_zero B, zero_sub,
    ← inertiaNeg_eq_inertiaPos_neg, hX.isHermitian.posSemidef_iff_inertiaNeg_eq_zero.mp hX,
    add_zero, hA.isHermitian.posDef_iff_inertiaPos_eq_card.mp hA]

/-- The inertia of a saddle-point matrix: for `A` positive definite, `[[A, B], [Bᴴ, 0]]` has
`rank B` negative eigenvalues. -/
theorem _root_.Matrix.PosDef.inertiaNeg_fromBlocks_zero {A : Matrix m m 𝕜} (hA : A.PosDef)
    (B : Matrix m n 𝕜) : inertiaNeg (Matrix.fromBlocks A B Bᴴ 0) = B.rank := by
  classical
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hX : (Bᴴ * A⁻¹ * B).PosSemidef := hA.inv.posSemidef.conjTranspose_mul_mul_same B
  have h1 := hX.isHermitian.inertiaPos_add_inertiaNeg
  rw [hX.isHermitian.posSemidef_iff_inertiaNeg_eq_zero.mp hX, add_zero,
    rank_conjTranspose_mul_inv_mul hA B] at h1
  rw [hA.isHermitian.inertiaNeg_fromBlocks hAu Matrix.isHermitian_zero B, zero_sub,
    inertiaNeg_eq_inertiaPos_neg (-(Bᴴ * A⁻¹ * B)), neg_neg, h1,
    hA.posSemidef.isHermitian.posSemidef_iff_inertiaNeg_eq_zero.mp hA.posSemidef, zero_add]

/-! ### Counting eigenvalues -/

/-- The negative index of `A - x • 1` counts the eigenvalues of `A` below `x`.
Port of `NLAlib.inertiaNeg_sub_smul_one_eq_card`. -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_sub_smul_one [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : ℝ) :
    inertiaNeg (A - x • (1 : Matrix n n 𝕜)) =
      ((Finset.range (Fintype.card n)).filter fun i => eigenvalue A i < x).card := by
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  rw [sub_eq_add_neg, ← neg_smul, hA.eigenvalue_add_smul_one _ (Finset.mem_range.mp hi),
    ← sub_eq_add_neg, sub_neg]

/-- The positive index of `A - x • 1` counts the eigenvalues of `A` above `x`.
Port of `NLAlib.inertiaPos_sub_smul_one_eq_card`. -/
theorem _root_.Matrix.IsHermitian.inertiaPos_sub_smul_one [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : ℝ) :
    inertiaPos (A - x • (1 : Matrix n n 𝕜)) =
      ((Finset.range (Fintype.card n)).filter fun i => x < eigenvalue A i).card := by
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  rw [sub_eq_add_neg, ← neg_smul, hA.eigenvalue_add_smul_one _ (Finset.mem_range.mp hi),
    ← sub_eq_add_neg, sub_pos]

/-- **Counting eigenvalues by a triangular factorization.** If `A - x • 1 = L D Lᴴ` with `L`
invertible and `D` real diagonal, the number of eigenvalues of `A` below `x` is the number of
negative entries of `D`. [GolubVanLoan2013, §8.4.2].
Port of `NLAlib.card_eigenvalues_lt_eq_card_neg_of_eq_mul_diagonal_mul`. -/
theorem _root_.Matrix.IsHermitian.card_eigenvalue_lt_eq_card_neg_of_sub_smul_one_eq
    [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : ℝ} {L : Matrix n n 𝕜} (hL : IsUnit L.det) {d : n → ℝ}
    (h : A - x • (1 : Matrix n n 𝕜) = L * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Lᴴ) :
    ((Finset.range (Fintype.card n)).filter fun i => eigenvalue A i < x).card =
      (Finset.univ.filter fun i => d i < 0).card := by
  rw [← hA.inertiaNeg_sub_smul_one, h, (inertia_mul_diagonal_mul_conjTranspose hL d).2]

/-- Elimination keeps a Hermitian matrix Hermitian. -/
private theorem isHermitian_gaussState {k : ℕ} {M : Matrix (Fin k) (Fin k) 𝕜}
    (hM : M.IsHermitian) (j : ℕ) : (gaussState M j).IsHermitian := by
  induction j with
  | zero => exact hM
  | succ j ih =>
    rw [gaussState]
    split_ifs with h
    · exact ih.eliminationStep _
    · exact ih

/-- **The `L D Lᴴ` factorization produced by elimination** of a Hermitian matrix at nonzero
pivots: column `j` of `L` is the pivot column of the `j`-th state and `D` holds the inverses of
the pivots. -/
private theorem eq_mul_diagonal_mul_conjTranspose_of_gaussState_ne_zero {k : ℕ}
    {M : Matrix (Fin k) (Fin k) 𝕜} (hM : M.IsHermitian)
    (hp : ∀ i : Fin k, gaussState M i i i ≠ 0) :
    M = Matrix.of (fun i j : Fin k => gaussState M j i j) *
      Matrix.diagonal (fun j : Fin k => (((RCLike.re (gaussState M j j j))⁻¹ : ℝ) : 𝕜)) *
        (Matrix.of fun i j : Fin k => gaussState M j i j)ᴴ := by
  have h0 : gaussState M k = 0 := by
    ext i j
    exact gaussState_apply_eq_zero_of_lt_left M (fun l _ => hp l) i.isLt j
  have h := eq_gaussState_add_sum M k
  rw [h0, zero_add, Finset.filter_true_of_mem fun j _ => j.isLt] at h
  ext i l
  refine (congrFun (congrFun h i) l).trans ?_
  rw [Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, (isHermitian_gaussState hM j).apply,
    smul_eq_mul, RCLike.ofReal_inv, (isHermitian_gaussState hM j).coe_re_apply_self j]
  ring

/-- **Counting eigenvalues by pivots** (the Sturm count). If elimination on `A - x • 1` meets no
zero pivot, the number of eigenvalues of `A` below `x`, which is `inertiaNeg (A - x • 1)`, is
the number of negative pivots (the pivots of a Hermitian matrix are real).
[GolubVanLoan2013, Theorem 8.4.1]; [Parlett1998, §3.3].
Port of `NLAlib.card_eigenvalues_lt_eq_card_sign_changes`, which the prototype leaves unproved.
Result: sturm-count -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_sub_smul_one_eq_card_gaussState_re_neg {k : ℕ}
    {A : Matrix (Fin k) (Fin k) 𝕜} (hA : A.IsHermitian) (x : ℝ)
    (hp : ∀ i : Fin k, gaussState (A - x • (1 : Matrix (Fin k) (Fin k) 𝕜)) i i i ≠ 0) :
    inertiaNeg (A - x • (1 : Matrix (Fin k) (Fin k) 𝕜)) =
      (Finset.univ.filter fun i : Fin k =>
        RCLike.re (gaussState (A - x • (1 : Matrix (Fin k) (Fin k) 𝕜)) i i i) < 0).card := by
  have hM : (A - x • (1 : Matrix (Fin k) (Fin k) 𝕜)).IsHermitian :=
    hA.sub (isHermitian_real_smul_one x)
  generalize A - x • (1 : Matrix (Fin k) (Fin k) 𝕜) = M at hM hp ⊢
  have hlow : (Matrix.of fun i j : Fin k => gaussState M j i j).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    exact gaussState_apply_eq_zero_of_lt_left M (fun l _ => hp l) (Fin.lt_def.mp hij') j
  have hL : IsUnit (Matrix.of fun i j : Fin k => gaussState M j i j).det :=
    hlow.isUnit_det_iff.mpr fun i => (hp i).isUnit
  have h := (inertia_mul_diagonal_mul_conjTranspose hL
    fun j : Fin k => (RCLike.re (gaussState M j j j))⁻¹).2
  rw [← eq_mul_diagonal_mul_conjTranspose_of_gaussState_ne_zero hM hp] at h
  rw [h]
  simp only [inv_lt_zero]

end NLAlib
