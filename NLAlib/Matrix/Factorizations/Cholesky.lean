/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.GroupTheory.Perm.Fin
public import NLAlib.Matrix.Factorizations.GaussState

/-!
# The Cholesky factorization

`NLAlib.IsCholesky A L` says that $\mathbf{A} = \mathbf{L}\mathbf{L}^{\mathsf{H}}$ with
$\mathbf{L}$ lower triangular with positive diagonal. A matrix has a Cholesky factorization exactly
when it is positive definite, and the factor is unique. A positive semidefinite matrix has a
factorization with nonnegative diagonal, and after a symmetric permutation one whose nonzero
columns are the first $\operatorname{rank} \mathbf{A}$.

## Main definitions

* `NLAlib.IsCholesky`: the factorization predicate.
* `NLAlib.choleskyLower`: the factor computed by elimination, for a matrix indexed by `Fin n`.
* `NLAlib.choleskyPivotPerm`: the greedy symmetric permutation for diagonal pivoting.

## Main results

* `NLAlib.IsCholesky.posDef`, `NLAlib.IsCholesky.unique`.
* `NLAlib.exists_isCholesky_iff_posDef`, `Matrix.PosDef.existsUnique_isCholesky`.
* `Matrix.PosDef.isCholesky_choleskyLower`: elimination computes the factorization.
* `Matrix.IsHermitian.choleskyLower_apply_self`,
  `Matrix.IsHermitian.choleskyLower_apply_self_pos_iff`: the diagonal of the computed factor.
* `Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose`: the pivoted factorization.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [LinearOrder n] [Fintype n]

/-- `IsCholesky A L`: **$\mathbf{A} = \mathbf{L}\mathbf{L}^{\mathsf{H}}$ is a Cholesky
factorization**, with $\mathbf{L}$ lower triangular with positive (real) diagonal.
[GolubVanLoan2013, Theorem 4.2.7]; [HornJohnson2013, Corollary 7.2.9]. -/
structure IsCholesky (A L : Matrix n n 𝕜) : Prop where
  /-- The factor is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- The diagonal of the factor is positive. -/
  apply_self_pos : ∀ i, 0 < L i i
  /-- The matrix is the factor times its conjugate transpose. -/
  eq_mul_conjTranspose : A = L * Lᴴ

section

variable [DecidableEq n] {A L : Matrix n n 𝕜}

/-- A Cholesky factor is invertible: $\det \mathbf{L}$ is a unit. -/
theorem IsCholesky.isUnit_det (h : IsCholesky A L) : IsUnit L.det :=
  h.isLowerTriangular.isUnit_det_iff.mpr fun i => (h.apply_self_pos i).ne'.isUnit

omit [DecidableEq n] in
/-- A matrix with a Cholesky factorization is positive definite. -/
theorem IsCholesky.posDef (h : IsCholesky A L) : A.PosDef := by
  classical
  rw [h.eq_mul_conjTranspose]
  exact Matrix.PosDef.mul_conjTranspose_self L
    (Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det L).mpr h.isUnit_det))

omit [DecidableEq n] in
/-- **The Cholesky factor is unique**: two Cholesky factors of the same matrix are equal.
[GolubVanLoan2013, Theorem 4.2.7]. -/
theorem IsCholesky.unique {L' : Matrix n n 𝕜} (h : IsCholesky A L) (h' : IsCholesky A L') :
    L = L' := by
  classical
  have hL := h.isUnit_det
  have hL' := h'.isUnit_det
  have hLt : IsUnit Lᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hL.star
  have hL't : IsUnit L'ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hL'.star
  have hLL : L * Lᴴ = L' * L'ᴴ := h.eq_mul_conjTranspose.symm.trans h'.eq_mul_conjTranspose
  have hDlow : (L'⁻¹ * L).IsLowerTriangular :=
    Matrix.BlockTriangular.mul h'.isLowerTriangular.inv h.isLowerTriangular
  have hD2 : L'⁻¹ * L = L'ᴴ * (Lᴴ)⁻¹ := by
    calc L'⁻¹ * L = L'⁻¹ * L * (Lᴴ * (Lᴴ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hLt, Matrix.mul_one]
      _ = L'⁻¹ * (L * Lᴴ) * (Lᴴ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L'ᴴ * (Lᴴ)⁻¹ := by
          rw [hLL, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hL', Matrix.one_mul]
  have hDup : (L'⁻¹ * L).IsUpperTriangular := by
    rw [hD2]
    exact Matrix.BlockTriangular.mul h'.isLowerTriangular.conjTranspose
      h.isLowerTriangular.conjTranspose.inv
  have hpos : ∀ i, 0 < (L'⁻¹ * L) i i := fun i => by
    rw [h'.isLowerTriangular.inv.mul_apply_self h.isLowerTriangular,
      h'.isLowerTriangular.inv_apply_self fun j => (h'.apply_self_pos j).ne']
    exact mul_pos (RCLike.inv_pos_of_pos (h'.apply_self_pos i)) (h.apply_self_pos i)
  have hDD : L'⁻¹ * L * (L'⁻¹ * L)ᴴ = 1 := by
    calc L'⁻¹ * L * (L'⁻¹ * L)ᴴ = L'⁻¹ * (L * Lᴴ) * (L'ᴴ)⁻¹ := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hLL, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hL', Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hL't]
  have hone : ∀ i, (L'⁻¹ * L) i i = 1 := fun i => by
    have h1 := congrFun (congrFun hDD i) i
    rw [hDlow.mul_apply_self hDup.conjTranspose, Matrix.conjTranspose_apply,
      (IsSelfAdjoint.of_nonneg (hpos i).le).star_eq, Matrix.one_apply_eq] at h1
    have h2 : ((L'⁻¹ * L) i i - 1) * ((L'⁻¹ * L) i i + 1) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (add_pos (hpos i) one_pos).ne'
  have hD1 : L'⁻¹ * L = 1 := by
    rw [eq_diagonal_of_isLowerTriangular_of_isUpperTriangular hDlow hDup]
    simp only [hone, Matrix.diagonal_one]
  calc L = L' * (L'⁻¹ * L) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hL', Matrix.one_mul]
    _ = L' := by rw [hD1, Matrix.mul_one]

/-- The determinant is the product of the squared diagonal of the Cholesky factor:
$\det \mathbf{A} = \prod_i \mathbf{L}_{i,i}^2$. -/
theorem IsCholesky.det_eq_prod (h : IsCholesky A L) : A.det = ∏ i, L i i ^ 2 := by
  rw [h.eq_mul_conjTranspose, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_of_isLowerTriangular _ h.isLowerTriangular, star_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(IsSelfAdjoint.of_nonneg (h.apply_self_pos i).le).star_eq, sq]

/-- Solving through a Cholesky factorization: $\mathbf{A}\mathbf{x} = \mathbf{b}$ exactly
when $\mathbf{L}^{\mathsf{H}}\mathbf{x} = \mathbf{L}^{-1}\mathbf{b}$. -/
theorem IsCholesky.mulVec_eq_iff (h : IsCholesky A L) {x b : n → 𝕜} :
    A *ᵥ x = b ↔ Lᴴ *ᵥ x = L⁻¹ *ᵥ b := by
  have hL := h.isUnit_det
  rw [h.eq_mul_conjTranspose, ← Matrix.mulVec_mulVec]
  constructor
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hL, Matrix.one_mulVec]
  · intro hx
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv L hL, Matrix.one_mulVec]

end

/-! ### Elimination -/

section Recursion

variable {n : ℕ}

/-- The Cholesky factor computed by elimination: column $j$ is the pivot column of step $j$
divided by the square root of the pivot. A zero pivot gives a zero column. -/
noncomputable def choleskyLower (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j =>
    if j ≤ i then gaussState A j i j / ((√(RCLike.re (gaussState A j j j)) : ℝ) : 𝕜) else 0

/-- The factor computed by elimination is lower triangular. -/
theorem isLowerTriangular_choleskyLower (A : Matrix (Fin n) (Fin n) 𝕜) :
    (choleskyLower A).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  simp only [choleskyLower, Matrix.of_apply, if_neg hij'.not_ge]

/-- Elimination preserves positive semidefinite matrices. -/
private theorem posSemidef_gaussState {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef)
    (k : ℕ) : (gaussState A k).PosSemidef := by
  rw [gaussState_eq_foldl]
  exact hA.foldl_eliminationStep _

/-- Elimination on a positive semidefinite matrix clears the rows of the pivots used, whether
or not the pivots are zero. -/
private theorem gaussState_apply_eq_zero_of_posSemidef {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosSemidef) {k : ℕ} {i : Fin n} (hi : (i : ℕ) < k) (l : Fin n) :
    gaussState A k i l = 0 := by
  induction k generalizing l with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    by_cases hk : k < n
    · rw [gaussState_succ A hk]
      by_cases hik : (i : ℕ) = k
      · obtain rfl : i = ⟨k, hk⟩ := Fin.ext hik
        exact (posSemidef_gaussState hA k).eliminationStep_apply_pivot_left _ l
      · exact eliminationStep_apply_eq_zero_of_row (fun l => ih (by omega) l) _ l
    · rw [gaussState, dif_neg hk]
      exact ih (by have := i.2; omega) l

/-- The diagonal of the factor computed by elimination on a Hermitian matrix is the square root
of the real part of the pivot: $\mathbf{L}_{i,i} = \sqrt{\operatorname{Re} \mathbf{A}^{(i)}_{i,i}}$,
with $\mathbf{A}^{(i)}$ the state after $i$ steps (`NLAlib.gaussState`) and $\sqrt{t} = 0$ for
$t < 0$. -/
theorem _root_.Matrix.IsHermitian.choleskyLower_apply_self {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (i : Fin n) :
    choleskyLower A i i = ((√(RCLike.re (gaussState A i i i)) : ℝ) : 𝕜) := by
  simp only [choleskyLower, Matrix.of_apply, le_refl, if_true]
  nth_rewrite 1 [← (hA.gaussState i).coe_re_apply_self i]
  rw [← RCLike.ofReal_div, Real.div_sqrt]

/-- For a Hermitian matrix, the diagonal entry $\mathbf{L}_{i,i}$ of the computed factor is
positive exactly when the pivot $\mathbf{A}^{(i)}_{i,i}$ is. -/
theorem _root_.Matrix.IsHermitian.choleskyLower_apply_self_pos_iff
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (i : Fin n) :
    0 < choleskyLower A i i ↔ 0 < gaussState A i i i := by
  rw [hA.choleskyLower_apply_self, RCLike.ofReal_pos, Real.sqrt_pos,
    ← (hA.gaussState i).coe_re_apply_self i, RCLike.ofReal_pos, RCLike.ofReal_re]

/-- The diagonal of the factor computed by elimination on a Hermitian matrix is nonnegative. -/
theorem _root_.Matrix.IsHermitian.choleskyLower_apply_self_nonneg
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (i : Fin n) :
    0 ≤ choleskyLower A i i := by
  rw [hA.choleskyLower_apply_self]
  exact RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _)

/-- The entries of the product of the computed factor with its conjugate transpose, when the
pivots are nonnegative. -/
private theorem choleskyLower_mul_conjTranspose_apply {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (h0 : ∀ j : Fin n, 0 ≤ gaussState A j j j) (i l : Fin n) :
    (choleskyLower A * (choleskyLower A)ᴴ) i l =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i ∧ j ≤ l),
        (gaussState A j j j)⁻¹ * (gaussState A j i j * gaussState A j j l) := by
  rw [Matrix.mul_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [choleskyLower, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hji : j ≤ i
  · by_cases hjl : j ≤ l
    · have hsq : ((√(RCLike.re (gaussState A j j j)) : ℝ) : 𝕜) *
          ((√(RCLike.re (gaussState A j j j)) : ℝ) : 𝕜) = gaussState A j j j := by
        rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (RCLike.nonneg_iff.mp (h0 j)).1,
          (hA.gaussState j).coe_re_apply_self j]
      rw [if_pos hji, if_pos hjl, if_pos ⟨hji, hjl⟩, star_div₀, RCLike.star_def,
        RCLike.conj_ofReal, ← RCLike.star_def, (hA.gaussState j).apply,
        div_mul_div_comm, hsq]
      ring
    · rw [if_neg hjl, if_neg (not_and_of_not_right _ hjl), star_zero, mul_zero]
  · rw [if_neg hji, if_neg (not_and_of_not_left _ hji), zero_mul]

/-- Elimination factors a Hermitian matrix whose pivots are nonnegative, as soon as a zero
pivot has a zero column. -/
private theorem eq_choleskyLower_mul_conjTranspose_of {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (h0 : ∀ j : Fin n, 0 ≤ gaussState A j j j)
    (hz : ∀ j i : Fin n, gaussState A j j j = 0 → gaussState A j i j = 0) :
    A = choleskyLower A * (choleskyLower A)ᴴ := by
  have hcol : ∀ j i : Fin n, gaussState A ((j : ℕ) + 1) i j = 0 := by
    intro j i
    rw [gaussState_succ A j.2]
    by_cases hp : gaussState A j j j = 0
    · rw [eliminationStep_eq_self_of_apply_self_eq_zero hp]
      exact hz j i hp
    · exact eliminationStep_apply_pivot_right hp i
  have hrow : ∀ j l : Fin n, gaussState A ((j : ℕ) + 1) j l = 0 := by
    intro j l
    rw [← (hA.gaussState ((j : ℕ) + 1)).apply, hcol j l, star_zero]
  have ht : ∀ (k : ℕ) (i l : Fin n), A i l = gaussState A k i l +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
        (gaussState A j j j)⁻¹ * (gaussState A j i j * gaussState A j j l) := by
    intro k i l
    have h := congrFun (congrFun (eq_gaussState_add_sum A k) i) l
    simpa only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul] using h
  ext i l
  rw [choleskyLower_mul_conjTranspose_apply hA h0]
  rcases le_total i l with hil | hil
  · rw [ht ((i : ℕ) + 1) i l, hrow i l, zero_add]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hil ⊢
    omega
  · rw [ht ((l : ℕ) + 1) i l, hcol l i, zero_add]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hil ⊢
    omega

/-- Elimination factors a positive semidefinite matrix:
$\mathbf{A} = \mathbf{L}\mathbf{L}^{\mathsf{H}}$ for the computed factor $\mathbf{L}$. -/
theorem _root_.Matrix.PosSemidef.eq_choleskyLower_mul_conjTranspose
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) :
    A = choleskyLower A * (choleskyLower A)ᴴ :=
  eq_choleskyLower_mul_conjTranspose_of hA.isHermitian
    (fun j => (posSemidef_gaussState hA j).diag_nonneg)
    fun j i hj => congrFun ((posSemidef_gaussState hA j).col_eq_zero_of_apply_self_eq_zero hj) i

/-- Elimination computes the Cholesky factorization of a positive definite matrix. -/
theorem _root_.Matrix.PosDef.isCholesky_choleskyLower {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) : IsCholesky A (choleskyLower A) :=
  ⟨isLowerTriangular_choleskyLower A,
    fun i => (hA.isHermitian.choleskyLower_apply_self_pos_iff i).mpr
      (hA.gaussState_apply_self_pos i),
    hA.posSemidef.eq_choleskyLower_mul_conjTranspose⟩

/-- Elimination on a Hermitian matrix produces a positive diagonal exactly when the matrix is
positive definite. -/
theorem _root_.Matrix.IsHermitian.forall_choleskyLower_apply_self_pos_iff
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    (∀ i, 0 < choleskyLower A i i) ↔ A.PosDef := by
  refine ⟨fun h => ?_, fun h => h.isCholesky_choleskyLower.apply_self_pos⟩
  have hp : ∀ j : Fin n, 0 < gaussState A j j j := fun j =>
    (hA.choleskyLower_apply_self_pos_iff j).mp (h j)
  exact IsCholesky.posDef ⟨isLowerTriangular_choleskyLower A, h,
    eq_choleskyLower_mul_conjTranspose_of hA (fun j => (hp j).le)
      fun j i hj => absurd hj (hp j).ne'⟩

/-- The ordering computed by diagonally pivoted Cholesky. At each step the first remaining
index with maximal real residual diagonal entry is swapped into the pivot position.
[Higham2002, §10.3].
Algorithm: pivoted-cholesky -/
noncomputable def choleskyPivotPerm (A : Matrix (Fin n) (Fin n) 𝕜) : Equiv.Perm (Fin n) :=
  Fin.greedyPerm (fun σ j i => RCLike.re (gaussState (A.submatrix σ σ) j i i)) n

/-- In the computed Cholesky ordering, the pivot is maximal on the remaining residual diagonal.
[Higham2002, §10.3]. -/
theorem re_gaussState_choleskyPivotPerm_le (A : Matrix (Fin n) (Fin n) 𝕜) (j i : Fin n)
    (hji : j ≤ i) :
    let B := A.submatrix (choleskyPivotPerm A) (choleskyPivotPerm A)
    RCLike.re (gaussState B j i i) ≤ RCLike.re (gaussState B j j j) := by
  have hs : ∀ (σ τ : Equiv.Perm (Fin n)) (j : Fin n), (∀ l : Fin n, l < j → τ l = l) →
      ∀ i, RCLike.re (gaussState (A.submatrix (τ.trans σ) (τ.trans σ)) j i i) =
        RCLike.re (gaussState (A.submatrix σ σ) j (τ i) (τ i)) := by
    intro σ τ j hτ i
    have hsub : A.submatrix (τ.trans σ) (τ.trans σ) = (A.submatrix σ σ).submatrix τ τ := rfl
    rw [hsub, gaussState_submatrix _ τ j fun l hl => hτ l (Fin.lt_def.mpr hl)]
    rfl
  exact Fin.le_greedyPerm_apply_self
    (fun σ j i => RCLike.re (gaussState (A.submatrix σ σ) j i i)) hs n j i j.isLt hji

/-- The positive pivots and zero columns in the computed diagonal pivot order. -/
private theorem choleskyLower_pivot_rank {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) :
    let σ := choleskyPivotPerm A
    (∀ i : Fin n, 0 < choleskyLower (A.submatrix σ σ) i i ↔ (i : ℕ) < A.rank) ∧
      ∀ i j : Fin n, A.rank ≤ (j : ℕ) → choleskyLower (A.submatrix σ σ) i j = 0 := by
  let σ := choleskyPivotPerm A
  let B := A.submatrix σ σ
  have hσ : ∀ j i : Fin n, j ≤ i → RCLike.re (gaussState B j i i) ≤
      RCLike.re (gaussState B j j j) := re_gaussState_choleskyPivotPerm_le A
  have hrank : (A.submatrix σ σ).rank = A.rank := Matrix.rank_submatrix A σ σ
  have hB : B.PosSemidef := hA.submatrix σ
  change (∀ i : Fin n, 0 < choleskyLower B i i ↔ (i : ℕ) < A.rank) ∧
    ∀ i j : Fin n, A.rank ≤ (j : ℕ) → choleskyLower B i j = 0
  change B.rank = A.rank at hrank
  rw [← hrank]
  have hG := posSemidef_gaussState hB
  -- a zero pivot means that elimination has reached the zero matrix
  have hzero : ∀ j : Fin n, gaussState B j j j = 0 → gaussState B j = 0 := by
    intro j hj
    have hdiag : ∀ i : Fin n, gaussState B j i i = 0 := by
      intro i
      rcases lt_or_ge i j with hij | hij
      · exact gaussState_apply_eq_zero_of_posSemidef hB (Fin.lt_def.mp hij) i
      · have h1 := hσ j i hij
        rw [hj, map_zero] at h1
        have h2 := (hG j).diag_nonneg (i := i)
        rw [← (hG j).isHermitian.coe_re_apply_self i] at h2 ⊢
        rw [le_antisymm h1 (RCLike.ofReal_nonneg.mp h2), RCLike.ofReal_zero]
    ext i l
    exact congrFun ((hG j).col_eq_zero_of_apply_self_eq_zero (hdiag l)) i
  -- the pivots before the rank are nonzero
  have hne : ∀ (k : ℕ) (i : Fin n), (i : ℕ) = k → k < B.rank → gaussState B i i i ≠ 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik hk hi
      have hp : ∀ l : Fin n, (l : ℕ) < (i : ℕ) → gaussState B l l l ≠ 0 := fun l hl =>
        ih l (hik ▸ hl) l rfl (by omega)
      have hr := rank_gaussState_add B i.2.le hp
      rw [hzero i hi, Matrix.rank_zero] at hr
      omega
  have h0 : gaussState B B.rank = 0 := by
    have hr := rank_gaussState_add B B.rank_le_width fun l hl => hne l l rfl hl
    exact Matrix.rank_eq_zero.mp (by omega)
  refine ⟨fun i => ?_, fun i j hj => ?_⟩
  · rw [hB.isHermitian.choleskyLower_apply_self_pos_iff]
    constructor
    · intro hi
      by_contra hlt
      rw [gaussState_eq_zero_of_le h0 (not_lt.mp hlt)] at hi
      exact lt_irrefl _ hi
    · exact fun hi => lt_of_le_of_ne (hG i).diag_nonneg (hne i i rfl hi).symm
  · simp only [choleskyLower, Matrix.of_apply, gaussState_eq_zero_of_le h0 hj, Matrix.zero_apply,
      zero_div, ite_self]

/-- **Rank detection by pivoted Cholesky.** Exactly the first $\operatorname{rank} \mathbf{A}$
pivots of the computed factor are positive, including for singular positive semidefinite inputs.
[Higham2002, Theorem 10.9].
Result: pivoted-cholesky-rank -/
theorem _root_.Matrix.PosSemidef.choleskyLower_choleskyPivotPerm_apply_self_pos_iff
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) (i : Fin n) :
    0 < choleskyLower (A.submatrix (choleskyPivotPerm A) (choleskyPivotPerm A)) i i ↔
      (i : ℕ) < A.rank :=
  (choleskyLower_pivot_rank hA).1 i

/-- Every column at or beyond the rank is zero in the computed pivoted Cholesky factor.
[Higham2002, Theorem 10.9]. -/
theorem _root_.Matrix.PosSemidef.choleskyLower_choleskyPivotPerm_apply_eq_zero_of_rank_le
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) (i j : Fin n) (hj : A.rank ≤ (j : ℕ)) :
    choleskyLower (A.submatrix (choleskyPivotPerm A) (choleskyPivotPerm A)) i j = 0 :=
  (choleskyLower_pivot_rank hA).2 i j hj

end Recursion

/-! ### Existence -/

section

variable {A : Matrix n n 𝕜}

/-- A Cholesky factorization transported along an order isomorphism of the index type. -/
private theorem IsCholesky.submatrix_orderIso {m : Type*} [LinearOrder m] [Fintype m]
    {L : Matrix n n 𝕜} (h : IsCholesky A L) (e : m ≃o n) :
    IsCholesky (A.submatrix e e) (L.submatrix e e) := by
  refine ⟨h.isLowerTriangular.submatrix_of_strictMono e.strictMono,
    fun i => h.apply_self_pos _, ?_⟩
  rw [h.eq_mul_conjTranspose, Matrix.conjTranspose_submatrix]
  exact (Matrix.submatrix_mul_equiv L Lᴴ e e.toEquiv e).symm

/-- **A matrix has a Cholesky factorization exactly when it is positive definite.**
Result: cholesky-existence -/
theorem exists_isCholesky_iff_posDef (A : Matrix n n 𝕜) : (∃ L, IsCholesky A L) ↔ A.PosDef := by
  refine ⟨fun ⟨L, h⟩ => h.posDef, fun hA => ?_⟩
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  have h := (hA.submatrix e.injective).isCholesky_choleskyLower.submatrix_orderIso e.symm
  have hAe : (A.submatrix e e).submatrix e.symm e.symm = A := by
    ext i j
    simp only [Matrix.submatrix_apply, OrderIso.apply_symm_apply]
  rw [hAe] at h
  exact ⟨_, h⟩

/-- A positive definite matrix has exactly one Cholesky factor. -/
theorem _root_.Matrix.PosDef.existsUnique_isCholesky (hA : A.PosDef) :
    ∃! L, IsCholesky A L := by
  obtain ⟨L, hL⟩ := (exists_isCholesky_iff_posDef A).mpr hA
  exact ⟨L, hL, fun L' hL' => hL'.unique hL⟩

/-- A positive semidefinite matrix is $\mathbf{L}\mathbf{L}^{\mathsf{H}}$ for a lower triangular
$\mathbf{L}$ with nonnegative diagonal. -/
theorem _root_.Matrix.PosSemidef.exists_eq_mul_conjTranspose_of_isLowerTriangular
    (hA : A.PosSemidef) :
    ∃ L : Matrix n n 𝕜, L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ A = L * Lᴴ := by
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  have hA' : (A.submatrix e e).PosSemidef := hA.submatrix e
  refine ⟨(choleskyLower (A.submatrix e e)).submatrix e.symm e.symm,
    (isLowerTriangular_choleskyLower _).submatrix_of_strictMono e.symm.strictMono,
    fun i => hA'.isHermitian.choleskyLower_apply_self_nonneg _, ?_⟩
  rw [Matrix.conjTranspose_submatrix]
  refine Eq.trans ?_ (Matrix.submatrix_mul_equiv _ _ e.symm e.symm.toEquiv e.symm).symm
  rw [← hA'.eq_choleskyLower_mul_conjTranspose]
  ext i j
  simp only [Matrix.submatrix_apply, OrderIso.apply_symm_apply]

/-- **Pivoted Cholesky.** A positive semidefinite matrix $\mathbf{A}$ has, after a symmetric
permutation $\sigma$ of rows and columns, a factorization $\mathbf{L}\mathbf{L}^{\mathsf{H}}$ with
$\mathbf{L}$ lower triangular with nonnegative diagonal, whose first
$\operatorname{rank} \mathbf{A}$ diagonal entries are positive and whose remaining columns vanish.
[Higham2002, Theorem 10.9]. -/
theorem _root_.Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose [LocallyFiniteOrderBot n]
    (hA : A.PosSemidef) :
    ∃ (σ : Equiv.Perm n) (L : Matrix n n 𝕜), L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧
      A.submatrix σ σ = L * Lᴴ ∧ (∀ i, 0 < L i i ↔ (Finset.Iio i).card < A.rank) ∧
      ∀ i j, A.rank ≤ (Finset.Iio j).card → L i j = 0 := by
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  have hA' : (A.submatrix e e).PosSemidef := hA.submatrix e
  let σ := choleskyPivotPerm (A.submatrix e e)
  obtain ⟨hpos, hzero⟩ := choleskyLower_pivot_rank hA'
  have hB : ((A.submatrix e e).submatrix σ σ).PosSemidef := hA'.submatrix σ
  have hrank : (A.submatrix e e).rank = A.rank := Matrix.rank_submatrix A e.toEquiv e.toEquiv
  have hcard : ∀ i : n, (Finset.Iio i).card = (e.symm i : ℕ) := by
    intro i
    rw [← Fin.card_Iio, ← Finset.card_image_of_injective _ e.injective]
    congr 1
    refine Finset.coe_injective ?_
    rw [Finset.coe_image, Finset.coe_Iio, Finset.coe_Iio, OrderIso.image_Iio,
      OrderIso.apply_symm_apply]
  rw [hrank] at hpos hzero
  refine ⟨(e.symm.toEquiv.trans σ).trans e.toEquiv,
    (choleskyLower ((A.submatrix e e).submatrix σ σ)).submatrix e.symm e.symm,
    (isLowerTriangular_choleskyLower _).submatrix_of_strictMono e.symm.strictMono,
    fun i => hB.isHermitian.choleskyLower_apply_self_nonneg _, ?_,
    fun i => by rw [hcard]; exact hpos _, fun i j hj => hzero _ _ (by rwa [hcard] at hj)⟩
  rw [Matrix.conjTranspose_submatrix]
  refine Eq.trans ?_ (Matrix.submatrix_mul_equiv _ _ e.symm e.symm.toEquiv e.symm).symm
  rw [← hB.eq_choleskyLower_mul_conjTranspose]
  ext i j
  simp only [Matrix.submatrix_apply, Equiv.trans_apply, RelIso.coe_fn_toEquiv]

end

end NLAlib
