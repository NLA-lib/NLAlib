/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU

/-!
# Singular LU and Gaussian elimination with partial pivoting

Elimination without pivoting, `NLAlib.luLower` and `NLAlib.luUpper`, factors a matrix as soon as
every zero pivot has only zeros below it (`NLAlib.eq_luLower_mul_luUpper`); nonzero pivots are
not needed. This file states that as a realisation theorem for `NLAlib.IsLU`, and specialises it
to partial pivoting, where every pivot is largest in absolute value among the entries below it:
then the multipliers are at most one and row $i$ of the upper factor grows by at most $2^i$.

## Main results

* `NLAlib.isLU_luLower_luUpper_of_forall_eq_zero`: elimination computes the LU factorization
  when every zero pivot has zeros below it.
* `NLAlib.isLU_luLower_luUpper_of_forall_norm_le`, `NLAlib.norm_luLower_apply_le_one`,
  `NLAlib.norm_luUpper_apply_le`: the factors computed with pivots of largest absolute value.
* `NLAlib.exists_perm_isLU_luLower_luUpper_norm_le`: partial pivoting with the row-wise growth
  bound $2^i$. Wilkinson's matrix attains this bound in the final row
  (`NLAlib.exists_norm_luUpper_apply_last_eq_two_pow`).
* `NLAlib.forall_luUpper_apply_self_ne_zero_iff_isUnit_det`: the partial pivoting permutation
  `NLAlib.luPartialPivotPerm` gives nonzero pivots exactly for nonsingular inputs.
* `NLAlib.exists_isLU_iff_forall_mem_span`,
  `NLAlib.exists_isLowerTriangular_isUnitUpperTriangular_iff_forall_mem_span`: row and column
  inclusion characterize existence of each normalization of LU, including for singular inputs.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {K : Type*} [Field K] {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Elimination computes the LU factorization when every zero pivot has zeros below it.
This covers singular matrices; `NLAlib.isLU_luLower_luUpper` is the case of nonzero pivots. -/
theorem isLU_luLower_luUpper_of_forall_eq_zero {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ j i : Fin n, j < i → gaussState A j j j = 0 → gaussState A j i j = 0) :
    IsLU A (luLower A) (luUpper A) :=
  ⟨isUnitLowerTriangular_luLower A, isUpperTriangular_luUpper A, eq_luLower_mul_luUpper h⟩

/-- Elimination computes the LU factorization when every pivot is largest in absolute value
among the entries below it, as after the row exchanges of partial pivoting:
$\lvert \mathbf{B}^{(j)}_{i,j} \rvert \le \lvert \mathbf{B}^{(j)}_{j,j} \rvert$ for $j \le i$, with
$\mathbf{B}^{(j)}$ the state after $j$ steps (`NLAlib.gaussState`). -/
theorem isLU_luLower_luUpper_of_forall_norm_le {B : Matrix (Fin n) (Fin n) 𝕜}
    (hB : ∀ j i : Fin n, j ≤ i → ‖gaussState B j i j‖ ≤ ‖gaussState B j j j‖) :
    IsLU B (luLower B) (luUpper B) := by
  refine isLU_luLower_luUpper_of_forall_eq_zero fun j i hji hj => ?_
  have h := hB j i hji.le
  rw [hj, norm_zero] at h
  exact norm_le_zero_iff.mp h

/-- With pivots of largest absolute value, the multipliers are at most one in absolute value:
$\lvert \mathbf{L}_{i,j} \rvert \le 1$ for the lower factor $\mathbf{L}$.
[GolubVanLoan2013, §3.4.5]. -/
theorem norm_luLower_apply_le_one {B : Matrix (Fin n) (Fin n) 𝕜}
    (hB : ∀ j i : Fin n, j ≤ i → ‖gaussState B j i j‖ ≤ ‖gaussState B j j j‖) (i j : Fin n) :
    ‖luLower B i j‖ ≤ 1 := by
  simp only [luLower, Matrix.of_apply]
  split_ifs with h1 h2
  · rw [norm_div]
    exact div_le_one_of_le₀ (hB j i h1.le) (norm_nonneg _)
  · rw [norm_one]
  · rw [norm_zero]
    exact zero_le_one

/-- **Row-wise growth with partial pivoting.** With pivots of largest absolute value, the
entries of row $i$ of the upper factor $\mathbf{U}$ exceed those of the matrix by a factor at most
$2^i$: if $\lvert \mathbf{B}_{i,j} \rvert \le M$ for all $i, j$, then
$\lvert \mathbf{U}_{i,j} \rvert \le 2^i M$, rows indexed from $0$.
[Higham2002, §9.3]; there as the growth factor bound $2^{n-1}$, which is the last row. -/
theorem norm_luUpper_apply_le {B : Matrix (Fin n) (Fin n) 𝕜} {M : ℝ}
    (hM : ∀ i j, ‖B i j‖ ≤ M)
    (hB : ∀ j i : Fin n, j ≤ i → ‖gaussState B j i j‖ ≤ ‖gaussState B j j j‖) (i j : Fin n) :
    ‖luUpper B i j‖ ≤ 2 ^ (i : ℕ) * M := by
  simp only [luUpper, Matrix.of_apply]
  split_ifs with h1
  · exact norm_gaussState_apply_le hM hB i i j le_rfl
  · rw [norm_zero]
    exact mul_nonneg (pow_nonneg zero_le_two _) ((norm_nonneg _).trans (hM i j))

/-- The row permutation chosen by Gaussian elimination with partial pivoting. At each step
the algorithm swaps the first remaining row of largest pivot modulus into the pivot position.
The factors are `NLAlib.luLower` and `NLAlib.luUpper` of the row-permuted matrix.
[TrefethenBau1997, Lecture 21]; [GolubVanLoan2013, §3.4].
Algorithm: partial-pivoting -/
noncomputable def luPartialPivotPerm (A : Matrix (Fin n) (Fin n) 𝕜) : Equiv.Perm (Fin n) :=
  Fin.greedyPerm (fun σ j i => ‖gaussState (A.submatrix σ id) j i j‖) n

/-- After the row exchanges of partial pivoting, the diagonal pivot is largest in modulus
in its active column at every step. -/
theorem norm_gaussState_luPartialPivotPerm_le (A : Matrix (Fin n) (Fin n) 𝕜) (j i : Fin n)
    (hji : j ≤ i) :
    ‖gaussState (A.submatrix (luPartialPivotPerm A) id) j i j‖ ≤
      ‖gaussState (A.submatrix (luPartialPivotPerm A) id) j j j‖ :=
  forall_weight_gaussState_submatrix_greedyPerm_le (fun x : 𝕜 => ‖x‖) A j i hji

/-- **Partial pivoting, row by row.** Every square matrix $\mathbf{A}$ indexed by `Fin n` has a
row permutation after which elimination computes an LU factorization whose multipliers are at
most one in absolute value and whose upper factor has row $i$ bounded by $2^i$ times a bound on
the entries of the matrix: if $\lvert \mathbf{A}_{i,j} \rvert \le M$ for all $i, j$, then
$\lvert \mathbf{L}_{i,j} \rvert \le 1$ and $\lvert \mathbf{U}_{i,j} \rvert \le 2^i M$.
[GolubVanLoan2013, §3.4.5]; [Higham2002, §9.3].
`NLAlib.exists_perm_isLU_norm_le` is the uniform bound on any linearly ordered index type. -/
theorem exists_perm_isLU_luLower_luUpper_norm_le (A : Matrix (Fin n) (Fin n) 𝕜) {M : ℝ}
    (hM : ∀ i j, ‖A i j‖ ≤ M) :
    ∃ σ : Equiv.Perm (Fin n),
      IsLU (A.submatrix σ id) (luLower (A.submatrix σ id)) (luUpper (A.submatrix σ id)) ∧
      (∀ i j, ‖luLower (A.submatrix σ id) i j‖ ≤ 1) ∧
      ∀ i j : Fin n, ‖luUpper (A.submatrix σ id) i j‖ ≤ 2 ^ (i : ℕ) * M := by
  have hσ := norm_gaussState_luPartialPivotPerm_le A
  exact ⟨luPartialPivotPerm A, isLU_luLower_luUpper_of_forall_norm_le hσ,
    norm_luLower_apply_le_one hσ,
    norm_luUpper_apply_le (fun a b => hM (luPartialPivotPerm A a) b) hσ⟩

/-- **Partial pivoting succeeds exactly for nonsingular inputs.** All diagonal entries of
$\mathbf{U} = \mathsf{luUpper}(\mathbf{B})$ are nonzero exactly when $\mathbf{A}$ is
invertible, where $\mathbf{B}$ permutes its rows by $\mathsf{luPartialPivotPerm}(\mathbf{A})$.
[TrefethenBau1997, Lecture 21]; [GolubVanLoan2013, Theorem 3.4.1].
Result: partial-pivoting-success -/
theorem forall_luUpper_apply_self_ne_zero_iff_isUnit_det (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∀ i, luUpper (A.submatrix (luPartialPivotPerm A) id) i i ≠ 0) ↔ IsUnit A.det := by
  have hLU := isLU_luLower_luUpper_of_forall_norm_le (norm_gaussState_luPartialPivotPerm_le A)
  simp only [← isUnit_iff_ne_zero, ← hLU.isUnit_det_iff, Matrix.det_permute, IsUnit.mul_iff]
  simp

section Wilkinson

/-- Wilkinson's example has ones on the diagonal and in the last column, and minus ones
strictly below the diagonal outside that column. -/
private def wilkinsonMatrix (n : ℕ) (𝕜 : Type*) [RCLike 𝕜] :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  fun i j => if j = Fin.last n then 1 else if i = j then 1 else if j < i then -1 else 0

/-- In the trailing block, each elimination step doubles the final column and leaves every
other entry in place. -/
private theorem gaussState_wilkinsonMatrix {n : ℕ} (k : ℕ) (i j : Fin (n + 1))
    (hi : k ≤ (i : ℕ)) (hj : k ≤ (j : ℕ)) :
    gaussState (wilkinsonMatrix n 𝕜) k i j =
      if j = Fin.last n then 2 ^ k else if i = j then 1 else if j < i then -1 else 0 := by
  induction k generalizing i j with
  | zero => simp only [gaussState_zero, wilkinsonMatrix, pow_zero]
  | succ k ih =>
    have hkn : k < n := by have := i.isLt; omega
    let p : Fin (n + 1) := ⟨k, by omega⟩
    have hkp : k ≤ (p : ℕ) := le_rfl
    have hpl : p ≠ Fin.last n := Fin.ne_of_val_ne hkn.ne
    have hpi : p < i := Fin.lt_def.mpr hi
    have hpj : p < j := Fin.lt_def.mpr hj
    rw [gaussState_succ _ (by omega), eliminationStep_apply]
    change gaussState _ k i j - (gaussState _ k p p)⁻¹ *
      (gaussState _ k i p * gaussState _ k p j) = _
    rw [ih i j (by omega) (by omega), ih p p hkp hkp, ih i p (by omega) hkp,
      ih p j hkp (by omega)]
    simp only [if_neg hpl, if_true, if_neg hpi.ne', if_pos hpi, if_neg hpj.ne,
      if_neg hpj.not_gt, inv_one, one_mul]
    split_ifs <;> ring

/-- The first active row always maximizes the pivot modulus on Wilkinson's matrix. -/
private theorem norm_gaussState_wilkinsonMatrix_le (j i : Fin (n + 1)) (hji : j ≤ i) :
    ‖gaussState (wilkinsonMatrix n 𝕜) j i j‖ ≤ ‖gaussState (wilkinsonMatrix n 𝕜) j j j‖ := by
  rw [gaussState_wilkinsonMatrix _ _ _ (Fin.le_def.mp hji) le_rfl,
    gaussState_wilkinsonMatrix _ _ _ le_rfl le_rfl]
  simp only [if_true]
  split_ifs <;> simp

/-- **Sharpness of partial pivoting growth.** In every positive dimension $n+1$, a matrix
$\mathbf{A}$ with entries of modulus at most one produces a last pivot of modulus $2^n$:
$\mathbf{U} = \mathsf{luUpper}(\mathbf{B})$, where $\mathbf{B}$ permutes the rows of
$\mathbf{A}$ by $\mathsf{luPartialPivotPerm}(\mathbf{A})$. Wilkinson's example needs no
exchanges under the first-maximum tie rule. [TrefethenBau1997, Lecture 22].
Result: partial-pivoting-growth-sharp -/
theorem exists_norm_luUpper_apply_last_eq_two_pow (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜, (∀ i j, ‖A i j‖ ≤ 1) ∧
      ‖luUpper (A.submatrix (luPartialPivotPerm A) id) (Fin.last n) (Fin.last n)‖ = 2 ^ n := by
  let A := wilkinsonMatrix n 𝕜
  have hperm : luPartialPivotPerm A = 1 := by
    apply Fin.greedyPerm_eq_one_of_forall_le
    intro j i hji
    exact norm_gaussState_wilkinsonMatrix_le j i hji
  refine ⟨A, ?_, ?_⟩
  · intro i j
    dsimp only [A, wilkinsonMatrix]
    split_ifs <;> simp
  · rw [hperm, luUpper_apply_self]
    change ‖gaussState (wilkinsonMatrix n 𝕜) n (Fin.last n) (Fin.last n)‖ = _
    rw [gaussState_wilkinsonMatrix n (Fin.last n) (Fin.last n) le_rfl le_rfl, if_pos rfl, norm_pow]
    norm_num

end Wilkinson

section RowInclusion

variable {ι R : Type*} [LinearOrder ι] [Fintype ι] [CommRing R]

/-- The terms from outside the strict lower triangle of a coefficient matrix vanish. -/
private theorem mul_apply_eq_sum_subtype {C A : Matrix ι ι R} {i : ι}
    (hC : ∀ j, ¬j < i → C i j = 0) (k : ι) :
    (C * A) i k = ∑ j : {j // j < i}, C i j * A j k := by
  classical
  rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun j => j < i)]
  have hz (j : {j // ¬j < i}) : C i j * A j k = 0 := by rw [hC j j.2, zero_mul]
  simp only [hz, Finset.sum_const_zero, add_zero]

/-- **Row inclusion characterizes LU existence.** A square matrix factors as a unit lower
triangular matrix times an upper triangular matrix exactly when, for each index $i$, row $i$
restricted to columns before $i$ lies in the span of the preceding rows on the same columns.
This includes singular matrices and empty index types. [HornJohnson2013, Theorem 3.5.3].
Result: lu-row-inclusion -/
theorem exists_isLU_iff_forall_mem_span (A : Matrix ι ι R) :
    (∃ L U, IsLU A L U) ↔ ∀ i : ι, (fun k : {k // k < i} => A i k) ∈
      Submodule.span R (Set.range fun j : {j // j < i} => fun k : {k // k < i} => A j k) := by
  classical
  constructor
  · rintro ⟨L, U, hLU⟩ i
    let C := 1 - L⁻¹
    have hH := hLU.isUnitLowerTriangular.inv
    have hC (j : ι) (hj : ¬j < i) : C i j = 0 := by
      by_cases hji : i = j
      · subst j
        simp [C, hH.apply_self]
      · have hij := lt_of_le_of_ne (le_of_not_gt hj) hji
        simp [C, Matrix.one_apply_ne hji, hH.isLowerTriangular hij]
    have hunit : IsUnit L.det := hLU.isUnitLowerTriangular.det_eq_one ▸ isUnit_one
    have hCA : C * A = A - U := by
      rw [Matrix.sub_mul, Matrix.one_mul, hLU.eq_mul, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul L hunit, Matrix.one_mul]
    apply (Submodule.mem_span_range_iff_exists_fun R).mpr
    refine ⟨fun j => C i j, ?_⟩
    funext k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply,
      hLU.isUpperTriangular k.property, sub_zero] using
        (mul_apply_eq_sum_subtype (A := A) hC k).symm.trans
          (congrArg (fun B : Matrix ι ι R => B i k) hCA)
  · intro hA
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun R).mp (hA i)
    let C : Matrix ι ι R := fun i j => if h : j < i then c i ⟨j, h⟩ else 0
    let H := 1 - C
    have hC (i j : ι) (h : ¬j < i) : C i j = 0 := dif_neg h
    have hH : IsUnitLowerTriangular H := by
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · change (1 : Matrix ι ι R) i j - C i j = 0
        rw [Matrix.one_apply_ne (show i < j from hij).ne, hC i j (show i < j from hij).not_gt,
          sub_self]
      · change (1 : Matrix ι ι R) i i - C i i = 1
        rw [Matrix.one_apply_eq, hC i i (lt_irrefl i), sub_zero]
    refine ⟨H⁻¹, H * A, hH.inv, ?_, ?_⟩
    · intro i k hki
      change ((1 - C) * A) i k = 0
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply,
        mul_apply_eq_sum_subtype (hC i), sub_eq_zero]
      have hcoeff (j : {j // j < i}) : C i j = c i j := dif_pos j.2
      simpa only [hcoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        using (congrFun (hc i) ⟨k, hki⟩).symm
    · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul H (hH.det_eq_one ▸ isUnit_one), Matrix.one_mul]

/-- **Column inclusion characterizes LU with a unit upper factor.** Column $i$ restricted to
rows before $i$ belongs to the span of the preceding columns on those rows exactly when the
matrix has a lower triangular factor times a unit upper triangular factor.
[HornJohnson2013, Theorem 3.5.3]. -/
theorem exists_isLowerTriangular_isUnitUpperTriangular_iff_forall_mem_span (A : Matrix ι ι R) :
    (∃ L U : Matrix ι ι R, L.IsLowerTriangular ∧ IsUnitUpperTriangular U ∧ A = L * U) ↔
      ∀ i : ι, (fun k : {k // k < i} => A k i) ∈
        Submodule.span R (Set.range fun j : {j // j < i} => fun k : {k // k < i} => A k j) := by
  change _ ↔ ∀ i : ι, (fun k : {k // k < i} => Aᵀ i k) ∈
    Submodule.span R (Set.range fun j : {j // j < i} => fun k : {k // k < i} => Aᵀ j k)
  rw [← exists_isLU_iff_forall_mem_span Aᵀ]
  constructor
  · rintro ⟨L, U, hL, hU, rfl⟩
    refine ⟨Uᵀ, Lᵀ, ⟨fun i j hij => hU.1 (i := j) (j := i) hij, hU.2⟩,
      fun i j hij => hL (i := j) (j := i) hij, Matrix.transpose_mul _ _⟩
  · rintro ⟨L, U, hLU⟩
    refine ⟨Uᵀ, Lᵀ, fun i j hij => hLU.2 (i := j) (j := i) hij,
      isUnitUpperTriangular_transpose_iff.mpr hLU.1, ?_⟩
    simpa only [Matrix.transpose_transpose, Matrix.transpose_mul] using
      congrArg Matrix.transpose hLU.eq_mul

end RowInclusion

end NLAlib
