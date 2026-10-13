/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.GaussState

/-!
# The LU factorization

`NLAlib.IsLU A L U` says that `A = L * U` with `L` unit lower triangular and `U` upper
triangular. The factorization of a nonsingular matrix is unique, and exists exactly when the
leading principal minors are nonzero; the pivots are ratios of consecutive leading minors. With a
row permutation it always exists, and partial pivoting bounds the entries of the factors.

Leading principal minors are `principalMinor A (Finset.Iic i)`.

## Main definitions

* `NLAlib.IsLU`: the factorization predicate.
* `NLAlib.luLower`, `NLAlib.luUpper`: the factors computed by elimination without pivoting, for a
  matrix indexed by `Fin n` over a field.

## Main results

* `NLAlib.IsLU.unique`, `NLAlib.IsLU.det_eq_prod`, `NLAlib.IsLU.principalMinor_eq_prod`.
* `NLAlib.exists_isLU_iff_forall_principalMinor_ne_zero`: existence for nonsingular matrices.
* `NLAlib.exists_isLU_of_forall_principalMinor_ne_zero_of_le_rank`: existence from the leading
  minors up to the rank.
* `NLAlib.isLU_luLower_luUpper`: elimination computes the factorization.
* `NLAlib.eq_luLower_mul_luUpper`: `A = luLower A * luUpper A` when zero pivots have zeros below.
* `NLAlib.exists_perm_isLU_norm_le`: partial pivoting, with the growth bound `2 ^ (n - 1)`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {R K : Type*} {n : Type*} [LinearOrder n] [Fintype n]

/-- `IsLU A L U`: **`A = L * U` is an LU factorization**, with `L` unit lower triangular and `U`
upper triangular. [GolubVanLoan2013, §3.2]; [HornJohnson2013, §3.5].
Port of `NLAlib.IsLU`, there over `ℝ`. -/
structure IsLU [Semiring R] (A L U : Matrix n n R) : Prop where
  /-- The left factor is unit lower triangular. -/
  isUnitLowerTriangular : IsUnitLowerTriangular L
  /-- The right factor is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- The matrix is the product of the factors. -/
  eq_mul : A = L * U

section CommRing

variable [CommRing R] [DecidableEq n] {A L U : Matrix n n R}

/-- The determinant is the product of the pivots. Port of `NLAlib.IsLU.det_eq_prod`. -/
theorem IsLU.det_eq_prod (h : IsLU A L U) : A.det = ∏ i, U i i := by
  rw [h.eq_mul, Matrix.det_mul, h.isUnitLowerTriangular.det_eq_one, one_mul,
    Matrix.det_of_isUpperTriangular h.isUpperTriangular]

/-- A matrix with an LU factorization is nonsingular exactly when its pivots are units. -/
theorem IsLU.isUnit_det_iff (h : IsLU A L U) : IsUnit A.det ↔ ∀ i, IsUnit (U i i) := by
  rw [h.eq_mul, Matrix.det_mul, h.isUnitLowerTriangular.det_eq_one, one_mul]
  exact h.isUpperTriangular.isUnit_det_iff

omit [DecidableEq n] in
/-- The leading blocks of an LU factorization are LU factorizations of the leading blocks.
Port of `NLAlib.IsLU.leadingSubmatrix`. -/
theorem IsLU.submatrix_of_isLowerSet (h : IsLU A L U) {s : Finset n}
    (hs : IsLowerSet (s : Set n)) :
    IsLU (A.submatrix (Subtype.val : s → n) (Subtype.val : s → n))
      (L.submatrix (Subtype.val : s → n) (Subtype.val : s → n))
      (U.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) := by
  refine ⟨⟨h.isUnitLowerTriangular.isLowerTriangular.submatrix_of_strictMono
    (Subtype.strictMono_coe _), fun i => h.isUnitLowerTriangular.apply_self _⟩,
    h.isUpperTriangular.submatrix_of_strictMono (Subtype.strictMono_coe _), ?_⟩
  rw [h.eq_mul]
  exact h.isUnitLowerTriangular.isLowerTriangular.submatrix_mul_of_isLowerSet U hs

/-- **Principal minors on lower sets.** For an LU factorization and a lower set `s` of indices,
the principal minor of `A` on `s` is the product of the pivots in `s`.
Port of `NLAlib.IsLU.leadingMinor_eq_prod`, there for leading blocks of a matrix on `Fin`. -/
theorem IsLU.principalMinor_eq_prod (h : IsLU A L U) {s : Finset n}
    (hs : IsLowerSet (s : Set n)) : principalMinor A s = ∏ i ∈ s, U i i := by
  rw [principalMinor, (h.submatrix_of_isLowerSet hs).det_eq_prod]
  exact Finset.prod_coe_sort s fun i => U i i

/-- **The LU factorization of a nonsingular matrix is unique.**
[HornJohnson2013, Corollary 3.5.6]. Port of `NLAlib.IsLU.unique`. -/
theorem IsLU.unique {L' U' : Matrix n n R} (hA : IsUnit A.det) (h : IsLU A L U)
    (h' : IsLU A L' U') : L = L' ∧ U = U' := by
  have hU : IsUnit U.det := by
    rwa [h.eq_mul, Matrix.det_mul, h.isUnitLowerTriangular.det_eq_one, one_mul] at hA
  have hL : IsUnit L.det := by
    rw [h.isUnitLowerTriangular.det_eq_one]
    exact isUnit_one
  have hL' : IsUnit L'.det := by
    rw [h'.isUnitLowerTriangular.det_eq_one]
    exact isUnit_one
  have hLU : L * U = L' * U' := h.eq_mul.symm.trans h'.eq_mul
  have key : L'⁻¹ * L = U' * U⁻¹ := by
    calc L'⁻¹ * L = L'⁻¹ * L * (U * U⁻¹) := by rw [Matrix.mul_nonsing_inv U hU, Matrix.mul_one]
      _ = L'⁻¹ * (L * U) * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L'⁻¹ * (L' * U') * U⁻¹ := by rw [hLU]
      _ = U' * U⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L' hL', Matrix.one_mul]
  have hup : (L'⁻¹ * L).IsUpperTriangular := by
    rw [key]
    exact Matrix.BlockTriangular.mul h'.isUpperTriangular h.isUpperTriangular.inv
  have h1 : L'⁻¹ * L = 1 :=
    (h'.isUnitLowerTriangular.inv.mul h.isUnitLowerTriangular).eq_one_of_isUpperTriangular hup
  have hLL : L = L' := by
    calc L = L' * (L'⁻¹ * L) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv L' hL', Matrix.one_mul]
      _ = L' := by rw [h1, Matrix.mul_one]
  refine ⟨hLL, ?_⟩
  have hLU' : L * U = L * U' := by rw [hLU, hLL]
  calc U = L⁻¹ * (L * U) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hL, Matrix.one_mul]
    _ = L⁻¹ * (L * U') := by rw [hLU']
    _ = U' := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hL, Matrix.one_mul]

/-- **Solving through an LU factorization**: `A x = b` exactly when `U x = L⁻¹ b`.
[GolubVanLoan2013, §3.2]. -/
theorem IsLU.mulVec_eq_iff (h : IsLU A L U) {x b : n → R} :
    A *ᵥ x = b ↔ U *ᵥ x = L⁻¹ *ᵥ b := by
  have hL : IsUnit L.det := by
    rw [h.isUnitLowerTriangular.det_eq_one]
    exact isUnit_one
  rw [h.eq_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hL, Matrix.one_mulVec]
  · intro hx
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv L hL, Matrix.one_mulVec]

end CommRing

/-- An LU factorization transported along an order isomorphism of the index type. -/
private theorem IsLU.submatrix_orderIso [Semiring R] {m : Type*} [LinearOrder m] [Fintype m]
    {A L U : Matrix n n R} (h : IsLU A L U) (e : m ≃o n) :
    IsLU (A.submatrix e e) (L.submatrix e e) (U.submatrix e e) := by
  refine ⟨⟨h.isUnitLowerTriangular.isLowerTriangular.submatrix_of_strictMono e.strictMono,
    fun i => h.isUnitLowerTriangular.apply_self _⟩,
    h.isUpperTriangular.submatrix_of_strictMono e.strictMono, ?_⟩
  rw [h.eq_mul]
  exact (Matrix.submatrix_mul_equiv L U e e.toEquiv e).symm

/-- A matrix has an LU factorization if its transport along an order isomorphism has one. -/
private theorem exists_isLU_of_orderIso [Semiring R] {m : Type*} [LinearOrder m] [Fintype m]
    {A : Matrix n n R} (e : m ≃o n) (h : ∃ L U, IsLU (A.submatrix e e) L U) :
    ∃ L U, IsLU A L U := by
  obtain ⟨L, U, hLU⟩ := h
  refine ⟨L.submatrix e.symm e.symm, U.submatrix e.symm e.symm, ?_⟩
  have h := hLU.submatrix_orderIso e.symm
  have hA : (A.submatrix e e).submatrix e.symm e.symm = A := by
    ext i j
    simp only [Matrix.submatrix_apply, OrderIso.apply_symm_apply]
  rwa [hA] at h

omit [Fintype n] in
/-- Principal minors transported along an order isomorphism of the index type. -/
private theorem principalMinor_submatrix_orderIso [CommRing R] [DecidableEq n] {m : Type*}
    [LinearOrder m] (A : Matrix n n R) (e : m ≃o n) {s : Finset m} {t : Finset n}
    (h : e '' (s : Set m) = t) : principalMinor (A.submatrix e e) s = principalMinor A t := by
  rw [principalMinor, Matrix.submatrix_submatrix]
  refine det_submatrix_eq_principalMinor A (e.injective.comp Subtype.val_injective) ?_
  rw [Set.range_comp, Subtype.range_coe, h]

/-! ### Elimination without pivoting -/

section Recursion

variable [Field K] {n : ℕ}

/-- The unit lower triangular factor computed by elimination without pivoting: column `j` holds
the multipliers of step `j`. Port of `NLAlib.lu`, first component. -/
def luLower (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if j < i then gaussState A j i j / gaussState A j j j else if i = j then 1 else 0

/-- The upper triangular factor computed by elimination without pivoting: row `i` is the pivot
row of step `i`. Port of `NLAlib.lu`, second component. -/
def luUpper (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if i ≤ j then gaussState A i i j else 0

/-- The lower factor of elimination is unit lower triangular.
Port of `NLAlib.isUnitLowerTriangular_lu_fst`. -/
theorem isUnitLowerTriangular_luLower (A : Matrix (Fin n) (Fin n) K) :
    IsUnitLowerTriangular (luLower A) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := hij
    simp only [luLower, Matrix.of_apply, if_neg hij'.not_gt, if_neg hij'.ne]
  · simp only [luLower, Matrix.of_apply, lt_self_iff_false, if_false, if_true]

/-- The upper factor of elimination is upper triangular.
Port of `NLAlib.isUpperTriangular_lu_snd`. -/
theorem isUpperTriangular_luUpper (A : Matrix (Fin n) (Fin n) K) :
    (luUpper A).IsUpperTriangular := by
  intro i j hij
  have hij' : j < i := hij
  simp only [luUpper, Matrix.of_apply, if_neg hij'.not_ge]

/-- The diagonal of the upper factor holds the pivots. -/
@[simp]
theorem luUpper_apply_self (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    luUpper A i i = gaussState A i i i := by
  simp only [luUpper, Matrix.of_apply, le_refl, if_true]

/-- The entries of the product of the factors computed by elimination. -/
private theorem luLower_mul_luUpper_apply (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (luLower A * luUpper A) i j =
      (∑ l ∈ Finset.univ.filter (fun l : Fin n => l < i ∧ l ≤ j),
        (gaussState A l l l)⁻¹ * (gaussState A l i l * gaussState A l l j)) +
      if i ≤ j then gaussState A i i j else 0 := by
  have hterm : ∀ l : Fin n, luLower A i l * luUpper A l j =
      (if l < i ∧ l ≤ j then
        (gaussState A l l l)⁻¹ * (gaussState A l i l * gaussState A l l j) else 0) +
      if l = i then (if i ≤ j then gaussState A i i j else 0) else 0 := by
    intro l
    simp only [luLower, luUpper, Matrix.of_apply]
    rcases lt_trichotomy l i with hl | rfl | hl
    · by_cases hlj : l ≤ j
      · simp only [hl, hlj, hl.ne, and_self, if_true, if_false, add_zero]
        ring
      · simp only [hl, hlj, hl.ne, and_false, if_true, if_false, mul_zero, add_zero]
    · simp only [lt_self_iff_false, if_false, if_true, false_and, one_mul, zero_add]
    · simp only [hl.not_gt, hl.ne, hl.ne', false_and, if_false, zero_mul, add_zero]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib,
    Finset.sum_filter, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]

/-- Elimination factors the matrix as soon as a zero pivot has only zeros below it. -/
theorem eq_luLower_mul_luUpper {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ j i : Fin n, j < i → gaussState A j j j = 0 → gaussState A j i j = 0) :
    A = luLower A * luUpper A := by
  ext i j
  rw [luLower_mul_luUpper_apply]
  rcases le_or_gt i j with hij | hij
  · have ht := congrFun (congrFun (eq_gaussState_add_sum A (i : ℕ)) i) j
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul] at ht
    have hfil : Finset.univ.filter (fun l : Fin n => l < i ∧ l ≤ j) =
        Finset.univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def] at hij ⊢
      omega
    rw [if_pos hij, hfil, add_comm]
    exact ht
  · have ht := congrFun (congrFun (eq_gaussState_add_sum A ((j : ℕ) + 1)) i) j
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul] at ht
    have hfil : Finset.univ.filter (fun l : Fin n => l < i ∧ l ≤ j) =
        Finset.univ.filter (fun l : Fin n => (l : ℕ) < (j : ℕ) + 1) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def] at hij ⊢
      omega
    have hz : gaussState A ((j : ℕ) + 1) i j = 0 := by
      rw [gaussState_succ A j.2]
      by_cases hp : gaussState A j j j = 0
      · rw [eliminationStep_eq_self_of_apply_self_eq_zero hp]
        exact h j i hij hp
      · exact eliminationStep_apply_pivot_right hp i
    rw [if_neg hij.not_ge, hfil, add_zero]
    rw [hz, zero_add] at ht
    exact ht

/-- **Elimination computes the LU factorization** when every pivot but the last is nonzero.
Port of `NLAlib.isLU_lu`. -/
theorem isLU_luLower_luUpper {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ i : Fin n, (i : ℕ) + 1 < n → luUpper A i i ≠ 0) :
    IsLU A (luLower A) (luUpper A) := by
  refine ⟨isUnitLowerTriangular_luLower A, isUpperTriangular_luUpper A,
    eq_luLower_mul_luUpper fun j i hji hj => ?_⟩
  refine absurd hj ?_
  rw [← luUpper_apply_self]
  exact h j (by have := Fin.lt_def.mp hji; omega)

/-- Elimination computes the LU factorization of a matrix whose proper leading principal minors
are nonzero. Port of `NLAlib.isLU_lu_of_forall_leadingMinor_ne_zero`. -/
theorem isLU_luLower_luUpper_of_forall_principalMinor_ne_zero {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ i, principalMinor A (Finset.Iio i) ≠ 0) : IsLU A (luLower A) (luUpper A) := by
  refine isLU_luLower_luUpper fun i hi => ?_
  rw [luUpper_apply_self]
  refine (forall_gaussState_ne_zero_iff A i).mpr (fun l hl => ?_) i le_rfl
  have hl' : (l : ℕ) + 1 < n := by have := Fin.le_def.mp hl; omega
  have hset : Finset.Iic l = Finset.Iio (⟨(l : ℕ) + 1, hl'⟩ : Fin n) := by
    ext x
    simp only [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def]
    omega
  rw [hset]
  exact h _

/-- **Elimination runs without a zero pivot exactly when all leading principal minors are
nonzero.** Port of `NLAlib.luSucceeds_iff_forall_leadingMinor_ne_zero`. -/
theorem forall_luUpper_apply_self_ne_zero_iff (A : Matrix (Fin n) (Fin n) K) :
    (∀ i, luUpper A i i ≠ 0) ↔ ∀ i, principalMinor A (Finset.Iic i) ≠ 0 := by
  simp only [luUpper_apply_self]
  rcases n with _ | n
  · exact ⟨fun _ i => i.elim0, fun _ i => i.elim0⟩
  · have h := forall_gaussState_ne_zero_iff A (Fin.last n)
    exact ⟨fun hp i => h.mp (fun l _ => hp l) i (Fin.le_last i),
      fun hm i => h.mpr (fun l _ => hm l) i (Fin.le_last i)⟩

/-- Elimination computes the LU factorization of a matrix whose leading principal minors up to
the rank are nonzero: the state after `rank A` steps is zero. -/
private theorem isLU_luLower_luUpper_of_le_rank {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ i : Fin n, (i : ℕ) + 1 ≤ A.rank → principalMinor A (Finset.Iic i) ≠ 0) :
    IsLU A (luLower A) (luUpper A) := by
  refine ⟨isUnitLowerTriangular_luLower A, isUpperTriangular_luUpper A,
    eq_luLower_mul_luUpper fun j i _ hj => ?_⟩
  have hp : ∀ l : Fin n, (l : ℕ) < A.rank → gaussState A l l l ≠ 0 := fun l hl =>
    (forall_gaussState_ne_zero_iff A l).mpr
      (fun l' hl' => h l' (by have := Fin.le_def.mp hl'; omega)) l le_rfl
  have hr : A.rank ≤ n := A.rank_le_width
  have h0 : gaussState A A.rank = 0 := by
    have hrank := rank_gaussState_add A hr hp
    exact Matrix.rank_eq_zero.mp (by omega)
  have hj' : A.rank ≤ (j : ℕ) := not_lt.mp fun hlt => hp j hlt hj
  rw [gaussState_eq_zero_of_le h0 hj']
  rfl

/-- A row permutation after which every pivot of elimination maximises a given weight over the
entries below it. -/
theorem exists_perm_forall_weight_gaussState_le (w : K → ℝ) (A : Matrix (Fin n) (Fin n) K) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j i : Fin n, j ≤ i →
      w (gaussState (A.submatrix σ id) j i j) ≤ w (gaussState (A.submatrix σ id) j j j) := by
  have hs : ∀ (σ τ : Equiv.Perm (Fin n)) (j : Fin n), (∀ l : Fin n, l < j → τ l = l) →
      ∀ i, w (gaussState (A.submatrix (τ.trans σ) id) j i j) =
        w (gaussState (A.submatrix σ id) j (τ i) j) := by
    intro σ τ j hτ i
    have hsub : A.submatrix (τ.trans σ) id = (A.submatrix σ id).submatrix τ id := rfl
    rw [hsub, gaussState_submatrix_left _ τ j fun l hl => hτ l (Fin.lt_def.mpr hl)]
    rfl
  obtain ⟨σ, hσ⟩ := exists_perm_forall_le_apply_self
    (fun σ j i => w (gaussState (A.submatrix σ id) j i j)) hs n
  exact ⟨σ, fun j i hji => hσ j i j.2 hji⟩

/-- Every square matrix indexed by `Fin n` is factored by elimination after a row
permutation. -/
private theorem exists_perm_isLU_luLower_luUpper (A : Matrix (Fin n) (Fin n) K) :
    ∃ σ : Equiv.Perm (Fin n),
      IsLU (A.submatrix σ id) (luLower (A.submatrix σ id)) (luUpper (A.submatrix σ id)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_forall_weight_gaussState_le (fun x : K => if x = 0 then 0 else 1) A
  refine ⟨σ, isUnitLowerTriangular_luLower _, isUpperTriangular_luUpper _,
    eq_luLower_mul_luUpper fun j i hji hj => ?_⟩
  have h := hσ j i hji.le
  rw [hj, if_pos rfl] at h
  by_contra hne
  rw [if_neg hne] at h
  exact absurd h (by norm_num)

/-- Entries of the states of elimination with partial pivoting at most double at each step. -/
theorem norm_gaussState_apply_le {𝕜 : Type*} [RCLike 𝕜] {B : Matrix (Fin n) (Fin n) 𝕜} {M : ℝ}
    (hM : ∀ i j, ‖B i j‖ ≤ M)
    (hB : ∀ j i : Fin n, j ≤ i → ‖gaussState B j i j‖ ≤ ‖gaussState B j j j‖) (k : ℕ)
    (i l : Fin n) (hk : k ≤ (i : ℕ)) : ‖gaussState B k i l‖ ≤ 2 ^ k * M := by
  induction k generalizing i l with
  | zero => simpa using hM i l
  | succ k ih =>
    have hkn : k < n := by omega
    have h1 := ih i l (by omega)
    have h2 := ih ⟨k, hkn⟩ l le_rfl
    have h3 : ‖(gaussState B k ⟨k, hkn⟩ ⟨k, hkn⟩)⁻¹ * gaussState B k i ⟨k, hkn⟩‖ ≤ 1 := by
      have hle := hB ⟨k, hkn⟩ i (Fin.le_def.mpr (by simp only; omega))
      rw [norm_mul, norm_inv]
      by_cases h0 : ‖gaussState B k ⟨k, hkn⟩ ⟨k, hkn⟩‖ = 0
      · rw [h0, inv_zero, zero_mul]
        exact zero_le_one
      · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)), mul_one]
        exact hle
    rw [gaussState_succ B hkn, eliminationStep_apply, ← mul_assoc]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, pow_succ]
    nlinarith [mul_le_mul h3 h2 (norm_nonneg _) zero_le_one]

/-- Partial pivoting for a matrix indexed by `Fin n`. -/
private theorem exists_perm_isLU_norm_le_fin {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix (Fin n) (Fin n) 𝕜) {M : ℝ} (hM : ∀ i j, ‖A i j‖ ≤ M) :
    ∃ σ : Equiv.Perm (Fin n),
      IsLU (A.submatrix σ id) (luLower (A.submatrix σ id)) (luUpper (A.submatrix σ id)) ∧
      (∀ i j, ‖luLower (A.submatrix σ id) i j‖ ≤ 1) ∧
      ∀ i j, ‖luUpper (A.submatrix σ id) i j‖ ≤ 2 ^ (n - 1) * M := by
  obtain ⟨σ, hσ⟩ := exists_perm_forall_weight_gaussState_le (fun x : 𝕜 => ‖x‖) A
  refine ⟨σ, ⟨isUnitLowerTriangular_luLower _, isUpperTriangular_luUpper _,
    eq_luLower_mul_luUpper fun j i hji hj => ?_⟩, fun i j => ?_, fun i j => ?_⟩
  · have h := hσ j i hji.le
    rw [hj, norm_zero] at h
    exact norm_le_zero_iff.mp h
  · simp only [luLower, Matrix.of_apply]
    split_ifs with h1 h2
    · rw [norm_div]
      exact div_le_one_of_le₀ (hσ j i h1.le) (norm_nonneg _)
    · rw [norm_one]
    · rw [norm_zero]
      exact zero_le_one
  · have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i j)
    simp only [luUpper, Matrix.of_apply]
    split_ifs with h1
    · refine (norm_gaussState_apply_le (fun a b => hM (σ a) b) hσ i i j le_rfl).trans ?_
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ one_le_two (by have := i.2; omega)) hM0
    · rw [norm_zero]
      positivity

end Recursion

/-! ### Existence -/

section Field

variable [Field K] [DecidableEq n] [LocallyFiniteOrderBot n]

/-- A matrix whose proper leading principal minors are nonzero has an LU factorization.
Port of `NLAlib.exists_isLU_of_forall_leadingMinor_ne_zero`, there over `ℝ`. -/
theorem exists_isLU_of_forall_principalMinor_ne_zero (A : Matrix n n K)
    (h : ∀ i, principalMinor A (Finset.Iio i) ≠ 0) : ∃ L U, IsLU A L U := by
  refine exists_isLU_of_orderIso (Fintype.orderIsoFinOfCardEq n rfl) ⟨_, _,
    isLU_luLower_luUpper_of_forall_principalMinor_ne_zero fun i => ?_⟩
  rw [principalMinor_submatrix_orderIso A _
    (t := Finset.Iio (Fintype.orderIsoFinOfCardEq n rfl i))
    (by rw [Finset.coe_Iio, Finset.coe_Iio, OrderIso.image_Iio])]
  exact h _

/-- **A matrix whose leading principal minors up to its rank are nonzero has an LU
factorization.** [HornJohnson2013, Theorem 3.5.2].
Port of `NLAlib.exists_unit_triangular_factorizations_of_leading_minors_through_rank`. -/
theorem exists_isLU_of_forall_principalMinor_ne_zero_of_le_rank (A : Matrix n n K)
    (h : ∀ i, (Finset.Iic i).card ≤ A.rank → principalMinor A (Finset.Iic i) ≠ 0) :
    ∃ L U, IsLU A L U := by
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  refine exists_isLU_of_orderIso e ⟨_, _, isLU_luLower_luUpper_of_le_rank fun i hi => ?_⟩
  have himg : e '' ((Finset.Iic i : Finset (Fin (Fintype.card n))) : Set _) =
      (Finset.Iic (e i) : Finset n) := by
    rw [Finset.coe_Iic, Finset.coe_Iic, OrderIso.image_Iic]
  rw [principalMinor_submatrix_orderIso A e himg]
  refine h _ ?_
  have hcard : (Finset.Iic (e i)).card = (i : ℕ) + 1 := by
    rw [← Fin.card_Iic, ← Finset.card_image_of_injective _ e.injective]
    congr 1
    exact Finset.coe_injective (by rw [Finset.coe_image, himg])
  rw [hcard]
  exact hi.trans_eq (Matrix.rank_submatrix A e.toEquiv e.toEquiv)

/-- **A nonsingular matrix has an LU factorization exactly when its leading principal minors
are nonzero.** [HornJohnson2013, Corollary 3.5.5].
Port of `NLAlib.exists_isLU_iff_forall_leadingMinor_ne_zero`, there over `ℝ`.
Result: lu-existence -/
theorem exists_isLU_iff_forall_principalMinor_ne_zero {A : Matrix n n K} (hA : IsUnit A.det) :
    (∃ L U, IsLU A L U) ↔ ∀ i, principalMinor A (Finset.Iic i) ≠ 0 := by
  constructor
  · rintro ⟨L, U, h⟩ i
    rw [h.principalMinor_eq_prod (by rw [Finset.coe_Iic]; exact isLowerSet_Iic i)]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => (h.isUnit_det_iff.mp hA j).ne_zero
  · exact fun h => exists_isLU_of_forall_principalMinor_ne_zero_of_le_rank A fun i _ => h i

omit [DecidableEq n] [LocallyFiniteOrderBot n] in
/-- **Every square matrix has an LU factorization after a row permutation.**
[GolubVanLoan2013, Theorem 3.4.1 context]. Port of `NLAlib.isPLU_luPartialPivot`, as an
existence statement over any field. -/
theorem exists_perm_isLU (A : Matrix n n K) :
    ∃ (σ : Equiv.Perm n) (L U : Matrix n n K), IsLU (A.submatrix σ id) L U := by
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  obtain ⟨σ, hσ⟩ := exists_perm_isLU_luLower_luUpper (A.submatrix e e)
  have h := hσ.submatrix_orderIso e.symm
  have hA : ((A.submatrix e e).submatrix σ id).submatrix e.symm e.symm =
      A.submatrix ((e.symm.toEquiv.trans σ).trans e.toEquiv) id := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, OrderIso.apply_symm_apply, Equiv.trans_apply,
      RelIso.coe_fn_toEquiv]
  rw [hA] at h
  exact ⟨_, _, _, h⟩

end Field

/-- **Partial pivoting.** Every square matrix has a row-permuted LU factorization in which the
entries of `L` are at most one in absolute value and the entries of `U` exceed those of `A` by a
factor at most `2 ^ (n - 1)`. [GolubVanLoan2013, §3.4.5]; [Higham2002, §9.3].
Port of `NLAlib.exists_isPLU_abs_le_one` and `NLAlib.abs_luPartialPivot_upper_le_two_pow`.
Result: partial-pivoting-growth -/
theorem exists_perm_isLU_norm_le {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜)
    {M : ℝ} (hM : ∀ i j, ‖A i j‖ ≤ M) :
    ∃ (σ : Equiv.Perm n) (L U : Matrix n n 𝕜), IsLU (A.submatrix σ id) L U ∧
      (∀ i j, ‖L i j‖ ≤ 1) ∧ ∀ i j, ‖U i j‖ ≤ 2 ^ (Fintype.card n - 1) * M := by
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  obtain ⟨σ, hσ, hL, hU⟩ := exists_perm_isLU_norm_le_fin (A.submatrix e e) fun i j => hM _ _
  have h := hσ.submatrix_orderIso e.symm
  have hA : ((A.submatrix e e).submatrix σ id).submatrix e.symm e.symm =
      A.submatrix ((e.symm.toEquiv.trans σ).trans e.toEquiv) id := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, OrderIso.apply_symm_apply, Equiv.trans_apply,
      RelIso.coe_fn_toEquiv]
  rw [hA] at h
  exact ⟨_, _, _, h, fun i j => hL _ _, fun i j => hU _ _⟩

end NLAlib
