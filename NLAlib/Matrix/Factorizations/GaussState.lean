/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Elimination

/-!
# Gaussian elimination in the natural order

`NLAlib.gaussState A k` is the matrix after eliminating the first `k` pivots of a matrix indexed
by `Fin n`, in the natural order. An algorithm is a total recursion; its breakdown is a zero
pivot, and its correctness theorem assumes nonzero pivots. The LU and Cholesky factors are read
off this sequence.

## Main definitions

* `NLAlib.gaussState`: the sequence of matrices produced by elimination in the natural order.

## Main results

* `NLAlib.principalMinor_eq_apply_self_mul_principalMinor_eliminationStep`: one elimination step
  factors the pivot out of a principal minor.
* `NLAlib.eq_gaussState_add_sum`: the telescoping identity, with no assumption on the pivots.
* `NLAlib.gaussState_apply_eq_zero_of_lt_left`, `NLAlib.gaussState_apply_eq_zero_of_lt_right`:
  the zero pattern while the pivots are nonzero.
* `NLAlib.rank_gaussState_add`: each step at a nonzero pivot lowers the rank by one.
* `NLAlib.principalMinor_Iic_eq_prod_gaussState`: a leading principal minor is the product of
  the pivots.
* `NLAlib.gaussState_apply_self_mul_principalMinor_Iio`: a pivot is the ratio of consecutive
  leading principal minors.
* `NLAlib.forall_gaussState_ne_zero_iff`: nonzero pivots are nonzero leading principal minors.
* `Matrix.PosDef.gaussState_apply_self_pos`: the pivots of a positive definite matrix are
  positive.
* `NLAlib.gaussState_submatrix`, `NLAlib.gaussState_submatrix_left`: elimination commutes with
  a reindexing that fixes the pivots used.
* `NLAlib.exists_perm_forall_le_apply_self`: greedy pivoting.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {K : Type*} [Field K] {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-- **A principal minor through an elimination step.** Eliminating a nonzero pivot `t` inside
`s` factors the pivot out of the principal minor on `s`: what remains is the principal minor of
the eliminated matrix on `s.erase t`. -/
theorem principalMinor_eq_apply_self_mul_principalMinor_eliminationStep [DecidableEq n]
    {A : Matrix n n K} {s : Finset n} {t : n} (hts : t ∈ s) (ht : A t t ≠ 0) :
    principalMinor A s = A t t * principalMinor (eliminationStep A t) (s.erase t) := by
  have h := det_eq_apply_self_mul_det_eliminationStep
    (A := A.submatrix (Subtype.val : s → n) Subtype.val) (t := ⟨t, hts⟩) ht
  rw [eliminationStep_submatrix, Matrix.submatrix_submatrix] at h
  rw [principalMinor, h]
  congr 1
  refine det_submatrix_eq_principalMinor _
    (f := (Subtype.val : s → n) ∘ (Subtype.val : {i : s // i ≠ ⟨t, hts⟩} → s))
    (Subtype.val_injective.comp Subtype.val_injective) ?_
  ext x
  simp only [Set.mem_range, Function.comp_apply, Subtype.exists, Finset.coe_erase,
    Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff, ne_eq, Subtype.mk.injEq]
  exact ⟨fun ⟨a, ha, hne, hax⟩ => hax ▸ ⟨ha, hne⟩, fun ⟨hx, hne⟩ => ⟨x, hx, hne, rfl⟩⟩

/-! ### Elimination in the natural order -/

/-- The matrix after eliminating the pivots `0, …, k - 1` of a matrix indexed by `Fin n`, in this
order. Steps beyond `n` do nothing. -/
def gaussState {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => A
  | k + 1 => if h : k < n then eliminationStep (gaussState A k) ⟨k, h⟩ else gaussState A k

section GaussState

variable {n : ℕ}

/-- Elimination starts from the matrix. -/
@[simp]
theorem gaussState_zero (A : Matrix (Fin n) (Fin n) K) : gaussState A 0 = A :=
  rfl

/-- One more step of elimination. -/
theorem gaussState_succ (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (h : k < n) :
    gaussState A (k + 1) = eliminationStep (gaussState A k) ⟨k, h⟩ := by
  rw [gaussState, dif_pos h]

/-- A step beyond the dimension does nothing. -/
private theorem gaussState_succ_of_le (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (h : n ≤ k) :
    gaussState A (k + 1) = gaussState A k := by
  rw [gaussState, dif_neg (not_lt.mpr h)]

private theorem filter_lt_succ {k : ℕ} (h : k < n) :
    Finset.univ.filter (fun j : Fin n => (j : ℕ) < k + 1) =
      insert ⟨k, h⟩ (Finset.univ.filter fun j : Fin n => (j : ℕ) < k) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

private theorem notMem_filter_lt {k : ℕ} (h : k < n) :
    (⟨k, h⟩ : Fin n) ∉ Finset.univ.filter fun j : Fin n => (j : ℕ) < k := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_self_iff_false, not_false_eq_true]

private theorem Iic_eq_filter_lt (i : Fin n) :
    Finset.Iic i = Finset.univ.filter fun l : Fin n => (l : ℕ) < i + 1 := by
  ext l
  simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
  omega

private theorem Iio_eq_filter_lt (i : Fin n) :
    Finset.Iio i = Finset.univ.filter fun l : Fin n => (l : ℕ) < i := by
  ext l
  simp only [Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]

/-- Elimination in the natural order is elimination along the list `0, …, k - 1`. -/
theorem gaussState_eq_foldl (A : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    gaussState A k = ((List.finRange n).take k).foldl eliminationStep A := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < n
    · have hk : k < (List.finRange n).length := by rwa [List.length_finRange]
      rw [gaussState_succ A h, ih, ← List.take_append_getElem hk, List.foldl_append,
        List.getElem_finRange]
      rfl
    · have hk : (List.finRange n).length ≤ k := by
        rw [List.length_finRange]
        exact not_lt.mp h
      rw [gaussState_succ_of_le A (not_lt.mp h), ih, List.take_of_length_le hk,
        List.take_of_length_le (hk.trans k.le_succ)]

/-- **The telescoping identity of elimination**: `A` is the current state plus the rank-one
matrices removed so far. It holds with no assumption on the pivots, since a zero pivot removes
nothing. -/
theorem eq_gaussState_add_sum (A : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    A = gaussState A k +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
        (gaussState A j j j)⁻¹ •
          Matrix.vecMulVec (fun i => gaussState A j i j) (gaussState A j j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases h : k < n
    · rw [filter_lt_succ h, Finset.sum_insert (notMem_filter_lt h), gaussState_succ A h,
        eliminationStep_eq_sub_smul_vecMulVec]
      conv_lhs => rw [ih]
      abel
    · have hfil : Finset.univ.filter (fun j : Fin n => (j : ℕ) < k + 1) =
          Finset.univ.filter (fun j : Fin n => (j : ℕ) < k) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hfil, gaussState_succ_of_le A (not_lt.mp h)]
      exact ih

/-- While the pivots are nonzero, the rows already eliminated are zero. -/
theorem gaussState_apply_eq_zero_of_lt_left (A : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (hp : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0) {i : Fin n} (hi : (i : ℕ) < k)
    (j : Fin n) : gaussState A k i j = 0 := by
  induction k generalizing j with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    have hp' : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0 := fun l hl =>
      hp l (Nat.lt_succ_of_lt hl)
    by_cases h : k < n
    · rw [gaussState_succ A h]
      by_cases hik : (i : ℕ) = k
      · obtain rfl : i = ⟨k, h⟩ := Fin.ext hik
        exact eliminationStep_apply_pivot_left (hp ⟨k, h⟩ (Nat.lt_succ_self k)) j
      · exact eliminationStep_apply_eq_zero_of_row (fun j => ih hp' (by omega) j) _ j
    · rw [gaussState_succ_of_le A (not_lt.mp h)]
      exact ih hp' (by omega) j

/-- While the pivots are nonzero, the columns already eliminated are zero. -/
theorem gaussState_apply_eq_zero_of_lt_right (A : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (hp : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0) (i : Fin n) {j : Fin n}
    (hj : (j : ℕ) < k) : gaussState A k i j = 0 := by
  induction k generalizing i with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    have hp' : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0 := fun l hl =>
      hp l (Nat.lt_succ_of_lt hl)
    by_cases h : k < n
    · rw [gaussState_succ A h]
      by_cases hjk : (j : ℕ) = k
      · obtain rfl : j = ⟨k, h⟩ := Fin.ext hjk
        exact eliminationStep_apply_pivot_right (hp ⟨k, h⟩ (Nat.lt_succ_self k)) i
      · exact eliminationStep_apply_eq_zero_of_col (fun i => ih hp' i (by omega)) _ i
    · rw [gaussState_succ_of_le A (not_lt.mp h)]
      exact ih hp' i (by omega)

/-- While the pivots are nonzero, each step lowers the rank by one. -/
theorem rank_gaussState_add (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k ≤ n)
    (hp : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0) :
    (gaussState A k).rank + k = A.rank := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < n := hk
    have h1 := rank_eliminationStep_add_one (hp ⟨k, h⟩ (Nat.lt_succ_self k))
    have h2 := ih (Nat.le_of_succ_le hk) fun l hl => hp l (Nat.lt_succ_of_lt hl)
    rw [gaussState_succ A h]
    change (eliminationStep (gaussState A k) ⟨k, h⟩).rank + 1 = (gaussState A k).rank at h1
    omega

/-- Leading principal minors through `k` elimination steps at nonzero pivots. -/
private theorem principalMinor_filter_lt_eq (A : Matrix (Fin n) (Fin n) K) {m k : ℕ}
    (hk : k ≤ m) (hm : m ≤ n) (hp : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0) :
    principalMinor A (Finset.univ.filter fun l : Fin n => (l : ℕ) < m) =
      (∏ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < k), gaussState A l l l) *
        principalMinor (gaussState A k)
          (Finset.univ.filter fun l : Fin n => k ≤ (l : ℕ) ∧ (l : ℕ) < m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : k < n := by omega
    have hmem : (⟨k, h⟩ : Fin n) ∈
        Finset.univ.filter fun l : Fin n => k ≤ (l : ℕ) ∧ (l : ℕ) < m := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, le_refl]
      omega
    have herase : (Finset.univ.filter fun l : Fin n => k ≤ (l : ℕ) ∧ (l : ℕ) < m).erase ⟨k, h⟩ =
        Finset.univ.filter fun l : Fin n => k + 1 ≤ (l : ℕ) ∧ (l : ℕ) < m := by
      ext l
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
        Fin.ext_iff]
      omega
    rw [ih (by omega) fun l hl => hp l (by omega),
      principalMinor_eq_apply_self_mul_principalMinor_eliminationStep hmem
        (hp ⟨k, h⟩ (Nat.lt_succ_self k)),
      ← gaussState_succ A h, herase, filter_lt_succ h, Finset.prod_insert (notMem_filter_lt h),
      ← mul_assoc, mul_comm (gaussState A (⟨k, h⟩ : Fin n) ⟨k, h⟩ ⟨k, h⟩)]

/-- A leading principal minor is the product of the pivots, when all but the last of them are
nonzero. -/
private theorem principalMinor_filter_lt_eq_prod (A : Matrix (Fin n) (Fin n) K) {m : ℕ}
    (hm : m ≤ n) (hp : ∀ l : Fin n, (l : ℕ) + 1 < m → gaussState A l l l ≠ 0) :
    principalMinor A (Finset.univ.filter fun l : Fin n => (l : ℕ) < m) =
      ∏ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < m), gaussState A l l l := by
  rcases m with _ | m
  · simp
  · have h : m < n := hm
    have hs : (Finset.univ.filter fun l : Fin n => m ≤ (l : ℕ) ∧ (l : ℕ) < m + 1) =
        {⟨m, h⟩} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [principalMinor_filter_lt_eq A (Nat.le_succ m) hm fun l hl => hp l (by omega), hs,
      principalMinor_singleton, filter_lt_succ h, Finset.prod_insert (notMem_filter_lt h),
      mul_comm]

/-- **Pivots and leading principal minors.** While the earlier pivots are nonzero, the leading
principal minor of order `i + 1` is the product of the first `i + 1` pivots.
Port of `NLAlib.leadingMinor_succ_eq_mul_leadingMinor_pivotSchur`, in closed form. -/
theorem principalMinor_Iic_eq_prod_gaussState (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (hp : ∀ l : Fin n, l < i → gaussState A l l l ≠ 0) :
    principalMinor A (Finset.Iic i) = ∏ l ∈ Finset.Iic i, gaussState A l l l := by
  rw [Iic_eq_filter_lt]
  exact principalMinor_filter_lt_eq_prod A i.2 fun l hl => hp l (Fin.lt_def.mpr (by omega))

/-- **A pivot is the ratio of consecutive leading principal minors**, while the earlier pivots
are nonzero. -/
theorem gaussState_apply_self_mul_principalMinor_Iio (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (hp : ∀ l : Fin n, l < i → gaussState A l l l ≠ 0) :
    gaussState A i i i * principalMinor A (Finset.Iio i) = principalMinor A (Finset.Iic i) := by
  rw [principalMinor_Iic_eq_prod_gaussState A i hp, Iio_eq_filter_lt,
    principalMinor_filter_lt_eq_prod A i.2.le fun l hl => hp l (Fin.lt_def.mpr (by omega)),
    ← Iio_eq_filter_lt, ← Finset.Iio_insert, Finset.prod_insert Finset.notMem_Iio_self]

/-- **The pivots up to `i` are nonzero exactly when the leading principal minors up to order
`i + 1` are nonzero.** -/
theorem forall_gaussState_ne_zero_iff (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    (∀ l : Fin n, l ≤ i → gaussState A l l l ≠ 0) ↔
      ∀ l : Fin n, l ≤ i → principalMinor A (Finset.Iic l) ≠ 0 := by
  constructor
  · intro h l hl
    rw [principalMinor_Iic_eq_prod_gaussState A l fun j hj => h j (hj.le.trans hl)]
    exact Finset.prod_ne_zero_iff.mpr fun j hj => h j ((Finset.mem_Iic.mp hj).trans hl)
  · intro h
    suffices H : ∀ (k : ℕ) (l : Fin n), (l : ℕ) = k → l ≤ i → gaussState A l l l ≠ 0 from
      fun l hl => H l l rfl hl
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro l hlk hl
      have hp : ∀ j : Fin n, j < l → gaussState A j j j ≠ 0 := fun j hj =>
        ih j (hlk ▸ Fin.lt_def.mp hj) j rfl (hj.le.trans hl)
      have hm := h l hl
      rw [principalMinor_Iic_eq_prod_gaussState A l hp] at hm
      exact Finset.prod_ne_zero_iff.mp hm l (Finset.mem_Iic.mpr le_rfl)

/-- The pivots of a positive definite matrix are positive. -/
theorem _root_.Matrix.PosDef.gaussState_apply_self_pos {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) (i : Fin n) : 0 < gaussState A i i i := by
  have hpos : ∀ s : Finset (Fin n), 0 < principalMinor A s := fun s =>
    (hA.submatrix Subtype.val_injective).det_pos
  suffices H : ∀ (k : ℕ) (l : Fin n), (l : ℕ) = k → 0 < gaussState A l l l from H i i rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro l hlk
    have hp : ∀ j : Fin n, j < l → gaussState A j j j ≠ 0 := fun j hj =>
      (ih j (hlk ▸ Fin.lt_def.mp hj) j rfl).ne'
    have hmul := gaussState_apply_self_mul_principalMinor_Iio A l hp
    have h1 := hpos (Finset.Iio l)
    have h2 := hpos (Finset.Iic l)
    have h3 : gaussState A l l l =
        principalMinor A (Finset.Iic l) * (principalMinor A (Finset.Iio l))⁻¹ := by
      rw [← hmul, mul_inv_cancel_right₀ h1.ne']
    rw [h3]
    exact mul_pos h2 (RCLike.inv_pos_of_pos h1)

/-- Once elimination reaches the zero matrix it stays there. -/
theorem gaussState_eq_zero_of_le {A : Matrix (Fin n) (Fin n) K} {k : ℕ}
    (h : gaussState A k = 0) {j : ℕ} (hkj : k ≤ j) : gaussState A j = 0 := by
  induction j, hkj using Nat.le_induction with
  | base => exact h
  | succ j _ ih =>
    by_cases hj : j < n
    · rw [gaussState_succ A hj, ih, eliminationStep_zero]
    · rw [gaussState_succ_of_le A (not_lt.mp hj)]
      exact ih

/-! ### Pivoting -/

/-- Elimination commutes with a reindexing of the rows that fixes the pivots used. -/
theorem gaussState_submatrix_left (A : Matrix (Fin n) (Fin n) K) (τ : Fin n → Fin n) (k : ℕ)
    (hτ : ∀ l : Fin n, (l : ℕ) < k → τ l = l) :
    gaussState (A.submatrix τ id) k = (gaussState A k).submatrix τ id := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun l hl => hτ l (Nat.lt_succ_of_lt hl)
    by_cases hk : k < n
    · rw [gaussState_succ _ hk, gaussState_succ _ hk, ih']
      ext a b
      simp only [eliminationStep_apply, Matrix.submatrix_apply, id_eq,
        hτ ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · rw [gaussState_succ_of_le _ (not_lt.mp hk), ih', gaussState_succ_of_le _ (not_lt.mp hk)]

/-- Elimination commutes with a simultaneous reindexing of the rows and columns that fixes the
pivots used. -/
theorem gaussState_submatrix (A : Matrix (Fin n) (Fin n) K) (τ : Fin n → Fin n) (k : ℕ)
    (hτ : ∀ l : Fin n, (l : ℕ) < k → τ l = l) :
    gaussState (A.submatrix τ τ) k = (gaussState A k).submatrix τ τ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun l hl => hτ l (Nat.lt_succ_of_lt hl)
    by_cases hk : k < n
    · rw [gaussState_succ _ hk, gaussState_succ _ hk, ih', eliminationStep_submatrix,
        hτ ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · rw [gaussState_succ_of_le _ (not_lt.mp hk), ih', gaussState_succ_of_le _ (not_lt.mp hk)]

/-- **Greedy pivoting.** Let `s σ j i` score the candidate `i` for the pivot position `j` after
the permutation `σ`, and suppose that composing `σ` with a permutation `τ` fixing the positions
before `j` permutes the scores at step `j` by `τ`. Then some permutation makes every pivot among
the first `k` maximal over the later positions: swap a maximiser into each position in turn.
This is the choice of pivots in partial pivoting and in diagonally pivoted Cholesky. -/
theorem exists_perm_forall_le_apply_self (s : Equiv.Perm (Fin n) → Fin n → Fin n → ℝ)
    (hs : ∀ (σ τ : Equiv.Perm (Fin n)) (j : Fin n), (∀ l : Fin n, l < j → τ l = l) →
      ∀ i, s (τ.trans σ) j i = s σ j (τ i)) (k : ℕ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j i : Fin n, (j : ℕ) < k → j ≤ i → s σ j i ≤ s σ j j := by
  induction k with
  | zero => exact ⟨1, fun j i hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨σ, hσ⟩ := ih
    by_cases hk : k < n
    · obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.Ici (⟨k, hk⟩ : Fin n))
        (s σ ⟨k, hk⟩) ⟨_, Finset.mem_Ici.mpr le_rfl⟩
      have hi₀' : k ≤ (i₀ : ℕ) := Fin.le_def.mp (Finset.mem_Ici.mp hi₀)
      have hτ : ∀ l : Fin n, (l : ℕ) < k → Equiv.swap (⟨k, hk⟩ : Fin n) i₀ l = l := fun l hl =>
        Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp only; omega))
          (Fin.ne_of_val_ne (by omega))
      have hge : ∀ (m : ℕ) (i : Fin n), m ≤ k → m ≤ (i : ℕ) →
          m ≤ ((Equiv.swap (⟨k, hk⟩ : Fin n) i₀ i : Fin n) : ℕ) := by
        intro m i hmk hmi
        rw [Equiv.swap_apply_def]
        split_ifs
        · omega
        · exact hmk
        · exact hmi
      refine ⟨(Equiv.swap ⟨k, hk⟩ i₀).trans σ, fun j i hj hji => ?_⟩
      have hτj : ∀ l : Fin n, l < j → Equiv.swap (⟨k, hk⟩ : Fin n) i₀ l = l := fun l hl =>
        hτ l (by have := Fin.lt_def.mp hl; omega)
      rw [hs σ _ j hτj, hs σ _ j hτj]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · rw [hτ j hjk]
        exact hσ j _ hjk (Fin.le_def.mpr (hge j i hjk.le (Fin.le_def.mp hji)))
      · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hjk
        rw [Equiv.swap_apply_left]
        exact hmax _ (Finset.mem_Ici.mpr (Fin.le_def.mpr (hge k i le_rfl (Fin.le_def.mp hji))))
    · exact ⟨σ, fun j i hj hji => hσ j i (by omega) hji⟩

end GaussState

end NLAlib
