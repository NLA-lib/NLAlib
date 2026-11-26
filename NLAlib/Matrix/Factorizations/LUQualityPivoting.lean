/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LUCompletePivoting
public import NLAlib.Matrix.Factorizations.LUGeneral

/-!
# LU under quantitative column pivots

A positive fraction of the active column maximum suffices for zero-column compatibility and
exact LU, including singular inputs. Independent active row and column exchanges preserve
previous quantitative column qualities. The lower multipliers are bounded by the reciprocal
quality fraction, with the diagonal covered when that fraction is at most one.

## Main results

* `NLAlib.isLU_luLower_luUpper_of_forall_mul_norm_le`: positive column quality implies exact LU.
* `NLAlib.norm_luLower_apply_le_inv`: the reciprocal-quality multiplier bound.
* `NLAlib.forall_mul_norm_gaussState_le_submatrix_left_right`: mixed prefix transport.
-/

@[expose] public section

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- A positive fraction of each pivot column's maximum forces zero pivots to have zero entries
below them, so the total canonical factors multiply to the input, even when it is singular. -/
theorem isLU_luLower_luUpper_of_forall_mul_norm_le {A : Matrix (Fin N) (Fin N) 𝕜}
    {α : ℝ} (hα : 0 < α)
    (h : ∀ j i : Fin N, j ≤ i → α * ‖gaussState A j i j‖ ≤ ‖gaussState A j j j‖) :
    IsLU A (luLower A) (luUpper A) := by
  refine isLU_luLower_luUpper_of_forall_eq_zero fun j i hji hp => ?_
  have hh := h j i hji.le
  rw [hp, norm_zero] at hh
  exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg (gaussState A j i j)])

/-- Positive column quality at most one bounds all canonical lower entries by its reciprocal.
Zero pivots use total division and need no nonbreakdown hypothesis. -/
theorem norm_luLower_apply_le_inv {A : Matrix (Fin N) (Fin N) 𝕜}
    {α : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (h : ∀ j i : Fin N, j ≤ i → α * ‖gaussState A j i j‖ ≤ ‖gaussState A j j j‖)
    (i j : Fin N) : ‖luLower A i j‖ ≤ α⁻¹ := by
  have hinv : 0 ≤ α⁻¹ := (inv_pos.mpr hα).le
  simp only [luLower, Matrix.of_apply]
  split_ifs with hji hij
  · rw [norm_div]
    by_cases hp : gaussState A j j j = 0
    · simp only [hp, norm_zero, div_zero]
      exact hinv
    · apply (div_le_iff₀ (norm_pos_iff.mpr hp)).mpr
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using h j i hji.le)
  · rw [norm_one]
    exact (one_le_inv₀ hα).mpr hα₁
  · rw [norm_zero]
    exact hinv

/-- Previously selected quantitative column pivots are preserved by independent active row
and column exchanges fixing their pivot positions. The quality fraction need not be positive
for this transport statement. -/
theorem forall_mul_norm_gaussState_le_submatrix_left_right
    (A : Matrix (Fin N) (Fin N) 𝕜) (ρ κ : Equiv.Perm (Fin N)) (k : ℕ) (α : ℝ)
    (hρ : ∀ i : Fin N, i.val < k → ρ i = i)
    (hκ : ∀ j : Fin N, j.val < k → κ j = j)
    (h : ∀ t i : Fin N, t.val < k → t ≤ i →
      α * ‖gaussState A t i t‖ ≤ ‖gaussState A t t t‖) :
    ∀ t i : Fin N, t.val < k → t ≤ i →
      α * ‖gaussState (A.submatrix ρ κ) t i t‖ ≤
        ‖gaussState (A.submatrix ρ κ) t t t‖ := by
  intro t i ht hti
  have hg := gaussState_submatrix_left_right A ρ κ t.val
    (fun a ha => hρ a (by omega)) (fun a ha => hκ a (by omega))
  have hle : t ≤ ρ i := by
    by_contra hn
    have hfix : ρ (ρ i) = ρ i :=
      hρ (ρ i) (by have := Fin.lt_def.mp (lt_of_not_ge hn); omega)
    have heq : ρ i = i := ρ.injective hfix
    rw [heq] at hn
    exact hn hti
  simpa only [hg, Matrix.submatrix_apply, hρ t ht, hκ t ht] using h t (ρ i) ht hle

/-- Updating both actual pivot logs composes their current-position swaps independently. -/
theorem submatrix_luPivotPermutation_update {β : Type*} (A : Matrix (Fin N) (Fin N) β)
    (p q : Fin N → Fin N) (k r c : Fin N) :
    A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update q k c) (k.val + 1)) =
      (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)).submatrix
        (Equiv.swap k r) (Equiv.swap k c) := by
  rw [luPivotPermutation_update, luPivotPermutation_update]
  ext i j
  rfl

/-- Active row and column exchanges transport the committed canonical factor prefixes.
Materializing the next total column and row then advances both prefixes. This statement is
independent of any numerical pivot policy, including when the chosen pivot is zero. -/
theorem forall_luLower_luUpper_eq_of_update {K : Type*} [Field K] (A : Matrix (Fin N) (Fin N) K)
    (p q : Fin N → Fin N) (k r c : Fin N) (hkr : k ≤ r) (hkc : k ≤ c)
    (F G : Matrix (Fin N) (Fin N) K)
    (hF : ∀ i j : Fin N, j.val < k.val →
      F i j = luLower (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) i j)
    (hG : ∀ i j : Fin N, i.val < k.val →
      G i j = luUpper (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) i j)
 :
    let B := A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)
    let B' := A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update q k c) (k.val + 1))
    let R := (gaussState B k.val).submatrix (Equiv.swap k r) (Equiv.swap k c)
    let F' := (F.submatrix (Equiv.swap k r) id).updateCol k
      (fun i => if i < k then 0 else if i = k then 1 else R i k / R k k)
    let G' := (G.submatrix id (Equiv.swap k c)).updateRow k
      (fun j => if j < k then 0 else R k j)
    (∀ i j : Fin N, j.val < k.val + 1 → F' i j = luLower B' i j) ∧
    (∀ i j : Fin N, i.val < k.val + 1 → G' i j = luUpper B' i j) := by
  let B := A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)
  let ρ := Equiv.swap k r
  let κ := Equiv.swap k c
  have hρ : ∀ i : Fin N, i.val < k.val → ρ i = i := Fin.swap_apply_of_lt_of_le k r hkr
  have hκ : ∀ j : Fin N, j.val < k.val → κ j = j := Fin.swap_apply_of_lt_of_le k c hkc
  have hR : gaussState (A.submatrix
      (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update q k c) (k.val + 1))) k.val =
      (gaussState B k.val).submatrix ρ κ := by
    rw [submatrix_luPivotPermutation_update]
    exact gaussState_submatrix_left_right B ρ κ k.val hρ hκ
  dsimp only
  constructor
  · intro i j hj
    by_cases hjk : j = k
    · subst j
      rw [Matrix.updateCol_self, luLower, Matrix.of_apply, hR]
      rcases lt_trichotomy i k with hi | rfl | hi
      · simp only [hi, hi.not_gt, hi.ne, if_true, if_false]
      · simp only [lt_self_iff_false, if_false, if_true]
      · simp only [hi, hi.not_gt, hi.ne', if_true, if_false, B, ρ, κ]
    · rw [Matrix.updateCol_ne hjk]
      have hj' : j.val < k.val := by
        have hne : j.val ≠ k.val := fun heq => hjk (Fin.ext heq)
        omega
      rw [Matrix.submatrix_apply, id_eq, hF (ρ i) j hj', submatrix_luPivotPermutation_update]
      exact (luLower_submatrix_left_right_apply B ρ κ k.val hρ hκ i j hj').symm
  · intro i j hi
    by_cases hik : i = k
    · subst i
      rw [Matrix.updateRow_self, luUpper, Matrix.of_apply, hR]
      by_cases hj : j < k
      · simp only [hj, not_le_of_gt hj, if_true, if_false]
      · simp only [hj, not_lt.mp hj, if_true, if_false, B, ρ, κ]
    · rw [Matrix.updateRow_ne hik]
      have hi' : i.val < k.val := by
        have hne : i.val ≠ k.val := fun heq => hik (Fin.ext heq)
        omega
      rw [Matrix.submatrix_apply, id_eq, hG i (κ j) hi', submatrix_luPivotPermutation_update]
      exact (luUpper_submatrix_left_right_apply B ρ κ k.val hρ hκ i j hi').symm

/-- Any selected positive-quality column step advances both factor prefixes and the entire
quantitative column-quality prefix. Positivity is needed only when consuming the completed
prefix as a factorization; this update algebra itself accepts an arbitrary real quality. -/
theorem forall_luLower_luUpper_mul_norm_le_of_update {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix (Fin N) (Fin N) 𝕜)
    (p q : Fin N → Fin N) (k r c : Fin N) (hkr : k ≤ r) (hkc : k ≤ c)
    (F G : Matrix (Fin N) (Fin N) 𝕜)
    (α : ℝ)
    (hF : ∀ i j : Fin N, j.val < k.val →
      F i j = luLower (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) i j)
    (hG : ∀ i j : Fin N, i.val < k.val →
      G i j = luUpper (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) i j)
    (hmax : ∀ t i : Fin N, t.val < k.val → t ≤ i →
      α * ‖gaussState (A.submatrix (luPivotPermutation p k.val)
        (luPivotPermutation q k.val)) t i t‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) t t t‖)
    (hpivot : ∀ i : Fin N, k ≤ i →
      α * ‖gaussState (A.submatrix (luPivotPermutation p k.val)
        (luPivotPermutation q k.val)) k i c‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k.val)
          (luPivotPermutation q k.val)) k r c‖) :
    let B := A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)
    let B' := A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update q k c) (k.val + 1))
    let R := (gaussState B k.val).submatrix (Equiv.swap k r) (Equiv.swap k c)
    let F' := (F.submatrix (Equiv.swap k r) id).updateCol k
      (fun i => if i < k then 0 else if i = k then 1 else R i k / R k k)
    let G' := (G.submatrix id (Equiv.swap k c)).updateRow k
      (fun j => if j < k then 0 else R k j)
    (∀ i j : Fin N, j.val < k.val + 1 → F' i j = luLower B' i j) ∧
    (∀ i j : Fin N, i.val < k.val + 1 → G' i j = luUpper B' i j) ∧
    (∀ t i : Fin N, t.val < k.val + 1 → t ≤ i →
      α * ‖gaussState B' t i t‖ ≤ ‖gaussState B' t t t‖) := by
  let B := A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)
  let ρ := Equiv.swap k r
  let κ := Equiv.swap k c
  have hρ : ∀ i : Fin N, i.val < k.val → ρ i = i := Fin.swap_apply_of_lt_of_le k r hkr
  have hκ : ∀ j : Fin N, j.val < k.val → κ j = j := Fin.swap_apply_of_lt_of_le k c hkc
  have hR : gaussState (A.submatrix
      (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update q k c) (k.val + 1))) k.val =
      (gaussState B k.val).submatrix ρ κ := by
    rw [submatrix_luPivotPermutation_update]
    exact gaussState_submatrix_left_right B ρ κ k.val hρ hκ
  obtain ⟨hFnew, hGnew⟩ := forall_luLower_luUpper_eq_of_update A p q k r c hkr hkc F G hF hG
  dsimp only
  refine ⟨hFnew, hGnew, ?_⟩
  intro t i ht hti
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
  · rw [submatrix_luPivotPermutation_update]
    exact forall_mul_norm_gaussState_le_submatrix_left_right B ρ κ k.val α hρ hκ hmax
      t i ht hti
  · have htk : t = k := Fin.ext ht
    subst t
    rw [hR]
    simpa only [B, ρ, κ, Matrix.submatrix_apply, Equiv.swap_apply_left] using
      hpivot (ρ i) (Fin.le_swap_apply_of_le k r hkr i hti)

end NLAlib
