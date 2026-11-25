/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LUPivoting

/-!
# LU prefixes under complete pivoting

Independent active row and column permutations commute with the elimination prefix. Completed
lower columns follow the row permutation and completed upper rows follow the column permutation.
Earlier pivots maximal over their entire active squares retain this property. All formulas are
total and admit zero pivots; no cleared-row or invertibility premise is used.

## Main results

* `NLAlib.gaussState_submatrix_left_right`: independent prefix-fixing reindexings commute.
* `NLAlib.luLower_submatrix_left_right_apply`: completed lower columns follow row exchanges.
* `NLAlib.luUpper_submatrix_left_right_apply`: completed upper rows follow column exchanges.
* `NLAlib.forall_weight_gaussState_le_submatrix_left_right`: complete maximality is retained.
-/

@[expose] public section

namespace NLAlib

variable {K : Type*} [Field K] {n : ℕ}

/-- Independent row and column maps fixing all previously used pivot positions commute with
those elimination steps. The maps need not be injective; no pivot is required to be nonzero. -/
theorem gaussState_submatrix_left_right (A : Matrix (Fin n) (Fin n) K)
    (ρ κ : Fin n → Fin n) (k : ℕ)
    (hρ : ∀ i : Fin n, i.val < k → ρ i = i)
    (hκ : ∀ j : Fin n, j.val < k → κ j = j) :
    gaussState (A.submatrix ρ κ) k = (gaussState A k).submatrix ρ κ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih (fun i hi => hρ i (Nat.lt_succ_of_lt hi))
      (fun j hj => hκ j (Nat.lt_succ_of_lt hj))
    by_cases hk : k < n
    · rw [gaussState_succ _ hk, gaussState_succ _ hk, ih']
      ext i j
      simp only [eliminationStep_apply, Matrix.submatrix_apply,
        hρ ⟨k, hk⟩ (Nat.lt_succ_self k), hκ ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · have hstop (M : Matrix (Fin n) (Fin n) K) : gaussState M (k + 1) = gaussState M k := by
        rw [gaussState, dif_neg hk]
      rw [hstop, hstop, ih']

/-- Independent active permutations carry a completed lower column along the row axis only.
The column permutation fixes that column and all earlier pivots. Singular matrices are allowed. -/
theorem luLower_submatrix_left_right_apply (A : Matrix (Fin n) (Fin n) K)
    (ρ κ : Equiv.Perm (Fin n)) (k : ℕ)
    (hρ : ∀ i : Fin n, i.val < k → ρ i = i)
    (hκ : ∀ j : Fin n, j.val < k → κ j = j) (i j : Fin n) (hj : j.val < k) :
    luLower (A.submatrix ρ κ) i j = luLower A (ρ i) j := by
  have hg := gaussState_submatrix_left_right A ρ κ j.val
    (fun i hi => hρ i (by omega)) (fun i hi => hκ i (by omega))
  rw [← luLower_submatrix_left_apply A ρ k hρ i j hj]
  have hgρ := gaussState_submatrix_left A ρ j.val (fun a ha => hρ a (by omega))
  simp only [luLower, Matrix.of_apply, hg, hgρ, Matrix.submatrix_apply, id_eq,
    hρ j hj, hκ j hj]

/-- Independent active permutations carry a completed upper row along the column axis only.
The row permutation fixes that row and all earlier pivots, including for zero pivots. -/
theorem luUpper_submatrix_left_right_apply (A : Matrix (Fin n) (Fin n) K)
    (ρ κ : Equiv.Perm (Fin n)) (k : ℕ)
    (hρ : ∀ i : Fin n, i.val < k → ρ i = i)
    (hκ : ∀ j : Fin n, j.val < k → κ j = j) (i j : Fin n) (hi : i.val < k) :
    luUpper (A.submatrix ρ κ) i j = luUpper A i (κ j) := by
  have hg := gaussState_submatrix_left_right A ρ κ i.val
    (fun j hj => hρ j (by omega)) (fun j hj => hκ j (by omega))
  have hle : i ≤ κ j ↔ i ≤ j := by
    constructor
    · intro h
      by_contra h'
      have hfix : κ j = j := hκ j (by have := Fin.lt_def.mp (lt_of_not_ge h'); omega)
      rw [hfix] at h
      exact h' h
    · intro h
      by_contra h'
      have hfix : κ (κ j) = κ j :=
        hκ (κ j) (by have := Fin.lt_def.mp (lt_of_not_ge h'); omega)
      have heq : κ j = j := κ.injective hfix
      rw [heq] at h'
      exact h' h
  simp only [luUpper, Matrix.of_apply, hg, Matrix.submatrix_apply, hρ i hi, hle]

/-- A complete active-square maximality prefix is retained under independent active row and
column permutations. The weight has an arbitrary ordered codomain and need not be a norm. -/
theorem forall_weight_gaussState_le_submatrix_left_right {β : Type*} [Preorder β]
    (w : K → β) (A : Matrix (Fin n) (Fin n) K) (ρ κ : Equiv.Perm (Fin n)) (k : ℕ)
    (hρ : ∀ i : Fin n, i.val < k → ρ i = i)
    (hκ : ∀ j : Fin n, j.val < k → κ j = j)
    (hmax : ∀ t i j : Fin n, t.val < k → t ≤ i → t ≤ j →
      w (gaussState A t i j) ≤ w (gaussState A t t t)) :
    ∀ t i j : Fin n, t.val < k → t ≤ i → t ≤ j →
      w (gaussState (A.submatrix ρ κ) t i j) ≤
        w (gaussState (A.submatrix ρ κ) t t t) := by
  intro t i j ht hti htj
  have hg := gaussState_submatrix_left_right A ρ κ t.val
    (fun a ha => hρ a (by omega)) (fun a ha => hκ a (by omega))
  have hle (τ : Equiv.Perm (Fin n)) (hτ : ∀ a : Fin n, a.val < k → τ a = a)
      (a : Fin n) (ha : t ≤ a) : t ≤ τ a := by
    by_contra h
    have hfix : τ (τ a) = τ a :=
      hτ (τ a) (by have := Fin.lt_def.mp (lt_of_not_ge h); omega)
    have heq : τ a = a := τ.injective hfix
    rw [heq] at h
    exact h ha
  simpa only [hg, Matrix.submatrix_apply, hρ t ht, hκ t ht] using
    hmax t (ρ i) (κ j) ht (hle ρ hρ i hti) (hle κ hκ j htj)

end NLAlib
