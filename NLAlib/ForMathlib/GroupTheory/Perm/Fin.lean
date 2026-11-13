/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.MinMax
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Greedy choice of a permutation

A permutation of `Fin n` can be built position by position, swapping into each position a
maximiser of a score that the permutations already chosen transform covariantly: the choice
of pivots in partial pivoting and in diagonally pivoted Cholesky. Upstream candidate for
`Mathlib.GroupTheory.Perm.Fin`.

## Main definitions

* `Fin.greedyPerm`: the permutation obtained by exchanging the first maximizing candidate
  into each pivot position.

## Main results

* `Fin.le_greedyPerm_apply_self`, `Fin.exists_perm_forall_le_apply_self`: pivots maximize
  the score at each step.
-/

@[expose] public section

namespace Fin

private def pivotCandidates {n : ℕ} (j : Fin n) : List (Fin n) :=
  j :: (List.finRange n).filter (j < ·)

private theorem mem_pivotCandidates {n : ℕ} {j i : Fin n} :
    i ∈ pivotCandidates j ↔ j ≤ i := by
  simp [pivotCandidates, le_iff_eq_or_lt, eq_comm]

private def firstPivot {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α) (j : Fin n) : Fin n :=
  ((pivotCandidates j).argmax f).getD j

private theorem firstPivot_mem_argmax {α : Type*} [LinearOrder α] {n : ℕ}
    (f : Fin n → α) (j : Fin n) : firstPivot f j ∈ (pivotCandidates j).argmax f := by
  cases h : (pivotCandidates j).argmax f with
  | none => exact False.elim (List.cons_ne_nil _ _ (List.argmax_eq_none.mp h))
  | some i => simp [firstPivot, h]

/-- The permutation after the first $k$ greedy pivot steps. At step $j$, swap the first
remaining maximizer of the current score into position $j$. Steps beyond the size leave
the ordering fixed. -/
def greedyPerm {α : Type*} [LinearOrder α] {n : ℕ}
    (s : Equiv.Perm (Fin n) → Fin n → Fin n → α) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | k + 1 =>
    let σ := greedyPerm s k
    if hk : k < n then
      let j : Fin n := ⟨k, hk⟩
      let candidates := j :: (List.finRange n).filter (j < ·)
      (Equiv.swap j ((candidates.argmax (s σ j)).getD j)).trans σ
    else σ

/-- If the current diagonal position always maximizes the score in the original ordering,
first-maximum pivoting never exchanges two rows. -/
theorem greedyPerm_eq_one_of_forall_le {α : Type*} [LinearOrder α] {n : ℕ}
    (s : Equiv.Perm (Fin n) → Fin n → Fin n → α)
    (h : ∀ j i, j ≤ i → s 1 j i ≤ s 1 j j) (k : ℕ) : greedyPerm s k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [greedyPerm, ih]
    split
    · rename_i hk
      let j : Fin n := ⟨k, hk⟩
      have hj : (pivotCandidates j).argmax (s 1 j) = some j := by
        refine List.argmax_eq_some_iff.mpr ⟨mem_pivotCandidates.mpr le_rfl,
          fun i hi => h j i (mem_pivotCandidates.mp hi), fun i _ _ => ?_⟩
        simp [pivotCandidates]
      change (Equiv.swap j (((pivotCandidates j).argmax (s 1 j)).getD j)).trans
        (1 : Equiv.Perm (Fin n)) = 1
      simp [hj]
    · rfl

/-- Greedy pivoting: let $s_\sigma(j, i)$ score the candidate $i$ for the pivot position $j$
after the permutation $\sigma$, and suppose that composing $\sigma$ with a permutation $\tau$
fixing the positions before $j$ permutes the scores at step $j$ by $\tau$:
$s_{\sigma \circ \tau}(j, i) = s_\sigma(j, \tau(i))$. Then some permutation $\sigma$ makes every
pivot among the first $k$ maximal over the later positions, $s_\sigma(j, i) \le s_\sigma(j, j)$ for
$j < k$ and $j \le i$: swap a maximiser into each position in turn.
This is the choice of pivots in partial pivoting and in diagonally pivoted Cholesky. -/
theorem le_greedyPerm_apply_self {α : Type*} [LinearOrder α] {n : ℕ}
    (s : Equiv.Perm (Fin n) → Fin n → Fin n → α)
    (hs : ∀ (σ τ : Equiv.Perm (Fin n)) (j : Fin n), (∀ l : Fin n, l < j → τ l = l) →
      ∀ i, s (τ.trans σ) j i = s σ j (τ i)) (k : ℕ) :
    ∀ j i : Fin n, (j : ℕ) < k → j ≤ i → s (greedyPerm s k) j i ≤ s (greedyPerm s k) j j := by
  induction k with
  | zero => exact fun j i hj => absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    let σ := greedyPerm s k
    by_cases hk : k < n
    · let i₀ := firstPivot (s σ ⟨k, hk⟩) ⟨k, hk⟩
      have hmax := firstPivot_mem_argmax (s σ ⟨k, hk⟩) ⟨k, hk⟩
      have hi₀' : k ≤ (i₀ : ℕ) := Fin.le_def.mp (mem_pivotCandidates.mp (List.argmax_mem hmax))
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
      intro j i hj hji
      simp only [greedyPerm, dif_pos hk]
      change s ((Equiv.swap ⟨k, hk⟩ i₀).trans σ) j i ≤ s ((Equiv.swap ⟨k, hk⟩ i₀).trans σ) j j
      have hτj : ∀ l : Fin n, l < j → Equiv.swap (⟨k, hk⟩ : Fin n) i₀ l = l := fun l hl =>
        hτ l (by have := Fin.lt_def.mp hl; omega)
      rw [hs σ _ j hτj, hs σ _ j hτj]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · rw [hτ j hjk]
        exact ih j _ hjk (Fin.le_def.mpr (hge j i hjk.le (Fin.le_def.mp hji)))
      · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hjk
        rw [Equiv.swap_apply_left]
        exact List.le_of_mem_argmax
          (mem_pivotCandidates.mpr (Fin.le_def.mpr (hge k i le_rfl (Fin.le_def.mp hji)))) hmax
    · simpa only [greedyPerm, dif_neg hk] using
        fun (j i : Fin n) (_ : (j : ℕ) < k + 1) hji => ih j i (by omega) hji

/-- A permutation whose first $k$ pivots maximize a score covariant under reordering the
remaining positions. -/
theorem exists_perm_forall_le_apply_self {α : Type*} [LinearOrder α] {n : ℕ}
    (s : Equiv.Perm (Fin n) → Fin n → Fin n → α)
    (hs : ∀ (σ τ : Equiv.Perm (Fin n)) (j : Fin n), (∀ l : Fin n, l < j → τ l = l) →
      ∀ i, s (τ.trans σ) j i = s σ j (τ i)) (k : ℕ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j i : Fin n, (j : ℕ) < k → j ≤ i → s σ j i ≤ s σ j j :=
  ⟨greedyPerm s k, le_greedyPerm_apply_self s hs k⟩

end Fin
