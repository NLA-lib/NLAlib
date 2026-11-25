/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LUGeneral
public import NLAlib.ForMathlib.GroupTheory.Perm.Fin

/-!
# LU prefixes under row pivoting

An active row permutation fixes the pivot positions already committed. It permutes the
completed lower-factor columns, preserves the completed upper-factor rows and retains earlier
pivot maximality. These are prefix statements: no assumption about cleared rows or nonzero
pivots is made, so singular matrices are included.

The computable swap-log decoder `luPivotPermutation` follows the row-reindexing convention
used by the library: after the next row exchange by a permutation $\tau$, the permutation
becomes $\sigma\circ\tau$, written `τ.trans σ` in Lean.

## Main results

* `NLAlib.luLower_submatrix_left_apply`: completed lower columns follow the row permutation.
* `NLAlib.luUpper_submatrix_left_apply`: completed upper rows are retained.
* `NLAlib.forall_weight_gaussState_le_submatrix_left`: earlier maximal pivots stay maximal.
* `NLAlib.luPivotPermutation_succ`, `NLAlib.luPivotPermutation_update`: swap-log recursion.
* `NLAlib.luPivotPermutation_congr`: only the recorded prefix influences its permutation.
-/

@[expose] public section

namespace NLAlib

variable {K : Type*} [Field K] {n : ℕ}

/-- A row permutation fixing every position before $k$ carries each completed lower-factor
column to its row-permuted counterpart. No nonzero-pivot assumption is needed, including when
the factors are the total elimination formulas on a singular matrix. -/
theorem luLower_submatrix_left_apply (A : Matrix (Fin n) (Fin n) K)
    (τ : Equiv.Perm (Fin n)) (k : ℕ) (hτ : ∀ l : Fin n, (l : ℕ) < k → τ l = l)
    (i j : Fin n) (hj : (j : ℕ) < k) :
    luLower (A.submatrix τ id) i j = luLower A (τ i) j := by
  have hfix : τ j = j := hτ j hj
  have hg := gaussState_submatrix_left A τ (j : ℕ)
    (fun l hl => hτ l (by omega))
  have hcut := Fin.lt_perm_apply_iff_of_forall_le_eq τ j
    (fun l hl => hτ l (by have := Fin.le_def.mp hl; omega)) i
  have heq : τ i = j ↔ i = j := by
    simpa only [hfix] using (show τ i = τ j ↔ i = j from τ.injective.eq_iff)
  simp only [luLower, Matrix.of_apply, hg, Matrix.submatrix_apply, id_eq, hfix,
    hcut, heq]

/-- A row permutation fixing every position before $k$ leaves the completed upper-factor
rows unchanged, without requiring invertibility or nonzero pivots. -/
theorem luUpper_submatrix_left_apply (A : Matrix (Fin n) (Fin n) K)
    (τ : Equiv.Perm (Fin n)) (k : ℕ) (hτ : ∀ l : Fin n, (l : ℕ) < k → τ l = l)
    (i j : Fin n) (hi : (i : ℕ) < k) :
    luUpper (A.submatrix τ id) i j = luUpper A i j := by
  have hg := gaussState_submatrix_left A τ (i : ℕ)
    (fun l hl => hτ l (by omega))
  simp only [luUpper, Matrix.of_apply, hg, Matrix.submatrix_apply, id_eq, hτ i hi]

/-- Earlier pivots that maximize a weight over the rows below them remain maximal after a
permutation of the active rows. Specializing the weight to the norm preserves the partial
pivoting hypothesis used by the exact LU realization and multiplier bounds. The weight is
arbitrary and the statement includes zero pivots. -/
theorem forall_weight_gaussState_le_submatrix_left (w : K → ℝ)
    (A : Matrix (Fin n) (Fin n) K) (τ : Equiv.Perm (Fin n)) (k : ℕ)
    (hτ : ∀ l : Fin n, (l : ℕ) < k → τ l = l)
    (hmax : ∀ j i : Fin n, (j : ℕ) < k → j ≤ i →
      w (gaussState A j i j) ≤ w (gaussState A j j j)) :
    ∀ j i : Fin n, (j : ℕ) < k → j ≤ i →
      w (gaussState (A.submatrix τ id) j i j) ≤
        w (gaussState (A.submatrix τ id) j j j) := by
  intro j i hj hji
  have hg := gaussState_submatrix_left A τ (j : ℕ)
    (fun l hl => hτ l (by omega))
  have hle : j ≤ τ i := by
    by_cases heq : j = i
    · subst i
      rw [hτ j hj]
    · exact ((Fin.lt_perm_apply_iff_of_forall_le_eq τ j
        (fun l hl => hτ l (by have := Fin.le_def.mp hl; omega)) i).mpr
        (lt_of_le_of_ne hji heq)).le
  simpa only [hg, Matrix.submatrix_apply, id_eq, hτ j hj] using hmax j (τ i) hj hle

/-- Decode the first $k$ absolute pivot indices in a swap log. Position $j$ exchanges row $j$
with row $p_j$, and the exchanges are composed in execution order. Values beyond the recorded
prefix are ignored; prefixes longer than the dimension stop at the full log. The empty log
decodes to the identity. This is a permutation interpretation, not a new factor predicate.
[GolubVanLoan2013, §3.4]. -/
def luPivotPermutation (p : Fin n → Fin n) (k : ℕ) : Equiv.Perm (Fin n) :=
  ((List.finRange n).take k).foldl
    (fun σ j => (Equiv.swap j (p j)).trans σ) (Equiv.refl _)

/-- No recorded row exchanges give the identity permutation. -/
@[simp]
theorem luPivotPermutation_zero (p : Fin n → Fin n) :
    luPivotPermutation p 0 = Equiv.refl _ := rfl

/-- Appending the pivot at position $k$ composes its row exchange with the decoded prefix.
The order is the one for successive row reindexings. -/
theorem luPivotPermutation_succ (p : Fin n → Fin n) (k : ℕ) (hk : k < n) :
    luPivotPermutation p (k + 1) =
      (Equiv.swap ⟨k, hk⟩ (p ⟨k, hk⟩)).trans (luPivotPermutation p k) := by
  have hlen : k < (List.finRange n).length := by simpa only [List.length_finRange] using hk
  rw [luPivotPermutation, ← List.take_append_getElem hlen, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.getElem_finRange]
  rfl

/-- Only pivot indices in the recorded prefix affect its decoded permutation. -/
theorem luPivotPermutation_congr (p q : Fin n → Fin n) (k : ℕ)
    (hp : ∀ j : Fin n, (j : ℕ) < k → p j = q j) :
    luPivotPermutation p k = luPivotPermutation q k := by
  have key : ∀ l : List (Fin n), (∀ j ∈ l, p j = q j) →
      ∀ σ : Equiv.Perm (Fin n),
        l.foldl (fun σ j => (Equiv.swap j (p j)).trans σ) σ =
          l.foldl (fun σ j => (Equiv.swap j (q j)).trans σ) σ := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons j l ih =>
      intro h σ
      simp only [List.foldl_cons, h j List.mem_cons_self]
      exact ih (fun a ha => h a (List.mem_cons_of_mem j ha)) _
  apply key
  intro j hj
  obtain ⟨t, ht, hj⟩ := List.mem_take_iff_getElem.mp hj
  apply hp
  have heq : (j : ℕ) = t := by
    have hval := (congrArg Fin.val hj).symm
    simpa only [List.getElem_finRange, Fin.val_cast] using hval
  omega

/-- Recording the next absolute pivot index leaves the earlier decoded prefix unchanged and
then composes precisely that next row exchange. This is the swap-log invariant of a pivoted
LU driver, including when the selected row is the pivot row itself. -/
theorem luPivotPermutation_update (p : Fin n → Fin n) (r s : Fin n) :
    luPivotPermutation (Function.update p r s) (r.val + 1) =
      (Equiv.swap r s).trans (luPivotPermutation p r.val) := by
  rw [luPivotPermutation_succ _ _ r.isLt, Function.update_self]
  congr 1
  apply luPivotPermutation_congr
  intro j hj
  exact Function.update_of_ne (show j ≠ r from fun h => by subst j; omega) _ _

end NLAlib
