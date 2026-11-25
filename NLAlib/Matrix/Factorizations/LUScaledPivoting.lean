/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LUGeneral
public import NLAlib.Matrix.Factorizations.LUPivoting
public import NLAlib.ForMathlib.GroupTheory.Perm.Fin
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# LU with fixed original row scales

Scaled partial pivoting compares each active-column magnitude with the supremum norm of its
original row. Active row permutations transport both quantities together. Zero original rows
remain zero throughout elimination, so a largest scaled pivot equal to zero has a zero active
column. The existing total canonical factors therefore realize an LU factorization even for
singular matrices.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.HasScaledPivotPrefix`: earlier pivots maximize ratios to their fixed row norms.

## Main results

* `NLAlib.gaussState_apply_eq_zero_of_row_eq_zero`: elimination preserves an original zero row.
* `NLAlib.gaussState_apply_eq_zero_of_norm_row_eq_zero`: zero row scale implies a zero residual row.
* `NLAlib.HasScaledPivotPrefix.submatrix_left`: the weighted prefix follows active row permutations.
* `NLAlib.HasScaledPivotPrefix.update`: commit a selected pre-swap scaled maximum.
* `NLAlib.HasScaledPivotPrefix.isLU`: completed scaled pivots yield canonical exact factors.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- An original zero row remains zero after any number of total elimination steps, without
requiring nonzero pivots or any assumption about the other rows. -/
theorem gaussState_apply_eq_zero_of_row_eq_zero {K : Type*} [Field K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (i : Fin N) (hrow : ∀ j, A i j = 0) (k : ℕ)
    (j : Fin N) : gaussState A k i j = 0 := by
  induction k generalizing j with
  | zero => exact hrow j
  | succ k ih =>
    rw [gaussState]
    split_ifs with hk
    · exact eliminationStep_apply_eq_zero_of_row ih _ j
    · exact ih j

variable {𝕜 : Type*} [RCLike 𝕜] {N k : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}

/-- A zero fixed original row norm implies that every entry of that row remains zero in the
elimination residual, including at singular pivots. The row norm is the existing finite Pi
supremum norm. -/
theorem gaussState_apply_eq_zero_of_norm_row_eq_zero (A : Matrix (Fin N) (Fin N) 𝕜)
    (i : Fin N) (hrow : ‖A i‖ = 0) (k : ℕ) (j : Fin N) : gaussState A k i j = 0 := by
  have he : A i = 0 := norm_eq_zero.mp hrow
  exact gaussState_apply_eq_zero_of_row_eq_zero A i
    (fun j => by simpa only [Pi.zero_apply] using congrFun he j) k j

/-- Every earlier pivot maximizes its active-column magnitude divided by its fixed original
row norm. A zero norm has a zero original row, so total division assigns that row score zero.
The predicate does not assert an unweighted bound on lower multipliers.
[Higham2002, §9.3]. -/
def HasScaledPivotPrefix (A : Matrix (Fin N) (Fin N) 𝕜) (k : ℕ) : Prop :=
  ∀ j i : Fin N, j.val < k → j ≤ i →
    ‖gaussState A j i j‖ / ‖A i‖ ≤ ‖gaussState A j j j‖ / ‖A j‖

/-- Earlier scaled pivots remain maximal after permuting active rows. Both the residual rows
and their fixed original row norms follow the same permutation; earlier pivot rows stay fixed.
No nonzero-pivot assumption is required. -/
theorem HasScaledPivotPrefix.submatrix_left (h : HasScaledPivotPrefix A k)
    (τ : Equiv.Perm (Fin N)) (hfix : ∀ i, i.val < k → τ i = i) :
    HasScaledPivotPrefix (A.submatrix τ id) k := by
  intro j i hj hji
  have hjfix : τ j = j := hfix j hj
  have hji' : j ≤ τ i := by
    by_contra hlt
    have hlt' : (τ i).val < j.val := lt_of_not_ge hlt
    have hfix' : τ (τ i) = τ i := hfix (τ i) (by omega)
    have he : τ i = i := τ.injective hfix'
    rw [he] at hlt'
    exact (not_lt_of_ge hji) hlt'
  have hg := gaussState_submatrix_left A τ j.val (fun l hl => hfix l (by omega))
  change ‖gaussState (A.submatrix τ id) j i j‖ / ‖A (τ i)‖ ≤
    ‖gaussState (A.submatrix τ id) j j j‖ / ‖A (τ j)‖
  simpa only [hg, Matrix.submatrix_apply, id_eq, hjfix] using h j (τ i) hj hji'

/-- Committing a newly selected scaled pivot extends the transported scaled prefix.
The selected ratio is compared before the active swap; no final-permutation tie claim is made. -/
theorem HasScaledPivotPrefix.update (A : Matrix (Fin N) (Fin N) 𝕜)
    (p : Fin N → Fin N) (k r : Fin N) (hkr : k ≤ r)
    (h : HasScaledPivotPrefix (A.submatrix (luPivotPermutation p k.val) id) k.val)
    (hp : ∀ i : Fin N, k ≤ i →
      ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) k i k‖ /
          ‖A (luPivotPermutation p k.val i)‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) k r k‖ /
          ‖A (luPivotPermutation p k.val r)‖) :
    HasScaledPivotPrefix
      (A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1)) id)
      (k.val + 1) := by
  let B := A.submatrix (luPivotPermutation p k.val) id
  let τ := Equiv.swap k r
  have hfix : ∀ i : Fin N, i.val < k.val → τ i = i :=
    Fin.swap_apply_of_lt_of_le k r hkr
  have he : A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1)) id =
      B.submatrix τ id := by
    rw [luPivotPermutation_update]
    rfl
  rw [he]
  intro j i hj hji
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · exact h.submatrix_left τ hfix j i hj hji
  · have hjk : j = k := Fin.ext hj
    subst j
    change ‖gaussState (B.submatrix τ id) k i k‖ / ‖B (τ i)‖ ≤
      ‖gaussState (B.submatrix τ id) k k k‖ / ‖B (τ k)‖
    rw [gaussState_submatrix_left B τ k.val hfix]
    have hh := hp (τ i) (Fin.le_swap_apply_of_le k r hkr i hji)
    change ‖gaussState B k (τ i) k‖ / ‖B (τ i)‖ ≤
      ‖gaussState B k (τ k) k‖ / ‖B (τ k)‖
    have hnorm (l : Fin N) : ‖B l‖ = ‖A (luPivotPermutation p k.val l)‖ := by
      congr 1
    rw [hnorm, hnorm]
    simpa only [τ, Equiv.swap_apply_left, B] using hh


/-- Largest fixed-scale ratios give a zero-compatible elimination sequence and therefore an
exact canonical LU factorization. This includes singular and empty matrices; no unweighted
multiplier bound or positive-row-scale assumption is imposed. [Higham2002, §9.3]. -/
theorem HasScaledPivotPrefix.isLU (h : HasScaledPivotPrefix A N) :
    IsLU A (luLower A) (luUpper A) := by
  refine isLU_luLower_luUpper_of_forall_eq_zero fun j i hji hp => ?_
  by_cases hs : ‖A i‖ = 0
  · exact gaussState_apply_eq_zero_of_norm_row_eq_zero A i hs j j
  · have hspos : 0 < ‖A i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs)
    have hratio := h j i j.isLt hji.le
    rw [hp, norm_zero, zero_div] at hratio
    have hzero := (div_le_iff₀ hspos).mp hratio
    rw [zero_mul] at hzero
    exact norm_le_zero_iff.mp hzero

end NLAlib
