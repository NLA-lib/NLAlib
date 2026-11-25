/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.CholeskyPivoting

/-!
# Absolute logs of first-maximum diagonal pivots

Each recorded pivot is an absolute current-position index. Its score is the Gaussian
residual diagonal before that exchange, under the permutation decoded from the earlier log.
Recording the first maximum makes ties explicit and does not depend on an execution trace.

## Main results

* `NLAlib.HasDiagonalPivotPrefix.update`: append an actually selected first-maximum pivot.
-/

@[expose] public section

namespace NLAlib

variable {N : ℕ}

/-- Every recorded absolute pivot is the first remaining index with maximal real residual
diagonal entry. The residual is determined by the original matrix and earlier log entries. -/
def HasDiagonalPivotPrefix (A : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → Fin N)
    (count : ℕ) : Prop :=
  ∀ k : Fin N, k.val < count →
    let σ := luPivotPermutation p k.val
    let R := gaussState (A.submatrix σ σ) k.val
    k ≤ p k ∧ (∀ i : Fin N, k ≤ i → R i i ≤ R (p k) (p k)) ∧
      (∀ i : Fin N, k ≤ i → i < p k → R i i < R (p k) (p k))

/-- An empty absolute pivot log places no condition on a matrix or on unrecorded entries. -/
theorem HasDiagonalPivotPrefix.initial (A : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → Fin N) :
    HasDiagonalPivotPrefix A p 0 := by
  intro k hk
  exact (Nat.not_lt_zero k.val hk).elim

/-- Appending the first remaining maximum preserves every earlier pivot choice. The earlier
scores and indices depend only on already recorded entries of the absolute log. -/
theorem HasDiagonalPivotPrefix.update {A : Matrix (Fin N) (Fin N) ℝ}
    {p : Fin N → Fin N} (k r : Fin N) (h : HasDiagonalPivotPrefix A p k.val)
    (hkr : k ≤ r)
    (hmax : ∀ i : Fin N, k ≤ i →
      gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val))
        k.val i i ≤
      gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val))
        k.val r r)
    (hfirst : ∀ i : Fin N, k ≤ i → i < r →
      gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val))
        k.val i i <
      gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val))
        k.val r r) :
    HasDiagonalPivotPrefix A (Function.update p k r) (k.val + 1) := by
  have hpref (t : ℕ) (ht : t ≤ k.val) :
      luPivotPermutation (Function.update p k r) t = luPivotPermutation p t := by
    apply luPivotPermutation_congr
    intro j hj
    exact Function.update_of_ne (show j ≠ k from fun he => by subst j; omega) _ _
  intro j hj
  by_cases he : j = k
  · subst j
    simpa only [Function.update_self, hpref k.val le_rfl] using ⟨hkr, hmax, hfirst⟩
  · have hjk : j.val < k.val := by have := Fin.ext_iff.not.mp he; omega
    simpa only [Function.update_of_ne he, hpref j.val hjk.le] using h j hjk

end NLAlib
