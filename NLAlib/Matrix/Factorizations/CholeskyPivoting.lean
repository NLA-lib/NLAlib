/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky
public import NLAlib.Matrix.Factorizations.LUPivoting
public import NLAlib.ForMathlib.GroupTheory.Perm.Fin

/-!
# Cholesky prefixes under symmetric pivoting

An active permutation acts simultaneously on residual rows and columns, and on the rows
of the factor columns already completed. The formulas include zero pivots.

## Main results

* `NLAlib.choleskyLower_submatrix_apply`: completed columns follow active row exchanges.
-/

@[expose] public section

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- A simultaneous permutation fixing the completed positions carries completed Cholesky
columns to their row-permuted counterparts. This total formula includes singular inputs. -/
theorem choleskyLower_submatrix_apply (A : Matrix (Fin n) (Fin n) 𝕜)
    (τ : Equiv.Perm (Fin n)) (k : ℕ) (hτ : ∀ l : Fin n, (l : ℕ) < k → τ l = l)
    (i j : Fin n) (hj : (j : ℕ) < k) :
    choleskyLower (A.submatrix τ τ) i j = choleskyLower A (τ i) j := by
  have hfix : τ j = j := hτ j hj
  have hg := gaussState_submatrix A τ (j : ℕ) (fun l hl => hτ l (by omega))
  have hle : j ≤ i ↔ j ≤ τ i := by
    constructor
    · intro hji
      by_contra h
      have hlt : τ i < j := lt_of_not_ge h
      have hfix' := hτ (τ i) (by have := Fin.lt_def.mp hlt; omega)
      have he := τ.injective hfix'
      rw [he] at hlt
      exact hlt.not_ge hji
    · intro hji
      by_contra h
      have hi : i < j := lt_of_not_ge h
      have hfix' := hτ i (by have := Fin.lt_def.mp hi; omega)
      rw [hfix'] at hji
      exact hi.not_ge hji
  simp only [choleskyLower, Matrix.of_apply, hg, Matrix.submatrix_apply, hfix, hle]

/-- Exchanging active factor rows and materializing the next canonical column advances the
Cholesky prefix under the permutation decoded from the updated absolute pivot log. -/
theorem forall_lt_choleskyLower_eq_of_update (A F : Matrix (Fin n) (Fin n) 𝕜)
    (p : Fin n → Fin n) (k r : Fin n) (hkr : k ≤ r)
    (hF : ∀ i j : Fin n, j.val < k.val → F i j =
      choleskyLower (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val)) i j) :
    let B := A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update p k r) (k.val + 1))
    ∀ i j : Fin n, j.val < k.val + 1 →
      ((F.submatrix (Equiv.swap k r) id).updateCol k (fun i => choleskyLower B i k)) i j =
        choleskyLower B i j := by
  dsimp only
  intro i j hj
  by_cases he : j = k
  · subst j
    rw [Matrix.updateCol_self]
  · rw [Matrix.updateCol_ne he, Matrix.submatrix_apply, id_eq]
    have hjk : j.val < k.val := by have := Fin.ext_iff.not.mp he; omega
    rw [hF _ _ hjk, luPivotPermutation_update]
    exact (choleskyLower_submatrix_apply
      (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val))
      (Equiv.swap k r) k.val
      (fun l hl => Fin.swap_apply_of_lt_of_le k r hkr l (Fin.lt_def.mpr hl)) i j hjk).symm

end NLAlib
