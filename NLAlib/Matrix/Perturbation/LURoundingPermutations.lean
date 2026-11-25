/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.LURoundingPrefix

/-!
# Column transport of rounded LU prefixes

An active column permutation transports the input, residual and upper-factor columns. It
leaves earlier pivot coordinates fixed, so the accumulated rounding-product lengths remain
unchanged. Together with row transport this supports complete pivoting using two actual logs.

## Main results

* `NLAlib.IsLURoundingPrefix.submatrix_right`: transport a rounded prefix by active columns.
-/

@[expose] public section

namespace NLAlib

variable {N k : ℕ} {u : ℝ} {B S L U : Matrix (Fin N) (Fin N) ℝ}

/-- A column permutation fixing coordinates before the active suffix transports the input,
residual and upper-factor columns together, with unchanged lower-factor entries and rounding
counts. No inactive residual entry is assumed zero. -/
theorem IsLURoundingPrefix.submatrix_right (h : IsLURoundingPrefix u k B S L U)
    (υ : Equiv.Perm (Fin N)) (hfix : ∀ j, j.val < k → υ j = j) :
    IsLURoundingPrefix u k (B.submatrix id υ) (S.submatrix id υ) L (U.submatrix id υ) := by
  have hactive (j : Fin N) : k ≤ (υ j).val ↔ k ≤ j.val := by
    constructor
    · intro ht
      by_contra hj
      have hlt : j.val < k := by omega
      rw [hfix j hlt] at ht
      omega
    · intro hj
      by_contra ht
      have hlt : (υ j).val < k := by omega
      have he : υ j = j := υ.injective (hfix (υ j) hlt)
      rw [he] at hlt
      omega
  obtain ⟨θ, η, hθ, hη, heq⟩ := h.factors
  refine ⟨h.le_dim, h.lower, h.diag, ?_, fun i j => θ i (υ j),
    fun t i j => η t i (υ j), ?_, ?_, ?_⟩
  · intro t j ht hjt
    have hj : j.val < k := lt_trans hjt ht
    simpa only [Matrix.submatrix_apply, id_eq, hfix j hj] using h.upper t j ht hjt
  · intro i j hi hj
    exact hθ i (υ j) hi ((hactive j).mpr hj)
  · intro t ht i j
    exact hη t ht i (υ j)
  · intro i j
    simpa only [Matrix.submatrix_apply, id_eq, hactive] using heq i (υ j)

end NLAlib
