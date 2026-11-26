/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU

/-!
# Triangular shapes of committed LU prefixes

A partial lower factor has zero entries above committed columns and a unit committed
diagonal. A partial upper factor has zeros left of committed rows. These structural facts
do not depend on reconstruction accuracy or a roundoff restriction.

## Main results

* `NLAlib.IsLUTriangularPrefix.succ`: one structural column and row extend the prefix.
* `NLAlib.IsLUTriangularPrefix.submatrix`: active row and column permutations preserve it.
-/

@[expose] public section

namespace NLAlib

variable {N k : ℕ} {L U : Matrix (Fin N) (Fin N) ℝ}

/-- Triangular factor shapes through the committed column and row prefix. -/
structure IsLUTriangularPrefix (k : ℕ) (L U : Matrix (Fin N) (Fin N) ℝ) : Prop where
  /-- Committed lower columns vanish above their diagonal. -/
  lower : ∀ i j, j.val < k → i < j → L i j = 0
  /-- The committed lower diagonal is one. -/
  diag : ∀ j, j.val < k → L j j = 1
  /-- Committed upper rows vanish to the left of their diagonal. -/
  upper : ∀ i j, i.val < k → j < i → U i j = 0

/-- Empty committed prefixes impose no shape requirements on future entries. -/
theorem IsLUTriangularPrefix.initial (L U : Matrix (Fin N) (Fin N) ℝ) :
    IsLUTriangularPrefix 0 L U :=
  ⟨fun _ _ h => (Nat.not_lt_zero _ h).elim, fun _ h => (Nat.not_lt_zero _ h).elim,
    fun _ _ h => (Nat.not_lt_zero _ h).elim⟩

/-- One lower column with zero upper entries and unit diagonal, and one upper row with zero
left entries, extend the triangular prefix independently of numerical reconstruction. -/
theorem IsLUTriangularPrefix.succ (h : IsLUTriangularPrefix k L U) (r : Fin N) (hr : r.val = k)
    (v row : Fin N → ℝ) (hv : ∀ i, i < r → v i = 0) (hd : v r = 1)
    (hrow : ∀ j, j < r → row j = 0) :
    IsLUTriangularPrefix (k + 1) (L.updateCol r v) (U.updateRow r row) := by
  constructor
  · intro i j hj hij
    by_cases he : j = r
    · subst j
      simp only [Matrix.updateCol_self]
      exact hv i hij
    · have hjk : j.val < k := by have hn := Fin.val_ne_of_ne he; omega
      simpa only [Matrix.updateCol_apply, if_neg he] using h.lower i j hjk hij
  · intro j hj
    by_cases he : j = r
    · subst j
      simpa only [Matrix.updateCol_self] using hd
    · have hjk : j.val < k := by have hn := Fin.val_ne_of_ne he; omega
      simpa only [Matrix.updateCol_apply, if_neg he] using h.diag j hjk
  · intro i j hi hji
    by_cases he : i = r
    · subst i
      simp only [Matrix.updateRow_self]
      exact hrow j hji
    · have hik : i.val < k := by have hn := Fin.val_ne_of_ne he; omega
      simpa only [Matrix.updateRow_apply, if_neg he] using h.upper i j hik hji

/-- Active permutations preserve the structural prefix: the lower rows and upper columns
are permuted while each committed position is fixed. -/
theorem IsLUTriangularPrefix.submatrix (h : IsLUTriangularPrefix k L U)
    (ρ κ : Equiv.Perm (Fin N)) (hρ : ∀ i : Fin N, i.val < k → ρ i = i)
    (hκ : ∀ j : Fin N, j.val < k → κ j = j) :
    IsLUTriangularPrefix k (L.submatrix ρ id) (U.submatrix id κ) := by
  constructor
  · intro i j hj hij
    have hi : i.val < k := by have hh : i.val < j.val := hij; omega
    simpa only [Matrix.submatrix_apply, id_eq, hρ i hi] using h.lower i j hj hij
  · intro j hj
    simpa only [Matrix.submatrix_apply, id_eq, hρ j hj] using h.diag j hj
  · intro i j hi hji
    have hj : j.val < k := by have hh : j.val < i.val := hji; omega
    simpa only [Matrix.submatrix_apply, id_eq, hκ j hj] using h.upper i j hi hji

/-- At the final prefix both actual factors have their complete triangular shapes. -/
theorem IsLUTriangularPrefix.complete (h : IsLUTriangularPrefix N L U) :
    IsUnitLowerTriangular L ∧ U.IsUpperTriangular :=
  ⟨⟨fun i j hij => h.lower i j j.isLt hij, fun j => h.diag j j.isLt⟩,
    fun i j hji => h.upper i j i.isLt hji⟩

end NLAlib
