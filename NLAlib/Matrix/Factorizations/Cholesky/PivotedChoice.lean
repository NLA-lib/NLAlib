/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.DiagonalChoice
public import NLAlib.Matrix.Factorizations.Cholesky.PivotPrefix

/-!
# Numerical meaning of the actual diagonal choice

At an exact positive-semidefinite residual every diagonal is nonnegative. The actual
largest-absolute-diagonal scan therefore supplies precisely the first remaining maximal
real diagonal and advances the original-matrix-based absolute log property.

## Main results

* `NLAlib.Cholesky.diagonalChoiceSpec_update`: append the actual scan's selected pivot.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K : Type} [Inhabited K]

/-- The actual scan output at a stored semidefinite Gaussian residual gives the first
remaining diagonal maximum, with its exactly decoded absolute current-position index. -/
theorem diagonalChoiceSpec_update {dec : K → ℝ} {N bound : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef) {p : Fin N → Fin N} (k : Fin N)
    (hprefix : HasDiagonalPivotPrefix A p k.val) {rs : List K} {w : K} {τ : Tape K}
    (hres : decodeMatrix dec N N rs =
      gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val)) k.val)
    (hpost : (diagonalChoiceSpec dec bound).post [N, k.val] τ [rs] [[w]]) :
    ∃ r : Fin N, k ≤ r ∧ dec w = r.val ∧
      HasDiagonalPivotPrefix A (Function.update p k r) (k.val + 1) := by
  obtain ⟨r, hkr, hd, hmax, hfirst⟩ := hpost
  have hnonneg (i : Fin N) : 0 ≤ gaussState
      (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val)) k.val i i :=
    ((hA.submatrix _).gaussState k.val).diag_nonneg (i := i)
  have hword (i : Fin N) : dec (vec rs (i.val * N + i.val)) = gaussState
      (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation p k.val)) k.val i i := by
    rw [← decodeMatrix_apply dec N N rs i i, hres]
  refine ⟨r, hkr, hd, hprefix.update k r hkr ?_ ?_⟩
  · intro i hi
    have h := hmax i hi
    simpa only [hword, abs_of_nonneg (hnonneg i), abs_of_nonneg (hnonneg r)] using h
  · intro i hi hir
    have h := hfirst i hi hir
    simpa only [hword, abs_of_nonneg (hnonneg i), abs_of_nonneg (hnonneg r)] using h

end NLAlib.Cholesky
