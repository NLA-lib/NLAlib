/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Pivoted
public import NLAlib.Matrix.Factorizations.LU

/-!
# Input-level nonsingularity for solves through pivoted factors

Exact LU of a nonsingular permuted input has a unit lower factor and nonzero upper diagonal.
Together with the actual reported history this gives the stored triangular solve's inputs.
No computed-pivot or successful-factorization condition is introduced in a full solve.

## Main results

* `NLAlib.TriangularSolve.pivotedSpec_pre_of_isLU`: derive the actual stored solve precondition.
* `NLAlib.TriangularSolve.mulVec_eq_of_submatrix_solve`: restore original solve coordinates.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K] {n : ℕ}

/-- Nonsingularity of the original permuted input gives nonzero stored triangular diagonals.
The permutation reaches the program only through its declared stored log words. -/
theorem pivotedSpec_pre_of_isLU {dec : K → ℝ} {B : Matrix (Fin n) (Fin n) ℝ}
    {ls us hs bs : List K} {τ : Tape K}
    (hf : IsLU B (decodeMatrix dec n n ls) (decodeMatrix dec n n us)) (hB : IsUnit B)
    (p : Fin n → Fin n) (hp : ∀ i : Fin n, i ≤ p i)
    (hlog : ∀ i : Fin n, dec (vec hs i.val) = (p i).val) :
    (pivotedSpec dec).pre [n] τ [ls, us, hs, bs] := by
  refine ⟨hf.isUnitLowerTriangular.isLowerTriangular, hf.isUpperTriangular, ?_, ?_, p, hp, hlog⟩
  · intro i hi
    have hd := hf.isUnitLowerTriangular.apply_self (⟨i, hi⟩ : Fin n)
    have he : dec (vec ls (i * n + i)) = 1 := by simpa only [decodeMatrix_apply] using hd
    rw [he]
    exact one_ne_zero
  · intro i hi
    have hd := (hf.isUnit_det_iff.mp ((Matrix.isUnit_iff_isUnit_det B).mp hB)) ⟨i, hi⟩
    simpa only [decodeMatrix_apply] using isUnit_iff_ne_zero.mp hd

/-- A solve for an independently row/column-permuted matrix restores the original equation
by undoing the column permutation. Only finite-sum reindexing is used. -/
theorem mulVec_eq_of_submatrix_solve {A : Matrix (Fin n) (Fin n) ℝ}
    (P Q : Equiv.Perm (Fin n)) {b z : Fin n → ℝ}
    (hsolve : A.submatrix P Q *ᵥ z = b ∘ P) :
    A *ᵥ (z ∘ Q.symm) = b := by
  have hEq : (A *ᵥ (z ∘ Q.symm)) ∘ P = b ∘ P := by
    simpa only [Matrix.submatrix_mulVec_equiv] using hsolve
  funext i
  have hh := congrFun hEq (P.symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh

end NLAlib.TriangularSolve
