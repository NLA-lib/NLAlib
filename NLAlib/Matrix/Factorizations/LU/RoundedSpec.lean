/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedSpec
public import NLAlib.Matrix.Perturbation.LUErr
public import NLAlib.Matrix.FinitePrecision.Rounding

/-!
# Rounded pivoted LU outputs

Actual absolute pivot histories identify the two permutations of the original input.
The actual factors are triangular, their lower multipliers have the policy's relative-error
bound, and roundoff below one gives the preserved componentwise reconstruction budget.
The original matrix is arbitrary, including singular and empty matrices.

## Main definitions

* `NLAlib.LU.Rounded.factorPivotedSpec`: rounded factors and actual reported pivot histories.
-/

@[expose] public section

namespace NLAlib.LU.Rounded

open Ops Computation

variable {K : Type} [Inhabited K]

/-- The bounded exact index range admits dimensions, while every matrix at those dimensions
is admitted. All nonnegative roundoffs retain shape and multiplier bounds; only the numerical
backward-error conclusion requires roundoff below one. -/
def factorPivotedSpec (dec : K → ℝ) (u quality : ℝ) (fixedColumns : Bool) (bound : ℕ) :
    Routine.Spec K :=
  spec% [n] (as) → (ls, us, hs, qs) requires n ≤ bound ensures
    ∃ p q : Fin n → Fin n,
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) ∧
      (fixedColumns = false → ∀ i : Fin n, dec (vec qs i.val) = (q i).val) ∧
      (fixedColumns = true → 0 < n → dec (vec qs 0) = (n - 1 : ℕ)) ∧
      (∀ i : Fin n, i ≤ p i) ∧ (∀ i : Fin n, i ≤ q i) ∧
      (fixedColumns = true → ∀ i : Fin n, q i = i) ∧
      let B := (decodeMatrix dec n n as).submatrix
        (luPivotPermutation p n) (luPivotPermutation q n)
      IsUnitLowerTriangular (decodeMatrix dec n n ls) ∧
        (decodeMatrix dec n n us).IsUpperTriangular ∧
        (u < 1 → IsLUErr (roundingFactor (n + 4) u) B
          (decodeMatrix dec n n ls) (decodeMatrix dec n n us)) ∧
        ∀ i j : Fin n, |decodeMatrix dec n n ls i j| ≤ (1 + u) / quality

/-- Empty factors and histories satisfy the rounded postcondition at every parameter value,
without reading any word or invoking any arithmetic operation. -/
theorem factorPivotedSpec_zero (dec : K → ℝ) (u quality : ℝ) (fixedColumns : Bool) (bound : ℕ)
    (τ : Tape K) :
    (factorPivotedSpec dec u quality fixedColumns bound).post [0] τ [[]] [[], [], [], []] := by
  refine ⟨id, id, fun i => Fin.elim0 i, fun _ i => Fin.elim0 i,
    fun _ hn => (Nat.lt_irrefl 0 hn).elim, fun i => Fin.elim0 i,
    fun i => Fin.elim0 i, fun _ i => Fin.elim0 i,
    ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
    fun i => Fin.elim0 i, fun _ => ?_, fun i => Fin.elim0 i⟩
  exact ⟨⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
    fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

end NLAlib.LU.Rounded
