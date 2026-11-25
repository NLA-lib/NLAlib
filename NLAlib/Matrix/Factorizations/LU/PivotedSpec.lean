/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Pivot

/-!
# Output specifications of pivoted LU policies

Actual recorded current-position choices determine independent row and column permutations.
Fixed-column policies store only one reusable column word and prove identity column choices
from each actual selector output. Positive column quality gives exact reconstruction even
for singular matrices and bounds the lower multipliers.

## Main definitions

* `NLAlib.LU.factorPivotedSpec`: canonical factors and actual history outputs.
* `NLAlib.LU.factorPivotedCoreSpec`: the concrete column-storage flag of the shared loop.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} [Inhabited K]

/-- Both actual current-position logs decode to finite active positions. The output factors
are canonical for the input permuted independently by those logs, satisfy exact LU, and have
lower multipliers bounded by the reciprocal quality. A fixed-column policy records identity
column choices. Singular and empty matrices are included. -/
def factorPivotedSpec (dec : K → ℝ) (quality : ℝ) (fixedColumns : Bool) : Routine.Spec K :=
  spec% [n] (as) → (ls, us, hs, qs) ensures
    ∃ p q : Fin n → Fin n,
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) ∧
      (fixedColumns = false → ∀ i : Fin n, dec (vec qs i.val) = (q i).val) ∧
      (fixedColumns = true → 0 < n → dec (vec qs 0) = (n - 1 : ℕ)) ∧
      (∀ i : Fin n, i ≤ p i) ∧ (∀ i : Fin n, i ≤ q i) ∧
      (fixedColumns = true → ∀ i : Fin n, q i = i) ∧
      let B := (decodeMatrix dec n n as).submatrix
        (luPivotPermutation p n) (luPivotPermutation q n)
      decodeMatrix dec n n ls = luLower B ∧ decodeMatrix dec n n us = luUpper B ∧
        IsLU B (decodeMatrix dec n n ls) (decodeMatrix dec n n us) ∧
        ∀ i j : Fin n, |decodeMatrix dec n n ls i j| ≤ quality⁻¹

/-- The shared loop's column-storage flag is fixed by its concrete policy. All input matrices
are admitted; the local policy judgment supplies zero-column compatibility. -/
def factorPivotedCoreSpec (dec : K → ℝ) (quality : ℝ) (fixedColumns : Bool) : Routine.Spec K :=
  spec% [n, columns] tape t (as) → (ls, us, hs, qs) requires
    columns = (if fixedColumns then 0 else 1) ensures
    (factorPivotedSpec dec quality fixedColumns).post [n] t [as] [ls, us, hs, qs]


/-- Empty factors and histories satisfy the pivoted output specification without reading any
word or imposing a condition on pivot quality. There are no pivots or multiplier entries. -/
theorem factorPivotedSpec_zero (dec : K → ℝ) (quality : ℝ) (fixedColumns : Bool)
    (τ : Tape K) :
    (factorPivotedSpec dec quality fixedColumns).post [0] τ [[]] [[], [], [], []] := by
  let B := (decodeMatrix dec 0 0 []).submatrix
    (luPivotPermutation (id : Fin 0 → Fin 0) 0) (luPivotPermutation (id : Fin 0 → Fin 0) 0)
  have hL : decodeMatrix dec 0 0 [] = luLower B := by ext i; exact Fin.elim0 i
  have hU : decodeMatrix dec 0 0 [] = luUpper B := by ext i; exact Fin.elim0 i
  refine ⟨id, id, fun i => Fin.elim0 i, fun _ i => Fin.elim0 i,
    fun _ hn => (Nat.lt_irrefl 0 hn).elim, fun i => Fin.elim0 i,
    fun i => Fin.elim0 i, fun _ i => Fin.elim0 i, hL, hU, ?_, fun i => Fin.elim0 i⟩
  have hLU : IsLU B (luLower B) (luUpper B) :=
    isLU_luLower_luUpper_of_forall_eq_zero (fun j => Fin.elim0 j)
  convert hLU using 1

end NLAlib.LU
