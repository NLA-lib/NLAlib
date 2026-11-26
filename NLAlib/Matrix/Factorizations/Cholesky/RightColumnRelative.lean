/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightColumn
public import NLAlib.Ops.Blas.Dot
public import NLAlib.Ops.ArithmeticError

/-!
# Relative rounding of the actual Cholesky column

At a positive residual pivot, roundoff below one preserves a positive rounded root.
The root and all normalized suffix entries satisfy the standard relative error relation.
These facts read directly from the actual column word postcondition.

## Main results

* `NLAlib.Cholesky.rightColumnSpec_relative`: positive root and relative quotient errors.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops Computation

variable {K : Type} [Inhabited K]

/-- The actual column words have a positive root and standard relative root and quotient
errors. Numerical input margin arguments establish the positive pivot before this call. -/
theorem rightColumnSpec_relative {M : Machine K} {dec : K → ℝ} {u : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u < 1) {n : ℕ}
    {p : K} {xs ys : List K} {τ : Tape K}
    (hpost : (rightColumnSpec M).post [n] τ [[p], xs] [ys]) (hp : 0 < dec p) :
    0 < dec (vec ys 0) ∧
      RelErr u (Real.sqrt (dec p)) (dec (vec ys 0)) ∧
      ∀ i < n, RelErr u (dec (vec xs i) / dec (vec ys 0)) (dec (vec ys (i + 1))) := by
  have hroot : AbsRelErr u 0 (Real.sqrt (dec p)) (dec (M.sqrt p)) := by
    simpa only [AbsRelErr, add_zero, abs_sub_comm, abs_of_nonneg (Real.sqrt_nonneg _)] using
      hM.sqrt p hp.le
  have hpos : 0 < dec (M.sqrt p) := by
    have hs : 0 < (1 - u) * Real.sqrt (dec p) :=
      mul_pos (sub_pos.mpr hu1) (Real.sqrt_pos.mpr hp)
    have he := (abs_le.mp hroot.abs_sub_le).2
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at he
    linarith
  have hy : ys = M.sqrt p :: scalF M (M.sqrt p) (vec xs) n := hpost
  have hhead : vec ys 0 = M.sqrt p := by rw [hy]; rfl
  refine ⟨by simpa only [hhead] using hpos, by simpa only [hhead] using hroot.relErr hu, ?_⟩
  intro i hi
  have hv : vec ys (i + 1) = M.div (vec xs i) (M.sqrt p) := by
    rw [hy]
    change vec (scalF M (M.sqrt p) (vec xs) n) i = _
    simp only [scalF, vec_map_range _ hi]
  rw [hv, hhead]
  apply AbsRelErr.relErr (u := u) _ hu
  simpa only [AbsRelErr, add_zero, abs_sub_comm] using hM.div (vec xs i) (M.sqrt p) hpos.ne'

end NLAlib.Cholesky
