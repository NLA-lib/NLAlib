/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.FindRitzSolve
public import Mathlib.Data.List.GetD

/-!
# Mathematical states of inverse-polynomial half norms

One half is a contiguous segment of stored shifts. Successive row solves implement a fold
over that segment, repeated by the supplied exponent. The established inverse-polynomial
identity identifies the final row with the last row of the inverse polynomial power.

## Main results

* `NLAlib.ShiftedQR.halfSegment`: the chosen contiguous segment of shifts.
* `NLAlib.ShiftedQR.shiftSolvePrefix`: the row after a prefix of one segment.
* `NLAlib.ShiftedQR.halfSolvePrefix_eq_power`: the final inverse-polynomial row.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open scoped Matrix

/-- A contiguous segment selected from the supplied list of shifts. -/
def halfSegment (ss : List ℂ) (a h : ℕ) : List ℂ := (ss.drop a).take h

/-- A segment wholly inside the supplied shift list has the requested length. -/
theorem length_halfSegment {ss : List ℂ} {a h : ℕ} (hah : a + h ≤ ss.length) :
    (halfSegment ss a h).length = h := by
  simp only [halfSegment, List.length_take, List.length_drop]
  omega

/-- The segment's actual stored shift comes from its original list index. -/
theorem halfSegment_getD {ss : List ℂ} {a h i : ℕ} (hi : i < h) :
    (halfSegment ss a h).getD i 0 = ss.getD (a + i) 0 := by
  simp only [halfSegment, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos hi, List.getElem?_drop]

/-- A row after the first $i$ shifted row solves of one selected segment. -/
noncomputable def shiftSolvePrefix {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (ss : List ℂ) (w : Fin n → ℂ) (i : ℕ) : Fin n → ℂ :=
  (ss.take i).foldl (fun v s => v ᵥ* (H - s • 1)⁻¹) w

/-- Before the first solve, the row is unchanged. -/
@[simp] theorem shiftSolvePrefix_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (ss : List ℂ) (w : Fin n → ℂ) : shiftSolvePrefix H ss w 0 = w := rfl

/-- One more stored shift is one more exact inverse row multiplication. -/
theorem shiftSolvePrefix_succ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (ss : List ℂ) (w : Fin n → ℂ) {i : ℕ} (hi : i < ss.length) :
    shiftSolvePrefix H ss w (i + 1) =
      shiftSolvePrefix H ss w i ᵥ* (H - ss.getD i 0 • 1)⁻¹ := by
  simp only [shiftSolvePrefix, List.take_succ_eq_append_getElem hi, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.getD_eq_getElem ss 0 hi]

/-- Completing a segment is its full row-solve fold. -/
theorem shiftSolvePrefix_last {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (ss : List ℂ) (w : Fin n → ℂ) :
    shiftSolvePrefix H ss w ss.length = ss.foldl (fun v s => v ᵥ* (H - s • 1)⁻¹) w := by
  rw [shiftSolvePrefix, List.take_length]

/-- The row after $e$ complete rounds of shifted row solves, starting at the last basis row. -/
noncomputable def halfSolvePrefix {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (e : ℕ) : Fin (n + 1) → ℂ :=
  (List.replicate e ss).flatten.foldl (fun v s => v ᵥ* (H - s • 1)⁻¹)
    (Pi.single (Fin.last n) 1)

/-- No inverse rounds give the initialized last basis row. -/
@[simp] theorem halfSolvePrefix_zero {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    halfSolvePrefix H ss 0 = Pi.single (Fin.last n) 1 := rfl

/-- A complete segment advances one inverse-polynomial power. -/
theorem halfSolvePrefix_succ {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (e : ℕ) :
    halfSolvePrefix H ss (e + 1) = shiftSolvePrefix H ss (halfSolvePrefix H ss e) ss.length := by
  simp only [halfSolvePrefix, shiftSolvePrefix, List.replicate_succ', List.flatten_append,
    List.flatten_singleton, List.foldl_append, List.take_length]

/-- The exact row-solve fold is the last row of the inverse polynomial power. -/
theorem halfSolvePrefix_eq_power {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (e : ℕ) :
    halfSolvePrefix H ss e = ((Polynomial.aeval H (shiftPoly ss))⁻¹ ^ e) (Fin.last n) := by
  exact (inv_aeval_shiftPoly_pow_apply_last H ss e).symm

end NLAlib.ShiftedQR
