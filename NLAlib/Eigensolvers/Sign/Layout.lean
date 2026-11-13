/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.State

/-!
# Matrix and scalar subviews of the sign workspace

The sign iteration has three matrix regions and one five-word scalar workspace. Calls use
views of those regions, derived by the shared apart-subview rule. The loop changes only the
failure flag and temporary literal in the scalar workspace; its threshold, one and negated
threshold are outside the written footprint.

## Main results

* `NLAlib.Sign.apart_step`, `apart_test`: standard operand collections from the workspace.
* `NLAlib.Sign.disj_loopFootprint_constantsFootprint`: preserved control words across rounds.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

/-- The loop can change the three matrices, failure flag and temporary literal.
The scalar threshold, one and negated threshold are outside this footprint. -/
def loopFootprint (n : ℕ) (x w v t : ℕ × ℕ) : Fp :=
  Store.inBlock x.1 x.2 (2 * (n * n)) ⊔ Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
    Store.inBlock v.1 v.2 (2 * (n * n)) ⊔ Store.inBlock t.1 (t.2 + 1) 2

/-- The three scalar words held fixed throughout the iteration. -/
def constantsFootprint (t : ℕ × ℕ) : Fp :=
  Store.inBlock t.1 t.2 1 ⊔
    (Store.inBlock t.1 (t.2 + 3) 1 ⊔ Store.inBlock t.1 (t.2 + 4) 1)

/-- The matrix-step operands are views of the standard workspace. The temporary literal is
word two; the other four scalar words remain outside its region. -/
theorem apart_step {n : ℕ} {x w v t : ℕ × ℕ}
    (h : Fp.Apart [x, w, v, t] [2 * (n * n), 2 * (n * n), 2 * (n * n), 5]) :
    Fp.Apart [x, w, v, (t.1, t.2 + 2)]
      [2 * (n * n), 2 * (n * n), 2 * (n * n), 1] := by
  have hv := h.subviews (fun i : Fin 4 => i) ![0, 0, 0, 2]
    ![2 * (n * n), 2 * (n * n), 2 * (n * n), 1]
    (by intro i; fin_cases i <;> simp)
    (by intro a b hab hp; exact False.elim (hab hp))
  simpa [List.ofFn_succ] using hv

/-- The stopping-test operands are standard views of the three matrices and five-word
workspace. Their distinct scalar offsets prove separation once; matrix disjointness is inherited. -/
theorem apart_test {n : ℕ} {x w v t : ℕ × ℕ}
    (h : Fp.Apart [x, w, v, t] [2 * (n * n), 2 * (n * n), 2 * (n * n), 5]) :
    Fp.Apart [x, (t.1, t.2 + 3), (t.1, t.2 + 4), t, w, v, (t.1, t.2 + 1)]
      [2 * (n * n), 1, 1, 1, 2 * (n * n), 2 * (n * n), 1] := by
  have hv := h.subviews (![0, 3, 3, 3, 1, 2, 3] : Fin 7 → Fin 4)
    ![0, 3, 4, 0, 0, 0, 1] ![2 * (n * n), 1, 1, 1, 2 * (n * n), 2 * (n * n), 1]
    (by intro i; fin_cases i <;> simp)
    (by intro a b hab hp; fin_cases a <;> fin_cases b <;> simp at hab hp ⊢)
  simpa [List.ofFn_succ] using hv

/-- The whole loop's written region is disjoint from its threshold, one and negated threshold.
Matrix separation follows from the standard workspace; scalar separation is interval arithmetic. -/
theorem disj_loopFootprint_constantsFootprint {n : ℕ} {x w v t : ℕ × ℕ}
    (h : Fp.Apart [x, w, v, t] [2 * (n * n), 2 * (n * n), 2 * (n * n), 5]) :
    Fp.Disj (loopFootprint n x w v t) (constantsFootprint t) := by
  have hx := h.disj_getD (i := 0) (j := 3) (by simp) (by simp) (by simp)
  have hw := h.disj_getD (i := 1) (j := 3) (by simp) (by simp) (by simp)
  have hv := h.disj_getD (i := 2) (j := 3) (by simp) (by simp) (by simp)
  have hmat : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)) ⊔
      Store.inBlock w.1 w.2 (2 * (n * n)) ⊔ Store.inBlock v.1 v.2 (2 * (n * n)))
      (Store.inBlock t.1 t.2 5) := Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hx, hw⟩, hv⟩
  have hsub : constantsFootprint t ≤ Store.inBlock t.1 t.2 5 := by
    fp_sub [constantsFootprint]
  exact Fp.disj_sup_left.mpr ⟨hmat.mono le_rfl hsub, by disjoint [constantsFootprint]⟩

end NLAlib.Sign
