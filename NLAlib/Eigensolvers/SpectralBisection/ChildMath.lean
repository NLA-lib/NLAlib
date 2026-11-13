/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ChildStorage

/-!
# Recovering parents of reached mathematical nodes

The existing path-append rule factors a non-root traversal into its reached parent and a
single occupied child. These facts connect stored mathematical outcomes to the next level.

## Main results

* `NLAlib.SpectralBisection.eighLoc_parent`: a reached successor node has a reached parent.
* `NLAlib.SpectralBisection.eighLoc_singleton_child`: a singleton follows constructor data.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

/-- A singleton traversal reaches exactly the occupied constructor child. -/
theorem eighLoc_singleton_child {K : Type} (F : FloatMachine K ℕ ℕ)
    {n fuel d lo lo' : ℕ} {R0 beta : K} {x y : EighNode K} {side : Bool}
    (h : eighLoc F n fuel R0 beta d lo x [side] = some (lo', y)) :
    let step := eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    let p := eighNextParams F x.R x.ε x.ℓ
    step.HasChild side ∧ lo' = step.childSlot lo side ∧
      y = ⟨step.childSize side, step.childMatrix side, p.1, p.2, x.ℓ + 1⟩ := by
  cases hs : eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo) with
  | leaf U values => simp [eighLoc, hs] at h
  | shift b A sigma =>
    by_cases hb : side = b
    · simpa [eighLoc, hs, EighStep.HasChild, EighStep.childSlot,
        EighStep.childSize, EighStep.childMatrix, hb] using h.symm
    · simp [eighLoc, hs, hb] at h
  | split r hr Qp Qm Ap Am sigma =>
    cases side <;>
      simpa [eighLoc, hs, EighStep.HasChild, EighStep.childSlot,
        EighStep.childSize, EighStep.childMatrix] using h.symm

/-- Every reached successor-depth node factors through a reached parent and singleton path. -/
theorem eighLoc_parent {K : Type} (F : FloatMachine K ℕ ℕ)
    {n fuel d lo' : ℕ} {R0 beta : K} {root y : EighNode K} {path : List Bool}
    (hlen : path.length = d + 1)
    (h : eighLoc F n fuel R0 beta 0 0 root path = some (lo', y)) :
    ∃ (a : List Bool) (side : Bool) (lo : ℕ) (x : EighNode K),
      a.length = d ∧ path = a ++ [side] ∧
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) ∧
      eighLoc F n fuel R0 beta d lo x [side] = some (lo', y) := by
  have hne : path ≠ [] := by intro he; simp [he] at hlen
  have he := List.dropLast_append_getLast hne
  have ha : path.dropLast.length = d := by
    have := congrArg List.length he
    simp only [List.length_append, List.length_singleton] at this
    omega
  rw [← he, eighLoc_append_singleton] at h
  obtain ⟨⟨lo, x⟩, hx, hc⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨path.dropLast, path.getLast hne, lo, x, ha, he.symm, hx,
    by simpa only [ha, Nat.zero_add] using hc⟩

end NLAlib.SpectralBisection
