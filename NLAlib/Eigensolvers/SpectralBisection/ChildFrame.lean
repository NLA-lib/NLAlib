/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ChildStorage
public import NLAlib.Eigensolvers.SpectralBisection.StepRead
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# Dormant size words through a complete downward level

The level loop writes only the exact outcomes of its active nodes and shared scratch. A
slot absent from the next mathematical level is not one of those outcomes' child size cells.
Spatial arena separation then preserves its original size word, including initialized zero.

## Main results

* `NLAlib.SpectralBisection.size_get_eq_of_absent_next`: absent slots retain their size words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Exact active-node frames preserve any absent next-level size cell. The family `x` is
mathematical specification data; actual code still obtains its dimensions from stored words. -/
theorem size_get_eq_of_absent_next {K : Type} (F : FloatMachine K ℕ ℕ)
    {n fuel d j : ℕ} {R0 beta : K} {root : EighNode K} (x : ℕ → EighNode K)
    (ma ua qa ea sz kd kp : ℕ × ℕ) {scratch : Fp} {s s' : Store K}
    (hj : j < n)
    (hReached : ∀ lo < n, 0 < (x lo).k → ∃ a : List Bool, a.length = d ∧
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x lo))
    (hPayload : ∀ lo < n, 0 < (x lo).k →
      Fp.Disj (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n)
        (stepPayloadFp n d lo ma ua qa ea sz kd kp
          (eighStep F n fuel R0 beta (x lo).A (x lo).R (x lo).ε (x lo).ℓ
            (eighTapeSample n d lo))))
    (hScratch : ¬ scratch sz.1 (sz.2 + n * (d + 1) + j))
    (hfr : s.EqOff (Fp.loopPrefix (fun lo => activeStepFp n d lo ma ua qa ea sz kd kp
      (eighStep F n fuel R0 beta (x lo).A (x lo).R (x lo).ε (x lo).ℓ
        (eighTapeSample n d lo))) n ⊔ scratch) s')
    (hAbsent : ∀ (path : List Bool) (y : EighNode K), path.length = d + 1 →
      eighLoc F n fuel R0 beta 0 0 root path ≠ some (j, y)) :
    s'.get sz.1 (sz.2 + n * (d + 1) + j) =
      s.get sz.1 (sz.2 + n * (d + 1) + j) := by
  apply hfr.get_eq
  intro h
  rcases h with ⟨lo, hlo, hcell⟩ | hs
  · by_cases hp : 0 < (x lo).k
    · obtain ⟨a, ha, hx⟩ := hReached lo hlo hp
      exact not_stepFp_size_of_absent_next F ma ua qa ea sz kd kp hj ha hx
        (hPayload lo hlo hp) hAbsent (by simpa only [activeStepFp, if_pos hp] using hcell)
    · simp only [activeStepFp, if_neg hp] at hcell
      exact hcell
  · exact hScratch hs

end NLAlib.SpectralBisection
