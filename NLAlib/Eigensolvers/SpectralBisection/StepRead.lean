/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.State
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Read footprints of stored bisection outcomes

A represented step reads exactly its output tuple. Its mathematical shift relation is constant
with respect to memory. Generic independent-loop rules can therefore retain completed outcomes
while later slots and shared scratch change.

## Main results

* `NLAlib.SpectralBisection.readsOnly_storesStep`: the existing stored-step predicate is local.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The occupied result cells of an active node; an empty size slot executes no node program. -/
def activeStepFp {K : Type} (n d lo : ℕ) (ma ua qa ea sz kd kp : ℕ × ℕ)
    {k : ℕ} (step : EighStep K k) : Fp :=
  if 0 < k then Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp step)
    (stepOutputLengths step) else ⊥

/-- The stored mathematical outcome depends only on its actual output cells. -/
theorem readsOnly_storesStep {K : Type} (M : Machine K) (R : K) (n d lo : ℕ)
    (ma ua qa ea sz kd kp : ℕ × ℕ) {k : ℕ} (step : EighStep K k) (pos : ℕ) :
    Store.ReadsOnly (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp step)
      (stepOutputLengths step))
      (fun s => StoresStep M R n d lo ma ua qa ea sz kd kp step ⟨s, pos⟩) := by
  intro s s' h hs
  exact ⟨hs.1, Store.readsOnly_readBlocks _ _ _ pos s s' h hs.2⟩

/-- Active stored outcomes have exactly their result footprint; inactive slots read no cells. -/
theorem readsOnly_activeStoresStep {K : Type} (M : Machine K) (R : K) (n d lo : ℕ)
    (ma ua qa ea sz kd kp : ℕ × ℕ) {k : ℕ} (step : EighStep K k) (pos : ℕ) :
    Store.ReadsOnly (activeStepFp n d lo ma ua qa ea sz kd kp step)
      (fun s => if 0 < k then StoresStep M R n d lo ma ua qa ea sz kd kp step ⟨s, pos⟩
        else True) := by
  by_cases hpos : 0 < k
  · simpa only [activeStepFp, if_pos hpos] using
      readsOnly_storesStep M R n d lo ma ua qa ea sz kd kp step pos
  · simp only [activeStepFp, if_neg hpos]
    exact fun _ _ _ _ => trivial

/-- A represented outcome is independent of the tape position: identical stores give the
same stored words and mathematical shift relation. -/
theorem StoresStep.of_store_eq {K : Type} {M : Machine K} {R : K} {n d lo k : ℕ}
    {ma ua qa ea sz kd kp : ℕ × ℕ} {step : EighStep K k} {μ ν : Mem K}
    (hstore : μ.store = ν.store)
    (h : StoresStep M R n d lo ma ua qa ea sz kd kp step μ) :
    StoresStep M R n d lo ma ua qa ea sz kd kp step ν :=
  StoresStep.of_eqOff (F := ⊥) (by rw [← hstore]; exact Store.EqOff.refl _ _)
    (Fp.disj_bot_left _) h

end NLAlib.SpectralBisection
