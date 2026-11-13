/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Storage

/-!
# Stored records under scratch cleanup

All words of a represented node outcome belong to its seven arena handles. Agreement below
those handles therefore retains all mathematical level records after scoped scratch is freed.

## Main results

* `NLAlib.SpectralBisection.StoresRecords.of_below`: records survive scratch cleanup.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Every output word of a mathematical outcome belongs to one of its seven arena handles. -/
theorem stepOutputs_below {K : Type} {n d lo k bound : ℕ} {ma ua qa ea sz kd kp : ℕ × ℕ}
    (hl : ∀ z ∈ [ma, ua, qa, ea, sz, kd, kp], z.1 < bound) (step : EighStep K k) :
    ∀ z ∈ stepOutputs n d lo ma ua qa ea sz kd kp step, z.1 < bound := by
  have hs : ma.1 < bound ∧ ua.1 < bound ∧ qa.1 < bound ∧ ea.1 < bound ∧ sz.1 < bound ∧
      kd.1 < bound ∧ kp.1 < bound := by simpa using hl
  cases step <;> simp [stepOutputs, splitOutputs] <;> tauto

/-- Agreement below the seven surviving arena handles preserves every stored level record. -/
theorem StoresRecords.of_below {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d bound : ℕ} {R0 beta : K} {root : EighNode K}
    {ma ua qa ea sz kd kp : ℕ × ℕ} {m m' : Mem K}
    (hfr : Store.Below bound m.store m'.store)
    (hl : ∀ z ∈ [ma, ua, qa, ea, sz, kd, kp], z.1 < bound)
    (h : StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp m) :
    StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp m' := by
  intro a lo x ha hx hp
  exact (h a lo x ha hx hp).of_below hfr (stepOutputs_below hl _)

end NLAlib.SpectralBisection
