/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpReadSeparation
public import NLAlib.Eigensolvers.SpectralBisection.DownArena
public import NLAlib.Eigensolvers.SpectralBisection.ResultGeometry

/-!
# Arena separation used by upward iteration

The complete arena collection and mathematical slot partition supply local result separation,
size-query protection, pending outcome protection and child result protection. These lemmas
expose the geometry once for the complete upward execution theorem.

## Main results

* `NLAlib.SpectralBisection.disj_results_step_of_arenas`: retain pending node outcomes.
* `NLAlib.SpectralBisection.disj_resultLevel_child_of_arenas`: retain occupied child results.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The complete arenas separate results of disjoint mathematical slot intervals. -/
theorem disj_results_of_arenas {n L d lo k j r : ℕ} (hd : d ≤ L + 1)
    (hslot : lo + k ≤ n) (hslot' : j + r ≤ n)
    (hsep : Disjoint (Finset.Ico lo (lo + k)) (Finset.Ico j (j + r)))
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (Fp.blocks (resultOperands n d lo ua ea) (resultLengths k))
      (Fp.blocks (resultOperands n d j ua ea) (resultLengths r)) := by
  have hUE := (apart_resultLevelSpan_of_arenas hd c ma ua qa ea sz kd kp lv su sg hAP).1
  apply disj_resultSlots hslot hslot' hsep ua ea
  simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using hUE

/-- Writing bounded current-level result fields preserves the actual size-query words. -/
theorem disj_resultLevel_sizes_of_arenas {n L d : ℕ} (hd : d ≤ L + 1)
    (ks : ℕ → ℕ) (hslot : ∀ lo < n, lo + ks lo ≤ n)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (resultLevelFootprint n d ks ua ea) (Store.inBlock sz.1 (sz.2 + n * d) n) := by
  have h := apart_resultLevel_size_of_arenas hd c ma ua qa ea sz kd kp lv su sg hAP
  have hx : Fp.Disj (resultLevelSpan n d ua ea) (Store.inBlock sz.1 (sz.2 + n * d) n) := by
    simpa [resultLevelSpan, Fp.blocks] using (h.take_drop (by rfl) 2).2.2
  exact hx.mono (resultLevelFootprint_le_span (d := d) hslot ua ea) le_rfl

/-- A different completed result slot preserves every actual field of a pending outcome. -/
theorem disj_results_step_of_arenas {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {n L d j k lo : ℕ} (base fuel : ℕ) (τ : Tape K) (R0 beta : K) (x : EighNode K)
    (hd : d ≤ L) (hslot : j + k ≤ n) (hslot' : lo + x.k ≤ n) (hp : 0 < x.k)
    (hsep : Disjoint (Finset.Ico j (j + k)) (Finset.Ico lo (lo + x.k)))
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    let step := eighStep (tapeMachine M dec mm qr n base τ) n fuel R0 beta
      x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    Fp.Disj (Fp.blocks (resultOperands n d j ua ea) (resultLengths k))
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp step) (stepOutputLengths step)) := by
  exact (disj_downRegion hslot hslot' hsep ma ua qa ea sz kd kp
    (apart_downArena hd hAP)).mono
      (resultSlot_le_downRegion (by omega) ma ua qa ea sz kd kp)
      (tapeStepFp_le_downRegion M dec mm qr n base fuel d lo τ R0 beta x hslot' hp
        ma ua qa ea sz kd kp)

/-- Parent reconstruction preserves the child result fields at the next depth. -/
theorem disj_resultLevel_child_of_arenas {K : Type} {n L d lo k : ℕ}
    (hd : d ≤ L) (ks : ℕ → ℕ) (hslot : ∀ j < n, j + ks j ≤ n)
    (step : EighStep K k) (hparent : lo + k ≤ n) (side : Bool)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (resultLevelFootprint n d ks ua ea)
      (Fp.blocks (resultOperands n (d + 1) (step.childSlot lo side) ua ea)
        (resultLengths (step.childSize side))) := by
  exact (disj_resultLevelSpans (e := d + 1) hd (by omega) (by omega)
    c ma ua qa ea sz kd kp lv su sg hAP).mono
      (resultLevelFootprint_le_span (d := d) hslot ua ea)
      (resultSlot_le_span (d := d + 1) (childSlot_add_childSize_le step hparent side) ua ea)

end NLAlib.SpectralBisection
