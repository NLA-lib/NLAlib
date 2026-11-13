/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLayout
public import NLAlib.Ops.Logic.Allocation

/-!
# Downward level frames and scoped scratch

The exact active outputs lie inside the seven caller-owned output levels. The other writes
belong to the next parameters, sample batches and one fresh scalar scratch handle.

## Main results

* `NLAlib.SpectralBisection.activeStepPrefix_le_downLevel`: the complete exact scan frame.
* `NLAlib.SpectralBisection.downFrame_le_output_scratch`: caller output and fresh scratch.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- All occupied node outputs of a bounded level lie inside its seven output regions. -/
theorem activeStepPrefix_le_downLevel {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {n d fuel ell : ℕ} (ks : ℕ → ℕ)
    (A : ∀ lo, Matrix (Fin (ks lo)) (Fin (ks lo)) (K × K))
    (hslot : ∀ lo < n, lo + ks lo ≤ n) (R0 beta R eps : K)
    (U : ℕ → K) (S : ℕ → ℕ → K × K) (ma ua qa ea sz kd kp : ℕ × ℕ) :
    Fp.loopPrefix (fun lo => activeStepFp n d lo ma ua qa ea sz kd kp
      (eighStep (M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2))
        n fuel R0 beta (A lo) R eps ell (storedNodeSample n lo (U lo) S))) n ≤
      downLevelRegion n d ma ua qa ea sz kd kp := by
  rintro b x ⟨lo, hi, hx⟩
  exact ((activeStepFp_le_downRegion M dec mm qr (d := d) (fuel := fuel) (ell := ell)
    (hslot lo hi) R0 beta R eps (U lo) S (A lo) ma ua qa ea sz kd kp).trans
      (downRegion_le_level (hslot lo hi) ma ua qa ea sz kd kp)) b x hx

/-- Removing a fresh scalar scratch handle leaves exactly the caller-owned level footprint. -/
theorem downFrame_le_output_scratch {n d bound : ℕ}
    (lv su sg ma ua qa ea sz kd kp t : ℕ × ℕ) {G : Fp}
    (hG : G ≤ downLevelRegion n d ma ua qa ea sz kd kp) (ht : bound ≤ t.1) :
    downPrepareFp n d lv su sg t ⊔ (G ⊔ Store.inBlock t.1 (t.2 + 4) 1) ≤
      downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp ⊔ Fp.above bound := by
  rintro b i h
  rcases h with ((hv | ht0) | (hu | hg)) | (hnode | ht4)
  · exact Or.inl (Or.inl (Or.inl hv))
  · rcases ht0 with ⟨rfl, _, _⟩; exact Or.inr ht
  · exact Or.inl (Or.inl (Or.inr (Or.inl hu)))
  · exact Or.inl (Or.inl (Or.inr (Or.inr hg)))
  · exact Or.inl (Or.inr (hG b i hnode))
  · rcases ht4 with ⟨rfl, _, _⟩; exact Or.inr ht

end NLAlib.SpectralBisection
