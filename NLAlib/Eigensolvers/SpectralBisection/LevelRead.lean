/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Storage
public import NLAlib.Eigensolvers.SpectralBisection.StepRead

/-!
# Read footprints of global mathematical level representations

The global input and outcome predicates inherit the read footprints of their scalar and
packed matrix fields. Any coarse enclosing footprint is sufficient. Separation from that
footprint transports the original represented data through completed deeper-level writes.

## Main results

* `NLAlib.SpectralBisection.readsOnly_storesLevel`: locality of represented level inputs.
* `NLAlib.SpectralBisection.readsOnly_storesRecords`: locality of represented level outcomes.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Level inputs read only their reached node fields, absent size words and parameter pair.
The supplied inclusions permit one coarse arena footprint for all these reads. -/
theorem readsOnly_storesLevel {K : Type} (M : Machine K) (F : FloatMachine K ℕ ℕ)
    (n fuel : ℕ) (R0 beta : K) (root : EighNode K) (d : ℕ)
    (ma sz lv : ℕ × ℕ) (pos : ℕ) (G : Fp)
    (hNode : ∀ (a : List Bool) lo (x : EighNode K), a.length = d →
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) →
        Store.inBlock sz.1 (sz.2 + n * d + lo) 1 ⊔
          Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo)
            (2 * (x.k * x.k)) ≤ G)
    (hAbsent : Store.inBlock sz.1 (sz.2 + n * d) n ≤ G)
    (hParams : Store.inBlock lv.1 (lv.2 + 2 * d) 2 ≤ G) :
    Store.ReadsOnly G (fun s => StoresLevel M F n fuel R0 beta root d ma sz lv ⟨s, pos⟩) := by
  intro s s' hagree h
  refine ⟨?_, ?_, ?_⟩
  · intro a lo x ha hx
    exact ((Store.readsOnly_get _ _ _).and (Store.readsOnly_readBlock _ _ _ _)).mono
      (hNode a lo x ha hx) s s' hagree (h.1 a lo x ha hx)
  · intro lo hlo hnone
    exact (hagree _ _ (hAbsent _ _ ⟨rfl, by omega, by omega⟩)).trans (h.2.1 lo hlo hnone)
  · exact (Store.readsOnly_readBlock _ _ _ _).mono hParams s s' hagree h.2.2

/-- Stored outcomes read only their exact result blocks. A single enclosing footprint can
therefore protect all still-needed outcomes of a shallower level. -/
theorem readsOnly_storesRecords {K : Type} (M : Machine K) (F : FloatMachine K ℕ ℕ)
    (n fuel : ℕ) (R0 beta : K) (root : EighNode K) (d : ℕ)
    (ma ua qa ea sz kd kp : ℕ × ℕ) (pos : ℕ) (G : Fp)
    (hBlocks : ∀ (a : List Bool) lo (x : EighNode K), a.length = d →
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) → 0 < x.k →
        Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp
          (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)))
          (stepOutputLengths
            (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo))) ≤ G) :
    Store.ReadsOnly G
      (fun s => StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp ⟨s, pos⟩) := by
  intro s s' hagree h a lo x ha hx hp
  exact (readsOnly_storesStep M x.R n d lo ma ua qa ea sz kd kp _ pos).mono
    (hBlocks a lo x ha hx hp) s s' hagree (h a lo x ha hx hp)

end NLAlib.SpectralBisection
