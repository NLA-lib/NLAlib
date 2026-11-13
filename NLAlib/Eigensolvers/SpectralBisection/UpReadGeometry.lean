/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownGeometry
public import NLAlib.Eigensolvers.SpectralBisection.LevelRead
public import NLAlib.Eigensolvers.SpectralBisection.TapeMachine

/-!
# Coarse shallow read regions for upward reconstruction

All input fields and stored node outcomes at one depth lie in a fixed collection of level
arenas. Its only result reads are in the current basis and eigenvalue levels. Completed
deeper result levels can therefore preserve these reads by ordinary interval separation.

## Main results

* `NLAlib.SpectralBisection.upReadRegion`: a coarse enclosing shallow read footprint.
* `NLAlib.SpectralBisection.readsOnly_storesLevel_upReadRegion`: input-level locality.
* `NLAlib.SpectralBisection.readsOnly_storesRecords_upReadRegion`: outcome locality.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Node outcome arenas, input matrix/size levels, parameter pair and literal-two cell.
The extra size word includes the initialized size cell of an empty root. -/
def upReadRegion (n d : ℕ) (ma lv ua qa ea sz kd kp c : ℕ × ℕ) : Fp :=
  downLevelRegion n d ma ua qa ea sz kd kp ⊔
    Fp.blocks [(ma.1, ma.2 + 2 * (n * n) * d), (sz.1, sz.2 + n * d),
      (lv.1, lv.2 + 2 * d), (c.1, c.2 + 1)] [2 * (n * n), n + 1, 2, 1]

/-- The literal-two cell is part of the shared shallow read region. -/
theorem constant_le_upReadRegion (n d : ℕ) (ma lv ua qa ea sz kd kp c : ℕ × ℕ) :
    Store.inBlock c.1 (c.2 + 1) 1 ≤ upReadRegion n d ma lv ua qa ea sz kd kp c := by
  exact fun _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- A reached node's size and packed input matrix lie in the shallow read region. -/
theorem nodeInput_le_upReadRegion {n d lo k : ℕ} (hslot : lo + k ≤ n)
    (ma lv ua qa ea sz kd kp c : ℕ × ℕ) :
    Store.inBlock sz.1 (sz.2 + n * d + lo) 1 ⊔
      Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ≤
        upReadRegion n d ma lv ua qa ea sz kd kp c := by
  apply sup_le
  · have hs : Store.inBlock sz.1 (sz.2 + n * d + lo) 1 ≤
        Store.inBlock sz.1 (sz.2 + n * d) (n + 1) :=
      Fp.inBlock_le_inBlock (by omega) (by omega)
    exact hs.trans (fun _ _ h => Or.inr (Or.inr (Or.inl h)))
  · have hm : Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ≤
        Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d) (2 * (n * n)) := by
      apply Fp.inBlock_le_inBlock (by omega)
      have hk : k ≤ n := by omega
      have hkk := Nat.mul_le_mul_left k hk
      have hn := Nat.mul_le_mul_left n hslot
      nlinarith
    exact hm.trans (fun _ _ h => Or.inr (Or.inl h))

/-- Canonical-root represented level inputs read only the shallow region. -/
theorem readsOnly_storesLevel_upReadRegion {K : Type} (M : Machine K)
    (F : FloatMachine K ℕ ℕ) (n fuel : ℕ) (R0 eps beta : K) (ell d : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (ma lv ua qa ea sz kd kp c : ℕ × ℕ) (pos : ℕ) :
    Store.ReadsOnly (upReadRegion n d ma lv ua qa ea sz kd kp c)
      (fun s => StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma sz lv ⟨s, pos⟩) := by
  apply readsOnly_storesLevel
  · intro a lo x _ hx
    exact nodeInput_le_upReadRegion (add_k_le_and_of_eighLoc hx).1 ma lv ua qa ea sz kd kp c
  · intro b i h
    exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1, by have := h.2.2; omega⟩))
  · exact fun _ _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- Indexed-reference step outputs fit the same slot reservation as the actual raw-word
execution. The sampler equality supplies the bridge without changing any operation model. -/
theorem tapeStepFp_le_downRegion {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (n base fuel d lo : ℕ) (τ : Tape K) (R0 beta : K) (x : EighNode K)
    (hslot : lo + x.k ≤ n) (hp : 0 < x.k) (ma ua qa ea sz kd kp : ℕ × ℕ) :
    let step := eighStep (tapeMachine M dec mm qr n base τ) n fuel R0 beta
      x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp step) (stepOutputLengths step) ≤
      downRegion n d lo x.k ma ua qa ea sz kd kp := by
  dsimp only
  rw [eighStep_tapeMachine M dec mm qr n base τ d lo fuel R0 beta x.R x.ε x.ℓ x.A hslot]
  exact stepFp_le_downRegion M dec mm qr hslot hp R0 beta x.R x.ε
    (vec (levelUniformWords n base τ d) lo) (levelGaussianMatrix n base τ d)
    x.A ma ua qa ea sz kd kp

/-- Actual indexed-sample outcomes read only the shallow region. The slot bound transports
the existing raw-word footprint theorem through the checked sample-coordinate equality. -/
theorem readsOnly_storesRecords_upReadRegion {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (n base fuel : ℕ) (τ : Tape K) (R0 eps beta : K) (ell d : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (ma lv ua qa ea sz kd kp c : ℕ × ℕ) (pos : ℕ) :
    Store.ReadsOnly (upReadRegion n d ma lv ua qa ea sz kd kp c)
      (fun s => StoresRecords M (tapeMachine M dec mm qr n base τ) n fuel R0 beta
        ⟨n, A, R0, eps, ell⟩ d ma ua qa ea sz kd kp ⟨s, pos⟩) := by
  apply readsOnly_storesRecords
  intro a lo x ha hx hp
  have hslot := (add_k_le_and_of_eighLoc hx).1
  exact (tapeStepFp_le_downRegion M dec mm qr n base fuel d lo τ R0 beta x hslot hp
    ma ua qa ea sz kd kp).trans
      ((downRegion_le_level hslot ma ua qa ea sz kd kp).trans le_sup_left)

end NLAlib.SpectralBisection
