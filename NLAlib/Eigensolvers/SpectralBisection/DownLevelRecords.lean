/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.SlotNodes
public import NLAlib.Eigensolvers.SpectralBisection.LevelSuccessor
public import NLAlib.Eigensolvers.SpectralBisection.DownPayloadGeometry
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# Global records from the downward scan

Typed slot lookups share the level's mathematical parameters. Actual outcomes on stored
sample batches therefore give the indexed-tape records directly; the lookups remain pure
specification data and never replace the program's stored-size queries.

## Main results

* `NLAlib.SpectralBisection.storesRecords_of_downSlots`: common-parameter scan outcomes.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The common level parameters identify each reached slot's actual rounded step. -/
theorem storesRecords_of_downSlots {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (n base : ℕ) (τ : Tape K) (fuel : ℕ) (R0 eps beta : K) (ell : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (d : ℕ)
    (ma ua qa ea sz kd kp : ℕ × ℕ) (m : Mem K)
    (hSlots : ∀ lo < n,
      let F := tapeMachine M dec mm qr n base τ
      let x := nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo
      let p := eighLevelParams F R0 eps ell d
      0 < x.k → StoresStep M p.1 n d lo ma ua qa ea sz kd kp
        (eighStep (M.toFloatMachine dec mm qr M.mul
          (fun z : K × K => M.normalWords z.1 z.2)) n fuel R0 beta x.A p.1 p.2 (ell + d)
          (storedNodeSample n lo (vec (levelUniformWords n base τ d) lo)
            (levelGaussianMatrix n base τ d))) m) :
    StoresRecords M (tapeMachine M dec mm qr n base τ) n fuel R0 beta
      ⟨n, A, R0, eps, ell⟩ d ma ua qa ea sz kd kp m := by
  apply storesRecords_of_nodeAtSlot_steps M dec mm qr n base τ fuel R0 eps beta ell A d
    ma ua qa ea sz kd kp m
  intro lo hlo
  have hp := nodeAtSlot_params (tapeMachine M dec mm qr n base τ) n fuel R0 eps beta
    ell A d lo
  dsimp only at hp ⊢
  rw [hp.1, hp.2.1, hp.2.2]
  exact hSlots lo hlo

/-- Stored batch outcomes and indexed tape outcomes agree at every typed root slot. -/
theorem eighStep_nodeAtSlot_tapeMachine {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (n base : ℕ) (τ : Tape K) (fuel : ℕ) (R0 eps beta : K) (ell : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (d lo : ℕ) (hlo : lo < n) :
    let F := tapeMachine M dec mm qr n base τ
    let x := nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo
    let p := eighLevelParams F R0 eps ell d
    eighStep (M.toFloatMachine dec mm qr M.mul
      (fun z : K × K => M.normalWords z.1 z.2)) n fuel R0 beta x.A p.1 p.2 (ell + d)
      (storedNodeSample n lo (vec (levelUniformWords n base τ d) lo)
        (levelGaussianMatrix n base τ d)) =
      eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo) := by
  dsimp only
  have hp := nodeAtSlot_params (tapeMachine M dec mm qr n base τ) n fuel R0 eps beta
    ell A d lo
  dsimp only at hp
  rw [hp.1, hp.2.1, hp.2.2]
  apply Eq.symm
  apply eighStep_tapeMachine
  have hk := nodeAtSlot_k_le (tapeMachine M dec mm qr n base τ) n fuel R0 eps beta
    ell A d lo
  omega

/-- Exact scan writes preserve unoccupied size words and establish the complete next level.
The scratch footprint may include the parameter update and the two sampled batches. -/
theorem storesLevel_succ_of_downFrame {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (n base : ℕ) (τ : Tape K) (fuel : ℕ) (R0 eps beta : K) (ell : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (d : ℕ)
    (ma ua qa ea sz kd kp lv : ℕ × ℕ) (scratch : Fp) (before after : Mem K)
    (hRecords : StoresRecords M (tapeMachine M dec mm qr n base τ) n fuel R0 beta
      ⟨n, A, R0, eps, ell⟩ d ma ua qa ea sz kd kp after)
    (hZero : ∀ j < n, before.store.get sz.1 (sz.2 + n * (d + 1) + j) = some (M.lit 0))
    (hParams : after.store.readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 =
      some [(eighLevelParams (tapeMachine M dec mm qr n base τ) R0 eps ell (d + 1)).1,
        (eighLevelParams (tapeMachine M dec mm qr n base τ) R0 eps ell (d + 1)).2])
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n))
    (hScratch : Fp.Disj scratch (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n)) :
    let F := tapeMachine M dec mm qr n base τ
    let x := fun lo => nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo
    let p := eighLevelParams F R0 eps ell d
    before.store.EqOff
      (Fp.loopPrefix (fun lo => activeStepFp n d lo ma ua qa ea sz kd kp
        (eighStep (M.toFloatMachine dec mm qr M.mul
          (fun z : K × K => M.normalWords z.1 z.2)) n fuel R0 beta (x lo).A p.1 p.2 (ell + d)
          (storedNodeSample n lo (vec (levelUniformWords n base τ d) lo)
            (levelGaussianMatrix n base τ d)))) n ⊔ scratch) after.store →
      StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ (d + 1) ma sz lv after := by
  dsimp only
  intro hfr
  let F := tapeMachine M dec mm qr n base τ
  let x := fun lo => nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo
  have hregion (lo : ℕ) (hlo : lo < n) :=
    eighStep_nodeAtSlot_tapeMachine M dec mm qr n base τ fuel R0 eps beta ell A d lo hlo
  apply storesLevel_succ M F x ma ua qa ea sz kd kp lv hRecords hZero hParams
  · intro lo _ hpos
    exact exists_eighLoc_of_nodeAtSlot_k_pos hpos
  · intro lo hlo hpos
    have hk := nodeAtSlot_k_le F n fuel R0 eps beta ell A d lo
    change (x lo).k ≤ n - lo at hk
    exact (disj_stepPayloadFp_size (by omega) hpos ma ua qa ea sz kd kp _ hAP).symm
  · exact hScratch
  · apply hfr.mono
    refine sup_le_sup (Fp.loopPrefix_mono ?_) le_rfl
    intro lo hlo
    rw [← hregion lo hlo]

end NLAlib.SpectralBisection
