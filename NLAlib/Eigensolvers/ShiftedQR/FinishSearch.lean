/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.IterationAlg

/-!
# Total completion of the scalar shift search

The promising search is called only after all stored Ritz candidates were rejected. The
mathematical rejection theorem then supplies its inverse-domain assumptions. The grid search
and final guarded trial compute the defined first-accepted/default matrix even when the full
candidate list contains no accepted shift. Registers and trial matrix are fresh workspace of
the enclosing iteration; their handle inequalities are discharged by its scoped allocations.

## Main results

* `NLAlib.ShiftedQR.candidates_eq_streamedGrid`: the actual streaming order.
* `NLAlib.ShiftedQR.finishRitzSearchWith_writes`: exact search completion including fallback.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The stored Ritz list, promising candidate and streamed grid have exactly the mathematical
strategy's candidate order when the grid denominator is the prescribed ceiling. -/
theorem candidates_eq_streamedGrid {n m D : ℕ} (B θ α γ : ℝ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ)
    (hD : D = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊) :
    ss ++ shqrCandidates B θ α γ m H ss = (ss ++ [findRitz H m 1 ss]) ++
      gridPoints (findRitz H m 1 ss)
        (exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H)) D := by
  rw [shqrCandidates, squareGrid_eq_gridPoints, ← hD]
  simp only [List.append_assoc, List.singleton_append]

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- Complete the actual three-phase search in the enclosing iteration's fresh register and
trial buffers. Singular candidate shifts are safe: a rejected shift is mathematically
nonsingular before the promising search uses its inverse. A wholly rejected list returns the
actual promising-shift fallback matrix, rather than an uninitialized or stale output. -/
theorem finishRitzSearchWith_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {F : Impl O Q} (hF : RitzSearchContract F I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m D : ℕ} {w ss c r z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ B θ α γ : ℝ} {shifts : List ℂ}
    (hHess : IsUpperHessenberg H) (hlen : shifts.length = 2 ^ m) (hk : 2 ^ m ≤ n)
    (hτ : 0 ≤ τ) (hDp : 0 < D)
    (hD : D = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hH : HoldsMatrix w H μ.store) (hSS : HoldsMatrix ss (shiftColumn shifts) μ.store)
    (hThreshold : μ.store.get c.1 c.2 = some (τ ^ 2))
    (hTarget : μ.store.get r.1 (r.2 + 1) =
      some ((1 - γ) ^ (2 * (2 ^ m)) * subdiagNormSqProd (2 ^ m) H))
    (hRadius : μ.store.get r.1 (r.2 + 2) =
      some (exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H)))
    (hState : CandidateHolds τ γ (2 ^ m) H shifts z (r.1, r.2 + 3) μ.store)
    (hl : μ.Live [w, ss, c, r, z]) (hr : r.2 + 8 ≤ μ.store.len r.1)
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len z.1)
    (hFreshR : r.1 ≠ w.1 ∧ r.1 ≠ ss.1 ∧ r.1 ≠ c.1 ∧ r.1 ≠ z.1)
    (hFreshZ : z.1 ≠ w.1 ∧ z.1 ≠ ss.1 ∧ z.1 ≠ c.1) :
    Writes .total I tape (finishRitzSearchWith F).body
      (Env.frame [n + 1, m, 2 ^ m, D] [w, ss, c, r, z, z, r])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 8)
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix z (shqrAcceptStep τ B θ α γ m H shifts) μ'.store) μ := by
  classical
  rcases hFreshR with ⟨hrw, hrss, hrc, hrz⟩
  rcases hFreshZ with ⟨hzw, hzss, hzc⟩
  have hwl := hl w (by simp)
  have hssl := hl ss (by simp)
  have hcl := hl c (by simp)
  have hrl := hl r (by simp)
  have hzl := hl z (by simp)
  have hkp : 0 < 2 ^ m := by positivity
  unfold finishRitzSearchWith
  cases he : shifts.find? (fun s => decide (IsShiftAccept τ γ (2 ^ m) H s)) with
  | none =>
    have hFlag := hState.flag_of_none he
    refine writes_ite rfl rfl (hC.test_isZero (d := []) hFlag) ?_
    simp only [id_eq, decide_true, if_true]
    have hdet := hHess.det_sub_smul_one_ne_zero_of_find_none (by omega) hkp hτ he
    have hFind := hF (μ := μ) (m := m) (tape := tape) (h := w) (ss := ss)
      (r := (r.1, r.2 + 4)) H shifts
      hHess hlen hdet hH hSS (by room) (by dsimp only; omega) (by disjoint)
    refine hFind.frame_seq_le rfl rfl (by room) (by fp_sub) ?_
    intro μ₁ hfr₁ ⟨hp₁, hCenter₁⟩
    have hH₁ := hH.of_eqOff hfr₁ (by disjoint)
    have hT₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hThreshold
    have hTarget₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hTarget
    have hRadius₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hRadius
    have hState₁ := hState.of_eqOff hfr₁ (by disjoint)
    have hTry := tryCandidate_writes (τp := tape) (m := μ₁)
      (a := w) (s := (r.1, r.2 + 4)) (t := c) (target := (r.1, r.2 + 1))
      (z := z) (f := (r.1, r.2 + 3)) hS hE hL hC hk hτ hH₁
      hCenter₁ hT₁ hTarget₁ hState₁ (by room)
      (by rw [hfr₁.len_eq]; exact hz) (by dsimp only; rw [hfr₁.len_eq]; omega)
      (by disjoint) (by disjoint)
    refine hTry.frame_seq_le rfl rfl (by room) (by fp_sub) ?_
    intro μ₂ hfr₂ ⟨hp₂, hState₂, _⟩
    have hH₂ := hH₁.of_eqOff hfr₂ (by disjoint)
    have hT₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hT₁
    have hTarget₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hTarget₁
    have hRadius₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hRadius₁
    have hCenter₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hCenter₁
    have hGrid := searchGridWithScratch_writes (τp := tape) (m := μ₂) (D := D)
      (a := w) (c := (r.1, r.2 + 4)) (r := (r.1, r.2 + 2)) (t := c)
      (target := (r.1, r.2 + 1)) (s := (r.1, r.2 + 6)) (z := z) (f := (r.1, r.2 + 3))
      hS hE hL hC hk hτ (by omega) hH₂ hCenter₂ hRadius₂ hT₂ hTarget₂ hState₂
      (by room) (by dsimp only; rw [hfr₂.len_eq, hfr₁.len_eq]; omega)
      (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hz)
      (by dsimp only; rw [hfr₂.len_eq, hfr₁.len_eq]; omega) (by disjoint) (by disjoint)
    refine hGrid.frame_seq_le rfl rfl (by room) (by fp_sub) ?_
    intro μ₃ hfr₃ ⟨hp₃, hState₃⟩
    have hH₃ := hH₂.of_eqOff hfr₃ (by disjoint)
    have hT₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hT₂
    have hTarget₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hTarget₂
    have hCenter₃ := hfr₃.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hCenter₂
    have hStateAll : CandidateHolds τ γ (2 ^ m) H
        (shifts ++ shqrCandidates B θ α γ m H shifts) z (r.1, r.2 + 3) μ₃.store := by
      rw [candidates_eq_streamedGrid B θ α γ H shifts hD]
      exact hState₃
    have hFinish := tryCandidate_writes (τp := tape) (m := μ₃)
      (a := w) (s := (r.1, r.2 + 4)) (t := c) (target := (r.1, r.2 + 1))
      (z := z) (f := (r.1, r.2 + 3)) hS hE hL hC hk hτ hH₃
      hCenter₃ hT₃ hTarget₃ hStateAll (by room)
      (by rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; exact hz)
      (by dsimp only; rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; omega)
      (by disjoint) (by disjoint)
    refine (hFinish.in_frame rfl rfl (by room)).mono (by fp_sub) ?_
    intro μ₄ _ ⟨hp₄, _, hSelected⟩
    exact ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), by
      simpa only [shqrAcceptStep, shqrAcceptShift] using hSelected⟩
  | some accepted =>
    obtain ⟨hFlag, hSelected⟩ := hState.result_of_some he
    refine writes_ite rfl rfl (hC.test_isZero (d := []) hFlag) ?_
    simp only [id_eq, one_ne_zero, decide_false, Bool.false_eq_true, if_false]
    have hAll : (shifts ++ shqrCandidates B θ α γ m H shifts).find?
        (fun s => decide (IsShiftAccept τ γ (2 ^ m) H s)) = some accepted := by
      simp only [List.find?_append, he, Option.or]
    exact (Writes.skip (I := I) (τ := tape) ⟨(rfl : μ.pos = μ.pos), by
      simpa only [shqrAcceptStep, shqrAcceptShift, hAll, Option.getD_some] using hSelected⟩).mono
      bot_le (fun _ _ h => h)

end NLAlib.ShiftedQR
