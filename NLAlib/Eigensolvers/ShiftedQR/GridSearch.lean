/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Search
public import NLAlib.Eigensolvers.ShiftedQR.Grid

/-!
# Streaming exceptional-grid search

Each grid point is computed by scalar arithmetic into the same two-word shift view. The
actual acceptance flag then controls its trial. The output matrix retains the first accepted
candidate; the grid itself is never materialized as an auxiliary word array.

## Main results

* `NLAlib.ShiftedQR.gridCandidate`: compute one actual point and consider its trial.
* `NLAlib.ShiftedQR.gridCandidate_writes`: exact ordered search transition for that point.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Compute one grid point in the reusable shift view and consider it while no prior candidate
has been accepted. Coordinates use actual counted literals and scalar divisions. -/
def gridCandidate : Impl Op Tst := opsImpl% [n, k, D, i, j]
    (A, Center, Radius, Threshold, Target, Flag) → (S, Z, Flag) {
  run gridPoint.body [D, i, j] (Center, Radius, S);
  run tryCandidate.body [n, k] (A, S, Threshold, Target, Flag, Z, Flag)
}

/-- One streaming point extends the actual first-accepted search state. Positive grid
resolution justifies its scalar divisions; no acceptance or execution hypothesis is assumed. -/
theorem gridCandidate_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τp : Tape ℝ} {m : Mem ℝ} {n k D i j : ℕ} {a c r t target s z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ γ radius : ℝ} {center : ℂ}
    {before : List ℂ} (hk : k ≤ n) (hτ : 0 ≤ τ) (hD : 1 ≤ D)
    (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [center.re, center.im])
    (hr : m.store.get r.1 r.2 = some radius) (ht : m.store.get t.1 t.2 = some (τ ^ 2))
    (hTarget : m.store.get target.1 target.2 = some ((1 - γ) ^ (2 * k) * subdiagNormSqProd k H))
    (hstate : CandidateHolds τ γ k H before z f m.store)
    (hl : m.Live [a, c, r, t, target, s, z, f])
    (hs : s.2 + 2 ≤ m.store.len s.1)
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hf : f.2 < m.store.len f.1)
    (hapart : Fp.Apart [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
    (hsep : Fp.Disj (Fp.blocks [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
      (Fp.blocks [a, c, r, t, target] [2 * ((n + 1) * (n + 1)), 2, 1, 1, 1])) :
    Writes .total I τp gridCandidate.body
      (Env.frame [n + 1, k, D, i, j] [a, c, r, t, target, f, s, z, f])
      (Fp.blocks [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
      (fun m' => m'.pos = m.pos ∧
        CandidateHolds τ γ k H (before ++ [gridPointValue center radius D i j]) z f m'.store)
      m := by
  have hszf : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1) := by
    simpa only [Fp.blocks, sup_bot_eq] using hapart.1
  have hzf : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock f.1 f.2 1) := by
    simpa only [Fp.blocks, sup_bot_eq] using hapart.2.1
  have htrialsep : Fp.Disj
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 2 ⊔ Store.inBlock t.1 t.2 1 ⊔
        Store.inBlock target.1 target.2 1) := by
    exact (hapart.disj_tail_head hsep le_rfl
      (G := Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock f.1 f.2 1) (by fp_sub)).mono le_rfl (by fp_sub)
  have hpoint := gridPoint_writes (τ := τp) (m := m) (i := i) (j := j)
    (c := c) (r := r) (s := s) (center := center) (radius := radius) hS hE hL hD
    (hsep.symm.mono (by fp_sub) (by fp_sub))
    (by simpa using Store.get_of_readBlock hc (j := 0) (by simp) (0 : ℝ))
    (by simpa using Store.get_of_readBlock hc (j := 1) (by simp) (0 : ℝ)) hr hs
  unfold gridCandidate
  refine hpoint.frame_seq_le rfl rfl
    (hl.mono (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp)) (by fp_sub) ?_
  intro m₁ hfr ⟨hp, hShift⟩
  have hH₁ := hH.of_eqOff hfr (hsep.mono (by fp_sub) (by fp_sub))
  have ht₁ := hfr.keep (Store.readsOnly_get _ _ _) (hsep.mono (by fp_sub) (by fp_sub)) ht
  have hTarget₁ := hfr.keep (Store.readsOnly_get _ _ _)
    (hsep.mono (by fp_sub) (by fp_sub)) hTarget
  have hState₁ := hstate.of_eqOff hfr hszf
  have hltrial : m₁.Live [a, s, t, target, z, f] := (hl.congr hfr.length_eq).mono (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have htrial := tryCandidate_writes (τp := τp) (m := m₁) hS hE hL hC hk hτ hH₁ hShift
    ht₁ hTarget₁ hState₁ hltrial (by rw [hfr.len_eq]; exact hz)
    (by rw [hfr.len_eq]; exact hf) hzf htrialsep
  refine (htrial.in_frame rfl rfl (hltrial.mono (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))).mono (by fp_sub) ?_
  intro m₂ _ ⟨hp', hState₂, _⟩
  exact ⟨hp'.trans hp, hState₂⟩

/-- Grid points in complete earlier rows and in the visited prefix of the current row. -/
noncomputable def gridVisited (center : ℂ) (radius : ℝ) (D i j : ℕ) : List ℂ :=
  ((List.range i).flatMap fun a =>
    (List.range (D + 1)).map fun b => gridPointValue center radius D a b) ++
      (List.range j).map fun b => gridPointValue center radius D i b

/-- One inner-loop visit appends its exact mathematical grid point. -/
theorem gridVisited_succ (center : ℂ) (radius : ℝ) (D i j : ℕ) :
    gridVisited center radius D i (j + 1) =
      gridVisited center radius D i j ++ [gridPointValue center radius D i j] := by
  simp only [gridVisited, List.range_succ, List.map_append, List.map_singleton,
    List.append_assoc]

/-- Finishing one complete row advances to the empty prefix of the next row. -/
theorem gridVisited_next_row (center : ℂ) (radius : ℝ) (D i : ℕ) :
    gridVisited center radius D i (D + 1) = gridVisited center radius D (i + 1) 0 := by
  simp only [gridVisited, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.range_zero, List.map_nil, List.append_nil]

/-- All complete rows are exactly the standard lexicographic grid enumeration. -/
theorem gridVisited_all (center : ℂ) (radius : ℝ) (D : ℕ) :
    gridVisited center radius D (D + 1) 0 = gridPoints center radius D := by
  simp only [gridVisited, gridPoints, List.range_zero, List.map_nil, List.append_nil]

/-- Stream the complete grid in nested-loop order using only one reusable shift pair. The
accepted result is retained by each subsequent candidate's actual flag guard. -/
def searchGridWithScratch : Impl Op Tst := opsImpl% [n, k, D]
    (A, Center, Radius, Threshold, Target, Flag) → (S, Z, Flag) {
  for i < D + 1 { for j < D + 1 {
    run gridCandidate.body [n, k, D, i, j]
      (A, Center, Radius, Threshold, Target, Flag, S, Z, Flag)
  } }
}

/-- The actual two-loop grid search extends any earlier search prefix by exactly the standard
grid order. Its persistent storage is independent of the number of grid candidates. -/
theorem searchGridWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τp : Tape ℝ} {m : Mem ℝ} {n k D : ℕ} {a c r t target s z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ γ radius : ℝ} {center : ℂ}
    {before : List ℂ} (hk : k ≤ n) (hτ : 0 ≤ τ) (hD : 1 ≤ D)
    (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [center.re, center.im])
    (hr : m.store.get r.1 r.2 = some radius) (ht : m.store.get t.1 t.2 = some (τ ^ 2))
    (hTarget : m.store.get target.1 target.2 = some ((1 - γ) ^ (2 * k) * subdiagNormSqProd k H))
    (hstate : CandidateHolds τ γ k H before z f m.store)
    (hl : m.Live [a, c, r, t, target, s, z, f])
    (hs : s.2 + 2 ≤ m.store.len s.1)
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hf : f.2 < m.store.len f.1)
    (hapart : Fp.Apart [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
    (hsep : Fp.Disj (Fp.blocks [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
      (Fp.blocks [a, c, r, t, target] [2 * ((n + 1) * (n + 1)), 2, 1, 1, 1])) :
    Writes .total I τp searchGridWithScratch.body
      (Env.frame [n + 1, k, D] [a, c, r, t, target, f, s, z, f])
      (Fp.blocks [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
      (fun m' => m'.pos = m.pos ∧
        CandidateHolds τ γ k H (before ++ gridPoints center radius D) z f m'.store) m := by
  let F := Fp.blocks [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1]
  have hLive : m.Live [a, c, r, t, target, f, s, z, f] := hl.mono (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  unfold searchGridWithScratch
  refine (writes_loop₂ (M := D + 1) (N := D + 1) rfl (fun _ => rfl)
    (fun _ _ => F) (fun _ _ _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun i j m' => m'.pos = m.pos ∧
      CandidateHolds τ γ k H (before ++ gridVisited center radius D i j) z f m'.store)
    ?_ ?_ ?_).mono le_rfl ?_
  · simpa only [gridVisited, List.range_zero, List.flatMap_nil, List.map_nil,
      List.nil_append, List.append_nil] using And.intro (rfl : m.pos = m.pos) hstate
  · intro i _ m' hp
    simpa only [gridVisited_next_row] using hp
  · intro i _ j _ m' hfr ⟨hp, hState⟩
    have hH' := hH.of_eqOff hfr (hsep.mono le_rfl (by fp_sub))
    have hc' := hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      (hsep.mono le_rfl (by fp_sub)) hc
    have hr' := hfr.keep (Store.readsOnly_get _ _ _)
      (hsep.mono le_rfl (by fp_sub)) hr
    have ht' := hfr.keep (Store.readsOnly_get _ _ _)
      (hsep.mono le_rfl (by fp_sub)) ht
    have hTarget' := hfr.keep (Store.readsOnly_get _ _ _)
      (hsep.mono le_rfl (by fp_sub)) hTarget
    have hRound := gridCandidate_writes (τp := τp) (m := m') (i := i) (j := j)
      hS hE hL hC hk hτ hD hH' hc' hr' ht' hTarget' hState (hl.congr hfr.length_eq)
      (by rw [hfr.len_eq]; exact hs) (by rw [hfr.len_eq]; exact hz)
      (by rw [hfr.len_eq]; exact hf) hapart hsep
    refine (hRound.in_frame rfl rfl (hLive.congr hfr.length_eq)).mono le_rfl ?_
    intro m'' _ ⟨hp', hState'⟩
    refine ⟨hp'.trans hp, ?_⟩
    rw [gridVisited_succ, ← List.append_assoc]
    exact hState'
  · intro m' _ hp
    simpa only [gridVisited_all] using hp

end NLAlib.ShiftedQR
