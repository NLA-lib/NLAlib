/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FindRitzNorms
public import NLAlib.Eigensolvers.ShiftedQR.FindRitzDecision

/-!
# One verified scalar Ritz-search level

The actual program reads its three natural state words through bounded index queries. Two
scalar half-norm computations and the actual norm comparison then select the next window.
The source matrix, shift list and exact mathematical search result are retained.

## Main results

* `NLAlib.ShiftedQR.findRitzWindow_writes`: the actual known-window numerical computation.
* `NLAlib.ShiftedQR.findRitzLevel_writes`: the actual bounded index reads and window transition.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Both actual norms and the actual comparison advance the stored window exactly.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem findRitzWindow_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e : ℕ} {b ss r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hwords : SearchWords r a h e m.store)
    (hdet : ∀ shift ∈ shifts, (H - shift • 1).det ≠ 0)
    (hak : a + 2 * h ≤ k) (hal : a + 2 * h ≤ shifts.length)
    (hra : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : m.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ m.store.len r.1) :
    Writes .total I τ findRitzWindow.body (Env.frame [n + 1, k, a, h, e] [b, ss, r, r])
      (Store.inBlock r.1 r.2 6)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
        HoldsShifts (k := k) ss shifts m'.store ∧
        SearchWords r (searchNext H shifts a h e) (h / 2) (2 * e) m'.store) m := by
  classical
  have hw := findRitzNorms_writes hS hE hCmp (τ := τ) hH hB hSS hwords hdet hak hal hra hrs hl hr
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hl) le_rfl
    fun m' hfr ⟨hp, hB', hSS', hwords', hleft, hright⟩ => ?_
  have hn := findRitzDecision_writes hL hE hCmp (τ := τ) hwords' hleft hright
    (by rw [hfr.len_eq]; omega)
  have hrl := Store.lt_length_of_get hwords'.1
  have hl' : m'.Live [r, r] := by simpa [Mem.Live] using hrl
  refine (hn.in_frame rfl rfl hl').mono (by fp_sub) ?_
  intro m'' hfr' ⟨hp', hnew⟩
  refine ⟨hp'.trans hp, hB'.of_eqOff hfr' (Fp.disj_inBlock_of_ne hra),
    hfr'.keep (readsOnly_holdsVector ss (fun i : Fin k => shifts.getD i 0))
      (Fp.disj_inBlock_of_ne hrs) hSS', ?_⟩
  simpa only [searchNext] using hnew

variable [Has IdxTst Tst]

/-- Bounded toNat queries read the actual stored start, half length and exponent before the
same numerical window transition. Every query's runtime bound is proved explicitly.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem findRitzLevel_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I)
    (hCmp : IsCmp id I) (hToNat : IsToNat id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e : ℕ} {b ss r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hwords : SearchWords r a h e m.store)
    (hdet : ∀ shift ∈ shifts, (H - shift • 1).det ≠ 0)
    (hak : a + 2 * h ≤ k) (hal : a + 2 * h ≤ shifts.length)
    (ha : a ≤ k) (hh : h ≤ k) (he : e ≤ k)
    (hra : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : m.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ m.store.len r.1) :
    Writes .total I τ findRitzLevel.body (Env.frame [n + 1, k] [b, ss, r, r])
      (Store.inBlock r.1 r.2 6)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
        HoldsShifts (k := k) ss shifts m'.store ∧
        SearchWords r (searchNext H shifts a h e) (h / 2) (2 * e) m'.store) m := by
  change Writes .total I τ (.bindIdx _ _ _ _) _ _ _ m
  refine writes_bindIdx_of_decode_nat hToNat rfl rfl hwords.1 rfl ha ?_
  refine writes_bindIdx_of_decode_nat hToNat rfl rfl hwords.2.1 rfl hh ?_
  refine writes_bindIdx_of_decode_nat hToNat rfl rfl hwords.2.2 rfl he ?_
  exact (findRitzWindow_writes hS hE hL hCmp (τ := τ)
    hH hB hSS hwords hdet hak hal hra hrs hl hr).in_frame
      (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
      (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) hl

end NLAlib.ShiftedQR
