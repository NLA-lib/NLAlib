/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FindRitzRegisters

/-!
# Actual comparisons and natural updates of the Ritz search

The two computed squared norms choose a half using the standard comparison query. The first
half wins a tie. The index operations then write the natural halved length and doubled exponent.

## Main results

* `NLAlib.ShiftedQR.findRitzChoice_writes`: the actual comparison selects the intended start.
* `NLAlib.ShiftedQR.findRitzDecision_writes`: all three actual search words advance together.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has IndexOp Op] [Has CmpTst Tst]

/-- The actual comparison keeps the first half on a tie and otherwise moves its start.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem findRitzChoice_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hL : IsIndexLit M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {a h : ℕ} {r : ℕ × ℕ} {left right : ℝ}
    (ha : m.store.get r.1 r.2 = some (a : ℝ))
    (hl : m.store.get r.1 (r.2 + 3) = some left)
    (hr : m.store.get r.1 (r.2 + 4) = some right) :
    Writes .total I τ findRitzChoice.body (Env.frame [a, h] [r, r])
      (Store.inBlock r.1 r.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get r.1 r.2 =
        some ((if right ≤ left then a else a + h : ℕ) : ℝ)) m := by
  classical
  have ht := hCmp.test_le (d := []) (m := m) (x := (r.1, r.2 + 4))
    (y := (r.1, r.2 + 3)) hr hl
  by_cases hc : right ≤ left
  · simp only [id_eq, hc, decide_true] at ht
    refine writes_ite rfl rfl ht ?_
    exact (Writes.skip ⟨rfl, by simpa only [if_pos hc] using ha⟩).mono bot_le (fun _ _ h => h)
  · simp only [id_eq, hc, decide_false] at ht
    refine writes_ite rfl rfl ht ?_
    refine (writes_indexNat hL hE rfl rfl ?_).mono le_rfl ?_
    · exact Store.lt_len_of_get ha
    · intro m' _ hp
      exact ⟨hp.1, by simpa only [if_neg hc] using hp.2⟩

/-- The comparison and actual natural-literal operations advance the start, half length and
exponent exactly. [BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem findRitzDecision_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hL : IsIndexLit M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {a h e : ℕ} {r : ℕ × ℕ} {left right : ℝ}
    (hwords : SearchWords r a h e m.store)
    (hl : m.store.get r.1 (r.2 + 3) = some left)
    (hr : m.store.get r.1 (r.2 + 4) = some right)
    (hcap : r.2 + 3 ≤ m.store.len r.1) :
    Writes .total I τ findRitzDecision.body (Env.frame [a, h, e] [r, r])
      (Store.inBlock r.1 r.2 3)
      (fun m' => m'.pos = m.pos ∧
        SearchWords r (if right ≤ left then a else a + h) (h / 2) (2 * e) m'.store) m := by
  classical
  have hrl := Store.lt_length_of_get hwords.1
  have hlive : m.Live [r, r] := by simpa [Mem.Live] using hrl
  have hw := findRitzChoice_writes hL hE hCmp (τ := τ) (h := h) hwords.1 hl hr
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hlive) (by fp_sub) fun m' hfr ⟨hp, hstart⟩ => ?_
  refine Writes.seq_le (writes_indexNat hL hE rfl rfl (by
    change r.2 + 1 < m'.store.len r.1
    rw [hfr.len_eq]
    omega)) (by fp_sub) fun m'' hfr' ⟨hp', hhalf⟩ => ?_
  have hstart' := hfr'.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_inBlock_of_le (by omega)).symm hstart
  refine (writes_indexNat hL hE rfl rfl (by
    change r.2 + 2 < m''.store.len r.1
    rw [hfr'.len_eq, hfr.len_eq]
    omega)).mono (by fp_sub) ?_
  intro m''' hfr'' ⟨hp'', hexp⟩
  exact ⟨hp''.trans (hp'.trans hp),
    hfr''.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hstart',
    hfr''.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hhalf, hexp⟩

end NLAlib.ShiftedQR
