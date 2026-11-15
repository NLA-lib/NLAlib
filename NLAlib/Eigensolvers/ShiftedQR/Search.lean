/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.SearchState
public import NLAlib.Ops.Logic.Loop

/-!
# Ordered scalar search for an accepted shift

The actual stored acceptance flag controls whether a candidate is tried. Once a candidate
passes, later candidates retain its matrix. Before one passes, output matrix capacity may be
uninitialized. This is the common transition used by Ritz and exceptional-grid searches.

## Main results

* `NLAlib.ShiftedQR.tryCandidate`: a trial guarded by the actual acceptance flag.
* `NLAlib.ShiftedQR.tryCandidate_writes`: one ordered mathematical search transition.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Try the stored candidate only while the actual flag is zero; an accepted matrix and flag
are retained by the skip branch. Flag's input and output views alias exactly. -/
def tryCandidate : Impl Op Tst := opsImpl% [n, k] (A, S, Threshold, Target, Flag) → (Z, Flag) {
  if (Has.inj CmpTst.isZero) [] (Flag) {
    run trial.body [n, k] (A, S, Threshold, Target, Z, Flag)
  } else { skip }
}

open Classical in
/-- The stored first-accepted-candidate invariant extends by one candidate. Rejected prefixes
execute the scalar trial; accepted prefixes execute the actual skip branch. -/
theorem tryCandidate_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τp : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a s t target z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} {τ γ : ℝ} {ss : List ℂ}
    (hk : k ≤ n) (hτ : 0 ≤ τ) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (ht : m.store.get t.1 t.2 = some (τ ^ 2))
    (hTarget : m.store.get target.1 target.2 = some ((1 - γ) ^ (2 * k) * subdiagNormSqProd k H))
    (hstate : CandidateHolds τ γ k H ss z f m.store)
    (hl : m.Live [a, s, t, target, z, f])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hf : f.2 < m.store.len f.1)
    (hzf : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock f.1 f.2 1))
    (hsep : Fp.Disj
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 2 ⊔ Store.inBlock t.1 t.2 1 ⊔
        Store.inBlock target.1 target.2 1)) :
    Writes .total I τp tryCandidate.body (Env.frame [n + 1, k] [a, s, t, target, f, z, f])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ CandidateHolds τ γ k H (ss ++ [shift]) z f m'.store ∧
        HoldsMatrix z (multiShiftedQRStep H (List.replicate k
          ((ss.find? fun s => decide (IsShiftAccept τ γ k H s)).getD shift))) m'.store) m := by
  classical
  unfold tryCandidate
  cases he : ss.find? (fun s => decide (IsShiftAccept τ γ k H s)) with
  | none =>
    have hflag := hstate.flag_of_none he
    have htest := hC.test_isZero (d := []) hflag
    refine writes_ite rfl rfl htest ?_
    simp only [id_eq, decide_true, if_true]
    have ht := trial_writes (τp := τp) hS hE hL hC hk hτ hH hs ht hTarget hl hz hf hzf hsep
    refine (ht.in_frame rfl rfl hl).mono le_rfl ?_
    intro m' _ ⟨hp, hZ, hFlag⟩
    exact ⟨hp, CandidateHolds.of_trial he hZ hFlag,
      by simpa only [he, Option.getD_none] using hZ⟩
  | some accepted =>
    have hflag := (hstate.result_of_some he).1
    have htest := hC.test_isZero (d := []) hflag
    refine writes_ite rfl rfl htest ?_
    simp only [id_eq, one_ne_zero, decide_false, Bool.false_eq_true, if_false]
    exact (Writes.skip (I := I) (τ := τp)
      ⟨(rfl : m.pos = m.pos), hstate.append_of_some he [shift],
        by simpa only [he, Option.getD_some] using (hstate.result_of_some he).2⟩).mono
      bot_le (fun _ _ h => h)

/-- Visit a physically stored list of candidate shifts. Two caller-owned words hold the
current shift, and the acceptance flag may already represent an accepted earlier prefix. -/
def searchStoredWithScratch : Impl Op Tst := opsImpl% [n, k, len]
    (A, SS, Threshold, Target, S, Flag) → (Z, Flag) {
  for i < len {
    run (unaryMap (Has.inj ScalarOp.copy)).body [2] (SS[2 * i], S);
    run tryCandidate.body [n, k] (A, S, Threshold, Target, Flag, Z, Flag)
  }
}

/-- A stored finite candidate list extends the exact ordered search state. The source matrix,
all candidate words and scalar test inputs are retained. Every trial uses actual scalar QR.
An already accepted earlier prefix is supported without recomputing its matrix. -/
theorem searchStoredWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τp : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a ss t target s z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ γ : ℝ} {before candidates : List ℂ}
    (hk : k ≤ n) (hτ : 0 ≤ τ) (hH : HoldsMatrix a H m.store)
    (hSS : HoldsMatrix ss (shiftColumn candidates) m.store)
    (ht : m.store.get t.1 t.2 = some (τ ^ 2))
    (hTarget : m.store.get target.1 target.2 = some ((1 - γ) ^ (2 * k) * subdiagNormSqProd k H))
    (hstate : CandidateHolds τ γ k H before z f m.store)
    (hl : m.Live [a, ss, t, target, s, z, f])
    (hs : s.2 + 2 ≤ m.store.len s.1)
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hf : f.2 < m.store.len f.1)
    (hapart : Fp.Apart [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
    (hsep : Fp.Disj (Fp.blocks [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
      (Fp.blocks [a, ss, t, target] [2 * ((n + 1) * (n + 1)), 2 * candidates.length, 1, 1])) :
    Writes .total I τp searchStoredWithScratch.body
      (Env.frame [n + 1, k, candidates.length] [a, ss, t, target, s, f, z, f])
      (Fp.blocks [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1])
      (fun m' => m'.pos = m.pos ∧
        CandidateHolds τ γ k H (before ++ candidates) z f m'.store) m := by
  classical
  let F := Fp.blocks [s, z, f] [2, 2 * ((n + 1) * (n + 1)), 1]
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
  unfold searchStoredWithScratch
  suffices hloop : Writes .total I τp (.loop _ _) _ F
      (fun m' => m'.pos = m.pos ∧
        CandidateHolds τ γ k H (before ++ candidates.take candidates.length) z f m'.store) m by
    simpa only [List.take_length] using hloop
  refine writes_loop rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧
      CandidateHolds τ γ k H (before ++ candidates.take i) z f m'.store)
    (by simpa using And.intro (rfl : m.pos = m.pos) hstate) ?_
  intro i hi m' hfr ⟨hpos, hState⟩
  have hH' := hH.of_eqOff hfr (hsep.mono le_rfl (by fp_sub))
  have hSS' := hSS.of_eqOff hfr (hsep.mono le_rfl (by fp_sub))
  have ht' := hfr.keep (Store.readsOnly_get _ _ _) (hsep.mono le_rfl (by fp_sub)) ht
  have hTarget' := hfr.keep (Store.readsOnly_get _ _ _) (hsep.mono le_rfl (by fp_sub)) hTarget
  have hPair : m'.store.readBlock ss.1 (ss.2 + 2 * i) 2 =
      some [(candidates[i]).re, (candidates[i]).im] := by
    simpa only [shiftColumn, Fin.val_zero, Nat.zero_mul, Nat.zero_add, Fin.getElem_fin] using
      hSS'.read_entry ⟨i, hi⟩ 0
  have hsource : Store.inBlock ss.1 (ss.2 + 2 * i) 2 ≤
      Store.inBlock ss.1 ss.2 (2 * candidates.length) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hcopy := writes_unaryMap_of_disj_or_eq (md := .total) (τ := τp) (m := m') (f := id)
    (x := (ss.1, ss.2 + 2 * i)) (y := s) (n := 2) (hS .copy)
    (Or.inl (hsep.symm.mono (hsource.trans (by fp_sub)) (by fp_sub)))
    hPair (by rw [hfr.len_eq]; exact hs)
  refine hcopy.frame_seq_le rfl rfl
    (by simpa [Mem.Live, hfr.length_eq] using
      And.intro (hl ss (by simp)) (hl s (by simp))) (by fp_sub) ?_
  intro m'' hcopyfr ⟨hcopypos, hShift⟩
  have hH'' := hH'.of_eqOff hcopyfr (hsep.mono (by fp_sub) (by fp_sub))
  have ht'' := hcopyfr.keep (Store.readsOnly_get _ _ _)
    (hsep.mono (by fp_sub) (by fp_sub)) ht'
  have hTarget'' := hcopyfr.keep (Store.readsOnly_get _ _ _)
    (hsep.mono (by fp_sub) (by fp_sub)) hTarget'
  have hState' := hState.of_eqOff hcopyfr hszf
  have hltrial : m.Live [a, s, t, target, z, f] := hl.mono (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have hTry := tryCandidate_writes (τp := τp) (m := m'') hS hE hL hC hk hτ hH''
    (by simpa only [List.map_id] using hShift) ht'' hTarget'' hState'
    (hltrial.congr (hcopyfr.length_eq.trans hfr.length_eq))
    (by rw [hcopyfr.len_eq, hfr.len_eq]; exact hz)
    (by rw [hcopyfr.len_eq, hfr.len_eq]; exact hf) hzf htrialsep
  refine (hTry.in_frame rfl rfl ?_).mono (by fp_sub) ?_
  · have hlTry : m''.Live [a, s, t, target, f, z, f] :=
      (hltrial.congr (hcopyfr.length_eq.trans hfr.length_eq)).mono (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    exact hlTry
  · intro m''' _ ⟨hp', hState'', _⟩
    refine ⟨hp'.trans (hcopypos.trans hpos), ?_⟩
    rw [List.take_succ_eq_append_getElem hi, ← List.append_assoc]
    exact hState''

end NLAlib.ShiftedQR
