/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensLog
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.Functional

/-!
# Validating a slot of a Givens log with an exact literal one

`NLAlib.slottedLogValidate_writes` closes the pending slot of a slotted log under the standard
model. A program that assumes no rounding model (a termination theorem) knows instead that the
natural literal $1$ is exact (`NLAlib.IsExactNatLit` at $1$), which is all the valid word needs: it
must be positive.

## Main results

* `NLAlib.HoldsSlottedLog.readsOnly_region`: a stored log reads only its region.
* `NLAlib.HoldsSlottedLog.validate_of_eqOff`: a positive valid word closes the pending slot.
* `NLAlib.replicate_zero_flatMap_entryWords`: the words of the zero fill.
* `NLAlib.slottedLogValidate_writes_of_exactNat`: the validation with an exact literal one.
* `NLAlib.slottedLogWrite_pos`: writing an entry keeps the tape position.
-/

@[expose] public section

namespace NLAlib

open Ops

/-- The words of `w` padding entries $(0, 0, 0)$ are $5w$ zeros. -/
theorem replicate_zero_flatMap_entryWords (w : ℕ) :
    (List.replicate w ((0, 0, 0) : GivensEntry)).flatMap entryWords =
      List.replicate (5 * w) 0 := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, show 5 * (w + 1) = 5 + 5 * w by ring,
      List.replicate_add]
    simp [entryWords]

/-- A stored slotted log reads only the words of its region (so it is kept by writes elsewhere
and by allocations). -/
theorem HoldsSlottedLog.readsOnly_region (lg : ℕ × ℕ) (ns w : ℕ)
    (L : List (Option (List GivensEntry))) (P : List GivensEntry) :
    Store.ReadsOnly (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (HoldsSlottedLog lg ns w L P) := by
  intro s s' hg ⟨hLn, hPw, hc, hp, hf⟩
  have hend : ∀ j, j < ns → j * (1 + 5 * w) + 1 + 5 * w ≤ ns * (1 + 5 * w) := fun j hj => by
    have := Nat.mul_le_mul_right (1 + 5 * w) (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at this
    omega
  have hget (j : ℕ) (hj : j < ns) :
      s'.get lg.1 (lg.2 + j * (1 + 5 * w)) = s.get lg.1 (lg.2 + j * (1 + 5 * w)) := by
    have := hend j hj
    exact hg _ _ ⟨rfl, by omega, by omega⟩
  have hblk (j : ℕ) (hj : j < ns) :
      s'.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
        s.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) := by
    have := hend j hj
    exact Store.readBlock_congr fun t ht => hg _ _ ⟨rfl, by omega, by omega⟩
  refine ⟨hLn, hPw, fun j hj => ?_, fun h => ?_, fun j hj hjn => ?_⟩
  · obtain ⟨v, hv, hm⟩ := hc j hj
    refine ⟨v, by rw [hget j (by omega)]; exact hv, ?_⟩
    split at hm
    · exact hm
    · exact ⟨hm.1, hm.2.1, by rw [hblk j (by omega)]; exact hm.2.2⟩
  · rw [hget _ h, hblk _ h]; exact hp h
  · rw [hget _ hjn, hblk _ hjn]; exact hf j hj hjn

/-- A positive valid word closes the pending slot: if the store moves only at the valid word
of the pending slot $L.\mathrm{length} < n_s$ and that word becomes positive, the pending entries
`P` become the accepted slot `some P`. -/
theorem HoldsSlottedLog.validate_of_eqOff {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s s' : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) (hL : L.length < ns)
    (hfr : s.EqOff (Store.inBlock lg.1 (lg.2 + L.length * (1 + 5 * w)) 1) s') {v : ℝ}
    (hv : s'.get lg.1 (lg.2 + L.length * (1 + 5 * w)) = some v) (hv0 : 0 < v) :
    HoldsSlottedLog lg ns w (L ++ [some P]) [] s' := by
  obtain ⟨-, hPw, hslots, hpend, hrest⟩ := h
  set o := lg.2 + L.length * (1 + 5 * w) with ho
  -- the slots after the pending one start after its valid word
  have hafter : ∀ j, L.length < j → o + 1 ≤ lg.2 + j * (1 + 5 * w) := fun j hj => by
    have := Nat.mul_le_mul_right (1 + 5 * w) (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at this
    omega
  have kget : ∀ {i : ℕ} {x : ℝ}, (i < o ∨ o < i) → s.get lg.1 i = some x →
      s'.get lg.1 i = some x := fun hi hx => by
    rcases hi with hi | hi
    · exact hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le hi).symm hx
    · exact hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le hi) hx
  have kblock : ∀ {i k : ℕ} {xs : List ℝ}, (i + k ≤ o ∨ o < i) →
      s.readBlock lg.1 i k = some xs → s'.readBlock lg.1 i k = some xs := fun hi hx => by
    rcases hi with hi | hi
    · exact hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_le hi).symm hx
    · exact hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_le hi) hx
  refine ⟨by simp; omega, by simp, fun j hj => ?_, fun hlt => ?_, fun j hj hjn => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · obtain ⟨x, hx, hm⟩ := hslots j hj'
      have hend : lg.2 + j * (1 + 5 * w) + 1 + 5 * w ≤ o := by
        have := Nat.mul_le_mul_right (1 + 5 * w) (Nat.succ_le_of_lt hj')
        rw [Nat.succ_mul] at this
        omega
      refine ⟨x, kget (Or.inl (by omega)) hx, ?_⟩
      rw [List.getElem_append_left hj']
      revert hm
      cases L[j] with
      | none => exact id
      | some es => exact fun ⟨h0, hes, hb⟩ => ⟨h0, hes, kblock (Or.inl hend) hb⟩
    · refine ⟨v, hv, ?_⟩
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
      exact ⟨hv0, hPw, kblock (Or.inr (by omega)) (hpend hL).2⟩
  · simp only [List.length_append, List.length_singleton] at hlt ⊢
    obtain ⟨h0, hb⟩ := hrest (L.length + 1) (by omega) hlt
    have ha := hafter (L.length + 1) (by omega)
    refine ⟨kget (Or.inr (by omega)) h0, ?_⟩
    rw [padEntries, List.nil_append, List.length_nil, Nat.sub_zero,
      replicate_zero_flatMap_entryWords]
    exact kblock (Or.inr (by omega)) hb
  · simp only [List.length_append, List.length_singleton] at hj
    obtain ⟨h0, hb⟩ := hrest j (by omega) hjn
    have ha := hafter j (by omega)
    exact ⟨kget (Or.inr (by omega)) h0, kblock (Or.inr (by omega)) hb⟩

variable {O Q : Type} [Has IndexOp O]

/-- Validating the pending slot with an exact literal one (`NLAlib.slottedLogValidate_writes`
without a rounding model): if the natural literal $1$ is exact, `NLAlib.slottedLogValidate` closes
the pending slot as accepted, writes only the log and keeps the tape position. -/
theorem slottedLogValidate_writes_of_exactNat {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch 1) {ns w : ℕ} {lg : ℕ × ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {τ : Tape ℝ} {μ : Mem ℝ}
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL' : L.length < ns) :
    Writes .total I τ (slottedLogValidate (O := O) (Q := Q)).body
      (Env.frame [w, L.length] [lg]) (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsSlottedLog lg ns w (L ++ [some P]) [] μ'.store) μ := by
  have h1 : Mch.lit ((1 : ℕ) : ℚ) = (1 : ℝ) := by simpa using hNat 1 le_rfl
  have hz := Store.lt_len_of_get (h.2.2.2.1 hL').1
  have hle : lg.2 + L.length * (1 + 5 * w) + 1 ≤ lg.2 + ns * (1 + 5 * w) := by
    have := Nat.mul_le_mul_right (1 + 5 * w) (Nat.succ_le_of_lt hL')
    rw [Nat.succ_mul] at this
    omega
  unfold slottedLogValidate
  refine (writes_indexLit (n := 1) (z := (lg.1, lg.2 + L.length * (1 + 5 * w))) hL rfl rfl
    hz).mono (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro μ' hfr ⟨hp, hg⟩
  exact ⟨hp, h.validate_of_eqOff hL' hfr (by rw [hg, h1]) one_pos⟩


section Write

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O]

/-- `NLAlib.slottedLogWrite` keeps the tape position and writes only the five words of its
entry: from a stored log with room in the pending slot and the two pairs at `pw`, `qw` outside
the log, on any machine with index literals. -/
theorem slottedLogWrite_pos {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) {ns w r : ℕ} {lg pw qw : ℕ × ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {p q : ℂ} {τ : Tape ℝ}
    {μ : Mem ℝ} (h : HoldsSlottedLog lg ns w L P μ.store) (hLn : L.length < ns)
    (hP : P.length < w) (hp : μ.store.readBlock pw.1 pw.2 2 = some [p.re, p.im])
    (hq : μ.store.readBlock qw.1 qw.2 2 = some [q.re, q.im])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock pw.1 pw.2 2 ⊔ Store.inBlock qw.1 qw.2 2)) :
    Writes .total I τ (slottedLogWrite (O := O) (Q := Q)).body
      (Env.frame [w, L.length, P.length, r] [pw, qw, lg])
      (Store.inBlock lg.1 (lg.2 + L.length * (1 + 5 * w) + 1 + 5 * P.length) 5)
      (fun μ' => μ'.pos = μ.pos) μ := by
  set o := lg.2 + L.length * (1 + 5 * w) with ho
  have hblk := (h.2.2.2.1 hLn).2
  have hroom : ∀ k, 1 ≤ k → k ≤ 5 → o + k + 5 * P.length < μ.store.len lg.1 := fun k hk hk' => by
    have := Store.lt_len_of_get (Store.get_of_readBlock hblk (j := 5 * P.length + (k - 1))
      (by omega) 0)
    omega
  have hend : L.length * (1 + 5 * w) + 1 + 5 * w ≤ ns * (1 + 5 * w) := by
    have := Nat.mul_le_mul_right (1 + 5 * w) (Nat.succ_le_of_lt hLn)
    rw [Nat.succ_mul] at this
    omega
  have hsub : ∀ k, 1 ≤ k → k ≤ 5 → Store.inBlock lg.1 (o + k + 5 * P.length) 1 ≤
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) :=
    fun k hk hk' => Fp.inBlock_le_inBlock (by omega) (by omega)
  have hloc : ∀ k, 1 ≤ k → k ≤ 5 → Store.inBlock lg.1 (o + k + 5 * P.length) 1 ≤
      Store.inBlock lg.1 (o + 1 + 5 * P.length) 5 :=
    fun k hk hk' => Fp.inBlock_le_inBlock (by omega) (by omega)
  have hpw := hd.mono le_rfl le_sup_left
  have hqw := hd.mono le_rfl le_sup_right
  -- the four input words, kept by writes in the log
  have K : ∀ {s s' : Store ℝ} {k : ℕ} {b i : ℕ} {v : ℝ}, 1 ≤ k → k ≤ 5 →
      Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) (Store.inBlock b i 1) →
      s.EqOff (Store.inBlock lg.1 (o + k + 5 * P.length) 1) s' → s.get b i = some v →
      s'.get b i = some v :=
    fun hk hk' hdj hf hv =>
      hf.keep (Store.readsOnly_get _ _ _) (hdj.mono (hsub _ hk hk') le_rfl) hv
  have gp0 := Store.get_of_readBlock hp (j := 0) (by norm_num) (0 : ℝ)
  have gp1 := Store.get_of_readBlock hp (j := 1) (by norm_num) (0 : ℝ)
  have gq0 := Store.get_of_readBlock hq (j := 0) (by norm_num) (0 : ℝ)
  have gq1 := Store.get_of_readBlock hq (j := 1) (by norm_num) (0 : ℝ)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at gp0 gp1 gq0 gq1
  have dp0 : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) (Store.inBlock pw.1 pw.2 1) :=
    hpw.mono le_rfl (Fp.inBlock_le_inBlock le_rfl (by omega))
  have dp1 : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock pw.1 (pw.2 + 1) 1) :=
    hpw.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))
  have dq0 : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) (Store.inBlock qw.1 qw.2 1) :=
    hqw.mono le_rfl (Fp.inBlock_le_inBlock le_rfl (by omega))
  have dq1 : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock qw.1 (qw.2 + 1) 1) :=
    hqw.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))
  unfold slottedLogWrite
  refine (writes_indexLit (n := r) (z := (lg.1, o + 1 + 5 * P.length)) hL rfl rfl
    (hroom 1 le_rfl (by omega))).seq_le (hloc 1 le_rfl (by omega)) ?_
  rintro μ₁ hf₁ ⟨hp₁, -⟩
  refine (writes_call_un (hS .copy) (x := pw) (z := (lg.1, o + 2 + 5 * P.length)) rfl rfl trivial
    (K (k := 1) le_rfl (by omega) dp0 hf₁ gp0) rfl
    (by rw [hf₁.len_eq]; exact hroom 2 (by omega) (by omega))).seq_le
    (hloc 2 (by omega) (by omega)) ?_
  rintro μ₂ hf₂ ⟨hp₂, -⟩
  refine (writes_call_un (hS .copy) (x := (pw.1, pw.2 + 1)) (z := (lg.1, o + 3 + 5 * P.length))
    rfl rfl trivial
    (K (k := 2) (by omega) (by omega) dp1 hf₂ (K (k := 1) le_rfl (by omega) dp1 hf₁ gp1)) rfl
    (by rw [hf₂.len_eq, hf₁.len_eq]; exact hroom 3 (by omega) (by omega))).seq_le
    (hloc 3 (by omega) (by omega)) ?_
  rintro μ₃ hf₃ ⟨hp₃, -⟩
  refine (writes_call_un (hS .copy) (x := qw) (z := (lg.1, o + 4 + 5 * P.length)) rfl rfl trivial
    (K (k := 3) (by omega) (by omega) dq0 hf₃ (K (k := 2) (by omega) (by omega) dq0 hf₂
      (K (k := 1) le_rfl (by omega) dq0 hf₁ gq0))) rfl
    (by rw [hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; exact hroom 4 (by omega) (by omega))).seq_le
    (hloc 4 (by omega) (by omega)) ?_
  rintro μ₄ hf₄ ⟨hp₄, -⟩
  refine (writes_call_un (hS .copy) (x := (qw.1, qw.2 + 1)) (z := (lg.1, o + 5 + 5 * P.length))
    rfl rfl trivial
    (K (k := 4) (by omega) (by omega) dq1 hf₄ (K (k := 3) (by omega) (by omega) dq1 hf₃
      (K (k := 2) (by omega) (by omega) dq1 hf₂ (K (k := 1) le_rfl (by omega) dq1 hf₁ gq1)))) rfl
    (by rw [hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; exact hroom 5 (by omega) le_rfl)).mono
    (hloc 5 (by omega) le_rfl) ?_
  rintro μ₅ - ⟨hp₅, -⟩
  rw [hp₅, hp₄, hp₃, hp₂, hp₁]

end Write

end NLAlib
