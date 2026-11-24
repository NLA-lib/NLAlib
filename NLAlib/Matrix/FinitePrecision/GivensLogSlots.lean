/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensLog
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.ProbabilisticFamily

/-!
# Closing and reading back the slots of a Givens log

A program that runs a fixed number of trials, each in its own slot of a slotted log
(`NLAlib.HoldsSlottedLog`), closes exactly that many slots, whatever happens: a trial that is not
accepted leaves its slot's valid word zero, and the slot is rejected
(`NLAlib.HoldsSlottedLog.reject`) without a write. This file collects the bookkeeping of closed
slots: the entries of appended and rejected slots, rejecting many slots at once, the log seen from a
later slot, and the read-back of the slots after a prefix (`NLAlib.slottedLogRead`), which names the
unitary of a run by a measurable function of the memory.

## Main results

* `NLAlib.HoldsSlottedLog.validate_of_eqOff`: a positive valid word closes the pending slot.
* `NLAlib.slottedLogValidate_writes_of_exactNat`: the validation with an exact literal one.
* `NLAlib.slottedLogWrite_pos`: writing an entry keeps the tape position.
* `NLAlib.slotEntries_replicate_none`: rejected slots have no entries.
* `NLAlib.eq_replicate_none_of_slotEntries_eq_nil`: closed slots without entries are rejected.
* `NLAlib.HoldsSlottedLog.rejects`: reject `c` empty slots.
* `NLAlib.HoldsSlottedLog.drop`: the log after a prefix of its slots.
* `NLAlib.slottedLogRead_drop`: the read-back after a prefix is a read-back.
* `NLAlib.HoldsSlottedLog.slotEntries_read_drop`: the valid entries after a prefix are read back.
* `NLAlib.measurable_givensLog_slottedLogRead_drop`: their unitary is measurable.
* `NLAlib.exists_readBlock_padEntries_iff`: an accepted block, cell by cell.
* `NLAlib.measurableSet_exists_holdsSlottedLog_append`: the stores holding `c` closed slots after
  a prefix form a measurable event.
-/

@[expose] public section

namespace NLAlib

open Ops

/-! ### Validating with an exact literal one -/

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

section Validate

variable {O Q : Type} [Has IndexOp O]

/-- Validating the pending slot with an exact literal one (`NLAlib.slottedLogValidate_writes`
without a rounding model): if the natural literal $1$ is exact, `NLAlib.slottedLogValidate` closes
the pending slot as accepted, writes only the log and keeps the tape position.
Shared by the trees of `NLAlib.hessenbergReduceLast`, `NLAlib.ShiftedQR.trialAccept`,
`NLAlib.SmallEig.decoupleLast` and 1 more. -/
theorem slottedLogValidate_writes_of_exactNat {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch 1) {ns w : ℕ} {lg : ℕ × ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {τ : Tape ℝ} {μ : Mem ℝ}
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL' : L.length < ns) :
    Writes .total I τ (slottedLogValidate (O := O) (Q := Q))
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


end Validate

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
    Writes .total I τ (slottedLogWrite (O := O) (Q := Q))
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

/-! ### Closed slots -/

/-- Rejected slots have no entries. -/
@[simp] theorem slotEntries_replicate_none (w c : ℕ) :
    slotEntries w (List.replicate c none) = [] := by
  induction c with
  | zero => rfl
  | succ c ih => simp [slotEntries, List.replicate_succ]

/-- Closed slots without entries are all rejected, when a slot holds at least one entry. -/
theorem eq_replicate_none_of_slotEntries_eq_nil {w : ℕ} (hw : 0 < w)
    {Ls : List (Option (List GivensEntry))} (h : slotEntries w Ls = []) :
    Ls = List.replicate Ls.length none := by
  induction Ls with
  | nil => rfl
  | cons o Ls ih =>
    cases o with
    | none =>
      simp only [slotEntries, List.flatMap_cons, Option.map_none, Option.getD_none,
        List.nil_append] at h
      rw [List.length_cons, List.replicate_succ, ← ih h]
    | some es =>
      have hlen : (padEntries w es).length = 0 := by
        simp only [slotEntries, List.flatMap_cons, Option.map_some, Option.getD_some,
          List.append_eq_nil_iff] at h
        rw [h.1, List.length_nil]
      simp only [padEntries, List.length_append, List.length_replicate] at hlen
      omega

/-- The planes of a padded slot are below $N$ when those of its entries are and $N \ge 2$ (the
padding entry has the plane $0$). -/
theorem padEntries_planes {N w : ℕ} {es : List GivensEntry} (hN : 1 < N)
    (hes : ∀ e ∈ es, e.1 + 1 < N) : ∀ e ∈ padEntries w es, e.1 + 1 < N := by
  intro e he
  simp only [padEntries, List.mem_append, List.mem_replicate] at he
  rcases he with he | ⟨-, rfl⟩
  exacts [hes e he, by change 0 + 1 < N; omega]

/-- Rejecting `c` empty slots: from a log with no pending entries and room for `c` more slots,
the slots close as rejected, without a write. -/
theorem HoldsSlottedLog.rejects {lg : ℕ × ℕ} {ns w : ℕ} {L : List (Option (List GivensEntry))}
    {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s) {c : ℕ} (hc : L.length + c ≤ ns) :
    HoldsSlottedLog lg ns w (L ++ List.replicate c none) [] s := by
  induction c with
  | zero => simpa using h
  | succ c ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    exact (ih (by omega)).reject (by simp; omega)

/-- **The log after a prefix of its slots**: the slots after `L` form a slotted log at the start
of slot `L.length`, with `ns - L.length` slots and the same pending entries. -/
theorem HoldsSlottedLog.drop {lg : ℕ × ℕ} {ns w : ℕ} {L L' : List (Option (List GivensEntry))}
    {P : List GivensEntry} {s : Store ℝ} (h : HoldsSlottedLog lg ns w (L ++ L') P s) :
    HoldsSlottedLog (lg.1, lg.2 + L.length * (1 + 5 * w)) (ns - L.length) w L' P s := by
  obtain ⟨hlen, hP, hslots, hpend, hrest⟩ := h
  simp only [List.length_append] at hlen hpend hrest
  have hidx : ∀ j, lg.2 + (L.length + j) * (1 + 5 * w) =
      lg.2 + L.length * (1 + 5 * w) + j * (1 + 5 * w) := fun j => by ring
  refine ⟨by omega, hP, fun j hj => ?_, fun hlt => ?_, fun j hj hjn => ?_⟩
  · obtain ⟨v, hv, hm⟩ := hslots (L.length + j) (by simp; omega)
    have e : (L ++ L')[L.length + j]'(by simp; omega) = L'[j] := by simp
    rw [e, hidx] at hm
    rw [hidx] at hv
    exact ⟨v, hv, hm⟩
  · have := hpend (by omega)
    rwa [hidx] at this
  · have := hrest (L.length + j) (by omega) (by omega)
    rwa [hidx] at this

/-- **The read-back after a prefix** of `j0` slots is the read-back of the log at the start of
slot `j0`, with the remaining slots. -/
theorem slottedLogRead_drop (lg : ℕ × ℕ) (ns w j0 : ℕ) (s : Store ℝ) :
    (slottedLogRead lg ns w s).drop j0 =
      slottedLogRead (lg.1, lg.2 + j0 * (1 + 5 * w)) (ns - j0) w s := by
  refine List.ext_getElem (by simp [slottedLogRead]) fun j h₁ h₂ => ?_
  simp only [slottedLogRead, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [show lg.2 + (j0 + j) * (1 + 5 * w) = lg.2 + j0 * (1 + 5 * w) + j * (1 + 5 * w) by ring]

/-- **The valid entries after a prefix are read back**: in a closed log `L ++ L'`, the valid
entries of the slots read back after the first `L.length` are those of `L'`. -/
theorem HoldsSlottedLog.slotEntries_read_drop {lg : ℕ × ℕ} {ns w : ℕ}
    {L L' : List (Option (List GivensEntry))} {s : Store ℝ}
    (h : HoldsSlottedLog lg ns w (L ++ L') [] s) :
    slotEntries w ((slottedLogRead lg ns w s).drop L.length) = slotEntries w L' := by
  have hlen := h.1
  simp only [List.length_append] at hlen
  have h' := h.drop.rejects (c := ns - L.length - L'.length) (by omega)
  have hread := h'.slotEntries_read (by simp; omega)
  rw [slottedLogRead_drop, ← hread]
  simp

/-- The unitary of the valid entries read back after a prefix of `j0` slots is a measurable
function of the memory. -/
theorem measurable_givensLog_slottedLogRead_drop (lg : ℕ × ℕ) (ns w n j0 : ℕ) :
    Measurable fun m : Mem ℝ =>
      givensLog n (slotEntries w ((slottedLogRead lg ns w m.store).drop j0)) := by
  simpa only [slottedLogRead_drop] using
    measurable_givensLog_slottedLogRead (lg.1, lg.2 + j0 * (1 + 5 * w)) (ns - j0) w n

/-! ### The closed slots as a measurable event -/

section Measurable

open MeasureTheory

/-- The words of a list of entries, entry by entry: word $5i + t$ ($t < 5$) is word $t$ of entry
$i$. -/
theorem getElem?_flatMap_entryWords (L : List GivensEntry) (i t : ℕ) (ht : t < 5) :
    (L.flatMap entryWords)[5 * i + t]? = L[i]?.bind fun e => (entryWords e)[t]? := by
  induction L generalizing i with
  | nil => simp
  | cons e L ih =>
    have h5 : (entryWords e).length = 5 := rfl
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [List.getElem?_append_left (by omega)]
      simp
    | succ i =>
      rw [List.getElem?_append_right (by omega), h5,
        show 5 * (i + 1) + t - 5 = 5 * i + t by omega, ih]
      simp

/-- The plane words a block of entries may hold: the naturals $r$ with $r + 1 < N$. -/
private theorem measurableSet_planeWords (N : ℕ) :
    MeasurableSet {x : ℝ | ∃ r : ℕ, r + 1 < N ∧ x = r} := by
  have e : {x : ℝ | ∃ r : ℕ, r + 1 < N ∧ x = r} =
      (fun r : ℕ => (r : ℝ)) '' {r | r + 1 < N} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun ⟨r, hr, hx⟩ => ⟨r, hr, hx.symm⟩, fun ⟨r, hr, hx⟩ => ⟨r, hr, hx.symm⟩⟩
  rw [e]
  exact ((Set.finite_lt_nat N).subset fun r (hr : r + 1 < N) => by
    change r < N; omega).image _ |>.measurableSet

/-- **An accepted block, cell by cell**: the $5w$ words at offset `o` of buffer `b` are the words
of `w` padded entries with planes $r$, $r + 1 < N$, exactly when every entry's plane word holds
such a natural and its other four words are stored. -/
theorem exists_readBlock_padEntries_iff {s : Store ℝ} {b o w N : ℕ} :
    (∃ es : List GivensEntry, es.length ≤ w ∧ (∀ e ∈ padEntries w es, e.1 + 1 < N) ∧
      s.readBlock b o (5 * w) = some ((padEntries w es).flatMap entryWords)) ↔
    ∀ i < w, (∃ p, s.get b (o + 5 * i) = some p ∧ p ∈ {x : ℝ | ∃ r : ℕ, r + 1 < N ∧ x = r}) ∧
      ∀ t < 4, ∃ p, s.get b (o + (5 * i + (t + 1))) = some p ∧ p ∈ (Set.univ : Set ℝ) := by
  constructor
  · rintro ⟨es, hes, hpl, hrb⟩ i hi
    have hEl : (padEntries w es).length = w := by simp [padEntries]; omega
    obtain ⟨-, hg⟩ := Store.readBlock_eq_some_iff.mp hrb
    have hc : ∀ t < 5, s.get b (o + (5 * i + t)) =
        (entryWords ((padEntries w es)[i]'(by omega)))[t]? := by
      intro t ht
      rw [hg _ (by omega), getElem?_flatMap_entryWords _ i t ht,
        List.getElem?_eq_getElem (by omega)]
      rfl
    refine ⟨⟨_, by simpa [entryWords] using hc 0 (by norm_num), (padEntries w es)[i].1,
      hpl _ (List.getElem_mem _), rfl⟩, fun t ht => ?_⟩
    refine ⟨(entryWords (padEntries w es)[i])[t + 1]'(by simp [entryWords]; omega), ?_, trivial⟩
    rw [hc (t + 1) (by omega), List.getElem?_eq_getElem (by simp [entryWords]; omega)]
  · intro h
    set x : ℕ → ℝ := fun j => (s.get b (o + j)).getD 0 with hx
    set es : List GivensEntry := List.ofFn fun i : Fin w =>
      (⌊x (5 * i)⌋₊, ⟨x (5 * i + 1), x (5 * i + 2)⟩, ⟨x (5 * i + 3), x (5 * i + 4)⟩) with hes
    have hpad : padEntries w es = es := by simp [hes, padEntries]
    have hplane : ∀ i < w, s.get b (o + 5 * i) = some ((⌊x (5 * i)⌋₊ : ℕ) : ℝ) ∧
        ⌊x (5 * i)⌋₊ + 1 < N := by
      intro i hi
      obtain ⟨⟨p, hp, r, hr, rfl⟩, -⟩ := h i hi
      simp [hx, hp, hr]
    have hword : ∀ i < w, ∀ t < 4,
        s.get b (o + (5 * i + (t + 1))) = some (x (5 * i + (t + 1))) := by
      intro i hi t ht
      obtain ⟨-, hrest⟩ := h i hi
      obtain ⟨p, hp, -⟩ := hrest t ht
      simp [hx, hp]
    refine ⟨es, by simp [hes], ?_, ?_⟩
    · rw [hpad]
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact (hplane i i.2).2
    · rw [hpad, Store.readBlock_eq_some_iff]
      refine ⟨by rw [length_flatMap_entryWords]; simp [hes], fun j hj => ?_⟩
      obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 5 ∧ j = 5 * i + t :=
        ⟨j / 5, j % 5, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 5).symm⟩
      have hi : i < w := by omega
      rw [getElem?_flatMap_entryWords _ i t ht]
      simp only [hes, List.getElem?_ofFn, hi, dite_true, Option.bind_some]
      interval_cases t
      · simpa [entryWords] using (hplane i hi).1
      · simpa [entryWords] using hword i hi 0 (by norm_num)
      · simpa [entryWords] using hword i hi 1 (by norm_num)
      · simpa [entryWords] using hword i hi 2 (by norm_num)
      · simpa [entryWords] using hword i hi 3 (by norm_num)

/-- The stores in which slot `j` of the log at `lg` holds some closed slot with planes below
$N$ form a measurable set of memories. -/
private theorem measurableSet_exists_slot (lg : ℕ × ℕ) (w N j : ℕ) :
    MeasurableSet {m : Mem ℝ | ∃ o : Option (List GivensEntry),
      (∀ x ∈ slotEntries w [o], x.1 + 1 < N) ∧
      ∃ v : ℝ, m.store.get lg.1 (lg.2 + j * (1 + 5 * w)) = some v ∧
        match o with
        | none => v ≤ 0
        | some es => 0 < v ∧ es.length ≤ w ∧
            m.store.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
              some ((padEntries w es).flatMap entryWords)} := by
  set z : ℕ × ℕ := (lg.1, lg.2 + j * (1 + 5 * w)) with hz
  have e : {m : Mem ℝ | ∃ o : Option (List GivensEntry),
      (∀ x ∈ slotEntries w [o], x.1 + 1 < N) ∧
      ∃ v : ℝ, m.store.get lg.1 (lg.2 + j * (1 + 5 * w)) = some v ∧
        match o with
        | none => v ≤ 0
        | some es => 0 < v ∧ es.length ≤ w ∧
            m.store.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
              some ((padEntries w es).flatMap entryWords)} =
      {m : Mem ℝ | ∃ v, m.store.get z.1 z.2 = some v ∧ v ∈ Set.Iic 0} ∪
        ({m : Mem ℝ | ∃ v, m.store.get z.1 z.2 = some v ∧ v ∈ Set.Ioi 0} ∩
          ⋂ i : Fin w, ({m : Mem ℝ | ∃ p, m.store.get lg.1 (z.2 + 1 + 5 * i) = some p ∧
            p ∈ {x : ℝ | ∃ r : ℕ, r + 1 < N ∧ x = r}} ∩
            ⋂ t : Fin 4, {m : Mem ℝ | ∃ p,
              m.store.get lg.1 (z.2 + 1 + (5 * i + (t + 1))) = some p ∧ p ∈ Set.univ})) := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter, hz,
      Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, and_true]
    constructor
    · rintro ⟨o, hpl, v, hv, ho⟩
      cases o with
      | none => exact Or.inl ⟨v, hv, ho⟩
      | some es =>
        obtain ⟨h0, hes, hrb⟩ := ho
        have := exists_readBlock_padEntries_iff.mp ⟨es, hes, by simpa using hpl, hrb⟩
        exact Or.inr ⟨⟨v, hv, h0⟩, fun i => ⟨(this i i.2).1, fun t => by
          simpa using (this i i.2).2 t t.2⟩⟩
    · rintro (⟨v, hv, h0⟩ | ⟨⟨v, hv, h0⟩, hb⟩)
      · exact ⟨none, by simp, v, hv, h0⟩
      · obtain ⟨es, hes, hpl, hrb⟩ := exists_readBlock_padEntries_iff.mpr fun i hi =>
          ⟨(hb ⟨i, hi⟩).1, fun t ht => by simpa using (hb ⟨i, hi⟩).2 ⟨t, ht⟩⟩
        exact ⟨some es, by simpa using hpl, v, hv, h0, hes, hrb⟩
  rw [e]
  exact (Mem.measurableSet_get_mem z measurableSet_Iic).union
    ((Mem.measurableSet_get_mem z measurableSet_Ioi).inter (.iInter fun i =>
      (Mem.measurableSet_get_mem (lg.1, z.2 + 1 + 5 * (i : ℕ)) (measurableSet_planeWords N)).inter
        (.iInter fun t => Mem.measurableSet_get_mem (lg.1, z.2 + 1 + (5 * (i : ℕ) + (t + 1)))
          .univ)))

/-- A slot holding a given closed slot `o` is a measurable event. -/
private theorem measurableSet_slot (lg : ℕ × ℕ) (w j : ℕ) (o : Option (List GivensEntry)) :
    MeasurableSet {m : Mem ℝ | ∃ v : ℝ, m.store.get lg.1 (lg.2 + j * (1 + 5 * w)) = some v ∧
      match o with
      | none => v ≤ 0
      | some es => 0 < v ∧ es.length ≤ w ∧
          m.store.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
            some ((padEntries w es).flatMap entryWords)} := by
  cases o with
  | none => exact Mem.measurableSet_get_mem (lg.1, lg.2 + j * (1 + 5 * w)) measurableSet_Iic
  | some es =>
    by_cases hes : es.length ≤ w
    · have e : {m : Mem ℝ | ∃ v : ℝ, m.store.get lg.1 (lg.2 + j * (1 + 5 * w)) = some v ∧
          (0 < v ∧ es.length ≤ w ∧
            m.store.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
              some ((padEntries w es).flatMap entryWords))} =
          {m : Mem ℝ | ∃ v, m.store.get lg.1 (lg.2 + j * (1 + 5 * w)) = some v ∧ v ∈ Set.Ioi 0} ∩
            {m : Mem ℝ | m.store.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
              some ((padEntries w es).flatMap entryWords)} := by
        ext m
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioi, hes, true_and]
        exact ⟨fun ⟨v, hv, h0, hb⟩ => ⟨⟨v, hv, h0⟩, hb⟩, fun ⟨⟨v, hv, h0⟩, hb⟩ => ⟨v, hv, h0, hb⟩⟩
      exact e ▸ (Mem.measurableSet_get_mem (lg.1, lg.2 + j * (1 + 5 * w)) measurableSet_Ioi).inter
        (Mem.measurableSet_readBlock_eq _ _ _ _)
    · have e : {m : Mem ℝ | ∃ v : ℝ, m.store.get lg.1 (lg.2 + j * (1 + 5 * w)) = some v ∧
          (0 < v ∧ es.length ≤ w ∧
            m.store.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
              some ((padEntries w es).flatMap entryWords))} = ∅ := by
        ext m
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun ⟨_, _, _, h, _⟩ => hes h
      exact e ▸ .empty

/-- A closed log made of the fixed slots `L0` and `c` further closed slots with planes below $N$,
slot by slot. -/
private theorem exists_holdsSlottedLog_append_iff {s : Store ℝ} {lg : ℕ × ℕ} {ns w N c : ℕ}
    {L0 : List (Option (List GivensEntry))} :
    (∃ Ls : List (Option (List GivensEntry)), Ls.length = c ∧
      (∀ x ∈ slotEntries w Ls, x.1 + 1 < N) ∧ HoldsSlottedLog lg ns w (L0 ++ Ls) [] s) ↔
    L0.length + c ≤ ns ∧
    (∀ j (hj : j < L0.length), ∃ v : ℝ, s.get lg.1 (lg.2 + j * (1 + 5 * w)) = some v ∧
      match L0[j] with
      | none => v ≤ 0
      | some es => 0 < v ∧ es.length ≤ w ∧
          s.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
            some ((padEntries w es).flatMap entryWords)) ∧
    (∀ j < c, ∃ o : Option (List GivensEntry), (∀ x ∈ slotEntries w [o], x.1 + 1 < N) ∧
      ∃ v : ℝ, s.get lg.1 (lg.2 + (L0.length + j) * (1 + 5 * w)) = some v ∧
        match o with
        | none => v ≤ 0
        | some es => 0 < v ∧ es.length ≤ w ∧
            s.readBlock lg.1 (lg.2 + (L0.length + j) * (1 + 5 * w) + 1) (5 * w) =
              some ((padEntries w es).flatMap entryWords)) ∧
    (L0.length + c < ns → s.get lg.1 (lg.2 + (L0.length + c) * (1 + 5 * w)) = some 0 ∧
      s.readBlock lg.1 (lg.2 + (L0.length + c) * (1 + 5 * w) + 1) (5 * w) =
        some ((padEntries w []).flatMap entryWords)) ∧
    (∀ j, L0.length + c < j → j < ns → s.get lg.1 (lg.2 + j * (1 + 5 * w)) = some 0 ∧
      s.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
        some (List.replicate (5 * w) 0)) := by
  constructor
  · rintro ⟨Ls, rfl, hpl, hlen, -, hslots, hpend, hrest⟩
    simp only [List.length_append] at hlen hpend hrest
    refine ⟨hlen, fun j hj => ?_, fun j hj => ?_, hpend, hrest⟩
    · obtain ⟨v, hv, hm⟩ := hslots j (by simp; omega)
      have e : (L0 ++ Ls)[j]'(by simp; omega) = L0[j] := List.getElem_append_left hj
      rw [e] at hm
      exact ⟨v, hv, hm⟩
    · obtain ⟨v, hv, hm⟩ := hslots (L0.length + j) (by simp; omega)
      have e : (L0 ++ Ls)[L0.length + j]'(by simp; omega) = Ls[j] := by simp
      rw [e] at hm
      refine ⟨Ls[j], fun x hx => hpl x ?_, v, hv, hm⟩
      simp only [slotEntries, List.mem_flatMap, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at hx ⊢
      exact ⟨Ls[j], List.getElem_mem _, hx⟩
  · rintro ⟨hlen, hfix, hnew, hpend, hrest⟩
    choose f hf using fun j : Fin c => hnew j j.2
    refine ⟨List.ofFn f, by simp, fun x hx => ?_, by simp; omega, by simp, fun j hj => ?_,
      by simpa using hpend, fun j hj hjn => hrest j (by simpa using hj) hjn⟩
    · simp only [slotEntries, List.mem_flatMap, List.mem_ofFn] at hx
      obtain ⟨o, ⟨i, rfl⟩, hx⟩ := hx
      exact (hf i).1 x (by simpa [slotEntries] using hx)
    · by_cases hj0 : j < L0.length
      · obtain ⟨v, hv, hm⟩ := hfix j hj0
        have e : (L0 ++ List.ofFn f)[j] = L0[j] := List.getElem_append_left hj0
        exact ⟨v, hv, by rw [e]; exact hm⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = L0.length + j' := ⟨j - L0.length, by omega⟩
        have hj' : j' < c := by simp at hj; omega
        obtain ⟨-, v, hv, hm⟩ := hf ⟨j', hj'⟩
        have e : (L0 ++ List.ofFn f)[L0.length + j'] = f ⟨j', hj'⟩ := by simp
        exact ⟨v, hv, by rw [e]; exact hm⟩

/-- **The stores holding `c` closed slots after a prefix are a measurable event**: the memories
whose store holds a slotted log at `lg` made of the fixed slots `L0` and `c` further closed slots,
with planes below $N$ and no pending entries, form a measurable set. -/
theorem measurableSet_exists_holdsSlottedLog_append (lg : ℕ × ℕ) (ns w N c : ℕ)
    (L0 : List (Option (List GivensEntry))) :
    MeasurableSet {m : Mem ℝ | ∃ Ls : List (Option (List GivensEntry)), Ls.length = c ∧
      (∀ x ∈ slotEntries w Ls, x.1 + 1 < N) ∧ HoldsSlottedLog lg ns w (L0 ++ Ls) [] m.store} := by
  simp only [exists_holdsSlottedLog_append_iff, Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => measurableSet_slot lg w j _)
    (MeasurableSet.inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_exists_slot lg w N (L0.length + j)) (MeasurableSet.inter ?_
        (MeasurableSet.iInter fun j => ?_))))
  · by_cases hP : L0.length + c < ns
    · simp only [hP, Set.iInter_true]
      exact (Mem.measurableSet_get_eq (lg.1, lg.2 + (L0.length + c) * (1 + 5 * w)) (0 : ℝ)).inter
        (Mem.measurableSet_readBlock_eq lg.1 (lg.2 + (L0.length + c) * (1 + 5 * w) + 1) (5 * w)
          _)
    · simp [hP]
  · by_cases h1 : L0.length + c < j
    · by_cases h2 : j < ns
      · simp only [h1, h2, Set.iInter_true]
        exact (Mem.measurableSet_get_eq (lg.1, lg.2 + j * (1 + 5 * w)) (0 : ℝ)).inter
          (Mem.measurableSet_readBlock_eq lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) _)
      · simp [h2]
    · simp [h1]

end Measurable

end NLAlib
