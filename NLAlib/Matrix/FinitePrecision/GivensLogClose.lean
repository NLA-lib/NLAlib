/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensLogSlots

/-!
# Opening and closing a Givens log

Bookkeeping for programs whose number of closed slots is not fixed in advance: opening a log on
any machine whose literal $0$ is exact, closing a pending slot together with further empty slots
as rejected, forgetting the pending entries of a log with no open slot, and the valid entries
read back from a closed log (`NLAlib.slottedLogRead`).

## Main results

* `NLAlib.slottedLogOpen_writes_of_lit_zero`: opening a log stores the empty log.
* `NLAlib.HoldsSlottedLog.reject_pending`: close the pending slot and more as rejected.
* `NLAlib.HoldsSlottedLog.of_length_eq`: a full log has no pending entries.
* `NLAlib.HoldsSlottedLog.slotEntries_slottedLogRead`: the valid entries read back.
-/

@[expose] public section

namespace NLAlib

open Ops

section Specs

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O]

omit [Has IndexOp O] in
/-- Opening a log stores the empty log, on any scalar machine whose literal $0$ is exact.
Shared by the trees of `NLAlib.hessenbergReduceQ`, `NLAlib.ShiftedQR.roundedDecoupleLoopWith`,
`NLAlib.ShiftedQR.roundedDecoupleWith` and 3 more. -/
theorem slottedLogOpen_writes_of_lit_zero {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (h0 : Mch.lit 0 = 0) {ns w : ℕ} {lg : ℕ × ℕ} {τ : Tape ℝ}
    {μ : Mem ℝ} (hroom : lg.2 + ns * (1 + 5 * w) ≤ μ.store.len lg.1) :
    Writes .total I τ (slottedLogOpen (O := O) (Q := Q)) (Env.frame [ns, w] [lg])
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsSlottedLog lg ns w [] [] μ'.store) μ := by
  unfold slottedLogOpen
  refine (writes_fill (v := fun _ => (0 : ℝ)) (pos := fun _ => μ.pos) rfl rfl
    fun i hi m' hfr _ hp => ?_).mono le_rfl ?_
  · refine (writes_call_const (hS (.lit 0)) rfl trivial ?_).mono le_rfl ?_
    · dsimp only; rw [hfr.len_eq]; omega
    · exact fun m'' _ ⟨hp', hg⟩ => ⟨by simpa [h0] using hg, hp'.trans hp⟩
  · rintro μ' - ⟨hv, hp⟩
    refine ⟨hp, holdsSlottedLog_nil_of_readBlock ?_⟩
    rw [Store.holdsVec_iff_readBlock.mp hv]
    simp

end Specs

/-- A log with no open slot holds whatever its pending entries: they are not stored. -/
theorem HoldsSlottedLog.of_length_eq {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) (hL : L.length = ns) :
    HoldsSlottedLog lg ns w L [] s := by
  obtain ⟨hLn, -, hc, -, hf⟩ := h
  exact ⟨hLn, Nat.zero_le _, hc, fun h => absurd h (by omega), hf⟩

/-- Closing the pending slot and `k` more as rejected: a log with pending entries and room for
$k + 1$ more slots holds, with them rejected, as a closed log. -/
theorem HoldsSlottedLog.reject_pending {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) {k : ℕ} (hk : L.length + (k + 1) ≤ ns) :
    HoldsSlottedLog lg ns w (L ++ List.replicate (k + 1) none) [] s := by
  have := (h.reject (by omega)).rejects (c := k) (by simp; omega)
  rwa [List.append_assoc, List.singleton_append, ← List.replicate_succ] at this

/-- The valid entries read back from a stored closed log are its own, up to padding. -/
theorem HoldsSlottedLog.slotEntries_slottedLogRead {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s) :
    slotEntries w (slottedLogRead lg ns w s) = slotEntries w L := by
  have hL := h.1
  rw [h.close.slottedLogRead_eq (by simp; omega), slotEntries_map_padEntries,
    slotEntries_append_replicate_none]

end NLAlib
