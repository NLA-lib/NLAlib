/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensLog
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Validating a slot of a Givens log with an exact literal one

`NLAlib.slottedLogValidate_writes` closes the pending slot of a slotted log under the standard
model. A program that assumes no rounding model (a termination theorem) knows instead that the
natural literal $1$ is exact (`NLAlib.IsExactNatLit` at $1$), which is all the valid word needs: it
must be positive.

## Main results

* `NLAlib.HoldsSlottedLog.validate_of_eqOff`: a positive valid word closes the pending slot.
* `NLAlib.replicate_zero_flatMap_entryWords`: the words of the zero fill.
* `NLAlib.slottedLogValidate_writes_of_exactNat`: the validation with an exact literal one.
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

end NLAlib
