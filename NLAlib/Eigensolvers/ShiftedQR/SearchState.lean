/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Trial

/-!
# Stored state of an ordered candidate search

Before any candidate passes, only the zero flag is required and the matrix output can remain
uninitialized. After the first accepted candidate, the flag is one and the matrix stores that
candidate's exact repeated-shift result. The state refers to the mathematical first accepted
candidate in the actual examined list.

## Main results

* `NLAlib.ShiftedQR.CandidateHolds`: the exact partial search state.
* `NLAlib.ShiftedQR.CandidateHolds.of_trial`: one actual trial extends a rejected prefix.
* `NLAlib.ShiftedQR.CandidateHolds.append_of_some`: an accepted result survives later candidates.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

open Classical in
/-- Actual zero/one flag and the first accepted matrix, requiring no initialized matrix before
any candidate has passed the acceptance test. -/
def CandidateHolds {n : ℕ} (τ γ : ℝ) (k : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ)
    (z f : ℕ × ℕ) (st : Store ℝ) : Prop :=
  match ss.find? (fun s => decide (IsShiftAccept τ γ k H s)) with
  | none => st.get f.1 f.2 = some 0
  | some shift => st.get f.1 f.2 = some 1 ∧
      HoldsMatrix z (multiShiftedQRStep H (List.replicate k shift)) st

/-- With no examined candidates only the actual zero flag is needed. -/
@[simp] theorem candidateHolds_nil {n : ℕ} {τ γ : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {z f : ℕ × ℕ} {st : Store ℝ} :
    CandidateHolds τ γ k H [] z f st ↔ st.get f.1 f.2 = some 0 := by
  rfl

open Classical in
/-- A search with no accepted candidate has its actual flag zero. -/
theorem CandidateHolds.flag_of_none {n : ℕ} {τ γ : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {z f : ℕ × ℕ} {st : Store ℝ}
    (h : CandidateHolds τ γ k H ss z f st)
    (hs : ss.find? (fun s => decide (IsShiftAccept τ γ k H s)) = none) :
    st.get f.1 f.2 = some 0 := by
  simpa only [CandidateHolds, hs] using h

open Classical in
/-- An accepted prefix has its actual flag one and stores precisely its first accepted matrix. -/
theorem CandidateHolds.result_of_some {n : ℕ} {τ γ : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {shift : ℂ}
    {z f : ℕ × ℕ} {st : Store ℝ} (h : CandidateHolds τ γ k H ss z f st)
    (hs : ss.find? (fun s => decide (IsShiftAccept τ γ k H s)) = some shift) :
    st.get f.1 f.2 = some 1 ∧
      HoldsMatrix z (multiShiftedQRStep H (List.replicate k shift)) st := by
  simpa only [CandidateHolds, hs] using h

/-- Disjoint writes preserve the search state, including its partially initialized output. -/
theorem CandidateHolds.of_eqOff {n : ℕ} {τ γ : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {z f : ℕ × ℕ}
    {st st' : Store ℝ} {F : Fp} (h : CandidateHolds τ γ k H ss z f st)
    (hfr : st.EqOff F st')
    (hd : Fp.Disj F (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock f.1 f.2 1)) : CandidateHolds τ γ k H ss z f st' := by
  classical
  unfold CandidateHolds at h ⊢
  split at h
  · rename_i he
    exact hfr.keep (Store.readsOnly_get _ _ _) (hd.mono le_rfl le_sup_right) h
  · rename_i shift he
    exact ⟨hfr.keep (Store.readsOnly_get _ _ _) (hd.mono le_rfl le_sup_right) h.1,
      h.2.of_eqOff hfr (hd.mono le_rfl le_sup_left)⟩

open Classical in
/-- Appending later candidates cannot replace an already accepted first result. -/
theorem CandidateHolds.append_of_some {n : ℕ} {τ γ : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {shift : ℂ}
    {z f : ℕ × ℕ} {st : Store ℝ} (h : CandidateHolds τ γ k H ss z f st)
    (hs : ss.find? (fun s => decide (IsShiftAccept τ γ k H s)) = some shift) (rest : List ℂ) :
    CandidateHolds τ γ k H (ss ++ rest) z f st := by
  simpa only [CandidateHolds, List.find?_append, hs, Option.or] using h

open Classical in
/-- A trial after a wholly rejected prefix stores exactly the first accepted result, or keeps
flag zero if the new candidate is also rejected. Its actual matrix is always computed. -/
theorem CandidateHolds.of_trial {n : ℕ} {τ γ : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {shift : ℂ}
    {z f : ℕ × ℕ} {st : Store ℝ}
    (hs : ss.find? (fun s => decide (IsShiftAccept τ γ k H s)) = none)
    (hZ : HoldsMatrix z (multiShiftedQRStep H (List.replicate k shift)) st)
    (hf : st.get f.1 f.2 = some (if IsShiftAccept τ γ k H shift then (1 : ℝ) else 0)) :
    CandidateHolds τ γ k H (ss ++ [shift]) z f st := by
  classical
  unfold CandidateHolds
  rw [List.find?_append, hs]
  by_cases ha : IsShiftAccept τ γ k H shift
  · simpa [ha, List.find?] using And.intro hf hZ
  · simpa [ha, List.find?] using hf

open Classical in
/-- A complete candidate search with an accepted candidate stores the existing mathematical
first-accepted shifted QR step. Existence is a mathematical candidate property, not an
assumption that the program ran or that its actual flag was set. -/
theorem CandidateHolds.acceptStep {n m : ℕ} {τ B θ α γ : ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {z f : ℕ × ℕ} {st : Store ℝ}
    (h : CandidateHolds τ γ (2 ^ m) H (ss ++ shqrCandidates B θ α γ m H ss) z f st)
    (hex : ∃ s ∈ ss ++ shqrCandidates B θ α γ m H ss, IsShiftAccept τ γ (2 ^ m) H s) :
    st.get f.1 f.2 = some 1 ∧ HoldsMatrix z (shqrAcceptStep τ B θ α γ m H ss) st := by
  classical
  cases he : (ss ++ shqrCandidates B θ α γ m H ss).find?
      (fun s => decide (IsShiftAccept τ γ (2 ^ m) H s)) with
  | none =>
    obtain ⟨s, hs, ha⟩ := hex
    have hn := List.find?_eq_none.mp he s hs
    exact False.elim (hn (by simpa only [decide_eq_true_eq] using ha))
  | some shift =>
    obtain ⟨hFlag, hZ⟩ := h.result_of_some he
    refine ⟨hFlag, ?_⟩
    simpa only [shqrAcceptStep, shqrAcceptShift, he, Option.getD_some] using hZ

end NLAlib.ShiftedQR
