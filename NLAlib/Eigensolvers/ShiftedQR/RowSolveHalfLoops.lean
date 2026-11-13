/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveHalf

/-!
# Repeated checked inverse-row solves for a half norm

The inner loop visits the selected contiguous shift segment. The outer loop repeats that
segment for the supplied exponent. A set flag retains its actual singular-shift witness and
skips all later arithmetic, including unused shifts in empty loops.

## Main results

* `NLAlib.ShiftedQR.halfRound`: one segment of checked shifted row solves.
* `NLAlib.ShiftedQR.halfRounds`: the exponent's repeated segments.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Visit every candidate of the supplied half once. -/
def halfRound : Impl Op Tst := opsImpl% [n, k, a, h] (H, SS, V, Flag) → (V, Flag) {
  for i < h {
    run halfSolveCandidate.body [n, k, a, i] (H, SS, V, Flag, V, Flag)
  }
}

/-- Repeat the half's candidate segment by the supplied exponent. -/
def halfRounds : Impl Op Tst := opsImpl% [n, k, a, h, e] (H, SS, V, Flag) → (V, Flag) {
  for r < e {
    run halfRound.body [n, k, a, h] (H, SS, V, Flag, V, Flag)
  }
}

/-- One segment computes its inverse-row fold or retains a witnessed singular candidate.
All source words are preserved and no unused shift is tested.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem halfRound_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h : ℕ} {b ss v f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ} {w : Fin (n + 1) → ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hak : a + h ≤ k)
    (hal : a + h ≤ shifts.length) (hSep : HalfSolveSeparate (n + 1) k b ss v f)
    (hl : m.Live [b, ss, v, f, v, f]) (hf : f.2 + 1 ≤ m.store.len f.1)
    (hstate : HalfVectorState v f H (halfSegment shifts a h) w m.store) :
    Writes .total I τ halfRound.body (Env.frame [n + 1, k, a, h] [b, ss, v, f, v, f])
      (Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
        HoldsShifts (k := k) ss shifts m'.store ∧
        HalfVectorState v f H (halfSegment shifts a h)
          (shiftSolvePrefix H (halfSegment shifts a h) w h) m'.store) m := by
  let seg := halfSegment shifts a h
  let F := Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1
  have hlen : seg.length = h := length_halfSegment hal
  change Writes .total I τ (.loop _ _) _ _ _ m
  refine writes_loop (N := h) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
      HoldsShifts (k := k) ss shifts m'.store ∧
      HalfVectorState v f H seg (shiftSolvePrefix H seg w i) m'.store)
    ⟨rfl, hB, hSS, by simpa only [shiftSolvePrefix_zero] using hstate⟩ ?_
  intro i hi m' hfr ⟨hp, hB', hSS', hstate'⟩
  rcases hstate' with ⟨hone, shift, hmem, hdet⟩ | ⟨hzero, hV⟩
  · have hw := halfSolveCandidate_singular hCmp (τ := τ) (n := n + 1) (k := k)
      (a := a) (i := i) (b := b) (ss := ss) (v := v) hone
    refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
      (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
      (hl.congr hfr.length_eq)).mono bot_le ?_
    rintro m'' _ rfl
    exact ⟨hp, hB', hSS', Or.inl ⟨hone, shift, hmem, hdet⟩⟩
  · have hw := halfSolveCandidate_clear hS hE hCmp (τ := τ) (a := a) (i := i)
      hH hB' hSS' hV (by omega) hSep hzero (by rw [hfr.len_eq]; exact hf)
    refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
      (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
      (hl.congr hfr.length_eq)).mono le_rfl ?_
    intro m'' _ ⟨hp', hB'', hSS'', hresult⟩
    refine ⟨hp'.trans hp, hB'', hSS'', ?_⟩
    have hi' : i < seg.length := by omega
    have hshift : shifts.getD (a + i) 0 = seg.getD i 0 := (halfSegment_getD hi).symm
    rcases hresult with ⟨hone, hdet⟩ | ⟨hzero, hV'⟩
    · refine Or.inl ⟨hone, shifts.getD (a + i) 0, ?_, hdet⟩
      rw [hshift, List.getD_eq_getElem seg 0 hi']
      exact List.getElem_mem hi'
    · refine Or.inr ⟨hzero, ?_⟩
      rw [hshift] at hV'
      simpa only [shiftSolvePrefix_succ H seg w hi'] using hV'

/-- The exponent loop computes the inverse-polynomial row or certifies a singular candidate.
An exponent of zero does not inspect any selected shift.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem halfRounds_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e : ℕ} {b ss v f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hak : a + h ≤ k)
    (hal : a + h ≤ shifts.length) (hSep : HalfSolveSeparate (n + 1) k b ss v f)
    (hl : m.Live [b, ss, v, f, v, f]) (hf : f.2 + 1 ≤ m.store.len f.1)
    (hstate : HalfVectorState v f H (halfSegment shifts a h) (Pi.single (Fin.last n) 1) m.store) :
    Writes .total I τ halfRounds.body (Env.frame [n + 1, k, a, h, e] [b, ss, v, f, v, f])
      (Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
        HoldsShifts (k := k) ss shifts m'.store ∧
        HalfVectorState v f H (halfSegment shifts a h)
          (halfSolvePrefix H (halfSegment shifts a h) e) m'.store) m := by
  let seg := halfSegment shifts a h
  let F := Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1
  have hlen : seg.length = h := length_halfSegment hal
  change Writes .total I τ (.loop _ _) _ _ _ m
  refine writes_loop (N := e) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
      HoldsShifts (k := k) ss shifts m'.store ∧
      HalfVectorState v f H seg (halfSolvePrefix H seg i) m'.store)
    ⟨rfl, hB, hSS, hstate⟩ ?_
  intro i _ m' hfr ⟨hp, hB', hSS', hstate'⟩
  have hw := halfRound_writes hS hE hCmp (τ := τ) hH hB' hSS' hak hal hSep
    (hl.congr hfr.length_eq) (by rw [hfr.len_eq]; exact hf) hstate'
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (hl.congr hfr.length_eq)).mono le_rfl ?_
  intro m'' _ ⟨hp', hB'', hSS'', hstate''⟩
  refine ⟨hp'.trans hp, hB'', hSS'', ?_⟩
  change HalfVectorState v f H seg
    (shiftSolvePrefix H seg (halfSolvePrefix H seg i) h) m''.store at hstate''
  have he : shiftSolvePrefix H seg (halfSolvePrefix H seg i) h =
      halfSolvePrefix H seg (i + 1) := by
    rw [← hlen, ← halfSolvePrefix_succ H seg i]
  simpa only [he] using hstate''

end NLAlib.ShiftedQR
