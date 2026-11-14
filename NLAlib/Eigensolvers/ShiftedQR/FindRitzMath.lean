/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveHalfMath
public import NLAlib.Matrix.QRIteration.Ritz

/-!
# Window invariants of the scalar Ritz binary search

The mathematical search and actual program compare the same two contiguous half windows.
Squared norms give the same ordering as norms, including the first-half tie rule.

## Main results

* `NLAlib.ShiftedQR.findRitz_window_succ`: one search level on a contiguous window.
* `NLAlib.ShiftedQR.findRitz_searchNext`: the squared-norm window transition.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

variable {n : ℕ}

/-- One level of the binary search, on the window of $2^{r+1}$ values from index $a$: the search
compares the windows of its two halves and descends into the first on a tie. -/
theorem findRitz_window_succ (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r e a : ℕ)
    (ss : List ℂ) (hlen : a + 2 ^ (r + 1) ≤ ss.length) :
    findRitz H (r + 1) e ((ss.drop a).take (2 ^ (r + 1))) =
      if ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly ((ss.drop (a + 2 ^ r)).take (2 ^ r))))⁻¹
          ^ e) (Fin.last n))‖ ≤
        ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly ((ss.drop a).take (2 ^ r))))⁻¹ ^ e)
          (Fin.last n))‖ then
        findRitz H r (2 * e) ((ss.drop a).take (2 ^ r))
      else findRitz H r (2 * e) ((ss.drop (a + 2 ^ r)).take (2 ^ r)) := by
  have hl : ((ss.drop a).take (2 ^ (r + 1))).length = 2 ^ (r + 1) := by simp; omega
  have hh : 2 ^ (r + 1) / 2 = 2 ^ r := by rw [pow_succ]; omega
  have h1 : ((ss.drop a).take (2 ^ (r + 1))).take (2 ^ r) = (ss.drop a).take (2 ^ r) := by
    rw [List.take_take]; congr 1; apply min_eq_left; rw [pow_succ]; omega
  have h2 : ((ss.drop a).take (2 ^ (r + 1))).drop (2 ^ r) = (ss.drop (a + 2 ^ r)).take (2 ^ r) := by
    rw [List.drop_take, List.drop_drop]
    congr 1; rw [pow_succ]; omega
  rw [findRitz, hl, hh, h1, h2]

/-- The search on a window of one value is that value. -/
theorem findRitz_window_zero (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e a : ℕ) (ss : List ℂ) :
    findRitz H 0 e ((ss.drop a).take 1) = ss.getD a 0 := by
  rw [findRitz]
  simp [List.getD_eq_getElem?_getD, List.head?_take, List.head?_drop]

/-- The squared inverse-polynomial norm compared for one selected window. -/
noncomputable def halfNormSq (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (a h e : ℕ) : ℝ :=
  ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (halfSegment ss a h)))⁻¹ ^ e)
    (Fin.last n))‖ ^ 2

/-- Keep the first half on ties and the second half only when its squared norm is larger. -/
noncomputable def searchNext (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (a h e : ℕ) : ℕ :=
  open Classical in if halfNormSq H ss (a + h) h e ≤ halfNormSq H ss a h e then a else a + h

/-- The actual squared-norm comparison chooses the same half as the mathematical search. -/
theorem findRitz_searchNext (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r e a : ℕ)
    (ss : List ℂ) (hlen : a + 2 ^ (r + 1) ≤ ss.length) :
    findRitz H (r + 1) e (halfSegment ss a (2 ^ (r + 1))) =
      findRitz H r (2 * e) (halfSegment ss (searchNext H ss a (2 ^ r) e) (2 ^ r)) := by
  rw [halfSegment, findRitz_window_succ H r e a ss hlen, searchNext, halfNormSq, halfNormSq]
  classical
  simp only [halfSegment, sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  split_ifs <;> rfl

/-- The chosen half remains inside the full window. -/
theorem searchNext_add_le (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r e a : ℕ)
    (ss : List ℂ) (hlen : a + 2 ^ (r + 1) ≤ ss.length) :
    searchNext H ss a (2 ^ r) e + 2 ^ r ≤ ss.length := by
  unfold searchNext
  have hp : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
  split_ifs <;> omega

/-- The natural half length of the remaining binary-search window. -/
def searchHalfLength (m i : ℕ) : ℕ := 2 ^ (m - i) / 2

/-- A live level's half length is the expected power of two. -/
theorem searchHalfLength_eq {m i : ℕ} (hi : i < m) :
    searchHalfLength m i = 2 ^ (m - i - 1) := by
  unfold searchHalfLength
  conv_lhs => rw [show m - i = (m - i - 1) + 1 by omega]
  rw [pow_succ]
  omega

/-- Halving a live natural half length gives the next level's half length, including zero
once the search has selected its singleton. -/
theorem searchHalfLength_succ {m i : ℕ} (hi : i < m) :
    searchHalfLength m (i + 1) = searchHalfLength m i / 2 := by
  rw [searchHalfLength_eq hi]
  unfold searchHalfLength
  rw [show m - (i + 1) = m - i - 1 by omega]

/-- The start index after each actual half selection. -/
noncomputable def searchStart (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => searchNext H ss (searchStart H ss m i) (searchHalfLength m i) (2 ^ i)

/-- The current window fits and retains exactly the original mathematical search result. -/
theorem searchStart_spec (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (m : ℕ) (hlen : ss.length = 2 ^ m) : ∀ i ≤ m,
    searchStart H ss m i + 2 ^ (m - i) ≤ ss.length ∧
      findRitz H m 1 ss = findRitz H (m - i) (2 ^ i)
        (halfSegment ss (searchStart H ss m i) (2 ^ (m - i))) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [searchStart, halfSegment, Nat.sub_zero, pow_zero, List.drop_zero, Nat.zero_add]
    exact ⟨by omega, by rw [← hlen, List.take_length]⟩
  | succ i ih =>
    intro hi
    obtain ⟨hfit, heq⟩ := ih (by omega)
    have hil : i < m := by omega
    have hr : m - i = (m - i - 1) + 1 := by omega
    have hnext := findRitz_searchNext H (m - i - 1) (2 ^ i) (searchStart H ss m i) ss
      (by simpa only [← hr] using hfit)
    have hnew := searchNext_add_le H (m - i - 1) (2 ^ i) (searchStart H ss m i) ss
      (by simpa only [← hr] using hfit)
    refine ⟨?_, ?_⟩
    · simpa only [searchStart, searchHalfLength_eq hil,
        show m - (i + 1) = m - i - 1 by omega] using hnew
    · rw [heq, hr, hnext]
      simp only [searchStart, searchHalfLength_eq hil, pow_succ,
        show m - (i + 1) = m - i - 1 by omega, Nat.mul_comm 2]

/-- At the last level the chosen actual list entry is the mathematical search result. -/
theorem searchStart_last (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (m : ℕ) (hlen : ss.length = 2 ^ m) :
    searchStart H ss m m < ss.length ∧ findRitz H m 1 ss = ss.getD (searchStart H ss m m) 0 := by
  obtain ⟨hfit, heq⟩ := searchStart_spec H ss m hlen m le_rfl
  simp only [Nat.sub_self, pow_zero] at hfit heq
  exact ⟨by omega, heq.trans (findRitz_window_zero H _ _ ss)⟩

end NLAlib.ShiftedQR
