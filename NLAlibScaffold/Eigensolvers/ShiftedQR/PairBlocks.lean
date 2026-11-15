/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Store
public import Mathlib.Analysis.Complex.Basic

/-!
# Complex numbers stored as pairs

The rounded shifted QR programs store a list of complex numbers $z_0, z_1, \dots$ as the words
$\operatorname{Re} z_0, \operatorname{Im} z_0, \operatorname{Re} z_1, \dots$ of a block. These
lemmas read single entries, windows and whole blocks of such a list.

## Main results

* `NLAlib.ShiftedQR.get_of_readBlock_flatMap_pair`,
  `NLAlib.ShiftedQR.readBlock_flatMap_pair_of_get`: a block of pairs and its cells.
* `NLAlib.ShiftedQR.readBlock_flatMap_pair_window`: a window of a block of pairs.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The entries $2j$ and $2j + 1$ of the pairs of a list of complex numbers. -/
theorem getElem?_flatMap_pair (zs : List ℂ) {j : ℕ} (hj : j < zs.length) :
    (zs.flatMap fun z => [z.re, z.im])[2 * j]? = some zs[j].re ∧
      (zs.flatMap fun z => [z.re, z.im])[2 * j + 1]? = some zs[j].im := by
  induction zs generalizing j with
  | nil => simp at hj
  | cons z zs ih =>
    cases j with
    | zero => simp
    | succ j =>
      obtain ⟨h1, h2⟩ := ih (j := j) (by simpa using hj)
      rw [List.flatMap_cons, show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
        show 2 * j + 1 + 1 + 1 = 2 * j + 1 + 1 + 1 from rfl]
      simpa using And.intro h1 h2

/-- A block of pairs read from its cells. -/
theorem readBlock_flatMap_pair_of_get {s : Store ℝ} {b o : ℕ} {zs : List ℂ}
    (h : ∀ j (hj : j < zs.length), s.get b (o + 2 * j) = some zs[j].re ∧
      s.get b (o + 2 * j + 1) = some zs[j].im) :
    s.readBlock b o (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]) := by
  refine Store.readBlock_eq_some_iff.mpr ⟨by simp [List.length_flatMap]; ring, fun k hk => ?_⟩
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hj : j < zs.length := by omega
    rw [(h j hj).1, (getElem?_flatMap_pair zs hj).1]
  · have hj : j < zs.length := by omega
    rw [← Nat.add_assoc, (h j hj).2, (getElem?_flatMap_pair zs hj).2]

/-- The cells of a block of pairs. -/
theorem get_of_readBlock_flatMap_pair {s : Store ℝ} {b o : ℕ} {zs : List ℂ}
    (h : s.readBlock b o (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]))
    {j : ℕ} (hj : j < zs.length) :
    s.get b (o + 2 * j) = some zs[j].re ∧ s.get b (o + 2 * j + 1) = some zs[j].im := by
  obtain ⟨-, hg⟩ := Store.readBlock_eq_some_iff.mp h
  refine ⟨(hg (2 * j) (by omega)).trans (getElem?_flatMap_pair zs hj).1, ?_⟩
  rw [Nat.add_assoc]
  exact (hg (2 * j + 1) (by omega)).trans (getElem?_flatMap_pair zs hj).2

/-- Dropping the pairs of the first `a` complex numbers. -/
theorem drop_flatMap_pair (l : List ℂ) (a : ℕ) :
    (l.flatMap fun z => [z.re, z.im]).drop (2 * a) = (l.drop a).flatMap fun z => [z.re, z.im] := by
  induction l generalizing a with
  | nil => simp
  | cons z l ih =>
    cases a with
    | zero => simp
    | succ a =>
      rw [List.flatMap_cons, List.drop_succ_cons, show 2 * (a + 1) = 2 * a + 2 by ring,
        ← List.drop_drop, show [z.re, z.im] ++ l.flatMap (fun z => [z.re, z.im]) =
          z.re :: z.im :: l.flatMap (fun z => [z.re, z.im]) from rfl]
      simpa using ih a

/-- Taking the pairs of the first `h` complex numbers. -/
theorem take_flatMap_pair (l : List ℂ) (h : ℕ) :
    (l.flatMap fun z => [z.re, z.im]).take (2 * h) = (l.take h).flatMap fun z => [z.re, z.im] := by
  induction l generalizing h with
  | nil => simp
  | cons z l ih =>
    cases h with
    | zero => simp
    | succ h =>
      rw [List.flatMap_cons, List.take_succ_cons, show 2 * (h + 1) = 2 * h + 1 + 1 by ring]
      simpa using ih h

/-- A window of the pairs of a stored list of complex numbers. -/
theorem readBlock_flatMap_pair_window {s : Store ℝ} {b o : ℕ} {l : List ℂ}
    (hl : s.readBlock b o (2 * l.length) = some (l.flatMap fun z => [z.re, z.im]))
    {a h : ℕ} (hah : a + h ≤ l.length) :
    s.readBlock b (o + 2 * a) (2 * h) =
      some (((l.drop a).take h).flatMap fun z => [z.re, z.im]) := by
  rw [Store.readBlock_sub hl (by omega), drop_flatMap_pair, take_flatMap_pair]

end NLAlib.ShiftedQR
