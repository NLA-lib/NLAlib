/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Column
public import NLAlib.Matrix.Factorizations.LUEntries

/-!
# Canonical factors from materialized machine columns

The actual word updates of `LU.materializeColumn` extend the canonical lower-column and
upper-row prefixes. The residual words decode to the current Gaussian state, and previous
factor prefixes decode to the canonical factors with initialized zero suffixes. Zero pivots
use the guarded literal-zero branch, so these statements require no nonsingularity.

## Main results

* `NLAlib.LU.columnLowerValues_prefix`: extend the committed lower columns by one.
* `NLAlib.LU.columnUpperValues_prefix`: extend the committed upper rows by one.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} {N : ℕ} {dec : K → ℝ} {M : Machine K}

/-- At a readable Gaussian residual, the actual guarded lower-column word update extends the
canonical lower prefix by one, including a zero pivot without a machine division by zero. -/
theorem columnLowerValues_prefix_of_column (hM : ExactModel dec M) (zeroPivot : Bool)
    (R L : ℕ → ℕ → K) (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N)
    (hz : zeroPivot = true ↔ dec (R k k) = 0)
    (hcol : ∀ i : Fin N, dec (R i k) = gaussState A k.val i k)
    (hlo : ∀ i j : Fin N, dec (L i j) = if j.val < k.val then luLower A i j else 0)
    (i j : Fin N) :
    dec (columnLowerValues M zeroPivot R L k i j) =
      if j.val < k.val + 1 then luLower A i j else 0 := by
  rw [columnLowerValues_dec hM zeroPivot R L k i j hz]
  by_cases hj : j = k
  · subst j
    rw [if_pos (Nat.lt_succ_self k.val), luLower_apply_eq_ite]
    by_cases hi : i < k
    · have hn : ¬k.val ≤ i.val := not_le.mpr hi
      rw [if_neg (fun h : k.val = k.val ∧ k.val ≤ i.val => hn h.2),
        hlo i k, if_neg (Nat.lt_irrefl k.val), if_pos hi]
    · have hki : k.val ≤ i.val := le_of_not_gt hi
      rw [if_pos ⟨rfl, hki⟩, if_neg hi]
      by_cases he : i = k
      · subst i
        simp only [if_true]
      · have hne : i.val ≠ k.val := fun h => he (Fin.ext h)
        rw [if_neg hne, if_neg he, hcol i, hcol k]
  · have hjn : j.val ≠ k.val := fun h => hj (Fin.ext h)
    rw [if_neg (fun h : j.val = k.val ∧ k.val ≤ i.val => hjn h.1), hlo i j]
    by_cases hlt : j.val < k.val
    · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
    · have hnot : ¬j.val < k.val + 1 := by omega
      rw [if_neg hlt, if_neg hnot]

/-- The full Gaussian residual specializes the pivot-only materialization lemma. -/
theorem columnLowerValues_prefix (hM : ExactModel dec M) (zeroPivot : Bool)
    (R L : ℕ → ℕ → K) (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N)
    (hz : zeroPivot = true ↔ dec (R k k) = 0)
    (hres : ∀ i j : Fin N, dec (R i j) = gaussState A k.val i j)
    (hlo : ∀ i j : Fin N, dec (L i j) = if j.val < k.val then luLower A i j else 0)
    (i j : Fin N) :
    dec (columnLowerValues M zeroPivot R L k i j) =
      if j.val < k.val + 1 then luLower A i j else 0 := by
  exact columnLowerValues_prefix_of_column hM zeroPivot R L A k hz (fun i => hres i k) hlo i j

/-- Copying the actual Gaussian pivot-row tail extends the canonical upper prefix by one.
The entries left of the pivot retain their initialized structural zeros. -/
theorem columnUpperValues_prefix_of_row (R U : ℕ → ℕ → K)
    (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N)
    (hrow : ∀ j : Fin N, dec (R k j) = gaussState A k.val k j)
    (hup : ∀ i j : Fin N, dec (U i j) = if i.val < k.val then luUpper A i j else 0)
    (i j : Fin N) :
    dec (columnUpperValues R U k i j) =
      if i.val < k.val + 1 then luUpper A i j else 0 := by
  by_cases hi : i = k
  · subst i
    rw [if_pos (Nat.lt_succ_self k.val), luUpper_apply_eq_ite]
    by_cases hj : j < k
    · have hn : ¬k.val ≤ j.val := not_le.mpr hj
      rw [columnUpperValues, if_neg (fun h : k.val = k.val ∧ k.val ≤ j.val => hn h.2), hup k j,
        if_neg (Nat.lt_irrefl k.val), if_pos hj]
    · have hkj : k.val ≤ j.val := le_of_not_gt hj
      rw [columnUpperValues, if_pos ⟨rfl, hkj⟩, if_neg hj, hrow j]
  · have hin : i.val ≠ k.val := fun h => hi (Fin.ext h)
    rw [columnUpperValues, if_neg (fun h : i.val = k.val ∧ k.val ≤ j.val => hin h.1), hup i j]
    by_cases hlt : i.val < k.val
    · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
    · have hnot : ¬i.val < k.val + 1 := by omega
      rw [if_neg hlt, if_neg hnot]

/-- The full Gaussian residual specializes the pivot-only materialization lemma. -/
theorem columnUpperValues_prefix (R U : ℕ → ℕ → K)
    (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N)
    (hres : ∀ i j : Fin N, dec (R i j) = gaussState A k.val i j)
    (hup : ∀ i j : Fin N, dec (U i j) = if i.val < k.val then luUpper A i j else 0)
    (i j : Fin N) :
    dec (columnUpperValues R U k i j) =
      if i.val < k.val + 1 then luUpper A i j else 0 := by
  exact columnUpperValues_prefix_of_row R U A k (fun j => hres k j) hup i j

/-- The actual materialization postcondition extends both decoded canonical factor prefixes.
This reads the packed output blocks from the word specification; no execution, factorization
or nonzero-pivot conclusion is assumed. -/
theorem materializeColumnSpec_prefix_of_column_row [Inhabited K] (hM : ExactModel dec M)
    {rs ls us ls' us' : List K} {τ : Tape K} (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N)
    (hpost : (materializeColumnSpec M dec).post [N, k.val] τ [rs, ls, us] [ls', us'])
    (hcol : ∀ i : Fin N, decodeMatrix dec N N rs i k = gaussState A k.val i k)
    (hrow : ∀ j : Fin N, decodeMatrix dec N N rs k j = gaussState A k.val k j)
    (hlo : ∀ i j : Fin N,
      decodeMatrix dec N N ls i j = if j.val < k.val then luLower A i j else 0)
    (hup : ∀ i j : Fin N,
      decodeMatrix dec N N us i j = if i.val < k.val then luUpper A i j else 0) :
    (∀ i j : Fin N,
      decodeMatrix dec N N ls' i j = if j.val < k.val + 1 then luLower A i j else 0) ∧
    (∀ i j : Fin N,
      decodeMatrix dec N N us' i j = if i.val < k.val + 1 then luUpper A i j else 0) := by
  obtain ⟨zeroPivot, hz, hls, hus⟩ := hpost
  have hRc (i : Fin N) : dec (vec rs (k * N + i)) = gaussState A k.val i k := by
    simpa only [decodeMatrix_apply] using hcol i
  have hRr (j : Fin N) : dec (vec rs (j * N + k)) = gaussState A k.val k j := by
    simpa only [decodeMatrix_apply] using hrow j
  constructor
  · intro i j
    rw [hls]
    change dec ((EntryCodec.scalar K).matrix N N
      ((EntryCodec.scalar K).packMatrix N N
        (columnLowerValues M zeroPivot (fun i j => vec rs (j * N + i))
          (fun i j => vec ls (j * N + i)) k)) i j) = _
    rw [EntryCodec.matrix_packMatrix]
    exact columnLowerValues_prefix_of_column hM zeroPivot _ _ A k hz hRc
      (fun i j => by simpa only [decodeMatrix_apply] using hlo i j) i j
  · intro i j
    rw [hus]
    change dec ((EntryCodec.scalar K).matrix N N
      ((EntryCodec.scalar K).packMatrix N N
        (columnUpperValues (fun i j => vec rs (j * N + i))
          (fun i j => vec us (j * N + i)) k)) i j) = _
    rw [EntryCodec.matrix_packMatrix]
    exact columnUpperValues_prefix_of_row _ _ A k hRr
      (fun i j => by simpa only [decodeMatrix_apply] using hup i j) i j

/-- A full decoded Gaussian residual supplies the pivot row and column required by the
materialization consumer. Its original full-residual interface is retained. -/
theorem materializeColumnSpec_prefix [Inhabited K] (hM : ExactModel dec M)
    {rs ls us ls' us' : List K} {τ : Tape K} (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N)
    (hpost : (materializeColumnSpec M dec).post [N, k.val] τ [rs, ls, us] [ls', us'])
    (hres : ∀ i j : Fin N, decodeMatrix dec N N rs i j = gaussState A k.val i j)
    (hlo : ∀ i j : Fin N,
      decodeMatrix dec N N ls i j = if j.val < k.val then luLower A i j else 0)
    (hup : ∀ i j : Fin N,
      decodeMatrix dec N N us i j = if i.val < k.val then luUpper A i j else 0) :
    (∀ i j : Fin N,
      decodeMatrix dec N N ls' i j = if j.val < k.val + 1 then luLower A i j else 0) ∧
    (∀ i j : Fin N,
      decodeMatrix dec N N us' i j = if i.val < k.val + 1 then luUpper A i j else 0) := by
  exact materializeColumnSpec_prefix_of_column_row hM A k hpost
    (fun i => hres i k) (fun j => hres k j) hlo hup

end NLAlib.LU
