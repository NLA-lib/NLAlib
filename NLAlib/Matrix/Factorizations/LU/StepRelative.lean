/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ColumnRelative
public import NLAlib.Matrix.Factorizations.LU.SchurRelative
public import NLAlib.Matrix.Factorizations.LU.Step
public import NLAlib.Matrix.Perturbation.LURoundingPrefix

/-!
# Rounded LU prefixes from actual stored word steps

The materialized column and row are updates of the decoded factors. Their actual quotient
errors and the five actual saved-pivot roundings advance the pure reconstruction invariant.
A zero pivot is admitted when its active column is zero, as implied by pivot selection.

## Main results

* `NLAlib.LU.materializeColumnSpec_relative`: actual factor updates and quotient errors.
* `NLAlib.LU.stepSpec_rounding`: the actual zero-safe step advances rounded reconstruction.
-/

@[expose] public section

namespace NLAlib.LU

open Ops Computation

variable {K : Type} [Inhabited K] {N : ℕ}

/-- Actual column words give decoded matrix updates and relative quotient errors. Exact
unit literals are supplied by the bounded-index interface of concrete pivoted routines. -/
theorem materializeColumnSpec_relative {M : Machine K} {dec : K → ℝ} {u : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hone : dec (M.lit 1) = 1) (k : Fin N)
    {rs ls us ls' us' : List K} {τ : Tape K}
    (hpost : (materializeColumnSpec M dec).post [N, k.val] τ [rs, ls, us] [ls', us'])
    (hL : ∀ i : Fin N, i < k → decodeMatrix dec N N ls i k = 0)
    (hU : ∀ j : Fin N, j < k → decodeMatrix dec N N us k j = 0) :
    let R := decodeMatrix dec N N rs
    let v := fun i : Fin N => relativeLowerColumn M dec (fun i j => vec rs (j * N + i)) k.val i.val
    decodeMatrix dec N N ls' = (decodeMatrix dec N N ls).updateCol k v ∧
      decodeMatrix dec N N us' = (decodeMatrix dec N N us).updateRow k
        (fun j => if j < k then 0 else R k j) ∧
      (∀ i : Fin N, i < k → v i = 0) ∧ v k = 1 ∧
      ∀ i : Fin N, k < i → RelErr u (R i k / R k k) (v i) := by
  obtain ⟨zeroPivot, hz, hls, hus⟩ := hpost
  let Rw := fun i j => vec rs (j * N + i)
  let Lw := fun i j => vec ls (j * N + i)
  let Uw := fun i j => vec us (j * N + i)
  have hzero : dec (M.lit 0) = 0 := by
    have hh := hM.lit 0
    norm_num at hh
    exact hh
  have hLt : ∀ i < k.val, dec (Lw i k.val) = 0 := by
    intro i hi
    simpa only [decodeMatrix_apply] using hL ⟨i, hi.trans k.isLt⟩ hi
  have hUt : ∀ j < k.val, dec (Uw k.val j) = 0 := by
    intro j hj
    simpa only [decodeMatrix_apply] using hU ⟨j, hj.trans k.isLt⟩ hj
  have hLeq : decodeMatrix dec N N ls' = fun i j : Fin N =>
      dec (columnLowerValues M zeroPivot Rw Lw k.val i.val j.val) := by
    rw [hls, decodeMatrix, EntryCodec.matrix_packMatrix]
    rfl
  have hUeq : decodeMatrix dec N N us' = fun i j : Fin N =>
      dec (columnUpperValues Rw Uw k.val i.val j.val) := by
    rw [hus, decodeMatrix, EntryCodec.matrix_packMatrix]
    rfl
  obtain ⟨hvzero, hvdiag, hvrel⟩ := relativeLowerColumn_error hM hu Rw k.val
  refine ⟨?_, ?_, fun i hi => hvzero i.val hi, hvdiag, ?_⟩
  · ext i j
    rw [hLeq]
    dsimp only
    rw [dec_columnLowerValues_eq hzero hone zeroPivot Rw Lw k.val i.val j.val hz hLt]
    simp only [Matrix.updateCol_apply, decodeMatrix_apply, Lw, Rw, Fin.ext_iff]
  · ext i j
    rw [hUeq]
    dsimp only
    rw [dec_columnUpperValues_eq Rw Uw k.val i.val j.val hUt]
    simp only [Matrix.updateRow_apply, decodeMatrix_apply, Rw, Uw, Fin.ext_iff, Fin.lt_def]
  · intro i hi
    simpa only [decodeMatrix_apply] using hvrel i.val hi


omit [Inhabited K] in
/-- The rounded saved-pivot word formula advances pure reconstruction at a nonzero pivot.
All scalar witnesses are read from the machine functions in their actual multiplication order. -/
theorem schurValues_rounding {M : Machine K} {dec : K → ℝ} {u : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u < 1)
    {A S L U : Matrix (Fin N) (Fin N) ℝ} {k : Fin N}
    (hprefix : IsLURoundingPrefix u k.val A S L U) (Rw : ℕ → ℕ → K)
    (hS : S = fun i j : Fin N => dec (Rw i j)) (v : Fin N → ℝ)
    (hvzero : ∀ i, i < k → v i = 0) (hvdiag : v k = 1)
    (hvrel : ∀ i, k < i → RelErr u (S i k / S k k) (v i)) (hp : S k k ≠ 0) :
    IsLURoundingPrefix u (k.val + 1) A
      (fun i j : Fin N => dec (schurValues M Rw k.val i.val j.val))
      (L.updateCol k v) (U.updateRow k (fun j => if j < k then 0 else S k j)) := by
  let c := M.div (M.lit (-1)) (Rw k k)
  let t := fun j : Fin N => M.mul c (Rw k j)
  let q := fun i j : Fin N => M.mul (t j) (Rw i k)
  refine hprefix.step_of_ne_zero hu hu1 k.isLt v _ (dec (M.lit (-1))) (dec c)
    (fun j => dec (t j)) (fun i j => dec (q i j)) hvzero hvdiag hvrel hp ?_ ?_ ?_ ?_ ?_
  · apply relErr_of_abs_sub_le hu
    simpa only [Rat.cast_neg, Rat.cast_one, abs_neg, abs_one, mul_one] using hM.lit (-1)
  · apply relErr_of_abs_sub_le hu
    simpa only [hS] using hM.div (M.lit (-1)) (Rw k k) (by simpa only [hS] using hp)
  · intro j
    apply relErr_of_abs_sub_le hu
    simpa only [hS] using hM.mul c (Rw k j)
  · intro i j
    simpa only [hS, mul_comm] using relErr_of_abs_sub_le hu (hM.mul (t j) (Rw i k))
  · intro i j
    apply relErr_of_abs_sub_le hu
    simpa only [hS, schurValues, rankOneValues, c, t, q] using hM.add (Rw i j) (q i j)

/-- The actual zero-safe step advances rounded reconstruction. The sole local zero-pivot
compatibility condition is supplied by an active-column pivot selector in the full algorithm. -/
theorem stepSpec_rounding {M : Machine K} {dec : K → ℝ} {u : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u < 1) (hone : dec (M.lit 1) = 1)
    (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N)
    {rs ls us rs' ls' us' : List K} {τ : Tape K}
    (hpost : (stepSpec M dec).post [N, k.val] τ [rs, ls, us] [rs', ls', us'])
    (hprefix : IsLURoundingPrefix u k.val A (decodeMatrix dec N N rs)
      (decodeMatrix dec N N ls) (decodeMatrix dec N N us))
    (hL : ∀ i : Fin N, i < k → decodeMatrix dec N N ls i k = 0)
    (hU : ∀ j : Fin N, j < k → decodeMatrix dec N N us k j = 0)
    (hcol : decodeMatrix dec N N rs k k = 0 →
      ∀ i : Fin N, k ≤ i → decodeMatrix dec N N rs i k = 0) :
    IsLURoundingPrefix u (k.val + 1) A (decodeMatrix dec N N rs')
      (decodeMatrix dec N N ls') (decodeMatrix dec N N us') := by
  obtain ⟨hcolumn, hschur⟩ := hpost
  obtain ⟨hLower, hUpper, hvzero, hvdiag, hvrel⟩ :=
    materializeColumnSpec_relative hM hu hone k hcolumn hL hU
  rw [hLower, hUpper]
  let Rw := fun i j => vec rs (j * N + i)
  let v := fun i : Fin N => relativeLowerColumn M dec Rw k.val i.val
  have hS : decodeMatrix dec N N rs = fun i j : Fin N => dec (Rw i j) := by
    ext i j
    exact decodeMatrix_apply dec N N rs i j
  have hbranch : (dec (vec rs (k.val * N + k.val)) = 0 → rs' = rs) ∧
      (dec (vec rs (k.val * N + k.val)) ≠ 0 → rs' = (EntryCodec.scalar K).packMatrix N N
        (schurValues M Rw k.val)) := hschur
  by_cases hp : decodeMatrix dec N N rs k k = 0
  · rw [hbranch.1 (by simpa only [decodeMatrix_apply] using hp)]
    exact hprefix.step_of_eq_zero hu k.isLt v hvzero hvdiag hvrel hp (hcol hp)
  · rw [hbranch.2 (by simpa only [decodeMatrix_apply] using hp), decodeMatrix,
      EntryCodec.matrix_packMatrix]
    exact schurValues_rounding hM hu hu1 hprefix Rw hS v hvzero hvdiag hvrel hp

/-- Future factor columns and rows remain their decoded initialization zeros after the
actual materialization, which changes only the current column and row suffixes. -/
theorem materializeColumnSpec_future {M : Machine K} {dec : K → ℝ} (k : Fin N)
    {rs ls us ls' us' : List K} {τ : Tape K}
    (hpost : (materializeColumnSpec M dec).post [N, k.val] τ [rs, ls, us] [ls', us'])
    (hL : ∀ i j : Fin N, k.val ≤ j.val → decodeMatrix dec N N ls i j = 0)
    (hU : ∀ i j : Fin N, k.val ≤ i.val → decodeMatrix dec N N us i j = 0) :
    (∀ i j : Fin N, k.val + 1 ≤ j.val → decodeMatrix dec N N ls' i j = 0) ∧
      (∀ i j : Fin N, k.val + 1 ≤ i.val → decodeMatrix dec N N us' i j = 0) := by
  obtain ⟨zeroPivot, -, hls, hus⟩ := hpost
  constructor
  · intro i j hj
    rw [hls, decodeMatrix, EntryCodec.matrix_packMatrix]
    change dec (columnLowerValues M zeroPivot (fun i j => vec rs (j * N + i))
      (fun i j => vec ls (j * N + i)) k.val i.val j.val) = 0
    have hcond : ¬(j.val = k.val ∧ k.val ≤ i.val) := by omega
    rw [columnLowerValues, if_neg hcond]
    simpa only [decodeMatrix_apply] using hL i j (by omega)
  · intro i j hi
    rw [hus, decodeMatrix, EntryCodec.matrix_packMatrix]
    change dec (columnUpperValues (fun i j => vec rs (j * N + i))
      (fun i j => vec us (j * N + i)) k.val i.val j.val) = 0
    have hcond : ¬(i.val = k.val ∧ k.val ≤ j.val) := by omega
    rw [columnUpperValues, if_neg hcond]
    simpa only [decodeMatrix_apply] using hU i j (by omega)

/-- Pivot quality bounds the newly committed actual lower column while preserving the
bounds on earlier columns. Only roundoff and the actual selected residual column are used. -/
theorem abs_decodeMatrix_le_of_materializeColumnSpec {M : Machine K} {dec : K → ℝ} {u quality : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hone : dec (M.lit 1) = 1)
    (hquality : 0 < quality) (hquality₁ : quality ≤ 1) (k : Fin N)
    {rs ls us ls' us' : List K} {τ : Tape K}
    (hpost : (materializeColumnSpec M dec).post [N, k.val] τ [rs, ls, us] [ls', us'])
    (hL : ∀ i : Fin N, i < k → decodeMatrix dec N N ls i k = 0)
    (hbound : ∀ i j : Fin N, j.val < k.val →
      |decodeMatrix dec N N ls i j| ≤ (1 + u) / quality)
    (hchoice : ∀ i : Fin N, k ≤ i → quality * |decodeMatrix dec N N rs i k| ≤
      |decodeMatrix dec N N rs k k|) :
    ∀ i j : Fin N, j.val < k.val + 1 →
      |decodeMatrix dec N N ls' i j| ≤ (1 + u) / quality := by
  obtain ⟨zeroPivot, hz, hls, -⟩ := hpost
  have hzero : dec (M.lit 0) = 0 := by
    have hh := hM.lit 0
    norm_num at hh
    exact hh
  have hLt : ∀ i < k.val, dec (vec ls (k.val * N + i)) = 0 := by
    intro i hi
    simpa only [decodeMatrix_apply] using hL ⟨i, hi.trans k.isLt⟩ hi
  intro i j hj
  rw [hls, decodeMatrix, EntryCodec.matrix_packMatrix]
  change |dec (columnLowerValues M zeroPivot (fun i j => vec rs (j * N + i))
    (fun i j => vec ls (j * N + i)) k.val i.val j.val)| ≤ _
  rw [dec_columnLowerValues_eq hzero hone zeroPivot _ _ k.val i.val j.val hz hLt]
  by_cases he : j = k
  · subst j
    rw [if_pos rfl]
    exact abs_relativeLowerColumn_le hM hu hquality hquality₁ _ k.val i.val
      (fun hi => by simpa only [decodeMatrix_apply] using hchoice i hi)
  · rw [if_neg (fun hh => he (Fin.ext hh))]
    simpa only [decodeMatrix_apply] using hbound i j (by have hn := Fin.val_ne_of_ne he; omega)

end NLAlib.LU
