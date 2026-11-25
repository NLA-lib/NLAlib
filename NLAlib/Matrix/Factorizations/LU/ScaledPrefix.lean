/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledChoice
public import NLAlib.Matrix.Factorizations.LU.PivotedPrefix
public import NLAlib.Matrix.Factorizations.LUScaledPivoting

/-!
# Stored prefixes for fixed-scale LU

The residual, canonical factor prefixes and actual row log share one permutation. Stored
scales decode to the original row norms transported by that permutation. Earlier pivots
satisfy the existing weighted-prefix predicate, without an unweighted multiplier claim.

## Main results

* `NLAlib.LU.IsScaledFactorPrefix.update`: commit the actual stored pivot and transported scales.
* `NLAlib.LU.IsScaledFactorPrefix.read_outputs`: actual factors and log at completion.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} {N : ℕ}

/-- Stored Gaussian/factor prefixes, actual committed log words, and original row scales.
Unwritten history choices are mathematical active positions and are never read prematurely. -/
def IsScaledFactorPrefix (dec : K → ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (k : ℕ) (R L U S H : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ p : Fin N → Fin N, (∀ i : Fin N, i ≤ p i) ∧
    IsFactorPrefix dec (A.submatrix (luPivotPermutation p k) id) k R L U s ∧
    (∀ i : Fin N, i.val < k → ∃ w, s.get H.1 (H.2 + i.val) = some w ∧
      dec w = (p i).val) ∧
    (∀ i : Fin N, ∃ w, s.get S.1 (S.2 + i.val) = some w ∧
      dec w = ‖A (luPivotPermutation p k i)‖) ∧
    HasScaledPivotPrefix (A.submatrix (luPivotPermutation p k) id) k

/-- The actual row log determines the source row permutation and both canonical factors.
The completed weighted-pivot property is recorded without an unweighted multiplier bound. -/
def factorScaledSpec [Inhabited K] (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls, us, hs) ensures
    ∃ p : Fin n → Fin n,
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) ∧ (∀ i : Fin n, i ≤ p i) ∧
      decodeMatrix dec n n ls =
        luLower ((decodeMatrix dec n n as).submatrix (luPivotPermutation p n) id) ∧
      decodeMatrix dec n n us =
        luUpper ((decodeMatrix dec n n as).submatrix (luPivotPermutation p n) id) ∧
      IsLU ((decodeMatrix dec n n as).submatrix (luPivotPermutation p n) id)
        (decodeMatrix dec n n ls) (decodeMatrix dec n n us) ∧
      HasScaledPivotPrefix
        ((decodeMatrix dec n n as).submatrix (luPivotPermutation p n) id) n

/-- Identity choices, zero factor prefixes and the actual initialized row scales establish
stage zero. No output history word is read in this theorem. -/
theorem IsScaledFactorPrefix.initial [Inhabited K] {dec : K → ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {R L U S H : ℕ × ℕ} {s : Store K} {ss : List K}
    (h : IsFactorPrefix dec A 0 R L U s)
    (hs : s.readBlock S.1 S.2 N = some ss)
    (hd : ∀ i : Fin N, dec (vec ss i.val) = ‖A i‖) :
    IsScaledFactorPrefix dec A 0 R L U S H s := by
  refine ⟨id, fun _ => le_rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [luPivotPermutation_zero, Equiv.coe_refl, Matrix.submatrix_id_id] using h
  · intro i hi
    exact (Nat.not_lt_zero i.val hi).elim
  · intro i
    exact ⟨vec ss i.val, Store.get_of_readBlock hs i.isLt default,
      by simpa only [luPivotPermutation_zero, Equiv.refl_apply] using hd i⟩
  · intro j i hj _
    exact (Nat.not_lt_zero j.val hj).elim

/-- The actual original-scale cells supply a contiguous initialized scale block. This readback
uses the existing stored-vector interface, including a vacuous empty scale vector. -/
theorem read_scaledPrefix_scales [Inhabited K] {dec : K → ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {p : Fin N → Fin N} {k : ℕ}
    {S : ℕ × ℕ} {s : Store K}
    (h : ∀ i : Fin N, ∃ w, s.get S.1 (S.2 + i.val) = some w ∧
      dec w = ‖A (luPivotPermutation p k i)‖) :
    ∃ ss : List K, s.readBlock S.1 S.2 N = some ss ∧
      ∀ i : Fin N, dec (vec ss i.val) = ‖A (luPivotPermutation p k i)‖ := by
  classical
  let f : ℕ → K := fun i => if hi : i < N then (h ⟨i, hi⟩).choose else default
  have hf : s.HoldsVec S.1 S.2 N f := by
    intro i hi
    simpa only [f, dif_pos hi] using (h ⟨i, hi⟩).choose_spec.1
  refine ⟨(List.range N).map f, Store.holdsVec_iff_readBlock.mp hf, ?_⟩
  intro i
  simp only [vec, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range i.isLt, Option.map_some, Option.getD_some]
  simpa only [f, dif_pos i.isLt, Fin.eta] using (h i).choose_spec.2

/-- Stored original scales provide active zero compatibility, including original zero rows
and singular residuals. This is the exact precondition consumed by the scaled selector. -/
theorem scaledChoice_pre_of_prefix [Inhabited K] {dec : K → ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {p : Fin N → Fin N} (k : Fin N)
    {rs ss : List K} {bound : ℕ} {τ : Tape K} (hN : N ≤ bound)
    (hres : ∀ i j : Fin N, decodeMatrix dec N N rs i j =
      gaussState (A.submatrix (luPivotPermutation p k.val) id) k.val i j)
    (hscale : ∀ i : Fin N, dec (vec ss i.val) = ‖A (luPivotPermutation p k.val i)‖) :
    (scaledChoiceSpec dec bound).pre [N, k.val] τ [rs, ss] := by
  refine ⟨⟨k.isLt, hN⟩, ?_⟩
  intro i _
  refine ⟨by rw [hscale]; exact norm_nonneg _, ?_⟩
  intro hz
  have hz' : ‖(A.submatrix (luPivotPermutation p k.val) id) i‖ = 0 := by
    change ‖A (luPivotPermutation p k.val i)‖ = 0
    exact (hscale i).symm.trans hz
  have he := gaussState_apply_eq_zero_of_norm_row_eq_zero
    (A.submatrix (luPivotPermutation p k.val) id) i hz' k.val k
  rw [← hres i k] at he
  simpa only [decodeMatrix_apply] using he

/-- Commit the actual row word and exchanged original scales. Canonical prefix advancement
is supplied by the shared actual total step; earlier weighted pivots transport covariantly. -/
theorem IsScaledFactorPrefix.update {dec : K → ℝ} (A : Matrix (Fin N) (Fin N) ℝ)
    (p : Fin N → Fin N) (k r : Fin N) (hkr : k ≤ r)
    (hp : ∀ i : Fin N, i ≤ p i) {R L U S H : ℕ × ℕ} {s : Store K} {w : K}
    (hf : IsFactorPrefix dec
      (A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1)) id)
      (k.val + 1) R L U s)
    (hH : ∀ i : Fin N, i.val < k.val → ∃ v,
      s.get H.1 (H.2 + i.val) = some v ∧ dec v = (p i).val)
    (hw : s.get H.1 (H.2 + k.val) = some w) (hd : dec w = r.val)
    (hS : ∀ i : Fin N, ∃ v, s.get S.1 (S.2 + i.val) = some v ∧
      dec v = ‖A (luPivotPermutation p k.val (Equiv.swap k r i))‖)
    (hweighted : HasScaledPivotPrefix (A.submatrix (luPivotPermutation p k.val) id) k.val)
    (hselected : ∀ i : Fin N, k ≤ i →
      ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) k i k‖ /
          ‖A (luPivotPermutation p k.val i)‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) k r k‖ /
          ‖A (luPivotPermutation p k.val r)‖) :
    IsScaledFactorPrefix dec A (k.val + 1) R L U S H s := by
  refine ⟨Function.update p k r, ?_, hf,
    Store.indexPrefix_succ_of_kept k r hH hw hd, ?_,
    HasScaledPivotPrefix.update A p k r hkr hweighted hselected⟩
  · intro i
    by_cases hi : i = k
    · subst i
      simpa only [Function.update_self] using hkr
    · simpa only [Function.update_of_ne hi] using hp i
  · intro i
    obtain ⟨v, hv, hd⟩ := hS i
    refine ⟨v, hv, ?_⟩
    simpa only [luPivotPermutation_update, Equiv.trans_apply] using hd

/-- Completion supplies actual readable factors and history. The existing weighted-prefix
factorization theorem handles zero scales and singular matrices, without nonsingularity. -/
theorem IsScaledFactorPrefix.read_outputs [Inhabited K] {dec : K → ℝ} {as : List K}
    {R L U S H : ℕ × ℕ} {s : Store K}
    (h : IsScaledFactorPrefix dec (decodeMatrix dec N N as) N R L U S H s) (τ : Tape K) :
    ∃ ls us hs : List K,
      s.readBlock L.1 L.2 (N * N) = some ls ∧
      s.readBlock U.1 U.2 (N * N) = some us ∧
      s.readBlock H.1 H.2 N = some hs ∧
      (factorScaledSpec dec).post [N] τ [as] [ls, us, hs] := by
  obtain ⟨p, hp, hf, hH, hS, hweighted⟩ := h
  obtain ⟨ls, us, hls, hus, hlo, hup⟩ := hf.read_factors
  obtain ⟨hs, hhs, hhd⟩ := Store.indexPrefix_readBlock (fun i => hH i i.isLt)
  refine ⟨ls, us, hs, hls, hus, hhs, p, hhd, hp, hlo, hup, ?_, hweighted⟩
  rw [hlo, hup]
  exact hweighted.isLU

end NLAlib.LU
