/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Prefix
public import NLAlib.Matrix.Factorizations.LU.PivotedSpec
public import NLAlib.Ops.Logic.IndexLog
public import NLAlib.Matrix.Factorizations.LUQualityPivoting

/-!
# Stored prefixes with independent pivot logs

The input at a stage is permuted by the two recorded sequences of current-position swaps.
The residual and initialized factor prefixes use the same stored invariant as unpivoted LU.
Quantitative column quality is recorded only for policies that supply a positive uniform
fraction. Fixed-scale pivoting uses its separate weighted invariant.

## Main definitions

* `NLAlib.LU.IsPivotedPrefix`: actual factors, both stored logs and earlier column quality.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} {N : ℕ}

/-- Stored canonical factor prefixes and both actual decoded pivot histories. The quality
fraction concerns only previously committed pivots; it is not a nonbreakdown assumption.
Unwritten choices are initialized mathematically to active positions, not read from storage. -/
def IsPivotedPrefix (dec : K → ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (quality : ℝ) (fixedColumns : Bool) (k : ℕ) (R L U H Q : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ p q : Fin N → Fin N,
    (∀ i : Fin N, i ≤ p i) ∧ (∀ i : Fin N, i ≤ q i) ∧
    (fixedColumns = true → ∀ i : Fin N, q i = i) ∧
    IsFactorPrefix dec
      (A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)) k R L U s ∧
    (∀ i : Fin N, i.val < k → ∃ w, s.get H.1 (H.2 + i.val) = some w ∧ dec w = (p i).val) ∧
    (fixedColumns = false → ∀ i : Fin N, i.val < k →
      ∃ w, s.get Q.1 (Q.2 + i.val) = some w ∧ dec w = (q i).val) ∧
    (fixedColumns = true → 0 < k →
      ∃ w, s.get Q.1 Q.2 = some w ∧ dec w = (k - 1 : ℕ)) ∧
    ∀ t i : Fin N, t.val < k → t ≤ i →
      quality * ‖gaussState
        (A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)) t i t‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)) t t t‖

/-- Active exchanges transport all stored factor-prefix equalities at the decoded matrix
level. Future columns and rows remain zero, while committed entries use canonical covariance. -/
theorem factorPrefix_submatrix {A F G : Matrix (Fin N) (Fin N) ℝ}
    (k : ℕ) (ρ κ : Equiv.Perm (Fin N))
    (hρ : ∀ i : Fin N, i.val < k → ρ i = i)
    (hκ : ∀ j : Fin N, j.val < k → κ j = j)
    (hF : ∀ i j : Fin N, F i j = if j.val < k then luLower A i j else 0)
    (hG : ∀ i j : Fin N, G i j = if i.val < k then luUpper A i j else 0) :
    (∀ i j : Fin N,
      F (ρ i) j = if j.val < k then luLower (A.submatrix ρ κ) i j else 0) ∧
    (∀ i j : Fin N,
      G i (κ j) = if i.val < k then luUpper (A.submatrix ρ κ) i j else 0) := by
  constructor
  · intro i j
    rw [hF]
    by_cases hj : j.val < k
    · rw [if_pos hj, if_pos hj]
      exact (luLower_submatrix_left_right_apply A ρ κ k hρ hκ i j hj).symm
    · simp only [if_neg hj]
  · intro i j
    rw [hG]
    by_cases hi : i.val < k
    · rw [if_pos hi, if_pos hi]
      exact (luUpper_submatrix_left_right_apply A ρ κ k hρ hκ i j hi).symm
    · simp only [if_neg hi]

/-- Actual swapped output blocks reconstruct the transported stored prefix. The premise
relates each new decoded matrix to its old words; it never assumes the selector or factor
step executes. This is the bridge from word-level row and column swaps to the loop invariant. -/
theorem IsFactorPrefix.of_submatrix_reads [Inhabited K] {dec : K → ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {k : ℕ} {R L U : ℕ × ℕ} {s : Store K}
    {rs ls us rs' ls' us' : List K} (ρ κ : Equiv.Perm (Fin N))
    (hρ : ∀ i : Fin N, i.val < k → ρ i = i)
    (hκ : ∀ j : Fin N, j.val < k → κ j = j)
    (hr : ∀ i j : Fin N, decodeMatrix dec N N rs i j = gaussState A k i j)
    (hl : ∀ i j : Fin N,
      decodeMatrix dec N N ls i j = if j.val < k then luLower A i j else 0)
    (hu : ∀ i j : Fin N,
      decodeMatrix dec N N us i j = if i.val < k then luUpper A i j else 0)
    (hR : s.readBlock R.1 R.2 (N * N) = some rs')
    (hL : s.readBlock L.1 L.2 (N * N) = some ls')
    (hU : s.readBlock U.1 U.2 (N * N) = some us')
    (hres : decodeMatrix dec N N rs' = (decodeMatrix dec N N rs).submatrix ρ κ)
    (hlo : decodeMatrix dec N N ls' = (decodeMatrix dec N N ls).submatrix ρ id)
    (hup : decodeMatrix dec N N us' = (decodeMatrix dec N N us).submatrix id κ) :
    IsFactorPrefix dec (A.submatrix ρ κ) k R L U s := by
  have hfg := factorPrefix_submatrix k ρ κ hρ hκ hl hu
  apply IsFactorPrefix.of_reads hR hL hU
  · intro i j
    rw [hres, gaussState_submatrix_left_right A ρ κ k hρ hκ]
    exact hr (ρ i) (κ j)
  · intro i j
    rw [hlo]
    exact hfg.1 i j
  · intro i j
    rw [hup]
    exact hfg.2 i j

/-- The initial stored factor prefix admits identity choices and empty histories. No history
word is read until a real pivot step has recorded it. -/
theorem IsPivotedPrefix.initial {dec : K → ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {quality : ℝ} {fixedColumns : Bool} {R L U H Q : ℕ × ℕ} {s : Store K}
    (h : IsFactorPrefix dec A 0 R L U s) :
    IsPivotedPrefix dec A quality fixedColumns 0 R L U H Q s := by
  refine ⟨id, id, fun _ => le_rfl, fun _ => le_rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [luPivotPermutation_zero, Equiv.coe_refl, Matrix.submatrix_id_id] using h
  · intro i hi
    exact (Nat.not_lt_zero i.val hi).elim
  · intro _ i hi
    exact (Nat.not_lt_zero i.val hi).elim
  · intro _ hk
    exact (Nat.lt_irrefl 0 hk).elim
  · intro t i ht
    exact (Nat.not_lt_zero t.val ht).elim

/-- Append the actual reported row and column words to a transported factor prefix. A fixed
column policy overwrites its one reusable cell and keeps the mathematical column choices
identically fixed; an independent policy appends to its complete stored column history. -/
theorem IsPivotedPrefix.update {dec : K → ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {quality : ℝ} {fixedColumns : Bool} {R L U H Q : ℕ × ℕ} {s : Store K}
    (p q : Fin N → Fin N) (k r c : Fin N)
    (hp : ∀ i : Fin N, i ≤ p i) (hq : ∀ i : Fin N, i ≤ q i)
    (hqfixed : fixedColumns = true → ∀ i : Fin N, q i = i)
    (hkr : k ≤ r) (hkc : k ≤ c) (hfixed : fixedColumns = true → c = k)
    (hF : IsFactorPrefix dec
      (A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
        (luPivotPermutation (Function.update q k c) (k.val + 1))) (k.val + 1) R L U s)
    (hH : ∀ i : Fin N, i.val < k.val → ∃ w,
      s.get H.1 (H.2 + i.val) = some w ∧ dec w = (p i).val)
    (hQ : fixedColumns = false → ∀ i : Fin N, i.val < k.val → ∃ w,
      s.get Q.1 (Q.2 + i.val) = some w ∧ dec w = (q i).val)
    {rw cw : K} (hrw : s.get H.1 (H.2 + k.val) = some rw) (hdr : dec rw = r.val)
    (hcw : s.get Q.1 (Q.2 + (if fixedColumns then 0 else k.val)) = some cw)
    (hdc : dec cw = c.val)
    (hm : ∀ t i : Fin N, t.val < k.val + 1 → t ≤ i → quality *
      ‖gaussState (A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
        (luPivotPermutation (Function.update q k c) (k.val + 1))) t i t‖ ≤
      ‖gaussState (A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
        (luPivotPermutation (Function.update q k c) (k.val + 1))) t t t‖) :
    IsPivotedPrefix dec A quality fixedColumns (k.val + 1) R L U H Q s := by
  refine ⟨Function.update p k r, Function.update q k c, ?_, ?_, ?_, hF, ?_, ?_, ?_, hm⟩
  · intro i
    by_cases hi : i = k
    · simpa only [hi, Function.update_self] using hkr
    · simpa only [Function.update_of_ne hi] using hp i
  · intro i
    by_cases hi : i = k
    · simpa only [hi, Function.update_self] using hkc
    · simpa only [Function.update_of_ne hi] using hq i
  · intro hf i
    by_cases hi : i = k
    · simpa only [hi, Function.update_self] using hfixed hf
    · simpa only [Function.update_of_ne hi] using hqfixed hf i
  · exact Store.indexPrefix_succ_of_kept k r hH hrw hdr
  · intro hf
    apply Store.indexPrefix_succ_of_kept k c (hQ hf) _ hdc
    simpa only [hf, Bool.false_eq_true, ite_false] using hcw
  · intro hf _
    refine ⟨cw, ?_, ?_⟩
    · simpa only [hf, ite_true, Nat.add_zero] using hcw
    · simpa only [hfixed hf, Nat.add_sub_cancel] using hdc

/-- A completed prefix supplies actual readable factors and both actual log blocks, together
with exact reconstruction and the policy's multiplier bound. Singular matrices are included:
positive column quality forces every skipped pivot column to be zero below its pivot. -/
theorem IsPivotedPrefix.read_outputs [Inhabited K] {dec : K → ℝ} {as : List K}
    {quality : ℝ} {fixedColumns : Bool} {R L U H Q : ℕ × ℕ} {s : Store K}
    (hα : 0 < quality) (hα₁ : quality ≤ 1)
    (h : IsPivotedPrefix dec (decodeMatrix dec N N as) quality fixedColumns N R L U H Q s)
    (τ : Tape K) :
    ∃ ls us hs qs : List K,
      s.readBlock L.1 L.2 (N * N) = some ls ∧
      s.readBlock U.1 U.2 (N * N) = some us ∧
      s.readBlock H.1 H.2 N = some hs ∧
      s.readBlock Q.1 Q.2 (if fixedColumns then N - (N - 1) else N) = some qs ∧
      (factorPivotedSpec dec quality fixedColumns).post [N] τ [as] [ls, us, hs, qs] := by
  obtain ⟨p, q, hp, hq, hfixed, hf, hH, hQ, hlast, hmax⟩ := h
  obtain ⟨ls, us, hls, hus, hlo, hup⟩ := hf.read_factors
  obtain ⟨hs, hhs, hhd⟩ := Store.indexPrefix_readBlock (fun i => hH i i.isLt)
  have hqread : ∃ qs : List K,
      s.readBlock Q.1 Q.2 (if fixedColumns then N - (N - 1) else N) = some qs ∧
      (fixedColumns = false → ∀ i : Fin N, dec (vec qs i.val) = (q i).val) ∧
      (fixedColumns = true → 0 < N → dec (vec qs 0) = (N - 1 : ℕ)) := by
    cases fixedColumns with
    | false =>
      obtain ⟨qs, hqs, hqd⟩ := Store.indexPrefix_readBlock (fun i => hQ rfl i i.isLt)
      exact ⟨qs, hqs, fun _ => hqd, fun h => Bool.noConfusion h⟩
    | true =>
      by_cases hN : 0 < N
      · obtain ⟨w, hw, hd⟩ := hlast rfl hN
        have hlen : N - (N - 1) = 1 := by omega
        refine ⟨[w], ?_, fun h => Bool.noConfusion h, fun _ _ => ?_⟩
        · simpa only [hlen, ite_true] using Store.readBlock_one_of_get hw
        · simpa [vec] using hd
      · have he : N = 0 := by omega
        exact ⟨[], by simp only [he, Nat.sub_self, Store.readBlock_zero, ite_true],
          fun h => Bool.noConfusion h, fun _ hn => (hN hn).elim⟩
  obtain ⟨qs, hqs, hqd, hlast⟩ := hqread
  refine ⟨ls, us, hs, qs, hls, hus, hhs, hqs, p, q, hhd, hqd, hlast, hp, hq, hfixed,
    hlo, hup, ?_, ?_⟩
  · rw [hlo, hup]
    exact isLU_luLower_luUpper_of_forall_mul_norm_le hα
      (fun t i hti => hmax t i t.isLt hti)
  · intro i j
    rw [hlo, ← Real.norm_eq_abs]
    exact norm_luLower_apply_le_inv hα hα₁
      (fun t a hta => hmax t a t.isLt hta) i j

end NLAlib.LU
