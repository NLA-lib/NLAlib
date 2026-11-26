/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RoundedPivotedStep
public import NLAlib.Matrix.Factorizations.LU.RoundedSpec

/-!
# Actual histories of rounded pivoted LU

The stored rounded factor prefix and the two actual current-position logs identify the input
permutations. Fixed-column policies retain a reusable single column-index cell. Every stored
claim concerns actual words; no execution witness or successful-run condition is included.

## Main results

* `NLAlib.LU.IsRoundedPivotedPrefix.update`: append actual row and column reports.
* `NLAlib.LU.IsRoundedPivotedPrefix.read_outputs`: read the final rounded factorization.
-/

@[expose] public section

namespace NLAlib.LU

open Ops Computation

variable {K : Type} [Inhabited K] {N : ℕ}

/-- Rounded factors and actual committed logs for the permuted original input. -/
def IsRoundedPivotedPrefix (dec : K → ℝ) (u : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (quality : ℝ) (fixedColumns : Bool) (k : ℕ) (R L U H Q : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ p q : Fin N → Fin N,
    (∀ i : Fin N, i ≤ p i) ∧ (∀ i : Fin N, i ≤ q i) ∧
    (fixedColumns = true → ∀ i : Fin N, q i = i) ∧
    IsRoundedFactorPrefix dec u quality
      (A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)) k R L U s ∧
    (∀ i : Fin N, i.val < k → ∃ w, s.get H.1 (H.2 + i.val) = some w ∧ dec w = (p i).val) ∧
    (fixedColumns = false → ∀ i : Fin N, i.val < k →
      ∃ w, s.get Q.1 (Q.2 + i.val) = some w ∧ dec w = (q i).val) ∧
    (fixedColumns = true → 0 < k →
      ∃ w, s.get Q.1 Q.2 = some w ∧ dec w = (k - 1 : ℕ))

/-- The initial stored factor prefix admits identity choices and empty histories. No history
word is read until a real pivot step has recorded it. -/
theorem IsRoundedPivotedPrefix.initial {dec : K → ℝ} {u : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {quality : ℝ} {fixedColumns : Bool} {R L U H Q : ℕ × ℕ} {s : Store K}
    (h : IsRoundedFactorPrefix dec u quality A 0 R L U s) :
    IsRoundedPivotedPrefix dec u A quality fixedColumns 0 R L U H Q s := by
  refine ⟨id, id, fun _ => le_rfl, fun _ => le_rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [luPivotPermutation_zero, Equiv.coe_refl, Matrix.submatrix_id_id] using h
  · intro i hi
    exact (Nat.not_lt_zero i.val hi).elim
  · intro _ i hi
    exact (Nat.not_lt_zero i.val hi).elim
  · intro _ hk
    exact (Nat.lt_irrefl 0 hk).elim
/-- Append the actual reported row and column words to a transported factor prefix. A fixed
column policy overwrites its one reusable cell and keeps the mathematical column choices
identically fixed; an independent policy appends to its complete stored column history. -/
theorem IsRoundedPivotedPrefix.update {dec : K → ℝ} {u : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {quality : ℝ} {fixedColumns : Bool} {R L U H Q : ℕ × ℕ} {s : Store K}
    (p q : Fin N → Fin N) (k r c : Fin N)
    (hp : ∀ i : Fin N, i ≤ p i) (hq : ∀ i : Fin N, i ≤ q i)
    (hqfixed : fixedColumns = true → ∀ i : Fin N, q i = i)
    (hkr : k ≤ r) (hkc : k ≤ c) (hfixed : fixedColumns = true → c = k)
    (hF : IsRoundedFactorPrefix dec u quality
      (A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
        (luPivotPermutation (Function.update q k c) (k.val + 1))) (k.val + 1) R L U s)
    (hH : ∀ i : Fin N, i.val < k.val → ∃ w,
      s.get H.1 (H.2 + i.val) = some w ∧ dec w = (p i).val)
    (hQ : fixedColumns = false → ∀ i : Fin N, i.val < k.val → ∃ w,
      s.get Q.1 (Q.2 + i.val) = some w ∧ dec w = (q i).val)
    {rw cw : K} (hrw : s.get H.1 (H.2 + k.val) = some rw) (hdr : dec rw = r.val)
    (hcw : s.get Q.1 (Q.2 + (if fixedColumns then 0 else k.val)) = some cw)
    (hdc : dec cw = c.val)
 :
    IsRoundedPivotedPrefix dec u A quality fixedColumns (k.val + 1) R L U H Q s := by
  refine ⟨Function.update p k r, Function.update q k c, ?_, ?_, ?_, hF, ?_, ?_, ?_⟩
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

/-- A completed actual history and rounded factor prefix give triangular factors,
all multiplier bounds and the conditional componentwise numerical error for arbitrary inputs. -/
theorem IsRoundedPivotedPrefix.read_outputs {dec : K → ℝ} {as : List K}
    {u quality : ℝ} {fixedColumns : Bool} {R L U H Q : ℕ × ℕ} {s : Store K}
    (hu : 0 ≤ u)
    (h : IsRoundedPivotedPrefix dec u (decodeMatrix dec N N as) quality fixedColumns N R L U H Q s)
    (bound : ℕ) (τ : Tape K) :
    ∃ ls us hs qs : List K,
      s.readBlock L.1 L.2 (N * N) = some ls ∧
      s.readBlock U.1 U.2 (N * N) = some us ∧
      s.readBlock H.1 H.2 N = some hs ∧
      s.readBlock Q.1 Q.2 (if fixedColumns then N - (N - 1) else N) = some qs ∧
      (Rounded.factorPivotedSpec dec u quality fixedColumns bound).post [N] τ
        [as] [ls, us, hs, qs] := by
  obtain ⟨p, q, hp, hq, hfixed, hf, hH, hQ, hlast⟩ := h
  obtain ⟨rs, ls, us, hR, hls, hus, hnum, hshape, -, -, hbound⟩ := hf
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
  obtain ⟨hLower, hUpper⟩ := hshape.complete
  exact ⟨ls, us, hs, qs, hls, hus, hhs, hqs, p, q, hhd, hqd, hlast, hp, hq, hfixed,
    hLower, hUpper, fun hu1 => (hnum hu1).isLUErr hu hu1, fun i j => hbound i j j.isLt⟩

end NLAlib.LU
