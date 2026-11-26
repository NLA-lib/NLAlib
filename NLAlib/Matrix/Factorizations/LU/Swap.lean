/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Strided
public import NLAlib.Ops.Catalog.Orth
public import NLAlib.Matrix.Factorizations.LU.PivotSaved

/-!
# Stored matrix permutations for pivoted factorizations

The bounded row and column exchanges retain every word exactly. Equal selected indices
execute no scalar operations. Both use the existing three-copy strided exchange, with one
scoped scalar temporary, rather than a matrix permutation primitive.

## Main results

* `NLAlib.LU.swapRows_meets`: actual word exchange of two bounded matrix rows.
* `NLAlib.LU.swapColumns_meets`: actual word exchange of two bounded matrix columns.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Exchange a pivot row with a selected later row; selecting the current row does nothing. -/
def swapRows : Routine Op Tst := routine% [n, k, r] (A : n * n) → (A) {
  ifPos (r - k) {
    run Examples.Strided.swapMatrixRows [n, n, k, r] (A)
  }
}

variable [Inhabited K]

/-- All output words are the original words with the two bounded rows exchanged. -/
def swapRowsSpec : Routine.Spec K :=
  spec% [n, k, r] (as) → (bs) requires k ≤ r ∧ r < n ensures
    bs.length = n * n ∧ ∀ i < n, ∀ j < n,
      vec bs (j * n + i) = vec as (j * n + Equiv.swap k r i)

private theorem vec_swappedRows (as : List K) {n i j k r : ℕ} (hi : i < n) (hj : j < n) :
    vec (Examples.Strided.swappedRows as n n k r) (j * n + i) =
      vec as (j * n + Equiv.swap k r i) := by
  have hn : 0 < n := Nat.zero_lt_of_lt hi
  have hq : j * n + i < n * n := Idx.add_lt_mul hj hi
  have hdiv : (j * n + i) / n = j := by
    rw [Nat.mul_comm j n, Nat.mul_add_div hn, Nat.div_eq_of_lt hi, Nat.add_zero]
  simp only [vec, List.getD_eq_getElem?_getD,
    Examples.Strided.getElem?_swappedRows as k r hq, Option.getD_some, hdiv,
    Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi, Equiv.swap_apply_def]
  rw [Nat.mul_comm n j]

/-- The actual row exchange is total under scalar copy contracts. No numerical arithmetic
or comparison accuracy assumption is needed, since the branch uses the supplied indices. -/
theorem swapRows_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (swapRows (Op := Op) (Tst := Tst)).Meets I (swapRowsSpec (K := K)) := by
  routine_intro [n, k, r] (A) reads (as)
  obtain ⟨hkr, hrn⟩ := hpre
  have hlen : as.length = n * n := Store.length_of_readBlock has
  refine writes_ifPos rfl ?_
  by_cases hlt : 0 < r - k
  · rw [if_pos hlt]
    call (Examples.Strided.swapMatrixRows_meets hI) [n, n, k, r] (A)
      (pre := ⟨by omega, hrn⟩) as m₁ hfr₁ hpos₁ (bs) hpost
    have he : bs = Examples.Strided.swappedRows as n n k r := hpost
    routine_exit
    rw [he]
    refine ⟨by simp [Examples.Strided.swappedRows], ?_⟩
    intro i hi j hj
    exact vec_swappedRows as hi hj
  · rw [if_neg hlt]
    have he : k = r := by omega
    exact ⟨rfl, [as], Mem.readBlocks_of_cons has rfl, hlen,
      fun i _ j _ => by simp only [he, Equiv.swap_self, Equiv.refl_apply]⟩

/-- The word row-exchange postcondition gives left reindexing of the actual decoded matrix. -/
theorem swapRowsSpec_decode {dec : K → ℝ} {n : ℕ} (k r : Fin n)
    {as bs : List K} {τ : Tape K}
    (h : (swapRowsSpec (K := K)).post [n, k.val, r.val] τ [as] [bs]) :
    decodeMatrix dec n n bs = (decodeMatrix dec n n as).submatrix (Equiv.swap k r) id := by
  ext i j
  rw [decodeMatrix_apply, Matrix.submatrix_apply, decodeMatrix_apply]
  congr 1
  rw [h.2 i.val i.isLt j.val j.isLt]
  simp only [Function.Injective.map_swap Fin.val_injective, id_eq]

/-- Exchange a pivot column with a selected later column; selecting it again does nothing. -/
def swapColumns : Routine Op Tst := routine% [n, k, r] (A : n * n) → (A) {
  ifPos (r - k) {
    run Examples.Strided.swapRows [n, 1] (A[k * n], A[r * n])
  }
}

/-- All output words are the original words with the two bounded columns exchanged. -/
def swapColumnsSpec : Routine.Spec K :=
  spec% [n, k, r] (as) → (bs) requires k ≤ r ∧ r < n ensures
    bs.length = n * n ∧ ∀ i < n, ∀ j < n,
      vec bs (j * n + i) = vec as (Equiv.swap k r j * n + i)

private theorem readBlock_swapped_columns {s s' : Store K} {b off n k r : ℕ}
    {as : List K} (hn : 0 < n)
    (hA : s.readBlock b off (n * n) = some as)
    (hfr : s.EqOff (Store.inBlock b (off + k * n) n ⊔
      Store.inBlock b (off + r * n) n) s')
    (hk : s'.readBlock b (off + k * n) n = some (pivotColumnWords as n r))
    (hr : s'.readBlock b (off + r * n) n = some (pivotColumnWords as n k)) :
    ∃ bs : List K, s'.readBlock b off (n * n) = some bs ∧ bs.length = n * n ∧
      ∀ i < n, ∀ j < n, vec bs (j * n + i) = vec as (Equiv.swap k r j * n + i) := by
  let bs := (List.range (n * n)).map fun q =>
    vec as (Equiv.swap k r (q / n) * n + q % n)
  have hg : ∀ q < n * n, s'.get b (off + q) = bs[q]? := by
    intro q hq
    have hi : q % n < n := Nat.mod_lt q hn
    have he : q / n * n + q % n = q := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod q n
    rw [List.getElem?_map, List.getElem?_range hq, Option.map_some]
    change s'.get b (off + q) = some (vec as (Equiv.swap k r (q / n) * n + q % n))
    by_cases hqk : q / n = k
    · have h := Store.get_of_readBlock hk hi default
      simp only [pivotColumnWords, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi, Option.map_some, Option.getD_some] at h
      simpa only [hqk, Equiv.swap_apply_left, vec, List.getD_eq_getElem?_getD,
        show off + q = off + k * n + q % n by
          have heK : k * n + q % n = q := by simpa only [hqk] using he
          omega] using h
    · by_cases hqr : q / n = r
      · have h := Store.get_of_readBlock hr hi default
        simp only [pivotColumnWords, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some] at h
        simpa only [hqr, Equiv.swap_apply_right, vec, List.getD_eq_getElem?_getD,
          show off + q = off + r * n + q % n by
            have heR : r * n + q % n = q := by simpa only [hqr] using he
            omega] using h
      · rw [Equiv.swap_apply_of_ne_of_ne hqk hqr, he, hfr.get_eq ?_]
        · exact Store.get_of_readBlock hA hq default
        · rintro (⟨_, hlo, hhi⟩ | ⟨_, hlo, hhi⟩)
          · exact hqk (Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega))
          · exact hqr (Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega))
  refine ⟨bs, Store.readBlock_eq_some_iff.mpr ⟨by simp [bs], hg⟩, by simp [bs], ?_⟩
  intro i hi j hj
  have hd : (j * n + i) / n = j := by
    rw [Nat.mul_comm j n, Nat.mul_add_div hn, Nat.div_eq_of_lt hi, Nat.add_zero]
  simp only [bs, vec, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Idx.add_lt_mul hj hi), Option.map_some, Option.getD_some, hd,
    Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi]

/-- Actual scalar copies exchange two columns exactly and retain every other word. -/
theorem swapColumns_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (swapColumns (Op := Op) (Tst := Tst)).Meets I (swapColumnsSpec (K := K)) := by
  routine_intro [n, k, r] (A) reads (as)
  obtain ⟨hkr, hrn⟩ := hpre
  have hkn : k < n := hkr.trans_lt hrn
  have hlen : as.length = n * n := Store.length_of_readBlock has
  have hk := read_pivotColumnWords has hkn
  have hr := read_pivotColumnWords has hrn
  refine writes_ifPos rfl ?_
  by_cases hlt : 0 < r - k
  · rw [if_pos hlt]
    call (Examples.Strided.swapRows_meets hI) [n, 1]
      ((A.1, A.2 + k * n), (A.1, A.2 + r * n)) (pre := Nat.zero_lt_one)
      as m₁ hfr₁ hpos₁ (ks, rs) hpost
    case' hcall => exact [pivotColumnWords as n k, pivotColumnWords as n r]
    case' hr => exact Mem.readViews_of_cons hk (Mem.readViews_of_cons hr rfl)
    case' hpre => exact Nat.zero_lt_one
    case' hroom =>
      exact ⟨Store.fits_of_readView hk (by change 0 < n * 1; omega),
        Store.fits_of_readView hr (by change 0 < n * 1; omega), trivial⟩
    case' hle =>
      change (Fp.inView A.1 (A.2 + k * n) ⟨1, some (n, 1)⟩ ⊔
        (Fp.inView A.1 (A.2 + r * n) ⟨1, some (n, 1)⟩ ⊔ ⊥)) ≤
          (Store.inBlock A.1 A.2 (n * n) ⊔ ⊥)
      simp only [Fp.inView_unitStride, sup_bot_eq]
      have hc (c : ℕ) (hc : c < n) : A.2 + c * n + n ≤ A.2 + n * n := by
        have hb := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hc)
        rw [Nat.succ_mul] at hb
        omega
      exact sup_le (Fp.inBlock_le_inBlock (by omega) (hc k hkn))
        (Fp.inBlock_le_inBlock (by omega) (hc r hrn))
    case' hsep =>
      have hd : Fp.Disj (Fp.inView A.1 (A.2 + k * n) ⟨1, some (n, 1)⟩)
          (Fp.inView A.1 (A.2 + r * n) ⟨1, some (n, 1)⟩) := by
        rw [Fp.inView_unitStride, Fp.inView_unitStride]
        apply Fp.disj_inBlock_of_le
        have hb := Nat.mul_le_mul_right n (show k + 1 ≤ r by omega)
        rw [Nat.succ_mul] at hb
        omega
      exact Routine.separatedAt_of_blocks rfl
        ⟨⟨fun b i h₁ h₂ => h₂.elim (hd b i h₁) False.elim, fun _ _ _ h => h, trivial⟩,
          fun _ _ _ h => h, trivial, fun _ _ h _ => h⟩
    obtain ⟨heK, heR⟩ : ks = pivotColumnWords as n r ∧ rs = pivotColumnWords as n k := hpost
    have hf : m.store.EqOff (Store.inBlock A.1 (A.2 + k * n) n ⊔
        Store.inBlock A.1 (A.2 + r * n) n) m₁.store := by
      simpa only [Fp.views, Fp.inView_unitStride, sup_bot_eq] using hfr₁
    rw [Store.readView_unitStride, heK] at hks
    rw [Store.readView_unitStride, heR] at hrs
    obtain ⟨bs, hbs, hblen, hwords⟩ := readBlock_swapped_columns
      (Nat.zero_lt_of_lt hrn) has hf hks hrs
    exact ⟨by omega, [bs], Mem.readBlocks_of_cons hbs rfl, hblen, hwords⟩
  · rw [if_neg hlt]
    have he : k = r := by omega
    exact ⟨rfl, [as], Mem.readBlocks_of_cons has rfl, hlen,
      fun i _ j _ => by simp only [he, Equiv.swap_self, Equiv.refl_apply]⟩

/-- The word column-exchange postcondition gives right reindexing of the decoded matrix. -/
theorem swapColumnsSpec_decode {dec : K → ℝ} {n : ℕ} (k r : Fin n)
    {as bs : List K} {τ : Tape K}
    (h : (swapColumnsSpec (K := K)).post [n, k.val, r.val] τ [as] [bs]) :
    decodeMatrix dec n n bs = (decodeMatrix dec n n as).submatrix id (Equiv.swap k r) := by
  ext i j
  rw [decodeMatrix_apply, Matrix.submatrix_apply, decodeMatrix_apply]
  congr 1
  rw [h.2 i.val i.isLt j.val j.isLt]
  simp only [Function.Injective.map_swap Fin.val_injective, id_eq]

end NLAlib.LU
