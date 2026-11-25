/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightPrefix
public import NLAlib.Matrix.Factorizations.CholeskyDiagonalPivoting
public import NLAlib.Matrix.Factorizations.LU.Swap
public import NLAlib.Matrix.Factorizations.Cholesky.SymmetricPivot

/-!
# Stored prefixes of diagonal-pivoted Cholesky

Uncommitted columns contain actual zero words. This stronger shape invariant is necessary
when full active rows of the factor are exchanged: decoded zero alone does not identify a
word for a noninjective decoding. The absolute log determines both the permuted source and
every earlier first-maximum diagonal choice.

## Main results

* `NLAlib.Cholesky.HasFutureZeroColumns.step`: a current-column suffix write retains future zeros.
* `NLAlib.Cholesky.HasFutureZeroColumns.swapRows`: active row exchanges retain future zeros.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K : Type} {N : ℕ}

/-- Every word of each uncommitted factor column is the actual initialization literal. -/
def HasFutureZeroColumns (zero : K) (N count : ℕ) (L : ℕ × ℕ) (s : Store K) : Prop :=
  ∀ i j : Fin N, count ≤ j.val → s.get L.1 (L.2 + j.val * N + i.val) = some zero

/-- The stored Gaussian and factor prefixes under the actual absolute pivot log, together
with its initialized future columns, committed decoded indices and first-maximum choices. -/
def IsDiagonalPrefix (dec : K → ℝ) (zero : K) (A : Matrix (Fin N) (Fin N) ℝ)
    (p : Fin N → Fin N) (count : ℕ) (R L H : ℕ × ℕ) (s : Store K) : Prop :=
  IsRightPrefix dec zero
      (A.submatrix (luPivotPermutation p count) (luPivotPermutation p count)) count R L s ∧
    HasFutureZeroColumns zero N count L s ∧
    (∀ j : Fin N, j.val < count → ∃ w : K,
      s.get H.1 (H.2 + j.val) = some w ∧ dec w = (p j).val) ∧
    HasDiagonalPivotPrefix A p count

/-- A Gaussian/factor prefix depends only on the two declared matrix blocks. -/
theorem IsRightPrefix.readsOnly (dec : K → ℝ) (zero : K)
    (A : Matrix (Fin N) (Fin N) ℝ) (count : ℕ) (R L : ℕ × ℕ) :
    Store.ReadsOnly (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (IsRightPrefix dec zero A count R L) := by
  intro s s' he h
  obtain ⟨rw, lw, hR, hL, hres, hfac, hupper⟩ := h
  refine ⟨rw, lw, ?_, ?_, hres, hfac, hupper⟩
  · intro i hi j hj
    change i < N at hi
    change j < N at hj
    rw [he _ _ (Or.inl ⟨rfl, by simp only [MatLayout.cell]; omega, by
      have hb := Idx.add_lt_mul hj hi
      simp only [MatLayout.cell]
      omega⟩)]
    exact hR i hi j hj
  · intro i hi j hj
    change i < N at hi
    change j < N at hj
    rw [he _ _ (Or.inr ⟨rfl, by simp only [MatLayout.cell]; omega, by
      have hb := Idx.add_lt_mul hj hi
      simp only [MatLayout.cell]
      omega⟩)]
    exact hL i hi j hj

/-- Future literal zeros are a property of the declared factor block alone. -/
theorem HasFutureZeroColumns.readsOnly (zero : K) (N count : ℕ) (L : ℕ × ℕ) :
    Store.ReadsOnly (Store.inBlock L.1 L.2 (N * N))
      (HasFutureZeroColumns zero N count L) := by
  intro s s' he h i j hj
  rw [he _ _ ⟨rfl, by omega, by have hb := Idx.add_lt_mul j.isLt i.isLt; omega⟩]
  exact h i j hj

/-- The diagonal-pivot invariant depends only on the residual, factor and actual log blocks.
This permits ordinary Ops frame and scope rules to retain it through scalar scratch work. -/
theorem IsDiagonalPrefix.readsOnly (dec : K → ℝ) (zero : K)
    (A : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → Fin N) (count : ℕ) (R L H : ℕ × ℕ) :
    Store.ReadsOnly ((Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N)) ⊔
      Store.inBlock H.1 H.2 N) (IsDiagonalPrefix dec zero A p count R L H) := by
  intro s s' he ⟨hpre, hfuture, hlog, hquality⟩
  refine ⟨IsRightPrefix.readsOnly dec zero _ count R L s s'
    (fun b i hi => he b i (Or.inl hi)) hpre,
    HasFutureZeroColumns.readsOnly zero N count L s s'
      (fun b i hi => he b i (Or.inl (Or.inr hi))) hfuture, ?_, hquality⟩
  intro j hj
  obtain ⟨w, hw, hd⟩ := hlog j hj
  exact ⟨w, (he _ _ (Or.inr ⟨rfl, by omega, by have := j.isLt; omega⟩)).trans hw, hd⟩

variable [Inhabited K]

/-- An initialized factor block has actual zero words in every column. -/
theorem HasFutureZeroColumns.of_replicate {zero : K} {L : ℕ × ℕ} {s : Store K}
    (h : s.readBlock L.1 L.2 (N * N) = some (List.replicate (N * N) zero)) :
    HasFutureZeroColumns zero N 0 L s := by
  intro i j _
  have hg := Store.get_of_readBlock h (Idx.add_lt_mul j.isLt i.isLt) default
  simpa only [List.getD_replicate (α := K) (x := zero)
    (h := Idx.add_lt_mul j.isLt i.isLt), Nat.add_assoc] using hg

omit [Inhabited K] in
/-- The actual current-column suffix footprint cannot change a word in a later column. -/
theorem HasFutureZeroColumns.step {zero : K} {L R : ℕ × ℕ} {s s' : Store K}
    (k : Fin N) (h : HasFutureZeroColumns zero N k.val L s) (hRL : R.1 ≠ L.1)
    (hfr : s.EqOff (Store.inBlock R.1 R.2 (N * N) ⊔
      Store.inBlock L.1 (L.2 + k.val * N + k.val) (N - k.val)) s') :
    HasFutureZeroColumns zero N (k.val + 1) L s' := by
  intro i j hj
  rw [hfr.get_eq ?_]
  · exact h i j (by omega)
  · rintro (hR | ⟨_, hlo, hhi⟩)
    · exact hRL hR.1.symm
    · have hb := Nat.mul_le_mul_right N hj
      rw [Nat.succ_mul] at hb
      omega

/-- A row permutation exchanges future zero words with other future zero words; injectivity
of the decoding is not used. -/
theorem HasFutureZeroColumns.swapRows {zero : K} {count : ℕ} {L : ℕ × ℕ}
    {s s' : Store K} {as bs : List K} (k r : Fin N) {τ : Tape K}
    (h : HasFutureZeroColumns zero N count L s)
    (has : s.readBlock L.1 L.2 (N * N) = some as)
    (hbs : s'.readBlock L.1 L.2 (N * N) = some bs)
    (hpost : (LU.swapRowsSpec (K := K)).post [N, k.val, r.val] τ [as] [bs]) :
    HasFutureZeroColumns zero N count L s' := by
  intro i j hj
  have hg := Store.get_of_readBlock hbs (Idx.add_lt_mul j.isLt i.isLt) default
  change s'.get L.1 (L.2 + (j.val * N + i.val)) = some (vec bs (j.val * N + i.val)) at hg
  rw [hpost.2 i.val i.isLt j.val j.isLt,
    ← Function.Injective.map_swap Fin.val_injective] at hg
  have hz := h (Equiv.swap k r i) j hj
  have hget := Store.get_of_readBlock has
    (Idx.add_lt_mul j.isLt (Equiv.swap k r i).isLt) default
  rw [← Nat.add_assoc, hz] at hget
  exact (by simpa only [Nat.add_assoc] using hg.trans hget.symm)

/-- A stored prefix supplies the two actual word blocks and their decoded matrix values. -/
theorem IsRightPrefix.read_blocks {dec : K → ℝ} {zero : K}
    {A : Matrix (Fin N) (Fin N) ℝ} {count : ℕ} {R L : ℕ × ℕ} {s : Store K}
    (h : IsRightPrefix dec zero A count R L s) :
    ∃ rs ls : List K, s.readBlock R.1 R.2 (N * N) = some rs ∧
      s.readBlock L.1 L.2 (N * N) = some ls ∧
      decodeMatrix dec N N rs = gaussState A count ∧
      (∀ i j : Fin N, decodeMatrix dec N N ls i j =
        if j.val < count then choleskyLower A i j else 0) ∧
      (∀ i j : Fin N, i < j → vec ls (j.val * N + i.val) = zero) := by
  obtain ⟨rw, lw, hR, hL, hres, hfac, hupper⟩ := h
  obtain ⟨rs, hrs, -, hrd⟩ := hR.readBlock rfl
  obtain ⟨ls, hls, -, hld⟩ := hL.readBlock rfl
  refine ⟨rs, ls, hrs, hls, ?_, ?_, ?_⟩
  · ext i j
    rw [decodeMatrix_apply, hrd i i.isLt j j.isLt, hres i j]
  · intro i j
    rw [decodeMatrix_apply, hld i i.isLt j j.isLt, hfac i j]
  · intro i j hij
    rw [hld i i.isLt j j.isLt]
    exact hupper i j hij

/-- The actual symmetric word exchange transports the stored Gaussian prefix and every
completed factor column. Future literal zeros supply the upper shape after the row exchange. -/
theorem IsRightPrefix.symmetricPivot {dec : K → ℝ} {zero : K}
    {A : Matrix (Fin N) (Fin N) ℝ} {R L : ℕ × ℕ} {s s' : Store K}
    {rs ls rs' ls' : List K} {τ : Tape K} (k r : Fin N) (hkr : k ≤ r)
    (hls : s.readBlock L.1 L.2 (N * N) = some ls)
    (hrs' : s'.readBlock R.1 R.2 (N * N) = some rs')
    (hls' : s'.readBlock L.1 L.2 (N * N) = some ls')
    (hres : decodeMatrix dec N N rs = gaussState A k.val)
    (hfac : ∀ i j : Fin N, decodeMatrix dec N N ls i j =
      if j.val < k.val then choleskyLower A i j else 0)
    (hupper : ∀ i j : Fin N, i < j → vec ls (j.val * N + i.val) = zero)
    (hfuture : HasFutureZeroColumns zero N k.val L s)
    (hpost : (symmetricPivotSpec (K := K)).post [N, k.val, r.val] τ [rs, ls] [rs', ls']) :
    IsRightPrefix dec zero (A.submatrix (Equiv.swap k r) (Equiv.swap k r)) k.val R L s' ∧
      HasFutureZeroColumns zero N k.val L s' := by
  have hfix (j : Fin N) (hj : j.val < k.val) : Equiv.swap k r j = j :=
    Fin.swap_apply_of_lt_of_le k r hkr j hj
  have hfuture' := hfuture.swapRows k r hls hls'
    (τ := τ) (show (LU.swapRowsSpec (K := K)).post [N, k.val, r.val] τ [ls] [ls'] from
      ⟨hpost.2.1, hpost.2.2.2⟩)
  refine ⟨⟨fun i j => vec rs' (j * N + i), fun i j => vec ls' (j * N + i),
    Store.holdsMat_of_readBlock rfl hrs', Store.holdsMat_of_readBlock rfl hls',
    ?_, ?_, ?_⟩, hfuture'⟩
  · have hd := symmetricPivotSpec_decode_residual (dec := dec) k r hpost
    rw [hres, ← gaussState_submatrix A (Equiv.swap k r) k.val hfix] at hd
    intro i j
    simpa only [decodeMatrix_apply] using congrFun (congrFun hd i) j
  · intro i j
    change dec (vec ls' (j.val * N + i.val)) = _
    rw [← decodeMatrix_apply dec N N ls' i j,
      symmetricPivotSpec_decode_factor (dec := dec) k r hpost,
      Matrix.submatrix_apply, id_eq, hfac]
    by_cases hj : j.val < k.val
    · rw [if_pos hj, if_pos hj]
      exact (choleskyLower_submatrix_apply A (Equiv.swap k r) k.val hfix i j hj).symm
    · rw [if_neg hj, if_neg hj]
  · intro i j hij
    change vec ls' (j.val * N + i.val) = zero
    by_cases hj : j.val < k.val
    · rw [hpost.2.2.2 i.val i.isLt j.val j.isLt,
        ← Function.Injective.map_swap Fin.val_injective, hfix i (by
          have hi : i.val < j.val := hij
          omega)]
      exact hupper i j hij
    · have hg := Store.get_of_readBlock hls' (Idx.add_lt_mul j.isLt i.isLt) default
      have hz := hfuture' i j (by omega)
      rw [← Nat.add_assoc, hz] at hg
      exact Option.some.inj hg.symm

/-- Copying the input and filling the factor establishes an empty diagonal-pivot prefix.
The log need not be initialized before its entries are actually written. -/
theorem IsDiagonalPrefix.initial {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    {R L H : ℕ × ℕ} {s : Store K} {as : List K} (p : Fin N → Fin N)
    (hR : s.readBlock R.1 R.2 (N * N) = some as)
    (hL : s.readBlock L.1 L.2 (N * N) = some (List.replicate (N * N) (M.lit 0))) :
    IsDiagonalPrefix dec (M.lit 0) (decodeMatrix dec N N as) p 0 R L H s := by
  refine ⟨?_, HasFutureZeroColumns.of_replicate hL, ?_, HasDiagonalPivotPrefix.initial _ _⟩
  · simpa only [luPivotPermutation_zero, Equiv.coe_refl, Matrix.submatrix_id_id] using
      IsRightPrefix.initial hM hR hL
  · intro j hj
    exact (Nat.not_lt_zero j.val hj).elim

end NLAlib.Cholesky
