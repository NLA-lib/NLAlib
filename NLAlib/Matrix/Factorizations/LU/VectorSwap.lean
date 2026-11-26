/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Strided
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Matrix.Factorizations.LUPivoting

/-!
# Exchanging two active vector entries

The existing scalar strided row-swap kernel on a one-column matrix exchanges two vector
entries. Equal positions execute no copy. The word-level judgment retains every other word
and is independent of numerical arithmetic, supporting actual pivot-log replay in solves.

## Main results

* `NLAlib.LU.swapVector_meets`: exact word exchange of bounded active positions.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Exchange entries `k` and `r` through the actual scalar strided row-swap kernel. -/
def swapVector : Routine Op Tst := routine% [n, k, r] (x : n) → (x) {
  ifPos (r - k) {
    run Examples.Strided.swapMatrixRows [n, 1, k, r] (x)
  }
}

variable [Inhabited K]

/-- The two selected entries are exchanged as words; all remaining entries are retained. -/
def swapVectorSpec : Routine.Spec K :=
  spec% [n, k, r] (xs) → (ys) requires k ≤ r ∧ r < n ensures
    ys.length = n ∧ ∀ i < n, vec ys i = vec xs (Equiv.swap k r i)

omit [Has ScalarOp Op] in
private theorem vec_swappedVector (xs : List K) {n k r i : ℕ} (hi : i < n) :
    vec (Examples.Strided.swappedRows xs n 1 k r) i = vec xs (Equiv.swap k r i) := by
  have he := Examples.Strided.getElem?_swappedRows xs k r (p := n) (n := 1) (by omega : i < n * 1)
  simp only [vec, List.getD_eq_getElem?_getD, he, Option.getD_some,
    Nat.div_eq_of_lt hi, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hi,
    Equiv.swap_apply_def]

/-- The actual copy-only kernel performs the vector exchange with no arithmetic model or
successful-run assumption. Its scratch is scoped and only the vector can change. -/
theorem swapVector_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (swapVector (Op := Op) (Tst := Tst)).Meets I (swapVectorSpec (K := K)) := by
  routine_intro [n, k, r] (x) reads (xs)
  obtain ⟨hkr, hr⟩ := hpre
  refine writes_ifPos rfl ?_
  by_cases hlt : 0 < r - k
  · rw [if_pos hlt]
    call (Examples.Strided.swapMatrixRows_meets hI) [n, 1, k, r] (x)
      as m₁ hfr₁ hpos₁ (ys) hpost
    case' hcall => exact [xs]
    case' hpre => exact ⟨by omega, hr⟩
    case' hr =>
      change m.readBlocks [x] [n * 1] = some [xs]
      simpa only [Nat.mul_one] using
        (Mem.readBlocks_of_cons (as := []) (ns := []) (xs := []) hxs rfl)
    have he : ys = Examples.Strided.swappedRows xs n 1 k r := hpost
    have hys' : m₁.store.readBlock x.1 x.2 n = some ys := by simpa only [Nat.mul_one] using hys
    refine ⟨hpos₁, [ys], Mem.readBlocks_of_cons hys' rfl, ?_⟩
    rw [he]
    exact ⟨by simp [Examples.Strided.swappedRows], fun i hi => vec_swappedVector xs hi⟩
  · rw [if_neg hlt]
    have he : k = r := by omega
    exact ⟨rfl, [xs], Mem.readBlocks_of_cons hxs rfl, Store.length_of_readBlock hxs,
      fun i _ => by simp only [he, Equiv.swap_self, Equiv.refl_apply]⟩

omit [Has ScalarOp Op] in
/-- Finite vector coordinates read the actual exchanged words as a finite permutation. -/
theorem swapVectorSpec_apply {n : ℕ} (k r : Fin n) {xs ys : List K} {τ : Tape K}
    (hpost : (swapVectorSpec (K := K)).post [n, k.val, r.val] τ [xs] [ys]) (i : Fin n) :
    vec ys i.val = vec xs (((Equiv.swap k r) i).val) := by
  have hh : ys.length = n ∧ ∀ j < n, vec ys j = vec xs (Equiv.swap k.val r.val j) := hpost
  have he : ((Equiv.swap k r i).val) = Equiv.swap k.val r.val i.val := by
    simp only [Equiv.swap_apply_def, Fin.ext_iff]
    split_ifs <;> rfl
  rw [he]
  exact hh.2 i.val i.isLt

end NLAlib.LU
