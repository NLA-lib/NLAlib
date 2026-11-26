/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Swap

/-!
# Stored row-scale exchanges

A fixed row scale follows the same current-position row exchange as its residual row. The
actual copy-only routine is the existing rectangular row swap on a single-column matrix;
selecting the incumbent row is a no-op. No arithmetic model is required.

## Main results

* `NLAlib.LU.swapScales_meets`: actual word exchange without numerical assumptions.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Exchange the two stored scale words at the supplied current row positions. -/
def swapScales : Routine Op Tst := routine% [n, k, r] (scales : n) → (scales) {
  ifPos (r - k) {
    run Examples.Strided.swapMatrixRows [n, 1, k, r] (scales)
  }
}

variable [Inhabited K]

/-- Every word is retained except the two actual selected positions, whose words exchange. -/
def swapScalesSpec : Routine.Spec K :=
  spec% [n, k, r] (ss) → (ts) requires k ≤ r ∧ r < n ensures
    ts.length = n ∧ ∀ i < n, vec ts i = vec ss (Equiv.swap k r i)

private theorem vec_swappedScales (ss : List K) {n i k r : ℕ} (hi : i < n) :
    vec (Examples.Strided.swappedRows ss n 1 k r) i = vec ss (Equiv.swap k r i) := by
  have hq : i < n * 1 := by simpa only [Nat.mul_one] using hi
  simp only [vec, List.getD_eq_getElem?_getD,
    Examples.Strided.getElem?_swappedRows ss k r hq, Option.getD_some,
    Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Equiv.swap_apply_def,
    Nat.mul_zero, Nat.zero_add]

/-- The actual rectangular copy loop exchanges fixed scales, including an unchanged pivot.
Its operation contracts impose no decoded arithmetic or positivity assumption. -/
theorem swapScales_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (swapScales (Op := Op) (Tst := Tst)).Meets I (swapScalesSpec (K := K)) := by
  routine_intro [n, k, r] (scales) reads (ss)
  obtain ⟨hkr, hrn⟩ := hpre
  have hlen : ss.length = n := Store.length_of_readBlock hss
  refine writes_ifPos rfl ?_
  by_cases hlt : 0 < r - k
  · rw [if_pos hlt]
    call (Examples.Strided.swapMatrixRows_meets hI) [n, 1, k, r] (scales)
      as m₁ hfr₁ hpos₁ (ts) hpost
    case' hcall => exact [ss]
    case' hr =>
      refine Mem.readBlocks_of_cons ?_ rfl
      change m.store.readBlock scales.1 scales.2 (n * 1) = some ss
      simpa only [Nat.mul_one] using hss
    case' hpre => exact ⟨by omega, hrn⟩
    have he : ts = Examples.Strided.swappedRows ss n 1 k r := hpost
    refine ⟨hpos₁, [ts], Mem.readBlocks_of_cons
      (by simpa only [Nat.mul_one] using hts) rfl, ?_⟩
    change ts.length = n ∧ ∀ i < n, vec ts i = vec ss (Equiv.swap k r i)
    rw [he]
    exact ⟨by simp [Examples.Strided.swappedRows], fun i hi => vec_swappedScales ss hi⟩
  · rw [if_neg hlt]
    have he : k = r := by omega
    exact ⟨rfl, [ss], Mem.readBlocks_of_cons hss rfl, hlen,
      fun i _ => by simp only [he, Equiv.swap_self, Equiv.refl_apply]⟩

end NLAlib.LU
