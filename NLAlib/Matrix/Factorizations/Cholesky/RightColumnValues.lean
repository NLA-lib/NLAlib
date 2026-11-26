/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightColumn
public import NLAlib.Matrix.Factorizations.Cholesky.RightPrefix

/-!
# Exact values of a right-looking Cholesky column

The actual column word specification gives the positive pivot root and the normalized
residual tail. At a Hermitian Gaussian state with positive pivot these are precisely the next
canonical Cholesky column. There is no execution or successful-run premise in the scalar argument.

## Main results

* `NLAlib.Cholesky.rightColumnSpec_decode`: exact decoded root and quotients.
* `NLAlib.Cholesky.rightColumnSpec_decode_choleskyLower`: the canonical column suffix.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K : Type} [Inhabited K]

/-- Exact decoded arithmetic turns the actual root/quotient word list into scalar
normalization at a positive pivot. The divisor is proved positive before division is used. -/
theorem rightColumnSpec_decode {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    {n : ℕ} {p : K} {xs ys : List K} {τ : Tape K}
    (hpost : (rightColumnSpec M).post [n] τ [[p], xs] [ys]) (hp : 0 < dec p) :
    dec (vec ys 0) = Real.sqrt (dec p) ∧
      ∀ i < n, dec (vec ys (i + 1)) = dec (vec xs i) / Real.sqrt (dec p) := by
  have hy : ys = M.sqrt p :: scalF M (M.sqrt p) (vec xs) n := hpost
  have hroot := hM.sqrt p hp.le
  have hnz : dec (M.sqrt p) ≠ 0 := by
    rw [hroot]
    exact (Real.sqrt_pos.mpr hp).ne'
  rw [hy]
  constructor
  · change dec (M.sqrt p) = Real.sqrt (dec p)
    exact hroot
  · intro i hi
    have hv : vec (scalF M (M.sqrt p) (vec xs) n) i = M.div (vec xs i) (M.sqrt p) := by
      simp [scalF, vec, List.getD_eq_getElem?_getD, hi]
    change dec ((M.sqrt p :: scalF M (M.sqrt p) (vec xs) n).getD (i + 1) default) = _
    rw [List.getD_cons_succ]
    change dec (vec (scalF M (M.sqrt p) (vec xs) n) i) = _
    rw [hv, hM.div _ _ hnz, hroot]

/-- At an exact Hermitian Gaussian residual with positive pivot, the words written by column
normalization decode to the canonical Cholesky factor from the diagonal downward. -/
theorem rightColumnSpec_decode_choleskyLower {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (k : Fin N) (hpivot : 0 < gaussState A k.val k k) (rw : ℕ → ℕ → K)
    (hR : ∀ i j : Fin N, dec (rw i j) = gaussState A k.val i j)
    {xs ys : List K} {τ : Tape K}
    (hx : ∀ i < N - k.val - 1, vec xs i = rw (k.val + 1 + i) k.val)
    (hy : (rightColumnSpec M).post [N - k.val - 1] τ [[rw k k], xs] [ys]) :
    ∀ i : Fin N, k ≤ i → dec (vec ys (i.val - k.val)) = choleskyLower A i k := by
  have hp : 0 < dec (rw k k) := by
    rw [hR k k]
    exact hpivot
  obtain ⟨hd, htail⟩ := rightColumnSpec_decode hM hy hp
  intro i hki
  by_cases hik : i = k
  · subst i
    rw [Nat.sub_self, hd, hR k k, hA.choleskyLower_apply_self]
    simp only [RCLike.re_to_real, RCLike.ofReal_real_eq_id, id_eq]
  · have hlt : k.val < i.val :=
      lt_of_le_of_ne hki (fun he => hik (Fin.ext he.symm))
    have ht : i.val - (k.val + 1) < N - k.val - 1 := by omega
    have he : i.val - k.val = (i.val - (k.val + 1)) + 1 := by omega
    rw [he, htail _ ht, hx _ ht]
    have hrow : k.val + 1 + (i.val - (k.val + 1)) = i.val := by omega
    rw [hrow, hR i k, hR k k]
    simp only [choleskyLower, Matrix.of_apply, if_pos hki, RCLike.re_to_real,
      RCLike.ofReal_real_eq_id, id_eq]

end NLAlib.Cholesky
