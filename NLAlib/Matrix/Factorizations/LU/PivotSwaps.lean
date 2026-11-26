/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Swap

/-!
# Matching residual and factor exchanges

A pivot step moves the selected residual row and column together with the corresponding
lower row and entire upper column. All four exchanges are the shared scalar copy routines;
no arithmetic model or pivot quality is needed for their exact word specification.

## Main results

* `NLAlib.LU.pivotSwaps_meets`: the actual four exchanges and their complete word output.
* `NLAlib.LU.pivotSwapsSpec_decode`: independent row and column covariance of decoded matrices.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Perform the four matching exchanges before factor materialization. The upper-column
exchange includes every committed upper row, so later column pivots preserve reconstruction. -/
def pivotSwaps : Routine Op Tst :=
  routine% [n, k, r, c] (R : n * n, L : n * n, U : n * n) → (R, L, U) {
    run swapRows [n, k, r] (R);
    run swapRows [n, k, r] (L);
    run swapColumns [n, k, c] (R);
    run swapColumns [n, k, c] (U)
  }

variable [Inhabited K]

/-- The exact original words with independent row and column exchanges. The updated lower
factor has only its rows exchanged; the upper factor has only its columns exchanged. -/
def pivotSwapsSpec : Routine.Spec K :=
  spec% [n, k, r, c] (rs, ls, us) → (rs', ls', us') requires
    (k ≤ r ∧ r < n) ∧ (k ≤ c ∧ c < n) ensures
    (∀ i < n, ∀ j < n,
      vec rs' (j * n + i) = vec rs (Equiv.swap k c j * n + Equiv.swap k r i)) ∧
    (∀ i < n, ∀ j < n, vec ls' (j * n + i) = vec ls (j * n + Equiv.swap k r i)) ∧
    (∀ i < n, ∀ j < n, vec us' (j * n + i) = vec us (Equiv.swap k c j * n + i))

/-- Each actual exchange succeeds under scalar copy contracts, including equal selected
positions. No nonzero-pivot premise or successful-run assumption is used. -/
theorem pivotSwaps_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (pivotSwaps (Op := Op) (Tst := Tst)).Meets I (pivotSwapsSpec (K := K)) := by
  routine_intro [n, k, r, c] (R, L, U) reads (rs, ls, us)
  obtain ⟨hrow, hcol⟩ := hpre
  call (swapRows_meets hI) [n, k, r] (R) (pre := hrow)
    as m₁ hfr₁ hpos₁ (rs₁) hR
  call (swapRows_meets hI) [n, k, r] (L) (pre := hrow)
    as m₂ hfr₂ hpos₂ (ls₁) hL
  call (swapColumns_meets hI) [n, k, c] (R) (pre := hcol)
    as m₃ hfr₃ hpos₃ (rs₂) hC
  call (swapColumns_meets hI) [n, k, c] (U) (pre := hcol)
    as m₄ hfr₄ hpos₄ (us₁) hU
  routine_exit
  refine ⟨?_, hL.2, hU.2⟩
  intro i hi j hj
  rw [hC.2 i hi j hj]
  apply hR.2 i hi
  by_cases hjk : j = k
  · simpa only [hjk, Equiv.swap_apply_left] using hcol.2
  by_cases hjc : j = c
  · simpa only [hjc, Equiv.swap_apply_right] using hrow.1.trans_lt hrow.2
  simpa only [Equiv.swap_apply_of_ne_of_ne hjk hjc] using hj

/-- The exact word output transports all three decoded matrices, with independent row and
column permutations. Decoding need not be injective and no arithmetic law is required. -/
theorem pivotSwapsSpec_decode {dec : K → ℝ} {n : ℕ} (k r c : Fin n)
    {rs ls us rs' ls' us' : List K} {τ : Tape K}
    (h : (pivotSwapsSpec (K := K)).post [n, k.val, r.val, c.val] τ
      [rs, ls, us] [rs', ls', us']) :
    decodeMatrix dec n n rs' = (decodeMatrix dec n n rs).submatrix
      (Equiv.swap k r) (Equiv.swap k c) ∧
    decodeMatrix dec n n ls' = (decodeMatrix dec n n ls).submatrix (Equiv.swap k r) id ∧
    decodeMatrix dec n n us' = (decodeMatrix dec n n us).submatrix id (Equiv.swap k c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    rw [decodeMatrix_apply, Matrix.submatrix_apply, decodeMatrix_apply]
    congr 1
    simpa only [Function.Injective.map_swap Fin.val_injective] using
      h.1 i.val i.isLt j.val j.isLt
  · ext i j
    rw [decodeMatrix_apply, Matrix.submatrix_apply, decodeMatrix_apply]
    congr 1
    simpa only [Function.Injective.map_swap Fin.val_injective, id_eq] using
      h.2.1 i.val i.isLt j.val j.isLt
  · ext i j
    rw [decodeMatrix_apply, Matrix.submatrix_apply, decodeMatrix_apply]
    congr 1
    simpa only [Function.Injective.map_swap Fin.val_injective, id_eq] using
      h.2.2 i.val i.isLt j.val j.isLt

end NLAlib.LU
