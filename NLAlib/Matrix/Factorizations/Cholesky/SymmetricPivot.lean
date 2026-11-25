/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Swap

/-!
# Actual symmetric pivot exchanges for Cholesky

The residual is exchanged in both rows and columns. Already computed factor entries follow
the same row exchange, including the entire earlier column prefix. Every exchange uses the
shared scalar-copy routines and their actual word postconditions.

## Main results

* `NLAlib.Cholesky.symmetricPivot_meets`: the residual and factor word permutations.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Symmetrically exchange the residual pivot and exchange the full corresponding factor rows. -/
def symmetricPivot : Routine Op Tst :=
  routine% [n, k, r] (R : n * n, L : n * n) → (R, L) {
    run LU.swapRows [n, k, r] (R);
    run LU.swapColumns [n, k, r] (R);
    run LU.swapRows [n, k, r] (L)
  }

variable [Inhabited K]

/-- The original residual words follow both exchanges; original factor words follow the row
exchange. The selected absolute index is in the active suffix. -/
def symmetricPivotSpec : Routine.Spec K :=
  spec% [n, k, r] (rs, ls) → (rs', ls') requires k ≤ r ∧ r < n ensures
    rs'.length = n * n ∧ ls'.length = n * n ∧
      (∀ i < n, ∀ j < n, vec rs' (j * n + i) =
        vec rs (Equiv.swap k r j * n + Equiv.swap k r i)) ∧
      (∀ i < n, ∀ j < n, vec ls' (j * n + i) = vec ls (j * n + Equiv.swap k r i))

/-- The three actual word-exchange calls satisfy the symmetric pivot contract. No property
of the decoding or numerical arithmetic is needed. -/
theorem symmetricPivot_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (symmetricPivot (Op := Op) (Tst := Tst)).Meets I (symmetricPivotSpec (K := K)) := by
  routine_intro [n, k, r] (R, L) reads (rs, ls)
  obtain ⟨hkr, hrn⟩ := hpre
  have hswap (i : ℕ) (hi : i < n) : Equiv.swap k r i < n := by
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  call (LU.swapRows_meets hI) [n, k, r] (R) (pre := ⟨hkr, hrn⟩)
    as m₁ hfr₁ hpos₁ (rs₁) hrow
  call (LU.swapColumns_meets hI) [n, k, r] (R) (pre := ⟨hkr, hrn⟩)
    as m₂ hfr₂ hpos₂ (rs₂) hcol
  call (LU.swapRows_meets hI) [n, k, r] (L) (pre := ⟨hkr, hrn⟩)
    as m₃ hfr₃ hpos₃ (ls₃) hfactor
  routine_exit
  refine ⟨hcol.1, hfactor.1, ?_, hfactor.2⟩
  intro i hi j hj
  rw [hcol.2 i hi j hj, hrow.2 i hi (Equiv.swap k r j) (hswap j hj)]

/-- The actual residual words decode to a simultaneous reindexing by the selected exchange. -/
theorem symmetricPivotSpec_decode_residual {dec : K → ℝ} {n : ℕ} (k r : Fin n)
    {rs ls rs' ls' : List K} {τ : Tape K}
    (h : (symmetricPivotSpec (K := K)).post [n, k.val, r.val] τ [rs, ls] [rs', ls']) :
    decodeMatrix dec n n rs' =
      (decodeMatrix dec n n rs).submatrix (Equiv.swap k r) (Equiv.swap k r) := by
  ext i j
  rw [decodeMatrix_apply, Matrix.submatrix_apply, decodeMatrix_apply]
  congr 1
  rw [h.2.2.1 i.val i.isLt j.val j.isLt]
  simp only [Function.Injective.map_swap Fin.val_injective]

/-- The actual factor words decode to left reindexing, retaining every completed column. -/
theorem symmetricPivotSpec_decode_factor {dec : K → ℝ} {n : ℕ} (k r : Fin n)
    {rs ls rs' ls' : List K} {τ : Tape K}
    (h : (symmetricPivotSpec (K := K)).post [n, k.val, r.val] τ [rs, ls] [rs', ls']) :
    decodeMatrix dec n n ls' = (decodeMatrix dec n n ls).submatrix (Equiv.swap k r) id := by
  ext i j
  rw [decodeMatrix_apply, Matrix.submatrix_apply, decodeMatrix_apply]
  congr 1
  rw [h.2.2.2 i.val i.isLt j.val j.isLt]
  simp only [Function.Injective.map_swap Fin.val_injective, id_eq]

end NLAlib.Cholesky
