/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledStep
public import NLAlib.Matrix.Factorizations.LU.PivotedCanonicalStep
public import NLAlib.Matrix.Factorizations.LUScaledPivoting

/-!
# Canonical prefixes after an actual fixed-scale step

The packed residual and fixed scales have actual separate output lengths. The common word
bridge advances the canonical matrix prefixes; the actual scale exchange transports the
original row norms by the same current row swap. Weighted maximality refers to the source
before the swap and supplies the existing scaled-prefix update theorem.

## Main results

* `NLAlib.LU.scaledStepSpec_prefix`: actual packed outputs give the next canonical prefixes.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} [Inhabited K] {N : ℕ}

/-- The actual selected row, canonical next residual/factors and exchanged original scales
follow from the word-level scaled step. The weighted maximum is recorded before the swap;
no unweighted multiplier bound or nonsingularity assumption is introduced. -/
theorem scaledStepSpec_prefix {M : Machine K} {dec : K → ℝ} {bound : ℕ}
    (hM : ExactModel dec M) (A : Matrix (Fin N) (Fin N) ℝ)
    (p : Fin N → Fin N) (k : Fin N) {τ : Tape K}
    {packed ls us packed' ls' us' : List K} {rword : K}
    (hpost : (scaledStepSpec M dec bound).post [N, k.val] τ
      [packed, ls, us] [packed', ls', us', [rword]])
    (hr : ∀ i j : Fin N, decodeMatrix dec N N (packed.take (N * N)) i j =
      gaussState (A.submatrix (luPivotPermutation p k.val) id) k.val i j)
    (hl : ∀ i j : Fin N, decodeMatrix dec N N ls i j = if j.val < k.val then
      luLower (A.submatrix (luPivotPermutation p k.val) id) i j else 0)
    (hu : ∀ i j : Fin N, decodeMatrix dec N N us i j = if i.val < k.val then
      luUpper (A.submatrix (luPivotPermutation p k.val) id) i j else 0)
    (hscale : ∀ i : Fin N, dec (vec ((packed.drop (N * N)).take N) i.val) =
      ‖A (luPivotPermutation p k.val i)‖) :
    ∃ r : Fin N, k ≤ r ∧ dec rword = r.val ∧
      (∀ i : Fin N, k ≤ i →
        ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) k i k‖ /
            ‖A (luPivotPermutation p k.val i)‖ ≤
          ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) k r k‖ /
            ‖A (luPivotPermutation p k.val r)‖) ∧
      let B := A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1)) id
      (∀ i j : Fin N, decodeMatrix dec N N (packed'.take (N * N)) i j =
        gaussState B (k.val + 1) i j) ∧
      (∀ i j : Fin N, decodeMatrix dec N N ls' i j =
        if j.val < k.val + 1 then luLower B i j else 0) ∧
      (∀ i j : Fin N, decodeMatrix dec N N us' i j =
        if i.val < k.val + 1 then luUpper B i j else 0) ∧
      ∀ i : Fin N, dec (vec ((packed'.drop (N * N)).take N) i.val) =
        ‖A (luPivotPermutation (Function.update p k r) (k.val + 1) i)‖ := by
  obtain ⟨r, hkr, hdr, hchoice, rs₀, ls₀, us₀, ss', rs', hlenR, hlenS,
    hswap, hscales, hstep, hpacked⟩ := hpost
  obtain ⟨r', hkr', hdr', hmax, hfirst⟩ := hchoice
  have he : r' = r := Fin.ext (Nat.cast_injective (hdr'.symm.trans hdr))
  subst r'
  let B := A.submatrix (luPivotPermutation p k.val) id
  have hnext := pivotSwapsSpec_stepSpec_prefix hM B k r k hkr le_rfl hswap hstep hr hl hu
  have hB : B.submatrix (Equiv.swap k r) (Equiv.swap k k) =
      A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1)) id := by
    rw [luPivotPermutation_update]
    ext i j
    simp only [B, Matrix.submatrix_apply, Equiv.trans_apply,
      Equiv.swap_self, Equiv.refl_apply, id_eq]
  rw [hB] at hnext
  have htake : packed'.take (N * N) = rs' := by
    rw [hpacked, ← hlenR, List.take_left]
  have hdrop : (packed'.drop (N * N)).take N = ss' := by
    rw [hpacked, ← hlenR, List.drop_left, ← hlenS, List.take_length]
  refine ⟨r, hkr, hdr, ?_, ?_, hnext.2.1, hnext.2.2, ?_⟩
  · intro i hi
    have hh := hmax i hi
    simpa only [← hr i k, ← hr r k, decodeMatrix_apply, Real.norm_eq_abs,
      hscale i, hscale r] using hh
  · simpa only [htake] using hnext.1
  · intro i
    rw [hdrop, luPivotPermutation_update, Equiv.trans_apply]
    have hh := congrArg dec (hscales.2 i.val i.isLt)
    have hd : dec (vec ss' i.val) =
        dec (vec ((packed.drop (N * N)).take N) (Equiv.swap k r i).val) := by
      simpa only [Function.Injective.map_swap Fin.val_injective] using hh
    exact hd.trans (hscale (Equiv.swap k r i))

end NLAlib.LU
