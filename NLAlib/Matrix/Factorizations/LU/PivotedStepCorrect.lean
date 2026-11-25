/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedStep
public import NLAlib.Matrix.Factorizations.LU.PivotedPrefix
public import NLAlib.Matrix.Factorizations.LU.PivotedCanonicalStep

/-!
# Canonical prefixes after an actual pivoted step

The word-level step reports the selected current positions and its actual swapped factor
blocks. Exact scalar arithmetic turns these outputs into the next Gaussian state for the
input permuted by the updated logs. Earlier column quality is transported by active swaps.

## Main results

* `NLAlib.LU.pivotedStepSpec_prefix`: the actual stored step advances canonical prefixes.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} [Inhabited K] {N : ℕ}

/-- Exact arithmetic converts the word-level policy step into the next canonical residual,
factor prefixes and quantitative column-quality prefix. The actual reported row and column
are the two updates to the permutation logs. Zero pivots are included in this algebra. -/
theorem pivotedStepSpec_prefix {M : Machine K} {dec : K → ℝ} {quality : ℝ}
    {bound : ℕ} {fixedColumns : Bool} (hM : ExactModel dec M)
    (A : Matrix (Fin N) (Fin N) ℝ) (p q : Fin N → Fin N) (k : Fin N)
    {τ : Tape K} {rs ls us rs' ls' us' : List K} {rword cword : K}
    (hpost : (pivotedStepSpec M dec quality bound fixedColumns).post [N, k.val] τ
      [rs, ls, us] [rs', ls', us', [rword], [cword]])
    (hr : ∀ i j : Fin N, decodeMatrix dec N N rs i j =
      gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) k i j)
    (hl : ∀ i j : Fin N, decodeMatrix dec N N ls i j = if j.val < k.val then
      luLower (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) i j else 0)
    (hu : ∀ i j : Fin N, decodeMatrix dec N N us i j = if i.val < k.val then
      luUpper (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) i j else 0)
    (hm : ∀ t i : Fin N, t.val < k.val → t ≤ i → quality *
      ‖gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) t i t‖ ≤
      ‖gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) t t t‖) :
    ∃ r c : Fin N, k ≤ r ∧ k ≤ c ∧ dec rword = r.val ∧ dec cword = c.val ∧
      (fixedColumns = true → c = k) ∧
      let B := A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
        (luPivotPermutation (Function.update q k c) (k.val + 1))
      (∀ i j : Fin N, decodeMatrix dec N N rs' i j = gaussState B (k.val + 1) i j) ∧
      (∀ i j : Fin N, decodeMatrix dec N N ls' i j =
        if j.val < k.val + 1 then luLower B i j else 0) ∧
      (∀ i j : Fin N, decodeMatrix dec N N us' i j =
        if i.val < k.val + 1 then luUpper B i j else 0) ∧
      ∀ t i : Fin N, t.val < k.val + 1 → t ≤ i →
        quality * ‖gaussState B t i t‖ ≤ ‖gaussState B t t t‖ := by
  obtain ⟨r, c, hkr, hkc, hdr, hdc, hfixed, hquality, rs₀, ls₀, us₀, hswap, hstep⟩ := hpost
  let B := A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)
  have hnext := pivotSwapsSpec_stepSpec_prefix hM B k r c hkr hkc hswap hstep hr hl hu
  have hpivot : ∀ i : Fin N, k ≤ i →
      quality * ‖gaussState B k i c‖ ≤ ‖gaussState B k r c‖ := by
    intro i hi
    have hh := hquality i hi
    dsimp only [B]
    simpa only [← hr i c, ← hr r c, decodeMatrix_apply, Real.norm_eq_abs] using hh
  have hmax := (forall_luLower_luUpper_mul_norm_le_of_update A p q k r c hkr hkc
    (decodeMatrix dec N N ls) (decodeMatrix dec N N us) quality
    (fun i j hj => by simpa only [if_pos hj] using hl i j)
    (fun i j hi => by simpa only [if_pos hi] using hu i j) hm hpivot).2.2
  refine ⟨r, c, hkr, hkc, hdr, hdc, fun hf => Fin.ext (hfixed hf), ?_⟩
  dsimp only
  rw [submatrix_luPivotPermutation_update]
  exact ⟨hnext.1, hnext.2.1, hnext.2.2, by
    simpa only [submatrix_luPivotPermutation_update] using hmax⟩

end NLAlib.LU
