/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RoundedPrefix
public import NLAlib.Matrix.Factorizations.LU.PivotedStepCorrect

/-!
# Rounded reconstruction after an actual pivoted LU step

The actual selected indices transport the rounded reconstruction, initialized future factors
and committed multiplier bounds. The zero-safe factor step then advances them, using pivot
quality to justify a skipped zero column. Both actual logs update the original input permutation.

## Main results

* `NLAlib.LU.pivotedStepSpec_rounded`: actual pivot reports advance stored rounded factors.
-/

@[expose] public section

namespace NLAlib.LU

open Ops Computation

variable {K : Type} [Inhabited K] {N : ℕ}

/-- Word-exact active row and column exchanges transport the rounded matrix invariant and
future structural zeros. No restriction is made on retired residual values. -/
theorem roundedPrefix_swaps {u quality : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    (k r c : Fin N) (hkr : k ≤ r) (hkc : k ≤ c) {dec : K → ℝ}
    {rs ls us rs₀ ls₀ us₀ : List K} {τ : Tape K}
    (hswap : (pivotSwapsSpec (K := K)).post [N, k.val, r.val, c.val] τ
      [rs, ls, us] [rs₀, ls₀, us₀])
    (hprefix : u < 1 → IsLURoundingPrefix u k.val A (decodeMatrix dec N N rs)
      (decodeMatrix dec N N ls) (decodeMatrix dec N N us))
    (hshape : IsLUTriangularPrefix k.val (decodeMatrix dec N N ls) (decodeMatrix dec N N us))
    (hL : ∀ i j : Fin N, k.val ≤ j.val → decodeMatrix dec N N ls i j = 0)
    (hU : ∀ i j : Fin N, k.val ≤ i.val → decodeMatrix dec N N us i j = 0)
    (hbound : ∀ i j : Fin N, j.val < k.val →
      |decodeMatrix dec N N ls i j| ≤ (1 + u) / quality) :
    (u < 1 → IsLURoundingPrefix u k.val (A.submatrix (Equiv.swap k r) (Equiv.swap k c))
      (decodeMatrix dec N N rs₀) (decodeMatrix dec N N ls₀) (decodeMatrix dec N N us₀)) ∧
      IsLUTriangularPrefix k.val (decodeMatrix dec N N ls₀) (decodeMatrix dec N N us₀) ∧
      (∀ i j : Fin N, k.val ≤ j.val → decodeMatrix dec N N ls₀ i j = 0) ∧
      (∀ i j : Fin N, k.val ≤ i.val → decodeMatrix dec N N us₀ i j = 0) ∧
      ∀ i j : Fin N, j.val < k.val →
        |decodeMatrix dec N N ls₀ i j| ≤ (1 + u) / quality := by
  obtain ⟨hsR, hsL, hsU⟩ := pivotSwapsSpec_decode (dec := dec) k r c hswap
  have hρ := Fin.swap_apply_of_lt_of_le k r hkr
  have hκ := Fin.swap_apply_of_lt_of_le k c hkc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hu1
    have hn := ((hprefix hu1).submatrix_left (Equiv.swap k r) hρ).submatrix_right
      (Equiv.swap k c) hκ
    rw [hsR, hsL, hsU]
    simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using hn
  · rw [hsL, hsU]
    exact hshape.submatrix (Equiv.swap k r) (Equiv.swap k c) hρ hκ
  · intro i j hj
    rw [hsL]
    exact hL ((Equiv.swap k r) i) j hj
  · intro i j hi
    rw [hsU]
    exact hU i ((Equiv.swap k c) j) hi
  · intro i j hj
    rw [hsL]
    exact hbound ((Equiv.swap k r) i) j hj

/-- An actual policy step advances rounded factors for the input permuted by its actual
reported histories. This applies to singular inputs because positive quality forces a zero
pivot's entire active column to vanish before the zero-safe step skips its division. -/
theorem pivotedStepSpec_rounded {M : Machine K} {dec : K → ℝ} {u quality : ℝ}
    {bound : ℕ} {fixedColumns : Bool} (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hone : dec (M.lit 1) = 1) (hquality : 0 < quality) (hquality₁ : quality ≤ 1)
    (A : Matrix (Fin N) (Fin N) ℝ) (p q : Fin N → Fin N) (k : Fin N)
    {τ : Tape K} {rs ls us rs' ls' us' : List K} {rword cword : K}
    (hpost : (pivotedStepSpec M dec quality bound fixedColumns).post [N, k.val] τ
      [rs, ls, us] [rs', ls', us', [rword], [cword]])
    (hprefix : u < 1 → IsLURoundingPrefix u k.val
      (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val))
      (decodeMatrix dec N N rs) (decodeMatrix dec N N ls) (decodeMatrix dec N N us))
    (hshape : IsLUTriangularPrefix k.val (decodeMatrix dec N N ls) (decodeMatrix dec N N us))
    (hL : ∀ i j : Fin N, k.val ≤ j.val → decodeMatrix dec N N ls i j = 0)
    (hU : ∀ i j : Fin N, k.val ≤ i.val → decodeMatrix dec N N us i j = 0)
    (hbound : ∀ i j : Fin N, j.val < k.val →
      |decodeMatrix dec N N ls i j| ≤ (1 + u) / quality)
    {R L U : ℕ × ℕ} {s : Store K}
    (hR' : s.readBlock R.1 R.2 (N * N) = some rs')
    (hL' : s.readBlock L.1 L.2 (N * N) = some ls')
    (hU' : s.readBlock U.1 U.2 (N * N) = some us') :
    ∃ r c : Fin N, k ≤ r ∧ k ≤ c ∧ dec rword = r.val ∧ dec cword = c.val ∧
      (fixedColumns = true → c = k) ∧
      IsRoundedFactorPrefix dec u quality
        (A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
          (luPivotPermutation (Function.update q k c) (k.val + 1)))
        (k.val + 1) R L U s := by
  obtain ⟨r, c, hkr, hkc, hdr, hdc, hfixed, hchoice, rs₀, ls₀, us₀, hswap, hstep⟩ := hpost
  obtain ⟨hn, hshape₀, hL₀, hU₀, hbound₀⟩ :=
    roundedPrefix_swaps k r c hkr hkc hswap hprefix hshape hL hU hbound
  obtain ⟨hsR, -, -⟩ := pivotSwapsSpec_decode (dec := dec) k r c hswap
  have hquality₀ : ∀ i : Fin N, k ≤ i → quality * |decodeMatrix dec N N rs₀ i k| ≤
      |decodeMatrix dec N N rs₀ k k| := by
    intro i hi
    rw [hsR]
    have hh := hchoice ((Equiv.swap k r) i) (Fin.le_swap_apply_of_le k r hkr i hi)
    simpa only [Matrix.submatrix_apply, Equiv.swap_apply_left, decodeMatrix_apply] using hh
  have hnext := IsRoundedFactorPrefix.of_step hM hu hone hquality hquality₁ k hstep
    hn hshape₀ hL₀ hU₀ hbound₀ hquality₀ hR' hL' hU'
  refine ⟨r, c, hkr, hkc, hdr, hdc, fun hf => Fin.ext (hfixed hf), ?_⟩
  simpa only [submatrix_luPivotPermutation_update] using hnext

end NLAlib.LU
