/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotSwaps
public import NLAlib.Matrix.Factorizations.LU.PivotedPrefix
public import NLAlib.Matrix.Factorizations.LU.StepCorrect

/-!
# Canonical prefixes after actual exchanges and elimination

The canonical part of a pivoted step is independent of its pivot policy. Actual row/column
exchanges transport the residual and committed factor prefixes; the shared total scalar step
then advances all three. Quality and fixed-scale policy proofs consume this same word bridge.

## Main results

* `NLAlib.LU.pivotSwapsSpec_stepSpec_prefix`: exchanged words give next canonical prefixes.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} [Inhabited K] {N : ℕ}

/-- Actual exchanges followed by the total scalar step advance the canonical residual and
factor prefixes for the source with those current-position exchanges. No column-quality,
nonzero-pivot or already-successful execution premise is required. -/
theorem pivotSwapsSpec_stepSpec_prefix {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) (B : Matrix (Fin N) (Fin N) ℝ) (k r c : Fin N)
    (hkr : k ≤ r) (hkc : k ≤ c) {τ : Tape K}
    {rs ls us rs₀ ls₀ us₀ rs' ls' us' : List K}
    (hswap : (pivotSwapsSpec (K := K)).post [N, k.val, r.val, c.val] τ
      [rs, ls, us] [rs₀, ls₀, us₀])
    (hstep : (stepSpec M dec).post [N, k.val] τ [rs₀, ls₀, us₀] [rs', ls', us'])
    (hr : ∀ i j : Fin N, decodeMatrix dec N N rs i j = gaussState B k.val i j)
    (hl : ∀ i j : Fin N, decodeMatrix dec N N ls i j =
      if j.val < k.val then luLower B i j else 0)
    (hu : ∀ i j : Fin N, decodeMatrix dec N N us i j =
      if i.val < k.val then luUpper B i j else 0) :
    let C := B.submatrix (Equiv.swap k r) (Equiv.swap k c)
    (∀ i j : Fin N, decodeMatrix dec N N rs' i j = gaussState C (k.val + 1) i j) ∧
      (∀ i j : Fin N, decodeMatrix dec N N ls' i j =
        if j.val < k.val + 1 then luLower C i j else 0) ∧
      (∀ i j : Fin N, decodeMatrix dec N N us' i j =
        if i.val < k.val + 1 then luUpper C i j else 0) := by
  let ρ := Equiv.swap k r
  let κ := Equiv.swap k c
  have hρ := Fin.swap_apply_of_lt_of_le k r hkr
  have hκ := Fin.swap_apply_of_lt_of_le k c hkc
  obtain ⟨hsR, hsL, hsU⟩ := pivotSwapsSpec_decode (dec := dec) k r c hswap
  have hfg := factorPrefix_submatrix k.val ρ κ hρ hκ hl hu
  have hr₀ : ∀ i j : Fin N, decodeMatrix dec N N rs₀ i j =
      gaussState (B.submatrix ρ κ) k.val i j := by
    intro i j
    rw [hsR, gaussState_submatrix_left_right B ρ κ k.val hρ hκ]
    exact hr (ρ i) (κ j)
  have hl₀ : ∀ i j : Fin N, decodeMatrix dec N N ls₀ i j =
      if j.val < k.val then luLower (B.submatrix ρ κ) i j else 0 := by
    intro i j
    rw [hsL]
    exact hfg.1 i j
  have hu₀ : ∀ i j : Fin N, decodeMatrix dec N N us₀ i j =
      if i.val < k.val then luUpper (B.submatrix ρ κ) i j else 0 := by
    intro i j
    rw [hsU]
    exact hfg.2 i j
  exact stepSpec_prefix hM (B.submatrix ρ κ) k hstep hr₀ hl₀ hu₀

end NLAlib.LU
