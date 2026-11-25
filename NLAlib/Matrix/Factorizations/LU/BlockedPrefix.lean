/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Prefix
public import NLAlib.Matrix.Factorizations.LUBlocked

/-!
# Stored prefixes inside a deferred LU panel

The copied residual agrees with Gaussian elimination except in the deferred trailing square.
The same initialized factor prefixes as ordinary LU are retained. This is a stored loop
invariant, with actual word witnesses and no execution or factorization premise.

## Main definitions

* `NLAlib.LU.IsPanelPrefix`: the deferred residual and committed factor prefixes.

## Main results

* `NLAlib.LU.IsFactorPrefix.toPanelPrefix`: enter a panel from a Gaussian boundary state.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} {N : ℕ}

/-- Actual residual and factor words at a panel iteration. Only the bottom-right square is
retained from panel entry; completed factor columns and rows are canonical. -/
def IsPanelPrefix (dec : K → ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (start stop k : ℕ) (R L U : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ rw lw uw : ℕ → ℕ → K,
    s.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw ∧
    s.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw ∧
    s.HoldsMat ⟨U.1, U.2, N, N, N⟩ uw ∧
    (∀ i j : Fin N, dec (rw i j) = luPanelState A start stop k i j) ∧
    (∀ i j : Fin N, dec (lw i j) = if j.val < k then luLower A i j else 0) ∧
    (∀ i j : Fin N, dec (uw i j) = if i.val < k then luUpper A i j else 0)

/-- Panel entry is exactly the complete Gaussian residual at the same factor-prefix boundary. -/
theorem IsFactorPrefix.toPanelPrefix {dec : K → ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {start : ℕ} (stop : ℕ) {R L U : ℕ × ℕ} {s : Store K}
    (h : IsFactorPrefix dec A start R L U s) :
    IsPanelPrefix dec A start stop start R L U s := by
  obtain ⟨rw, lw, uw, hR, hL, hU, hres, hlo, hup⟩ := h
  refine ⟨rw, lw, uw, hR, hL, hU, ?_, hlo, hup⟩
  intro i j
  rw [luPanelState_start]
  exact hres i j

end NLAlib.LU
