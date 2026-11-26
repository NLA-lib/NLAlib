/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Step
public import NLAlib.Matrix.Factorizations.LU.ColumnCorrect

/-!
# Canonical prefixes after a stored elimination step

The actual word postconditions for factor materialization and guarded Schur elimination
advance the decoded canonical prefix together. This consumer is shared by the unpivoted
and pivoted loop invariants, and needs no nonzero-pivot assumption.

## Main results

* `NLAlib.LU.stepSpec_prefix`: the actual residual and factor words extend one prefix.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} [Inhabited K] {N : ℕ} {M : Machine K} {dec : K → ℝ}

/-- Exact arithmetic turns the guarded step's actual word postcondition into the next
Gaussian residual and canonical factor prefixes, including a zero pivot. -/
theorem stepSpec_prefix (hM : ExactModel dec M)
    {rs ls us rs' ls' us' : List K} {τ : Tape K} (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N)
    (hpost : (stepSpec M dec).post [N, k.val] τ [rs, ls, us] [rs', ls', us'])
    (hres : ∀ i j : Fin N, decodeMatrix dec N N rs i j = gaussState A k.val i j)
    (hlo : ∀ i j : Fin N,
      decodeMatrix dec N N ls i j = if j.val < k.val then luLower A i j else 0)
    (hup : ∀ i j : Fin N,
      decodeMatrix dec N N us i j = if i.val < k.val then luUpper A i j else 0) :
    (∀ i j : Fin N, decodeMatrix dec N N rs' i j = gaussState A (k.val + 1) i j) ∧
    (∀ i j : Fin N,
      decodeMatrix dec N N ls' i j = if j.val < k.val + 1 then luLower A i j else 0) ∧
    (∀ i j : Fin N,
      decodeMatrix dec N N us' i j = if i.val < k.val + 1 then luUpper A i j else 0) := by
  obtain ⟨hcol, hschur⟩ := hpost
  have hfac := materializeColumnSpec_prefix hM A k hcol hres hlo hup
  have he : decodeMatrix dec N N rs = gaussState A k.val := Matrix.ext hres
  have hr := schurStepTotalSpec_decode hM k hschur
  refine ⟨?_, hfac.1, hfac.2⟩
  intro i j
  rw [hr, he, gaussState_succ A k.isLt]

end NLAlib.LU
