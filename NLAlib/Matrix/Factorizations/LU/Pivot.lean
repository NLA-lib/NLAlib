/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Orth
public import NLAlib.Ops.Routine
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Matrix.Factorizations.LUQualityPivoting

/-!
# Stored pivot choices for Gaussian elimination

A selector returns two actual current-position indices. The selected entry has a declared
fraction of every active entry in its column. Positive fractions imply zero-column
compatibility, so the factorization driver covers singular matrices. First-tie and stronger
policy-specific properties belong to each selector's own specification.

## Main definitions

* `NLAlib.LU.choiceSpec`: bounded actual row and column indices with column quality.

## Main results

The common pivoted driver consumes this specification through the selector's judgment.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

/-- The fixed interface of a pivot-selector body. The tree is supplied before any matrix
or dimensions, and contains actual scalar operations and queries. This wrapper lets the
common factorization driver frame selectors through one declared routine interface. -/
def choiceRoutine {Op Tst : Type} (body : Stmt Op Tst) : Routine Op Tst :=
  routine% [n, k] (R : n * n) → (p : 2) := body

variable {K : Type} [Inhabited K]

/-- The selected current-position row and column lie in the active square and decode exactly
from the two output words. The selected magnitude dominates `quality` times every active
entry of its column. The matrix order is bounded by the exact natural-literal allowance. -/
def choiceSpec (dec : K → ℝ) (quality : ℝ) (bound : ℕ)
    (fixedColumns : Bool := false) : Routine.Spec K :=
  spec% [n, k] (rs) → ([r, c]) requires (k < n ∧ n ≤ bound) ensures
    ∃ row col : Fin n, k ≤ row.val ∧ k ≤ col.val ∧ dec r = row.val ∧ dec c = col.val ∧
      (fixedColumns = true → col.val = k) ∧
      ∀ i : Fin n, k ≤ i.val →
        quality * |dec (vec rs (col.val * n + i.val))| ≤
          |dec (vec rs (col.val * n + row.val))|

end NLAlib.LU
