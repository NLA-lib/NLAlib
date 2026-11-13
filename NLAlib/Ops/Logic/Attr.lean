/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Basic

/-!
# Simp sets of the logic layer

* `fpNF`: footprints to arithmetic (`NLAlib.Ops.Store.inBlock`, `NLAlib.Ops.Store.inBuf`, `⊔`,
  `≤`, the blocks of a call, matrix layouts). Used by `fp_mem`, `fp_sub`, `disjoint`.
* `idxNF`: index arithmetic: quotients and remainders of row-major and column-major offsets,
  products of a bound by a size. Used by `idx`.
* `decodeNF`: stored blocks to the vectors and matrices of layer 1 (`vec` of a slice). Used by
  `decode`.

## Main results

The three simp attributes above.
-/

@[expose] public section

/-- Footprints to arithmetic, for `fp_mem`, `fp_sub` and `disjoint`. -/
register_simp_attr fpNF

/-- Index arithmetic, for `idx`. -/
register_simp_attr idxNF

/-- Stored blocks to vectors and matrices, for `decode`. -/
register_simp_attr decodeNF
