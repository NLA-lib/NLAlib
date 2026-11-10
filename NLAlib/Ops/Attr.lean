/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Attr.Register

/-!
# The simp set of `store_simp`

`storeNF` is the simp set that the tactic `store_simp` uses besides the store lemmas. A catalog
file tags the lemmas that unfold the shapes of its contracts (the lengths of the blocks an
operation reads and writes), so that the obligations of the call rules are computed.

## Main results

* `storeNF`: the simp attribute. A catalog file tags its contracts in operand form with it, so
  that their shapes and relations are unfolded at a call.
* `admNF`: the simp attribute of the predicates on admitted operands.
-/

@[expose] public section

/-- The simp set of `store_simp`: unfolding lemmas of the shapes of contracts. -/
register_simp_attr storeNF

/-- The simp set that unfolds the predicates on admitted operands of the catalog, for the side
goals of the call rule (`wp_side`). -/
register_simp_attr admNF

/-- The simp set of `count_eval`: the costs of the operations in the profiles, so that a
pushed-forward count evaluates to a closed form. -/
register_simp_attr countNF
