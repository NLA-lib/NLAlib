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
-/

public section

/-- The simp set of `store_simp`: unfolding lemmas of the shapes of contracts. -/
register_simp_attr storeNF
