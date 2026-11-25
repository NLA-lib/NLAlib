/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.Embedding

/-!
# Values of suffix embeddings

The existing tail embedding `Fin.natAdd_castLEEmb` includes `Fin (n-k)` into `Fin n`.
An element of its domain supplies the bound needed to identify the displacement with `k`;
no separate bound on the starting position is needed for an empty suffix.
Upstream candidate for `Mathlib.Data.Fin.Embedding`.

## Main results

* `Fin.val_natAdd_castLEEmb_sub`: the natural value of a suffix index shifted into its parent.
-/

@[expose] public section

namespace Fin

/-- Including an index of a truncated suffix into its parent adds the suffix's starting
position to that index. Existence of the suffix index itself ensures the required bound. -/
theorem val_natAdd_castLEEmb_sub {n : ℕ} (k : ℕ) (h : n - k ≤ n) (i : Fin (n - k)) :
    (natAdd_castLEEmb h i).val = k + i.val := by
  have hk : k ≤ n := by have := i.isLt; omega
  change i.val + (n - (n - k)) = k + i.val
  rw [Nat.sub_sub_self hk, Nat.add_comm]

end Fin
