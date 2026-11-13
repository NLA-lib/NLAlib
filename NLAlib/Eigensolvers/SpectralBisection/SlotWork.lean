/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.SlotNodes
public import NLAlib.ForMathlib.Algebra.BigOperators.Intervals

/-!
# Kernel work across the mathematical slot partition

Every level occupies disjoint root-slot intervals, including empty lookup slots. A monotone
superadditive size cost therefore charges at most the root cost per level. This is a bound on
the mathematical sizes selected by the stored-size invariant, not on the static manifest's
union of all possible query answers.

## Main results

* `NLAlib.SpectralBisection.sum_slotWork_le`: one root-size kernel cost per level.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

/-- For a monotone superadditive natural-valued cost, all canonical slot sizes at a fixed
depth cost at most the root size. Zero-sized fallback slots and an empty root are included. -/
theorem sum_slotWork_le {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ)
    (R0 eps beta : K) (ell : ℕ) (A : Matrix (Fin n) (Fin n) (K × K)) (d : ℕ)
    {T : ℕ → ℕ} (hT : Monotone T) (hadd : ∀ a b, T a + T b ≤ T (a + b)) :
    ∑ lo ∈ Finset.range n,
      T ((nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo).k) ≤ T n := by
  apply Finset.sum_apply_le_of_pairwiseDisjoint_Ico (off := id) _ hT hadd
  · intro lo hlo lo' hlo' hne
    exact disjoint_nodeAtSlot_intervals F n fuel R0 eps beta ell A d lo lo' hne
  · intro lo hlo
    dsimp only [id]
    have hk := nodeAtSlot_k_le F n fuel R0 eps beta ell A d lo
    have hln := Finset.mem_range.mp hlo
    omega

end NLAlib.SpectralBisection
