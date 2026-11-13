/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Layout
public import NLAlib.ForMathlib.Algebra.BigOperators.Intervals

/-!
# Arena storage for spectral bisection levels

A level contains `n` slots, each reserving `2 * n` scalar words. A node of size `k` at slot
`lo` owns `k` slots; its complex square matrix uses only `2 * k * k` of these words. The
column-range rules of `Ops.MatLayout` prove disjointness from the mathematical slot intervals,
without a program-specific frame judgment or an induction through every matrix instruction.

The weighted-cost rule uses the same disjoint slot intervals. It applies to any monotone
superadditive cost of a node size, including the cost of matrix multiplication or QR.

## Main results

* `NLAlib.SpectralBisection.nodeFp_le_level`: a node payload lies in its level.
* `NLAlib.SpectralBisection.disj_nodeFp`: disjoint slot intervals give disjoint node payloads.
* `NLAlib.SpectralBisection.pairwise_disj_nodeFp`: one slot invariant frames every node payload.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The scalar-word slot layout of level `d` in a complex-matrix arena for root size `n`. -/
def levelLayout (buf n d : ℕ) : MatLayout :=
  ⟨buf, 2 * (n * n) * d, 2 * n, n, 2 * n⟩

/-- The scalar-word payload of the square complex matrix of a size-`k` node at slot `lo`. -/
def nodeFp (buf n d lo k : ℕ) : Fp :=
  Store.inBlock buf ((levelLayout buf n d).off + lo * (2 * n)) (2 * (k * k))

/-- A node matrix uses at most the `k` slots reserved for it when its size is at most `n`. -/
theorem nodeFp_le_slots (buf n d lo k : ℕ) (hk : k ≤ n) :
    nodeFp buf n d lo k ≤
      Store.inBlock buf ((levelLayout buf n d).off + lo * (2 * n)) (k * (2 * n)) := by
  apply Fp.inBlock_le_inBlock le_rfl
  have h := Nat.mul_le_mul_left (2 * k) hk
  nlinarith

/-- The payload of a node whose slot interval is inside `[0, n)` lies in the level arena. -/
theorem nodeFp_le_level (buf n d lo k : ℕ) (hk : lo + k ≤ n) :
    nodeFp buf n d lo k ≤
      Store.inBlock buf ((levelLayout buf n d).off) (2 * (n * n)) := by
  refine (nodeFp_le_slots buf n d lo k (by omega)).trans ?_
  apply Fp.inBlock_le_inBlock (by omega)
  have h := Nat.mul_le_mul_right (2 * n) hk
  nlinarith

/-- A node at level `d` lies in an arena containing `D` levels whenever `d < D`. -/
theorem nodeFp_le_arena (buf n d lo k D : ℕ) (hk : lo + k ≤ n) (hd : d < D) :
    nodeFp buf n d lo k ≤ Store.inBlock buf 0 (2 * (n * n) * D) := by
  refine (nodeFp_le_level buf n d lo k hk).trans ?_
  apply Fp.inBlock_le_inBlock (Nat.zero_le _)
  simpa only [levelLayout, Nat.zero_add] using Idx.mul_add_le_mul' hd (2 * (n * n))

/-- Nonoverlapping slot ranges in one level have disjoint complex matrix payloads. -/
theorem disj_nodeFp (buf n d lo k lo' k' : ℕ) (hk : k ≤ n) (hk' : k' ≤ n)
    (hsep : lo + k ≤ lo') :
    Fp.Disj (nodeFp buf n d lo k) (nodeFp buf n d lo' k') :=
  ((levelLayout buf n d).disj_of_cols hsep).mono
    (nodeFp_le_slots buf n d lo k hk) (nodeFp_le_slots buf n d lo' k' hk')

/-- Payloads in distinct ordered levels are disjoint, regardless of their node slots. -/
theorem disj_nodeFp_of_lt (buf n d lo k d' lo' k' : ℕ) (hk : lo + k ≤ n)
    (hk' : lo' + k' ≤ n) (hd : d < d') :
    Fp.Disj (nodeFp buf n d lo k) (nodeFp buf n d' lo' k') := by
  refine (Fp.disj_inBlock_of_le ?_).mono
    (nodeFp_le_level buf n d lo k hk) (nodeFp_le_level buf n d' lo' k' hk')
  simpa only [levelLayout, Nat.zero_add] using Idx.mul_add_le_mul' hd (2 * (n * n))

/-- A zero-size node has no matrix payload. -/
theorem nodeFp_zero (buf n d lo : ℕ) : nodeFp buf n d lo 0 = ⊥ := by
  funext b x
  apply propext
  simp only [nodeFp, Fp.inBlock_apply, Fp.bot_apply, Nat.mul_zero, Nat.add_zero]
  exact ⟨fun h => (Nat.not_lt_of_ge h.2.1) h.2.2, False.elim⟩

/-- Disjoint mathematical slot intervals give disjoint matrix payloads, including empty nodes. -/
theorem disj_nodeFp_of_disjoint (buf n d lo k lo' k' : ℕ) (hk : k ≤ n) (hk' : k' ≤ n)
    (hdisj : Disjoint (Finset.Ico lo (lo + k)) (Finset.Ico lo' (lo' + k'))) :
    Fp.Disj (nodeFp buf n d lo k) (nodeFp buf n d lo' k') := by
  by_cases hzero : k = 0
  · subst k
    rw [nodeFp_zero]
    exact Fp.disj_bot_left _
  by_cases hzero' : k' = 0
  · subst k'
    rw [nodeFp_zero]
    exact Fp.disj_bot_right _
  have hsep : lo + k ≤ lo' ∨ lo' + k' ≤ lo := by
    by_contra h
    push Not at h
    have hleft : max lo lo' ∈ Finset.Ico lo (lo + k) :=
      Finset.mem_Ico.mpr ⟨le_max_left _ _, by omega⟩
    have hright : max lo lo' ∈ Finset.Ico lo' (lo' + k') :=
      Finset.mem_Ico.mpr ⟨le_max_right _ _, by omega⟩
    exact Finset.disjoint_left.mp hdisj hleft hright
  exact hsep.elim (disj_nodeFp buf n d lo k lo' k' hk hk')
    (fun h => (disj_nodeFp buf n d lo' k' lo k hk' hk h).symm)

/-- A level's mathematical partition invariant frames all its matrix payloads simultaneously. -/
theorem pairwise_disj_nodeFp {ι : Type*} (s : Finset ι) (buf n d : ℕ) {lo k : ι → ℕ}
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => Finset.Ico (lo i) (lo i + k i))
    (hk : ∀ i ∈ s, lo i + k i ≤ n) :
    (s : Set ι).Pairwise fun i j => Fp.Disj (nodeFp buf n d (lo i) (k i))
      (nodeFp buf n d (lo j) (k j)) := by
  intro i hi j hj hij
  exact disj_nodeFp_of_disjoint buf n d (lo i) (k i) (lo j) (k j)
    (by have := hk i hi; omega) (by have := hk j hj; omega) (hdisj hi hj hij)

end NLAlib.SpectralBisection
