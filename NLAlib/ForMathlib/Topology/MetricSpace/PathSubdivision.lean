/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Subdivisions subordinate to an open cover

Uniform meshes on the unit interval and its square refine open covers. Upstream candidate for
Mathlib.

A mesh smaller than a Lebesgue number of the pulled-back cover suffices, by Mathlib’s
`lebesgue_number_lemma_of_metric`. The proofs adapt the original NLAlib atlas at commit
`77514ce`.

## Main results

* `exists_uniform_grid_subordinate_open_cover`.
-/
@[expose] public section

section

open Set Metric

/-- Every node of the uniform subdivision lies in the closed unit interval. -/
theorem Nat.cast_div_mem_Icc {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    (i : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact ⟨div_nonneg (Nat.cast_nonneg i) hn'.le,
    (div_le_one hn').mpr (by exact_mod_cast hi)⟩

private theorem uniformSubdivision_cell_subset_ball {n i : ℕ} {δ : ℝ}
    (hδ : 1 / (n : ℝ) < δ) :
    Icc ((i : ℝ) / n) ((i + 1 : ℝ) / n) ⊆ ball ((i : ℝ) / n) δ := by
  intro t ht
  rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
  apply lt_of_le_of_lt _ hδ
  have htop : t ≤ (i : ℝ) / n + 1 / n := by simpa only [add_div] using ht.2
  linarith

/-- Let $\psi$ be a continuous map from the real plane to a topological space. For any open
cover of $\psi([0,1]^2)$ there is a positive integer $n$ such that the image of each closed
cell of the uniform $n\times n$ grid lies in a single member of the cover. -/
theorem exists_uniform_grid_subordinate_open_cover
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (ψ : ℝ × ℝ → X) (hψ : Continuous ψ)
    (U : ι → Set X) (hU : ∀ j, IsOpen (U j))
    (hcover : ψ '' Icc (0 : ℝ × ℝ) 1 ⊆ ⋃ j, U j) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < n, ∀ k < n, ∃ j,
      ∀ t ∈ Icc (((i : ℝ) / n), ((k : ℝ) / n))
        (((i + 1 : ℝ) / n), ((k + 1 : ℝ) / n)), ψ t ∈ U j := by
  have hpre : Icc (0 : ℝ × ℝ) 1 ⊆ ⋃ j, ψ ⁻¹' U j := by
    intro t ht
    simpa only [mem_iUnion, mem_preimage] using hcover (mem_image_of_mem ψ ht)
  obtain ⟨δ, hδ, hmesh⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun j => hψ.isOpen_preimage _ (hU j)) hpre
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hm' : 1 / ((m + 1 : ℕ) : ℝ) < δ := by simpa only [Nat.cast_add, Nat.cast_one] using hm
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  intro i hi k hk
  have hi' := Nat.cast_div_mem_Icc (Nat.succ_pos m) hi.le
  have hk' := Nat.cast_div_mem_Icc (Nat.succ_pos m) hk.le
  obtain ⟨j, hj⟩ := hmesh (((i : ℝ) / (m + 1 : ℕ)), ((k : ℝ) / (m + 1 : ℕ)))
    ⟨⟨hi'.1, hk'.1⟩, ⟨hi'.2, hk'.2⟩⟩
  refine ⟨j, fun t ht => hj ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨mem_ball.mp (uniformSubdivision_cell_subset_ball hm' ⟨ht.1.1, ht.2.1⟩),
    mem_ball.mp (uniformSubdivision_cell_subset_ball hm' ⟨ht.1.2, ht.2.2⟩)⟩

end
