/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Nets of the unit sphere of a finite-dimensional normed space

The volumetric bound on the size of a separated subset of the unit sphere of a finite-dimensional
real normed space, and the finite `ε`-net of the sphere that it gives. Upstream candidates for
`Mathlib.Topology.MetricSpace.CoveringNumbers`, or for a file next to it, since the proof compares
Haar measures of balls.

## Main results

* `Metric.card_le_of_subset_sphere_of_isSeparated`: an `ε`-separated finite subset of the unit
  sphere has at most `(1 + 2 / ε) ^ d` points, `d` the real dimension.
* `Metric.exists_finset_isCover_sphere_card_le`: the unit sphere has an `ε`-net of unit vectors
  with at most `(1 + 2 / ε) ^ d` points.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace Metric

/-- **The volumetric packing bound.** An `ε`-separated finite subset of the unit sphere of a
finite-dimensional real normed space of dimension `d` has at most `(1 + 2 / ε) ^ d` points, since
the disjoint balls of radius `ε / 2` about its points lie in the ball of radius `1 + ε / 2`.
[Vershynin2018, Corollary 4.2.13]. -/
theorem card_le_of_subset_sphere_of_isSeparated {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ε : ℝ≥0} (hε : 0 < ε) (S : Finset E)
    (hS : (S : Set E) ⊆ sphere 0 1) (hsep : IsSeparated ε (S : Set E)) :
    (S.card : ℝ) ≤ (1 + 2 / (ε : ℝ)) ^ Module.finrank ℝ E := by
  borelize E
  have hε' : (0 : ℝ) < ε := mod_cast hε
  set d := Module.finrank ℝ E
  set μ : Measure E := Measure.addHaar
  set V := μ (ball 0 1)
  have hV0 : V ≠ 0 := (measure_ball_pos μ (0 : E) one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hdisj : (S : Set E).PairwiseDisjoint fun x => ball x ((ε : ℝ) / 2) := by
    intro x hx y hy hxy
    have h : ((ε : ℝ≥0) : ENNReal) < edist x y := hsep hx hy hxy
    rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at h
    exact ball_disjoint_ball (by linarith)
  have hsub : (⋃ x ∈ S, ball x ((ε : ℝ) / 2)) ⊆ ball (0 : E) (1 + ε / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [mem_ball, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hz
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 (hS hx)
    linarith [norm_le_insert' z x]
  have hmeas := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hmeas
  simp only [Measure.addHaar_ball_of_pos μ _ (by positivity : (0 : ℝ) < ε / 2),
    Measure.addHaar_ball_of_pos μ _ (by positivity : (0 : ℝ) < 1 + ε / 2),
    Finset.sum_const, nsmul_eq_mul] at hmeas
  rw [← mul_assoc] at hmeas
  have h2 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 hmeas
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hpos : (0 : ℝ) < ((ε : ℝ) / 2) ^ d := by positivity
  rw [← le_div_iff₀ hpos, ← div_pow] at h2
  calc (S.card : ℝ) ≤ ((1 + (ε : ℝ) / 2) / ((ε : ℝ) / 2)) ^ d := h2
    _ = (1 + 2 / (ε : ℝ)) ^ d := by
      congr 1
      field_simp
      ring

/-- **A finite net of the unit sphere.** A finite-dimensional real normed space of dimension `d`
has a finite `ε`-net of its unit sphere, made of unit vectors, with at most `(1 + 2 / ε) ^ d`
points: a separated subset of the sphere of largest size.
[Vershynin2018, Corollary 4.2.13]. -/
theorem exists_finset_isCover_sphere_card_le (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N : Finset E, (N : Set E) ⊆ sphere 0 1 ∧ IsCover ε (sphere (0 : E) 1) (N : Set E) ∧
      (N.card : ℝ) ≤ (1 + 2 / (ε : ℝ)) ^ Module.finrank ℝ E := by
  classical
  set b : ℝ := (1 + 2 / (ε : ℝ)) ^ Module.finrank ℝ E
  have htop : packingNumber ε (sphere (0 : E) 1) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENat.natCast_ne_top ⌊b⌋₊) ?_
    refine iSup_le fun C => iSup_le fun hC => iSup_le fun hsep => ?_
    by_contra hlt
    obtain ⟨T, hTC, hT⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt (not_le.1 hlt))
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe hT
    have hcard := card_le_of_subset_sphere_of_isSeparated hε hTfin.toFinset
      (by simpa using hTC.trans hC) (by simpa using hsep.subset hTC)
    have hTcard : hTfin.toFinset.card = ⌊b⌋₊ + 1 := by
      rw [← Set.ncard_eq_toFinset_card T hTfin, Set.ncard, hT]
      rfl
    rw [hTcard] at hcard
    push_cast at hcard
    linarith [Nat.lt_floor_add_one b]
  have hfin : (maximalSeparatedSet ε (sphere (0 : E) 1)).Finite :=
    Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet htop]; exact htop)
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · simpa using maximalSeparatedSet_subset
  · simpa using isCover_maximalSeparatedSet htop
  · exact card_le_of_subset_sphere_of_isSeparated hε _ (by simpa using maximalSeparatedSet_subset)
      (by simpa using isSeparated_maximalSeparatedSet)

end Metric
