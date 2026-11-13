/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Approximation by strictly decreasing finite sequences

Perturb finite weakly decreasing data to distinct coordinates with quantitative control.
Upstream candidate for Mathlib.

The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `Fin.exists_strictAnti_tendsto_mem_Icc`.
-/
@[expose] public section

section

open Filter Set

open scoped Topology

namespace Fin

/-- A finite antitone list in a nondegenerate compact interval is the limit of
strictly antitone lists in that same interval. No separation assumption is imposed
on the original list, and the empty list is included. -/
theorem exists_strictAnti_tendsto_mem_Icc {n : ℕ} {b : Fin n → ℝ}
    (hb : Antitone b) {l u : ℝ} (hlu : l < u) (hmem : ∀ i, b i ∈ Icc l u) :
    ∃ v : ℕ → Fin n → ℝ, (∀ k, StrictAnti (v k)) ∧
      (∀ k i, v k i ∈ Icc l u) ∧ Tendsto v atTop (𝓝 b) := by
  let δ : ℝ := (u - l) / ((n : ℝ) + 1)
  let c : Fin n → ℝ := fun i => u - δ * ((i : ℝ) + 1)
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr hlu) hden
  have hδeq : δ * ((n : ℝ) + 1) = u - l := by
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  have hc : StrictAnti c := by
    intro i j hij
    have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    dsimp [c]
    nlinarith
  have hcmem : ∀ i, c i ∈ Icc l u := by
    intro i
    have hile : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have := (Nat.cast_le.mpr (Nat.le_of_lt i.isLt) : (i : ℝ) ≤ n)
      linarith
    have hnonneg : 0 ≤ (i : ℝ) + 1 := by positivity
    dsimp [c]
    constructor <;> nlinarith
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεle (k : ℕ) : ε k ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
  let v : ℕ → Fin n → ℝ := fun k i => (1 - ε k) * b i + ε k * c i
  refine ⟨v, ?_, ?_, ?_⟩
  · intro k i j hij
    exact add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hb hij.le) (sub_nonneg.mpr (hεle k)))
      (mul_lt_mul_of_pos_left (hc hij) (hεpos k))
  · intro k i
    have heps : 0 ≤ 1 - ε k := sub_nonneg.mpr (hεle k)
    have hbmem := hmem i
    have hcmemi := hcmem i
    have h₁ := mul_nonneg heps (sub_nonneg.mpr hbmem.1)
    have h₂ := mul_nonneg (hεpos k).le (sub_nonneg.mpr hcmemi.1)
    have h₃ := mul_nonneg heps (sub_nonneg.mpr hbmem.2)
    have h₄ := mul_nonneg (hεpos k).le (sub_nonneg.mpr hcmemi.2)
    dsimp [v]
    constructor <;> nlinarith
  · apply tendsto_pi_nhds.mpr
    intro i
    have heps : Tendsto ε atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [v, sub_zero, one_mul, zero_mul, add_zero] using
      (((tendsto_const_nhds (x := (1 : ℝ))).sub heps).mul_const (b i)).add
        (heps.mul_const (c i))

end Fin

end
