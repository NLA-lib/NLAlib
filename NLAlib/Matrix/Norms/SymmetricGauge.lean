/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Seminorm
public import Mathlib.Data.Finsupp.Basic
public import NLAlib.Matrix.Majorization.DoublyStochastic

/-!
# Symmetric gauge functions

A symmetric gauge function is a norm on finitely supported real sequences that is invariant under
permutations of the indices and under changes of sign of the entries. By von Neumann's theorem
these are exactly the functions `Φ` for which `A ↦ Φ (singular values of A)` is a unitarily
invariant norm, and one gauge gives such a norm on matrices of every shape at once; see
`NLAlib.Matrix.Norms.UnitarilyInvariant`.

The carrier is `ℕ →₀ ℝ`, the type of Mathlib's `LinearMap.singularValues`, and the structure
extends Mathlib's `Seminorm`. The `ℓ^q` and Ky Fan gauges are in
`NLAlib.Matrix.Norms.GaugeExamples`.

## Main definitions

* `NLAlib.SymmetricGauge`: the structure.

## Main results

* `NLAlib.SymmetricGauge.le_of_abs_le`: gauges are monotone in the absolute values.
* `NLAlib.SymmetricGauge.le_of_forall_sum_le`: gauges respect weak majorization (Fan dominance
  for sequences).
* `NLAlib.SymmetricGauge.apply_single_mul_abs_le`, `NLAlib.SymmetricGauge.le_apply_single_mul_sum`:
  every gauge lies between multiples of the `ℓ^∞` and `ℓ^1` gauges.
-/

@[expose] public section

namespace NLAlib

/-- A **symmetric gauge function**: a norm on finitely supported real sequences, invariant under
permutations of the indices and under taking absolute values of the entries. It extends Mathlib's
`Seminorm`, so the seminorm API applies (`map_zero`, `map_neg_eq_map`, `map_add_le_add`,
`map_smul_eq_mul`, `apply_nonneg`, `Φ.toSeminorm`).
[HornJohnson2013, Definition 7.4.7.1]; [Bhatia1997, §IV.1].
Port of `NLAlib.SymmetricGauge`, there on `ι → ℝ` for one finite index type. -/
structure SymmetricGauge extends Seminorm ℝ (ℕ →₀ ℝ) where
  /-- Definiteness. -/
  eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0
  /-- Invariance under permutations of the indices. -/
  map_equivMapDomain' : ∀ (σ : Equiv.Perm ℕ) x, toFun (x.equivMapDomain σ) = toFun x
  /-- Invariance under taking absolute values of the entries. -/
  map_abs' : ∀ x, toFun (x.mapRange abs abs_zero) = toFun x

/-- Two finitely supported sequences vanish beyond a common index. This is how statements about
gauges are reduced to vectors on `Fin N`. -/
theorem exists_forall_le_apply_eq_zero (x y : ℕ →₀ ℝ) :
    ∃ N, (∀ i, N ≤ i → x i = 0) ∧ ∀ i, N ≤ i → y i = 0 := by
  classical
  obtain ⟨N, hN⟩ := (x.support ∪ y.support).exists_nat_subset_range
  refine ⟨N, fun i hi => ?_, fun i hi => ?_⟩
  · by_contra hne
    exact (Finset.mem_range.mp
      (hN (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hne)))).not_ge hi
  · by_contra hne
    exact (Finset.mem_range.mp
      (hN (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hne)))).not_ge hi

/-- Extension by zero of a vector on `Fin N` to a finitely supported sequence. -/
private noncomputable def extendFin (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin N)).symm.toLinearMap

private theorem extendFin_apply_of_lt {N : ℕ} (z : Fin N → ℝ) {i : ℕ} (hi : i < N) :
    extendFin N z i = z ⟨i, hi⟩ := by
  exact Finsupp.mapDomain_apply Fin.val_injective
    ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin N)).symm z) ⟨i, hi⟩

private theorem extendFin_apply_of_le {N : ℕ} (z : Fin N → ℝ) {i : ℕ} (hi : N ≤ i) :
    extendFin N z i = 0 := by
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨j, rfl⟩
  exact j.isLt.not_ge hi

private theorem extendFin_comp_perm {N : ℕ} (z : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    extendFin N (z ∘ σ) =
      (extendFin N z).equivMapDomain (σ.extendDomain Fin.equivSubtype).symm := by
  ext i
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  obtain hi | hi := lt_or_ge i N
  · have h := σ.extendDomain_apply_image Fin.equivSubtype ⟨i, hi⟩
    have h' : σ.extendDomain Fin.equivSubtype i = (σ ⟨i, hi⟩ : ℕ) := h
    rw [h', extendFin_apply_of_lt _ hi, extendFin_apply_of_lt _ (σ ⟨i, hi⟩).isLt]
    rfl
  · rw [σ.extendDomain_apply_not_subtype Fin.equivSubtype (b := i) (not_lt.mpr hi),
      extendFin_apply_of_le _ hi, extendFin_apply_of_le _ hi]

namespace SymmetricGauge

instance : FunLike SymmetricGauge (ℕ →₀ ℝ) ℝ where
  coe Φ := Φ.toFun
  coe_injective := by
    rintro ⟨⟨⟨f, _, _, _⟩, _⟩, _, _, _⟩ ⟨⟨⟨g, _, _, _⟩, _⟩, _, _, _⟩ h
    obtain rfl : f = g := h
    rfl

instance : SeminormClass SymmetricGauge ℝ (ℕ →₀ ℝ) where
  map_zero Φ := Φ.map_zero'
  map_add_le_add Φ := Φ.add_le'
  map_neg_eq_map Φ := Φ.neg'
  map_smul_eq_mul Φ := Φ.smul'

variable (Φ : SymmetricGauge)

/-- Two gauges with the same values are equal. -/
@[ext]
theorem ext {Φ Ψ : SymmetricGauge} (h : ∀ x, Φ x = Ψ x) : Φ = Ψ :=
  DFunLike.ext Φ Ψ h

/-- The underlying seminorm has the same values. -/
@[simp]
theorem coe_toSeminorm : ⇑Φ.toSeminorm = Φ :=
  rfl

/-! ### Norm properties -/

/-- A gauge is definite. -/
@[simp]
theorem eq_zero_iff {x : ℕ →₀ ℝ} : Φ x = 0 ↔ x = 0 := by
  refine ⟨Φ.eq_zero_of_map_eq_zero' x, fun h => ?_⟩
  rw [h, map_zero]

/-- A gauge is a convex function. Port of `NLAlib.SymmetricGauge.convex_sublevel`. -/
theorem convexOn : ConvexOn ℝ Set.univ Φ := by
  exact Φ.toSeminorm.convexOn

/-! ### Symmetry -/

/-- A gauge is invariant under permutations of the indices. -/
@[simp]
theorem map_equivMapDomain (σ : Equiv.Perm ℕ) (x : ℕ →₀ ℝ) : Φ (x.equivMapDomain σ) = Φ x :=
  Φ.map_equivMapDomain' σ x

/-- A gauge depends only on the absolute values of the entries.
Port of `NLAlib.SymmetricGauge.value_abs`. -/
@[simp]
theorem map_abs (x : ℕ →₀ ℝ) : Φ (x.mapRange abs abs_zero) = Φ x :=
  Φ.map_abs' x

/-- Two sequences with the same absolute values have the same gauge. -/
theorem eq_of_abs_eq {x y : ℕ →₀ ℝ} (h : ∀ i, |x i| = |y i|) : Φ x = Φ y := by
  rw [← Φ.map_abs x, ← Φ.map_abs y]
  congr 1
  ext i
  simpa only [Finsupp.mapRange_apply] using h i

/-! ### Monotonicity and majorization -/

/-- Shrinking one entry in absolute value does not increase a gauge: the new sequence is a convex
combination of the old one and its reflection in that coordinate. -/
private theorem le_of_eq_off_of_abs_le {x y : ℕ →₀ ℝ} {a : ℕ} (h : ∀ i, i ≠ a → x i = y i)
    (ha : |x a| ≤ |y a|) : Φ x ≤ Φ y := by
  classical
  obtain hya | hya := eq_or_ne (y a) 0
  · have hxy : x = y := by
      ext i
      obtain rfl | hi := eq_or_ne i a
      · rw [hya, abs_zero] at ha
        rw [hya, abs_nonpos_iff.mp ha]
      · exact h i hi
    rw [hxy]
  · obtain ⟨t, ht⟩ : ∃ t, t = x a / y a := ⟨_, rfl⟩
    have hta : t * y a = x a := by rw [ht, div_mul_cancel₀ _ hya]
    have ht1 : |t| ≤ 1 := by
      rw [ht, abs_div]
      exact div_le_one_of_le₀ ha (abs_nonneg _)
    obtain ⟨ht_lo, ht_hi⟩ := abs_le.mp ht1
    have hΦ : Φ (y.update a (-(y a))) = Φ y := Φ.eq_of_abs_eq fun i => by
      obtain rfl | hi := eq_or_ne i a
      · rw [Finsupp.update_apply, if_pos rfl, abs_neg]
      · rw [Finsupp.update_apply, if_neg hi]
    have hx : x = ((1 + t) / 2) • y + ((1 - t) / 2) • y.update a (-(y a)) := by
      ext i
      rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.update_apply,
        smul_eq_mul, smul_eq_mul]
      obtain rfl | hi := eq_or_ne i a
      · rw [if_pos rfl, ← hta]
        ring
      · rw [if_neg hi, h i hi]
        ring
    calc Φ x = Φ (((1 + t) / 2) • y + ((1 - t) / 2) • y.update a (-(y a))) := by rw [← hx]
      _ ≤ Φ (((1 + t) / 2) • y) + Φ (((1 - t) / 2) • y.update a (-(y a))) :=
        map_add_le_add Φ _ _
      _ = (1 + t) / 2 * Φ y + (1 - t) / 2 * Φ y := by
        rw [map_smul_eq_mul, map_smul_eq_mul, hΦ, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      _ = Φ y := by ring

private theorem le_of_abs_le_of_eq_off (s : Finset ℕ) :
    ∀ {x y : ℕ →₀ ℝ}, (∀ i, |x i| ≤ |y i|) → (∀ i ∉ s, x i = y i) → Φ x ≤ Φ y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x y _ h
    rw [Finsupp.ext fun i => h i (Finset.notMem_empty i)]
  | insert a s _ ih =>
    intro x y h hs
    have h1 : Φ x ≤ Φ (x.update a (y a)) := by
      refine Φ.le_of_eq_off_of_abs_le (a := a) (fun i hi => ?_) ?_
      · rw [Finsupp.update_apply, if_neg hi]
      · rw [Finsupp.update_apply, if_pos rfl]
        exact h a
    have h2 : Φ (x.update a (y a)) ≤ Φ y := by
      refine ih (fun i => ?_) fun i hi => ?_
      · rw [Finsupp.update_apply]
        split_ifs with hia
        · rw [hia]
        · exact h i
      · rw [Finsupp.update_apply]
        split_ifs with hia
        · rw [hia]
        · exact hs i fun hmem => (Finset.mem_insert.mp hmem).elim hia hi
    exact h1.trans h2

/-- **A gauge is monotone in the absolute values of the entries.**
[HornJohnson2013, Theorem 5.4.19 and §7.4.7].
Port of `NLAlib.SymmetricGauge.value_le_of_nonneg_of_le`. -/
theorem le_of_abs_le {x y : ℕ →₀ ℝ} (h : ∀ i, |x i| ≤ |y i|) : Φ x ≤ Φ y := by
  classical
  refine Φ.le_of_abs_le_of_eq_off (x.support ∪ y.support) h fun i hi => ?_
  rw [Finset.notMem_union] at hi
  rw [Finsupp.notMem_support_iff.mp hi.1, Finsupp.notMem_support_iff.mp hi.2]

/-- **Fan dominance for sequences.** If `y` is non-increasing and every sum of absolute values of
entries of `x` over an index set `S` is at most the sum of the first `S.card` entries of `y`, then
`Φ x ≤ Φ y`: gauges respect weak majorization.
[HornJohnson2013, Theorem 7.4.8.4]; [Bhatia1997, Theorem IV.1.6 context].
Port of `NLAlib.SymmetricGauge.value_le_of_weaklyMajorized`. -/
theorem le_of_forall_sum_le {x y : ℕ →₀ ℝ} (hy : Antitone y)
    (h : ∀ S : Finset ℕ, ∑ i ∈ S, |x i| ≤ ∑ i ∈ Finset.range S.card, y i) : Φ x ≤ Φ y := by
  obtain ⟨N, hx0, hy0⟩ := exists_forall_le_apply_eq_zero x y
  have hmaj : WeaklyMajorized (fun i : Fin N => |x i|) (fun i : Fin N => y i) := by
    refine weaklyMajorized_fin_of_forall_sum_le (hy.antitoneOn _) fun S => ?_
    have hS := h (S.map Fin.valEmbedding)
    rwa [Finset.sum_map, Finset.card_map] at hS
  obtain ⟨z, hxz, hzy⟩ := hmaj.exists_le_majorized
  have h1 : Φ x = Φ (extendFin N fun i : Fin N => |x i|) := Φ.eq_of_abs_eq fun i => by
    obtain hi | hi := lt_or_ge i N
    · rw [extendFin_apply_of_lt _ hi, abs_abs]
    · rw [hx0 i hi, extendFin_apply_of_le _ hi]
  have h2 : Φ (extendFin N fun i : Fin N => |x i|) ≤ Φ (extendFin N z) :=
    Φ.le_of_abs_le fun i => by
      obtain hi | hi := lt_or_ge i N
      · rw [extendFin_apply_of_lt _ hi, extendFin_apply_of_lt _ hi, abs_abs]
        exact (hxz ⟨i, hi⟩).trans (le_abs_self _)
      · rw [extendFin_apply_of_le _ hi, extendFin_apply_of_le _ hi]
  have h3 : Φ (extendFin N z) ≤ Φ (extendFin N fun i : Fin N => y i) :=
    hzy.le_of_convexOn_of_comp_perm (Φ := fun z => Φ (extendFin N z))
      (Φ.convexOn.comp_linearMap (extendFin N)) fun z σ => by
        rw [extendFin_comp_perm, map_equivMapDomain]
  have h4 : extendFin N (fun i : Fin N => y i) = y := by
    ext i
    obtain hi | hi := lt_or_ge i N
    · rw [extendFin_apply_of_lt _ hi]
    · rw [hy0 i hi, extendFin_apply_of_le _ hi]
  rw [h1]
  exact h2.trans (h3.trans_eq (by rw [h4]))

/-! ### Comparison with the extreme gauges -/

/-- The value of a gauge at the first unit coordinate sequence is positive. By `apply_single` it
is the value at every unit coordinate sequence. -/
theorem apply_single_pos : 0 < Φ (Finsupp.single 0 1) := by
  refine lt_of_le_of_ne (apply_nonneg Φ _) fun h => ?_
  exact one_ne_zero (Finsupp.single_eq_zero.mp (Φ.eq_zero_iff.mp h.symm))

/-- A gauge takes the same value at every unit coordinate sequence. -/
theorem apply_single (i : ℕ) (a : ℝ) : Φ (Finsupp.single i a) = |a| * Φ (Finsupp.single 0 1) := by
  have h : Finsupp.single i a =
      a • (Finsupp.single 0 (1 : ℝ)).equivMapDomain (Equiv.swap 0 i) := by
    rw [Finsupp.equivMapDomain_single, Equiv.swap_apply_left, Finsupp.smul_single, smul_eq_mul,
      mul_one]
  rw [h, map_smul_eq_mul, map_equivMapDomain, Real.norm_eq_abs]

/-- Every gauge dominates a multiple of the `ℓ^∞` gauge: `Φ(e₀) |x i| ≤ Φ x`.
[HornJohnson2013, §7.4.7]. -/
theorem apply_single_mul_abs_le (x : ℕ →₀ ℝ) (i : ℕ) : Φ (Finsupp.single 0 1) * |x i| ≤ Φ x := by
  rw [mul_comm, ← Φ.apply_single i (x i)]
  refine Φ.le_of_abs_le fun j => ?_
  obtain rfl | hj := eq_or_ne j i
  · rw [Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne hj, abs_zero]
    exact abs_nonneg _

/-- Every gauge is dominated by a multiple of the `ℓ^1` gauge: `Φ x ≤ Φ(e₀) ∑ |x i|`.
[HornJohnson2013, §7.4.7]. -/
theorem le_apply_single_mul_sum (x : ℕ →₀ ℝ) :
    Φ x ≤ Φ (Finsupp.single 0 1) * ∑ i ∈ x.support, |x i| := by
  calc Φ x = Φ (∑ i ∈ x.support, Finsupp.single i (x i)) := congrArg Φ x.sum_single.symm
    _ ≤ ∑ i ∈ x.support, Φ (Finsupp.single i (x i)) :=
      Finset.le_sum_of_subadditive Φ (map_zero Φ).le (map_add_le_add Φ) _ _
    _ = Φ (Finsupp.single 0 1) * ∑ i ∈ x.support, |x i| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Φ.apply_single, mul_comm]

end SymmetricGauge

end NLAlib
