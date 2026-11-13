/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Seminorm
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Logic.Equiv.Fintype
public import NLAlib.ForMathlib.Data.Finsupp.Basic
public import NLAlib.ForMathlib.Data.Finsupp.Order
public import NLAlib.Matrix.Majorization.DoublyStochastic

/-!
# Symmetric gauge functions

A symmetric gauge function is a norm on finitely supported real sequences that is invariant under
permutations of the indices and under changes of sign of the entries. By von Neumann's theorem
these are exactly the functions $\Phi$ for which
$\mathbf{A} \mapsto \Phi\bigl(\sigma_0(\mathbf{A}), \sigma_1(\mathbf{A}), \dots\bigr)$ is a
unitarily invariant norm, and one gauge gives such a norm on matrices of every shape at once; see
`NLAlib.Matrix.Norms.UnitarilyInvariant`.

The carrier is `ℕ →₀ ℝ`, the type of Mathlib's `LinearMap.singularValues`, and the structure
extends Mathlib's `Seminorm`. The $\ell^q$ and Ky Fan gauges are in
`NLAlib.Matrix.Norms.GaugeExamples`.

## Main definitions

* `NLAlib.SymmetricGauge`: the structure.

## Main results

* `NLAlib.SymmetricGauge.exists_eq_restrict`: extension of a gauge from a fixed finite dimension.
* `NLAlib.SymmetricGauge.le_of_abs_le`: gauges are monotone in the absolute values.
* `NLAlib.SymmetricGauge.le_of_forall_sum_le`: gauges respect weak majorization (Fan dominance
  for sequences).
* `NLAlib.SymmetricGauge.apply_single_mul_abs_le`, `NLAlib.SymmetricGauge.le_apply_single_mul_sum`:
  every gauge lies between multiples of the $\ell^\infty$ and $\ell^1$ gauges.
-/

@[expose] public section

namespace NLAlib

/-- A **symmetric gauge function**: a norm on finitely supported real sequences, invariant under
permutations of the indices and under taking absolute values of the entries. It extends Mathlib's
`Seminorm`, so the seminorm API applies (`map_zero`, `map_neg_eq_map`, `map_add_le_add`,
`map_smul_eq_mul`, `apply_nonneg`, `Φ.toSeminorm`).
[HornJohnson2013, Definition 7.4.7.1]; [Bhatia1997, §IV.1]. -/
structure SymmetricGauge extends Seminorm ℝ (ℕ →₀ ℝ) where
  /-- Definiteness. -/
  eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0
  /-- Invariance under permutations of the indices. -/
  map_equivMapDomain' : ∀ (σ : Equiv.Perm ℕ) x, toFun (x.equivMapDomain σ) = toFun x
  /-- Invariance under taking absolute values of the entries. -/
  map_abs' : ∀ x, toFun (x.mapRange abs abs_zero) = toFun x

/-- Extension by zero of a vector on `Fin N` to a finitely supported sequence. -/
private noncomputable def extendFinLinear (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin N)).symm.toLinearMap

private theorem extendFinLinear_apply_of_lt {N : ℕ} (z : Fin N → ℝ) {i : ℕ} (hi : i < N) :
    extendFinLinear N z i = z ⟨i, hi⟩ := by
  exact Finsupp.mapDomain_apply Fin.val_injective
    ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin N)).symm z) ⟨i, hi⟩

private theorem extendFinLinear_apply_of_le {N : ℕ} (z : Fin N → ℝ) {i : ℕ} (hi : N ≤ i) :
    extendFinLinear N z i = 0 := by
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨j, rfl⟩
  exact j.isLt.not_ge hi

private theorem extendFinLinear_comp_perm {N : ℕ} (z : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    extendFinLinear N (z ∘ σ) =
      (extendFinLinear N z).equivMapDomain (σ.extendDomain Fin.equivSubtype).symm := by
  ext i
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  obtain hi | hi := lt_or_ge i N
  · have h := σ.extendDomain_apply_image Fin.equivSubtype ⟨i, hi⟩
    have h' : σ.extendDomain Fin.equivSubtype i = (σ ⟨i, hi⟩ : ℕ) := h
    rw [h', extendFinLinear_apply_of_lt _ hi, extendFinLinear_apply_of_lt _ (σ ⟨i, hi⟩).isLt]
    rfl
  · rw [σ.extendDomain_apply_not_subtype Fin.equivSubtype (b := i) (not_lt.mpr hi),
      extendFinLinear_apply_of_le _ hi, extendFinLinear_apply_of_le _ hi]

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

/-- A gauge is a convex function. -/
theorem convexOn : ConvexOn ℝ Set.univ Φ := by
  exact Φ.toSeminorm.convexOn

/-! ### Symmetry -/

/-- A gauge is invariant under permutations of the indices. -/
@[simp]
theorem map_equivMapDomain (σ : Equiv.Perm ℕ) (x : ℕ →₀ ℝ) : Φ (x.equivMapDomain σ) = Φ x :=
  Φ.map_equivMapDomain' σ x

/-- A gauge depends only on the absolute values of the entries: $\Phi(\lvert x \rvert) = \Phi(x)$.
-/
@[simp]
theorem map_abs (x : ℕ →₀ ℝ) : Φ |x| = Φ x := by
  have h : |x| = x.mapRange abs abs_zero := by
    ext i
    rw [Finsupp.abs_apply, Finsupp.mapRange_apply]
  rw [h]
  exact Φ.map_abs' x

/-- Two sequences with the same absolute values have the same gauge. -/
theorem eq_of_abs_eq {x y : ℕ →₀ ℝ} (h : ∀ i, |x i| = |y i|) : Φ x = Φ y := by
  rw [← Φ.map_abs x, ← Φ.map_abs y]
  congr 1
  ext i
  simpa only [Finsupp.abs_apply] using h i

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

/-- **A gauge is monotone in the absolute values of the entries.** If
$\lvert \mathbf{x}_i \rvert \le \lvert \mathbf{y}_i \rvert$ for every $i$ then
$\Phi(\mathbf{x}) \le \Phi(\mathbf{y})$.
[HornJohnson2013, Theorem 5.4.19 and §7.4.7]. -/
theorem le_of_abs_le {x y : ℕ →₀ ℝ} (h : ∀ i, |x i| ≤ |y i|) : Φ x ≤ Φ y := by
  classical
  refine Φ.le_of_abs_le_of_eq_off (x.support ∪ y.support) h fun i hi => ?_
  rw [Finset.notMem_union] at hi
  rw [Finsupp.notMem_support_iff.mp hi.1, Finsupp.notMem_support_iff.mp hi.2]

/-- **Fan dominance for sequences.** If $\mathbf{y}$ is non-increasing and every sum of absolute
values of entries of $\mathbf{x}$ over a finite index set $S$ is at most the sum of the first
$\lvert S \rvert$ entries of $\mathbf{y}$,
$\sum_{i \in S} \lvert \mathbf{x}_i \rvert \le \sum_{i < \lvert S \rvert} \mathbf{y}_i$, then
$\Phi(\mathbf{x}) \le \Phi(\mathbf{y})$: gauges respect weak majorization.
[HornJohnson2013, Theorem 7.4.8.4]; [Bhatia1997, Theorem IV.1.6 context]. -/
theorem le_of_forall_sum_le {x y : ℕ →₀ ℝ} (hy : Antitone y)
    (h : ∀ S : Finset ℕ, ∑ i ∈ S, |x i| ≤ ∑ i ∈ Finset.range S.card, y i) : Φ x ≤ Φ y := by
  obtain ⟨N, hx0, hy0⟩ := Finsupp.exists_forall_le_apply_eq_zero x y
  have hmaj : WeaklyMajorized (fun i : Fin N => |x i|) (fun i : Fin N => y i) := by
    refine weaklyMajorized_fin_of_forall_sum_le (hy.antitoneOn _) fun S => ?_
    have hS := h (S.map Fin.valEmbedding)
    rwa [Finset.sum_map, Finset.card_map] at hS
  obtain ⟨z, hxz, hzy⟩ := hmaj.exists_le_majorized
  have h1 : Φ x = Φ (extendFinLinear N fun i : Fin N => |x i|) := Φ.eq_of_abs_eq fun i => by
    obtain hi | hi := lt_or_ge i N
    · rw [extendFinLinear_apply_of_lt _ hi, abs_abs]
    · rw [hx0 i hi, extendFinLinear_apply_of_le _ hi]
  have h2 : Φ (extendFinLinear N fun i : Fin N => |x i|) ≤ Φ (extendFinLinear N z) :=
    Φ.le_of_abs_le fun i => by
      obtain hi | hi := lt_or_ge i N
      · rw [extendFinLinear_apply_of_lt _ hi, extendFinLinear_apply_of_lt _ hi, abs_abs]
        exact (hxz ⟨i, hi⟩).trans (le_abs_self _)
      · rw [extendFinLinear_apply_of_le _ hi, extendFinLinear_apply_of_le _ hi]
  have h3 : Φ (extendFinLinear N z) ≤ Φ (extendFinLinear N fun i : Fin N => y i) :=
    hzy.le_of_convexOn_of_comp_perm (Φ := fun z => Φ (extendFinLinear N z))
      (Φ.convexOn.comp_linearMap (extendFinLinear N)) fun z σ => by
        rw [extendFinLinear_comp_perm, map_equivMapDomain]
  have h4 : extendFinLinear N (fun i : Fin N => y i) = y := by
    ext i
    obtain hi | hi := lt_or_ge i N
    · rw [extendFinLinear_apply_of_lt _ hi]
    · rw [hy0 i hi, extendFinLinear_apply_of_le _ hi]
  rw [h1]
  exact h2.trans (h3.trans_eq (by rw [h4]))

/-! ### Comparison with the extreme gauges -/

/-- The value of a gauge at the first unit coordinate sequence $\mathbf{e}_0$ is positive:
$\Phi(\mathbf{e}_0) > 0$. By `apply_single` it is the value at every unit coordinate sequence. -/
theorem apply_single_pos : 0 < Φ (Finsupp.single 0 1) := by
  refine lt_of_le_of_ne (apply_nonneg Φ _) fun h => ?_
  exact one_ne_zero (Finsupp.single_eq_zero.mp (Φ.eq_zero_iff.mp h.symm))

/-- A gauge takes the same value at every unit coordinate sequence:
$\Phi(a\mathbf{e}_i) = \lvert a \rvert \, \Phi(\mathbf{e}_0)$, with $\mathbf{e}_i$ the $i$-th unit
coordinate sequence. -/
theorem apply_single (i : ℕ) (a : ℝ) : Φ (Finsupp.single i a) = |a| * Φ (Finsupp.single 0 1) := by
  have h : Finsupp.single i a =
      a • (Finsupp.single 0 (1 : ℝ)).equivMapDomain (Equiv.swap 0 i) := by
    rw [Finsupp.equivMapDomain_single, Equiv.swap_apply_left, Finsupp.smul_single, smul_eq_mul,
      mul_one]
  rw [h, map_smul_eq_mul, map_equivMapDomain, Real.norm_eq_abs]

/-- Every gauge dominates a multiple of the $\ell^\infty$ gauge:
$\Phi(\mathbf{e}_0) \lvert \mathbf{x}_i \rvert \le \Phi(\mathbf{x})$ for every $i$.
[HornJohnson2013, §7.4.7]. -/
theorem apply_single_mul_abs_le (x : ℕ →₀ ℝ) (i : ℕ) : Φ (Finsupp.single 0 1) * |x i| ≤ Φ x := by
  rw [mul_comm, ← Φ.apply_single i (x i)]
  refine Φ.le_of_abs_le fun j => ?_
  obtain rfl | hj := eq_or_ne j i
  · rw [Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne hj, abs_zero]
    exact abs_nonneg _

/-- Every gauge is dominated by a multiple of the $\ell^1$ gauge:
$\Phi(\mathbf{x}) \le \Phi(\mathbf{e}_0) \sum_i \lvert \mathbf{x}_i \rvert$.
[HornJohnson2013, §7.4.7]. -/
theorem le_apply_single_mul_sum (x : ℕ →₀ ℝ) :
    Φ x ≤ Φ (Finsupp.single 0 1) * ∑ i ∈ x.support, |x i| := by
  calc Φ x = Φ (∑ i ∈ x.support, Finsupp.single i (x i)) := congrArg Φ x.sum_single.symm
    _ ≤ ∑ i ∈ x.support, Φ (Finsupp.single i (x i)) :=
      Finset.le_sum_of_subadditive Φ (map_zero Φ).le (map_add_le_add Φ) _ _
    _ = Φ (Finsupp.single 0 1) * ∑ i ∈ x.support, |x i| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Φ.apply_single, mul_comm]

/-! ### Extension from a finite dimension -/

/-- Deleting coordinates is the average of the identity and a change of signs. -/
private theorem seminorm_indicator_le {d : ℕ} (p : Seminorm ℝ (Fin d → ℝ))
    (habs : ∀ z : Fin d → ℝ, p (fun i => |z i|) = p z) (z : Fin d → ℝ)
    (s : Set (Fin d)) : p (s.indicator z) ≤ p z := by
  classical
  let w : Fin d → ℝ := fun i => if i ∈ s then z i else -z i
  have hw : p w = p z := by
    rw [← habs w, ← habs z]
    congr 1
    funext i
    by_cases hi : i ∈ s <;> simp [w, hi]
  have he : (2 : ℝ) • s.indicator z = z + w := by
    funext i
    by_cases hi : i ∈ s <;> simp [w, Set.indicator, hi, two_mul]
  have hp := map_add_le_add p z w
  rw [← he, map_smul_eq_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hw] at hp
  linarith

/-- Selecting entries of a zero-padded vector permutes some coordinates and deletes others. -/
private theorem restrict_perm_le {d : ℕ} (p : Seminorm ℝ (Fin d → ℝ))
    (hperm : ∀ (ρ : Equiv.Perm (Fin d)) (z : Fin d → ℝ), p (z ∘ ρ) = p z)
    (habs : ∀ z : Fin d → ℝ, p (fun i => |z i|) = p z) (x : ℕ →₀ ℝ)
    (hx : ∀ i, d ≤ i → x i = 0) (σ : Equiv.Perm ℕ) :
    p (fun i : Fin d => x (σ i)) ≤ p (fun i : Fin d => x i) := by
  classical
  let s := {i : Fin d | σ i < d}
  let f : s → Fin d := fun i => ⟨σ i.val, i.property⟩
  have hf : Function.Injective f := fun i j h =>
    Subtype.ext (Fin.ext (σ.injective (congrArg Fin.val h)))
  let e := Equiv.ofInjective f hf
  let ρ := e.extendSubtype
  let z : Fin d → ℝ := fun i => x i
  have h : (fun i : Fin d => x (σ i)) = s.indicator (z ∘ ρ) := by
    funext i
    by_cases hi : i ∈ s
    · rw [Set.indicator_of_mem hi, Function.comp_apply]
      change x (σ i) = x (e.extendSubtype i)
      rw [Equiv.extendSubtype_apply_of_mem e i hi]
      rfl
    · rw [Set.indicator_of_notMem hi, hx]
      exact le_of_not_gt hi
  rw [h]
  exact (seminorm_indicator_le p habs _ s).trans_eq (hperm ρ z)

/-- A definite, sign- and permutation-invariant seminorm on a positive number of coordinates
extends to a symmetric gauge on finitely supported sequences. The extension takes the supremum
of the seminorm over all selections of the given number of coordinates. It restricts to the
original norm on vectors supported in these coordinates. -/
theorem exists_eq_restrict {d : ℕ} (hd : 0 < d) (p : Seminorm ℝ (Fin d → ℝ))
    (hdef : ∀ z, p z = 0 → z = 0)
    (hperm : ∀ (σ : Equiv.Perm (Fin d)) (z : Fin d → ℝ), p (z ∘ σ) = p z)
    (habs : ∀ z : Fin d → ℝ, p (fun i => |z i|) = p z) :
    ∃ Φ : SymmetricGauge, ∀ x : ℕ →₀ ℝ, (∀ i, d ≤ i → x i = 0) →
      Φ x = p (fun i : Fin d => x i) := by
  classical
  -- Each selected tuple takes its values in the finite range of the input.
  let q (σ : Equiv.Perm ℕ) : Seminorm ℝ (ℕ →₀ ℝ) :=
    p.comp (LinearMap.pi fun i : Fin d => Finsupp.lapply (σ i))
  have hB (x : ℕ →₀ ℝ) : BddAbove (Set.range fun σ => q σ x) := by
    let : Finite (Set.range x) := x.finite_range.to_subtype
    have hf := Set.finite_range (fun z : Fin d → Set.range x => p (fun i => (z i).val))
    refine (hf.subset ?_).bddAbove
    rintro _ ⟨σ, rfl⟩
    exact ⟨fun i => ⟨x (σ i), ⟨σ i, rfl⟩⟩, rfl⟩
  let P := ⨆ σ, q σ
  have hP (x : ℕ →₀ ℝ) : P x = ⨆ σ : Equiv.Perm ℕ, p (fun i : Fin d => x (σ i)) :=
    Seminorm.iSup_apply (Seminorm.bddAbove_range_iff.mpr hB)
  let Φ : SymmetricGauge := {
    toSeminorm := P
    eq_zero_of_map_eq_zero' := by
      intro x hx
      ext i
      let σ := Equiv.swap 0 i
      have hs : p (fun j : Fin d => x (σ j)) ≤ P x := by
        rw [hP]
        exact le_ciSup (hB x) σ
      have hz := hdef _ (le_antisymm (hs.trans_eq hx) (apply_nonneg p _))
      simpa [σ] using congrFun hz (⟨0, hd⟩ : Fin d)
    map_equivMapDomain' := by
      intro τ x
      change P (x.equivMapDomain τ) = P x
      simp only [hP, Finsupp.equivMapDomain_apply]
      apply le_antisymm
      · refine ciSup_le fun σ => ?_
        exact le_ciSup (hB x) (σ.trans τ.symm)
      · refine ciSup_le fun σ => ?_
        have h := le_ciSup (hB (x.equivMapDomain τ)) (σ.trans τ)
        change p (fun i : Fin d => (x.equivMapDomain τ) (τ (σ i))) ≤
          ⨆ ρ : Equiv.Perm ℕ, p (fun i : Fin d => (x.equivMapDomain τ) (ρ i)) at h
        simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using h
    map_abs' := by
      intro x
      change P (x.mapRange abs abs_zero) = P x
      simp only [hP, Finsupp.mapRange_apply, habs] }
  refine ⟨Φ, fun x hx => ?_⟩
  change P x = _
  rw [hP]
  exact le_antisymm (ciSup_le (restrict_perm_le p hperm habs x hx)) (le_ciSup (hB x) 1)

end SymmetricGauge

end NLAlib
