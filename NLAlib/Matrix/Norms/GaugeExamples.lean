/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import NLAlib.Matrix.Norms.SymmetricGauge

/-!
# The `ℓ^q` and Ky Fan gauges

The two families of symmetric gauge functions behind the named matrix norms:
`NLAlib.lpGauge q`, the `ℓ^q` norm of a finitely supported sequence for `1 ≤ q`, and
`NLAlib.kyFanGauge k`, the sum of the `k` largest absolute values for `k ≠ 0`. Their matrix norms
are the Schatten and Ky Fan norms (`NLAlib.lpGauge_matrixNorm` and `NLAlib.kyFanGauge_matrixNorm`
in `NLAlib.Matrix.Norms.UnitarilyInvariant`).

## Main definitions

* `NLAlib.lpGauge q`: the `ℓ^q` gauge, `1 ≤ q`.
* `NLAlib.kyFanGauge k`: the sum of the `k` largest absolute values, `k ≠ 0`.

## Main results

* `NLAlib.lpGauge_apply_of_ne_top`, `NLAlib.lpGauge_top_apply`, `NLAlib.lpGauge_one_apply`: the
  values of the `ℓ^q` gauges.
* `NLAlib.lpGauge_apply_eq_norm_toLp`: the bridge to Mathlib's `PiLp` norms on `Fin N → ℝ`.
* `NLAlib.sum_abs_le_kyFanGauge`, `NLAlib.kyFanGauge_apply_of_antitone`: the Ky Fan gauge bounds
  every sum of `k` absolute values, and is the sum of the first `k` entries of a non-increasing
  sequence.
-/

@[expose] public section

open scoped ENNReal

namespace NLAlib

/-! ### The `ℓ^q` gauges -/

/-- The function underlying `lpGauge`. -/
private noncomputable def lpFun (q : ℝ≥0∞) (x : ℕ →₀ ℝ) : ℝ :=
  if q = ⊤ then ⨆ i, |x i| else (x.sum fun _ a => |a| ^ q.toReal) ^ q.toReal⁻¹

private theorem bddAbove_range_abs (x : ℕ →₀ ℝ) : BddAbove (Set.range fun i => |x i|) := by
  refine ((x.finite_range.image abs).subset ?_).bddAbove
  rintro _ ⟨i, rfl⟩
  exact ⟨x i, ⟨i, rfl⟩, rfl⟩

private theorem lpFun_eq_norm_toLp {q : ℝ≥0∞} (hq : 1 ≤ q) {x : ℕ →₀ ℝ} {N : ℕ}
    (hx : ∀ i, N ≤ i → x i = 0) :
    lpFun q x = ‖(WithLp.toLp q fun i : Fin N => x i : PiLp q fun _ : Fin N => ℝ)‖ := by
  rw [lpFun]
  split_ifs with hq'
  · subst hq'
    rw [PiLp.norm_eq_ciSup]
    simp only [Real.norm_eq_abs]
    refine le_antisymm (Real.iSup_le (fun i => ?_) (Real.iSup_nonneg fun _ => abs_nonneg _))
      (Real.iSup_le (fun i => ?_) (Real.iSup_nonneg fun _ => abs_nonneg _))
    · obtain hi | hi := lt_or_ge i N
      · exact le_ciSup (f := fun j : Fin N => |x j|) (Set.finite_range _).bddAbove ⟨i, hi⟩
      · rw [hx i hi, abs_zero]
        exact Real.iSup_nonneg fun _ => abs_nonneg _
    · exact le_ciSup (bddAbove_range_abs x) (i : ℕ)
  · have hpos : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq).ne' hq'
    have hsupp : x.support ⊆ Finset.range N := fun i hi => by
      rw [Finset.mem_range]
      by_contra hlt
      exact Finsupp.mem_support_iff.mp hi (hx i (not_lt.mp hlt))
    rw [PiLp.norm_eq_sum hpos, one_div, Finsupp.sum_of_support_subset x hsupp _
      fun i _ => by rw [abs_zero, Real.zero_rpow hpos.ne']]
    simp only [Real.norm_eq_abs]
    rw [Fin.sum_univ_eq_sum_range (fun i => |x i| ^ q.toReal) N]

private theorem lpFun_zero {q : ℝ≥0∞} (hq : 1 ≤ q) : lpFun q 0 = 0 := by
  have := Fact.mk hq
  rw [lpFun_eq_norm_toLp hq (N := 0) fun _ _ => rfl]
  exact norm_eq_zero.mpr (Subsingleton.elim _ _)

private theorem lpFun_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (x y : ℕ →₀ ℝ) :
    lpFun q (x + y) ≤ lpFun q x + lpFun q y := by
  have := Fact.mk hq
  obtain ⟨N, hx, hy⟩ := exists_forall_le_apply_eq_zero x y
  have hxy : ∀ i, N ≤ i → (x + y) i = 0 := fun i hi => by
    rw [Finsupp.add_apply, hx i hi, hy i hi, add_zero]
  rw [lpFun_eq_norm_toLp hq hx, lpFun_eq_norm_toLp hq hy, lpFun_eq_norm_toLp hq hxy]
  exact norm_add_le (WithLp.toLp q fun i : Fin N => x i) (WithLp.toLp q fun i : Fin N => y i)

private theorem lpFun_smul {q : ℝ≥0∞} (hq : 1 ≤ q) (c : ℝ) (x : ℕ →₀ ℝ) :
    lpFun q (c • x) = ‖c‖ * lpFun q x := by
  have := Fact.mk hq
  obtain ⟨N, hx, -⟩ := exists_forall_le_apply_eq_zero x x
  have hcx : ∀ i, N ≤ i → (c • x) i = 0 := fun i hi => by
    rw [Finsupp.smul_apply, hx i hi, smul_zero]
  rw [lpFun_eq_norm_toLp hq hx, lpFun_eq_norm_toLp hq hcx]
  exact norm_smul c (WithLp.toLp q fun i : Fin N => x i)

private theorem lpFun_neg {q : ℝ≥0∞} (hq : 1 ≤ q) (x : ℕ →₀ ℝ) : lpFun q (-x) = lpFun q x := by
  have h := lpFun_smul hq (-1) x
  rwa [neg_one_smul, norm_neg, norm_one, one_mul] at h

private theorem eq_zero_of_lpFun_eq_zero {q : ℝ≥0∞} (hq : 1 ≤ q) (x : ℕ →₀ ℝ)
    (h : lpFun q x = 0) : x = 0 := by
  have := Fact.mk hq
  obtain ⟨N, hx, -⟩ := exists_forall_le_apply_eq_zero x x
  rw [lpFun_eq_norm_toLp hq hx, norm_eq_zero] at h
  ext i
  obtain hi | hi := lt_or_ge i N
  · exact congrFun (congrArg WithLp.ofLp h) ⟨i, hi⟩
  · exact hx i hi

private theorem lpFun_equivMapDomain (q : ℝ≥0∞) (σ : Equiv.Perm ℕ) (x : ℕ →₀ ℝ) :
    lpFun q (x.equivMapDomain σ) = lpFun q x := by
  rw [lpFun, lpFun]
  split_ifs with hq'
  · simp only [Finsupp.equivMapDomain_apply]
    exact σ.symm.iSup_comp (g := fun i => |x i|)
  · rw [Finsupp.sum_equivMapDomain]

private theorem lpFun_mapRange_abs {q : ℝ≥0∞} (hq : 1 ≤ q) (x : ℕ →₀ ℝ) :
    lpFun q (x.mapRange abs abs_zero) = lpFun q x := by
  rw [lpFun, lpFun]
  split_ifs with hq'
  · simp only [Finsupp.mapRange_apply, abs_abs]
  · have hpos : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq).ne' hq'
    rw [Finsupp.sum_mapRange_index fun i => by rw [abs_zero, Real.zero_rpow hpos.ne']]
    simp only [abs_abs]

/-- The **`ℓ^q` gauge**, `1 ≤ q`: `(∑ |x i| ^ q) ^ (1 / q)`, and `sup |x i|` for `q = ⊤`. Its
matrix norm is the Schatten `q`-norm. -/
noncomputable def lpGauge (q : ℝ≥0∞) (hq : 1 ≤ q) : SymmetricGauge where
  toFun x := if q = ⊤ then ⨆ i, |x i| else (x.sum fun _ a => |a| ^ q.toReal) ^ q.toReal⁻¹
  map_zero' := by exact lpFun_zero hq
  add_le' := by exact lpFun_add_le hq
  neg' := by exact lpFun_neg hq
  smul' := by exact lpFun_smul hq
  eq_zero_of_map_eq_zero' := by exact eq_zero_of_lpFun_eq_zero hq
  map_equivMapDomain' := by exact lpFun_equivMapDomain q
  map_abs' := by exact lpFun_mapRange_abs hq

private theorem lpGauge_apply {q : ℝ≥0∞} (hq : 1 ≤ q) (x : ℕ →₀ ℝ) :
    lpGauge q hq x = lpFun q x :=
  rfl

/-- The `ℓ^q` gauge for finite `q`. -/
theorem lpGauge_apply_of_ne_top {q : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ⊤) (x : ℕ →₀ ℝ) :
    lpGauge q hq x = (∑ i ∈ x.support, |x i| ^ q.toReal) ^ q.toReal⁻¹ := by
  rw [lpGauge_apply, lpFun, if_neg hq', Finsupp.sum]

/-- The `ℓ^∞` gauge is the largest absolute value. -/
theorem lpGauge_top_apply (x : ℕ →₀ ℝ) : lpGauge ⊤ le_top x = ⨆ i, |x i| := by
  rw [lpGauge_apply, lpFun, if_pos rfl]

/-- The `ℓ^1` gauge is the sum of the absolute values. -/
theorem lpGauge_one_apply (x : ℕ →₀ ℝ) : lpGauge 1 le_rfl x = ∑ i ∈ x.support, |x i| := by
  rw [lpGauge_apply_of_ne_top le_rfl ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, Real.rpow_one, inv_one]

/-- The `ℓ^q` gauge of a sequence supported in the first `N` indices is the `PiLp` norm of its
first `N` entries. This is the bridge to Mathlib's `ℓ^q` norms on `Fin N → ℝ`. -/
theorem lpGauge_apply_eq_norm_toLp {q : ℝ≥0∞} (hq : 1 ≤ q) {x : ℕ →₀ ℝ} {N : ℕ}
    (hx : ∀ i, N ≤ i → x i = 0) :
    lpGauge q hq x = ‖(WithLp.toLp q fun i : Fin N => x i : PiLp q fun _ : Fin N => ℝ)‖ := by
  exact lpFun_eq_norm_toLp hq hx

/-! ### The Ky Fan gauges -/

/-- The function underlying `kyFanGauge`. -/
private noncomputable def kyFanFun (k : ℕ) (x : ℕ →₀ ℝ) : ℝ :=
  ⨆ s : {s : Finset ℕ // s.card ≤ k}, ∑ i ∈ s.1, |x i|

private theorem sum_abs_le_sum_support (x : ℕ →₀ ℝ) (s : Finset ℕ) :
    ∑ i ∈ s, |x i| ≤ ∑ i ∈ x.support, |x i| := by
  classical
  calc ∑ i ∈ s, |x i| ≤ ∑ i ∈ s ∪ x.support, |x i| :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => abs_nonneg _
    _ = ∑ i ∈ x.support, |x i| :=
        (Finset.sum_subset Finset.subset_union_right fun i _ hi => by
          rw [Finsupp.notMem_support_iff.mp hi, abs_zero]).symm

private theorem sum_abs_le_kyFanFun {k : ℕ} (x : ℕ →₀ ℝ) {s : Finset ℕ} (hs : s.card ≤ k) :
    ∑ i ∈ s, |x i| ≤ kyFanFun k x := by
  refine le_ciSup (f := fun s : {s : Finset ℕ // s.card ≤ k} => ∑ i ∈ s.1, |x i|)
    ⟨∑ i ∈ x.support, |x i|, ?_⟩ ⟨s, hs⟩
  rintro _ ⟨t, rfl⟩
  exact sum_abs_le_sum_support x t.1

private theorem kyFanFun_le {k : ℕ} {x : ℕ →₀ ℝ} {c : ℝ}
    (h : ∀ s : Finset ℕ, s.card ≤ k → ∑ i ∈ s, |x i| ≤ c) : kyFanFun k x ≤ c := by
  have : Nonempty {s : Finset ℕ // s.card ≤ k} := ⟨⟨∅, by simp⟩⟩
  exact ciSup_le fun s => h s.1 s.2

private theorem kyFanFun_zero (k : ℕ) : kyFanFun k 0 = 0 := by
  refine le_antisymm (kyFanFun_le fun s _ => ?_) ?_
  · simp only [Finsupp.coe_zero, Pi.zero_apply, abs_zero, Finset.sum_const_zero, le_refl]
  · have h := sum_abs_le_kyFanFun (k := k) 0 (s := ∅) (by simp)
    rwa [Finset.sum_empty] at h

private theorem kyFanFun_add_le (k : ℕ) (x y : ℕ →₀ ℝ) :
    kyFanFun k (x + y) ≤ kyFanFun k x + kyFanFun k y := by
  refine kyFanFun_le fun s hs => ?_
  calc ∑ i ∈ s, |(x + y) i| ≤ ∑ i ∈ s, (|x i| + |y i|) :=
        Finset.sum_le_sum fun i _ => abs_add_le (x i) (y i)
    _ = ∑ i ∈ s, |x i| + ∑ i ∈ s, |y i| := Finset.sum_add_distrib
    _ ≤ kyFanFun k x + kyFanFun k y :=
        add_le_add (sum_abs_le_kyFanFun x hs) (sum_abs_le_kyFanFun y hs)

private theorem kyFanFun_smul (k : ℕ) (c : ℝ) (x : ℕ →₀ ℝ) :
    kyFanFun k (c • x) = ‖c‖ * kyFanFun k x := by
  rw [kyFanFun, kyFanFun, Real.norm_eq_abs, Real.mul_iSup_of_nonneg (abs_nonneg c)]
  simp only [Finsupp.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

private theorem kyFanFun_neg (k : ℕ) (x : ℕ →₀ ℝ) : kyFanFun k (-x) = kyFanFun k x := by
  simp only [kyFanFun, Finsupp.neg_apply, abs_neg]

private theorem eq_zero_of_kyFanFun_eq_zero {k : ℕ} (hk : k ≠ 0) (x : ℕ →₀ ℝ)
    (h : kyFanFun k x = 0) : x = 0 := by
  ext i
  have hi := sum_abs_le_kyFanFun x (s := {i}) (k := k)
    (by rw [Finset.card_singleton]; exact Nat.one_le_iff_ne_zero.mpr hk)
  rw [Finset.sum_singleton, h] at hi
  exact abs_nonpos_iff.mp hi

private theorem kyFanFun_equivMapDomain_le (k : ℕ) (σ : Equiv.Perm ℕ) (x : ℕ →₀ ℝ) :
    kyFanFun k (x.equivMapDomain σ) ≤ kyFanFun k x := by
  refine kyFanFun_le fun s hs => ?_
  have h := sum_abs_le_kyFanFun x (s := s.map σ.symm.toEmbedding) (k := k)
    (by rwa [Finset.card_map])
  rw [Finset.sum_map] at h
  exact h

private theorem kyFanFun_equivMapDomain (k : ℕ) (σ : Equiv.Perm ℕ) (x : ℕ →₀ ℝ) :
    kyFanFun k (x.equivMapDomain σ) = kyFanFun k x := by
  refine le_antisymm (kyFanFun_equivMapDomain_le k σ x) ?_
  have h := kyFanFun_equivMapDomain_le k σ.symm (x.equivMapDomain σ)
  rwa [← Finsupp.equivMapDomain_trans, Equiv.self_trans_symm, Finsupp.equivMapDomain_refl] at h

private theorem kyFanFun_mapRange_abs (k : ℕ) (x : ℕ →₀ ℝ) :
    kyFanFun k (x.mapRange abs abs_zero) = kyFanFun k x := by
  simp only [kyFanFun, Finsupp.mapRange_apply, abs_abs]

/-- The **Ky Fan `k`-gauge**, `k ≠ 0`: the largest sum of `k` absolute values. Its matrix norm
is the Ky Fan `k`-norm. -/
noncomputable def kyFanGauge (k : ℕ) (hk : k ≠ 0) : SymmetricGauge where
  toFun x := ⨆ s : {s : Finset ℕ // s.card ≤ k}, ∑ i ∈ s.1, |x i|
  map_zero' := by exact kyFanFun_zero k
  add_le' := by exact kyFanFun_add_le k
  neg' := by exact kyFanFun_neg k
  smul' := by exact kyFanFun_smul k
  eq_zero_of_map_eq_zero' := by exact eq_zero_of_kyFanFun_eq_zero hk
  map_equivMapDomain' := by exact kyFanFun_equivMapDomain k
  map_abs' := by exact kyFanFun_mapRange_abs k

/-- Every sum of at most `k` absolute values is at most the Ky Fan `k`-gauge. -/
theorem sum_abs_le_kyFanGauge {k : ℕ} (hk : k ≠ 0) (x : ℕ →₀ ℝ) {s : Finset ℕ}
    (hs : s.card ≤ k) : ∑ i ∈ s, |x i| ≤ kyFanGauge k hk x := by
  exact sum_abs_le_kyFanFun x hs

/-- A non-increasing finitely supported sequence is nonnegative. -/
private theorem nonneg_of_antitone {x : ℕ →₀ ℝ} (hx : Antitone x) (i : ℕ) : 0 ≤ x i := by
  obtain ⟨N, hN, -⟩ := exists_forall_le_apply_eq_zero x x
  exact (hN (max i N) (le_max_right i N)).symm.trans_le (hx (le_max_left i N))

/-- The Ky Fan `k`-gauge of a non-increasing sequence is the sum of its first `k` entries. A
non-increasing finitely supported sequence is nonnegative, so no absolute values appear. -/
theorem kyFanGauge_apply_of_antitone {k : ℕ} (hk : k ≠ 0) {x : ℕ →₀ ℝ} (hx : Antitone x) :
    kyFanGauge k hk x = ∑ i ∈ Finset.range k, x i := by
  have hx0 : ∀ i, 0 ≤ x i := nonneg_of_antitone hx
  have habs : ∀ s : Finset ℕ, ∑ i ∈ s, |x i| = ∑ i ∈ s, x i := fun s =>
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hx0 i)
  refine le_antisymm (kyFanFun_le fun s hs => ?_) ?_
  · calc ∑ i ∈ s, |x i| = ∑ i ∈ s, x i := habs s
      _ ≤ ∑ i ∈ Finset.range s.card, x i := sum_le_sum_range_card_of_antitone hx s
      _ ≤ ∑ i ∈ Finset.range k, x i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hs) fun i _ _ => hx0 i
  · rw [← habs]
    exact sum_abs_le_kyFanGauge hk x (Finset.card_range k).le

end NLAlib
