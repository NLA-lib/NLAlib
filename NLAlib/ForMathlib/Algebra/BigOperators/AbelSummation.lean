/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith

/-!
# Abel's inequality for sums against a non-increasing weight

If the partial sums of `b` are dominated by those of `c`, a non-increasing weight `a` preserves
the domination: `∑ i < N, a i * b i ≤ ∑ i < N, a i * c i`, provided the weight is nonnegative or
the total sums of `b` and `c` agree. Mathlib has the summation by parts identity
(`Finset.sum_range_by_parts`) and not this inequality. Upstream candidates for
`Mathlib.Algebra.Order.BigOperators.Ring.Finset`.

## Main results

* `Finset.sum_range_mul_add_le_sum_range_mul_of_antitoneOn`: the general form, with a lower bound
  `t` on the weight and the slack term `t * (∑ c - ∑ b)`.
* `Finset.sum_range_mul_le_sum_range_mul_of_antitoneOn_of_nonneg`: nonnegative weight.
* `Finset.sum_range_mul_le_sum_range_mul_of_antitoneOn_of_sum_eq`: equal total sums.
-/

@[expose] public section

namespace Finset

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a b c : ℕ → R} {N : ℕ}

/-- **Abel's inequality**, with a slack term. If `a` is non-increasing below `N` and bounded
below by `t` there, and the partial sums of `b` are at most those of `c` up to `N`, then
`∑ i < N, a i * b i + t * (∑ i < N, c i - ∑ i < N, b i) ≤ ∑ i < N, a i * c i`. The cases `t = 0`
and equal total sums are `Finset.sum_range_mul_le_sum_range_mul_of_antitoneOn_of_nonneg` and
`Finset.sum_range_mul_le_sum_range_mul_of_antitoneOn_of_sum_eq`. -/
theorem sum_range_mul_add_le_sum_range_mul_of_antitoneOn (ha : AntitoneOn a (Set.Iio N))
    (h : ∀ k ≤ N, ∑ i ∈ range k, b i ≤ ∑ i ∈ range k, c i) {t : R} (ht : ∀ i < N, t ≤ a i) :
    ∑ i ∈ range N, a i * b i + t * (∑ i ∈ range N, c i - ∑ i ∈ range N, b i) ≤
      ∑ i ∈ range N, a i * c i := by
  induction N generalizing t with
  | zero => simp
  | succ N ih =>
    have hlt {i : ℕ} (hi : i ∈ Set.Iio N) : i ∈ Set.Iio (N + 1) :=
      Set.mem_Iio.mpr ((Set.mem_Iio.mp hi).trans N.lt_succ_self)
    have h1 := ih (fun i hi j hj hij => ha (hlt hi) (hlt hj) hij) (fun k hk => h k (by omega))
      (t := a N) fun i hi => ha (hlt hi) (Set.mem_Iio.mpr N.lt_succ_self) hi.le
    have h2 := h (N + 1) le_rfl
    have h3 := ht N N.lt_succ_self
    rw [sum_range_succ, sum_range_succ] at h2
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h2)]

/-- **Abel's inequality** for a nonnegative weight. If `a` is non-increasing and nonnegative
below `N`, and the partial sums of `b` are at most those of `c` up to `N`, then
`∑ i < N, a i * b i ≤ ∑ i < N, a i * c i`. -/
theorem sum_range_mul_le_sum_range_mul_of_antitoneOn_of_nonneg (ha : AntitoneOn a (Set.Iio N))
    (h : ∀ k ≤ N, ∑ i ∈ range k, b i ≤ ∑ i ∈ range k, c i) (ha0 : ∀ i < N, 0 ≤ a i) :
    ∑ i ∈ range N, a i * b i ≤ ∑ i ∈ range N, a i * c i := by
  have key := sum_range_mul_add_le_sum_range_mul_of_antitoneOn ha h ha0
  rwa [zero_mul, add_zero] at key

/-- **Abel's inequality** for equal total sums. If `a` is non-increasing below `N`, the partial
sums of `b` are at most those of `c` up to `N`, and the two sums up to `N` agree, then
`∑ i < N, a i * b i ≤ ∑ i < N, a i * c i`, with no sign condition on `a`. -/
theorem sum_range_mul_le_sum_range_mul_of_antitoneOn_of_sum_eq (ha : AntitoneOn a (Set.Iio N))
    (h : ∀ k ≤ N, ∑ i ∈ range k, b i ≤ ∑ i ∈ range k, c i)
    (hsum : ∑ i ∈ range N, b i = ∑ i ∈ range N, c i) :
    ∑ i ∈ range N, a i * b i ≤ ∑ i ∈ range N, a i * c i := by
  obtain _ | N := N
  · simp
  · have key := sum_range_mul_add_le_sum_range_mul_of_antitoneOn ha h (t := a N) fun i hi =>
      ha (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr N.lt_succ_self) (Nat.lt_succ_iff.mp hi)
    rwa [hsum, sub_self, mul_zero, add_zero] at key

end Finset
