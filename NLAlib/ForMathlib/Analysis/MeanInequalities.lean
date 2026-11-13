/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# Finite moment inequalities

For weights $w_i \ge 0$ summing to $1$ and values $x_i \ge 0$, the weight of the event
$x_i > t\sum_j w_jx_j$ is at least $(1 - t)^2(\sum_i w_ix_i)^2/\sum_i w_ix_i^2$. The measure form
is `ProbabilityTheory.sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt` in
`NLAlib.ForMathlib.Probability.Moments.PaleyZygmund`; the finite form lets the matrix files work
with finite weighted sums and no measure theory. Upstream candidate for
`Mathlib/Analysis/MeanInequalities.lean`, next to the weighted power-mean inequalities.

The even moments of a random sign admit the sharp quadratic bound with coefficient
$2r-1$, used for the corresponding Schatten moment inequality.

## Main results

* `Finset.sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter`: the finite weighted Paley–Zygmund
  inequality.
* `Real.add_pow_add_sub_pow_le`: the even two-point moment bound.
-/

@[expose] public section

namespace Finset

/-- **The Paley–Zygmund inequality for finite weighted sums.** For a finite family of weights
$w_i \ge 0$ with $\sum_i w_i = 1$, values $x_i \ge 0$ and $0 \le t \le 1$,
$$(1 - t)^2\Bigl(\sum_i w_ix_i\Bigr)^2 \le \Bigl(\sum_i w_ix_i^2\Bigr)
\sum_{i \,:\, x_i > t\sum_j w_jx_j} w_i\,.$$
[PaleyZygmund1932, Lemma 19], in its discrete form. -/
theorem sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter {ι : Type*} (s : Finset ι) {w x : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 ≤ x i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) ^ 2 * (∑ i ∈ s, w i * x i) ^ 2 ≤
      (∑ i ∈ s, w i * x i ^ 2) *
        ∑ i ∈ s.filter (fun i => t * ∑ j ∈ s, w j * x j < x i), w i := by
  set m := ∑ j ∈ s, w j * x j with hm_def
  have hm : 0 ≤ m := sum_nonneg fun i hi => mul_nonneg (hw i hi) (hx i hi)
  set A := s.filter (fun i => t * m < x i) with hA_def
  have hsplit : ∑ i ∈ s.filter (fun i => ¬ t * m < x i), w i * x i
      + ∑ i ∈ A, w i * x i = m := by
    rw [add_comm]
    exact Finset.sum_filter_add_sum_filter_not s (fun i => t * m < x i) (fun i => w i * x i)
  have hlow : ∑ i ∈ s.filter (fun i => ¬ t * m < x i), w i * x i ≤ t * m := by
    have h1 : ∑ i ∈ s.filter (fun i => ¬ t * m < x i), w i * x i
        ≤ ∑ i ∈ s.filter (fun i => ¬ t * m < x i), t * m * w i :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_filter, not_lt] at hi
        rw [mul_comm (w i)]
        exact mul_le_mul_of_nonneg_right hi.2 (hw i hi.1)
    rw [← Finset.mul_sum] at h1
    have h2 : ∑ i ∈ s.filter (fun i => ¬ t * m < x i), w i ≤ 1 := by
      have := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun i => ¬ t * m < x i) s) (fun i hi _ => hw i hi)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg ht0 hm)]
  have hlow' : (1 - t) * m ≤ ∑ i ∈ A, w i * x i := by linarith
  have hCS : (∑ i ∈ A, w i * x i) ^ 2 ≤ (∑ i ∈ A, w i) * ∑ i ∈ A, w i * x i ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A
      (fun i hi => hw i (Finset.mem_filter.1 hi).1)
      (fun i hi => mul_nonneg (hw i (Finset.mem_filter.1 hi).1) (sq_nonneg _))
      (fun i _ => le_of_eq (by ring))
  have hsub : ∑ i ∈ A, w i * x i ^ 2 ≤ ∑ i ∈ s, w i * x i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => mul_nonneg (hw i hi) (sq_nonneg _))
  have hAw : 0 ≤ ∑ i ∈ A, w i := sum_nonneg fun i hi => hw i (Finset.mem_filter.1 hi).1
  have hfin : (∑ i ∈ A, w i) * ∑ i ∈ A, w i * x i ^ 2
      ≤ (∑ i ∈ A, w i) * ∑ i ∈ s, w i * x i ^ 2 :=
    mul_le_mul_of_nonneg_left hsub hAw
  have hsq := pow_le_pow_left₀ (mul_nonneg (by linarith) hm) hlow' 2
  rw [mul_pow] at hsq
  rw [mul_comm]
  linarith

end Finset

open Finset

private theorem choose_two_mul_le (r k : ℕ) :
    (2 * r).choose (2 * k) ≤ r.choose k * (2 * r - 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hkr : k < r
    · refine Nat.le_of_mul_le_mul_right (c := (2 * k + 2) * (2 * k + 1)) ?_ (by positivity)
      have h0 := Nat.choose_succ_right_eq (2 * r) (2 * k)
      have h1 := Nat.choose_succ_right_eq (2 * r) (2 * k + 1)
      have h := Nat.choose_succ_right_eq r k
      calc
        (2 * r).choose (2 * (k + 1)) * ((2 * k + 2) * (2 * k + 1)) =
          (2 * r).choose (2 * k) * (2 * r - 2 * k) * (2 * r - (2 * k + 1)) := by
            rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, ← mul_assoc, h1,
              mul_right_comm _ _ (2 * k + 1), h0]
        _ ≤ r.choose k * (2 * r - 1) ^ k * (2 * (r - k)) * (2 * r - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul ih (Nat.mul_sub_left_distrib 2 r k).ge) (by omega)
        _ = r.choose (k + 1) * (2 * r - 1) ^ (k + 1) * (2 * k + 2) := by
          rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_succ]
          calc
            _ = r.choose k * (r - k) * (2 * r - 1) ^ k * (2 * r - 1) * 2 := by ring
            _ = _ := by rw [← h]; ring
        _ ≤ _ := by
          rw [← mul_assoc]
          exact Nat.le_mul_of_pos_right _ (by positivity)
    · rw [Nat.choose_eq_zero_of_lt (by omega : 2 * r < 2 * (k + 1))]
      exact Nat.zero_le _

private theorem sum_range_even (f : ℕ → ℝ) (hodd : ∀ j, f (2 * j + 1) = 0) (r : ℕ) :
    ∑ i ∈ range (2 * r + 1), f i = ∑ j ∈ range (r + 1), f (2 * j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ (fun j => f (2 * j)) (r + 1), sum_range_succ f (2 * (r + 1)),
      show 2 * (r + 1) = (2 * r + 1) + 1 by omega, sum_range_succ f (2 * r + 1), ih, hodd, add_zero]

/-- The even moment of a scalar translated by a random sign satisfies the two-point bound
$$\frac{(a+b)^{2r}+(a-b)^{2r}}{2} \le (a^2 + (2r-1)b^2)^r.$$
The coefficient is sharp for positive $r$. Scalar case of [Tropp2022, Theorem 8.2]. -/
theorem Real.add_pow_add_sub_pow_le (a b : ℝ) (r : ℕ) :
    ((a + b) ^ (2 * r) + (a - b) ^ (2 * r)) / 2 ≤
      (a ^ 2 + (2 * (r : ℝ) - 1) * b ^ 2) ^ r := by
  rcases r.eq_zero_or_pos with rfl | hr
  · simp
  let f (k : ℕ) := (b ^ k + (-b) ^ k) / 2 * a ^ (2 * r - k) * (2 * r).choose k
  have hsum : ((a + b) ^ (2 * r) + (a - b) ^ (2 * r)) / 2 = ∑ k ∈ range (2 * r + 1), f k := by
    rw [add_comm a b, sub_eq_add_neg, add_comm a (-b), add_pow, add_pow, ← sum_add_distrib, sum_div]
    exact sum_congr rfl fun k _ => by dsimp [f]; ring
  have hodd (k : ℕ) : f (2 * k + 1) = 0 := by
    simp [f, (show Odd (2 * k + 1) from ⟨k, rfl⟩).neg_pow]
  rw [hsum, sum_range_even f hodd, add_comm (a ^ 2), add_pow]
  refine sum_le_sum fun k _ => ?_
  have hcoef : ((2 * r).choose (2 * k) : ℝ) ≤ r.choose k * (2 * (r : ℝ) - 1) ^ k := by
    have h : ((2 * r).choose (2 * k) : ℝ) ≤ r.choose k * ((2 * r - 1 : ℕ) : ℝ) ^ k := by
      exact_mod_cast choose_two_mul_le r k
    simpa only [Nat.cast_sub (show 1 ≤ 2 * r by omega), Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat] using h
  have h := mul_le_mul_of_nonneg_left hcoef
    (mul_nonneg (pow_nonneg (sq_nonneg b) k) (pow_nonneg (sq_nonneg a) (r - k)))
  dsimp [f]
  rw [(even_two_mul k).neg_pow, ← Nat.mul_sub_left_distrib, pow_mul, pow_mul, mul_pow]
  linarith
