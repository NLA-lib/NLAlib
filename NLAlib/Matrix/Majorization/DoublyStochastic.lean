/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
public import NLAlib.Matrix.Majorization.Basic

/-!
# Majorization, doubly stochastic matrices and convex functions

The Hardy–Littlewood–Pólya characterisations of majorization: `x` is majorized by `y` exactly
when `x = D y` for a doubly stochastic matrix `D`, exactly when `x` lies in the convex hull of the
permutations of `y`, and exactly when `∑ φ (x i) ≤ ∑ φ (y i)` for every convex `φ`. Weak
majorization is characterised by monotone convex functions.

## Main results

* `NLAlib.majorized_iff_exists_doublyStochastic`: Hardy–Littlewood–Pólya.
* `NLAlib.majorized_iff_mem_convexHull_permutations`: Rado.
* `NLAlib.Majorized.sum_convex_le`, `NLAlib.majorized_iff_forall_sum_convex_le`: Karamata.
* `NLAlib.Majorized.le_of_convexOn_of_comp_perm`: symmetric convex functions are Schur-convex.
* `NLAlib.WeaklyMajorized.sum_monotone_convex_le`: Tomić–Weyl.
* `NLAlib.WeaklyMajorized.exists_le_majorized`: weak majorization is domination followed by
  majorization.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The image of a vector under a doubly stochastic matrix is majorized by the vector.
[HornJohnson2013, Theorem 4.3.49].
Port of `NLAlib.majorized_mulVec_of_doublyStochastic`. -/
theorem majorized_mulVec_of_mem_doublyStochastic (y : ι → ℝ) {D : Matrix ι ι ℝ}
    (hD : D ∈ doublyStochastic ℝ ι) : Majorized (D *ᵥ y) y := by
  sorry

/-- **Hardy–Littlewood–Pólya.** `x` is majorized by `y` exactly when `x = D y` for some doubly
stochastic matrix `D`. [HornJohnson2013, Theorem 4.3.49].
Port of `NLAlib.majorized_iff_exists_doublyStochastic`.
Result: hardy-littlewood-polya -/
theorem majorized_iff_exists_doublyStochastic {x y : ι → ℝ} :
    Majorized x y ↔ ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x := by
  sorry

/-- **Rado's theorem.** `x` is majorized by `y` exactly when `x` lies in the convex hull of the
permutations of `y`. [HornJohnson2013, Theorem 4.3.49].
Port of `NLAlib.majorized_iff_mem_convexHull_permutations`.
Result: majorization-convex-hull -/
theorem majorized_iff_mem_convexHull_permutations {x y : ι → ℝ} :
    Majorized x y ↔ x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) := by
  sorry

/-- **Karamata's inequality.** If `x` is majorized by `y` and `φ` is convex, then
`∑ φ (x i) ≤ ∑ φ (y i)`. [HornJohnson2013, Theorem 4.3.50].
Port of `NLAlib.Majorized.sum_convex_le`.
Result: karamata-inequality -/
theorem Majorized.sum_convex_le {x y : ι → ℝ} (h : Majorized x y) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) : ∑ i, φ (x i) ≤ ∑ i, φ (y i) := by
  sorry

/-- **Schur-convexity of symmetric convex functions.** If `x` is majorized by `y` and
`Φ : (ι → ℝ) → ℝ` is convex and invariant under permutations of the coordinates, then
`Φ x ≤ Φ y`. Karamata's inequality is the separable case `Φ z = ∑ i, φ (z i)`.
[HornJohnson2013, Theorem 4.3.49 with Birkhoff's theorem 8.7.2]; [Bhatia1997, Theorem II.3.3]. -/
theorem Majorized.le_of_convexOn_of_comp_perm {x y : ι → ℝ} (h : Majorized x y)
    {Φ : (ι → ℝ) → ℝ} (hΦ : ConvexOn ℝ Set.univ Φ)
    (hperm : ∀ (z : ι → ℝ) (σ : Equiv.Perm ι), Φ (z ∘ σ) = Φ z) : Φ x ≤ Φ y := by
  sorry

/-- Majorization is characterised by convex functions.
Port of `NLAlib.majorized_iff_sum_convex_le`. -/
theorem majorized_iff_forall_sum_convex_le {x y : ι → ℝ} :
    Majorized x y ↔ ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → ∑ i, φ (x i) ≤ ∑ i, φ (y i) := by
  sorry

/-- A weakly majorized vector lies below a majorized one: `x ≤ z` entrywise with `z` majorized
by `y`. Port of `NLAlib.WeaklyMajorized.exists_le_majorized`. -/
theorem WeaklyMajorized.exists_le_majorized {x y : ι → ℝ} (h : WeaklyMajorized x y) :
    ∃ z : ι → ℝ, x ≤ z ∧ Majorized z y := by
  sorry

/-- If `x` is weakly majorized by `y` and `Φ : (ι → ℝ) → ℝ` is convex, monotone and invariant
under permutations of the coordinates, then `Φ x ≤ Φ y`. This is the form in which symmetric
gauge functions consume weak majorization. [Bhatia1997, Theorem II.3.3 and Example II.3.5]. -/
theorem WeaklyMajorized.le_of_convexOn_of_monotone_of_comp_perm {x y : ι → ℝ}
    (h : WeaklyMajorized x y) {Φ : (ι → ℝ) → ℝ} (hΦ : ConvexOn ℝ Set.univ Φ) (hmono : Monotone Φ)
    (hperm : ∀ (z : ι → ℝ) (σ : Equiv.Perm ι), Φ (z ∘ σ) = Φ z) : Φ x ≤ Φ y := by
  sorry

/-- **Tomić–Weyl.** If `x` is weakly majorized by `y` and `φ` is monotone and convex, then
`∑ φ (x i) ≤ ∑ φ (y i)`. [HornJohnson1991, Theorem 3.3.14 context].
Port of `NLAlib.WeaklyMajorized.sum_monotone_convex_le`.
Result: tomic-weyl-inequality -/
theorem WeaklyMajorized.sum_monotone_convex_le {x y : ι → ℝ} (h : WeaklyMajorized x y)
    {φ : ℝ → ℝ} (hφm : Monotone φ) (hφ : ConvexOn ℝ Set.univ φ) :
    ∑ i, φ (x i) ≤ ∑ i, φ (y i) := by
  sorry

/-- Weak majorization is characterised by the hinge functions `u ↦ max (u - a) 0`.
Port of `NLAlib.weaklyMajorized_iff_sum_max_sub_le`. -/
theorem weaklyMajorized_iff_forall_sum_max_sub_le {x y : ι → ℝ} :
    WeaklyMajorized x y ↔ ∀ a : ℝ, ∑ i, max (x i - a) 0 ≤ ∑ i, max (y i - a) 0 := by
  sorry

/-- A weight vector with entries in `[0, 1]` and total `k` picks out at most the sum of the `k`
largest entries. Port of `NLAlib.sum_mul_le_sumLargest`. -/
theorem sum_mul_le_sumLargest (x w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) {k : ℕ}
    (hk : ∑ i, w i = k) : ∑ i, x i * w i ≤ sumLargest x k := by
  sorry

/-- **Rearrangement through majorization.** If `x` is majorized by `y` then for every weight
vector `a` there is a permutation `σ` with `∑ a i * x i ≤ ∑ a i * y (σ i)`.
Port of `NLAlib.Majorized.exists_perm_sum_mul_le`. -/
theorem Majorized.exists_perm_sum_mul_le {x y : ι → ℝ} (h : Majorized x y) (a : ι → ℝ) :
    ∃ σ : Equiv.Perm ι, ∑ i, a i * x i ≤ ∑ i, a i * y (σ i) := by
  sorry

/-- A doubly stochastic transport plan costs at least as much as the best permutation.
Port of `NLAlib.exists_perm_sum_le_doublyStochastic_cost`. -/
theorem exists_perm_sum_le_sum_mul_of_mem_doublyStochastic (C : Matrix ι ι ℝ) {W : Matrix ι ι ℝ}
    (hW : W ∈ doublyStochastic ℝ ι) :
    ∃ σ : Equiv.Perm ι, ∑ i, C i (σ i) ≤ ∑ i, ∑ j, W i j * C i j := by
  sorry

end NLAlib
