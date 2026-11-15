/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Scalar

/-!
# Rounded products

The product $w_0 w_1 \cdots w_j$ of $j + 1$ words, accumulated left to right by $j$ rounded
multiplications (`NLAlib.prodWords`), has relative error at most $(1 + \boldsymbol{u})^j - 1$ in
the standard model of rounded arithmetic: each multiplication multiplies the accumulated relative
error factor by at most $1 + \boldsymbol{u}$. [Higham2002, Lemma 3.1].

## Main definitions

* `NLAlib.prodWords`: the rounded partial products of a sequence of words.

## Main results

* `NLAlib.Ops.StdModel.roundoff_nonneg`: the unit roundoff of a standard model is nonnegative.
* `NLAlib.Ops.StdModel.abs_prodWords_sub_le`: the relative error of a rounded product.
-/

@[expose] public section

namespace NLAlib

open Ops

/-- The **rounded partial products** of the words $w_0, w_1, \dots$ on the machine `M`:
`prodWords M w 0` $= w_0$ and `prodWords M w (j + 1)` $= \mathrm{fl}(\,$`prodWords M w j`
$\cdot\, w_{j+1})$, the product of $w_0, \dots, w_j$ by $j$ multiplications, left to right. -/
def prodWords {K : Type} (M : Machine K) (w : ℕ → K) : ℕ → K
  | 0 => w 0
  | j + 1 => M.mul (prodWords M w j) (w (j + 1))

/-- The unit roundoff of a standard model is nonnegative: the literal $1$ is rounded within
$\boldsymbol{u}$. -/
theorem Ops.StdModel.roundoff_nonneg {K : Type} {u : ℝ} {dec : K → ℝ} {M : Machine K}
    (hM : StdModel u dec M) : 0 ≤ u := by
  have h := hM.lit 1
  simp only [Rat.cast_one, abs_one, mul_one] at h
  exact (abs_nonneg _).trans h

/-- **The rounded product of words**: in the standard model with unit roundoff
$\boldsymbol{u}$ and decoding `dec`, the product of the words $w_0, \dots, w_j$ accumulated by
$j$ rounded multiplications (`NLAlib.prodWords`) satisfies
$$\Bigl\lvert \mathrm{dec}(\mathrm{fl}(w_0 \cdots w_j)) - \prod_{i \le j} \mathrm{dec}(w_i)
\Bigr\rvert \le \bigl((1 + \boldsymbol{u})^j - 1\bigr) \prod_{i \le j} \lvert\mathrm{dec}(w_i)
\rvert.$$
No hypothesis on $\boldsymbol{u}$: the model forces $\boldsymbol{u} \ge 0$. [Higham2002,
Lemma 3.1]. -/
theorem Ops.StdModel.abs_prodWords_sub_le {K : Type} {u : ℝ} {dec : K → ℝ} {M : Machine K}
    (hM : StdModel u dec M) (w : ℕ → K) (j : ℕ) :
    |dec (prodWords M w j) - ∏ i ∈ Finset.range (j + 1), dec (w i)| ≤
      ((1 + u) ^ j - 1) * ∏ i ∈ Finset.range (j + 1), |dec (w i)| := by
  have hu := hM.roundoff_nonneg
  induction j with
  | zero => simp [prodWords]
  | succ j ih =>
    rw [Finset.prod_range_succ (fun i => dec (w i)),
      Finset.prod_range_succ (fun i => |dec (w i)|)]
    set p := ∏ i ∈ Finset.range (j + 1), dec (w i)
    have hp : |p| = ∏ i ∈ Finset.range (j + 1), |dec (w i)| := by
      simp only [p, Finset.abs_prod]
    rw [← hp] at ih ⊢
    set q := dec (prodWords M w j)
    set x := dec (w (j + 1))
    have hmul : |dec (prodWords M w (j + 1)) - q * x| ≤ u * |q * x| := hM.mul _ _
    have hq : |q| ≤ (1 + u) ^ j * |p| := by
      have := abs_sub_abs_le_abs_sub q p
      linarith
    have hpow : 1 ≤ (1 + u) ^ j := one_le_pow₀ (by linarith)
    have htri : |dec (prodWords M w (j + 1)) - p * x| ≤
        |dec (prodWords M w (j + 1)) - q * x| + |q - p| * |x| := by
      rw [← abs_mul, sub_mul]
      exact abs_sub_le _ _ _
    have h1 : u * |q * x| ≤ u * ((1 + u) ^ j * |p|) * |x| := by
      rw [abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hu) (abs_nonneg _)
    have h2 : |q - p| * |x| ≤ ((1 + u) ^ j - 1) * |p| * |x| :=
      mul_le_mul_of_nonneg_right ih (abs_nonneg _)
    calc |dec (prodWords M w (j + 1)) - p * x|
        ≤ u * ((1 + u) ^ j * |p|) * |x| + ((1 + u) ^ j - 1) * |p| * |x| := by linarith
      _ = ((1 + u) ^ (j + 1) - 1) * (|p| * |x|) := by rw [pow_succ]; ring

end NLAlib
