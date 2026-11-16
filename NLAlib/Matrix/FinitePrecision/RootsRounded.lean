/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Scalar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rounded roots of order a power of two

A $k$-th root of a nonnegative scalar with $k = 2^m$ is computed by $m$ rounded square roots,
with relative error at most $3\boldsymbol{u}$: the square root halves the relative error of its
input and adds $\boldsymbol{u}$. No root-finding routine is needed for such $k$; for example,
[BanksGarzaVargasSrivastava2022, Lemma 2.1] assumes a Newton routine for general $k$, with
unspecified constants $c_{\mathrm{root}}, C_{\mathrm{root}}$.

## Main definitions

* `NLAlib.sqrtIter`: $m$ square roots on the machine.

## Main results

* `NLAlib.Ops.StdModel.abs_sqrtIter_sub_le`: the relative error of $m$ rounded square roots.
* `NLAlib.abs_rpow_inv_sub_le_of_abs_sub_pow_le`: a $k$-th root keeps a relative error.
-/

@[expose] public section

namespace NLAlib

open Ops

/-- $m$ square roots of the word `a` on the machine `M`. -/
def sqrtIter {K : Type} (M : Machine K) : ℕ → K → K
  | 0, a => a
  | m + 1, a => sqrtIter M m (M.sqrt a)

private theorem sqrtIter_succ_eq {K : Type} (M : Machine K) (m : ℕ) (a : K) :
    sqrtIter M (m + 1) a = M.sqrt (sqrtIter M m a) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih => exact ih (M.sqrt a)

private theorem abs_sqrtIter_sub_le_aux {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    |sqrtIter M m a - a ^ ((2 : ℝ) ^ m)⁻¹| ≤ 3 * u * a ^ ((2 : ℝ) ^ m)⁻¹ := by
  induction m generalizing a with
  | zero =>
    simp only [sqrtIter, pow_zero, inv_one, Real.rpow_one, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hu) ha
  | succ m ih =>
    rw [sqrtIter_succ_eq]
    have hbd := ih ha
    have ht0 : 0 ≤ a ^ ((2 : ℝ) ^ m)⁻¹ := Real.rpow_nonneg ha _
    have hr0 : 0 ≤ a ^ ((2 : ℝ) ^ (m + 1))⁻¹ := Real.rpow_nonneg ha _
    have htr : a ^ ((2 : ℝ) ^ m)⁻¹ = (a ^ ((2 : ℝ) ^ (m + 1))⁻¹) ^ 2 := by
      rw [show ((a ^ ((2 : ℝ) ^ (m + 1))⁻¹) ^ 2 : ℝ) = a ^ (((2 : ℝ) ^ (m + 1))⁻¹ * 2) from by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num]
      congr 1
      rw [pow_succ]
      field_simp
    generalize a ^ ((2 : ℝ) ^ (m + 1))⁻¹ = r at hr0 htr ⊢
    rw [htr] at hbd ht0
    generalize sqrtIter M m a = x at hbd ⊢
    have hx0 : 0 ≤ x := by nlinarith [(abs_le.mp hbd).1, sq_nonneg r]
    have hsq : |M.sqrt x - √x| ≤ u * √x := hM.sqrt x hx0
    have hs0 : 0 ≤ √x := Real.sqrt_nonneg _
    have hss : (√x) ^ 2 = x := Real.sq_sqrt hx0
    generalize √x = s at hsq hs0 hss
    subst hss
    obtain ⟨h1, h2⟩ := abs_le.mp hbd
    have hd1 : s ^ 2 - r ^ 2 ≤ 3 * u * r ^ 2 := by nlinarith [mul_nonneg hu (sq_nonneg r)]
    have hd2 : r ^ 2 - s ^ 2 ≤ 3 * u * r ^ 2 := by nlinarith [mul_nonneg hu (sq_nonneg r)]
    have hup : s ≤ 1.02 * r := by nlinarith [mul_nonneg hu (sq_nonneg r)]
    have hlo : 0.98 * r ≤ s := by nlinarith [mul_nonneg hu (sq_nonneg r)]
    have hA : u * s ≤ 1.02 * u * r := by nlinarith
    have hB1 : s - r ≤ 1.9 * u * r := by nlinarith [mul_nonneg hu (sq_nonneg r)]
    have hB2 : r - s ≤ 1.9 * u * r := by nlinarith [mul_nonneg hu (sq_nonneg r)]
    have hsr : |s - r| ≤ 1.9 * u * r := abs_le.mpr ⟨by linarith, hB1⟩
    have hfin := abs_sub_le (M.sqrt (s ^ 2)) s r
    linarith [mul_nonneg hu hr0]

/-- A $k$-th root keeps a relative error: if $\lvert t - \tau^k\rvert \le \varepsilon\,\tau^k$
with $\tau \ge 0$, $0 \le \varepsilon \le 1$ and $k \ge 1$, then
$\lvert t^{1/k} - \tau\rvert \le \varepsilon\,\tau$. -/
theorem abs_rpow_inv_sub_le_of_abs_sub_pow_le {k : ℕ} (hk : k ≠ 0) {τ t ε : ℝ} (hτ : 0 ≤ τ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : |t - τ ^ k| ≤ ε * τ ^ k) :
    |t ^ ((k : ℝ)⁻¹) - τ| ≤ ε * τ := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have hτk : 0 ≤ τ ^ k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hinv : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk1
  have hinv0 : 0 ≤ (k : ℝ)⁻¹ := by positivity
  have hroot : (τ ^ k) ^ ((k : ℝ)⁻¹) = τ := Real.pow_rpow_inv_natCast hτ hk
  have hup : t ^ ((k : ℝ)⁻¹) ≤ (1 + ε) * τ := by
    calc t ^ ((k : ℝ)⁻¹) ≤ ((1 + ε) * τ ^ k) ^ ((k : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by nlinarith) (by linarith) hinv0
      _ = (1 + ε) ^ ((k : ℝ)⁻¹) * τ := by rw [Real.mul_rpow (by linarith) hτk, hroot]
      _ ≤ (1 + ε) * τ := by
          gcongr
          calc (1 + ε) ^ ((k : ℝ)⁻¹) ≤ (1 + ε) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) hinv
            _ = 1 + ε := Real.rpow_one _
  have hlo : (1 - ε) * τ ≤ t ^ ((k : ℝ)⁻¹) := by
    calc (1 - ε) * τ ≤ (1 - ε) ^ ((k : ℝ)⁻¹) * τ := by
          gcongr
          calc 1 - ε = (1 - ε) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (1 - ε) ^ ((k : ℝ)⁻¹) :=
                Real.rpow_le_rpow_of_exponent_ge' (by linarith) (by linarith) hinv0 hinv
      _ = ((1 - ε) * τ ^ k) ^ ((k : ℝ)⁻¹) := by rw [Real.mul_rpow (by linarith) hτk, hroot]
      _ ≤ t ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by nlinarith) (by linarith) hinv0
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Rounded roots of order $2^m$**: under the standard model with $0 \le \boldsymbol{u} \le
1/100$, $m$ rounded square roots of $a \ge 0$ are within $3\boldsymbol{u}\,a^{1/2^m}$ of
$a^{1/2^m}$. [BanksGarzaVargasSrivastava2022, Lemma 2.1], for $k = 2^m$. -/
theorem Ops.StdModel.abs_sqrtIter_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    |sqrtIter M m a - a ^ ((2 : ℝ) ^ m)⁻¹| ≤ 3 * u * a ^ ((2 : ℝ) ^ m)⁻¹ :=
  abs_sqrtIter_sub_le_aux hM hu hu' m ha

end NLAlib
