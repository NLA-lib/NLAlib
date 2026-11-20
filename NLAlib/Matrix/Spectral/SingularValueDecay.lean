/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Schatten
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Decay of singular values against the optimal Schatten error

Statements about the singular values $\sigma_0 \ge \sigma_1 \ge \cdots$ of one matrix and its
optimal rank-$k$ error $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}$: a tail count
(if $\sigma_{k+j}$ is not much smaller than $\sigma_k$, the optimal error is at least of order
$(j + 1)^{1/p}\sigma_k$), a comparison of the Frobenius tail with the Schatten tail for
$p \le 2$, and the choice of a head index $L \le k$ with a relative gap before it and a flat
spectrum after it.

## Main results

* `NLAlib.mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow`:
  $(j + 1)\,\sigma_{k+j}^p \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p$.
* `NLAlib.singularValues_rpow_mul_frobNorm_sub_truncatedSVD_sq_le`:
  $\sigma_k^{p-2}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le
  \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p$ for $1 \le p \le 2$.
* `NLAlib.exists_le_singularValues_le_and_gap`: a head index with a gap.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- **Tail count**: for $0 < p < \infty$ and all $k$, $j$,
$$(j + 1)\,\sigma_{k+j}(\mathbf{A})^p \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,,$$
since the $j + 1$ singular values $\sigma_k, \dots, \sigma_{k+j}$ of the tail are at least
$\sigma_{k+j}$. [BakshiClarksonWoodruff2022, proof of Theorem 3.1]; used there with the count of
the wide block in place of $j + 1$. -/
theorem mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ⊤) (A : Matrix m n 𝕜) (k j : ℕ) :
    ((j : ℝ) + 1) * singularValues A (k + j) ^ p.toReal ≤
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  set E := A - truncatedSVD A k
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hN : E.rank ≤ j + 1 + Fintype.card n := by
    have := E.rank_le_card_width
    omega
  rw [schattenNorm_rpow hp0 hp E hN]
  calc ((j : ℝ) + 1) * singularValues A (k + j) ^ p.toReal
        = ∑ _i ∈ Finset.range (j + 1), singularValues A (k + j) ^ p.toReal := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ ∑ i ∈ Finset.range (j + 1), singularValues E i ^ p.toReal :=
        Finset.sum_le_sum fun i hi => by
          rw [singularValues_sub_truncatedSVD]
          exact Real.rpow_le_rpow (singularValues_nonneg _ _)
            (singularValues_antitone A (by simp only [Finset.mem_range] at hi; omega)) hp'.le
    _ ≤ ∑ i ∈ Finset.range (j + 1 + Fintype.card n), singularValues E i ^ p.toReal :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          fun i _ _ => Real.rpow_nonneg (singularValues_nonneg _ _) _

omit [DecidableEq m] [DecidableEq n] in
/-- The Frobenius tail against the Schatten tail: for $1 \le p \le 2$ and every $k$,
$$\sigma_k(\mathbf{A})^{p-2}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,,$$
termwise from $\sigma_i^2\,\sigma_k^{p-2} \le \sigma_i^p$ for $i \ge k$. When $\sigma_k = 0$ and
$p < 2$ the power $\sigma_k^{p-2}$ is $0$ in Lean and the inequality holds. -/
theorem singularValues_rpow_mul_frobNorm_sub_truncatedSVD_sq_le {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ (p.toReal - 2) * frobNorm (A - truncatedSVD A k) ^ 2 ≤
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  set E := A - truncatedSVD A k
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top (by simp) hp2
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hp2' : p.toReal ≤ 2 := by simpa using ENNReal.toReal_mono (by simp) hp2
  have hterm (i : ℕ) : singularValues A k ^ (p.toReal - 2) * singularValues E i ^ 2 ≤
      singularValues E i ^ p.toReal := by
    rw [singularValues_sub_truncatedSVD]
    rcases (singularValues_nonneg A (k + i)).eq_or_lt with h | h
    · rw [← h, zero_pow two_ne_zero, mul_zero]
      exact Real.rpow_nonneg le_rfl _
    · calc _ ≤ singularValues A (k + i) ^ (p.toReal - 2) * singularValues A (k + i) ^ 2 :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos h
              (singularValues_antitone A (Nat.le_add_right k i)) (by linarith)) (sq_nonneg _)
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_add h]; norm_num
  rw [frobNorm_sq_eq_sum_range_singularValues_sq E E.rank_le_card_width,
    schattenNorm_rpow hp0 hpt E E.rank_le_card_width, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hterm i

omit [DecidableEq m] [DecidableEq n] in
/-- **A head index with a gap**: for every matrix $\mathbf{A}$, every $k$ and real $p \ge 1$
there is $L \le k$ such that the spectrum is flat from $L$ to $k$,
$\sigma_L \le (1 + 1/p)\,\sigma_k$, and, when $L = h + 1 \ge 1$, the head is large and is
followed by a relative gap,
$$\Bigl(1 + \frac{1}{2p}\Bigr)\sigma_k < \sigma_h \qquad\text{and}\qquad
\sigma_L^2 \le \Bigl(1 - \frac{1}{2k(p + 1)}\Bigr)\sigma_h^2\,.$$
The index $L = 0$ is allowed and then says $\sigma_0 \le (1 + 1/p)\,\sigma_k$.
[BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there the largest index with a relative gap
$\varepsilon/d$ is taken, which exists only under a condition relating $k$, $p$, $\varepsilon$
and the dimension $d$; here the gap is $1/(2k(p + 1))$ on the squares and there is no
condition. -/
theorem exists_le_singularValues_le_and_gap (A : Matrix m n 𝕜) (k : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ L ≤ k, singularValues A L ≤ (1 + 1 / p) * singularValues A k ∧
      ∀ h, h + 1 = L → (1 + 1 / (2 * p)) * singularValues A k < singularValues A h ∧
        singularValues A L ^ 2 ≤ (1 - 1 / (2 * k * (p + 1))) * singularValues A h ^ 2 := sorry

end NLAlib
