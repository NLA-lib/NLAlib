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

private theorem one_add_one_div_two_mul_sq_le {p : ℝ} (hp : 1 ≤ p) :
    (1 + 1 / (2 * p)) ^ 2 ≤ (1 - 1 / (2 * (p + 1))) * (1 + 1 / p) ^ 2 := by
  have hp0 : 0 < p := by linarith
  rw [show (1 + 1 / (2 * p)) ^ 2 = (2 * p + 1) ^ 2 / (4 * p ^ 2) by field_simp; ring,
    show (1 - 1 / (2 * (p + 1))) * (1 + 1 / p) ^ 2 = (2 * p + 1) * (p + 1) / (2 * p ^ 2) by
      field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

private theorem one_sub_le_one_sub_pow {k : ℕ} (hk : 0 < k) {p : ℝ} (hp : 1 ≤ p) :
    1 - 1 / (2 * (p + 1)) ≤ (1 - 1 / (2 * (k : ℝ) * (p + 1))) ^ k := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ha : 1 / (2 * (k : ℝ) * (p + 1)) ≤ 2 := by
    have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h := one_add_mul_le_pow (a := -(1 / (2 * (k : ℝ) * (p + 1)))) (by linarith) k
  have he : (k : ℝ) * -(1 / (2 * (k : ℝ) * (p + 1))) = -(1 / (2 * (p + 1))) := by
    field_simp
  rwa [he, ← sub_eq_add_neg, ← sub_eq_add_neg] at h

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
        singularValues A L ^ 2 ≤ (1 - 1 / (2 * k * (p + 1))) * singularValues A h ^ 2 := by
  classical
  have hp0 : 0 < p := by linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, le_rfl, le_mul_of_one_le_left (singularValues_nonneg A 0) ?_,
      fun h hh => absurd hh (Nat.succ_ne_zero h)⟩
    have : 0 ≤ 1 / p := by positivity
    linarith
  set σ := singularValues A with hσ
  set T := (1 + 1 / (2 * p)) * σ k with hT
  set c := 1 - 1 / (2 * (k : ℝ) * (p + 1)) with hc
  have hσ0 (i : ℕ) : 0 ≤ σ i := singularValues_nonneg A i
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (hσ0 k)
  have hσk : σ k ≤ T := le_mul_of_one_le_left (hσ0 k) (by
    have : 0 ≤ 1 / (2 * p) := by positivity
    linarith)
  have hc1 : c ≤ 1 := by
    have : 0 ≤ 1 / (2 * (k : ℝ) * (p + 1)) := by positivity
    linarith
  have hc0 : 0 ≤ c := by
    have hk' : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
    have : 1 / (2 * (k : ℝ) * (p + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  let Q : ℕ → Prop := fun L => L = 0 ∨ ∃ h, h + 1 = L ∧ T < σ h ∧ σ L ^ 2 ≤ c * σ h ^ 2
  set L := Nat.findGreatest Q k with hL
  have hQL : Q L := Nat.findGreatest_spec (Nat.zero_le k) (Or.inl rfl)
  have hnot (j : ℕ) (hLj : L ≤ j) (hjk : j < k) (hTj : T < σ j) : c * σ j ^ 2 < σ (j + 1) ^ 2 := by
    by_contra hcon
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_of_le hLj) hjk
      (Or.inr ⟨j, rfl, hTj, not_lt.mp hcon⟩)
  have hdesc (d : ℕ) (hd : L + d ≤ k) : c ^ d * σ L ^ 2 ≤ max (σ (L + d) ^ 2) (T ^ 2) := by
    induction d with
    | zero => simp
    | succ d ih =>
      have ih := ih (by omega)
      rcases le_or_gt (σ (L + d)) T with hle | hlt
      · rw [max_eq_right (pow_le_pow_left₀ (hσ0 _) hle 2)] at ih
        calc c ^ (d + 1) * σ L ^ 2 = c * (c ^ d * σ L ^ 2) := by ring
          _ ≤ 1 * T ^ 2 := mul_le_mul hc1 ih (by positivity) zero_le_one
          _ ≤ _ := by rw [one_mul]; exact le_max_right _ _
      · rw [max_eq_left (pow_le_pow_left₀ hT0 hlt.le 2)] at ih
        calc c ^ (d + 1) * σ L ^ 2 = c * (c ^ d * σ L ^ 2) := by ring
          _ ≤ c * σ (L + d) ^ 2 := mul_le_mul_of_nonneg_left ih hc0
          _ ≤ σ (L + d + 1) ^ 2 := (hnot (L + d) (by omega) (by omega) hlt).le
          _ ≤ _ := le_max_left _ _
  have hLk : L ≤ k := Nat.findGreatest_le k
  have hfin : c ^ k * σ L ^ 2 ≤ T ^ 2 := by
    have h := hdesc (k - L) (by omega)
    rw [Nat.add_sub_cancel' hLk, max_eq_right (pow_le_pow_left₀ (hσ0 _) hσk 2)] at h
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hc0 hc1 (Nat.sub_le k L))
      (sq_nonneg _)).trans h
  refine ⟨L, hLk, ?_, fun h hh => ?_⟩
  · have hb := one_sub_le_one_sub_pow hk hp
    have hb0 : 0 < 1 - 1 / (2 * (p + 1)) := by
      rw [sub_pos, div_lt_one (by positivity)]; linarith
    have hkey := one_add_one_div_two_mul_sq_le hp
    have hsq : σ L ^ 2 ≤ ((1 + 1 / p) * σ k) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hb0
      calc (1 - 1 / (2 * (p + 1))) * σ L ^ 2 ≤ c ^ k * σ L ^ 2 :=
            mul_le_mul_of_nonneg_right hb (sq_nonneg _)
        _ ≤ T ^ 2 := hfin
        _ ≤ (1 - 1 / (2 * (p + 1))) * ((1 + 1 / p) * σ k) ^ 2 := by
            rw [hT, mul_pow, mul_pow, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (hσ0 _) (mul_nonneg (by positivity) (hσ0 k)) two_ne_zero).mp hsq
  · rcases hQL with h0 | ⟨h', hh', hT', hgap⟩
    · omega
    · obtain rfl : h' = h := by omega
      exact ⟨hT', hgap⟩

end NLAlib
