/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Dense

/-!
# The bits of precision and the operation count of the dense Schur solver

The parameters of `NLAlib.Schur.denseSchur` as functions of $L = \log_2(4(n + 1)/(\delta\varphi))$:
the arguments of the stages' bits are polynomial in $2^L$ (`NLAlib.Schur.denseSchur_arg_bounds`),
the shift degree is $O(L\log L)$ and the caps polylogarithmic
(`NLAlib.Schur.denseSchur_caps_le`). Hence the precision threshold has $O(L^4\log^2 L)$ bits
and the static count is $O((n + 1)^3L^9\log^6 L)$.

## Main results

* `NLAlib.Schur.logb_inv_uDenseSchur_le`: the bits of precision.
* `NLAlib.Schur.uDenseSchurAt_pos`, `NLAlib.Schur.logb_inv_uDenseSchurAt_le`: the threshold at
  two tolerances is positive, with the same bits.
* `NLAlib.Schur.denseSchur_work_le_polylog`: the operation count is $O(n^3L^9\log^6 L)$.
* `NLAlib.Schur.denseSchur_work_le_pow`: its cruder form $O(n^3L^{15})$.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops ShiftedQR SmallEig Real


/-- The arguments of the bits are polynomial in $Y = 4(n + 1)/(\delta\varphi)$: there is an
exponent $E$ such that for $0 < \delta \le 1$ and $0 < \varphi \le 1$, $Y \ge 4$, the argument
$Y_c = 4(n + 1)(2B)8^2/(\delta'\min(\Gamma/2, 8)(\varphi/2))$ of the core's bits and the
condition bound $2B$ are at most $Y^E$, and the regularizer's precision term, $t_1t_2/(28800(n +
1)^3)$, $\delta'/(3200(n + 1)^2)$, $\delta/(64(n + 1))$ and $\delta$ are at least $Y^{-E}$ (the
thresholds $t_1, t_2$ of `NLAlib.SmallEig.exists_loBd_smallEigCond_gap_reduce`). -/
theorem denseSchur_arg_bounds : ∃ E : ℕ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ → φ ≤ 1 →
    4 ≤ 4 * ((n : ℝ) + 1) / (δ * φ) ∧
    HiBd (4 * ((n : ℝ) + 1) / (δ * φ)) E
      (4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
        (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2))) ∧
    HiBd (4 * ((n : ℝ) + 1) / (δ * φ)) E (2 * denseSchurB n δ φ) ∧
    LoBd (4 * ((n : ℝ) + 1) / (δ * φ)) E (uSmallEigReduce (n + 1) 4 (denseSchurDelta n δ)
      (φ / 2) ginibreGapTail ginibreConditionTail) ∧
    LoBd (4 * ((n : ℝ) + 1) / (δ * φ)) E
      (smallEigGap (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail *
        smallEigCond (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreConditionTail /
          (28800 * ((n : ℝ) + 1) ^ 3)) ∧
    LoBd (4 * ((n : ℝ) + 1) / (δ * φ)) E (denseSchurDelta n δ / (3200 * ((n : ℝ) + 1) ^ 2)) ∧
    LoBd (4 * ((n : ℝ) + 1) / (δ * φ)) E (δ / (64 * ((n : ℝ) + 1))) ∧
    LoBd (4 * ((n : ℝ) + 1) / (δ * φ)) E δ := by
  obtain ⟨e, he⟩ := exists_loBd_smallEigCond_gap_reduce (c₁ := ginibreGapTail)
    (c₂ := ginibreConditionTail) ginibreGapTail_b_pos ginibreConditionTail_b_pos
  refine ⟨20 * e + 40, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hd0, hd1, hg, hc, hc1, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  set Y := 4 * N / (δ * φ) with hYdef
  have hδφ : 0 < δ * φ := mul_pos hδ hφ
  have hδφ1 : δ * φ ≤ 1 := by nlinarith
  have hY : 4 * N ≤ Y := by rw [hYdef, le_div_iff₀ hδφ]; nlinarith
  have hY4 : 4 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hNY : HiBd Y 1 N := ⟨by linarith, by rw [pow_one]; linarith⟩
  have hδY : LoBd Y 1 δ := ⟨hδ, by
    rw [pow_one, hYdef, mul_div_assoc', le_div_iff₀ hδφ]; nlinarith⟩
  have hφY : LoBd Y 1 φ := ⟨hφ, by
    rw [pow_one, hYdef, mul_div_assoc', le_div_iff₀ hδφ]; nlinarith⟩
  have hsq : HiBd Y 1 (√N) := ⟨by positivity, by
    rw [pow_one, Real.sqrt_le_left (by linarith)]; nlinarith⟩
  have hδ' : LoBd Y 4 (denseSchurDelta n δ) := by
    have := hδY.div ((HiBd.const hY4 (by norm_num : (0 : ℝ) < 16)
      (by norm_num : (16 : ℝ) ≤ 4 ^ 2)).mul hsq)
    simpa [denseSchurDelta, hN] using this
  have hφ2 : LoBd Y 2 (φ / 2) :=
    hφY.div (HiBd.const hY4 (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 4 ^ 1))
  set A := 4 * ((n + 1 : ℕ) : ℝ) * 4 / (denseSchurDelta n δ * (φ / 2)) with hA
  have hAY : HiBd Y 9 A := by
    have h := (((HiBd.const hY4 (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 4 ^ 1)).mul
      hNY).mul (HiBd.const hY4 (by norm_num : (0 : ℝ) < 4)
        (by norm_num : (4 : ℝ) ≤ 4 ^ 1))).div (hδ'.mul hφ2)
    simpa [hA, hN] using h
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ (by positivity)]
    push_cast
    have : denseSchurDelta n δ * (φ / 2) ≤ 1 := by nlinarith
    nlinarith
  obtain ⟨ht2, ht1, hR⟩ := he (nmax := n + 1) (S := 4) (δ := denseSchurDelta n δ) (φ := φ / 2)
    (by omega) hd0 (by linarith) (half_pos hφ) (by linarith)
  have ht2Y := ht2.of_hiBd hA1 hAY
  have ht1Y := ht1.of_hiBd hA1 hAY
  have hRY := hR.of_hiBd hA1 hAY
  have hBc : HiBd Y (1 + 9 * e) (2 * denseSchurB n δ φ) := by
    have h := (HiBd.const hY4 (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 4 ^ 1)).mul
      (HiBd.inv ht2Y)
    refine h.of_le (by linarith) (le_of_eq ?_)
    unfold denseSchurB; field_simp; ring
  have hΓc : LoBd Y (9 * e) (denseSchurΓ n δ φ / 2) := by
    refine ht1Y.of_le (le_of_eq ?_)
    unfold denseSchurΓ; ring
  have hm : LoBd Y (9 * e) (min (denseSchurΓ n δ φ / 2) 8) :=
    hΓc.min (LoBd.const hY4 (by norm_num) (by
      have : (1 : ℝ) ≤ 4 ^ (9 * e) := one_le_pow₀ (by norm_num)
      linarith))
  have hYc := ((((HiBd.const hY4 (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 4 ^ 1)).mul
      hNY).mul hBc).mul (HiBd.const hY4 (by norm_num : (0 : ℝ) < 8 ^ 2)
        (by norm_num : (8 : ℝ) ^ 2 ≤ 4 ^ 3))).div ((hδ'.mul hm).mul hφ2)
  have ht12 := ((ht1Y.of_le (by linarith : smallEigGap (n + 1) 4 (denseSchurDelta n δ) (φ / 2)
      ginibreGapTail / 4 ≤ smallEigGap (n + 1) 4 (denseSchurDelta n δ) (φ / 2)
        ginibreGapTail)).mul ht2Y).div ((HiBd.const hY4 (by norm_num : (0 : ℝ) < 28800)
      (by norm_num : (28800 : ℝ) ≤ 4 ^ 8)).mul (hNY.pow 3))
  have hd3 := hδ'.div ((HiBd.const hY4 (by norm_num : (0 : ℝ) < 3200)
      (by norm_num : (3200 : ℝ) ≤ 4 ^ 6)).mul (hNY.pow 2))
  have hd64 := hδY.div ((HiBd.const hY4 (by norm_num : (0 : ℝ) < 64)
      (by norm_num : (64 : ℝ) ≤ 4 ^ 3)).mul hNY)
  refine ⟨hY4, hYc.mono hY1 (by omega), hBc.mono hY1 (by omega), hRY.mono hY1 (by omega),
    ht12.mono hY1 (by omega), hd3.mono hY1 (by omega), hd64.mono hY1 (by omega),
    hδY.mono hY1 (by omega)⟩


private theorem logb_two_four : logb 2 (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, logb_pow, logb_self_eq_one one_lt_two]; norm_num

private theorem two_le_logb_of_four_le {Y : ℝ} (hY : 4 ≤ Y) : 2 ≤ logb 2 Y := by
  have := logb_le_logb_of_le one_lt_two (by norm_num) hY
  rwa [logb_two_four] at this

/-- The shift degree is $O(L\log L)$: there is a constant $K \ge 0$ with
$k \le KL(\log_2 L + 1)$, $L = \log_2(4(n + 1)/(\delta\varphi))$, for $0 < \delta \le 1$ and
$0 < \varphi \le 1$ (`NLAlib.ShiftedQR.shqrDegree_le_log`, the condition bound being polynomial). -/
theorem denseSchurDegree_le_log : ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → (denseSchurDegree n δ φ : ℝ) ≤ K * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) *
      (logb 2 (logb 2 (4 * ((n : ℝ) + 1) / (δ * φ))) + 1) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨c, hc⟩ := shqrDegree_le_log
  set c' := max c 0
  have hc' : 0 ≤ c' := le_max_right _ _
  have hE2 : (1 : ℝ) ≤ logb 2 ((E : ℝ) + 2) := by
    rw [le_logb_iff_rpow_le one_lt_two (by positivity), rpow_one]; linarith [E.cast_nonneg (α := ℝ)]
  set K := c' * ((E : ℝ) + 2) * (logb 2 ((E : ℝ) + 2) + 1) with hK
  refine ⟨K, by positivity, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, hYc, hBc, -, -, -, -, -⟩ := hE (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  set Y := 4 * ((n : ℝ) + 1) / (δ * φ) with hYdef
  set L := logb 2 Y with hLdef
  have hL2 : 2 ≤ L := two_le_logb_of_four_le hY4
  have hlL : 1 ≤ logb 2 L := by
    rw [le_logb_iff_rpow_le one_lt_two (by linarith), rpow_one]; exact hL2
  have hE0 : (0 : ℝ) ≤ E := E.cast_nonneg
  set k := denseSchurDegree n δ φ with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    have := denseSchurDegree_pos n δ φ; exact_mod_cast this
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  have hB0 : (0 : ℝ) < 2 * denseSchurB n δ φ := by linarith
  have hlB : logb 2 (2 * denseSchurB n δ φ) ≤ E * L := hBc.logb_le
  have hlB0 : 0 ≤ logb 2 (2 * denseSchurB n δ φ) := logb_nonneg one_lt_two hB1
  have h := hc (B := 2 * denseSchurB n δ φ) hB1
  have hx1 : logb 2 (4 * (2 * denseSchurB n δ φ)) + 1 ≤ (E + 2) * L := by
    rw [logb_mul (by norm_num) hB0.ne', logb_two_four]; nlinarith
  have hx2 : logb 2 (16 * (2 * denseSchurB n δ φ)) = 4 + logb 2 (2 * denseSchurB n δ φ) := by
    rw [logb_mul (by norm_num) hB0.ne', show (16 : ℝ) = 2 ^ 4 by norm_num, logb_pow,
      logb_self_eq_one one_lt_two]; norm_num
  have hy : logb 2 (logb 2 (16 * (2 * denseSchurB n δ φ))) + 1 ≤
      (logb 2 ((E : ℝ) + 2) + 1) * (logb 2 L + 1) := by
    rw [hx2]
    have h1 : logb 2 (4 + logb 2 (2 * denseSchurB n δ φ)) ≤ logb 2 (((E : ℝ) + 2) * L) :=
      logb_le_logb_of_le one_lt_two (by linarith) (by nlinarith)
    have h2 : logb 2 (((E : ℝ) + 2) * L) = logb 2 ((E : ℝ) + 2) + logb 2 L :=
      logb_mul (by positivity) (by positivity)
    rw [h2] at h1
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ logb 2 ((E : ℝ) + 2))
      (by linarith : (0 : ℝ) ≤ logb 2 L)]
  have hy0 : 0 ≤ logb 2 (logb 2 (16 * (2 * denseSchurB n δ φ))) + 1 := by
    rw [hx2]
    have := logb_nonneg one_lt_two (by linarith : (1 : ℝ) ≤ 4 + logb 2 (2 * denseSchurB n δ φ))
    linarith
  have hx0 : 0 ≤ logb 2 (4 * (2 * denseSchurB n δ φ)) + 1 := by
    have := logb_nonneg one_lt_two (by linarith : (1 : ℝ) ≤ 4 * (2 * denseSchurB n δ φ))
    linarith
  have hkB : (k : ℝ) = shqrDegree (4 * (2 * denseSchurB n δ φ)) := rfl
  calc (k : ℝ) ≤ c * (logb 2 (4 * (2 * denseSchurB n δ φ)) + 1) *
        (logb 2 (logb 2 (16 * (2 * denseSchurB n δ φ))) + 1) := hkB ▸ h
    _ ≤ c' * (logb 2 (4 * (2 * denseSchurB n δ φ)) + 1) *
        (logb 2 (logb 2 (16 * (2 * denseSchurB n δ φ))) + 1) := by
        gcongr; exact le_max_left _ _
    _ ≤ c' * ((E + 2) * L) * ((logb 2 ((E : ℝ) + 2) + 1) * (logb 2 L + 1)) := by gcongr
    _ = c' * ((E : ℝ) + 2) * (logb 2 ((E : ℝ) + 2) + 1) * L * (logb 2 L + 1) := by ring
    _ = K * L * (logb 2 L + 1) := by rw [hK]

/-- The iteration cap is $O(L)$: there is a constant $K \ge 0$ with $F \le KL$,
$L = \log_2(4(n + 1)/(\delta\varphi))$, for $0 < \delta \le 1$ and $0 < \varphi \le 1$
(`NLAlib.ShiftedQR.shqrCap_le_log`). -/
theorem denseSchurCap_le_log : ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → (denseSchurCap n δ φ : ℝ) ≤ K * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨cF, hcF⟩ := shqrCap_le_log
  set cF' := max cF 0
  have hcF' : 0 ≤ cF' := le_max_right _ _
  set K := cF' * ((E : ℝ) + 1) with hK
  refine ⟨K, by positivity, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, hYc, hBc, -, -, -, -, -⟩ := hE (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  set Y := 4 * ((n : ℝ) + 1) / (δ * φ) with hYdef
  set L := logb 2 Y with hLdef
  have hL2 : 2 ≤ L := two_le_logb_of_four_le hY4
  have hlL : 1 ≤ logb 2 L := by
    rw [le_logb_iff_rpow_le one_lt_two (by linarith), rpow_one]; exact hL2
  have hE0 : (0 : ℝ) ≤ E := E.cast_nonneg
  set k := denseSchurDegree n δ φ with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    have := denseSchurDegree_pos n δ φ; exact_mod_cast this
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  have hB0 : (0 : ℝ) < 2 * denseSchurB n δ φ := by linarith
  have hlB : logb 2 (2 * denseSchurB n δ φ) ≤ E * L := hBc.logb_le
  have hlB0 : 0 ≤ logb 2 (2 * denseSchurB n δ φ) := logb_nonneg one_lt_two hB1
  obtain ⟨hYc4, -⟩ := shqrArg_facts (n := n) (k := shqrDegree (4 * (2 * denseSchurB n δ φ)))
    hB1 (half_pos hΓ) hd0 (by linarith : denseSchurDelta n δ ≤ 8) (half_pos hφ) (by linarith) rfl
  have h := hcF (n := n) hB1 (half_pos hΓ) hd0 (by linarith : denseSchurDelta n δ ≤ 8)
    (half_pos hφ) (by linarith)
  have hl := hYc.logb_le
  have hl0 := logb_nonneg one_lt_two (by linarith : (1 : ℝ) ≤ 4 * ((n : ℝ) + 1) *
    (2 * denseSchurB n δ φ) * 8 ^ 2 /
      (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2)))
  have hF : (denseSchurCap n δ φ : ℝ) ≤ cF' * (E * L + 1) := by
    refine h.trans ?_
    calc cF * logb 2 (4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
          (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2))) + cF
        = cF * (logb 2 (4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
          (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2))) + 1) := by ring
      _ ≤ cF' * (logb 2 (4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
          (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2))) + 1) := by
          gcongr; exact le_max_left _ _
      _ ≤ cF' * (E * L + 1) := by gcongr
  calc (denseSchurCap n δ φ : ℝ) ≤ cF' * (E * L + 1) := hF
    _ ≤ cF' * ((E + 1) * L) := by gcongr; nlinarith
    _ = cF' * (E + 1) * L := by ring
    _ = K * L := by rw [hK]

/-- The leaf cap is $O(kL)$: there is a constant $K \ge 0$ with $T \le K(k + 1)L$,
$L = \log_2(4(n + 1)/(\delta\varphi))$, for $0 < \delta \le 1$ and $0 < \varphi \le 1$
(`NLAlib.SmallEig.smallEigCap_le_logb` at the argument of
`NLAlib.ShiftedQR.hiBd_smallEigForwardArg`). -/
theorem denseSchurLeafCap_le_log : ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 →
    0 < φ → φ ≤ 1 → (denseSchurLeafCap n δ φ : ℝ) ≤
      K * ((denseSchurDegree n δ φ : ℝ) + 1) * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨cT, hcT0, hcT⟩ := smallEigCap_le_logb ginibreGapTail ginibreConditionTail
    ginibreGapTail_b_pos ginibreConditionTail_b_pos
  set K := cT * (36 * (E : ℝ) + 1) with hK
  refine ⟨K, by positivity, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, hYc, hBc, -, -, -, -, -⟩ := hE (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  set Y := 4 * ((n : ℝ) + 1) / (δ * φ) with hYdef
  set L := logb 2 Y with hLdef
  have hL2 : 2 ≤ L := two_le_logb_of_four_le hY4
  have hlL : 1 ≤ logb 2 L := by
    rw [le_logb_iff_rpow_le one_lt_two (by linarith), rpow_one]; exact hL2
  have hE0 : (0 : ℝ) ≤ E := E.cast_nonneg
  set k := denseSchurDegree n δ φ with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    have := denseSchurDegree_pos n δ φ; exact_mod_cast this
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  have hB0 : (0 : ℝ) < 2 * denseSchurB n δ φ := by linarith
  have hlB : logb 2 (2 * denseSchurB n δ φ) ≤ E * L := hBc.logb_le
  have hlB0 : 0 ≤ logb 2 (2 * denseSchurB n δ φ) := logb_nonneg one_lt_two hB1
  have hΓ2 : 0 < denseSchurΓ n δ φ / 2 := half_pos hΓ
  have hβ := shqrSmallEigAccuracy_pos (n := n) hB1 hΓ2 hd0 (by norm_num : (0 : ℝ) < 8)
  have hβS := shqrSmallEigAccuracy_le (n := n) hB1 hΓ2 hd0 (by linarith : denseSchurDelta n δ ≤ 8)
  obtain ⟨hf0, hfS, -⟩ := forwardBackwardError_spec (kmax := k) hβ (by linarith : _ ≤ (32 : ℝ))
  have hφL := shqrSmallEigFailure_pos (n := n) (B := 2 * denseSchurB n δ φ)
    (Γ := denseSchurΓ n δ φ / 2) (S := 8) (δ := denseSchurDelta n δ) (half_pos hφ)
  have hφL1 := shqrSmallEigFailure_le (n := n) (B := 2 * denseSchurB n δ φ)
    (Γ := denseSchurΓ n δ φ / 2) (S := 8) (δ := denseSchurDelta n δ) (half_pos hφ).le
  have hT := hcT (nmax := k) (by exact_mod_cast hk1) hf0 hfS hφL (by linarith)
  obtain ⟨-, hA⟩ := hiBd_smallEigForwardArg (n := n) (k := k) hB1 hΓ2 hd0
    (by linarith : denseSchurDelta n δ ≤ 8) (half_pos hφ) (by linarith) rfl
  rw [show (4 : ℝ) * 8 = 32 by norm_num] at hA
  have hlA := (hA.logb_le).trans (mul_le_mul_of_nonneg_left hYc.logb_le (by positivity))
  have hTe : (denseSchurLeafCap n δ φ : ℝ) = smallEigCap k 32
      (forwardBackwardError k 32 (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ)
        (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ)))
      (shqrSmallEigFailure n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
        (denseSchurDelta n δ) (φ / 2)) ginibreGapTail ginibreConditionTail := by
    rw [denseSchurLeafCap_eq]; rfl
  rw [hTe]
  refine hT.trans ?_
  push_cast at hlA ⊢
  have hkL : 1 ≤ ((k : ℝ) + 1) * L := by nlinarith
  calc cT * (logb 2 (4 * (k : ℝ) * 32 / (forwardBackwardError k 32
        (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
          (denseSchurDelta n δ)) * shqrSmallEigFailure n (2 * denseSchurB n δ φ)
            (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ) (φ / 2))) + 1)
      ≤ cT * ((26 + 36 * (k : ℝ)) * (E * L) + 1) := by gcongr
    _ ≤ cT * ((36 * E + 1) * ((k + 1) * L)) := by gcongr; nlinarith
    _ = cT * (36 * E + 1) * (k + 1) * L := by ring
    _ = K * (k + 1) * L := by rw [hK]



/-- The shift degree and the caps are polylogarithmic: there is a constant $K \ge 0$ such
that for $0 < \delta \le 1$ and $0 < \varphi \le 1$, with $L = \log_2(4(n + 1)/(\delta\varphi))
\ge 2$, the shift degree is $k \le KL(\log_2 L + 1)$, the iteration cap $F \le KL$ and the leaf
cap $T \le K(k + 1)L$ (`NLAlib.Schur.denseSchurDegree_le_log`, `NLAlib.Schur.denseSchurCap_le_log`,
`NLAlib.Schur.denseSchurLeafCap_le_log`). -/
theorem denseSchur_caps_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → 2 ≤ logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) ∧
      (denseSchurDegree n δ φ : ℝ) ≤ K * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) *
        (logb 2 (logb 2 (4 * ((n : ℝ) + 1) / (δ * φ))) + 1) ∧
      (denseSchurCap n δ φ : ℝ) ≤ K * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) ∧
      (denseSchurLeafCap n δ φ : ℝ) ≤
        K * ((denseSchurDegree n δ φ : ℝ) + 1) * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨K₁, hK₁, h₁⟩ := denseSchurDegree_le_log
  obtain ⟨K₂, hK₂, h₂⟩ := denseSchurCap_le_log
  obtain ⟨K₃, hK₃, h₃⟩ := denseSchurLeafCap_le_log
  refine ⟨max K₁ (max K₂ K₃), le_max_of_le_left hK₁, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  have hL := two_le_logb_of_four_le (hE (n := n) hδ hδ1 hφ hφ1).1
  have hl : 0 ≤ logb 2 (logb 2 (4 * ((n : ℝ) + 1) / (δ * φ))) + 1 := by
    have := logb_nonneg one_lt_two (by linarith : (1 : ℝ) ≤ logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)))
    linarith
  have hk : (0 : ℝ) ≤ denseSchurDegree n δ φ := Nat.cast_nonneg _
  refine ⟨hL, (h₁ hδ hδ1 hφ hφ1).trans ?_, (h₂ hδ hδ1 hφ hφ1).trans ?_,
    (h₃ hδ hδ1 hφ hφ1).trans ?_⟩
  · gcongr; exact le_max_left _ _
  · gcongr; exact le_max_of_le_right (le_max_left _ _)
  · gcongr; exact le_max_of_le_right (le_max_right _ _)

private theorem logb_two_le_two_mul {L : ℝ} (hL : 1 ≤ L) : logb 2 L ≤ 2 * L := by
  have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < L)
  have h2 := Real.log_two_gt_d9
  rw [logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- The shifted QR words of the core are at most $426680$: Exc's net at $\varepsilon \ge 1/100$
has at most $213334$ points (`NLAlib.length_squareGrid_le`). -/
theorem length_denseSchurShQRParams_le {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    ((denseSchurShQRParams n δ φ).length : ℝ) ≤ 426680 := by
  obtain ⟨-, -, -, -, -, hB, -⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  have hB4 : (1 : ℝ) ≤ 4 * (2 * denseSchurB n δ φ) := by linarith
  have he := shqrEps_ge hB4
  have he2 := shqrEps_le_half hB4
  set ε := shqrEps (shqrDegree (4 * (2 * denseSchurB n δ φ))) (4 * (2 * denseSchurB n δ φ))
  have hg := length_squareGrid_le 0 1.3 (ε := 3 * ε / 4) (by linarith) (by linarith)
  have hq : 12 / (3 * ε / 4) ^ 2 ≤ 213334 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  simp only [denseSchurShQRParams, shqrParams, length_roundedDecoupleParams, denseSchurDegree]
  push_cast
  have : ((excNet ε).length : ℝ) ≤ 213334 := by
    unfold excNet; exact hg.trans hq
  linarith


private theorem logb_inv_min_le {x y M : ℝ} (hx : logb 2 x⁻¹ ≤ M) (hy : logb 2 y⁻¹ ≤ M) :
    logb 2 (min x y)⁻¹ ≤ M := by
  rcases min_choice x y with h | h <;> rw [h] <;> assumption

private theorem logb_inv_le_logb_inv {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    logb 2 y⁻¹ ≤ logb 2 x⁻¹ :=
  logb_le_logb_of_le one_lt_two (inv_pos.mpr (hx.trans_le hxy)) (inv_anti₀ hx hxy)

private theorem rotations_le_pow {N k F np T X : ℝ} (hN0 : 0 ≤ N) (hk0 : 0 ≤ k) (hF0 : 0 ≤ F)
    (hnp0 : 0 ≤ np) (hT0 : 0 ≤ T) (hX : 1 ≤ X) (hN : N ≤ X) (hk : k ≤ X) (hF : F ≤ X)
    (hnp : np ≤ X) (hT : T ≤ X) :
    N ^ 2 + (2 * N * (F * (k + 1 + np) * (k * N) + 2 * k * (k + 2)) +
      N * (k * k + 2 * (k + 1) * ((T + k) * k + 6))) ≤ 52 * X ^ 5 := by
  have h1 : k + 1 + np ≤ 3 * X := by linarith
  have h2 : k + 2 ≤ 3 * X := by linarith
  have h3 : k + 1 ≤ 2 * X := by linarith
  have h4 : (T + k) * k + 6 ≤ 8 * X ^ 2 := by nlinarith
  have hX0 : 0 ≤ X := by linarith
  calc N ^ 2 + (2 * N * (F * (k + 1 + np) * (k * N) + 2 * k * (k + 2)) +
        N * (k * k + 2 * (k + 1) * ((T + k) * k + 6)))
      ≤ X ^ 2 + (2 * X * (X * (3 * X) * (X * X) + 2 * X * (3 * X)) +
        X * (X * X + 2 * (2 * X) * (8 * X ^ 2))) := by gcongr
    _ ≤ 52 * X ^ 5 := by
      have a2 : X ^ 2 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
      have a3 : X ^ 3 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
      have a4 : X ^ 4 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
      nlinarith

/-- The words of the core are between $1$ and $426692$. -/
theorem denseSchur_np_bounds {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) :
    (1 : ℝ) ≤ (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length ∧
      ((denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length : ℝ) ≤ 426692 := by
  have := length_denseSchurShQRParams_le (n := n) hδ hδ1 hφ hφ1
  simp only [List.length_append, denseSchurLeafParams, smallEigForwardParams,
    length_smallEigParams]
  push_cast
  exact ⟨by linarith [(denseSchurShQRParams n δ φ).length.cast_nonneg (α := ℝ)], by linarith⟩

/-- The replay term of the precision threshold without the leaf term is polynomially small:
`NLAlib.ShiftedQR.uShQRSchurReplay` at $R_L = 0$ is at least $Y^{-e}$,
$Y = 4(n + 1)/(\delta\varphi)$. -/
private theorem denseSchur_replay_zero_loBd : ∃ e : ℕ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 →
    0 < φ → φ ≤ 1 → LoBd (4 * ((n : ℝ) + 1) / (δ * φ)) e
      (uShQRSchurReplay n (denseSchurDegree n δ φ)
        (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length (denseSchurCap n δ φ) 0
        (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ)) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  refine ⟨E * 70, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, hYc, -, -, -, -, -, -⟩ := hE (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hnp1, hnp⟩ := denseSchur_np_bounds (n := n) hδ hδ1 hφ hφ1
  clear hE
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  obtain ⟨hYc4, hkY, hNY, hbs, -, hFY, -⟩ := shqrArg_facts (n := n)
    (k := denseSchurDegree n δ φ) hB1 (half_pos hΓ) hd0 (by linarith : denseSchurDelta n δ ≤ 8)
    (half_pos hφ) (by linarith) rfl
  set Yc := 4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
    (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2))
  have hYc1 : 1 ≤ Yc := by linarith
  have hY2 : 2 ≤ Yc := by linarith
  set k := denseSchurDegree n δ φ with hkdef
  set F := denseSchurCap n δ φ
  set np := (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length
  have hnpY : HiBd Yc 10 (np : ℝ) := (HiBd.const hYc4 (by norm_num : (0 : ℝ) < 426692)
    (by norm_num : (426692 : ℝ) ≤ 4 ^ 10)).of_le (by linarith) hnp
  have h1 : HiBd Yc 0 (1 : ℝ) := HiBd.const hYc4 one_pos (by norm_num)
  have hLS : HiBd Yc 43 ((F : ℝ) * (k + 1 + np) * (k * ((n : ℝ) + 1))) :=
    (hFY.mul ((hkY.add' hY2 h1).add' hY2 hnpY)).mul (hkY.mul hNY)
  have hden := ((HiBd.const hYc4 (by norm_num : (0 : ℝ) < 16) (by norm_num : (16 : ℝ) ≤ 4 ^ 2)).mul
    hNY).mul (((HiBd.const hYc4 (by norm_num : (0 : ℝ) < 78)
      (by norm_num : (78 : ℝ) ≤ 4 ^ 4)).mul hLS).add' hY2
    (((HiBd.const hYc4 (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) ≤ 4 ^ 2)).mul hNY).mul
      (hkY.add' hY2 (HiBd.const hYc4 (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≤ 4 ^ 1)))))
  have hrep : LoBd Yc 70 (uShQRSchurReplay n k np F 0 (2 * denseSchurB n δ φ)
      (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ)) := by
    refine (hbs.div hden).of_le (le_of_eq ?_)
    unfold uShQRSchurReplay shqrSchurLogSize
    push_cast
    rw [mul_zero, add_zero]
    field_simp
  exact hrep.of_hiBd hYc1 hYc

/-- The rotation count is polynomial: there is an exponent $P$ such that for
$0 < \delta \le 1$ and $0 < \varphi \le 1$ the rotation count $R$ =
`NLAlib.Schur.denseSchurRotations` is at most $Y^P$, $Y = 4(n + 1)/(\delta\varphi)$: $R$ is a
polynomial in $n + 1$, $k$, $F$, $T$ and the number of words. -/
theorem denseSchurRotations_hiBd : ∃ P : ℕ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → HiBd (4 * ((n : ℝ) + 1) / (δ * φ)) P (denseSchurRotations n δ φ) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨K, hK0, hK⟩ := denseSchurLeafCap_le_log
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt (426693 + 4 * K) (by norm_num : (1 : ℝ) < 4)
  refine ⟨3 + 5 * a + 5 * (12 * E + 1), fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, hYc, -, -, -, -, -, -⟩ := hE (n := n) hδ hδ1 hφ hφ1
  have hT := hK (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  obtain ⟨-, hnp⟩ := denseSchur_np_bounds (n := n) hδ hδ1 hφ hφ1
  clear hE hK
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  obtain ⟨hYc4, hkY, -, -, -, hFY, -⟩ := shqrArg_facts (n := n)
    (k := denseSchurDegree n δ φ) hB1 (half_pos hΓ) hd0 (by linarith : denseSchurDelta n δ ≤ 8)
    (half_pos hφ) (by linarith) rfl
  set Y := 4 * ((n : ℝ) + 1) / (δ * φ) with hYdef
  have hY1 : 1 ≤ Y := by linarith
  have hYc1 : 1 ≤ 4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
    (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2)) := by linarith
  set k := denseSchurDegree n δ φ with hkdef
  set F := denseSchurCap n δ φ
  set T := denseSchurLeafCap n δ φ
  set np := (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast denseSchurDegree_pos n δ φ
  set m := 12 * E + 1
  set X := (4 : ℝ) ^ a * Y ^ m
  have hYm : ∀ j ≤ m, Y ^ j ≤ X := fun j hj =>
    (pow_le_pow_right₀ hY1 hj).trans (le_mul_of_one_le_left (by positivity)
      (one_le_pow₀ (by norm_num)))
  have hX1 : 1 ≤ X := (one_le_pow₀ hY1).trans (hYm 0 (by omega))
  have hkX : (k : ℝ) ≤ X := ((hkY.of_hiBd hYc1 hYc).2).trans (hYm _ (by omega))
  have hFX : (F : ℝ) ≤ X := ((hFY.of_hiBd hYc1 hYc).2).trans (hYm _ (by omega))
  have hNX : (n : ℝ) + 1 ≤ X := by
    have : (n : ℝ) + 1 ≤ Y := by
      have hδφ : δ * φ ≤ 1 := by nlinarith
      rw [hYdef, le_div_iff₀ (by positivity)]; nlinarith
    exact this.trans ((pow_one Y).symm.le.trans (hYm 1 (by omega)))
  have hnpX : (np : ℝ) ≤ X := by
    have : (4 : ℝ) ^ a ≤ X := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hY1)
    linarith
  have hTX : (T : ℝ) ≤ X := by
    have hL := logb_two_le_two_mul hY1
    have hk9 : (k : ℝ) ≤ Y ^ (E * 9) := (hkY.of_hiBd hYc1 hYc).2
    have hT' : (T : ℝ) ≤ 4 * K * Y ^ (E * 9 + 1) := by
      rw [pow_succ]
      calc (T : ℝ) ≤ K * ((k : ℝ) + 1) * logb 2 Y := hT
        _ ≤ K * (2 * Y ^ (E * 9)) * (2 * Y) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hK0) hL
            (logb_nonneg one_lt_two hY1) (by positivity)
        _ = _ := by ring
    have h4K : 4 * K ≤ 4 ^ a := by linarith
    calc (T : ℝ) ≤ 4 * K * Y ^ (E * 9 + 1) := hT'
      _ ≤ 4 ^ a * Y ^ m := by
        gcongr
        change E * 9 + 1 ≤ 12 * E + 1
        omega
  have hR := rotations_le_pow (by positivity) (Nat.cast_nonneg k) (Nat.cast_nonneg F)
    (Nat.cast_nonneg np) (Nat.cast_nonneg T) hX1 hNX hkX hFX hnpX hTX
  have hRe : (denseSchurRotations n δ φ : ℝ) = ((n : ℝ) + 1) ^ 2 +
      (2 * ((n : ℝ) + 1) * (F * (k + 1 + np) * (k * ((n : ℝ) + 1)) + 2 * k * (k + 2)) +
        ((n : ℝ) + 1) * (k * k + 2 * (k + 1) * ((T + k) * k + 6))) := by
    unfold denseSchurRotations denseSchurRotationsWith shqrSchurRotations shqrSchurLogSize
      smallEigLeafRotations
    push_cast; ring
  have hR0 : 0 < (denseSchurRotations n δ φ : ℝ) := by
    rw [hRe]; positivity
  have hRY : HiBd Y (3 + 5 * a + 5 * m) (denseSchurRotations n δ φ : ℝ) := by
    refine ⟨hR0, ?_⟩
    rw [hRe]
    refine hR.trans ?_
    have h3 : (52 : ℝ) ≤ Y ^ 3 := by
      have : (4 : ℝ) ^ 3 ≤ Y ^ 3 := pow_le_pow_left₀ (by norm_num) hY4 3
      linarith
    have h4 : (4 : ℝ) ^ a ≤ Y ^ a := pow_le_pow_left₀ (by norm_num) hY4 a
    calc 52 * X ^ 5 = 52 * ((4 : ℝ) ^ a) ^ 5 * (Y ^ m) ^ 5 := by ring
      _ ≤ Y ^ 3 * (Y ^ a) ^ 5 * (Y ^ m) ^ 5 := by gcongr
      _ = Y ^ (3 + 5 * a + 5 * m) := by ring
  exact hRY

/-- The replay term of the precision threshold has $O(L)$ bits: there is a constant $c$ such
that for $0 < \delta \le 1$ and $0 < \varphi \le 1$ the replay term
`NLAlib.ShiftedQR.uShQRSchurReplay` of the core with the `SmallEig` leaf's $R_L$ rotations has at
most $cL$ bits, $L = \log_2(4(n + 1)/(\delta\varphi))$: the leaf term costs a factor
$1 + 54R_L$ (`NLAlib.ShiftedQR.uShQRSchurReplay_zero_div_le`) with $R_L \le R$ =
`NLAlib.Schur.denseSchurRotations` polynomial (`NLAlib.Schur.denseSchurRotations_hiBd`). -/
theorem denseSchur_replay_bits : ∃ c : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ → φ ≤ 1 →
    logb 2 (uShQRSchurReplay n (denseSchurDegree n δ φ)
      (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length (denseSchurCap n δ φ)
      (smallEigLeafRotations (denseSchurDegree n δ φ) (denseSchurLeafCap n δ φ))
      (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ))⁻¹ ≤
        c * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨e, he⟩ := denseSchur_replay_zero_loBd
  obtain ⟨P, hP⟩ := denseSchurRotations_hiBd
  refine ⟨((e + (3 + P) : ℕ) : ℝ), fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  have hY4 := (hE (n := n) hδ hδ1 hφ hφ1).1
  have h0 := he (n := n) hδ hδ1 hφ hφ1
  have hR := hP (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, -, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  clear hE he hP
  set RL := smallEigLeafRotations (denseSchurDegree n δ φ) (denseSchurLeafCap n δ φ)
  have hRL : RL ≤ denseSchurRotations n δ φ := by
    unfold denseSchurRotations denseSchurRotationsWith shqrSchurRotations
    exact le_add_left (le_add_left (Nat.le_mul_of_pos_left _ (Nat.succ_pos n)))
  have hR1 : (1 : ℝ) ≤ denseSchurRotations n δ φ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hR.1.ne')
  have hRLR : (RL : ℝ) ≤ denseSchurRotations n δ φ := by exact_mod_cast hRL
  have hRLY : HiBd (4 * ((n : ℝ) + 1) / (δ * φ)) (3 + P) (1 + 54 * (RL : ℝ)) :=
    ((HiBd.const hY4 (by norm_num : (0 : ℝ) < 55) (by norm_num : (55 : ℝ) ≤ 4 ^ 3)).mul hR).of_le
      (by positivity) (by linarith)
  have hle := uShQRSchurReplay_zero_div_le (n := n) (k := denseSchurDegree n δ φ)
    (np := (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length)
    (F := denseSchurCap n δ φ) (RL := RL) (by linarith : (1 : ℝ) ≤ 2 * denseSchurB n δ φ)
    (half_pos hΓ) hd0 (by norm_num : (0 : ℝ) < 8)
  exact ((h0.div hRLY).of_le hle).logb_inv_le

/-- The accumulator term of the precision threshold has $O(L)$ bits: there is a constant $c$
such that for $0 < \delta \le 1$ and $0 < \varphi \le 1$ the term $\delta/(4096(n + 1)R)$,
$R$ = `NLAlib.Schur.denseSchurRotations`, has at most $cL$ bits,
$L = \log_2(4(n + 1)/(\delta\varphi))$ (`NLAlib.Schur.denseSchurRotations_hiBd`). -/
theorem denseSchur_rotations_bits : ∃ c : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → logb 2 (δ / (4096 * ((n : ℝ) + 1) * denseSchurRotations n δ φ))⁻¹ ≤
      c * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨P, hP⟩ := denseSchurRotations_hiBd
  refine ⟨((E + (6 + 1 + P) : ℕ) : ℝ), fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, -, -, -, -, -, -, hδY⟩ := hE (n := n) hδ hδ1 hφ hφ1
  have hNY0 : HiBd (4 * ((n : ℝ) + 1) / (δ * φ)) 1 ((n : ℝ) + 1) := by
    refine ⟨by positivity, ?_⟩
    have hδφ : δ * φ ≤ 1 := by nlinarith
    rw [pow_one, le_div_iff₀ (by positivity)]; nlinarith
  exact (hδY.div (((HiBd.const hY4 (by norm_num : (0 : ℝ) < 4096)
    (by norm_num : (4096 : ℝ) ≤ 4 ^ 6)).mul hNY0).mul (hP hδ hδ1 hφ hφ1))).logb_inv_le

/-- The core's terms have $O(kL + k^2L^2)$ bits: there are constants $a, b, d \ge 0$ such that
for $0 < \delta \le 1$ and $0 < \varphi \le 1$ the precision threshold
`NLAlib.ShiftedQR.uShQRSmallEig` of the core with the `SmallEig` leaf has at most
$akL + bk^2L^2 + d$ bits, $L = \log_2(4(n + 1)/(\delta\varphi))$
(`NLAlib.ShiftedQR.logb_inv_uShQRSmallEig_le`, its argument being polynomial in $2^L$). -/
theorem denseSchur_core_bits : ∃ a b d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ d ∧ ∀ {n : ℕ} {δ φ : ℝ},
    0 < δ → δ ≤ 1 → 0 < φ → φ ≤ 1 →
    logb 2 (uShQRSmallEig n (denseSchurDegree n δ φ) (2 * denseSchurB n δ φ)
      (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ) (φ / 2) ginibreGapTail
        ginibreConditionTail)⁻¹ ≤
      a * denseSchurDegree n δ φ * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) +
        b * (denseSchurDegree n δ φ : ℝ) ^ 2 * logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) ^ 2 + d := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨e₁, e₂, e₃, he⟩ := logb_inv_uShQRSmallEig_le ginibreGapTail ginibreConditionTail
    ginibreGapTail_b_pos ginibreConditionTail_b_pos
  have hE0 : (0 : ℝ) ≤ E := E.cast_nonneg
  refine ⟨max e₁ 0 * E, max e₂ 0 * (E : ℝ) ^ 2, max e₃ 0,
    mul_nonneg (le_max_right _ _) hE0, mul_nonneg (le_max_right _ _) (by positivity),
    le_max_right _ _, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, hYc, -, -, -, -, -, -⟩ := hE (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  clear hE
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  set L := logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) with hLdef
  set k := denseSchurDegree n δ φ with hkdef
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have h := he (n := n) (k := k) hB1 (half_pos hΓ) hd0 (by linarith : denseSchurDelta n δ ≤ 8)
    (half_pos hφ) (by linarith) rfl
  obtain ⟨hYc4, -⟩ := shqrArg_facts (n := n) (k := k) hB1 (half_pos hΓ) hd0
    (by linarith : denseSchurDelta n δ ≤ 8) (half_pos hφ) (by linarith) rfl
  set L₁ := logb 2 (4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
    (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2)))
  have hL₁ : L₁ ≤ E * L := hYc.logb_le
  have hL₁0 : 0 ≤ L₁ := logb_nonneg one_lt_two (by linarith)
  refine h.trans ?_
  have h1 : e₁ * k * L₁ ≤ max e₁ 0 * E * k * L := by
    calc e₁ * k * L₁ ≤ max e₁ 0 * k * L₁ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hk0) hL₁0
      _ ≤ max e₁ 0 * k * (E * L) :=
          mul_le_mul_of_nonneg_left hL₁ (mul_nonneg (le_max_right _ _) hk0)
      _ = _ := by ring
  have h2 : e₂ * k ^ 2 * L₁ ^ 2 ≤ max e₂ 0 * (E : ℝ) ^ 2 * k ^ 2 * L ^ 2 := by
    calc e₂ * k ^ 2 * L₁ ^ 2 ≤ max e₂ 0 * k ^ 2 * L₁ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (sq_nonneg _)) (sq_nonneg _)
      _ ≤ max e₂ 0 * k ^ 2 * (E * L) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL₁0 hL₁ 2)
            (mul_nonneg (le_max_right _ _) (sq_nonneg _))
      _ = _ := by ring
  have h3 : e₃ ≤ max e₃ 0 := le_max_left _ _
  linarith

/-- The bound $akL + bk^2L^2 + cL + d$ with $k \le KL(\log_2 L + 1)$ and $L \ge 2$ is at most
$(aK + bK^2 + c)L^4(\log_2 L + 1)^2 + d$. -/
private theorem poly_le_of_degree_le {a b c d K L k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hK : 0 ≤ K) (hL2 : 2 ≤ L) (hk0 : 0 ≤ k) (hk : k ≤ K * L * (logb 2 L + 1)) :
    a * k * L + b * k ^ 2 * L ^ 2 + c * L + d ≤
      (a * K + b * K ^ 2 + c) * L ^ 4 * (logb 2 L + 1) ^ 2 + d := by
  have hlL : 1 ≤ logb 2 L := by
    rw [le_logb_iff_rpow_le one_lt_two (by linarith), rpow_one]; exact hL2
  have hL4 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hl2 : logb 2 L + 1 ≤ (logb 2 L + 1) ^ 2 := by nlinarith
  set P := L ^ 4 * (logb 2 L + 1) ^ 2 with hP
  have hkP : k * L ≤ K * P := by
    calc k * L ≤ K * L * (logb 2 L + 1) * L := by gcongr
      _ = K * (L ^ 2 * (logb 2 L + 1)) := by ring
      _ ≤ K * (L ^ 4 * (logb 2 L + 1) ^ 2) := by gcongr
  have hk2P : k ^ 2 * L ^ 2 ≤ K ^ 2 * P := by
    calc k ^ 2 * L ^ 2 ≤ (K * L * (logb 2 L + 1)) ^ 2 * L ^ 2 := by gcongr
      _ = K ^ 2 * P := by rw [hP]; ring
  have hLP : L ≤ P := by
    have : L ≤ L ^ 4 := (le_self_pow₀ (by linarith) (by norm_num : 2 ≠ 0)).trans hL4
    calc L ≤ L ^ 4 * 1 := by rw [mul_one]; exact this
      _ ≤ P := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have e : (a * K + b * K ^ 2 + c) * L ^ 4 * (logb 2 L + 1) ^ 2 =
      a * (K * P) + b * (K ^ 2 * P) + c * P := by rw [hP]; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hkP ha
  have := mul_le_mul_of_nonneg_left hk2P hb
  have := mul_le_mul_of_nonneg_left hLP hc
  nlinarith

/-- **The bits of precision of the dense Schur solver**: there are absolute constants $c_1, c_2$
such that for every order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$,
$$\log_2\frac{1}{\boldsymbol{u}_0} \le c_1L^4(\log_2 L + 1)^2 + c_2, \qquad
  L = \log_2\frac{4(n + 1)}{\delta\varphi}\,,$$
$\boldsymbol{u}_0$ = `NLAlib.Schur.uDenseSchur`: $O(\log^4(n/(\delta\varphi)))$ bits up to
$(\log\log)^2$, the shift degree being $\Theta(L\log L)$.
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1]
(the bits of the eigenvalue solver); the Schur form costs no more bits.

Note: Each term of the threshold has $O(L)$ bits except the core's and the leaf's, which have
$O(kL_c + k^2L_c^2)$ (`NLAlib.ShiftedQR.logb_inv_uShQRSmallEig_le`), $L_c = O(L)$
(`NLAlib.Schur.denseSchur_arg_bounds`) and $k = O(L\log L)$ (`NLAlib.Schur.denseSchur_caps_le`).
-/
theorem logb_inv_uDenseSchur_le : ∃ c₁ c₂ : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → Real.logb 2 (uDenseSchur n δ φ)⁻¹ ≤
      c₁ * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ 4 *
        (Real.logb 2 (Real.logb 2 (4 * (n + 1) / (δ * φ))) + 1) ^ 2 + c₂ := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  obtain ⟨K, hK0, hK⟩ := denseSchur_caps_le
  obtain ⟨c₃, hc₃⟩ := denseSchur_replay_bits
  obtain ⟨c₄, hc₄⟩ := denseSchur_rotations_bits
  obtain ⟨a, b, d, ha0, hb0, hd0', hcore⟩ := denseSchur_core_bits
  have hE0 : (0 : ℝ) ≤ E := E.cast_nonneg
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (E : ℝ) + max c₃ 0 + max c₄ 0 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  refine ⟨a * K + b * K ^ 2 + c, d + 7, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, hYc, -, hRed, ht12, hd3, hd64, -⟩ := hE (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hL2, hk, -, -⟩ := hK (n := n) hδ hδ1 hφ hφ1
  have hrep := hc₃ (n := n) hδ hδ1 hφ hφ1
  have hrot := hc₄ (n := n) hδ hδ1 hφ hφ1
  have hcr := hcore (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  clear hE hK hc₃ hc₄ hcore
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  set L := logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) with hLdef
  set k := denseSchurDegree n δ φ with hkdef
  have hL0 : 0 ≤ L := by linarith
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  -- every term has at most `M = a k L + b k² L² + c L + (d + 7)` bits
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = a * k * L + b * k ^ 2 * L ^ 2 + c * L + (d + 7) := ⟨_, rfl⟩
  refine le_trans ?_ (poly_le_of_degree_le (d := d + 7) ha0 hb0 hc0 hK0 hL2 hk0 hk)
  rw [← hM]
  have hM0 : 0 ≤ a * k * L + b * k ^ 2 * L ^ 2 := by positivity
  have hcL : ∀ (x : ℝ) (e : ℝ), e ≤ c → logb 2 x⁻¹ ≤ e * L → logb 2 x⁻¹ ≤ M :=
    fun x e he hx => by
      have : e * L ≤ c * L := mul_le_mul_of_nonneg_right he hL0
      rw [hM]; linarith
  have hEc : (E : ℝ) ≤ c := by rw [hc]; linarith [le_max_right c₃ 0, le_max_right c₄ 0]
  have h3c : c₃ ≤ c := by rw [hc]; linarith [le_max_left c₃ 0, le_max_right c₄ 0]
  have h4c : c₄ ≤ c := by rw [hc]; linarith [le_max_right c₃ 0, le_max_left c₄ 0]
  have hcore' : logb 2 (uShQRSmallEig n k (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
      (denseSchurDelta n δ) (φ / 2) ginibreGapTail ginibreConditionTail)⁻¹ ≤ M := by
    have : 0 ≤ c * L := by positivity
    rw [hM]; linarith
  have hpos := (uShQRSmallEig_pos ginibreGapTail_b_pos ginibreConditionTail_b_pos (n := n)
    hB1 (half_pos hΓ) hd0 (by linarith : denseSchurDelta n δ ≤ 8) (half_pos hφ) (by linarith)
    (rfl : k = _)).1
  have hShQR := (logb_inv_le_logb_inv hpos (min_le_left _ _)).trans hcore'
  have hLeaf : logb 2 (uSmallEigForward k 32 (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ)
      (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ)) (denseSchurLeafFailure n δ φ)
      ginibreGapTail ginibreConditionTail)⁻¹ ≤ M := by
    refine (logb_inv_le_logb_inv hpos ?_).trans hcore'
    unfold uShQRSmallEig denseSchurLeafFailure
    rw [show (4 : ℝ) * 8 = 32 by norm_num]
    exact min_le_right _ _
  have h100 : logb 2 (1 / 100 : ℝ)⁻¹ ≤ M := by
    have : logb 2 (1 / 100 : ℝ)⁻¹ ≤ 7 := by
      rw [one_div, inv_inv, logb_le_iff_le_rpow one_lt_two (by norm_num)]; norm_num
    have : 0 ≤ c * L := by positivity
    rw [hM]; linarith
  unfold uDenseSchur uDenseSchurWith
  exact logb_inv_min_le (logb_inv_min_le (hcL _ _ hEc hRed.logb_inv_le) (logb_inv_min_le
    (hcL _ _ hEc hd3.logb_inv_le) (logb_inv_min_le (hcL _ _ hEc ht12.logb_inv_le)
      (logb_inv_min_le hShQR (logb_inv_min_le h100 (logb_inv_min_le (hcL _ _ h3c hrep)
        (logb_inv_min_le (hcL _ _ h4c hrot) (hcL _ _ hEc hd64.logb_inv_le)))))))) hLeaf

section Count

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The precision threshold at two tolerances is positive** for $0 < \delta_R, \delta_C \le 1$
and $0 < \varphi \le 1$. -/
theorem uDenseSchurAt_pos {n : ℕ} {δR δC φ : ℝ} (hδR : 0 < δR) (hδR1 : δR ≤ 1) (hδC : 0 < δC)
    (hδC1 : δC ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) : 0 < uDenseSchurAt n δR δC φ := by
  obtain ⟨-, -, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδR hδR1 hφ hφ1
  obtain ⟨hd0, hd1, -⟩ := denseSchur_params_basic (n := n) hδC hδC1 hφ hφ1
  have hk := denseSchurDegree_pos n δR φ
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δR φ := by linarith
  have hβ := shqrSmallEigAccuracy_pos (n := n) hB1 (half_pos hΓ) hd0 (by norm_num : (0 : ℝ) < 8)
  have hβS := shqrSmallEigAccuracy_le (n := n) hB1 (half_pos hΓ) hd0
    (by linarith : denseSchurDelta n δC ≤ 8)
  obtain ⟨hf0, hfS, -⟩ := forwardBackwardError_spec (kmax := denseSchurDegree n δR φ)
    hβ (by linarith : _ ≤ (32 : ℝ))
  have hφL := shqrSmallEigFailure_pos (n := n) (B := 2 * denseSchurB n δR φ)
    (Γ := denseSchurΓ n δR φ / 2) (S := 8) (δ := denseSchurDelta n δC) (half_pos hφ)
  have hφL1 := shqrSmallEigFailure_le (n := n) (B := 2 * denseSchurB n δR φ)
    (Γ := denseSchurΓ n δR φ / 2) (S := 8) (δ := denseSchurDelta n δC) (half_pos hφ).le
  refine lt_min (uDenseSchurAtWith_pos _ _ hδR hδR1 hδC hδC1 hφ hφ1) ?_
  exact (uSmallEig_spec ginibreGapTail_b_pos ginibreConditionTail_b_pos hk hf0 hfS hφL
    (by linarith)).1

/-- **The bits of precision of the dense Schur solver at two tolerances**: there are constants
$c_1, c_2$ such that for every order $n + 1$, $0 < \delta_R, \delta_C \le 1$ and
$0 < \varphi \le 1$, $\log_2(1/\boldsymbol{u}_0) \le c_1L^4(\log_2L + 1)^2 + c_2$ with
$\boldsymbol{u}_0$ = `NLAlib.Schur.uDenseSchurAt` and
$L = \log_2(4(n + 1)/(\min(\delta_R, \delta_C)\varphi))$.
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1]
(the bits of the eigenvalue solver); the second tolerance costs no more bits. -/
theorem logb_inv_uDenseSchurAt_le : ∃ c₁ c₂ : ℝ, ∀ {n : ℕ} {δR δC φ : ℝ}, 0 < δR → δR ≤ 1 →
    0 < δC → δC ≤ 1 → 0 < φ → φ ≤ 1 → Real.logb 2 (uDenseSchurAt n δR δC φ)⁻¹ ≤
      c₁ * Real.logb 2 (4 * (n + 1) / (min δR δC * φ)) ^ 4 *
        (Real.logb 2 (Real.logb 2 (4 * (n + 1) / (min δR δC * φ))) + 1) ^ 2 + c₂ := by
  sorry

/-- **The operation count of the dense Schur solver is $n^3$ times a polylogarithm**: there is a
constant $C$ such that for every order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$, the
instrumented static count at `NLAlib.Schur.denseSchurDims` and zero offsets is at most
$C(n + 1)^3L^9(\log_2 L + 1)^6$, $L = \log_2(4(n + 1)/(\delta\varphi))$: $(k + 1)^4 \le
(KL(\log_2 L + 1))^4$, $F + 1 \le KL$, $(T + 1)^2 \le (KL^2(\log_2 L + 1))^2$ in
`NLAlib.Schur.denseSchur_work_le` (`NLAlib.Schur.denseSchur_caps_le`), the words of the stages
bounded by constants. [BanksGarzaVargasSrivastava2022, Theorem 1.4]'s exponent is $2$ for the
eigenvalues alone, with a run-time count over the deflation tree. -/
theorem denseSchur_work_le_polylog (sG : ℕ) : ∃ C : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ →
    δ ≤ 1 → 0 < φ → φ ≤ 1 →
    (Count.size (stmtCost (denseSchur (O := O) (Q := Q) sG).instrument
      (denseSchurDims n δ φ ++ [0, 0, 0, 0, 0])) : ℝ) ≤
      C * ((n : ℝ) + 1) ^ 3 * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ 9 *
        (Real.logb 2 (Real.logb 2 (4 * (n + 1) / (δ * φ))) + 1) ^ 6 := by
  obtain ⟨K, hK0, hK⟩ := denseSchur_caps_le
  refine ⟨384547 * 426707 * (K + 1) ^ 4 * (K + 1) * (K * (K + 1) + 1) ^ 2,
    fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hL2, hk, hF, hT⟩ := hK (n := n) hδ hδ1 hφ hφ1
  clear hK
  set L := logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) with hLdef
  set ℓ := logb 2 L + 1 with hℓdef
  set k := denseSchurDegree n δ φ
  set F := denseSchurCap n δ φ
  set T := denseSchurLeafCap n δ φ
  set nr := (denseSchurRegParams n δ φ).length
  set nq := (denseSchurThreshold n δ φ :: (denseSchurShQRParams n δ φ ++
    denseSchurLeafParams n δ φ)).length
  have hd : denseSchurDims n δ φ ++ [0, 0, 0, 0, 0] = [n + 1, nr, nq, k, F, T, 0, 0, 0, 0, 0] :=
    rfl
  have hw := denseSchur_work_le (O := O) (Q := Q) sG n nr nq k F T
  rw [hd]
  have hwR : (Count.size (stmtCost (denseSchur (O := O) (Q := Q) sG).instrument
      [n + 1, nr, nq, k, F, T, 0, 0, 0, 0, 0]) : ℝ) ≤
      384547 * ((n : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) ^ 4 * ((nr : ℝ) + nq + 1) * ((F : ℝ) + 1) *
        ((T : ℝ) + 1) ^ 2 := by exact_mod_cast hw
  refine hwR.trans ?_
  have hnr : (nr : ℝ) = 12 := by simp [nr, denseSchurRegParams, length_smallEigParams]
  have hnq : (nq : ℝ) ≤ 426693 := by
    have := length_denseSchurShQRParams_le (n := n) hδ hδ1 hφ hφ1
    simp only [nq, List.length_cons, List.length_append, denseSchurLeafParams,
      smallEigForwardParams, length_smallEigParams]
    push_cast
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hℓ1 : 1 ≤ ℓ := by
    have := logb_nonneg one_lt_two hL1
    linarith
  have hLℓ : 1 ≤ L * ℓ := one_le_mul_of_one_le_of_one_le hL1 hℓ1
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hF0 : (0 : ℝ) ≤ F := F.cast_nonneg
  have hT0 : (0 : ℝ) ≤ T := T.cast_nonneg
  have hk1 : (k : ℝ) + 1 ≤ (K + 1) * (L * ℓ) := by
    have e : (K + 1) * (L * ℓ) = K * L * ℓ + L * ℓ := by ring
    linarith
  have hF1 : (F : ℝ) + 1 ≤ (K + 1) * L := by
    have e : (K + 1) * L = K * L + L := by ring
    linarith
  have hT1 : (T : ℝ) + 1 ≤ (K * (K + 1) + 1) * (L ^ 2 * ℓ) := by
    have h1 : (T : ℝ) ≤ K * ((K + 1) * (L * ℓ)) * L :=
      hT.trans (by gcongr)
    have : (1 : ℝ) ≤ L ^ 2 * ℓ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hℓ1
    have e : K * ((K + 1) * (L * ℓ)) * L = K * (K + 1) * (L ^ 2 * ℓ) := by ring
    have e2 : (K * (K + 1) + 1) * (L ^ 2 * ℓ) = K * (K + 1) * (L ^ 2 * ℓ) + L ^ 2 * ℓ := by
      ring
    linarith
  have hq : (nr : ℝ) + nq + 1 ≤ 426707 := by rw [hnr]; linarith
  have hN : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
  calc 384547 * ((n : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) ^ 4 * ((nr : ℝ) + nq + 1) * ((F : ℝ) + 1) *
        ((T : ℝ) + 1) ^ 2
      ≤ 384547 * ((n : ℝ) + 1) ^ 3 * ((K + 1) * (L * ℓ)) ^ 4 * 426707 * ((K + 1) * L) *
        ((K * (K + 1) + 1) * (L ^ 2 * ℓ)) ^ 2 := by gcongr
    _ = 384547 * 426707 * (K + 1) ^ 4 * (K + 1) * (K * (K + 1) + 1) ^ 2 *
        ((n : ℝ) + 1) ^ 3 * L ^ 9 * ℓ ^ 6 := by ring

/-- The operation count of the dense Schur solver is $n^3$ times a power of $L$: there is a
constant $C$ such that for every order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$, the
instrumented static count at `NLAlib.Schur.denseSchurDims` and zero offsets is at most
$C(n + 1)^3L^{15}$, $L = \log_2(4(n + 1)/(\delta\varphi))$:
`NLAlib.Schur.denseSchur_work_le_polylog` with $\log_2 L + 1 \le 3L$. -/
theorem denseSchur_work_le_pow (sG : ℕ) : ∃ C : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ →
    δ ≤ 1 → 0 < φ → φ ≤ 1 →
    (Count.size (stmtCost (denseSchur (O := O) (Q := Q) sG).instrument
      (denseSchurDims n δ φ ++ [0, 0, 0, 0, 0])) : ℝ) ≤
      C * ((n : ℝ) + 1) ^ 3 * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ 15 := by
  obtain ⟨C, hC⟩ := denseSchur_work_le_polylog (O := O) (Q := Q) sG
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  refine ⟨max C 0 * 3 ^ 6, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  set L := logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) with hLdef
  have hL1 : 1 ≤ L := by linarith [two_le_logb_of_four_le (hE (n := n) hδ hδ1 hφ hφ1).1]
  have hℓ0 : 0 ≤ logb 2 L + 1 := by linarith [logb_nonneg one_lt_two hL1]
  have hℓ : logb 2 L + 1 ≤ 3 * L := by linarith [logb_two_le_two_mul hL1]
  have hL0 : 0 ≤ L := by linarith
  refine (hC hδ hδ1 hφ hφ1).trans ?_
  calc C * ((n : ℝ) + 1) ^ 3 * L ^ 9 * (logb 2 L + 1) ^ 6
      ≤ max C 0 * ((n : ℝ) + 1) ^ 3 * L ^ 9 * (logb 2 L + 1) ^ 6 := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * ((n : ℝ) + 1) ^ 3 * L ^ 9 * (3 * L) ^ 6 := by gcongr
    _ = max C 0 * 3 ^ 6 * ((n : ℝ) + 1) ^ 3 * L ^ 15 := by ring

end Count

end NLAlib.Schur
