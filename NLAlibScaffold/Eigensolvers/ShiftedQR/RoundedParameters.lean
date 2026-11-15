/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import NLAlib.Matrix.FinitePrecision.Rounding

/-!
# Parameters of the rounded shifted QR algorithm

[BanksGarzaVargasSrivastava2022, §2.3 and Theorem 6.3]: the shift degree $k$ of (eqn:setk), the
global constants $\theta$, $\alpha$, $\gamma = 0.2$, Exc's $\varepsilon$ and the shift reach $C$,
and the parameter choices of the headline in the order of the paper, with no circularity:
the decoupling threshold $\omega$ from the error budget, the iteration cap $F$, the failure
split, the radius $R$ and the separation $d$ of the shifts, then one closed-form unit roundoff
`NLAlib.ShiftedQR.uShQR`, a minimum of named per-block terms. Everything is written for the
iterate class: condition $4B$ and separation $\Gamma/4$ (one doubling for the worklist, one for
the iterates), iterate norm $4\Sigma$, block norm $2\Sigma$.

## Main definitions

* `NLAlib.ShiftedQR.SatisfiesSetk`, `NLAlib.ShiftedQR.shqrLogDegree`,
  `NLAlib.ShiftedQR.shqrDegree`: the degree rule (eqn:setk).
* `NLAlib.ShiftedQR.shqrTheta`, `NLAlib.ShiftedQR.shqrAlpha`, `NLAlib.ShiftedQR.shqrEps`,
  `NLAlib.ShiftedQR.shqrC`: the global constants.
* `NLAlib.ShiftedQR.shqrOmega`, `NLAlib.ShiftedQR.shqrCap`,
  `NLAlib.ShiftedQR.shqrSmallEigFailure`, `NLAlib.ShiftedQR.shqrSmallEigAccuracy`,
  `NLAlib.ShiftedQR.shqrDist`: the parameter choices.
* `NLAlib.ShiftedQR.uShQR`: the precision threshold.

## Main results

* `NLAlib.ShiftedQR.two_le_shqrDegree`, `NLAlib.ShiftedQR.rpow_two_div_shqrDegree_le`: $k \ge 2$
  and $B^{2/k} \le 2$.
* `NLAlib.ShiftedQR.shqrEps_le_half`: Exc's $\varepsilon \le 1/2$ under (eqn:setk).
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Real Filter Topology

/-! ### The shift degree -/

/-- The degree rule (eqn:setk) at $k = 2^q$, $q \ge 1$:
$B^{(8q + 3)/(k - 1)}(2B^4)^{2/(k - 1)} \le 3$. -/
def SatisfiesSetk (B : ℝ) (q : ℕ) : Prop :=
  1 ≤ q ∧ B ^ ((8 * q + 3 : ℝ) / (2 ^ q - 1)) * (2 * B ^ 4) ^ ((2 : ℝ) / (2 ^ q - 1)) ≤ 3

/-- The exponent $q$ of the shift degree: the least $q \ge 1$ satisfying (eqn:setk). -/
noncomputable def shqrLogDegree (B : ℝ) : ℕ := sInf {q | SatisfiesSetk B q}

/-- The shift degree $k = 2^q$ of (eqn:setk) [BanksGarzaVargasSrivastava2022, eqn:setk]. -/
noncomputable def shqrDegree (B : ℝ) : ℕ := 2 ^ shqrLogDegree B

/-- (eqn:setk) in logarithms: for $B > 0$ and $q \ge 1$ it reads
$(8q + 11)\log B + 2\log 2 \le (2^q - 1)\log 3$. -/
theorem satisfiesSetk_iff {B : ℝ} (hB : 0 < B) {q : ℕ} (hq : 1 ≤ q) :
    SatisfiesSetk B q ↔ (8 * q + 11) * log B + 2 * log 2 ≤ (2 ^ q - 1) * log 3 := by
  have hk : (0 : ℝ) < 2 ^ q - 1 := by
    have : (2 : ℝ) ≤ 2 ^ q := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
    linarith
  have h2 : 0 < 2 * B ^ 4 := by positivity
  have hpos : 0 < B ^ ((8 * q + 3 : ℝ) / (2 ^ q - 1)) * (2 * B ^ 4) ^ ((2 : ℝ) / (2 ^ q - 1)) :=
    by positivity
  have hlog : log (B ^ ((8 * q + 3 : ℝ) / (2 ^ q - 1)) * (2 * B ^ 4) ^ ((2 : ℝ) / (2 ^ q - 1))) =
      ((8 * q + 11) * log B + 2 * log 2) / (2 ^ q - 1) := by
    rw [log_mul (by positivity) (by positivity), log_rpow hB, log_rpow h2,
      log_mul (by norm_num) (by positivity), log_pow]
    field_simp
    push_cast
    ring
  simp only [SatisfiesSetk, hq, true_and]
  rw [← log_le_log_iff hpos (by norm_num), hlog, div_le_iff₀ hk]
  constructor <;> intro h <;> linarith

/-- (eqn:setk) has a solution for every $B \ge 1$: $(8q + 11)/2^q \to 0$. -/
theorem exists_satisfiesSetk {B : ℝ} (hB : 1 ≤ B) : ∃ q, SatisfiesSetk B q := by
  have hL : 0 ≤ log B := log_nonneg hB
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (r := 2) (by norm_num)
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (r := 2) (by norm_num)
  have ht : Tendsto (fun q : ℕ => (8 * log B) * ((q : ℝ) ^ 1 / 2 ^ q) +
      (11 * log B + 3) * ((q : ℝ) ^ 0 / 2 ^ q)) atTop (𝓝 0) := by
    simpa using (h1.const_mul (8 * log B)).add (h0.const_mul (11 * log B + 3))
  obtain ⟨q, hlt, hq⟩ := ((ht.eventually (gt_mem_nhds one_pos)).and
    (eventually_ge_atTop 1)).exists
  refine ⟨q, (satisfiesSetk_iff (by linarith) hq).mpr ?_⟩
  have h2q : (0 : ℝ) < 2 ^ q := by positivity
  have hq' : (8 * q + 11) * log B + 3 ≤ 2 ^ q := by
    have e : (8 * log B) * ((q : ℝ) ^ 1 / 2 ^ q) + (11 * log B + 3) * ((q : ℝ) ^ 0 / 2 ^ q) =
        ((8 * q + 11) * log B + 3) / 2 ^ q := by field_simp; ring
    rw [e, div_lt_one h2q] at hlt
    exact hlt.le
  have hl3 : 1 < log 3 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    linarith [exp_one_lt_d9]
  have hl2 := log_two_lt_d9
  have : (1 : ℝ) ≤ 2 ^ q - 1 := by
    have : (2 : ℝ) ≤ 2 ^ q := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
    linarith
  nlinarith

/-- The exponent of the shift degree satisfies (eqn:setk), for $B \ge 1$. -/
theorem satisfiesSetk_shqrLogDegree {B : ℝ} (hB : 1 ≤ B) :
    SatisfiesSetk B (shqrLogDegree B) :=
  Nat.sInf_mem (exists_satisfiesSetk hB)

/-- No smaller exponent satisfies (eqn:setk). -/
theorem not_satisfiesSetk_of_lt_shqrLogDegree {B : ℝ} {q : ℕ} (hq : q < shqrLogDegree B) :
    ¬ SatisfiesSetk B q :=
  Nat.notMem_of_lt_sInf hq

/-- For $B \ge 1$ the exponent is at least $2$: (eqn:setk) fails at $k = 2$, where it reads
$4B^{19} \le 3$. -/
theorem two_le_shqrLogDegree {B : ℝ} (hB : 1 ≤ B) : 2 ≤ shqrLogDegree B := by
  obtain ⟨h1, -⟩ := satisfiesSetk_shqrLogDegree hB
  by_contra h
  have he : shqrLogDegree B = 1 := by omega
  have hs := satisfiesSetk_shqrLogDegree hB
  rw [he, satisfiesSetk_iff (by linarith) le_rfl] at hs
  have hL : 0 ≤ log B := log_nonneg hB
  have : log 3 < 2 * log 2 := by
    rw [← log_rpow (by norm_num)]
    exact log_lt_log (by norm_num) (by norm_num)
  push_cast at hs
  nlinarith

/-- **The shift degree is at least two** (errata N11: Sh's decrease factor $1.002$ needs
$k \ge 2$): for $B \ge 1$, the degree $k$ of (eqn:setk) satisfies $k \ge 2$ (even $k \ge 4$).
No printed source. -/
theorem two_le_shqrDegree {B : ℝ} (hB : 1 ≤ B) : 2 ≤ shqrDegree B := by
  have := two_le_shqrLogDegree hB
  calc 2 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ shqrLogDegree B := Nat.pow_le_pow_right (by norm_num) this

/-- **The degree rule gives $B^{2/k} \le 2$** (the hypothesis `hBk` of Regularize): for $B \ge 1$
and $k$ the degree of (eqn:setk), $B^{2/k} \le 2$ (in fact $\le 1.05$). No printed source. -/
theorem rpow_two_div_shqrDegree_le {B : ℝ} (hB : 1 ≤ B) :
    B ^ ((2 : ℝ) / shqrDegree B) ≤ 2 := by
  set q := shqrLogDegree B
  have hq := two_le_shqrLogDegree hB
  have hs := (satisfiesSetk_iff (by linarith) (by omega : 1 ≤ q)).mp
    (satisfiesSetk_shqrLogDegree hB)
  have hL : 0 ≤ log B := log_nonneg hB
  have hk : (shqrDegree B : ℝ) = 2 ^ q := by simp [shqrDegree, q]
  have h4 : (4 : ℝ) ≤ 2 ^ q := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hl3 : log 3 < 2 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have := add_one_lt_exp (x := (2 : ℝ)) (by norm_num)
    linarith
  rw [← log_le_log_iff (by positivity) (by norm_num), log_rpow (by linarith), hk]
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  -- $4\log B \le (8q + 11)\log B < 2^{q + 1}\log 2$.
  have key : 4 * log B ≤ (8 * q + 11) * log B := by nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have : (2 ^ q - 1) * log 3 ≤ 2 ^ q * (2 * log 2) := by
    have : log 3 < 2 * log 2 := by
      rw [← log_rpow (by norm_num)]
      exact log_lt_log (by norm_num) (by norm_num)
    nlinarith
  nlinarith

end NLAlib.ShiftedQR
