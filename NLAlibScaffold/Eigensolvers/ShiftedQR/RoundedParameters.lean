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

/-! ### The global constants

They depend on the shift degree $k$ and the condition bound $B$ only (eqn:settheta);
`NLAlib.ShiftedQR.shStep_pwrites` and `NLAlib.ShiftedQR.regularize_pwrites` take them in exactly
these forms. -/

/-- The optimality factor $\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$ of Regularize's
output [BanksGarzaVargasSrivastava2022, eqn:settheta]. -/
noncomputable def shqrTheta (k : ℕ) (B : ℝ) : ℝ :=
  1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)

/-- The promising factor $\alpha = (1.01B)^{4\log_2 k/k}$
[BanksGarzaVargasSrivastava2022, eqn:settheta]. -/
noncomputable def shqrAlpha (k : ℕ) (B : ℝ) : ℝ := (1.01 * B) ^ ((4 * Nat.log 2 k : ℝ) / k)

/-- Exc's net width
$\varepsilon = \bigl(0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2)\bigr)^{k/(k-1)}$
at $\gamma = 0.2$ (Lemma 5.3, with the rounded threshold's $0.998$). -/
noncomputable def shqrEps (k : ℕ) (B : ℝ) : ℝ :=
  (0.998 * (1 - 0.2) * (1 - 0.2) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * shqrAlpha k B ^ 2 *
    shqrTheta k B ^ 2)) ^ ((k : ℝ) / (k - 1))

/-- The lower radius coefficient $1.998^{1/k}\theta\alpha B^{1/k}$ of Exc: its disk has radius
at least this times $\psi_k$. -/
noncomputable def shqrRadiusLo (k : ℕ) (B : ℝ) : ℝ :=
  (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * shqrTheta k B * shqrAlpha k B * B ^ ((k : ℝ)⁻¹)

/-- The upper radius coefficient $2.002^{1/k}\theta\alpha B^{1/k}$ of Exc (errata N2). -/
noncomputable def shqrRadiusHi (k : ℕ) (B : ℝ) : ℝ :=
  (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * shqrTheta k B * shqrAlpha k B * B ^ ((k : ℝ)⁻¹)

/-- The shift reach $C = 1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k}$ (errata N2: at most
$4.7$ under (eqn:setk); the paper's $3$, the errata's first $4.1$, are too small). -/
noncomputable def shqrC (k : ℕ) (B : ℝ) : ℝ := 1.1 + 2.1 * shqrRadiusHi k B

theorem shqrTheta_pos (k : ℕ) {B : ℝ} (hB : 0 < B) : 0 < shqrTheta k B := by
  unfold shqrTheta; positivity

theorem shqrAlpha_pos (k : ℕ) {B : ℝ} (hB : 0 < B) : 0 < shqrAlpha k B := by
  unfold shqrAlpha; positivity

theorem one_le_shqrTheta (k : ℕ) {B : ℝ} (hB : 1 ≤ B) : 1 ≤ shqrTheta k B := by
  unfold shqrTheta
  have h1 : 1 ≤ (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num)
      (neg_nonpos.mpr (by positivity))
  have h2 : 1 ≤ (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) :=
    one_le_rpow (by nlinarith [one_le_pow₀ (n := 4) hB]) (by positivity)
  nlinarith

theorem one_le_shqrAlpha (k : ℕ) {B : ℝ} (hB : 1 ≤ B) : 1 ≤ shqrAlpha k B := by
  unfold shqrAlpha
  exact one_le_rpow (by linarith) (by positivity)

theorem shqrEps_pos (k : ℕ) {B : ℝ} (hB : 0 < B) : 0 < shqrEps k B := by
  have := shqrTheta_pos k hB
  have := shqrAlpha_pos k hB
  unfold shqrEps; positivity

theorem shqrRadiusLo_pos (k : ℕ) {B : ℝ} (hB : 0 < B) : 0 < shqrRadiusLo k B := by
  have := shqrTheta_pos k hB
  have := shqrAlpha_pos k hB
  unfold shqrRadiusLo; positivity

theorem shqrRadiusHi_pos (k : ℕ) {B : ℝ} (hB : 0 < B) : 0 < shqrRadiusHi k B := by
  have := shqrTheta_pos k hB
  have := shqrAlpha_pos k hB
  unfold shqrRadiusHi; positivity

theorem shqrRadiusLo_le_shqrRadiusHi (k : ℕ) {B : ℝ} (hB : 0 < B) :
    shqrRadiusLo k B ≤ shqrRadiusHi k B := by
  have := shqrTheta_pos k hB
  have := shqrAlpha_pos k hB
  unfold shqrRadiusLo shqrRadiusHi
  gcongr
  norm_num

/-- The logarithm of Exc's denominator $(13B^4)^{1/k}\alpha^2\theta^2$ is at least
$(\log 26 + (8 + 8q)\log B)/k$ at $k = 2^q$, $B \ge 1$. -/
theorem log_shqrEps_denom_ge {B : ℝ} (hB : 1 ≤ B) (q : ℕ) :
    (log 26 + (8 + 8 * q) * log B) / 2 ^ q ≤
      log ((13 * B ^ 4) ^ (((2 ^ q : ℕ) : ℝ)⁻¹) * shqrAlpha (2 ^ q) B ^ 2 *
        shqrTheta (2 ^ q) B ^ 2) := by
  have hB0 : 0 < B := by linarith
  have hK : (0 : ℝ) < 2 ^ q := by positivity
  have hL : 0 ≤ log B := log_nonneg hB
  have hθ := shqrTheta_pos (2 ^ q) hB0
  have hα := shqrAlpha_pos (2 ^ q) hB0
  have l01 : 0 ≤ log (1.01 : ℝ) := log_nonneg (by norm_num)
  have l998 : log (0.998 : ℝ) ≤ 0 := log_nonpos (by norm_num) (by norm_num)
  have hB4 : log (B ^ 4) = 4 * log B := by rw [log_pow]; norm_num
  have h1 : log ((13 * B ^ 4) ^ (((2 ^ q : ℕ) : ℝ)⁻¹)) = (2 ^ q)⁻¹ * (log 13 + 4 * log B) := by
    rw [log_rpow (by positivity), log_mul (by norm_num) (by positivity), hB4]; push_cast; ring
  have h2 : log (shqrAlpha (2 ^ q) B ^ 2) = 2 * (4 * q / 2 ^ q * (log 1.01 + log B)) := by
    rw [log_pow, shqrAlpha, log_rpow (by positivity), log_mul (by norm_num) (by positivity),
      Nat.log_pow (by norm_num)]
    push_cast; ring
  have h3 : log (shqrTheta (2 ^ q) B ^ 2) = 2 * (log 1.01 + (-(2 ^ q : ℝ)⁻¹) * log 0.998 +
      (2 * 2 ^ q : ℝ)⁻¹ * (log 2 + 4 * log B)) := by
    rw [log_pow, shqrTheta, log_mul (by positivity) (by positivity),
      log_mul (by norm_num) (by positivity), log_rpow (by norm_num), log_rpow (by positivity),
      log_mul (by norm_num) (by positivity), hB4]
    push_cast; ring
  have e26 : log (26 : ℝ) = log 13 + log 2 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity), h1, h2, h3,
    e26, div_le_iff₀ hK]
  have hK1 : (2 ^ q : ℝ) * (2 ^ q)⁻¹ = 1 := mul_inv_cancel₀ hK.ne'
  have hK2 : (2 ^ q : ℝ) * (2 * 2 ^ q)⁻¹ = 1 / 2 := by field_simp
  have hK3 : (2 ^ q : ℝ) * (4 * q / 2 ^ q) = 4 * q := by field_simp
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have : 0 ≤ (2 ^ q : ℝ) * (2 * (log 1.01 + (-(2 ^ q : ℝ)⁻¹) * log 0.998)) +
      2 * (4 * q) * log 1.01 := by
    have : (2 ^ q : ℝ) * (2 * (log 1.01 + (-(2 ^ q : ℝ)⁻¹) * log 0.998)) =
        2 * 2 ^ q * log 1.01 - 2 * log 0.998 := by field_simp; ring
    rw [this]; nlinarith
  rw [mul_comm _ (2 ^ q : ℝ)]
  have expand : (2 ^ q : ℝ) * ((2 ^ q)⁻¹ * (log 13 + 4 * log B) +
      2 * (4 * q / 2 ^ q * (log 1.01 + log B)) + 2 * (log 1.01 + (-(2 ^ q : ℝ)⁻¹) * log 0.998 +
        (2 * 2 ^ q : ℝ)⁻¹ * (log 2 + 4 * log B))) =
      (2 ^ q * (2 ^ q)⁻¹) * (log 13 + 4 * log B) + 2 * (2 ^ q * (4 * q / 2 ^ q)) *
        (log 1.01 + log B) + (2 ^ q : ℝ) * (2 * (log 1.01 + (-(2 ^ q : ℝ)⁻¹) * log 0.998)) +
        2 * (2 ^ q * (2 * 2 ^ q)⁻¹) * (log 2 + 4 * log B) := by ring
  rw [expand, hK1, hK2, hK3]
  nlinarith

/-- **Exc's net width is at most one half under (eqn:setk)** (the hypothesis `hε2` of Sh): for
$B \ge 1$ and $k$ the degree of (eqn:setk), $\varepsilon \le 1/2$ (in fact $\varepsilon < 0.39$;
numerically $\varepsilon \in [0.098, 0.353]$ over $B \ge 1$). No printed source. -/
theorem shqrEps_le_half {B : ℝ} (hB : 1 ≤ B) : shqrEps (shqrDegree B) B ≤ 1 / 2 := by
  set q := shqrLogDegree B with hqdef
  have hB0 : 0 < B := by linarith
  have hq := two_le_shqrLogDegree hB
  have hL : 0 ≤ log B := log_nonneg hB
  have hmin := not_satisfiesSetk_of_lt_shqrLogDegree (B := B) (q := q - 1) (by omega)
  rw [satisfiesSetk_iff hB0 (by omega)] at hmin
  have hq1 : ((q - 1 : ℕ) : ℝ) = q - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hpow : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := by
    rw [eq_div_iff (by norm_num), ← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hq1, hpow] at hmin
  have hl3 : 1 < log 3 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    linarith [exp_one_lt_d9]
  have h12 : log 12 ≤ log 26 := log_le_log (by norm_num) (by norm_num)
  have e12 : log (12 : ℝ) = log 3 + 2 * log 2 := by
    rw [show (12 : ℝ) = 3 * 2 ^ 2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    push_cast; ring
  have hK : (0 : ℝ) < 2 ^ q := by positivity
  -- the denominator's logarithm exceeds $\log 3/2 > 1/2$
  have hden := log_shqrEps_denom_ge hB q
  have hgt : log 3 / 2 < (log 26 + (8 + 8 * q) * log B) / 2 ^ q := by
    rw [lt_div_iff₀ hK]
    nlinarith
  have hθ := shqrTheta_pos (2 ^ q) hB0
  have hα := shqrAlpha_pos (2 ^ q) hB0
  set P := (13 * B ^ 4) ^ (((2 ^ q : ℕ) : ℝ)⁻¹) * shqrAlpha (2 ^ q) B ^ 2 *
    shqrTheta (2 ^ q) B ^ 2 with hP
  have hP0 : 0 < P := by positivity
  have hP1 : 1.27744 < P := by
    have h := log_le_sub_one_of_pos (x := (1.27744 : ℝ)) (by norm_num)
    have : log (1.27744 : ℝ) < log P := by linarith
    exact (log_lt_log_iff (by norm_num) hP0).mp this
  have hb : 0.998 * (1 - 0.2) * (1 - 0.2) / P ≤ 1 / 2 := by
    rw [div_le_iff₀ hP0]; linarith
  have hb0 : 0 < 0.998 * (1 - 0.2) * (1 - 0.2) / P := by positivity
  have h4 : (4 : ℝ) ≤ 2 ^ q :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hexp : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) / (((2 ^ q : ℕ) : ℝ) - 1) := by
    push_cast
    rw [le_div_iff₀ (by linarith)]
    linarith
  calc shqrEps (shqrDegree B) B
      = (0.998 * (1 - 0.2) * (1 - 0.2) / P) ^ (((2 ^ q : ℕ) : ℝ) / (((2 ^ q : ℕ) : ℝ) - 1)) := by
        simp only [shqrEps, shqrDegree, hP, ← hqdef]
    _ ≤ (0.998 * (1 - 0.2) * (1 - 0.2) / P) ^ (1 : ℝ) :=
        rpow_le_rpow_of_exponent_ge hb0 (by linarith) hexp
    _ ≤ 1 / 2 := by rw [rpow_one]; exact hb

/-! ### The parameter choices

Inputs: the order $n + 1$, the shift degree $k$, the condition bound $B$, the separation
$\Gamma$, the norm bound $\Sigma$ (`S`), the backward error $\delta$ and the failure probability
$\varphi$. The choices, in order: the error budget and $\omega$; the cap $F$; the failure split;
the radius $R$ and the forward accuracy of `SmallEig`; Regularize's distance $\eta/2$ and Sh's
separation $d$; the precision threshold; and only then the words that depend on it (the
thresholds). The blocks run at condition $4B$, separation $\Gamma/4$, iterate norm $4\Sigma$. -/

/-- The backward error budget $\min(\delta, \Gamma/(16(n + 1)B))$ of the worklist: at most $\delta$
(the headline) and at most the class-preservation bound of the worklist. -/
noncomputable def shqrBudget (n : ℕ) (B Γ δ : ℝ) : ℝ := min δ (Γ / (16 * (n + 1) * B))

/-- The decoupling threshold $\omega = \mathrm{budget}/(12(n + 1))$ of the iteration. -/
noncomputable def shqrOmega (n : ℕ) (B Γ δ : ℝ) : ℝ := shqrBudget n B Γ δ / (12 * (n + 1))

/-- The contraction $1.002(1 - \gamma) = 0.8016$ of $\psi_k$ per Sh step at $\gamma = 0.2$. -/
noncomputable def shqrContraction : ℝ := 1.002 * (1 - 0.2)

/-- The iteration cap $F = \lceil \log(4\Sigma/\omega)/\log(1/0.8016) \rceil + 1$ (errata N7's
$+1$): $\psi_k \le 4\Sigma$ cannot stay above $\omega$ through $F$ contractions. -/
noncomputable def shqrCap (n : ℕ) (B Γ S δ : ℝ) : ℕ :=
  ⌈log (4 * S / shqrOmega n B Γ δ) / log (1 / shqrContraction)⌉₊ + 1

/-- The failure unit $\varphi/(12F(n + 1))$; also the failure allowed to `SmallEig`. -/
noncomputable def shqrSmallEigFailure (n : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  φ / (12 * shqrCap n B Γ S δ * (n + 1))

/-- The failure probability given to Regularize's disk draws, twice the unit (Regularize fails
with `SmallEig`'s failure plus half of it). -/
noncomputable def shqrRegularizeFailure (n : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  2 * shqrSmallEigFailure n B Γ S δ φ

/-- Regularize's radius $R = \omega^2/(8080 \cdot 4\Sigma)$. -/
noncomputable def shqrRadius (n : ℕ) (B Γ S δ : ℝ) : ℝ :=
  shqrOmega n B Γ δ ^ 2 / (8080 * (4 * S))

/-- The forward accuracy required of `SmallEig`, equal to the radius $R$ (Regularize needs
$\beta + R \le \omega^2/(4040 \cdot 4\Sigma)$ with room for rounding). -/
noncomputable def shqrSmallEigAccuracy (n : ℕ) (B Γ S δ : ℝ) : ℝ := shqrRadius n B Γ S δ

/-- Regularize's window $\eta = R\sqrt{\varphi_{\mathrm{reg}}/(2k)}$; the stored shifts are at
distance at least $\eta/2$ from the spectrum. -/
noncomputable def shqrEta (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  shqrRadius n B Γ S δ * √(shqrRegularizeFailure n B Γ S δ φ / (2 * k))

/-- Sh's shift separation
$d = \min(\eta/2, \varepsilon c_{\mathrm{lo}}\omega\sqrt{\varphi/(11(n + 1))}/4)$,
at condition $4B$ and with Sh's failure the unit $\varphi/(12F(n + 1))$. -/
noncomputable def shqrDist (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  min (shqrEta n k B Γ S δ φ / 2)
    (shqrEps k (4 * B) * (shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ) *
      √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)

/-! ### The precision threshold -/

/-- The precision term of the counts: $\boldsymbol{u} \le 1/10$ and
$10^5(n + 1 + k)^2\boldsymbol{u} \le 1$. -/
noncomputable def uShQRBasic (n k : ℕ) : ℝ :=
  min (1 / 10) (1 / (100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2))

/-- The precision term of Regularize (`NLAlib.ShiftedQR.regularize_pwrites` at condition $4B$,
norm $4\Sigma$): the rounding of the translates (`hβ`, `hdη`), Optimal's test (`huo`, N14) and
the forward error of the shifted chains (`hxu`, `hbound`). -/
noncomputable def uShQRRegularize (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  min (shqrOmega n B Γ δ ^ 2 / (16160 * (4 * S) ^ 2)) <|
  min (shqrEta n k B Γ S δ φ / (8 * (4 * S))) <|
  min ((shqrTheta k (4 * B) * shqrOmega n B Γ δ) ^ k /
    (30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ)) * ((2 + 2 * 1.1) * (4 * S)) ^ k)) <|
  min ((16 * (4 * B))⁻¹ * (shqrEta n k B Γ S δ φ / 2 / ((2 + 2 * 1.1) * (4 * S))) ^ k /
    (300 * (n + 1) ^ 2))
  (shqrOmega n B Γ δ / 2 / ((66 + 2 * 1.1) * (4 * B) * (4 * S) *
    ((2 + 2 * 1.1) * (4 * S) / (shqrEta n k B Γ S δ φ / 2)) ^ k * √(n + 1) * (300 * (n + 1) ^ 2)))

/-- The precision term of Sh (`NLAlib.ShiftedQR.shStep_pwrites` at condition $4B$, norm
$4\Sigma$): Find's half products (`hxu`), the forward error of the chains (`hbound`) and Exc's
rounded net and translate (`hexc1`, `hexc2`, at $\omega \le \psi_k \le 4\Sigma$). -/
noncomputable def uShQRSh (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  min ((8004 * (4 * B))⁻¹ * (shqrDist n k B Γ S δ φ / ((2 + 2 * shqrC k (4 * B)) * (4 * S))) ^ k /
    (300 * (n + 1) ^ 2)) <|
  min (0.001 * shqrOmega n B Γ δ / ((66 + 2 * shqrC k (4 * B)) * (4 * B) * (4 * S) *
    ((2 + 2 * shqrC k (4 * B)) * (4 * S) / shqrDist n k B Γ S δ φ) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2))) <|
  min (0.005 * shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ /
    (6 * (1.1 * (4 * S) + 3 * shqrRadiusHi k (4 * B) * (4 * S))))
  (shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ *
    √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8 /
      (6 * (1.1 * (4 * S) + 3 * shqrRadiusHi k (4 * B) * (4 * S))))

/-- The precision term of the iteration loop: $F$ iterations of Regularize and Sh, each with
backward error $(3.1 + C) \cdot 4\Sigma((1 + 300(n + 1)^2\boldsymbol{u})^k - 1)$, stay within a
sixth of the budget per round. -/
noncomputable def uShQRLoop (n k : ℕ) (B Γ S δ : ℝ) : ℝ :=
  min (1 / (2 * k * (300 * (n + 1) ^ 2)))
    (shqrBudget n B Γ δ / (6 * (n + 1)) / (shqrCap n B Γ S δ * ((3.1 + shqrC k (4 * B)) *
      (4 * S)) * (2 * k * (300 * (n + 1) ^ 2))))

/-- **The precision threshold of the rounded shifted QR algorithm**
[BanksGarzaVargasSrivastava2022, Theorem 6.3, corrected]: the minimum of the named per-block
terms `NLAlib.ShiftedQR.uShQRBasic`, `NLAlib.ShiftedQR.uShQRRegularize`,
`NLAlib.ShiftedQR.uShQRSh` and `NLAlib.ShiftedQR.uShQRLoop`. -/
noncomputable def uShQR (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  min (uShQRBasic n k) <| min (uShQRRegularize n k B Γ S δ φ) <|
    min (uShQRSh n k B Γ S δ φ) (uShQRLoop n k B Γ S δ)

/-! ### The words that depend on the precision threshold -/

/-- The bottom-scan threshold word of the iteration,
$(1 + \boldsymbol{u}_{\mathrm{ShQR}})^2\omega^2$ (at least $(1 + \boldsymbol{u})^2\omega^2$ for
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$). -/
noncomputable def shqrScanThreshold (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) ^ 2 * shqrOmega n B Γ δ ^ 2

/-- The decoupling level
$\omega_D = (1 + \boldsymbol{u}_{\mathrm{ShQR}})\omega/(1 - \boldsymbol{u}_{\mathrm{ShQR}})$
that a passing bottom scan certifies. -/
noncomputable def shqrDecoupled (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) * shqrOmega n B Γ δ / (1 - uShQR n k B Γ S δ φ)

/-- The worklist's deflation threshold word $(1 + \boldsymbol{u}_{\mathrm{ShQR}})^2\omega_D^2$. -/
noncomputable def shqrDeflationThreshold (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) ^ 2 * shqrDecoupled n k B Γ S δ φ ^ 2

/-- The worklist's cut level
$c = (1 + \boldsymbol{u}_{\mathrm{ShQR}})\omega_D/(1 - \boldsymbol{u}_{\mathrm{ShQR}})$. -/
noncomputable def shqrCut (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) * shqrDecoupled n k B Γ S δ φ / (1 - uShQR n k B Γ S δ φ)

/-- The backward error of the decoupler on a block, $F(3.1 + C) \cdot 4\Sigma((1 +
300(n + 1)^2\boldsymbol{u})^k - 1)$: $F$ iterations of Regularize and Sh on iterates of norm at
most $4\Sigma$. -/
noncomputable def shqrDecoupleError (n k : ℕ) (B Γ S δ u : ℝ) : ℝ :=
  shqrCap n B Γ S δ * ((3.1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))

/-! ### Positivity (review B1)

Without these the headline would be vacuous through $0 \le \boldsymbol{u} \le$ `uShQR` and the bit
count $\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}})$ would be junk. -/

section Positivity

variable {n k : ℕ} {B Γ S δ φ : ℝ}

theorem shqrBudget_pos (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) : 0 < shqrBudget n B Γ δ := by
  have : 0 < B := by linarith
  unfold shqrBudget; positivity

theorem shqrOmega_pos (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) : 0 < shqrOmega n B Γ δ := by
  have := shqrBudget_pos (n := n) hB hΓ hδ
  unfold shqrOmega; positivity

theorem one_le_shqrCap : 1 ≤ shqrCap n B Γ S δ := by
  unfold shqrCap; omega

/-- **The failure allowed to `SmallEig` is positive**: for $\varphi > 0$,
$0 < \varphi/(12F(n + 1))$. No printed source. -/
theorem shqrSmallEigFailure_pos (hφ : 0 < φ) : 0 < shqrSmallEigFailure n B Γ S δ φ := by
  have : (1 : ℝ) ≤ shqrCap n B Γ S δ := by exact_mod_cast one_le_shqrCap
  unfold shqrSmallEigFailure; positivity

theorem shqrRadius_pos (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S) :
    0 < shqrRadius n B Γ S δ := by
  have := shqrOmega_pos (n := n) hB hΓ hδ
  unfold shqrRadius; positivity

/-- **The forward accuracy required of `SmallEig` is positive**: for $B \ge 1$, $\Gamma > 0$,
$\delta > 0$ and $\Sigma > 0$, $0 < \omega^2/(8080 \cdot 4\Sigma)$. No printed source. -/
theorem shqrSmallEigAccuracy_pos (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S) :
    0 < shqrSmallEigAccuracy n B Γ S δ :=
  shqrRadius_pos hB hΓ hδ hS

theorem shqrEta_pos (hk : 0 < k) (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S)
    (hφ : 0 < φ) : 0 < shqrEta n k B Γ S δ φ := by
  have := shqrRadius_pos (n := n) hB hΓ hδ hS
  have := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have : (0 : ℝ) < k := by exact_mod_cast hk
  unfold shqrEta shqrRegularizeFailure; positivity

theorem shqrDist_pos (hk : 0 < k) (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S)
    (hφ : 0 < φ) : 0 < shqrDist n k B Γ S δ φ := by
  have hB4 : 0 < 4 * B := by linarith
  have := shqrEta_pos (n := n) hk hB hΓ hδ hS hφ
  have := shqrOmega_pos (n := n) hB hΓ hδ
  have := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have := shqrEps_pos k hB4
  have := shqrRadiusLo_pos k hB4
  unfold shqrDist; positivity

theorem shqrC_pos (k : ℕ) (hB : 0 < B) : 0 < shqrC k B := by
  have := shqrRadiusHi_pos k hB
  unfold shqrC; positivity

/-- **The precision threshold is positive** (review B1): for $k \ge 1$, $B \ge 1$, $\Gamma > 0$,
$\delta > 0$, $\Sigma > 0$ and $\varphi > 0$, $0 < \boldsymbol{u}_{\mathrm{ShQR}}$. No printed
source. -/
theorem uShQR_pos (hk : 0 < k) (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S)
    (hφ : 0 < φ) : 0 < uShQR n k B Γ S δ φ := by
  have hB4 : 0 < 4 * B := by linarith
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have hb := shqrBudget_pos (n := n) hB hΓ hδ
  have hη := shqrEta_pos (n := n) hk hB hΓ hδ hS hφ
  have hd := shqrDist_pos (n := n) hk hB hΓ hδ hS hφ
  have hf := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have := shqrEps_pos k hB4
  have := shqrRadiusLo_pos k hB4
  have := shqrRadiusHi_pos k hB4
  have := shqrTheta_pos k hB4
  have := shqrC_pos k hB4
  have hF : (1 : ℝ) ≤ shqrCap n B Γ S δ := by exact_mod_cast one_le_shqrCap
  have : (0 : ℝ) < k := by exact_mod_cast hk
  unfold uShQR uShQRBasic uShQRRegularize uShQRSh uShQRLoop
  refine lt_min (by positivity) (lt_min ?_ (lt_min ?_ ?_))
  · exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))
  · exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (by positivity)))
  · exact lt_min (by positivity) (by positivity)

end Positivity

end NLAlib.ShiftedQR
