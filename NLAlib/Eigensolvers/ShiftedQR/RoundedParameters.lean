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
# Shift degree and constants of the rounded shifted QR algorithm

[BanksGarzaVargasSrivastava2022, §2.3 and Theorem 6.3]: the shift degree $k$ of (eqn:setk) and the
global constants $\theta$, $\alpha$, $\gamma = 0.2$, Exc's $\varepsilon$ and the shift reach $C$,
with their bounds under (eqn:setk). The parameter choices that use them are in
`NLAlib.Eigensolvers.ShiftedQR.RoundedParameterChoices`.

## Main definitions

* `NLAlib.ShiftedQR.SatisfiesSetk`, `NLAlib.ShiftedQR.shqrLogDegree`,
  `NLAlib.ShiftedQR.shqrDegree`: the degree rule (eqn:setk).
* `NLAlib.ShiftedQR.shqrTheta`, `NLAlib.ShiftedQR.shqrAlpha`, `NLAlib.ShiftedQR.shqrEps`,
  `NLAlib.ShiftedQR.shqrC`: the global constants.

## Main results

* `NLAlib.ShiftedQR.two_le_shqrDegree`, `NLAlib.ShiftedQR.rpow_two_div_shqrDegree_le`: $k \ge 2$
  and $B^{2/k} \le 2$.
* `NLAlib.ShiftedQR.shqrEps_le_half`, `NLAlib.ShiftedQR.shqrEps_ge`: Exc's
  $1/100 \le \varepsilon \le 1/2$ under (eqn:setk).
* `NLAlib.ShiftedQR.shqrAlpha_le`, `NLAlib.ShiftedQR.shqrTheta_le`, `NLAlib.ShiftedQR.shqrC_le`,
  `NLAlib.ShiftedQR.shqrDegree_le`: under (eqn:setk), $\alpha \le 1.8$, $\theta \le 1.2$,
  $C \le 7$ and $k \le 512B^2$.
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

/-- The shift degree is at least two: for $B \ge 1$, the degree $k$ of (eqn:setk) satisfies
$k \ge 2$ (even $k \ge 4$). Sh's decrease factor $1.002$
([BanksGarzaVargasSrivastava2022, Lemma 5.4]) needs $k \ge 2$; at $k = 1$ it is $1.0021$. -/
theorem two_le_shqrDegree {B : ℝ} (hB : 1 ≤ B) : 2 ≤ shqrDegree B := by
  have := two_le_shqrLogDegree hB
  calc 2 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ shqrLogDegree B := Nat.pow_le_pow_right (by norm_num) this

/-- The degree rule gives $B^{2/k} \le 2$ (the hypothesis `hBk` of Regularize): for $B \ge 1$
and $k$ the degree of (eqn:setk), $B^{2/k} \le 2$ (in fact $\le 1.05$). -/
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

/-- The upper radius coefficient $2.002^{1/k}\theta\alpha B^{1/k}$ of Exc. The bound
(eq:boundsonR) of [BanksGarzaVargasSrivastava2022, Lemma 5.3] has $1.001\theta\alpha B^{1/k}$,
which omits the factor $2^{1/k}$ of the first line of Exc. -/
noncomputable def shqrRadiusHi (k : ℕ) (B : ℝ) : ℝ :=
  (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * shqrTheta k B * shqrAlpha k B * B ^ ((k : ℝ)⁻¹)

/-- The shift reach $C = 1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k}$, at most $4.7$ under
(eqn:setk). [BanksGarzaVargasSrivastava2022, Lemma 5.3 and Lemma 6.4] take $C = 3$, which is too
small once the radius bound carries the factor $2.002^{1/k}$. -/
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

/-- Exc's net width is at most one half under (eqn:setk) (the hypothesis `hε2` of Sh): for
$B \ge 1$ and $k$ the degree of (eqn:setk), $\varepsilon \le 1/2$ (in fact $\varepsilon < 0.39$;
numerically $\varepsilon \in [0.098, 0.353]$ over $B \ge 1$). -/
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

/-! ### Bounds on the constants under (eqn:setk) -/

/-- A root bound: $x \le c^m$ gives $x^{1/m} \le c$. -/
theorem rpow_inv_natCast_le_of_le_pow {x c : ℝ} {m : ℕ} (hm : m ≠ 0) (hx : 0 ≤ x) (hc : 0 ≤ c)
    (h : x ≤ c ^ m) : x ^ ((m : ℝ)⁻¹) ≤ c := by
  calc x ^ ((m : ℝ)⁻¹) ≤ (c ^ m) ^ ((m : ℝ)⁻¹) := rpow_le_rpow hx h (by positivity)
    _ = c := pow_rpow_inv_natCast hc hm

/-- The facts of (eqn:setk) used for the constants: at $k = 2^q$, $q \ge 2$,
$B^{q/k} \le 1.148$ and $B^{1/k} \le 1.042$. -/
theorem setk_rpow_bounds {B : ℝ} (hB : 1 ≤ B) :
    B ^ ((shqrLogDegree B : ℝ) / shqrDegree B) ≤ 1.148 ∧
      B ^ ((shqrDegree B : ℝ)⁻¹) ≤ 1.042 := by
  set q := shqrLogDegree B with hqdef
  have hq := two_le_shqrLogDegree hB
  obtain ⟨-, hs⟩ := satisfiesSetk_shqrLogDegree hB
  rw [← hqdef] at hs
  have hk : (shqrDegree B : ℝ) = 2 ^ q := by simp [shqrDegree, q]
  have h4 : (4 : ℝ) ≤ 2 ^ q :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hk1 : (0 : ℝ) < 2 ^ q - 1 := by linarith
  have hq0 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set e : ℝ := (8 * q + 11) / (2 ^ q - 1) with he
  have he0 : 0 < e := by positivity
  -- $B^e \le 3$
  have hBe : B ^ e ≤ 3 := by
    have h8 : B ^ ((8 : ℝ) / (2 ^ q - 1)) ≤ (2 * B ^ 4) ^ ((2 : ℝ) / (2 ^ q - 1)) := by
      rw [show (8 : ℝ) / (2 ^ q - 1) = ((4 : ℕ) : ℝ) * (2 / (2 ^ q - 1)) by push_cast; ring,
        rpow_natCast_mul (by linarith)]
      exact rpow_le_rpow (by positivity) (by nlinarith [one_le_pow₀ (n := 4) hB])
        (by positivity)
    calc B ^ e = B ^ ((8 * q + 3 : ℝ) / (2 ^ q - 1)) * B ^ ((8 : ℝ) / (2 ^ q - 1)) := by
          rw [← rpow_add (by linarith)]; congr 1; rw [he]; field_simp; ring
      _ ≤ B ^ ((8 * q + 3 : ℝ) / (2 ^ q - 1)) * (2 * B ^ 4) ^ ((2 : ℝ) / (2 ^ q - 1)) := by
          gcongr
      _ ≤ 3 := hs
  have key : ∀ {x : ℝ} {m : ℕ}, m ≠ 0 → x ≤ e / m → B ^ x ≤ 3 ^ ((m : ℝ)⁻¹) := by
    intro x m hm hx
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    calc B ^ x ≤ B ^ (e * (m : ℝ)⁻¹) := rpow_le_rpow_of_exponent_le hB (by rwa [← div_eq_mul_inv])
      _ = (B ^ e) ^ ((m : ℝ)⁻¹) := rpow_mul (by linarith) _ _
      _ ≤ 3 ^ ((m : ℝ)⁻¹) := rpow_le_rpow (by positivity) hBe (by positivity)
  refine ⟨?_, ?_⟩
  · refine (key (m := 8) (by norm_num) ?_).trans
      (rpow_inv_natCast_le_of_le_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    rw [hk, he, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  · refine (key (m := 27) (by norm_num) ?_).trans
      (rpow_inv_natCast_le_of_le_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    rw [hk, he, div_div, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith

/-- The shift degree is $k = 2^q$ with $2q \le k$ and $k \ge 4$. -/
theorem shqrDegree_facts {B : ℝ} (hB : 1 ≤ B) :
    (4 : ℝ) ≤ shqrDegree B ∧ 2 * (shqrLogDegree B : ℝ) ≤ shqrDegree B := by
  have hq := two_le_shqrLogDegree hB
  have hk : (shqrDegree B : ℝ) = 2 ^ shqrLogDegree B := by simp [shqrDegree]
  rw [hk]
  refine ⟨?_, ?_⟩
  · calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ shqrLogDegree B := pow_le_pow_right₀ (by norm_num) hq
  · have h : ∀ q : ℕ, 2 * q ≤ 2 ^ q := by
      intro q
      induction q with
      | zero => simp
      | succ q ih => rw [pow_succ]; have := Nat.lt_two_pow_self (n := q); omega
    exact_mod_cast h _

/-- The promising factor under (eqn:setk): for $B \ge 1$ and $k$ the degree of (eqn:setk),
$\alpha = (1.01B)^{4\log_2 k/k} \le 1.8$ (numerically $\le 1.64$). -/
theorem shqrAlpha_le {B : ℝ} (hB : 1 ≤ B) : shqrAlpha (shqrDegree B) B ≤ 1.8 := by
  obtain ⟨hq, -⟩ := setk_rpow_bounds hB
  obtain ⟨hk4, h2q⟩ := shqrDegree_facts hB
  have hlog : Nat.log 2 (shqrDegree B) = shqrLogDegree B := by
    simp [shqrDegree, Nat.log_pow (by norm_num : 1 < 2)]
  have hk0 : (0 : ℝ) < shqrDegree B := by linarith
  unfold shqrAlpha
  rw [hlog, mul_rpow (by norm_num) (by linarith)]
  have h1 : (1.01 : ℝ) ^ ((4 * shqrLogDegree B : ℝ) / shqrDegree B) ≤ 1.01 ^ (2 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_iff₀ hk0]; linarith)
  have h2 : B ^ ((4 * shqrLogDegree B : ℝ) / shqrDegree B) ≤ 1.148 ^ 4 := by
    rw [mul_div_assoc, rpow_mul (by linarith)]
    calc (B ^ (4 : ℝ)) ^ ((shqrLogDegree B : ℝ) / shqrDegree B)
        = (B ^ ((shqrLogDegree B : ℝ) / shqrDegree B)) ^ (4 : ℕ) := by
          rw [← rpow_natCast, ← rpow_mul (by linarith), ← rpow_mul (by linarith)]
          push_cast; ring_nf
      _ ≤ 1.148 ^ 4 := pow_le_pow_left₀ (by positivity) hq 4
  calc (1.01 : ℝ) ^ ((4 * shqrLogDegree B : ℝ) / shqrDegree B) *
        B ^ ((4 * shqrLogDegree B : ℝ) / shqrDegree B) ≤ 1.01 ^ (2 : ℝ) * 1.148 ^ 4 := by
        gcongr
    _ ≤ 1.8 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num

/-- The optimality factor under (eqn:setk): for $B \ge 1$ and $k$ the degree of (eqn:setk),
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)} \le 1.2$ (numerically $\le 1.15$, and
$\le 1.05$ for $B \ge 4$). -/
theorem shqrTheta_le {B : ℝ} (hB : 1 ≤ B) : shqrTheta (shqrDegree B) B ≤ 1.2 := by
  obtain ⟨-, hb⟩ := setk_rpow_bounds hB
  obtain ⟨hk4, -⟩ := shqrDegree_facts hB
  set k := shqrDegree B
  have hk0 : (0 : ℝ) < k := by linarith
  have hB0 : 0 ≤ B := by linarith
  unfold shqrTheta
  have h1 : (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) ≤ 0.998 ^ (-1 : ℝ) :=
    rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (by rw [neg_le_neg_iff, inv_le_one₀ hk0]; linarith)
  have h2 : (2 : ℝ) ^ ((2 * k : ℝ)⁻¹) ≤ 1.091 := by
    refine (rpow_le_rpow_of_exponent_le (by norm_num) (?_ : (2 * k : ℝ)⁻¹ ≤ ((8 : ℕ) : ℝ)⁻¹)).trans
      (rpow_inv_natCast_le_of_le_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    exact inv_anti₀ (by norm_num) (by push_cast; linarith)
  have h3 : (B ^ 4) ^ ((2 * k : ℝ)⁻¹) ≤ 1.042 ^ 2 := by
    calc (B ^ 4) ^ ((2 * k : ℝ)⁻¹) = (B ^ ((k : ℝ)⁻¹)) ^ (2 : ℕ) := by
          rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul hB0, ← rpow_mul hB0]
          congr 1; field_simp; norm_num
      _ ≤ 1.042 ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
  rw [mul_rpow (by norm_num) (by positivity)]
  calc 1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * ((2 : ℝ) ^ ((2 * k : ℝ)⁻¹) * (B ^ 4) ^ ((2 * k : ℝ)⁻¹))
      ≤ 1.01 * 0.998 ^ (-1 : ℝ) * (1.091 * 1.042 ^ 2) := by gcongr
    _ ≤ 1.2 := by rw [rpow_neg_one]; norm_num

/-- The shift reach under (eqn:setk): for $B \ge 1$ and $k$ the degree of (eqn:setk),
$C = 1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le 7$ (a factorwise bound; numerically
$C \le 4.69$, which needs a joint analysis of the factors). -/
theorem shqrC_le {B : ℝ} (hB : 1 ≤ B) : shqrC (shqrDegree B) B ≤ 7 := by
  obtain ⟨-, hb⟩ := setk_rpow_bounds hB
  obtain ⟨hk4, -⟩ := shqrDegree_facts hB
  have hα := shqrAlpha_le hB
  have hθ := shqrTheta_le hB
  have hα0 := shqrAlpha_pos (shqrDegree B) (by linarith : 0 < B)
  have hθ0 := shqrTheta_pos (shqrDegree B) (by linarith : 0 < B)
  set k := shqrDegree B
  have hk0 : (0 : ℝ) < k := by linarith
  have h1 : (2.002 : ℝ) ^ ((k : ℝ)⁻¹) ≤ 1.19 := by
    refine (rpow_le_rpow_of_exponent_le (by norm_num) (?_ : (k : ℝ)⁻¹ ≤ ((4 : ℕ) : ℝ)⁻¹)).trans
      (rpow_inv_natCast_le_of_le_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    exact inv_anti₀ (by norm_num) (by push_cast; linarith)
  unfold shqrC shqrRadiusHi
  have : (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * shqrTheta k B * shqrAlpha k B * B ^ ((k : ℝ)⁻¹) ≤
      1.19 * 1.2 * 1.8 * 1.042 := by gcongr
  linarith

/-- An upper bound for the shift degree: for $B \ge 1$, the degree of (eqn:setk) is at most
$512B^2$: (eqn:setk) holds at $q = 2m + 9$ for $2^m \le B < 2^{m+1}$. -/
theorem shqrDegree_le {B : ℝ} (hB : 1 ≤ B) : (shqrDegree B : ℝ) ≤ 512 * B ^ 2 := by
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hB (by norm_num : (1 : ℝ) < 2)
  have hB0 : 0 < B := by linarith
  have hsq : ∀ j : ℕ, (j + 1) ^ 2 ≤ 4 ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ 4]
      have : (j + 1 + 1) ^ 2 ≤ 4 * (j + 1) ^ 2 := by ring_nf; omega
      omega
  have hset : SatisfiesSetk B (2 * m + 9) := by
    rw [satisfiesSetk_iff hB0 (by omega)]
    have hl : log B ≤ (m + 1) * log 2 := by
      have := log_le_log hB0 hm2.le
      rw [log_pow] at this; push_cast at this; exact this
    have hl0 : 0 ≤ log B := log_nonneg hB
    have hl2 : 0 < log 2 := log_pos (by norm_num)
    have hl23 : log 2 ≤ log 3 := log_le_log (by norm_num) (by norm_num)
    have hnat : ((16 * m + 83) * (m + 1) + 3 : ℝ) ≤ 2 ^ (2 * m + 9) := by
      have : (16 * m + 83) * (m + 1) + 3 ≤ 2 ^ (2 * m + 9) := by
        rw [pow_add, pow_mul]; norm_num; nlinarith [hsq m]
      exact_mod_cast this
    push_cast
    have h2 : (1 : ℝ) ≤ 2 ^ (2 * m + 9) - 1 := by nlinarith
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    calc (8 * (2 * (m : ℝ) + 9) + 11) * log B + 2 * log 2
        ≤ (8 * (2 * (m : ℝ) + 9) + 11) * ((m + 1) * log 2) + 2 * log 2 := by gcongr
      _ = ((16 * m + 83) * (m + 1) + 2) * log 2 := by ring
      _ ≤ (2 ^ (2 * m + 9) - 1) * log 2 := by gcongr; linarith
      _ ≤ (2 ^ (2 * m + 9) - 1) * log 3 := by gcongr
  have hle : shqrLogDegree B ≤ 2 * m + 9 := Nat.sInf_le hset
  have : (shqrDegree B : ℝ) ≤ 2 ^ (2 * m + 9) := by
    simp only [shqrDegree, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hle
  calc (shqrDegree B : ℝ) ≤ 2 ^ (2 * m + 9) := this
    _ = 512 * (2 ^ m) ^ 2 := by ring
    _ ≤ 512 * B ^ 2 := by gcongr

/-- The logarithm of Exc's denominator $P = (13B^4)^{1/k}\alpha^2\theta^2$ at $k = 2^q$, $B > 0$,
times $k$: $k\log P = \log 26 + (8 + 8q)\log B + 8q\log 1.01 + 2k\log 1.01 - 2\log 0.998$. -/
theorem mul_log_shqrEps_denom {B : ℝ} (hB : 0 < B) (q : ℕ) :
    2 ^ q * log ((13 * B ^ 4) ^ (((2 ^ q : ℕ) : ℝ)⁻¹) * shqrAlpha (2 ^ q) B ^ 2 *
        shqrTheta (2 ^ q) B ^ 2) =
      log 26 + (8 + 8 * q) * log B + 8 * q * log 1.01 + 2 * 2 ^ q * log 1.01 -
        2 * log 0.998 := by
  have hθ := shqrTheta_pos (2 ^ q) hB
  have hα := shqrAlpha_pos (2 ^ q) hB
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
    e26]
  field_simp
  ring

/-- Exc's net width is at least one hundredth under (eqn:setk) (the lower bound behind
Regularize's window, the hypothesis `hd` of
`NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract`): for $B \ge 1$ and $k$ the degree of
(eqn:setk), $\varepsilon \ge 1/100$ (numerically $\varepsilon \ge 0.039$; the denominator
$(13B^4)^{1/k}\alpha^2\theta^2$ is at most $6$, and $k/(k - 1) \le 2$). -/
theorem shqrEps_ge {B : ℝ} (hB : 1 ≤ B) : 1 / 100 ≤ shqrEps (shqrDegree B) B := by
  set q := shqrLogDegree B with hqdef
  have hB0 : 0 < B := by linarith
  have hq := two_le_shqrLogDegree hB
  have hL : 0 ≤ log B := log_nonneg hB
  have hs := (satisfiesSetk_iff hB0 (by omega : 1 ≤ q)).mp (satisfiesSetk_shqrLogDegree hB)
  have hK4 : (4 : ℝ) ≤ 2 ^ q :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  -- $2q \le 2^q$
  have h2q : (2 * q : ℝ) ≤ 2 ^ q := by
    have h := Nat.lt_two_pow_self (n := q - 1)
    have e : 2 ^ q = 2 * 2 ^ (q - 1) := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    exact_mod_cast (show 2 * q ≤ 2 ^ q by omega)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  -- numerical facts
  have l101 : log (1.01 : ℝ) ≤ 0.01 := by
    have := log_le_sub_one_of_pos (x := (1.01 : ℝ)) (by norm_num); linarith
  have l101' : 0 ≤ log (1.01 : ℝ) := log_nonneg (by norm_num)
  have l998 : -0.0021 ≤ log (0.998 : ℝ) := by
    have := one_sub_inv_le_log_of_pos (x := (0.998 : ℝ)) (by norm_num); norm_num at this ⊢
    linarith
  have l26 : log (26 : ℝ) ≤ 3 * log 3 := by
    have : log (3 ^ 3 : ℝ) = 3 * log 3 := by rw [log_pow]; norm_num
    rw [← this]; exact log_le_log (by norm_num) (by norm_num)
  have l169 : 7 / 16 ≤ 4 * log 2 - 2 * log 3 := by
    have := one_sub_inv_le_log_of_pos (x := (16 / 9 : ℝ)) (by norm_num)
    rw [show (16 / 9 : ℝ) = 2 ^ 4 / 3 ^ 2 by norm_num, log_div (by norm_num) (by norm_num),
      log_pow, log_pow] at this
    norm_num at this ⊢; linarith
  have l2 := log_two_gt_d9
  set P := (13 * B ^ 4) ^ (((2 ^ q : ℕ) : ℝ)⁻¹) * shqrAlpha (2 ^ q) B ^ 2 *
    shqrTheta (2 ^ q) B ^ 2 with hP
  have hθ := shqrTheta_pos (2 ^ q) hB0
  have hα := shqrAlpha_pos (2 ^ q) hB0
  have hP0 : 0 < P := by positivity
  have hden := mul_log_shqrEps_denom hB0 q
  rw [← hP] at hden
  -- $k\log P \le k\log 6$
  have hP6 : log P ≤ log 6 := by
    have e6 : log (6 : ℝ) = log 2 + log 3 := by
      rw [← log_mul (by norm_num) (by norm_num)]; norm_num
    have a1 : (q : ℝ) * log 1.01 ≤ q * 0.01 := mul_le_mul_of_nonneg_left l101 hq0
    have a2 : (2 ^ q : ℝ) * log 1.01 ≤ 2 ^ q * 0.01 :=
      mul_le_mul_of_nonneg_left l101 (by positivity)
    have a3 : 0 ≤ (2 ^ q - 4 : ℝ) * (log 2 - 0.06) := mul_nonneg (by linarith) (by linarith)
    have a4 : 0 ≤ (q : ℝ) * log B := mul_nonneg hq0 hL
    have h : 2 ^ q * log P ≤ 2 ^ q * log 6 := by rw [hden, e6]; nlinarith
    exact le_of_mul_le_mul_left h (by positivity)
  have hP6' : P ≤ 6 := (log_le_log_iff hP0 (by norm_num)).mp hP6
  set x := 0.998 * (1 - 0.2) * (1 - 0.2) / P with hx
  have hx0 : 0 < x := by positivity
  have hx10 : 1 / 10 ≤ x := by rw [hx, le_div_iff₀ hP0]; linarith
  have hk : ((2 ^ q : ℕ) : ℝ) = 2 ^ q := by push_cast; ring
  have he : shqrEps (shqrDegree B) B = x ^ (((2 ^ q : ℕ) : ℝ) / (((2 ^ q : ℕ) : ℝ) - 1)) := by
    simp only [shqrEps, shqrDegree, hx, hP, ← hqdef]
  have hexp0 : (0 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) / (((2 ^ q : ℕ) : ℝ) - 1) := by
    rw [hk]; exact div_nonneg (by linarith) (by linarith)
  have hexp2 : ((2 ^ q : ℕ) : ℝ) / (((2 ^ q : ℕ) : ℝ) - 1) ≤ 2 := by
    rw [hk, div_le_iff₀ (by linarith)]; linarith
  rw [he]
  rcases le_or_gt x 1 with hx1 | hx1
  · calc (1 / 100 : ℝ) ≤ x ^ 2 := by nlinarith
      _ = x ^ (2 : ℝ) := (rpow_natCast x 2).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_ge hx0 hx1 hexp2
  · exact le_trans (by norm_num) (one_le_rpow hx1.le hexp0)

end NLAlib.ShiftedQR
