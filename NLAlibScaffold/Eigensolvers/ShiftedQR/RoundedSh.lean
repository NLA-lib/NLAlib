/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedShTrial
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedFind
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedRegularize

/-!
# The rounded shifting strategy

The shifting strategy $\mathrm{Sh}_{k,B}$ of [BanksGarzaVargasSrivastava2022, Lemma 5.4]
in floating point: from $\theta$-optimal shifts, `Find` selects a promising one, $r$; if the
rounded $\tau_{(z - r)^k}(\mathbf{H})^k$ (`comptau` of the rounded step) is below the rounded
$(1 - \gamma)^k\psi_k(\mathbf{H})^k$, the rounded step with $r$ is the output; otherwise the
exceptional shifts around $r$ are tried in turn, and one of them decouples or contracts the
potential except with probability $\varphi$ (the random translate of `Exc`). A flag word records
whether a step was taken ($1$) or no trial succeeded ($2$, the fail word of the errata N11).

## Main definitions

* `NLAlib.ShiftedQR.shStep`: the program; `NLAlib.ShiftedQR.ShOutcome`: its outcome.

## Main results

* `NLAlib.ShiftedQR.potential_contract_of_comptau_lt`,
  `NLAlib.ShiftedQR.norm_inv_le_of_le_comptau`: the two branches of the `comptau` test.
* `NLAlib.ShiftedQR.excRadius_window`: the rounded exceptional radius is in the window of
  `Exc`.
* `NLAlib.ShiftedQR.shStep_pwrites`: `Sh` as a probabilistic block.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The last row of the inverse of a matrix with nonzero determinant is nonzero. -/
theorem norm_toLp_inv_apply_pos {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.det ≠ 0)
    (i : Fin (n + 1)) : 0 < ‖WithLp.toLp 2 (A⁻¹ i)‖ := by
  refine (norm_nonneg _).lt_of_ne fun h0 => ?_
  have hrow : A⁻¹ i = 0 := by
    have := (norm_eq_zero.mp h0.symm)
    simpa using congrArg WithLp.ofLp this
  have hdet : A⁻¹.det = 0 := Matrix.det_eq_zero_of_row_eq_zero i fun j => by
    simp [hrow]
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hdet
  exact hA (inv_eq_zero.mp hdet)

/-- The last row of $(\mathbf{H} - r)^{-k}$ is nonzero when $r$ is no eigenvalue of a
diagonalisable $\mathbf{H}$. -/
theorem norm_toLp_inv_aeval_replicate_last_pos {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) {r : ℂ}
    (hne : ∀ i, e i ≠ r) (k : ℕ) :
    0 < ‖WithLp.toLp 2
      ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖ := by
  refine norm_toLp_inv_apply_pos ?_ _
  rw [aeval_shiftPoly_replicate, Matrix.det_pow]
  exact pow_ne_zero _ (det_sub_smul_one_ne_zero_of_forall_ne hV hHV hne)

/-- The norm of the last row of $(\mathbf{H} - s)^{-k}$ is a measurable function of $s$. -/
theorem measurable_norm_toLp_inv_aeval_replicate_last (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (k : ℕ) : Measurable fun s : ℂ => ‖WithLp.toLp 2
      ((Polynomial.aeval H (shiftPoly (List.replicate k s)))⁻¹ (Fin.last n))‖ := by
  have hc : Continuous fun s : ℂ =>
      (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ^ k := by fun_prop
  have hinv : Measurable fun s : ℂ =>
      ((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ^ k)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hc.matrix_det.measurable.inv).smul hc.matrix_adjugate.measurable
  simp only [aeval_shiftPoly_replicate]
  exact (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_apply (Fin.last n) |>.comp hinv) |>.norm

end NLAlib

namespace NLAlib.ShiftedQR

open Ops

/-- $1.0011^k \cdot 1.0012 \le 1.002^k$ for $k \ge 2$: the contraction factor of `Sh`
([BanksGarzaVargasSrivastava2022, Lemma 5.4]; $k \ge 2$ is needed, errata N11). -/
theorem pow_mul_le_pow_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    (1.0011 : ℝ) ^ k * 1.0012 ≤ 1.002 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k _ ih =>
    rw [pow_succ, pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1.0011) k]

/-- **The accepted branch of the `comptau` test** ([BanksGarzaVargasSrivastava2022, proof of
Lemma 5.4]): let $N > 0$ (the norm $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\|$), the
computed $t$ within $0.001$, relatively, of $N^{-1}$, the computed threshold within
$(10k + 12)\boldsymbol{u}$, relatively, of $(1 - \gamma)^k\psi^k$, $\psi \ge 0$, $\gamma \le 1$,
$k \ge 2$ and $10^5k\boldsymbol{u} \le 1$. If $t$ is below the threshold and
$\psi'^k N \le 1.0011^k$ with $\psi' \ge 0$, then $\psi' \le 1.002(1 - \gamma)\psi$. -/
theorem potential_contract_of_comptau_lt {u γ t thr N ψ ψ' : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hu0 : 0 ≤ u) (hku : 100000 * k * u ≤ 1) (hγ1 : γ ≤ 1) (hψ : 0 ≤ ψ) (hψ' : 0 ≤ ψ')
    (hN : 0 < N) (ht : |t - N⁻¹| ≤ 0.001 * N⁻¹)
    (hthr : |thr - (1 - γ) ^ k * ψ ^ k| ≤ (10 * k + 12) * u * ((1 - γ) ^ k * ψ ^ k))
    (hlt : t < thr) (hpot : ψ' ^ k * N ≤ 1.0011 ^ k) : ψ' ≤ 1.002 * (1 - γ) * ψ := by
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hg : 0 ≤ 1 - γ := by linarith
  have hc : 0 ≤ (1 - γ) ^ k * ψ ^ k := by positivity
  have hδ : (10 * k + 12) * u ≤ 0.00016 := by nlinarith
  have h1 : 0.999 * N⁻¹ ≤ t := by linarith [(abs_le.mp ht).1]
  have h2 : thr ≤ (1 + 0.00016) * ((1 - γ) ^ k * ψ ^ k) := by
    nlinarith [(abs_le.mp hthr).2, mul_le_mul_of_nonneg_right hδ hc]
  have h3 : N⁻¹ ≤ 1.0012 * ((1 - γ) ^ k * ψ ^ k) := by nlinarith
  have h4 : ψ' ^ k ≤ 1.0011 ^ k * N⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hN]; exact hpot
  have h5 : ψ' ^ k ≤ (1.002 * (1 - γ) * ψ) ^ k := by
    have hp := pow_mul_le_pow_of_two_le hk
    calc ψ' ^ k ≤ 1.0011 ^ k * (1.0012 * ((1 - γ) ^ k * ψ ^ k)) :=
          h4.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ = (1.0011 ^ k * 1.0012) * ((1 - γ) ^ k * ψ ^ k) := by ring
      _ ≤ 1.002 ^ k * ((1 - γ) ^ k * ψ ^ k) := mul_le_mul_of_nonneg_right hp hc
      _ = _ := by rw [mul_pow, mul_pow]; ring
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) h5

/-- **The rejected branch of the `comptau` test** ([BanksGarzaVargasSrivastava2022, proof of
Lemma 5.4]): under the hypotheses of `NLAlib.ShiftedQR.potential_contract_of_comptau_lt` on
$t$ and the threshold, with $\gamma < 1$ and $\psi > 0$, if $t$ is not below the threshold,
then $N \le ((0.998(1 - \gamma)\psi)^{-1})^k$: the shift $r$ stagnates with the ratio
$\xi = 0.998(1 - \gamma)$. -/
theorem norm_inv_le_of_le_comptau {u γ t thr N ψ : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hu0 : 0 ≤ u) (hku : 100000 * k * u ≤ 1) (hγ1 : γ < 1) (hψ : 0 < ψ) (hN : 0 < N)
    (ht : |t - N⁻¹| ≤ 0.001 * N⁻¹)
    (hthr : |thr - (1 - γ) ^ k * ψ ^ k| ≤ (10 * k + 12) * u * ((1 - γ) ^ k * ψ ^ k))
    (hle : thr ≤ t) : N ≤ ((0.998 * (1 - γ) * ψ)⁻¹) ^ k := by
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hg : 0 < 1 - γ := by linarith
  have hc : 0 < (1 - γ) ^ k * ψ ^ k := by positivity
  have hδ : (10 * k + 12) * u ≤ 0.00016 := by nlinarith
  have h1 : t ≤ 1.001 * N⁻¹ := by linarith [(abs_le.mp ht).2]
  have h2 : (1 - 0.00016) * ((1 - γ) ^ k * ψ ^ k) ≤ thr := by
    nlinarith [(abs_le.mp hthr).1, mul_le_mul_of_nonneg_right hδ hc.le]
  have h3 : 0.998 * ((1 - γ) ^ k * ψ ^ k) ≤ N⁻¹ := by nlinarith
  have h4 : (0.998 : ℝ) ^ k ≤ 0.998 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have h5 : (0.998 * (1 - γ) * ψ) ^ k ≤ N⁻¹ := by
    rw [mul_pow, mul_pow, mul_assoc]
    exact (mul_le_mul_of_nonneg_right h4 hc.le).trans h3
  rw [inv_pow]
  have hξ : 0 < (0.998 * (1 - γ) * ψ) ^ k := pow_pos (mul_pos (mul_pos (by norm_num) hg) hψ) k
  rw [le_inv_comm₀ hN hξ]
  exact h5

/-- **The rounded exceptional radius is in the window of `Exc`**
([BanksGarzaVargasSrivastava2022, line 1 of `Exc`], with the window of the errata N2): on a
machine with the standard model at $10^5k\boldsymbol{u} \le 1$, $k \ge 1$, for $p$ within
$20\boldsymbol{u}$, relatively, of $\psi \ge 0$ and $X \ge 0$, the rounded product
$\tilde R = \mathrm{fl}(2^{1/k}X \cdot p)$ satisfies
$1.998^{1/k}X\psi \le \tilde R \le 2.002^{1/k}X\psi$. -/
theorem excRadius_window {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {k : ℕ} (hk : 0 < k)
    (hku : 100000 * k * u ≤ 1) {X ψ p : ℝ} (hX : 0 ≤ X) (hψ : 0 ≤ ψ)
    (hp : |p - ψ| ≤ 20 * u * ψ) :
    (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * X * ψ ≤ M.mul ((2 : ℝ) ^ ((k : ℝ)⁻¹) * X) p ∧
      M.mul ((2 : ℝ) ^ ((k : ℝ)⁻¹) * X) p ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * X * ψ := by
  have hu0 := hM.roundoff_nonneg
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hm := hM.mul ((2 : ℝ) ^ ((k : ℝ)⁻¹) * X) p
  simp only [id] at hm
  set c := (2 : ℝ) ^ ((k : ℝ)⁻¹) * X
  have hc : 0 ≤ c := by positivity
  have hplo : (1 - 20 * u) * ψ ≤ p := by linarith [(abs_le.mp hp).1]
  have hphi : p ≤ (1 + 20 * u) * ψ := by linarith [(abs_le.mp hp).2]
  have hp0 : 0 ≤ p := le_trans (by nlinarith) hplo
  rw [abs_of_nonneg (mul_nonneg hc hp0)] at hm
  have hku' : (k : ℝ) * u ≤ 0.00001 := by nlinarith
  have hu1 : u ≤ 0.00001 := by nlinarith
  -- the factors $0.999^{1/k} \le 1 - 0.001/k$ and $1 + 0.0005/k \le 1.001^{1/k}$
  have hlo : (0.999 : ℝ) ^ ((k : ℝ)⁻¹) ≤ 1 - 0.001 / k := by
    have := rpow_one_add_le_one_add_mul_self (s := -0.001) (by norm_num)
      (p := (k : ℝ)⁻¹) (by positivity) (inv_le_one_of_one_le₀ hk1)
    rw [show (1 : ℝ) + -0.001 = 0.999 by norm_num] at this
    rw [div_eq_inv_mul]; linarith
  have hhi : 1 + 0.0005 / (k : ℝ) ≤ (1.001 : ℝ) ^ ((k : ℝ)⁻¹) := by
    have hb := one_add_pow_le_one_add_two_mul (u := 0.0005 / (k : ℝ)) (by positivity) (N := k)
      (by rw [mul_div_cancel₀ _ hk0.ne']; norm_num)
    rw [mul_assoc, mul_div_cancel₀ _ hk0.ne'] at hb
    have := Real.rpow_le_rpow (by positivity) hb (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by positivity) hk.ne', show (1 : ℝ) + 2 * 0.0005 = 1.001 by
      norm_num] at this
  have e1 : (1.998 : ℝ) ^ ((k : ℝ)⁻¹) = (0.999 : ℝ) ^ ((k : ℝ)⁻¹) * 2 ^ ((k : ℝ)⁻¹) := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have e2 : (2.002 : ℝ) ^ ((k : ℝ)⁻¹) = (1.001 : ℝ) ^ ((k : ℝ)⁻¹) * 2 ^ ((k : ℝ)⁻¹) := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hcψ : 0 ≤ c * ψ := mul_nonneg hc hψ
  have hdk : (0.001 : ℝ) / k * 1 ≥ 21 * u := by
    rw [ge_iff_le, mul_one, le_div_iff₀ hk0]; nlinarith
  have hdk' : (0.0005 : ℝ) / k ≥ 22 * u := by
    rw [ge_iff_le, le_div_iff₀ hk0]; nlinarith
  constructor
  · rw [e1, show (0.999 : ℝ) ^ ((k : ℝ)⁻¹) * 2 ^ ((k : ℝ)⁻¹) * X * ψ =
      (0.999 : ℝ) ^ ((k : ℝ)⁻¹) * (c * ψ) by ring]
    have h1 : (1 - u) * (1 - 20 * u) * (c * ψ) ≤ M.mul c p := by
      have : (1 - u) * (c * ((1 - 20 * u) * ψ)) ≤ (1 - u) * (c * p) := by
        have : 0 ≤ 1 - u := by linarith
        gcongr
      nlinarith [(abs_le.mp hm).1]
    have h2 : 1 - 0.001 / (k : ℝ) ≤ (1 - u) * (1 - 20 * u) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (hlo.trans h2) hcψ]
  · rw [e2, show (1.001 : ℝ) ^ ((k : ℝ)⁻¹) * 2 ^ ((k : ℝ)⁻¹) * X * ψ =
      (1.001 : ℝ) ^ ((k : ℝ)⁻¹) * (c * ψ) by ring]
    have h1 : M.mul c p ≤ (1 + u) * (1 + 20 * u) * (c * ψ) := by
      have : (1 + u) * (c * p) ≤ (1 + u) * (c * ((1 + 20 * u) * ψ)) := by gcongr
      nlinarith [(abs_le.mp hm).2]
    have h2 : (1 + u) * (1 + 20 * u) ≤ 1 + 0.0005 / (k : ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (h2.trans hhi) hcψ]

end NLAlib.ShiftedQR
