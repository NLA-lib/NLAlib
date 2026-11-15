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

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

/-- The threshold word of the `comptau` test: the stored word `C` times the rounded square root
of the rounded bottom product of the order-$n$ matrix `A` (`NLAlib.ShiftedQR.optimalThresholdWord`).
The interface is `[n, k] (A, C) → (P)`. -/
def shThreshold : Impl O Q := opsImpl% [n, k] (A, C) → (P) {
  run subdiagProduct.body [n, k] (A, P);
  call (Has.inj ScalarOp.sqrt) [] (P) → (P);
  call (Has.inj ScalarOp.mul) [] (C, P) → (P)
}

/-- The computation of the `comptau` test of `Sh`: the rounded degree $k$ step with the shift
`Z` repeated on a copy `T` of the order-$N$ matrix `A` (`SR` the repeated shifts), its `comptau`
into `P0`, and the threshold with the word `Cg` into `P1`. The interface is
`[N, k] (A, Z, Cg) → (T, SR, P0, P1)`. -/
def shTestStep : Impl O Q := opsImpl% [N, k] (A, Z, Cg) → (T, SR, P0, P1) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (N * N)] (A, T);
  run replicatePair.body [k] (Z, SR);
  run (stepComptau (O := O) (Q := Q)).body [N, k] (T, SR, T, P0);
  run shThreshold.body [N, k] (A, Cg, P1)
}

/-- The exceptional branch of `Sh`: the flag `Fl` is $2$ (no step yet) and the search word `Gw`
is $1$; the threshold $\mathrm{fl}(c_p\tilde\psi)$ of the potential test into `Pt` and the
radius $\mathrm{fl}(c_r\tilde\psi)$ into `Rt` (which held $\tilde\psi$); the exceptional shifts
around the centre `Z` (`NLAlib.ShiftedQR.excShifts`, with the translate factor `Cw` and the
net `G`) into `Ss`; and the trials (`NLAlib.ShiftedQR.shTrials`). The interface is
`[N, k, q, n0] (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, T, SR, Ds, Rg, P2, Ss) → (A, Gw, Fl)`. -/
def shExc : Impl O Q :=
  opsImpl% [N, k, q, n0] (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, T, SR, Ds, Rg, P2, Ss) →
      (A, Gw, Fl) {
    call (Has.inj (ScalarOp.lit 2)) [] () → (Fl);
    call (Has.inj (ScalarOp.lit 1)) [] () → (Gw);
    call (Has.inj ScalarOp.mul) [] (Cp, Rt) → (Pt);
    call (Has.inj ScalarOp.mul) [] (Cr, Rt) → (Rt);
    run (excShifts (O := O) (Q := Q)).body [n0] (Z, Rt, Cw, G, Ss);
    run shTrials.body [N, k, q, n0] (A, Ss, Thr, Pt, T, SR, Ds, Rg, P2, A, Gw, Fl)
  }

/-- `Sh` with caller-owned scratch: the rounded potential $\tilde\psi$ of `A` into `Rt`, `Find`
(`NLAlib.ShiftedQR.findRounded` with `NLAlib.ShiftedQR.comptauHalf`) over the $k = 2^m$ shifts
`SS` into `Z`, the `comptau` test (`NLAlib.ShiftedQR.shTestStep`, word `Cg`); below the
threshold the step is accepted (`NLAlib.ShiftedQR.trialAccept`, flag $1$), otherwise the
exceptional branch runs (`NLAlib.ShiftedQR.shExc`). The interface is
`[N, m, k, n0] (A, SS, Cg, Cr, Cw, Cp, G, Thr, Z, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss, Gw) →
(A, Fl)`. -/
def shStepWithScratch : Impl O Q :=
  opsImpl% [N, m, k, n0]
      (A, SS, Cg, Cr, Cw, Cp, G, Thr, Z, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss, Gw) → (A, Fl) {
    run roundedPotential.body [N, k, m] (A, Rt);
    run (findRounded (comptauHalf (O := O) (Q := Q))).body [N, m, k] (A, SS, Z);
    run shTestStep.body [N, k] (A, Z, Cg, T, SR, P0, P1);
    if (Has.inj CmpTst.lt) [] (P0, P1) {
      run trialAccept.body [N] (T, A, Gw, Fl)
    } else {
      run shExc.body [N, k, m, n0]
        (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, T, SR, Ds, Rg, P2, Ss, A, Gw, Fl)
    }
  }

/-- **The shifting strategy `Sh`** ([BanksGarzaVargasSrivastava2022, Lemma 5.4], with the fail
word of the errata N11): from the order-$N$ matrix `A` and $k = 2^m$ optimal shifts `SS`, with
the words `Cg` ($(1 - \gamma)^k$), `Cr` (the radius factor $2^{1/k}\theta\alpha B^{1/k}$),
`Cw` ($\varepsilon/2$), `Cp` ($1.0015(1 - \gamma)$), the net `G` of $n_0$ points and the scan
threshold `Thr`, store a step at `A` and set the flag `Fl` to $1$, or set it to $2$ if no trial
succeeded. All scratch is scoped. The interface is `[N, m, k, n0] (A, SS, Cg, Cr, Cw, Cp, G, Thr)
→ (A, Fl)`. -/
def shStep : Impl O Q := opsImpl% [N, m, k, n0] (A, SS, Cg, Cr, Cw, Cp, G, Thr) → (A, Fl) {
  let Z ← alloc 2;
  let Rt ← alloc 1;
  let Pt ← alloc 1;
  let P0 ← alloc 1;
  let P1 ← alloc 1;
  let T ← alloc (2 * (N * N));
  let SR ← alloc (2 * k);
  let Ds ← alloc (2 * k);
  let Rg ← alloc 5;
  let P2 ← alloc 1;
  let Ss ← alloc (2 * n0);
  let Gw ← alloc 1;
  run shStepWithScratch.body [N, m, k, n0]
    (A, SS, Cg, Cr, Cw, Cp, G, Thr, Z, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss, Gw, A, Fl)
}

end Program

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Test

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

omit [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The threshold of the `comptau` test on any scalar machine stores
`NLAlib.ShiftedQR.optimalThresholdWord` and writes only its output word, which is apart from the
matrix and the word `C`. -/
theorem shThreshold_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {τ : Tape ℝ}
    {m : Mem ℝ} {n k : ℕ} {a c p : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {cv : ℝ}
    (hk : k ≤ n) (hH : HoldsMatrix a H m.store) (hc : m.store.get c.1 c.2 = some cv)
    (hp : p.2 < m.store.len p.1)
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock p.1 p.2 1))
    (hcp : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ (shThreshold (O := O) (Q := Q)).body (Env.frame [n + 1, k] [a, c, p])
      (Store.inBlock p.1 p.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get p.1 p.2 = some (optimalThresholdWord M H k cv))
      m := by
  have hal := Store.lt_length_of_get (hH.get_re 0 0)
  have hpl := Store.lt_length_of_lt_len hp
  unfold shThreshold
  refine (subdiagProduct_writes_word (τ := τ) hS hk hH hp hap).frame_seq_le rfl rfl
    (by simp [Mem.Live, hal, hpl]) le_rfl ?_
  intro m₁ hfr₁ ⟨hp₁, hP₁⟩
  have hc₁ := hfr₁.keep (Store.readsOnly_get _ _ _) hcp.symm hc
  refine (writes_call_un (hS .sqrt) (x := p) (z := p) rfl rfl trivial hP₁ rfl
    (Store.lt_len_of_get hP₁)).seq_le le_rfl ?_
  intro m₂ hfr₂ ⟨hp₂, hR₂⟩
  have hc₂ := hfr₂.keep (Store.readsOnly_get _ _ _) hcp.symm hc₁
  refine (writes_call_bin (hS .mul) (x := c) (y := p) (z := p) rfl rfl trivial hc₂ hR₂ rfl
    (fun _ => ⟨by simp [Mem.Live, Store.lt_length_of_get hc₂, Store.lt_length_of_get hR₂],
      Store.lt_len_of_get hR₂⟩)).mono le_rfl ?_
  intro m₃ _ ⟨hp₃, hT₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hT₃⟩

omit [Has IndexOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **The computation of the `comptau` test** on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$ and $30000(k + 1)\boldsymbol{u} \le 1$, with exact
comparisons: let $\mathbf{H} \ne 0$ of order $n + 1$ be upper Hessenberg at `A`,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le \kappa$, the shift $r$ at `Z` with $\lvert r\rvert \le C\|\mathbf{H}\|_2$
($C \ge 0$) at distance at least $d > 0$ from every $e_i$, the word $c$ at `Cg`, $1 \le k \le n$,
and
$300(n+1)^2\boldsymbol{u} \le (8004\kappa)^{-1}(d/((2 + 2C)\|\mathbf{H}\|_2))^k$. Then
`NLAlib.ShiftedQR.shTestStep` writes only its four outputs, stores at `T` a backward-stable degree
$k$ step $\widehat{\mathbf{H}}$ with the shift $r$ repeated (relative error
$300(n+1)^2\boldsymbol{u}$), upper Hessenberg, at `P0` a value within $0.001$, relatively, of
$\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\|^{-1}$, and at `P1` the threshold
`NLAlib.ShiftedQR.optimalThresholdWord`. -/
theorem shTestStep_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hCmp : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ}
    {C κ d : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {r : ℂ}
    {a z cg t sr p0 p1 : ℕ × ℕ} {cv : ℝ} (hH : IsUpperHessenberg H) (hH0 : H ≠ 0)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ κ)
    (hC : 0 ≤ C) (hd : 0 < d) (hr : ‖r‖ ≤ C * specNorm H) (hdist : ∀ i, d ≤ ‖e i - r‖)
    (hk0 : 0 < k) (hk : k ≤ n) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hu : 30000 * (k + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ k)
    (hA : HoldsMatrix a H m.store) (hz : m.store.readBlock z.1 z.2 2 = some [r.re, r.im])
    (hcg : m.store.get cg.1 cg.2 = some cv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrp0 : p0.2 < m.store.len p0.1)
    (hrp1 : p1.2 < m.store.len p1.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock p0.1 p0.2 1 ⊔ Store.inBlock p1.1 p1.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock z.1 z.2 2 ⊔
        Store.inBlock cg.1 cg.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htp : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p0.1 p0.2 1))
    (hp1 : Fp.Disj (Store.inBlock p1.1 p1.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock p0.1 p0.2 1)) :
    Writes .total I τ (shTestStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, z, cg, t, sr, p0, p1])
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock p0.1 p0.2 1 ⊔ Store.inBlock p1.1 p1.2 1)
      (fun m' => m'.pos = m.pos ∧ ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs ∧
          IsUpperHessenberg H' ∧ HoldsMatrix t H' m'.store ∧
          (∃ tc : ℝ, m'.store.get p0.1 p0.2 = some tc ∧
            |tc - ‖WithLp.toLp 2 ((Polynomial.aeval H
              (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖⁻¹| ≤ 0.001 * ‖WithLp.toLp 2
                ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖⁻¹) ∧
          m'.store.get p1.1 p1.2 = some (optimalThresholdWord M H k cv)) m := by
  have hal := Store.lt_length_of_get (hA.get_re 0 0)
  have hzl := Store.lt_length_of_get (Store.get_of_readBlock hz (j := 0) (by norm_num) 0)
  have hcl := Store.lt_length_of_get hcg
  have htl := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith)
  have hsl := Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega)
  have hp0l := Store.lt_length_of_lt_len hrp0
  have hp1l := Store.lt_length_of_lt_len hrp1
  unfold shTestStep
  refine (copyMatrix_writes (τ := τ) hS hA hrt (hW.symm.mono (by fp_sub) (by fp_sub))).frame_seq_le
    rfl rfl (by simp [Mem.Live, hal, htl]) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨hp₁, hT₁⟩
  have hk₁ : ∀ {F : Fp}, F ≤ Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock p0.1 p0.2 1 ⊔ Store.inBlock p1.1 p1.2 1 →
      Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock z.1 z.2 2 ⊔
        Store.inBlock cg.1 cg.2 1) := fun h => hW.mono h le_rfl
  have hz₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) ((hk₁ (by fp_sub)).mono le_rfl
    (by fp_sub)) hz
  have hrep := replicatePair_writes (τ := τ) (sr := sr) (k := k) hS hz₁
    (by rw [hfr₁.len_eq]; exact hrsr) ((hk₁ (by fp_sub)).symm.mono (by fp_sub) le_rfl)
  refine hrep.frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hzl, hsl]) (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨hp₂, hSR₂⟩
  have hT₂ := hT₁.of_eqOff hfr₂ hts.symm
  have hL₂ : m₂.store.length = m.store.length := by rw [hfr₂.length_eq, hfr₁.length_eq]
  have hst := stepComptau_writes (τ := τ) (m := m₂) (a := t) (s := sr) (p := p0)
    (ss := List.replicate k r) hS hM hCmp hH hH0 hV hHV hκ hC hd
    (fun s hs => by rw [List.eq_of_mem_replicate hs]; exact hr)
    (fun s hs => by rw [List.eq_of_mem_replicate hs]; exact hdist) hnu
    (by rw [List.length_replicate]; exact hu) (by rw [List.length_replicate]; exact hxu)
    (by simp [Mem.Live, hL₂, htl, hsl, hp0l]) hT₂ hSR₂
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hrp0) (by simpa using hts) htp
  rw [List.length_replicate] at hst
  refine hst.frame_seq_le rfl rfl (by simp [Mem.Live, hL₂, htl, hsl, hp0l]) (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨hp₃, H', Rs, hch, hH', hT₃, tc, htc, hb⟩
  have hL₃ : m₃.store.length = m.store.length := by rw [hfr₃.length_eq, hL₂]
  have hkeep : ∀ {F : Fp}, F ≤ Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock p0.1 p0.2 1 → ∀ {b : ℕ × ℕ} {l : ℕ}
      {xs : List ℝ}, Store.inBlock b.1 b.2 l ≤ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock z.1 z.2 2 ⊔ Store.inBlock cg.1 cg.2 1 →
      m.store.readBlock b.1 b.2 l = some xs → ∀ μ : Mem ℝ, m.store.EqOff F μ.store →
        μ.store.readBlock b.1 b.2 l = some xs := fun hF _ _ _ hb hx μ hfr =>
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hW.mono (hF.trans le_sup_left) hb) hx
  have hfr₁₃ : m.store.EqOff (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock p0.1 p0.2 1) m₃.store :=
    ((hfr₁.mono (by fp_sub)).trans (hfr₂.mono (by fp_sub))).trans (hfr₃.mono (by fp_sub))
  have hA₃ : HoldsMatrix a H m₃.store := hkeep le_rfl (by fp_sub) hA m₃ hfr₁₃
  have hcg₃ := hfr₁₃.keep (Store.readsOnly_get _ _ _) (hW.mono le_sup_left (by fp_sub)) hcg
  have hth := shThreshold_writes (τ := τ) (m := m₃) (a := a) (c := cg) (p := p1) (k := k) hS hk
    hA₃ hcg₃ (by rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; exact hrp1)
    (hW.symm.mono (by fp_sub) (by fp_sub)) (hW.symm.mono (by fp_sub) (by fp_sub))
  refine (hth.in_frame rfl rfl (by simp [Mem.Live, hL₃, hal, hcl, hp1l])).mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨hp₄, hP₄⟩
  refine ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), H', Rs, hch, hH', hT₃.of_eqOff hfr₄
    (hp1.mono le_rfl le_sup_left), ⟨tc, hfr₄.keep (Store.readsOnly_get _ _ _)
      (hp1.mono le_rfl le_sup_right) htc, hb⟩, hP₄⟩

end Test

end NLAlib.ShiftedQR
