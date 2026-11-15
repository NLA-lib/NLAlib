/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedRegularizeTrial

/-!
# The trials of the rounded shifting strategy

The shifting strategy $\mathrm{Sh}_{k,B}$ of [BanksGarzaVargasSrivastava2022, §5] tries the
exceptional shifts in turn: a rounded degree $k$ step with the shift repeated, on a copy, accepted
when one of its bottom $k$ subdiagonal entries passes the scan or its rounded potential is below
a rounded multiple of the potential of the input. A shift $s$ with
$\tau_{(z - s)^k}(\mathbf{H}) \le (1 - \gamma)\psi_k(\mathbf{H})$ is accepted: its rounded step
either decouples or contracts the potential by $1.0011(1 - \gamma)$
([BanksGarzaVargasSrivastava2022, Lemma 5.2], corrected as in the errata G12).

## Main definitions

* `NLAlib.ShiftedQR.shTrial`, `NLAlib.ShiftedQR.shTrials`: the programs.
* `NLAlib.ShiftedQR.ShTrialDone`: an accepted trial.

## Main results

* `NLAlib.IsStableQRChain.exists_norm_subdiag_lt_or_potential_pow_mul_le`: a rounded step with
  one repeated shift decouples, or its potential is at most $1.0011\,\tau$.
* `NLAlib.ShiftedQR.potential_contract_of_lt`, `NLAlib.ShiftedQR.lt_of_potential_contract`: the
  potential test, from rounded potentials.
* `NLAlib.ShiftedQR.shTrials_writes`: the trials on any scalar machine.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The potential is a function of the moduli of the subdiagonal entries. -/
theorem hessenbergPotential_congr_norm {k : ℕ} {H₁ H₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : ∀ i : Fin n, ‖H₁ i.succ i.castSucc‖ = ‖H₂ i.succ i.castSucc‖) :
    hessenbergPotential k H₁ = hessenbergPotential k H₂ := by
  unfold hessenbergPotential
  rw [Finset.prod_congr rfl fun i _ => h i]

/-- A diagonal unitary similarity keeps the moduli of the subdiagonal entries. -/
theorem norm_conjTranspose_diagonal_mul_mul_diagonal_apply {D : Fin (n + 1) → ℂ}
    (hD : ∀ i, ‖D i‖ = 1) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i j : Fin (n + 1)) :
    ‖((Matrix.diagonal D)ᴴ * X * Matrix.diagonal D) i j‖ = ‖X i j‖ := by
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply, norm_mul, norm_star, hD, one_mul, mul_one]

/-- **A rounded step with one repeated shift decouples or contracts like the exact step**
([BanksGarzaVargasSrivastava2022, Lemma 5.2], with the case split over the bottom $k$
subdiagonal entries of the errata G12): let $\mathbf{H} \ne 0$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le B$, $\|\mathbf{H}\|_2 \le \Sigma$, $1 \le k \le n$, $\omega > 0$, and $r$
a shift with $\lvert r\rvert \le C\|\mathbf{H}\|_2$ ($C \ge 0$) at distance at least $d > 0$ from
every $e_i$. If $\widehat{\mathbf{H}}$ is the result of a backward-stable chain of $k$ steps with
the shift $r$ and relative error $x \ge 0$,
$$x \le (16B)^{-1}\Bigl(\frac{d}{(2 + 2C)\Sigma}\Bigr)^k, \qquad
(66 + 2C)B\Sigma\Bigl(\frac{(2 + 2C)\Sigma}{d}\Bigr)^k\sqrt{n + 1}\,x \le 0.001\,\omega,$$
then one of the last $k$ subdiagonal entries of $\widehat{\mathbf{H}}$ has modulus below
$\omega$, or
$\psi_k(\widehat{\mathbf{H}})^k\,\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\| \le 1.0011^k$,
i.e. $\psi_k(\widehat{\mathbf{H}}) \le 1.0011\,\tau_{(z - r)^k}(\mathbf{H})$. -/
theorem IsStableQRChain.exists_norm_subdiag_lt_or_potential_pow_mul_le {x C B S d ω : ℝ}
    {k : ℕ} {H H' V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {r : ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H (List.replicate k r) H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hd : 0 < d) (hω : 0 < ω) (hk : 0 < k) (hkn : k ≤ n) (hH0 : H ≠ 0)
    (hH : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hS : specNorm H ≤ S) (hr : ‖r‖ ≤ C * specNorm H)
    (hdist : ∀ i, d ≤ ‖e i - r‖)
    (hxu : x ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) * x ≤ 0.001 * ω) :
    (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ < ω) ∨
      hessenbergPotential k H' ^ k * ‖WithLp.toLp 2
        ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖ ≤ 1.0011 ^ k := by
  have hHp : 0 < specNorm H :=
    (specNorm_nonneg H).lt_of_ne fun h0 => hH0 (specNorm_eq_zero_iff.mp h0.symm)
  have hS0 : 0 < S := hHp.trans_le hS
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num)
    ((one_le_pseudoConditionNumber hV.ne_zero).trans hκ)
  have hne : ∀ i, e i ≠ r := fun i he => by
    have := hdist i; rw [he, sub_self, norm_zero] at this; linarith
  set X := multiShiftedQRStep H (List.replicate k r)
  have hpot := hH.hessenbergPotential_multiShiftedQRStep_replicate_pow_mul_le hk hkn
    (det_sub_smul_one_ne_zero_of_forall_ne hV hHV (fun i => hne i))
  rw [aeval_shiftPoly_replicate, ← Matrix.inv_pow']
  have hs : ∀ s ∈ List.replicate k r, ‖s‖ ≤ C * specNorm H := fun s hs => by
    rw [List.eq_of_mem_replicate hs]; exact hr
  have hdist' : ∀ s ∈ List.replicate k r, ∀ i, d ≤ ‖e i - s‖ := fun s hs i => by
    rw [List.eq_of_mem_replicate hs]; exact hdist i
  obtain ⟨D, hD, hF⟩ := h.exists_frobNorm_conj_sub_le hx hC hd hH0 hH hV hHV hκ hs hdist'
    (by rw [List.length_replicate]; exact hxu.trans (by gcongr))
  rw [List.length_replicate] at hF
  set H₁ := (Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D
  have hF' : frobNorm (H₁ - X) ≤ 0.001 * ω := by
    refine hF.trans (le_trans ?_ hbound)
    gcongr
  have hn : ∀ i : Fin n, ‖H₁ i.succ i.castSucc‖ = ‖H' i.succ i.castSucc‖ := fun i =>
    norm_conjTranspose_diagonal_mul_mul_diagonal_apply hD H' _ _
  rcases potential_le_or_exists_lt_of_sub_le hk hω (H₁ := H₁) (H₂ := X) fun i _ => by
      have := norm_apply_le_frobNorm (H₁ - X) i.succ i.castSucc
      rw [Matrix.sub_apply] at this
      linarith with ⟨i, hik, hi⟩ | hle
  · exact Or.inl ⟨i, hik, by rwa [← hn i]⟩
  · right
    rw [hessenbergPotential_congr_norm (k := k) hn] at hle
    have hX0 := hessenbergPotential_nonneg k X
    have hpow : hessenbergPotential k H' ^ k ≤ 1.0011 ^ k * hessenbergPotential k X ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (hessenbergPotential_nonneg k H') hle k
    calc _ ≤ 1.0011 ^ k * hessenbergPotential k X ^ k * ‖WithLp.toLp 2
          (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k) (Fin.last n))‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ 1.0011 ^ k * 1 := by rw [mul_assoc]; gcongr
      _ = _ := mul_one _

end NLAlib

namespace NLAlib.ShiftedQR

/-- **The potential test accepts only a contraction**: if the rounded potentials $p_T$, $p_H$ of
$\widehat{\mathbf{H}}$ and $\mathbf{H}$ are within $20\boldsymbol{u}$, relatively, of
$\psi_T, \psi_H \ge 0$, the threshold $P$ is within $\boldsymbol{u}$, relatively, of
$1.0015(1 - \gamma)p_H$, $\gamma \le 1$, $2 \cdot 10^5\boldsymbol{u} \le 1$ and $p_T < P$, then
$\psi_T \le 1.002(1 - \gamma)\psi_H$. -/
theorem potential_contract_of_lt {u ψT ψH pT pH P γ : ℝ} (hu0 : 0 ≤ u)
    (hu : 200000 * u ≤ 1) (hγ1 : γ ≤ 1) (hψT : 0 ≤ ψT) (hψH : 0 ≤ ψH)
    (hpT : |pT - ψT| ≤ 20 * u * ψT) (hpH : |pH - ψH| ≤ 20 * u * ψH)
    (hP : |P - 1.0015 * (1 - γ) * pH| ≤ u * |1.0015 * (1 - γ) * pH|) (hlt : pT < P) :
    ψT ≤ 1.002 * (1 - γ) * ψH := by
  have hg : 0 ≤ 1 - γ := by linarith
  have hpH0 : 0 ≤ pH := by nlinarith [(abs_le.mp hpH).1]
  have hc : 0 ≤ 1.0015 * (1 - γ) * pH := by positivity
  rw [abs_of_nonneg hc] at hP
  have h1 : (1 - 20 * u) * ψT ≤ pT := by nlinarith [(abs_le.mp hpT).1]
  have h2 : P ≤ (1 + u) * (1.0015 * (1 - γ) * pH) := by linarith [(abs_le.mp hP).2]
  have h3 : pH ≤ (1 + 20 * u) * ψH := by linarith [(abs_le.mp hpH).2]
  have h4 : (1 + u) * (1.0015 * (1 - γ) * pH) ≤
      (1 + u) * (1.0015 * (1 - γ) * ((1 + 20 * u) * ψH)) := by gcongr
  have h5 : (1 + u) * (1.0015 * ((1 + 20 * u))) ≤ 1.002 * (1 - 20 * u) := by nlinarith
  have h6 : (1 - 20 * u) * ψT ≤ (1 - 20 * u) * (1.002 * (1 - γ) * ψH) := by
    have := mul_le_mul_of_nonneg_right h5 (mul_nonneg hg hψH)
    nlinarith
  exact le_of_mul_le_mul_left h6 (by linarith)

/-- **The potential test accepts a contraction by $1.0011(1 - \gamma)$**: under the
hypotheses of `NLAlib.ShiftedQR.potential_contract_of_lt` without $p_T < P$, if
$\psi_T \le 1.0011(1 - \gamma)\psi_H$, $\gamma < 1$ and $\psi_H > 0$, then $p_T < P$. -/
theorem lt_of_potential_contract {u ψT ψH pT pH P γ : ℝ} (hu0 : 0 ≤ u)
    (hu : 200000 * u ≤ 1) (hγ1 : γ < 1) (hψH : 0 < ψH)
    (hpT : |pT - ψT| ≤ 20 * u * ψT) (hpH : |pH - ψH| ≤ 20 * u * ψH)
    (hP : |P - 1.0015 * (1 - γ) * pH| ≤ u * |1.0015 * (1 - γ) * pH|)
    (hle : ψT ≤ 1.0011 * (1 - γ) * ψH) : pT < P := by
  have hg : 0 < 1 - γ := by linarith
  have hpH0 : 0 ≤ pH := by nlinarith [(abs_le.mp hpH).1]
  have hc : 0 ≤ 1.0015 * (1 - γ) * pH := by positivity
  rw [abs_of_nonneg hc] at hP
  have h1 : pT ≤ (1 + 20 * u) * ψT := by linarith [(abs_le.mp hpT).2]
  have h2 : (1 - u) * (1.0015 * (1 - γ) * pH) ≤ P := by linarith [(abs_le.mp hP).1]
  have h3 : (1 - 20 * u) * ψH ≤ pH := by linarith [(abs_le.mp hpH).1]
  have h4 : (1 + 20 * u) * ψT ≤ (1 + 20 * u) * (1.0011 * (1 - γ) * ψH) := by gcongr
  have h5 : (1 - u) * (1.0015 * (1 - γ) * ((1 - 20 * u) * ψH)) ≤
      (1 - u) * (1.0015 * (1 - γ) * pH) := by
    have : 0 ≤ 1 - u := by linarith
    gcongr
  have hpos : 0 < (1 - γ) * ψH := mul_pos hg hψH
  have h6 : (1 + 20 * u) * 1.0011 < (1 - u) * 1.0015 * (1 - 20 * u) := by nlinarith
  have h7 : (1 + 20 * u) * (1.0011 * (1 - γ) * ψH) <
      (1 - u) * (1.0015 * (1 - γ) * ((1 - 20 * u) * ψH)) := by
    have := mul_lt_mul_of_pos_right h6 hpos
    nlinarith
  linarith

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The potential test of a trial: the rounded potential of the step `T` (`k = 2^q`) into `P2`;
if it is below the threshold word `Pt`, accept the step (`NLAlib.ShiftedQR.trialAccept`). The
interface is `[N, k, q] (Pt, T, P2) → (A, G, Fl)`. -/
def shPotentialAccept : Impl O Q := opsImpl% [N, k, q] (Pt, T, P2) → (A, G, Fl) {
  run roundedPotential.body [N, k, q] (T, P2);
  if (Has.inj CmpTst.lt) [] (P2, Pt) {
    run trialAccept.body [N] (T, A, G, Fl)
  } else {
    skip
  }
}

/-- **One trial of `Sh`**: if the search word `G` is positive, run `NLAlib.ShiftedQR.trialStep`
with the shift `S`; accept the step if its scan found a small entry (`Rg[3]` positive), else
run the potential test `NLAlib.ShiftedQR.shPotentialAccept` against `Pt`. The interface is
`[N, k, q] (A, S, Thr, Pt, T, SR, Ds, Rg, P2) → (A, G, Fl)`. -/
def shTrial : Impl O Q :=
  opsImpl% [N, k, q] (A, S, Thr, Pt, T, SR, Ds, Rg, P2) → (A, G, Fl) {
    if (Has.inj CmpTst.isPos) [] (G) {
      run trialStep.body [N, k] (A, S, Thr, T, SR, Ds, Rg);
      if (Has.inj CmpTst.isPos) [] (Rg[3]) {
        run trialAccept.body [N] (T, A, G, Fl)
      } else {
        run shPotentialAccept.body [N, k, q] (Pt, T, P2, A, G, Fl)
      }
    } else {
      skip
    }
  }

/-- The $n_0$ trials of `Sh`, with the shifts `S[2j]` in turn. The interface is
`[N, k, q, n0] (A, S, Thr, Pt, T, SR, Ds, Rg, P2) → (A, G, Fl)`. -/
def shTrials : Impl O Q :=
  opsImpl% [N, k, q, n0] (A, S, Thr, Pt, T, SR, Ds, Rg, P2) → (A, G, Fl) {
    for j < n0 {
      run shTrial.body [N, k, q] (A, S[2 * j], Thr, Pt, T, SR, Ds, Rg, P2, A, G, Fl)
    }
  }

end Program

end NLAlib.ShiftedQR
