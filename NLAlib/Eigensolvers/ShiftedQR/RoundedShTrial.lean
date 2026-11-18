/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedRegularizeTrial
public import NLAlib.Matrix.QRIteration.StableStepForward

/-!
# The trials of the rounded shifting strategy

The shifting strategy $\mathrm{Sh}_{k,B}$ of [BanksGarzaVargasSrivastava2022, §5] tries the
exceptional shifts in turn: a rounded degree $k$ step with the shift repeated, on a copy, accepted
when one of its bottom $k$ subdiagonal entries passes the scan or its rounded potential is below
a rounded multiple of the potential of the input. A shift $s$ with
$\tau_{(z - s)^k}(\mathbf{H}) \le (1 - \gamma)\psi_k(\mathbf{H})$ is accepted: its rounded step
either decouples or contracts the potential by $1.0011(1 - \gamma)$
([BanksGarzaVargasSrivastava2022, Lemma 5.2], with the product and the case split taken over
the bottom $k$ subdiagonal entries, where the paper takes all $n - 1$).

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
([BanksGarzaVargasSrivastava2022, Lemma 5.2]; the paper takes the product and the case split
over all $n - 1$ subdiagonal entries, here over the bottom $k$, which is the decoupling the
deflation needs): let $\mathbf{H} \ne 0$ be upper Hessenberg,
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

/-- The potential test accepts only a contraction: if the rounded potentials $p_T$, $p_H$ of
$\widehat{\mathbf{H}}$ and $\mathbf{H}$ are within $20\boldsymbol{u}$, relatively, of
$\psi_T, \psi_H \ge 0$, the threshold $P$ is within $\boldsymbol{u}$, relatively, of
$1.0015(1 - \gamma)p_H$, $\gamma \le 1$, $2 \cdot 10^5\boldsymbol{u} \le 1$ and $p_T < P$, then
$\psi_T \le 1.002(1 - \gamma)\psi_H$. -/
theorem potential_contract_of_lt {u ψT ψH pT pH P γ : ℝ} (hu0 : 0 ≤ u)
    (hu : 200000 * u ≤ 1) (hγ1 : γ ≤ 1) (hψH : 0 ≤ ψH)
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

/-- The potential test accepts a contraction by $1.0011(1 - \gamma)$: if the rounded
potentials $p_T$, $p_H$ are within $20\boldsymbol{u}$, relatively, of $\psi_T$ and $\psi_H > 0$,
the threshold $P$ is within $\boldsymbol{u}$, relatively, of $1.0015(1 - \gamma)p_H$,
$\gamma < 1$, $\boldsymbol{u} \ge 0$, $2 \cdot 10^5\boldsymbol{u} \le 1$ and
$\psi_T \le 1.0011(1 - \gamma)\psi_H$, then $p_T < P$. -/
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
if it is below the threshold word `Pt`, accept the step (`NLAlib.ShiftedQR.trialAccept`, which
validates slot $j$ of the log `Lg`). The interface is `[N, k, q, w, j] (Pt, T, P2) → (A, G, Fl,
Lg)`.
-/
def shPotentialAccept : Impl O Q := opsImpl% [N, k, q, w, j] (Pt, T, P2) → (A, G, Fl, Lg) {
  run roundedPotential.body [N, k, q] (T, P2);
  if (Has.inj CmpTst.lt) [] (P2, Pt) {
    run trialAccept.body [N, w, j] (T, A, G, Fl, Lg)
  } else {
    skip
  }
}

/-- **One trial of `Sh`**: if the search word `G` is positive, run `NLAlib.ShiftedQR.trialStep`
with the shift `S`; accept the step if its scan found a small entry (`Rg[3]` positive), else
run the potential test `NLAlib.ShiftedQR.shPotentialAccept` against `Pt`. The step records its
rotations in slot $j$ of the log `Lg`, validated on acceptance. The interface is
`[N, k, q, w, j] (A, S, Thr, Pt, T, SR, Ds, Rg, P2) → (A, G, Fl, Lg)`. -/
def shTrial : Impl O Q :=
  opsImpl% [N, k, q, w, j] (A, S, Thr, Pt, T, SR, Ds, Rg, P2) → (A, G, Fl, Lg) {
    if (Has.inj CmpTst.isPos) [] (G) {
      run trialStep.body [N, k, w, j] (A, S, Thr, T, SR, Ds, Rg, Lg);
      if (Has.inj CmpTst.isPos) [] (Rg[3]) {
        run trialAccept.body [N, w, j] (T, A, G, Fl, Lg)
      } else {
        run shPotentialAccept.body [N, k, q, w, j] (Pt, T, P2, A, G, Fl, Lg)
      }
    } else {
      skip
    }
  }

/-- The $n_0$ trials of `Sh`, with the shifts `S[2t]` in turn, trial $t$ at the slot $j_0 + t$ of
the log `Lg`. The interface is `[N, k, q, n0, w, j0] (A, S, Thr, Pt, T, SR, Ds, Rg, P2) → (A, G,
Fl, Lg)`.
-/
def shTrials : Impl O Q :=
  opsImpl% [N, k, q, n0, w, j0] (A, S, Thr, Pt, T, SR, Ds, Rg, P2) → (A, G, Fl, Lg) {
    for t < n0 {
      run shTrial.body [N, k, q, w, j0 + t]
        (A, S[2 * t], Thr, Pt, T, SR, Ds, Rg, P2, A, G, Fl, Lg)
    }
  }

end Program

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Trials

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IdxTst Q] in
/-- The potential test on a scalar machine with the standard model at
$20000k\boldsymbol{u} \le 1$, exact comparisons and exact natural literals up to $1$: from a
step $\widehat{\mathbf{H}}$ at `T` ($k = 2^q \le n$), the threshold $p_t$ at `Pt`, the matrix
$\mathbf{H}$ at `A` and the words $g$, $f$ at `G`, `Fl`,
`NLAlib.ShiftedQR.shPotentialAccept` computes a $p$ within $20\boldsymbol{u}$, relatively, of
$\psi_k(\widehat{\mathbf{H}})$, and either $p < p_t$ and the step is accepted (`A` holds
$\widehat{\mathbf{H}}$, `G` is $0$, `Fl` is $1$), or $p_t \le p$ and `A`, `G`, `Fl` are
unchanged. It writes only `A`, `G`, `Fl` and `P2`. -/
theorem shPotentialAccept_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hNat : IsExactNatLit id M 1) (hC : IsCmp id I) {τ : Tape ℝ}
    {m : Mem ℝ} {n k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) (hu : 20000 * k * u ≤ 1)
    {pt t p2 a g f : ℕ × ℕ} {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {pv gv fv : ℝ}
    (hT : HoldsMatrix t H' m.store) (hA : HoldsMatrix a H m.store)
    (hpt : m.store.get pt.1 pt.2 = some pv) (hg : m.store.get g.1 g.2 = some gv)
    (hf : m.store.get f.1 f.2 = some fv) (hrp : p2.2 < m.store.len p2.1)
    (hta : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hga : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hp2 : Fp.Disj (Store.inBlock p2.1 p2.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock pt.1 pt.2 1 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1))
    (hL : IsIndexLit M I) {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    {P : List GivensEntry} (hlog : HoldsSlottedLog lg ns w LL P m.store) (hj : LL.length < ns)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [pt, t, p2, a, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (shPotentialAccept (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, w, LL.length] [pt, t, p2, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock p2.1 p2.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => ∃ p : ℝ, |p - hessenbergPotential k H'| ≤ 20 * u * hessenbergPotential k H' ∧
        ((p < pv ∧ HoldsMatrix a H' m'.store ∧ m'.store.get g.1 g.2 = some 0 ∧
            m'.store.get f.1 f.2 = some 1 ∧ HoldsSlottedLog lg ns w (LL ++ [some P]) [] m'.store) ∨
          (pv ≤ p ∧ HoldsMatrix a H m'.store ∧ m'.store.get g.1 g.2 = some gv ∧
            m'.store.get f.1 f.2 = some fv ∧ HoldsSlottedLog lg ns w LL P m'.store))) m := sorry

/-- An **accepted step** of `Sh`, with the threshold words $t$ of the scan and $p_t$ of the
potential test: one of the bottom $k$ subdiagonal entries passes the scan, or a value within
$20\boldsymbol{u}$, relatively, of $\psi_k(\widehat{\mathbf{H}})$ is below $p_t$. -/
def ShAccepted (u : ℝ) {n : ℕ} (k : ℕ) (tv pv : ℝ) (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Prop :=
  (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
    ∃ p : ℝ, |p - hessenbergPotential k H'| ≤ 20 * u * hessenbergPotential k H' ∧ p < pv

/-- The outcome of one trial of `Sh` from the search word $g$, the flag word $f$ and the matrix
$\mathbf{H}$ at `a`, with the shift $r$: either nothing visible changed (and, if $g > 0$, the
computed step passed neither test), or $g > 0$ and an accepted step
(`NLAlib.ShiftedQR.ShAccepted`), by the exact unitary of the trial's entries, was copied to `a`,
`G` is $0$ and `Fl` is $1$. The trial's slot of the log is closed: rejected, or accepted. -/
def ShTrialPost (u : ℝ) {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℂ)
    (tv pv gv fv : ℝ) (a g f lg : ℕ × ℕ) (ns w : ℕ) (LL : List (Option (List GivensEntry)))
    (m' : Mem ℝ) : Prop :=
  (HoldsSlottedLog lg ns w (LL ++ [none]) [] m'.store ∧ m'.store.get g.1 g.2 = some gv ∧
    m'.store.get f.1 f.2 = some fv ∧ HoldsMatrix a H m'.store ∧
    (0 < gv → ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs ∧
        (∀ i : Fin n, n ≤ (i : ℕ) + k → tv < (1 + u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2) ∧
        ∃ p : ℝ, |p - hessenbergPotential k H'| ≤ 20 * u * hessenbergPotential k H' ∧
          pv ≤ p)) ∨
  (0 < gv ∧ m'.store.get g.1 g.2 = some 0 ∧ m'.store.get f.1 f.2 = some 1 ∧
    ∃ es : List GivensEntry, es.length = k * n ∧ (∀ x ∈ es, x.1 + 1 < n + 1) ∧
      HoldsSlottedLog lg ns w (LL ++ [some es]) [] m'.store ∧
    ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs
        (givensLog (n + 1) es) ∧
        IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧ ShAccepted u k tv pv H')

omit [Has IdxTst Q] in
/-- One trial of `Sh` on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$ and $20000k\boldsymbol{u} \le 1$, exact comparisons, index
literals and exact natural literals up to $n + 1$, for $k = 2^q \le n$:
`NLAlib.ShiftedQR.shTrial` writes only the matrix `A`, the words `G`, `Fl` and its scratch, and
ends in `NLAlib.ShiftedQR.ShTrialPost`. -/
theorem shTrial_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k q : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) (hkq : k = 2 ^ q) (hu : 20000 * k * u ≤ 1)
    {a sp thr pt t sr ds rg p2 g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {r : ℂ} {tv pv gv fv : ℝ}
    (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hthr : m.store.get thr.1 thr.2 = some tv) (hpt : m.store.get pt.1 pt.2 = some pv)
    (hg : m.store.get g.1 g.2 = some gv) (hf : m.store.get f.1 f.2 = some fv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1) (hrp : p2.2 < m.store.len p2.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hPt : Fp.Disj (Store.inBlock pt.1 pt.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5))
    (hP2 : Fp.Disj (Store.inBlock p2.1 p2.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock pt.1 pt.2 1 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length < ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, sp, thr, pt, t, sr, ds, rg, p2, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (shTrial (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, w, LL.length] [a, sp, thr, pt, t, sr, ds, rg, p2, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5 ⊔ Store.inBlock p2.1 p2.2 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (ShTrialPost u k H r tv pv gv fv a g f lg ns w LL) m := sorry

omit [Has IdxTst Q] in
/-- The trials of `Sh` on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$ and $20000k\boldsymbol{u} \le 1$, exact comparisons, index
literals and exact natural literals up to $n + 1$, for $k = 2^q \le n$: from an upper Hessenberg
$\mathbf{H}$ at `A`, $n_0$ shifts $z_j$ stored as pairs at `S`, the threshold words $t$ at `Thr`
and $p_t$ at `Pt`, the search word $1$ at `G`, and a shift $z_{j_0}$ every backward-stable degree
$k$ step of which has a bottom subdiagonal entry of modulus below $\omega$,
$(1 + \boldsymbol{u})^2\omega^2 \le t$, or passes the potential test against $p_t$,
`NLAlib.ShiftedQR.shTrials` sets the flag to $1$ and stores at `A` an accepted
(`NLAlib.ShiftedQR.ShAccepted`) backward-stable degree $k$ step with some shift $z_j$
repeated, upper Hessenberg. -/
theorem shTrials_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k q n0 : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) (hkq : k = 2 ^ q) (hu : 20000 * k * u ≤ 1)
    {a s thr pt t sr ds rg p2 g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {zs : Fin n0 → ℂ} {tv pv fv ω : ℝ}
    (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hA : HoldsMatrix a H m.store)
    (hs : ∀ j : Fin n0, m.store.readBlock s.1 (s.2 + 2 * j) 2 = some [(zs j).re, (zs j).im])
    (hthr : m.store.get thr.1 thr.2 = some tv) (hpt : m.store.get pt.1 pt.2 = some pv)
    (hg : m.store.get g.1 g.2 = some 1) (hf : m.store.get f.1 f.2 = some fv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1) (hrp : p2.2 < m.store.len p2.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * n0) ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
      Store.inBlock f.1 f.2 1) (Store.inBlock s.1 s.2 (2 * n0) ⊔ Store.inBlock thr.1 thr.2 1))
    (hPt : Fp.Disj (Store.inBlock pt.1 pt.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1))
    (hP2 : Fp.Disj (Store.inBlock p2.1 p2.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock pt.1 pt.2 1 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock s.1 s.2 (2 * n0) ⊔ Store.inBlock thr.1 thr.2 1))
    (jstar : Fin n0) (hgood : ∀ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) Rs,
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs jstar)) H' Rs →
        (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ < ω) ∨
          ∀ p : ℝ, |p - hessenbergPotential k H'| ≤ 20 * u * hessenbergPotential k H' → p < pv)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + n0 ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, s, thr, pt, t, sr, ds, rg, p2, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (shTrials (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, n0, w, LL.length] [a, s, thr, pt, t, sr, ds, rg, p2, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5 ⊔ Store.inBlock p2.1 p2.2 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.store.get f.1 f.2 = some 1 ∧
        ∃ (j : Fin n0) (Ls : List (Option (List GivensEntry)))
        (es : List GivensEntry), Ls.length = n0 ∧ (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store ∧ slotEntries w Ls = padEntries w es ∧
        ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs j)) H' Rs
          (givensLog (n + 1) es) ∧
          IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧ ShAccepted u k tv pv H') m := sorry

end Trials

end NLAlib.ShiftedQR
