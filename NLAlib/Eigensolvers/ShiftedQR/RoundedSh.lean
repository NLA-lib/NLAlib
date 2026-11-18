/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedShExc
public import NLAlib.Eigensolvers.ShiftedQR.RoundedFind

/-!
# The rounded shifting strategy

The shifting strategy $\mathrm{Sh}_{k,B}$ of [BanksGarzaVargasSrivastava2022, Lemma 5.4]
in floating point: from $\theta$-optimal shifts, `Find` selects a promising one, $r$; if the
rounded $\tau_{(z - r)^k}(\mathbf{H})^k$ (`comptau` of the rounded step) is below the rounded
$(1 - \gamma)^k\psi_k(\mathbf{H})^k$, the rounded step with $r$ is the output; otherwise the
exceptional shifts around $r$ are tried in turn, and one of them decouples or contracts the
potential except with probability $\varphi$ (the random translate of `Exc`). A flag word records
whether a step was taken ($1$) or no trial succeeded ($2$, a failure word the paper's `Sh` does
not have: it has no branch for the case that no shift is accepted).

## Main definitions

* `NLAlib.ShiftedQR.shStep`: the program; `NLAlib.ShiftedQR.ShOutcome`: its outcome.

## Main results

* `NLAlib.ShiftedQR.potential_contract_of_comptau_lt`,
  `NLAlib.ShiftedQR.norm_inv_le_of_le_comptau`: the two branches of the `comptau` test.
* `NLAlib.ShiftedQR.shTestStep_writes`: the computation of the test.
* `NLAlib.ShiftedQR.shAccept_decoupled_or_contract`, `NLAlib.ShiftedQR.shAccept_writes`: the
  accepted step.

The assembly, `Sh` as a probabilistic block, is in `NLAlib.Eigensolvers.ShiftedQR.RoundedShStep`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

/-- $1.0011^k \cdot 1.0012 \le 1.002^k$ for $k \ge 2$: the contraction factor of `Sh`
([BanksGarzaVargasSrivastava2022, Lemma 5.4], whose decrease factor $1.002$ needs $k \ge 2$:
$k = 1$ gives $1.0021$). -/
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
$\psi'^k N \le 1.0011^k$, then $\psi' \le 1.002(1 - \gamma)\psi$. -/
theorem potential_contract_of_comptau_lt {u γ t thr N ψ ψ' : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hu0 : 0 ≤ u) (hku : 100000 * k * u ≤ 1) (hγ1 : γ ≤ 1) (hψ : 0 ≤ ψ) (hN : 0 < N)
    (ht : |t - N⁻¹| ≤ 0.001 * N⁻¹)
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
Lemma 5.4]): let $N > 0$ (the norm $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\|$), the
computed $t$ within $0.001$, relatively, of $N^{-1}$, the computed threshold within
$(10k + 12)\boldsymbol{u}$, relatively, of $(1 - \gamma)^k\psi^k$, $\psi > 0$, $\gamma < 1$,
$k \ge 2$, $\boldsymbol{u} \ge 0$ and $10^5k\boldsymbol{u} \le 1$. If $t$ is not below the
threshold, then $N \le ((0.998(1 - \gamma)\psi)^{-1})^k$: the shift $r$ stagnates with the
ratio $\xi = 0.998(1 - \gamma)$. -/
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
into `P0`, and the threshold with the word `Cg` into `P1`; the step records its rotations in slot
$j$ of the log `Lg` of slot width $w$. The interface is
`[N, k, w, j] (A, Z, Cg) → (T, SR, P0, P1, Lg)`. -/
def shTestStep : Impl O Q := opsImpl% [N, k, w, j] (A, Z, Cg) → (T, SR, P0, P1, Lg) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (N * N)] (A, T);
  run replicatePair.body [k] (Z, SR);
  run (stepComptau (O := O) (Q := Q)).body [N, k, w, j] (T, SR, T, P0, Lg);
  run shThreshold.body [N, k] (A, Cg, P1)
}

/-- The deterministic start of `Sh`: the rounded potential $\tilde\psi$ of the order-$N$ matrix
`A` into `Rt`, `Find` (`NLAlib.ShiftedQR.findRounded` with `NLAlib.ShiftedQR.comptauHalf`) over
the $k = 2^m$ shifts `SS` into `Z`, and the computation of the `comptau` test
(`NLAlib.ShiftedQR.shTestStep`, word `Cg`, at slot $j$ of the log) into `P0`, `P1`. The
interface is `[N, m, k, w, j] (A, SS, Cg) → (Z, Rt, P0, P1, T, SR, Lg)`. -/
def shPrefix : Impl O Q := opsImpl% [N, m, k, w, j] (A, SS, Cg) → (Z, Rt, P0, P1, T, SR, Lg) {
  run roundedPotential.body [N, k, m] (A, Rt);
  run (findRounded (comptauHalf (O := O) (Q := Q))).body [N, m, k] (A, SS, Z);
  run shTestStep.body [N, k, w, j] (A, Z, Cg, T, SR, P0, P1, Lg)
}

/-- The decision of `Sh`: below the threshold (`P0 < P1`) the step `T` is accepted
(`NLAlib.ShiftedQR.trialAccept`, flag $1$), otherwise the exceptional branch runs
(`NLAlib.ShiftedQR.shExc`). The interface is
`[N, k, q, n0, w, j] (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss) →
(A, Gw, Fl, Lg)`; acceptance validates the test step's slot $j$, the exceptional trials use the
slots $j + 1, \dots, j + n_0$.
-/
def shDecide : Impl O Q :=
  opsImpl% [N, k, q, n0, w, j]
      (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss) → (A, Gw, Fl, Lg) {
    if (Has.inj CmpTst.lt) [] (P0, P1) {
      run trialAccept.body [N, w, j] (T, A, Gw, Fl, Lg)
    } else {
      run shExc.body [N, k, q, n0, w, j + 1]
        (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, T, SR, Ds, Rg, P2, Ss, A, Gw, Fl, Lg)
    }
  }

/-- `Sh` with caller-owned scratch: the start (`NLAlib.ShiftedQR.shPrefix`) and the decision
(`NLAlib.ShiftedQR.shDecide`). The interface is
`[N, m, k, n0, w, j0] (A, SS, Cg, Cr, Cw, Cp, G, Thr, Z, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss,
Gw) → (A, Fl, Lg)`. -/
def shStepWithScratch : Impl O Q :=
  opsImpl% [N, m, k, n0, w, j0]
      (A, SS, Cg, Cr, Cw, Cp, G, Thr, Z, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss, Gw) →
      (A, Fl, Lg) {
    run shPrefix.body [N, m, k, w, j0] (A, SS, Cg, Z, Rt, P0, P1, T, SR, Lg);
    run shDecide.body [N, k, m, n0, w, j0]
      (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss, A, Gw, Fl, Lg)
  }

/-- **The shifting strategy `Sh`** ([BanksGarzaVargasSrivastava2022, Lemma 5.4], with a failure flag
for the case, which the paper does not treat, that no shift is accepted): from the order-$N$ matrix
`A` and $k = 2^m$ optimal shifts `SS`, with the words `Cg` ($(1 - \gamma)^k$), `Cr` (the radius
factor $2^{1/k}\theta\alpha B^{1/k}$), `Cw` ($\varepsilon/2$), `Cp` ($1.0015(1 - \gamma)$), the net
`G` of $n_0$ points and the scan threshold `Thr`, store a step at `A` and set the flag `Fl` to $1$,
or set it to $2$ if no trial succeeded. All scratch is scoped. The interface is
`[N, m, k, n0, w, j0] (A, SS, Cg, Cr, Cw, Cp, G, Thr) → (A, Fl, Lg)`: the test step records its
rotations in slot $j_0$ of the log `Lg` of slot width $w$, the exceptional trials in the slots
$j_0 + 1, \dots, j_0 + n_0$; the accepted slot is validated. -/
def shStep : Impl O Q :=
  opsImpl% [N, m, k, n0, w, j0] (A, SS, Cg, Cr, Cw, Cp, G, Thr) → (A, Fl, Lg) {
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
  run shStepWithScratch.body [N, m, k, n0, w, j0]
    (A, SS, Cg, Cr, Cw, Cp, G, Thr, Z, Rt, Pt, P0, P1, T, SR, Ds, Rg, P2, Ss, Gw, A, Fl, Lg)
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

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The computation of the `comptau` test on a scalar machine with the standard model at
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
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock p0.1 p0.2 1))
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length < ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, z, cg, t, sr, p0, p1], b.1 ≠ lg.1) :
    Writes .total I τ (shTestStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, z, cg, t, sr, p0, p1, lg])
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock p0.1 p0.2 1 ⊔ Store.inBlock p1.1 p1.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ ∃ es : List GivensEntry, es.length = k * n ∧
        (∀ x ∈ es, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w LL es m'.store ∧
        ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs
          (givensLog (n + 1) es) ∧
          IsUpperHessenberg H' ∧ HoldsMatrix t H' m'.store ∧
          (∃ tc : ℝ, m'.store.get p0.1 p0.2 = some tc ∧
            |tc - ‖WithLp.toLp 2 ((Polynomial.aeval H
              (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖⁻¹| ≤ 0.001 * ‖WithLp.toLp 2
                ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖⁻¹) ∧
          m'.store.get p1.1 p1.2 = some (optimalThresholdWord M H k cv)) m := sorry

end Test

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

/-- **The accepted branch of the `comptau` test decouples or contracts**
([BanksGarzaVargasSrivastava2022, proof of Lemma 5.4]): let $\widehat{\mathbf{H}}$ be computed from
$\mathbf{H}$ by a backward-stable chain of $k$ steps with the shift $r$, relative error
$x = 300(n+1)^2\boldsymbol{u}$; let $\mathbf{H} \ne 0$ of order $n + 1$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with $\kappa(\mathbf{V}) \le B$,
$\|\mathbf{H}\|_2 \le S$, $\lvert r \rvert \le C\|\mathbf{H}\|_2$ ($C \ge 0$) at distance at least
$d > 0$ from every $e_i$, $\omega > 0$, $x \le (16B)^{-1}(d/((2 + 2C)S))^k$ and
$(66 + 2C)BS((2 + 2C)S/d)^k\sqrt{n + 1}\,x \le 0.001\,\omega$; let $2 \le k \le n$,
$10^5k\boldsymbol{u} \le 1$, $\gamma \le 1$, a threshold word
$t \ge (1 + \boldsymbol{u})^2\omega^2$, a computed $t_c$ within $0.001$, relatively, of
$\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\|^{-1}$ and below the rounded threshold
`NLAlib.ShiftedQR.optimalThresholdWord` with the word $(1 - \gamma)^k$, the computed step
$\widehat{\mathbf{H}}$ has a bottom subdiagonal entry passing the scan, or
$\psi_k(\widehat{\mathbf{H}}) \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$. -/
theorem shAccept_decoupled_or_contract {M : Machine ℝ} {u C B S d ω γ tv tc : ℝ}
    (hM : StdModel u id M) {k : ℕ} {H H' V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {r : ℂ} {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (hch : IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs)
    (hk : 2 ≤ k) (hkn : k ≤ n) (hku : 100000 * k * u ≤ 1) (hC : 0 ≤ C) (hd : 0 < d)
    (hω : 0 < ω) (hH0 : H ≠ 0) (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hS : specNorm H ≤ S) (hr : ‖r‖ ≤ C * specNorm H) (hdist : ∀ i, d ≤ ‖e i - r‖)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hγ1 : γ ≤ 1) (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    (htc : |tc - ‖WithLp.toLp 2 ((Polynomial.aeval H
      (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖⁻¹| ≤ 0.001 * ‖WithLp.toLp 2
        ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖⁻¹)
    (hlt : tc < optimalThresholdWord M H k ((1 - γ) ^ k)) :
    (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
      hessenbergPotential k H' ≤ 1.002 * (1 - γ) * hessenbergPotential k H := by
  have hu0 := hM.roundoff_nonneg
  have hk0 : 0 < k := by omega
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hne : ∀ i, e i ≠ r := fun i he => by
    have := hdist i; rw [he, sub_self, norm_zero] at this; linarith
  have hN := norm_toLp_inv_aeval_replicate_last_pos hV hHV hne k
  rcases hch.exists_norm_subdiag_lt_or_potential_pow_mul_le (by positivity) hC hd hω hk0 hkn hH0
    hH hV hHV hκ hS hr hdist hxu hbound with ⟨i, hik, hi⟩ | hpot
  · refine Or.inl ⟨i, hik, ?_⟩
    have h1 : (1 - u) ^ 2 ≤ (1 + u) ^ 2 := by nlinarith
    have h2 : ‖H' i.succ i.castSucc‖ ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hi.le 2
    nlinarith [sq_nonneg (1 - u), sq_nonneg ‖H' i.succ i.castSucc‖]
  · refine Or.inr (potential_contract_of_comptau_lt hk hu0 hku hγ1
      (hessenbergPotential_nonneg k H) hN htc ?_ hlt hpot)
    have := abs_optimalThresholdWord_sub_le hM hk0 hkn (by nlinarith) (c := (1 - γ) ^ k)
      (pow_nonneg (by linarith) k) H
    simpa [mul_pow] using this

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

/-- The state of `Sh` after the rounded potential: the context and at `L + 1` a $p$ within
$20\boldsymbol{u}$, relatively, of $\psi_k(\mathbf{H})$. -/
def ShState1 (u : ℝ) (L k : ℕ) (ε : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (cg cr cw cp tv : ℝ) (a s wg wr ww wp g thr f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m ∧
    ∃ p : ℝ, |p - hessenbergPotential k H| ≤ 20 * u * hessenbergPotential k H ∧
      m.store.get (L + 1) 0 = some p

/-- The state of `Sh` after `Find`: `NLAlib.ShiftedQR.ShState1` and an $\alpha$-promising shift at
`L` (a pair). -/
def ShState2 (u : ℝ) (L k : ℕ) (ε : ℝ) (H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (e : Fin (n + 1) → ℂ) (ss : List ℂ) (α cg cr cw cp tv : ℝ)
    (a s wg wr ww wp g thr f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  ShState1 u L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m ∧
    ∃ r : ℂ, m.store.readBlock L 0 2 = some [r.re, r.im] ∧ IsPromisingRitzValue α V e ss r

/-- The state of `Sh` after the computation of the `comptau` test: `NLAlib.ShiftedQR.ShState1`,
an $\alpha$-promising shift $r$ at `L`, at `L + 5` a backward-stable degree $k$ step with $r$
repeated by the exact unitary of its entries (pending in the log after `LL`), at `L + 3` a value
within $0.001$, relatively, of $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\|^{-1}$, and at `L
+ 4` the rounded threshold. -/
def ShState3 (M : Machine ℝ) (u : ℝ) (L k : ℕ) (ε : ℝ)
    (H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e : Fin (n + 1) → ℂ) (ss : List ℂ)
    (α cg cr cw cp tv : ℝ) (a s wg wr ww wp g thr f lg : ℕ × ℕ) (ns w : ℕ)
    (LL : List (Option (List GivensEntry))) (m : Mem ℝ) : Prop :=
  ShState1 u L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m ∧
    ∃ r : ℂ, m.store.readBlock L 0 2 = some [r.re, r.im] ∧ IsPromisingRitzValue α V e ss r ∧
      ∃ es : List GivensEntry, es.length = k * n ∧ (∀ x ∈ es, x.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns w LL es m.store ∧
      ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs
          (givensLog (n + 1) es) ∧
          IsUpperHessenberg H' ∧ HoldsMatrix (L + 5, 0) H' m.store ∧
          (∃ tc : ℝ, m.store.get (L + 3) 0 = some tc ∧
            |tc - ‖WithLp.toLp 2 ((Polynomial.aeval H
              (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖⁻¹| ≤ 0.001 * ‖WithLp.toLp 2
                ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖⁻¹) ∧
          m.store.get (L + 4) 0 = some (optimalThresholdWord M H k cg)

section Steps

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

omit [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The rounded potential of `Sh` (`NLAlib.ShiftedQR.roundedPotential_writes`) reaches
`NLAlib.ShiftedQR.ShState1`, for
$k = 2^q \le n$ and $20000k\boldsymbol{u} \le 1$. -/
theorem shPotential_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n)
    (hu : 20000 * k * u ≤ 1) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {cg cr cw cp tv : ℝ}
    (hm : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) :
    Writes .total I τ (roundedPotential (Op := O) (Tst := Q)).body
      (Env.frame [n + 1, k, q] [a, (L + 1, 0)]) (Store.inBlock (L + 1) 0 1)
      (ShState1 u L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f) m := by
  obtain ⟨⟨ha, hs, hwg, hwr, hww, hwp, hg, hthl, hfl⟩, -, -⟩ := hv
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := id hm
  refine (roundedPotential_writes (τ := τ) (p := (L + 1, 0)) hS hM hkq hkn hu hA (by simp [h1])
    (by disjoint)).mono le_rfl ?_
  rintro m' hfr ⟨-, p, hp, hpψ⟩
  exact ⟨hm.of_eqOff hfr (by disjoint), p, hpψ, hp⟩

omit [Has DiskSampleOp O] in
/-- `Find` of `Sh` (`NLAlib.ShiftedQR.findRounded_writes` with the comparison values of
`NLAlib.ShiftedQR.comptauHalf_isHalfTau`) reaches
`NLAlib.ShiftedQR.ShState2`: from `NLAlib.ShiftedQR.ShState1`, for $k = 2^m$ shifts at distance at
least $d > 0$ from the spectrum and in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$, $\mathbf{H} \ne 0$
upper Hessenberg, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le B$, $(n + 1)\boldsymbol{u} \le 1/2500$,
$30000(\lfloor k/2 \rfloor + 1)\boldsymbol{u} \le 1$ and
$300(n+1)^2\boldsymbol{u} \le (8004B)^{-1}(d/((2 + 2C)\|\mathbf{H}\|_2))^{\lfloor k/2 \rfloor}$, the
stored shift is $(1.01B)^{4m/2^m}$-promising. -/
theorem shFind_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) (hQ : IsToNat id I)
    (hNat : IsExactNatLit id M (n + 1)) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hkq : k = 2 ^ q)
    (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} {B C d cg cr cw cp tv : ℝ} (hH : IsUpperHessenberg H)
    (hH0 : H ≠ 0) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hC0 : 0 ≤ C) (hd : 0 < d) (hlen : ss.length = k)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hu : 30000 * (((k / 2 : ℕ) : ℝ) + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (8004 * B)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ (k / 2))
    (hm : ShState1 u L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) :
    Writes .total I τ (findRounded (comptauHalf (O := O) (Q := Q))).body
      (Env.frame [n + 1, q, k] [a, s, (L, 0)]) (Store.inBlock L 0 2)
      (ShState2 u L k ε H V e ss ((1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q)) cg cr cw cp tv
        a s wg wr ww wp g thr f) m := by
  obtain ⟨⟨ha, hs', hwg, hwr, hww, hwp, hg, hthl, hfl⟩, -, -⟩ := hv
  obtain ⟨⟨hA, hss, -, -, -, -, -, -, -, hlen', h0, -⟩, -⟩ := id hm
  have hne : ∀ r ∈ ss, ∀ i, e i ≠ r := fun r hr i he => by
    have := hdist r hr i; rw [he, sub_self, norm_zero] at this; linarith
  have hTau := comptauHalf_isHalfTau (I := I) hS hM hC hL hH hH0 hV hHV hκ hC0 hd hs hdist hnu
    (by rw [hlen]; exact hu) (by rw [hlen]; exact hxu)
  refine (findRounded_writes (τ := τ) (b := a) (ss := s) (z := (L, 0)) hS hL hC hQ hV hHV hκ hne
    hTau (hNat.mono (by omega)) hkq hlen hA (by rw [hlen]; exact hss)
    (by simp [Mem.Live, hlen']; omega) (by disjoint) (by simp [h0])).mono le_rfl ?_
  rintro m' hfr ⟨-, c, hc, hpr⟩
  obtain ⟨hctx, p, hp, hP⟩ := hm
  exact ⟨⟨hctx.of_eqOff hfr (by disjoint), p, hp, hfr.keep (Store.readsOnly_get _ _ _)
    (by disjoint) hP⟩, c, hc, hpr⟩

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The computation of the `comptau` test of `Sh` (`NLAlib.ShiftedQR.shTestStep_writes`) reaches
`NLAlib.ShiftedQR.ShState3` from `NLAlib.ShiftedQR.ShState2`, for $1 \le k \le n$ and shifts at
distance at least $d > 0$ from the spectrum and in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$. -/
theorem shTest_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {L k : ℕ} (hk0 : 0 < k)
    (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} {B C d α cg cr cw cp tv : ℝ} (hH : IsUpperHessenberg H)
    (hH0 : H ≠ 0) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hC0 : 0 ≤ C) (hd : 0 < d)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hu : 30000 * (k + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ k)
    (hm : ShState2 u L k ε H V e ss α cg cr cw cp tv a s wg wr ww wp g thr f m)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length < ns) (hw : k * n ≤ w)
    (hlgL : lg.1 < L) (hlgv : ∀ b ∈ [a, s, wg, wr, ww, wp, g, thr, f], b.1 ≠ lg.1) :
    Writes .total I τ (shTestStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, (L, 0), wg, (L + 5, 0), (L + 6, 0), (L + 3, 0),
        (L + 4, 0), lg])
      (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 6) 0 (2 * k) ⊔
        Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (ShState3 M u L k ε H V e ss α cg cr cw cp tv a s wg wr ww wp g thr f lg ns w LL) m := sorry

omit [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The accepted branch of `Sh`: from `NLAlib.ShiftedQR.ShState3` with the word
$c_g = (1 - \gamma)^k$ and the computed $t_c$ below the threshold, the acceptance
(`NLAlib.ShiftedQR.trialAccept`) ends in `NLAlib.ShiftedQR.ShOutcome`. Here $\mathbf{H} \ne 0$ of
order $n + 1$ is upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with $\kappa(\mathbf{V}) \le B$,
$\|\mathbf{H}\|_2 \le S$, the shifts lie in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$ ($C \ge 0$) at
distance at least $d > 0$ from every $e_i$, $\omega > 0$,
$x = 300(n+1)^2\boldsymbol{u} \le (16B)^{-1}(d/((2 + 2C)S))^k$,
$(66 + 2C)BS((2 + 2C)S/d)^k\sqrt{n + 1}\,x \le 0.001\,\omega$, $2 \le k \le n$,
$10^5k\boldsymbol{u} \le 1$, $\gamma \le 1$ and the scan threshold is at least
$(1 + \boldsymbol{u})^2\omega^2$. -/
theorem shAccept_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hNat : IsExactNatLit id M 1) {τ : Tape ℝ} {m : Mem ℝ} {L k : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) (hku : 100000 * k * u ≤ 1) {ε : ℝ}
    {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {B S C d ω γ α cr cw cp tv : ℝ} (hH : IsUpperHessenberg H) (hH0 : H ≠ 0) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hC0 : 0 ≤ C) (hd : 0 < d) (hω : 0 < ω)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω) (hγ1 : γ ≤ 1) (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    (hL : IsIndexLit M I)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length < ns) (hlgL :
      lg.1 < L)
    (hlgv : ∀ b ∈ [a, s, wg, wr, ww, wp, g, thr, f], b.1 ≠ lg.1)
    (hm : ShState3 M u L k ε H V e ss α ((1 - γ) ^ k) cr cw cp tv a s wg wr ww wp g thr f lg ns w LL
      m)
    (hlt : ∀ tc, m.store.get (L + 3) 0 = some tc →
      tc < optimalThresholdWord M H k ((1 - γ) ^ k)) :
    Writes .total I τ (trialAccept (O := O) (Q := Q)).body
      (Env.frame [n + 1, w, LL.length] [(L + 5, 0), a, (L + 11, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f lg
        ns w LL 1)
      m := sorry

/-- The rejected branch of `Sh` enters the exceptional branch: from
`NLAlib.ShiftedQR.ShState3` with $c_g = (1 - \gamma)^k$, $\gamma < 1$,
$\psi_k(\mathbf{H}) > 0$, $2 \le k \le n$, $10^5k\boldsymbol{u} \le 1$, shifts that are no
eigenvalue, and the computed $t_c$ not below the threshold, the state is
`NLAlib.ShiftedQR.ShExcPre`: the promising shift stagnates with the ratio $0.998(1 - \gamma)$. -/
theorem ShState3.shExcPre {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {m : Mem ℝ} {L k : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) (hku : 100000 * k * u ≤ 1) {ε : ℝ}
    {a s wg wr ww wp g thr f : ℕ × ℕ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} {γ α cr cw cp tv : ℝ}
    {lg : ℕ × ℕ} {ns w : ℕ} {LL : List (Option (List GivensEntry))}
    (hm : ShState3 M u L k ε H V e ss α ((1 - γ) ^ k) cr cw cp tv a s wg wr ww wp g thr f lg ns w LL
      m)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hne : ∀ r ∈ ss, ∀ i, e i ≠ r)
    (hγ1 : γ < 1) (hψ : 0 < hessenbergPotential k H)
    (hle : ∀ tc, m.store.get (L + 3) 0 = some tc →
      optimalThresholdWord M H k ((1 - γ) ^ k) ≤ tc) :
    ShExcPre u L k ε H V e ss α γ ((1 - γ) ^ k) cr cw cp tv a s wg wr ww wp g thr f m := sorry

end Steps

end NLAlib.ShiftedQR
