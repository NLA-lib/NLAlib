/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSh

/-!
# The rounded shifting strategy as a probabilistic block

The assembly of $\mathrm{Sh}_{k,B}$ of [BanksGarzaVargasSrivastava2022, Lemma 5.4] in floating
point from its steps (`Find`, the `comptau` test, the accepted step and the trials of `Exc`): the
decision between the accepted step and the exceptional shifts, the prefix of the program, and the
whole step as a probabilistic block specification. A failure word records that no trial
succeeded, a branch the paper's `Sh` does not have.

## Main results

* `NLAlib.ShiftedQR.shDecide_pwrites`: the decision between the accepted step and `Exc`.
* `NLAlib.ShiftedQR.shPrefix_writes`: the prefix (`Find` and the test).
* `NLAlib.ShiftedQR.shStep_pwrites`: `Sh` as a probabilistic block.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

variable {n : ℕ}

section Assembly

/-- The forms of the precision condition $x \le (8004B)^{-1}(d/((2 + 2C)\Sigma))^k$ that the
steps of `Sh` use: with $\|\mathbf{H}\|_2$ for $\Sigma \ge \|\mathbf{H}\|_2 > 0$, with the
exponent $k/2$ (as $d \le (2 + 2C)\|\mathbf{H}\|_2$), and with $16$ for $8004$. -/
theorem shPrecision_forms {x B C d S : ℝ} {k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hHp : 0 < specNorm H) (hSH : specNorm H ≤ S) (hC0 : 0 ≤ C) (hd : 0 < d) (hB : 0 < B)
    (hdH : d ≤ (2 + 2 * C) * specNorm H)
    (hxu : x ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k) :
    x ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ k ∧
      x ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ (k / 2) ∧
      x ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k := by
  have hS0 : 0 < S := hHp.trans_le hSH
  have hρ0 : 0 ≤ d / ((2 + 2 * C) * S) := by positivity
  have hρ : d / ((2 + 2 * C) * S) ≤ d / ((2 + 2 * C) * specNorm H) := by gcongr
  have hρ1 : d / ((2 + 2 * C) * specNorm H) ≤ 1 := (div_le_one (by positivity)).mpr hdH
  have h1 : x ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ k :=
    hxu.trans (by gcongr)
  refine ⟨h1, h1.trans ?_, hxu.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hρ1
      (Nat.div_le_self k 2)) (by positivity)
  · exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by linarith)) (by positivity)


variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]


omit [Has IdxTst Q] in
/-- The decision of `Sh` as a probabilistic block: `NLAlib.ShiftedQR.shDecide` from the
state `NLAlib.ShiftedQR.ShState3` (with the words $(1 - \gamma)^k$,
$2^{1/k}\theta\alpha B^{1/k}$, $\varepsilon/2$, $1.0015(1 - \gamma)$) ends in
`NLAlib.ShiftedQR.ShOutcome` except with probability at most $\varphi$: the accepted branch
(`NLAlib.ShiftedQR.shAccept_writes`) never fails, the exceptional one
(`NLAlib.ShiftedQR.shExc_pwrites`) fails with probability at most $\varphi$. -/
theorem shDecide_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {L k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {B S ω θ α γ φ C d tv : ℝ} (hH : IsUpperHessenberg H) (hH0 : H ≠ 0) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hlen : ss.length = k) (hopt : IsOptimalRitzValues θ H ss) (hθ : 1 ≤ θ) (hd' : 0 < d)
    (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖) (hsH : ∀ s ∈ ss, ‖s‖ ≤ 1.1 * specNorm H)
    (hsC : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hne : ∀ r ∈ ss, ∀ i, e i ≠ r) (hα1 : 1 ≤ α)
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : d ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hku : 100000 * k * u ≤ 1)
    (hxu16 : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hj : LL.length + (excNet ε).length < ns) (hw : k * n ≤ w) (hlgL : lg.1 < L) (hlgv : ∀ b ∈ [a,
      s, wg, wr, ww, wp, g, thr, f], b.1 ≠ lg.1) :
    PWrites law I (shDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, (excNet ε).length, w, LL.length] [a, (L, 0), wr, ww, wp, g, thr,
        (L + 1, 0),
        (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0), (L + 8, 0),
        (L + 9, 0), (L + 10, 0), a, (L + 11, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (ShState3 M u L k ε H V e ss α ((1 - γ) ^ k)
        ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹))) (ε / 2) (1.0015 * (1 - γ)) tv
        a s wg wr ww wp g thr f lg ns w LL)
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f lg
        ns w LL (1 + (excNet ε).length))
      φ := sorry

omit [Has DiskSampleOp O] in
/-- The start of `Sh`: from the context `NLAlib.ShiftedQR.ShCtx`, the rounded potential,
`Find` and the computation of the `comptau` test (`NLAlib.ShiftedQR.shPotential_writes`,
`NLAlib.ShiftedQR.shFind_writes`, `NLAlib.ShiftedQR.shTest_writes`) reach
`NLAlib.ShiftedQR.ShState3` with $\alpha = (1.01B)^{4m/2^m}$. -/
theorem shPrefix_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) (hQ : IsToNat id I)
    (hNat : IsExactNatLit id M (n + 1)) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ} (hkq : k = 2 ^ q)
    (hk : 2 ≤ k) (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f) {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} {B C d α cg cr cw cp tv : ℝ} (hH : IsUpperHessenberg H)
    (hH0 : H ≠ 0) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hC0 : 0 ≤ C) (hd : 0 < d) (hlen : ss.length = k)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hα : α = (1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q))
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hku : 100000 * k * u ≤ 1)
    (hxuT : 300 * (n + 1) ^ 2 * u ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ k)
    (hxuF : 300 * (n + 1) ^ 2 * u ≤
      (8004 * B)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ (k / 2))
    (hm : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length < ns) (hw : k * n ≤ w)
    (hlgL : lg.1 < L) (hlgv : ∀ b ∈ [a, s, wg, wr, ww, wp, g, thr, f], b.1 ≠ lg.1) :
    Writes .total I τ (shPrefix (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, w, LL.length] [a, s, wg, (L, 0), (L + 1, 0), (L + 3, 0), (L + 4,
        0), (L + 5, 0),
        (L + 6, 0), lg])
      (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock L 0 2 ⊔
        (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 6) 0 (2 * k) ⊔
          Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (ShState3 M u L k ε H V e ss α cg cr cw cp tv a s wg wr ww wp g thr f lg ns w LL) m := sorry

/-- `Sh` with scratch as a probabilistic block, on a scalar machine with the standard model, exact
comparisons, index literals, index conversion and exact natural literals up to $n + 1$, a measurable
tape-local interpretation with an exact polar disk sampler on a stream `s₀` uniform on $[0, 1]$: let
$\mathbf{H}$ be upper Hessenberg of order $n + 1$,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with $\kappa(\mathbf{V}) \le B$,
$\|\mathbf{H}\|_2 \le \Sigma$, $2 \le k = 2^m \le n$, $0 < \omega \le \psi_k(\mathbf{H})$, the $k$
stored shifts $\theta$-optimal ($\theta \ge 1$), in $\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$ and at
distance at least $d > 0$ from every $e_i$; $\alpha = (1.01B)^{4m/2^m}$, $0 < \gamma < 1$,
$\varepsilon = (0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$,
$0 < \varphi \le 1/5$, $d \le \varepsilon R_{\mathrm{lo}}\sqrt{\varphi/(11(n + 1))}/4$ for
$[R_{\mathrm{lo}}, R_{\mathrm{hi}}] =
[1.998^{1/k}, 2.002^{1/k}]\,\theta\alpha B^{1/k}\psi_k(\mathbf{H})$,
$1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le C$, the stored words $(1 - \gamma)^k$,
$2^{1/k}\theta\alpha B^{1/k}$, $\varepsilon/2$, $1.0015(1 - \gamma)$, the net
`NLAlib.ShiftedQR.excNet ε`, a scan threshold $t \ge (1 + \boldsymbol{u})^2\omega^2$, and the
precision conditions $(n + 1)\boldsymbol{u} \le 1/2500$, $10^5k\boldsymbol{u} \le 1$,
$x = 300(n+1)^2\boldsymbol{u} \le (8004B)^{-1}(d/((2 + 2C)\Sigma))^k$,
$(66 + 2C)B\Sigma((2 + 2C)\Sigma/d)^k\sqrt{n + 1}\,x \le 0.001\,\omega$ and
$6\boldsymbol{u}(1.1\Sigma + 3R_{\mathrm{hi}}) \le
\min(0.005, \sqrt{\varphi/(11(n + 1))}/8)\,\varepsilon R_{\mathrm{lo}}$.
Then `NLAlib.ShiftedQR.shStepWithScratch`, from the context `NLAlib.ShiftedQR.ShCtx` with these
words and scratch above `L`, writes only the matrix, the flag and the scratch, and ends in
`NLAlib.ShiftedQR.ShOutcome` except with probability at most $\varphi$. -/
theorem shStepWithScratch_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {L k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {B S ω θ α γ φ C d tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hlen : ss.length = k) (hopt : IsOptimalRitzValues θ H ss) (hθ : 1 ≤ θ) (hd' : 0 < d)
    (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖) (hsH : ∀ s ∈ ss, ‖s‖ ≤ 1.1 * specNorm H)
    (hα : α = (1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : d ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hku : 100000 * k * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hj : LL.length + (excNet ε).length < ns) (hw : k * n ≤ w) (hlgL : lg.1 < L) (hlgv : ∀ b ∈ [a,
      s, wg, wr, ww, wp, g, thr, f], b.1 ≠ lg.1) :
    PWrites law I (shStepWithScratch (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length, w, LL.length] [a, s, wg, wr, ww, wp, g, thr,
        (L, 0),
        (L + 1, 0), (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0),
        (L + 8, 0), (L + 9, 0), (L + 10, 0), (L + 11, 0), a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => ShCtx L k ε H ss ((1 - γ) ^ k) ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹)))
        (ε / 2) (1.0015 * (1 - γ)) tv a s wg wr ww wp g thr f m ∧
        HoldsSlottedLog lg ns w LL [] m.store)
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f lg
        ns w LL (1 + (excNet ε).length))
      φ := sorry

/-- **The rounded shifting strategy `Sh` as a probabilistic block**
([BanksGarzaVargasSrivastava2022, Lemma 5.4], corrected: the requirements add
$\|\mathbf{H}\|_2 \le \Sigma$ and $k \ge 2$, which the decrease factor $1.002$ needs, and a
failure flag is set when no shift is accepted; the accepted step is the rounded one, where line 4
of the printed `Sh` outputs the exact step; the exceptional radius carries the factor $2^{1/k}$
of line 1 of `Exc`, so that it lies in $[1.998^{1/k}, 2.002^{1/k}]\,\theta\alpha B^{1/k}\psi$
where the paper has $1.001\,\theta\alpha B^{1/k}\psi$; and the net of `Exc` covers
$\mathbb{D}(r, (1 + \varepsilon)R)$ with rounding at most $0.005\varepsilon R$ and the packing
count $11$, where the paper intersects with $\mathbb{D}(r, R)$, budgets $0.1\varepsilon R$ and
counts $3$): on a scalar machine with the standard model, exact comparisons, index literals, index
conversion and exact natural literals up to $n + 1$, a measurable tape-local interpretation
with an exact polar disk sampler on a stream `s₀` uniform on $[0, 1]$: let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$
with $\kappa(\mathbf{V}) \le B$, $\|\mathbf{H}\|_2 \le \Sigma$, $2 \le k = 2^m \le n$,
$0 < \omega \le \psi_k(\mathbf{H})$, the $k$ stored shifts $\theta$-optimal ($\theta \ge 1$), in
$\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$ and at distance at least $d > 0$ from every $e_i$;
$\alpha = (1.01B)^{4m/2^m}$, $0 < \gamma < 1$,
$\varepsilon = (0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$,
$0 < \varphi \le 1/5$, $d \le \varepsilon R_{\mathrm{lo}}\sqrt{\varphi/(11(n + 1))}/4$ for
$[R_{\mathrm{lo}}, R_{\mathrm{hi}}] = [1.998^{1/k}, 2.002^{1/k}]\,\theta\alpha B^{1/k}
\psi_k(\mathbf{H})$, $1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le C$, the stored words
$(1 - \gamma)^k$, $2^{1/k}\theta\alpha B^{1/k}$, $\varepsilon/2$, $1.0015(1 - \gamma)$, the net
`NLAlib.ShiftedQR.excNet ε`, a scan threshold $t \ge (1 + \boldsymbol{u})^2\omega^2$, and the
precision conditions $(n + 1)\boldsymbol{u} \le 1/2500$, $10^5k\boldsymbol{u} \le 1$,
$x = 300(n+1)^2\boldsymbol{u} \le (8004B)^{-1}(d/((2 + 2C)\Sigma))^k$,
$(66 + 2C)B\Sigma((2 + 2C)\Sigma/d)^k\sqrt{n + 1}\,x \le 0.001\,\omega$ and
$6\boldsymbol{u}(1.1\Sigma + 3R_{\mathrm{hi}}) \le \min(0.005, \sqrt{\varphi/(11(n + 1))}/8)
\,\varepsilon R_{\mathrm{lo}}$. Then `NLAlib.ShiftedQR.shStep` writes only the matrix and the
flag and, except with probability at most $\varphi$, ends in `NLAlib.ShiftedQR.ShOutcome`: the
flag is $1$ and the matrix is an upper Hessenberg perturbed unitary similarity of $\mathbf{H}$
with error $(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$, decoupled at the bottom (a bottom
subdiagonal entry passes the scan) or with $\psi_k \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$. -/
theorem shStep_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔
        Store.inBlock ww.1 ww.2 1 ⊔ Store.inBlock wp.1 wp.2 1 ⊔
        Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔ Store.inBlock thr.1 thr.2 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {B S ω θ α γ φ C d tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hlen : ss.length = k) (hopt : IsOptimalRitzValues θ H ss) (hθ : 1 ≤ θ) (hd' : 0 < d)
    (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖) (hsH : ∀ s ∈ ss, ‖s‖ ≤ 1.1 * specNorm H)
    (hα : α = (1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : d ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hku : 100000 * k * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hj : LL.length + (excNet ε).length < ns) (hw : k * n ≤ w) (hlgv : ∀ b ∈ [a, s, wg, wr, ww,
      wp, g, thr, f], b.1 ≠ lg.1) :
    PWrites law I (shStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length, w, LL.length] [a, s, wg, wr, ww, wp, g, thr, a,
        f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, s, wg, wr, ww, wp, g, thr, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock s.1 s.2 (2 * k) = some (ss.flatMap fun z => [z.re, z.im]) ∧
        m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
        m.store.get thr.1 thr.2 = some tv ∧ f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f lg
        ns w LL (1 + (excNet ε).length))
      φ := sorry

end Assembly

end NLAlib.ShiftedQR
