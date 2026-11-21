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
(`NLAlib.ShiftedQR.shExc_pwrites`) fails with probability at most $\varphi$.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    PWrites law I (shDecide (O := O) (Q := Q))
      (Env.frame [n + 1, k, q, (excNet ε).length] [a, (L, 0), wr, ww, wp, g, thr, (L + 1, 0),
        (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0), (L + 8, 0),
        (L + 9, 0), (L + 10, 0), a, (L + 11, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (ShState3 M u L k ε H V e ss α ((1 - γ) ^ k)
        ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹))) (ε / 2) (1.0015 * (1 - γ)) tv
        a s wg wr ww wp g thr f)
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f)
      φ := by
  have hv' := hv
  obtain ⟨⟨ha, hs, hwg, hwr, hww, hwp, hg, hthl, hfl⟩, -, -⟩ := hv'
  have hψ0 : 0 < hessenbergPotential k H := lt_of_lt_of_le hω hψ
  have hC0 : 0 ≤ C := by
    have : 0 ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) := by
      have : 0 ≤ θ := by linarith
      have : 0 ≤ α := by linarith
      have : 0 ≤ B := le_trans zero_le_one ((one_le_pseudoConditionNumber hV.ne_zero).trans hκ)
      positivity
    linarith
  have hlive : ∀ (l : List (ℕ × ℕ)), (∀ x ∈ l, x.1 < L + 12) → ∀ m,
      ShCtx L k ε H ss ((1 - γ) ^ k) ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹)))
        (ε / 2) (1.0015 * (1 - γ)) tv a s wg wr ww wp g thr f m → m.Live l :=
    fun l hl m hm x hx => by rw [hm.2.2.2.2.2.2.2.2.2.1]; exact hl x hx
  unfold shDecide
  refine (PWrites.ite hI (φ₁ := 0) (φ₂ := φ) ?_ ?_ ?_).mono (fun _ h => h) le_rfl (fun _ h => h)
    (by simp [hφ.le])
  · rintro m ⟨-, r, -, -, H', Rs, -, -, -, ⟨tc, htc, -⟩, hthr⟩
    exact ⟨_, by rw [Interp.testAt_eq rfl rfl, hC.test_lt htc hthr]⟩
  · refine PWrites.of_writes (le_refl 0) fun m τ ⟨hm, ht⟩ => ?_
    refine ((shAccept_writes (τ := τ) hS hM (hNat.mono (by omega)) hk hkn hku hv hH hH0 hV hHV
      hκ hSH hC0 hd' hω hsC hdist hxu16 hbound hγ1.le hthrω hm fun tc htc => ?_).in_frame
      rfl rfl (hlive _ (by simp; omega) m hm.1.1)).mono (by fp_sub) fun _ _ h => h
    obtain ⟨-, r, -, -, H', Rs, -, -, -, -, hthr⟩ := hm
    rw [Interp.testAt_eq rfl rfl, hC.test_lt htc hthr] at ht
    simpa using ht
  · refine ((shExc_pwrites hI hloc hS hM hu1 hL hNat hC hD hU hk hkn hkq hku hv hH hlen hV hHV hκ
      hSH hopt (fun i s hs => hne s hs i) hsH hω hψ hγ hγ1 hθ hα1 hε hε2 hφ hφ1 hd hd' hC1 hexc1
      hexc2 hnu hxu16 hbound hthrω rfl rfl rfl).in_frame rfl rfl fun m hm =>
        hlive _ (by simp; omega) m hm.1).mono (fun m ⟨hm, he⟩ => hm.shExcPre hM hk hkn hku hV hHV
          hne hγ1 hψ0 fun tc htc => ?_) le_rfl (fun _ h => h) le_rfl
    obtain ⟨-, r, -, -, H', Rs, -, -, -, -, hthr⟩ := hm
    rw [Interp.testAt_eq rfl rfl, hC.test_lt htc hthr] at he
    simpa using he

omit [Has DiskSampleOp O] in
/-- The start of `Sh`: from the context `NLAlib.ShiftedQR.ShCtx`, the rounded potential,
`Find` and the computation of the `comptau` test (`NLAlib.ShiftedQR.shPotential_writes`,
`NLAlib.ShiftedQR.shFind_writes`, `NLAlib.ShiftedQR.shTest_writes`) reach
`NLAlib.ShiftedQR.ShState3` with $\alpha = (1.01B)^{4m/2^m}$.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
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
    (hm : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m) :
    Writes .total I τ (shPrefix (O := O) (Q := Q))
      (Env.frame [n + 1, q, k] [a, s, wg, (L, 0), (L + 1, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0),
        (L + 6, 0)])
      (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock L 0 2 ⊔
        (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 6) 0 (2 * k) ⊔
          Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 1))
      (ShState3 M u L k ε H V e ss α cg cr cw cp tv a s wg wr ww wp g thr f) m := by
  have hv' := hv
  obtain ⟨⟨ha, hs', hwg, hwr, hww, hwp, hg, hthl, hfl⟩, -, -⟩ := hv'
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hu0 := hM.roundoff_nonneg
  have hlen' := hm.2.2.2.2.2.2.2.2.2.1
  unfold shPrefix
  refine (shPotential_writes (τ := τ) hS hM hkq hkn (by nlinarith) hv hm).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen']; omega) (by fp_sub) ?_
  intro m₁ hfr₁ hm₁
  have hl₁ : m₁.store.length = L + 12 := by rw [hfr₁.length_eq, hlen']
  have hk2' : ((k / 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.div_le_self k 2
  refine (shFind_writes (τ := τ) hS hM hL hC hQ hNat hkq hkn hv hH hH0 hV hHV hκ hC0 hd hlen hs
    hdist hnu (by nlinarith) hxuF hm₁).frame_seq_le rfl rfl
    (by simp [Mem.Live, hl₁]; omega) (by fp_sub) ?_
  intro m₂ hfr₂ hm₂
  have hl₂ : m₂.store.length = L + 12 := by rw [hfr₂.length_eq, hl₁]
  rw [← hα] at hm₂
  exact ((shTest_writes (τ := τ) hS hM hC (by omega) hkn hv hH hH0 hV hHV hκ hC0 hd hs hdist hnu
    (by nlinarith) hxuT hm₂).in_frame rfl rfl (by simp [Mem.Live, hl₂]; omega)).mono
    (by fp_sub) fun _ _ h => h

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
`NLAlib.ShiftedQR.ShOutcome` except with probability at most $\varphi$.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    PWrites law I (shStepWithScratch (O := O) (Q := Q))
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, s, wg, wr, ww, wp, g, thr, (L, 0),
        (L + 1, 0), (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0),
        (L + 8, 0), (L + 9, 0), (L + 10, 0), (L + 11, 0), a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (ShCtx L k ε H ss ((1 - γ) ^ k) ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹)))
        (ε / 2) (1.0015 * (1 - γ)) tv a s wg wr ww wp g thr f)
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f)
      φ := by
  have hv' := hv
  obtain ⟨⟨ha, hs, hwg, hwr, hww, hwp, hg, hthl, hfl⟩, -, -⟩ := hv'
  have hk0 : 0 < k := by omega
  have hψ0 : 0 < hessenbergPotential k H := lt_of_lt_of_le hω hψ
  have hHp : 0 < specNorm H := hψ0.trans_le (hessenbergPotential_le_specNorm hk0 hkn H)
  have hH0 : H ≠ 0 := fun h0 => by rw [h0, specNorm_zero] at hHp; exact lt_irrefl 0 hHp
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hα1 : 1 ≤ α := hα ▸ Real.one_le_rpow (by linarith) (by positivity)
  have hC0 : (1.1 : ℝ) ≤ C := by
    have : 0 ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) := by
      have : 0 ≤ θ := by linarith
      have : 0 ≤ α := by linarith
      positivity
    linarith
  have hsC : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H := fun s hs =>
    (hsH s hs).trans (mul_le_mul_of_nonneg_right hC0 hHp.le)
  have hne : ∀ r ∈ ss, ∀ i, e i ≠ r := fun r hr i he => by
    have := hdist r hr i; rw [he, sub_self, norm_zero] at this; linarith
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ ∈ ss := List.exists_mem_of_length_pos (by omega)
  have hdH : d ≤ (2 + 2 * C) * specNorm H := by
    have h1 := hdist s₁ hs₁ 0
    have h2 := norm_sub_le (e 0) s₁
    have h3 := norm_le_specNorm_of_mul_eq_mul_diagonal hV hHV 0
    nlinarith [hsC s₁ hs₁]
  obtain ⟨hxuT, hxuF, hxu16⟩ := shPrecision_forms hHp hSH (by linarith) hd' (by linarith) hdH hxu
  unfold shStepWithScratch
  refine (PWrites.seq hI hloc (φ₁ := 0) (φ₂ := φ) hφ.le (PWrites.of_writes le_rfl
    fun m τ hm => (shPrefix_writes (τ := τ) hS hM hL hC hQ hNat hkq hk hkn hv hH hH0 hV hHV hκ
      (by linarith) hd' hlen hsC hdist hα hnu hku hxuT hxuF hm).in_frame rfl rfl
      (by simp [Mem.Live, hm.2.2.2.2.2.2.2.2.2.1]; omega))
    ((shDecide_pwrites hI hloc hS hM hu1 hL hNat hC hD hU hkq hk hkn hv hH hH0 hV hHV hκ hSH hω hψ
      hlen hopt hθ hd' hdist hsH hsC hne hα1 hγ hγ1 hε hε2 hφ hφ1 hd hC1 hnu hku hxu16 hbound hexc1
      hexc2 hthrω).in_frame rfl rfl fun m hm => by
        simp [Mem.Live, hm.1.1.2.2.2.2.2.2.2.2.2.1]; omega)).mono (fun _ h => h)
    (sup_le (sup_le (sup_le (Fp.inBlock_le_sup_above (by omega)) (Fp.inBlock_le_sup_above le_rfl))
      (sup_le (sup_le (sup_le (Fp.inBlock_le_sup_above (by omega))
        (Fp.inBlock_le_sup_above (by omega))) (Fp.inBlock_le_sup_above (by omega)))
        (Fp.inBlock_le_sup_above (by omega)))) le_rfl) (fun _ h => h) (by simp)

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
subdiagonal entry passes the scan) or with $\psi_k \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    PWrites law I (shStep (O := O) (Q := Q))
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, s, wg, wr, ww, wp, g, thr, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m => m.Live [a, s, wg, wr, ww, wp, g, thr, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock s.1 s.2 (2 * k) = some (ss.flatMap fun z => [z.re, z.im]) ∧
        m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
        m.store.get thr.1 thr.2 = some tv ∧ f.2 < m.store.len f.1)
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f)
      φ := by
  have e : (shStep (O := O) (Q := Q)) = Stmt.allocs [.const 2, .const 1, .const 1,
      .const 1, .const 1, .const 2 * (.var 0 * .var 0), .const 2 * .var 2, .const 2 * .var 2,
      .const 5, .const 1, .const 2 * .var 3, .const 1]
      (.frame [.var 0, .var 1, .var 2, .var 3] [⟨0, .var 4⟩, ⟨1, .var 5⟩, ⟨2, .var 6⟩,
        ⟨3, .var 7⟩, ⟨4, .var 8⟩, ⟨5, .var 9⟩, ⟨6, .var 10⟩, ⟨7, .var 11⟩, ⟨10, .const 0⟩,
        ⟨11, .const 0⟩, ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨14, .const 0⟩, ⟨15, .const 0⟩,
        ⟨16, .const 0⟩, ⟨17, .const 0⟩, ⟨18, .const 0⟩, ⟨19, .const 0⟩, ⟨20, .const 0⟩,
        ⟨21, .const 0⟩, ⟨0, .var 4⟩, ⟨9, .var 13⟩]
        (shStepWithScratch (O := O) (Q := Q))) := rfl
  rw [e]
  refine PWrites.allocs rfl (Pre₁ := fun L μ => ShViews L n k ε a s wg wr ww wp g thr f ∧
    ShCtx L k ε H ss ((1 - γ) ^ k) ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹))) (ε / 2)
      (1.0015 * (1 - γ)) tv a s wg wr ww wp g thr f μ) ?_ ?_ fun L => ?_
  · rintro m s₁ ⟨hl, hA, hs, hwg, hwr, hww, hwp, hg, hthr, hrf⟩ hlen hlens hBelow
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ : a.1 < m.store.length ∧ s.1 < m.store.length ∧
        wg.1 < m.store.length ∧ wr.1 < m.store.length ∧ ww.1 < m.store.length ∧
        wp.1 < m.store.length ∧ g.1 < m.store.length ∧ thr.1 < m.store.length ∧
        f.1 < m.store.length := by simpa [Mem.Live] using hl
    have hl12 := fun i (hi : i < 12) => hlens i (by simpa using hi)
    refine ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, haf, hio⟩, hA.of_below hBelow h1,
      hBelow.readBlock_of h2 hs, hBelow.get_of h3 hwg, hBelow.get_of h4 hwr, hBelow.get_of h5 hww,
      hBelow.get_of h6 hwp, hBelow.readBlock_of h7 hg, hBelow.get_of h8 hthr,
      by rw [(hBelow f.1 h9).1]; exact hrf, by simpa using hlen, ?_⟩
    simpa using ⟨hl12 0 (by norm_num), hl12 1 (by norm_num), hl12 2 (by norm_num),
      hl12 3 (by norm_num), hl12 4 (by norm_num), hl12 5 (by norm_num), hl12 6 (by norm_num),
      hl12 7 (by norm_num), hl12 8 (by norm_num), hl12 9 (by norm_num), hl12 10 (by norm_num),
      hl12 11 (by norm_num)⟩
  · rintro m ⟨hl, -⟩ st st' p hBelow ⟨hF, H', hsim, hH', hA, hdec⟩
    have hlv : a.1 < m.store.length ∧ f.1 < m.store.length := by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hl
      exact ⟨hl.1, hl.2.2.2.2.2.2.2.2⟩
    exact ⟨hBelow.get_of hlv.2 hF, H', hsim, hH', hA.of_below hBelow hlv.1, hdec⟩
  · by_cases hvL : ShViews L n k ε a s wg wr ww wp g thr f
    · refine ((shStepWithScratch_pwrites hI hloc hS hM hu1 hL hNat hC hQ hD hU hkq hk hkn hvL hH hV
        hHV hκ hSH hω hψ hlen hopt hθ hd' hdist hsH hα hγ hγ1 hε hε2 hφ hφ1 hd hC1 hnu hku hxu
        hbound hexc1 hexc2 hthrω).in_frame rfl rfl ?_).mono (fun _ h => h.2) (by fp_sub)
        (fun _ h => h) le_rfl
      rintro μ ⟨-, -, -, -, -, -, -, -, -, hlen, -⟩
      obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, -⟩ := hvL
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, hlen]
      omega
    · exact PWrites.of_writes hφ.le fun _ _ h => absurd h.1 hvL

end Assembly

end NLAlib.ShiftedQR
