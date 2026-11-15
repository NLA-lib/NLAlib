/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedParameters

/-!
# The precision hypotheses of the rounded shifted QR algorithm

[BanksGarzaVargasSrivastava2022, Theorem 6.3, corrected]: the parameter choices of
`NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedParameters` and every
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ meet the parameter and precision hypotheses of
the proved blocks, each listed as a structure in the form the block takes it: Sh (P9) and
Regularize (P10) at condition $4B$, separation $\Gamma/4$ and iterate norm $4\Sigma$, the
worklist (T1) at block norm $2\Sigma$, and the loop's needs (cap, iterate norm, failure split,
scan).

## Main definitions

* `NLAlib.ShiftedQR.ShStepHyps`, `NLAlib.ShiftedQR.RegularizeHyps`,
  `NLAlib.ShiftedQR.SolveRoundedHyps`, `NLAlib.ShiftedQR.ShIterationHyps`.

## Main results

* `NLAlib.ShiftedQR.shStepHyps_of_le_uShQR`, `NLAlib.ShiftedQR.regularizeHyps_of_le_uShQR`,
  `NLAlib.ShiftedQR.solveRoundedHyps_of_le_uShQR`, `NLAlib.ShiftedQR.shIterationHyps_of_le_uShQR`.
* `NLAlib.ShiftedQR.shqrParams_spec`: all four at once (PAR1).
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Real

/-! ### The hypotheses of the blocks

Each structure lists the parameter and precision hypotheses of one proved block in exactly the
form the block takes them, so that a consumer passes the fields. Collected from:
`NLAlib.ShiftedQR.shStep_pwrites` (`RoundedSh.lean`; it discharges those of P4–P8, P15, Find,
Exc, comptau and the chains inside), `NLAlib.ShiftedQR.regularize_pwrites`
(`RoundedRegularize.lean`; P4, P14, Optimal, the chains, `SmallEig`) and
`NLAlib.ShiftedQR.solveRounded_measureReal_not_spectrum_le` (`RoundedHeadline.lean`; C4p, C4,
P1–P3). `NLAlib.ShiftedQR.IsRandomSmallEig.randomLeafContract` (LF1) needs only $\beta \ge 0$. -/

/-- The parameter and precision hypotheses of `NLAlib.ShiftedQR.shStep_pwrites` (P9) other than
the machine, the input matrix and the stored words, for the condition bound `B`, the norm bound
`S`, the threshold `ω`, the factors `θ`, `α`, `γ`, Exc's width `ε`, the failure `φ`, the shift
reach `C`, the separation `d` and the scan threshold word `tv`. The hypotheses that involve
$\psi_k(\mathbf{H})$ are stated for every $\psi \in [\omega, S]$, which the loop's scan
($\omega \le \psi_k$) and $\psi_k \le \|\mathbf{H}\|_2 \le S$ give. -/
structure ShStepHyps (u : ℝ) (n k : ℕ) (B S ω θ α γ ε φ C d tv : ℝ) : Prop where
  /-- The unit roundoff is at most one. -/
  hu1 : u ≤ 1
  /-- The threshold is positive. -/
  hω : 0 < ω
  /-- Optimality factor at least one. -/
  hθ : 1 ≤ θ
  /-- The separation is positive. -/
  hd' : 0 < d
  /-- The promising factor at $k = 2^q$. -/
  hα : ∀ q : ℕ, k = 2 ^ q → α = (1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q)
  /-- The contraction parameter is positive. -/
  hγ : 0 < γ
  /-- The contraction parameter is below one. -/
  hγ1 : γ < 1
  /-- Exc's net width. -/
  hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
    ((k : ℝ) / (k - 1))
  /-- Exc's net width is at most one half. -/
  hε2 : ε ≤ 1 / 2
  /-- The failure is positive. -/
  hφ : 0 < φ
  /-- The failure is at most one fifth. -/
  hφ1 : φ ≤ 1 / 5
  /-- The separation is below Exc's translate scale. -/
  hd : ∀ ψ, ω ≤ ψ → ψ ≤ S → d ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
    ψ) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4
  /-- The shift reach. -/
  hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹)) ≤ C
  /-- The order condition. -/
  hnu : (n + 1 : ℝ) * u ≤ 1 / 2500
  /-- The degree condition. -/
  hku : 100000 * k * u ≤ 1
  /-- Find's half products. -/
  hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k
  /-- The forward error of the chains. -/
  hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
    (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω
  /-- Exc's rounded net. -/
  hexc1 : ∀ ψ, ω ≤ ψ → ψ ≤ S → 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
    B ^ ((k : ℝ)⁻¹) * ψ)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
      B ^ ((k : ℝ)⁻¹) * ψ)
  /-- Exc's rounded translate. -/
  hexc2 : ∀ ψ, ω ≤ ψ → ψ ≤ S → 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
    B ^ ((k : ℝ)⁻¹) * ψ)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
      B ^ ((k : ℝ)⁻¹) * ψ) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8
  /-- The scan threshold word. -/
  hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv

/-- The parameter and precision hypotheses of `NLAlib.ShiftedQR.regularize_pwrites` (P10) other
than the machine, the input matrix and the stored words, for the condition bound `B`, the norm
bound `S`, a lower bound `g` on the separation of the eigenvalues, the threshold `ω`, the
radius `R`, the failure `φ`, `SmallEig`'s forward error `β` and the scan threshold word `tv`. -/
structure RegularizeHyps (u : ℝ) (n k : ℕ) (B S g ω R φ β tv : ℝ) : Prop where
  /-- The unit roundoff is at most one. -/
  hu1 : u ≤ 1
  /-- `SmallEig`'s error is nonnegative. -/
  hβ0 : 0 ≤ β
  /-- The degree condition $B^{2/k} \le 2$. -/
  hBk : B ^ ((2 : ℝ) / k) ≤ 2
  /-- The threshold is positive. -/
  hω : 0 < ω
  /-- The separation exceeds $2\omega^2/S$. -/
  hgap : 2 * ω ^ 2 / S ≤ g
  /-- The radius is positive. -/
  hR : 0 < R
  /-- The failure is positive. -/
  hφ : 0 < φ
  /-- The failure is at most one. -/
  hφ1 : φ ≤ 1
  /-- The translates and their rounding. -/
  hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S)
  /-- The rounding of the translates. -/
  hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))
  /-- The order condition. -/
  hnu : (n + 1 : ℝ) * u ≤ 1 / 2500
  /-- Optimal's test (N14). -/
  huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
    (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k
  /-- Optimal's counts. -/
  huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1
  /-- The chains of the trials. -/
  hxu : 300 * (n + 1) ^ 2 * u ≤
    (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k
  /-- The forward error of the chains. -/
  hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
    √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2
  /-- The scan threshold word. -/
  hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv

/-- The parameter and precision hypotheses of
`NLAlib.ShiftedQR.solveRounded_measureReal_not_spectrum_le` (T1, the worklist) for the condition
bound `B`, the separation `g`, a bound `S` on the input's norm, the target backward error `δ`,
the deflation threshold word `thr`, the cut level `c`, the decoupler's level `ω`, the leaf's
backward error `β`, the decoupler's backward error `e` on blocks of norm at most `N₀`, plus the
headline's $2(n + 1)(c + e + \beta) \le \delta$. -/
structure SolveRoundedHyps (u : ℝ) (n : ℕ) (B g S δ thr c ω β e N₀ : ℝ) : Prop where
  /-- The unit roundoff is nonnegative. -/
  hu : 0 ≤ u
  /-- The unit roundoff is below one. -/
  hu1 : u < 1
  /-- The deflation threshold finds the decoupled entry. -/
  hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr
  /-- The deflation threshold cuts only small entries. -/
  hcut : thr ≤ (1 - u) ^ 2 * c ^ 2
  /-- The cut level is nonnegative. -/
  hc : 0 ≤ c
  /-- The leaf's error is nonnegative. -/
  hβ : 0 ≤ β
  /-- The decoupler's error is nonnegative. -/
  hε0 : 0 ≤ e
  /-- The norm class covers every block. -/
  hN₀ : S + 2 * (n + 1) * (c + e + β) ≤ N₀
  /-- Class preservation. -/
  hsmall : 2 * (n + 1) * (c + e + β) ≤ g / (16 * (n + 1) * B)
  /-- The headline backward error. -/
  hδ : 2 * (n + 1) * (c + e + β) ≤ δ

/-- The parameter facts the iteration loop (P10b, P11d, P11p) needs, for the cap `F`, the
iterate norm bound `S`, the block norm bound `N₀`, the threshold `ω`, the decoupler's level `ωD`,
the scan threshold word `tv`, the decoupler's backward error `e`, the failure budget `φ`,
`SmallEig`'s failure `φse` and the failures `φreg`, `φsh` of Regularize's draws and of Sh: the
cap outlasts the contraction of $\psi_k$; the iterates stay of norm at most `S`; the failures of
$F$ iterations and the leaves of $2(n + 1)$ rounds add up to at most $\varphi$; a passing scan
certifies `ωD`, a failing one certifies $\psi_k > \omega$. -/
structure ShIterationHyps (u : ℝ) (n F : ℕ) (S N₀ ω ωD tv e φ φse φreg φsh : ℝ) : Prop where
  /-- The cap is at least one. -/
  hF : 1 ≤ F
  /-- The cap outlasts the contraction. -/
  hcap : shqrContraction ^ F * S < ω
  /-- The iterates stay in the norm class. -/
  hnorm : N₀ + e ≤ S
  /-- The failures add up to at most $\varphi$. -/
  hfail : ∀ φ', 0 ≤ φ' → φ' ≤ φse → 2 * (n + 1) * (F * (φ' + φreg / 2 + φsh) + φ') ≤ φ
  /-- A passing scan certifies `ωD`. -/
  hdec : ∀ h : ℝ, 0 ≤ h → (1 - u) ^ 2 * h ^ 2 ≤ tv → h ≤ ωD
  /-- A failing scan certifies $\psi_k > \omega$. -/
  hpass : ∀ h : ℝ, 0 ≤ h → tv < (1 + u) ^ 2 * h ^ 2 → ω < h

/-! ### The choices meet the hypotheses (PAR1) -/

section Spec

variable {n k : ℕ} {B Γ S δ φ u : ℝ}

/-- **The parameter choices meet Sh's hypotheses** (P9 at condition $4B$, norm $4\Sigma$): for
$B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$, $k$ the degree of (eqn:setk)
at $4B$ and $0 \le \boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$, the threshold $\omega$, the
global constants, the failure $\varphi/(12F(n + 1))$, the separation $d$ and the scan threshold
word satisfy every parameter and precision hypothesis of `NLAlib.ShiftedQR.shStep_pwrites`. No
printed source. -/
theorem shStepHyps_of_le_uShQR (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) (hu0 : 0 ≤ u)
    (hu : u ≤ uShQR n k B Γ S δ φ) :
    ShStepHyps u n k (4 * B) (4 * S) (shqrOmega n B Γ δ) (shqrTheta k (4 * B))
      (shqrAlpha k (4 * B)) 0.2 (shqrEps k (4 * B)) (shqrSmallEigFailure n B Γ S δ φ)
      (shqrC k (4 * B)) (shqrDist n k B Γ S δ φ) (shqrScanThreshold n k B Γ S δ φ) := by
  have hB1 : 1 ≤ 4 * B := by linarith
  have hB4 : 0 < 4 * B := by linarith
  have hS : 0 < S := hδ.trans_le hδS
  have hk2 : 2 ≤ k := hk ▸ two_le_shqrDegree hB1
  have hk0 : 0 < k := by omega
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have hωS := shqrOmega_le_S (n := n) hB hΓ hδ hδS
  have hd := shqrDist_pos (n := n) hk0 hB hΓ hδ hS hφ
  have hf := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have hε := shqrEps_pos k hB4
  have hlo := shqrRadiusLo_pos k hB4
  have hhi := shqrRadiusHi_pos k hB4
  have hC := shqrC_pos k hB4
  have hF : (1 : ℝ) ≤ shqrCap n B Γ S δ := by exact_mod_cast one_le_shqrCap
  obtain ⟨hnu, hku, -⟩ := counts_of_le_uShQR hu0 hu
  have hSh := hu.trans uShQR_le_uShQRSh
  unfold uShQRSh at hSh
  have s1 := hSh.trans (min_le_left _ _)
  have s2 := hSh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have s3 := hSh.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have s4 := hSh.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hexc : ∀ ψ, ψ ≤ 4 * S → 6 * u * (1.1 * (4 * S) + 3 * (shqrRadiusHi k (4 * B) * ψ)) ≤
      6 * u * (1.1 * (4 * S) + 3 * shqrRadiusHi k (4 * B) * (4 * S)) := by
    intro ψ hψS
    have : shqrRadiusHi k (4 * B) * ψ ≤ shqrRadiusHi k (4 * B) * (4 * S) := by gcongr
    nlinarith
  refine
    { hu1 := hu.trans (uShQR_le_one_div_ten.trans (by norm_num))
      hω := hω
      hθ := one_le_shqrTheta k hB1
      hd' := hd
      hα := fun q hq => by rw [shqrAlpha, hq, Nat.log_pow (by norm_num)]; push_cast; rfl
      hγ := by norm_num
      hγ1 := by norm_num
      hε := rfl
      hε2 := hk ▸ shqrEps_le_half hB1
      hφ := hf
      hφ1 := ?_
      hd := fun ψ hψ _ => ?_
      hC1 := le_rfl
      hnu := hnu
      hku := hku
      hxu := ?_
      hbound := ?_
      hexc1 := fun ψ hψ hψS => ?_
      hexc2 := fun ψ hψ hψS => ?_
      hthrω := ?_ }
  · unfold shqrSmallEigFailure
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  · refine (min_le_right _ _).trans ?_
    change shqrEps k (4 * B) * (shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ) *
        √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4 ≤
      shqrEps k (4 * B) * (shqrRadiusLo k (4 * B) * ψ) *
        √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4
    gcongr
  · rw [le_div_iff₀ (by positivity)] at s1; linarith
  · rw [le_div_iff₀ (by positivity)] at s2; linarith
  · change 6 * u * (1.1 * (4 * S) + 3 * (shqrRadiusHi k (4 * B) * ψ)) ≤
      0.005 * shqrEps k (4 * B) * (shqrRadiusLo k (4 * B) * ψ)
    refine (hexc ψ hψS).trans ?_
    rw [le_div_iff₀ (by positivity)] at s3
    have : shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ ≤
        shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * ψ := by gcongr
    nlinarith
  · change 6 * u * (1.1 * (4 * S) + 3 * (shqrRadiusHi k (4 * B) * ψ)) ≤
      shqrEps k (4 * B) * (shqrRadiusLo k (4 * B) * ψ) *
        √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8
    refine (hexc ψ hψS).trans ?_
    rw [le_div_iff₀ (by positivity)] at s4
    have : shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ *
        √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) ≤
        shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * ψ *
        √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) := by gcongr
    nlinarith
  · unfold shqrScanThreshold
    gcongr

/-- **The parameter choices meet Regularize's hypotheses** (P10 at condition $4B$, norm
$4\Sigma$, separation $\Gamma/4$): under the hypotheses of
`NLAlib.ShiftedQR.shStepHyps_of_le_uShQR`, for a `SmallEig` forward error
$0 \le \beta \le$ `shqrSmallEigAccuracy`, the threshold $\omega$, the radius $R$, the failure
$2\varphi/(12F(n + 1))$ of the draws and the scan threshold word satisfy every parameter and
precision hypothesis of `NLAlib.ShiftedQR.regularize_pwrites`. No printed source. -/
theorem regularizeHyps_of_le_uShQR (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) (hu0 : 0 ≤ u)
    (hu : u ≤ uShQR n k B Γ S δ φ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β ≤ shqrSmallEigAccuracy n B Γ S δ) :
    RegularizeHyps u n k (4 * B) (4 * S) (Γ / 4) (shqrOmega n B Γ δ) (shqrRadius n B Γ S δ)
      (shqrRegularizeFailure n B Γ S δ φ) β (shqrScanThreshold n k B Γ S δ φ) := by
  have hB1 : 1 ≤ 4 * B := by linarith
  have hS : 0 < S := hδ.trans_le hδS
  have hk2 : 2 ≤ k := hk ▸ two_le_shqrDegree hB1
  have hk0 : 0 < k := by omega
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have hωS := shqrOmega_le_S (n := n) hB hΓ hδ hδS
  have hωb := shqrOmega_le_div (n := n) hB hΓ hδ
  have hR := shqrRadius_pos (n := n) hB hΓ hδ hS
  have hη := shqrEta_pos (n := n) hk0 hB hΓ hδ hS hφ
  have hθ := shqrTheta_pos k (by linarith : 0 < 4 * B)
  have hf := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have hF : (1 : ℝ) ≤ shqrCap n B Γ S δ := by exact_mod_cast one_le_shqrCap
  obtain ⟨hnu, -, huo1⟩ := counts_of_le_uShQR hu0 hu
  have hReg := hu.trans uShQR_le_uShQRRegularize
  unfold uShQRRegularize at hReg
  have r1 := hReg.trans (min_le_left _ _)
  have r2 := hReg.trans ((min_le_right _ _).trans (min_le_left _ _))
  have r3 := hReg.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have r4 := hReg.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have r5 := hReg.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hηd : shqrEta n k B Γ S δ φ = shqrRadius n B Γ S δ *
      √(shqrRegularizeFailure n B Γ S δ φ / (2 * k)) := rfl
  rw [hηd] at r2 r4 r5 hη
  have hβR : β ≤ shqrRadius n B Γ S δ := hβ
  -- $R = \omega^2/(8080 \cdot 4\Sigma) \le 4\Sigma/2$
  have hR2 : shqrRadius n B Γ S δ * (8080 * (4 * S)) = shqrOmega n B Γ δ ^ 2 := by
    unfold shqrRadius; field_simp
  have hRS : 2 * shqrRadius n B Γ S δ ≤ 4 * S := by nlinarith
  have hsum : 4 * S + β + shqrRadius n B Γ S δ ≤ 2 * (4 * S) := by linarith
  refine
    { hu1 := hu.trans (uShQR_le_one_div_ten.trans (by norm_num))
      hβ0 := hβ0
      hBk := hk ▸ rpow_two_div_shqrDegree_le hB1
      hω := hω
      hgap := ?_
      hR := hR
      hφ := by unfold shqrRegularizeFailure; positivity
      hφ1 := ?_
      hβ := ?_
      hdη := ?_
      hnu := hnu
      huo := ?_
      huo1 := huo1
      hxu := ?_
      hbound := ?_
      hthrω := by unfold shqrScanThreshold; gcongr }
  · -- $2\omega^2/(4\Sigma) \le \omega/2 \le \Gamma/4$
    have hbΓ := shqrBudget_le_right (n := n) (B := B) (Γ := Γ) (δ := δ)
    have hΓB : Γ / (16 * (n + 1) * B) ≤ Γ / 16 := by
      gcongr
      have : (0 : ℝ) ≤ n := by positivity
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · unfold shqrRegularizeFailure shqrSmallEigFailure
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  · exact add_shqrRadius_add_le hS hsum hu0 r1 hβR
  · have h2 : u * (8 * (4 * S)) ≤ shqrRadius n B Γ S δ *
        √(shqrRegularizeFailure n B Γ S δ φ / (2 * k)) := (le_div_iff₀ (by positivity)).mp r2
    have a1 : 4 * u * (4 * S + β + shqrRadius n B Γ S δ) ≤ 4 * u * (2 * (4 * S)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    linarith
  · rw [le_div_iff₀ (by positivity)] at r3
    have e : (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * (4 * B) ^ 4) ^ ((2 * k : ℝ)⁻¹) *
        shqrOmega n B Γ δ) = shqrTheta k (4 * B) * shqrOmega n B Γ δ := rfl
    rw [e]; linarith
  · rw [le_div_iff₀ (by positivity)] at r4; linarith
  · rw [le_div_iff₀ (by positivity)] at r5; linarith

/-- The cut level is at most $2\omega$: $((1 + v)/(1 - v))^2 \le 2$ for $0 \le v \le 1/10$. -/
theorem shqrCut_le (hu0 : 0 ≤ u) (hu : u ≤ uShQR n k B Γ S δ φ) (hω : 0 ≤ shqrOmega n B Γ δ) :
    shqrCut n k B Γ S δ φ ≤ 2 * shqrOmega n B Γ δ := by
  set v := uShQR n k B Γ S δ φ with hvdef
  have hv0 : 0 ≤ v := hu0.trans hu
  have hv1 : v ≤ 1 / 10 := uShQR_le_one_div_ten
  have e : shqrCut n k B Γ S δ φ = (1 + v) ^ 2 * shqrOmega n B Γ δ / (1 - v) ^ 2 := by
    unfold shqrCut shqrDecoupled
    rw [← hvdef]
    field_simp [show (1 : ℝ) - v ≠ 0 by linarith]
  rw [e, div_le_iff₀ (by nlinarith)]
  have h2 : (1 + v) ^ 2 ≤ 2 * (1 - v) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h2 hω]

/-- **The parameter choices meet the worklist's hypotheses** (T1 with the block norm $2\Sigma$):
under the hypotheses of `NLAlib.ShiftedQR.shStepHyps_of_le_uShQR`, for a leaf error
$0 \le \beta \le$ `shqrSmallEigAccuracy`, the deflation threshold word, the cut level, the
decoupler's level $\omega_D$ and its backward error `shqrDecoupleError` satisfy every parameter
and precision hypothesis of `NLAlib.ShiftedQR.solveRounded_measureReal_not_spectrum_le`, and the
total backward error $2(n + 1)(c + e + \beta)$ is at most $\delta$. No printed source. -/
theorem solveRoundedHyps_of_le_uShQR (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hk : k = shqrDegree (4 * B)) (hu0 : 0 ≤ u) (hu : u ≤ uShQR n k B Γ S δ φ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β ≤ shqrSmallEigAccuracy n B Γ S δ) :
    SolveRoundedHyps u n B Γ S δ (shqrDeflationThreshold n k B Γ S δ φ) (shqrCut n k B Γ S δ φ)
      (shqrDecoupled n k B Γ S δ φ) β (shqrDecoupleError n k B Γ S δ u) (2 * S) := by
  have hS : 0 < S := hδ.trans_le hδS
  have hk0 : 0 < k := by have := hk ▸ two_le_shqrDegree (by linarith : 1 ≤ 4 * B); omega
  set v := uShQR n k B Γ S δ φ with hvdef
  have hv0 : 0 ≤ v := hu0.trans hu
  have hv1 : v ≤ 1 / 10 := uShQR_le_one_div_ten
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have hωS := shqrOmega_le_S (n := n) hB hΓ hδ hδS
  have hb := shqrOmega_mul (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hbδ := shqrBudget_le_left (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hbΓ := shqrBudget_le_right (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hc := shqrCut_le hu0 hu hω.le
  have he := shqrDecoupleError_le hk0 hB hS hu0 hu
  have hωD : 0 ≤ shqrDecoupled n k B Γ S δ φ := by
    unfold shqrDecoupled; rw [← hvdef]
    exact div_nonneg (by positivity) (by linarith)
  have hc0 : 0 ≤ shqrCut n k B Γ S δ φ := by
    unfold shqrCut; rw [← hvdef]
    exact div_nonneg (by positivity) (by linarith)
  have he0 : 0 ≤ shqrDecoupleError n k B Γ S δ u := by
    unfold shqrDecoupleError
    have := shqrC_pos k (by linarith : 0 < 4 * B)
    have : 1 ≤ (1 + 300 * (n + 1) ^ 2 * u) ^ k :=
      one_le_pow₀ (le_add_of_nonneg_right (by positivity))
    have : (0 : ℝ) ≤ shqrCap n B Γ S δ := by positivity
    have : (0 : ℝ) ≤ (3.1 + shqrC k (4 * B)) * (4 * S) := by positivity
    positivity
  -- $\beta \le R \le \omega$
  have hβω : β ≤ shqrOmega n B Γ δ := by
    refine hβ.trans ?_
    change shqrOmega n B Γ δ ^ 2 / (8080 * (4 * S)) ≤ shqrOmega n B Γ δ
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hE : 2 * (n + 1) * (shqrCut n k B Γ S δ φ + shqrDecoupleError n k B Γ S δ u + β) ≤
      shqrBudget n B Γ δ := by
    have h6 : shqrBudget n B Γ δ / (6 * (n + 1)) * (2 * (n + 1)) = shqrBudget n B Γ δ / 3 := by
      field_simp; ring
    nlinarith
  refine
    { hu := hu0
      hu1 := by linarith
      hfind := by unfold shqrDeflationThreshold; rw [← hvdef]; gcongr
      hcut := ?_
      hc := hc0
      hβ := hβ0
      hε0 := he0
      hN₀ := by linarith
      hsmall := hE.trans hbΓ
      hδ := hE.trans hbδ }
  have e : shqrCut n k B Γ S δ φ * (1 - v) = (1 + v) * shqrDecoupled n k B Γ S δ φ := by
    unfold shqrCut; rw [← hvdef]; field_simp [show (1 : ℝ) - v ≠ 0 by linarith]
  unfold shqrDeflationThreshold
  rw [← hvdef]
  have h1 : (1 - v) ^ 2 ≤ (1 - u) ^ 2 := by gcongr; linarith
  calc (1 + v) ^ 2 * shqrDecoupled n k B Γ S δ φ ^ 2
      = (1 - v) ^ 2 * shqrCut n k B Γ S δ φ ^ 2 := by rw [← mul_pow, ← mul_pow, ← e]; ring
    _ ≤ (1 - u) ^ 2 * shqrCut n k B Γ S δ φ ^ 2 := by gcongr

/-- **The parameter choices meet the loop's needs** (P10b, P11d, P11p): under the hypotheses of
`NLAlib.ShiftedQR.shStepHyps_of_le_uShQR`, the cap $F \ge 1$ outlasts the contraction
($0.8016^F \cdot 4\Sigma < \omega$), iterates of a block of norm at most $2\Sigma$ stay of norm at
most $4\Sigma$, the failures (`SmallEig` at most $\varphi/(12F(n + 1))$, the draws twice that,
Sh once) of $F$ iterations and the leaves over $2(n + 1)$ rounds add to at most $\varphi$, and
the scan with the threshold word certifies $\omega_D$ on success and $\psi_k > \omega$ on
failure. No printed source. -/
theorem shIterationHyps_of_le_uShQR (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hk : k = shqrDegree (4 * B)) (hu0 : 0 ≤ u) (hu : u ≤ uShQR n k B Γ S δ φ) :
    ShIterationHyps u n (shqrCap n B Γ S δ) (4 * S) (2 * S) (shqrOmega n B Γ δ)
      (shqrDecoupled n k B Γ S δ φ) (shqrScanThreshold n k B Γ S δ φ)
      (shqrDecoupleError n k B Γ S δ u) φ (shqrSmallEigFailure n B Γ S δ φ)
      (shqrRegularizeFailure n B Γ S δ φ) (shqrSmallEigFailure n B Γ S δ φ) := by
  have hS : 0 < S := hδ.trans_le hδS
  have hk0 : 0 < k := by have := hk ▸ two_le_shqrDegree (by linarith : 1 ≤ 4 * B); omega
  set v := uShQR n k B Γ S δ φ with hvdef
  have hv0 : 0 ≤ v := hu0.trans hu
  have hv1 : v ≤ 1 / 10 := uShQR_le_one_div_ten
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have he := shqrDecoupleError_le hk0 hB hS hu0 hu
  have hbδ := shqrBudget_le_left (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hb := shqrBudget_pos (n := n) hB hΓ hδ
  have hn : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := by positivity
                                  linarith
  have hF : (1 : ℝ) ≤ shqrCap n B Γ S δ := by exact_mod_cast one_le_shqrCap
  refine
    { hF := one_le_shqrCap
      hcap := shqrContraction_pow_shqrCap_mul_lt hB hΓ hδ hS
      hnorm := ?_
      hfail := fun φ' h0 h1 => ?_
      hdec := fun h hh0 hh => ?_
      hpass := fun h hh0 hh => ?_ }
  · have : shqrBudget n B Γ δ / (6 * (n + 1)) ≤ shqrBudget n B Γ δ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · -- $2(n + 1)(3F\varphi_1 + \varphi_1) \le 2\varphi/3$ with $\varphi_1 = \varphi/(12F(n + 1))$
    have e1 : shqrSmallEigFailure n B Γ S δ φ * (12 * shqrCap n B Γ S δ * (n + 1)) = φ := by
      unfold shqrSmallEigFailure; field_simp
    unfold shqrRegularizeFailure
    set φ₁ := shqrSmallEigFailure n B Γ S δ φ
    set F : ℝ := (shqrCap n B Γ S δ : ℝ)
    have hφ₁ : 0 ≤ φ₁ := h0.trans h1
    have a1 : (n + 1) * F * φ' ≤ (n + 1) * F * φ₁ := by gcongr
    have a2 : (n + 1) * φ' ≤ (n + 1) * F * φ₁ := by
      have : (n + 1) * φ' ≤ (n + 1) * φ₁ := by gcongr
      have : (n + 1) * φ₁ * 1 ≤ (n + 1) * φ₁ * F := by gcongr
      linarith
    have e2 : 2 * (n + 1) * (F * (φ' + 2 * φ₁ / 2 + φ₁) + φ') =
        2 * ((n + 1) * F * φ') + 4 * ((n + 1) * F * φ₁) + 2 * ((n + 1) * φ') := by ring
    rw [e2]
    have : (n + 1) * F * φ₁ * 12 = φ := by rw [← e1]; ring
    nlinarith
  · -- $(1 - v)h \le (1 - u)h \le (1 + v)\omega$
    have h1 : (1 - v) * h ≤ (1 - u) * h := by gcongr
    have h2 : ((1 - u) * h) ^ 2 ≤ ((1 + v) * shqrOmega n B Γ δ) ^ 2 := by
      unfold shqrScanThreshold at hh; rw [← hvdef] at hh; nlinarith
    have h3 : (1 - u) * h ≤ (1 + v) * shqrOmega n B Γ δ :=
      (pow_le_pow_iff_left₀ (by nlinarith) (by positivity) two_ne_zero).mp h2
    unfold shqrDecoupled; rw [← hvdef, le_div_iff₀ (by linarith)]
    nlinarith
  · have h1 : (1 + u) ^ 2 * shqrOmega n B Γ δ ^ 2 ≤ shqrScanThreshold n k B Γ S δ φ := by
      unfold shqrScanThreshold; gcongr
    have h2 : shqrOmega n B Γ δ ^ 2 < h ^ 2 := by
      have hp : 0 < (1 + u) ^ 2 := by positivity
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hh0 h2

/-- **The parameter choices of the rounded shifted QR algorithm meet every precision hypothesis**
(PAR1) [BanksGarzaVargasSrivastava2022, Theorem 6.3, corrected]: for $B \ge 1$, $\Gamma > 0$,
$0 < \delta \le \Sigma$, $0 < \varphi \le 1$, $k$ the degree of (eqn:setk) at $4B$,
$0 \le \boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ and a `SmallEig` forward error
$0 \le \beta \le$ `shqrSmallEigAccuracy`, the choices meet the hypotheses of Sh (P9) and
Regularize (P10) at condition $4B$, separation $\Gamma/4$ and iterate norm $4\Sigma$, those of
the worklist (T1) at block norm $2\Sigma$ with total backward error at most $\delta$, and the
loop's (cap, iterate norm, failure split, scan). -/
theorem shqrParams_spec (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) (hu0 : 0 ≤ u) (hu : u ≤ uShQR n k B Γ S δ φ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ shqrSmallEigAccuracy n B Γ S δ) :
    ShStepHyps u n k (4 * B) (4 * S) (shqrOmega n B Γ δ) (shqrTheta k (4 * B))
        (shqrAlpha k (4 * B)) 0.2 (shqrEps k (4 * B)) (shqrSmallEigFailure n B Γ S δ φ)
        (shqrC k (4 * B)) (shqrDist n k B Γ S δ φ) (shqrScanThreshold n k B Γ S δ φ) ∧
      RegularizeHyps u n k (4 * B) (4 * S) (Γ / 4) (shqrOmega n B Γ δ) (shqrRadius n B Γ S δ)
        (shqrRegularizeFailure n B Γ S δ φ) β (shqrScanThreshold n k B Γ S δ φ) ∧
      SolveRoundedHyps u n B Γ S δ (shqrDeflationThreshold n k B Γ S δ φ)
        (shqrCut n k B Γ S δ φ) (shqrDecoupled n k B Γ S δ φ) β
        (shqrDecoupleError n k B Γ S δ u) (2 * S) ∧
      ShIterationHyps u n (shqrCap n B Γ S δ) (4 * S) (2 * S) (shqrOmega n B Γ δ)
        (shqrDecoupled n k B Γ S δ φ) (shqrScanThreshold n k B Γ S δ φ)
        (shqrDecoupleError n k B Γ S δ u) φ (shqrSmallEigFailure n B Γ S δ φ)
        (shqrRegularizeFailure n B Γ S δ φ) (shqrSmallEigFailure n B Γ S δ φ) :=
  ⟨shStepHyps_of_le_uShQR hB hΓ hδ hδS hφ hφ1 hk hu0 hu,
    regularizeHyps_of_le_uShQR hB hΓ hδ hδS hφ hφ1 hk hu0 hu hβ0 hβ,
    solveRoundedHyps_of_le_uShQR hB hΓ hδ hδS hk hu0 hu hβ0 hβ,
    shIterationHyps_of_le_uShQR hB hΓ hδ hδS hφ hk hu0 hu⟩

end Spec

end NLAlib.ShiftedQR
