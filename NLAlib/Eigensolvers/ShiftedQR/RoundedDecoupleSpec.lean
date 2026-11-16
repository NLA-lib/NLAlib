/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecouple
public import NLAlib.Eigensolvers.ShiftedQR.RoundedPrecision
public import NLAlib.Eigensolvers.ShiftedQR.RoundedParameterChoices

/-!
# The rounded decoupling loop at the headline's parameters

[BanksGarzaVargasSrivastava2022, Lemma 6.4 and Theorem 6.3, corrected]: at the parameter choices
of `NLAlib.Eigensolvers.ShiftedQR.RoundedParameters` and every
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$, the rounded decoupling loop
`NLAlib.ShiftedQR.roundedDecouple` meets the randomized decoupling contract that the worklist
takes, on the class of the worklist (condition $2B$, separation $\Gamma/2$), for orders up to
$n + 1$ and norms up to $2\Sigma$. It is
`NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract` with $n_{\max} = n$,
$N_{\max} = 2\Sigma$, iterate norm $4\Sigma$ and class constant $4B$, every hypothesis
discharged at the parameter choices (`NLAlib.ShiftedQR.shqrParams_spec`,
`NLAlib.ShiftedQR.shqrEta_div_two_le`, `NLAlib.ShiftedQR.shqrExc_of_le_uShQR`).

## Main results

* `NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract_of_le_uShQR`: the contract.
* `NLAlib.ShiftedQR.shqrLoopError_le_shqrDecoupleError`: its backward error is at most
  `NLAlib.ShiftedQR.shqrDecoupleError`.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The decoupling loop's backward error is at most `shqrDecoupleError`: for $\Sigma \ge 0$
and $\boldsymbol{u} \ge 0$, $F(1 + C) \cdot 4\Sigma((1 + 300(n + 1)^2\boldsymbol{u})^k - 1) \le
F(3.1 + C) \cdot 4\Sigma((1 + 300(n + 1)^2\boldsymbol{u})^k - 1)$. No printed source. -/
theorem shqrLoopError_le_shqrDecoupleError {n k : ℕ} {B Γ S δ u : ℝ} (hS : 0 ≤ S) (hu0 : 0 ≤ u) :
    shqrCap n B Γ S δ *
      ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) ≤
      shqrDecoupleError n k B Γ S δ u := by
  have hX : 0 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k - 1 := by
    have : 1 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k := one_le_pow₀ (by nlinarith)
    linarith
  unfold shqrDecoupleError
  gcongr
  norm_num

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- Matching the contract's hypotheses, with their long real constants, against the parameter
-- choices is heavy.
omit [Has EigenvalueKernelOp O] in
/-- **The rounded decoupling loop with a small-eigenvalue routine meets the randomized decoupling
contract at the headline's parameters**, with the routine's words `qs` (none, or $12$) after the
words of `NLAlib.ShiftedQR.roundedDecoupleParams` and the routine meeting
`NLAlib.ShiftedQR.RandomSmallEigContractAt` on orders at most $k$ and norms at most $4\Sigma$ (the
iterate norm): the merged statement is the case of the kernel. The rounded decoupling loop meets
the randomized decoupling contract at the headline's parameters ([BanksGarzaVargasSrivastava2022,
Lemma 6.4] in floating point, corrected): on a machine with the standard model at $\boldsymbol{u}
\le \boldsymbol{u}_{\mathrm{ShQR}}$, exact natural literals up to $n + 1$, a measurable
interpretation reading the tape only in its windows, a `SmallEig` kernel on a stream uniform on
$[0, 1]$ with forward error $0 \le \beta \le$ `shqrSmallEigAccuracy` and failure
$\varphi_{\mathrm{se}} \ge 0$, and an exact polar disk sampler on it, for $B \ge 1$, $\Gamma > 0$,
$0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of (eqn:setk) at $4B$, the loop
`NLAlib.ShiftedQR.roundedDecouple` with the words of `NLAlib.ShiftedQR.roundedDecoupleParams` at
the parameter choices of `NLAlib.Eigensolvers.ShiftedQR.RoundedParameters` meets
`NLAlib.ShiftedQR.RandomDecouplingContract` on the class (condition $2B$, separation $\Gamma/2$)
for orders up to $n + 1$ and norms up to $2\Sigma$, with the cap $F$, failure probability
$F(\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi_1)$ ($\varphi_1 = \varphi/(12F(n + 1))$,
$\varphi_R = 2\varphi_1$), the level $\omega_D$ and the backward error $F(1 + C) \cdot 4\Sigma((1 +
300(n + 1)^2\boldsymbol{u})^k - 1)$. No printed source. -/
theorem roundedDecoupleWith_randomDecouplingRoutineContract_of_le_uShQR_at {M : Machine ℝ}
    {I : Interp O Q ℝ} {u : ℝ} (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hS : IsScalar M I) (hM : StdModel u id M)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hDisk : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k : ℕ} {B Γ S δ φ : ℝ} (hB : 1 ≤ B)
    (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hk : k = shqrDegree (4 * B)) (hβ0 : 0 ≤ β) (hβ : β ≤ shqrSmallEigAccuracy n B Γ S δ)
    (hφse : 0 ≤ φse) (hu : u ≤ uShQR n k B Γ S δ φ) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law β φse k 12 T (4 * S) qs SE I)
    (hq12 : qs = [] ∨ qs.length = 12) {ps : List ℝ}
    (hps : ps = roundedDecoupleParams (shqrLoopThreshold n k B Γ S δ φ) (shqrRadius n B Γ S δ)
        (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B) (shqrAlpha k (4 * B)) (shqrEps k (4 * B)) k
        (Nat.log 2 k) ++ qs) :
    RandomDecouplingRoutineContract law (2 * B) (Γ / 2)
      (shqrCap n B Γ S δ * (φse + shqrRegularizeFailure n B Γ S δ φ / 2 +
        shqrSmallEigFailure n B Γ S δ φ)) k (shqrCap n B Γ S δ) T n (2 * S) ps
      (shqrDecoupled n k B Γ S δ φ)
      (fun _ => shqrCap n B Γ S δ *
        ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecoupleWith SE) I := by
  have hu0 := hM.roundoff_nonneg
  obtain ⟨SH, RG, SR, IT⟩ := shqrParams_spec hB hΓ hδ hδS hφ hφ1 hk hu0 hu hβ0 hβ
  have hSp : 0 < S := hδ.trans_le hδS
  have hk2 : 2 ≤ k := hk ▸ two_le_shqrDegree (by linarith)
  have hkq : k = 2 ^ Nat.log 2 k := by
    rw [hk, shqrDegree, Nat.log_pow (by norm_num)]
  have hd := shqrEta_div_two_le (n := n) hB hΓ hδ hδS hφ hk
  have hdist : shqrDist n k B Γ S δ φ = shqrEta n k B Γ S δ φ / 2 := min_eq_left hd
  obtain ⟨hexc1, hexc2⟩ := shqrExc_of_le_uShQR (n := n) (k := k) (Γ := Γ) (φ := φ) hB hδ hδS hu
  have hxu := SH.hxu
  have hbound := SH.hbound
  rw [hdist] at hxu hbound
  obtain ⟨hthr, hcut⟩ := shqrLoopThreshold_spec hu0 hu
  have hv1 : uShQR n k B Γ S δ φ ≤ 1 / 10 := uShQR_le_one_div_ten
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have hωD : 0 ≤ shqrDecoupled n k B Γ S δ φ := by
    unfold shqrDecoupled; exact div_nonneg (mul_nonneg (sq_nonneg _) hω.le) (sq_nonneg _)
  -- the cap: $(1 + u)^2(0.8016^F \cdot 2\Sigma)^2 \le (1 + u)^2\omega^2 \le t \le t_L$
  have htv0 : 0 ≤ shqrScanThreshold n k B Γ S δ φ := by unfold shqrScanThreshold; positivity
  have htL : shqrScanThreshold n k B Γ S δ φ ≤ shqrLoopThreshold n k B Γ S δ φ := by
    have h1 : shqrScanThreshold n k B Γ S δ φ ≤ (1 + u) ^ 2 * shqrScanThreshold n k B Γ S δ φ :=
      le_mul_of_one_le_left htv0 (by nlinarith)
    have hL0 : 0 ≤ shqrLoopThreshold n k B Γ S δ φ := by
      unfold shqrLoopThreshold; positivity
    have h2 : (1 - u) ^ 2 * shqrLoopThreshold n k B Γ S δ φ ≤ shqrLoopThreshold n k B Γ S δ φ :=
      mul_le_of_le_one_left hL0 (by nlinarith)
    linarith
  have hfuel : (1 + u) ^ 2 * ((1.002 * (1 - 0.2)) ^ shqrCap n B Γ S δ * (2 * S)) ^ 2 ≤
      shqrLoopThreshold n k B Γ S δ φ := by
    have hcap := IT.hcap
    unfold shqrContraction at hcap
    have hx0 : 0 ≤ (1.002 * (1 - 0.2) : ℝ) ^ shqrCap n B Γ S δ * (2 * S) := by positivity
    have hx : (1.002 * (1 - 0.2) : ℝ) ^ shqrCap n B Γ S δ * (2 * S) ≤ shqrOmega n B Γ δ := by
      nlinarith
    have := SH.hthrω
    calc (1 + u) ^ 2 * ((1.002 * (1 - 0.2)) ^ shqrCap n B Γ S δ * (2 * S)) ^ 2
        ≤ (1 + u) ^ 2 * shqrOmega n B Γ δ ^ 2 := by gcongr
      _ ≤ _ := this.trans htL
  have hEle := shqrLoopError_le_shqrDecoupleError (n := n) (k := k) (B := B) (Γ := Γ) (δ := δ)
    hSp.le hu0
  have hSN := IT.hnorm
  have he := shqrDecoupleError_le (by omega) hB hSp hu0 hu
  have hbΓ := shqrBudget_le_right (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hsmall : shqrCap n B Γ S δ *
      ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) ≤
      Γ / 2 / (16 * (n + 1) * (2 * B)) := by
    have hn1 : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := by positivity
                                     linarith
    have hG : 0 < Γ / (16 * (n + 1) * B) := by positivity
    have e1 : Γ / 2 / (16 * (n + 1) * (2 * B)) = Γ / (16 * (n + 1) * B) / 4 := by
      field_simp; ring
    have e2 : shqrBudget n B Γ δ / (6 * (n + 1)) ≤ Γ / (16 * (n + 1) * B) / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := shqrBudget_pos (n := n) hB hΓ hδ
      nlinarith
    rw [e1]; linarith
  intro n' N w q f H V d hkn hn hN hHess hnorm hV hHV hκ hgap
  exact roundedDecoupleWith_randomDecouplingRoutineContract_at hI hloc hS hM SR.hu1 hL hNat hC hQ
    hβ0 hφse hDisk hU hkq hk2 hΓ le_rfl (by positivity) RG.hBk RG.hω RG.hgap RG.hR RG.hφ RG.hφ1
    RG.hβ RG.hdη RG.hnu RG.huo RG.huo1 RG.hxu RG.hbound (SH.hα _ hkq) SH.hγ SH.hγ1 SH.hε
    SH.hε2 SH.hφ SH.hφ1 hd SH.hC1 hxu hbound hexc1 hexc2 SH.hthrω hthr hcut hωD hfuel
    (by linarith) hsmall hSE hq12 hps H V d hkn hn hN hHess hnorm hV hHV hκ hgap


-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- Matching the contract's hypotheses, with their long real constants, against the parameter
-- choices is heavy.
/-- **The rounded decoupling loop meets the randomized decoupling contract at the headline's
parameters** ([BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating point, corrected): on a
machine with the standard model at $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$, exact
natural literals up to $n + 1$, a measurable interpretation reading the tape only in its windows,
a `SmallEig` kernel on a stream uniform on $[0, 1]$ with forward error
$0 \le \beta \le$ `shqrSmallEigAccuracy` and failure $\varphi_{\mathrm{se}} \ge 0$, and an exact
polar disk sampler on it, for $B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$ and $k$ the degree of (eqn:setk) at $4B$, the loop
`NLAlib.ShiftedQR.roundedDecouple` with the words of `NLAlib.ShiftedQR.roundedDecoupleParams` at
the parameter choices of `NLAlib.Eigensolvers.ShiftedQR.RoundedParameters` meets
`NLAlib.ShiftedQR.RandomDecouplingContract` on the class (condition $2B$, separation $\Gamma/2$)
for orders up to $n + 1$ and norms up to $2\Sigma$, with the cap $F$, failure probability
$F(\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi_1)$ ($\varphi_1 = \varphi/(12F(n + 1))$,
$\varphi_R = 2\varphi_1$), the level $\omega_D$ and the backward error $F(1 + C) \cdot 4\Sigma((1 +
300(n + 1)^2\boldsymbol{u})^k - 1)$. No printed source. -/
theorem roundedDecouple_randomDecouplingContract_of_le_uShQR {M : Machine ℝ}
    {I : Interp O Q ℝ} {u : ℝ} (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hS : IsScalar M I) (hM : StdModel u id M)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hSE : IsRandomSmallEig law s₀ β φse I) (hDisk : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k : ℕ} {B Γ S δ φ : ℝ} (hB : 1 ≤ B)
    (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hk : k = shqrDegree (4 * B)) (hβ0 : 0 ≤ β) (hβ : β ≤ shqrSmallEigAccuracy n B Γ S δ)
    (hφse : 0 ≤ φse) (hu : u ≤ uShQR n k B Γ S δ φ) :
    RandomDecouplingContract law (2 * B) (Γ / 2)
      (shqrCap n B Γ S δ * (φse + shqrRegularizeFailure n B Γ S δ φ / 2 +
        shqrSmallEigFailure n B Γ S δ φ)) k (shqrCap n B Γ S δ) n (2 * S)
      (roundedDecoupleParams (shqrLoopThreshold n k B Γ S δ φ) (shqrRadius n B Γ S δ)
        (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B) (shqrAlpha k (4 * B)) (shqrEps k (4 * B)) k
        (Nat.log 2 k))
      (shqrDecoupled n k B Γ S δ φ)
      (fun _ => shqrCap n B Γ S δ *
        ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecouple (O := O) (Q := Q)) I := by
  intro n' N w q f H V d hkn hn hN hHess hnorm hV hHV hκ hgap
  unfold roundedDecouple
  exact (roundedDecoupleWith_randomDecouplingRoutineContract_of_le_uShQR_at hI hloc hS hM hL
    hNat hC hQ hDisk hU hB hΓ hδ hδS hφ hφ1 hk hβ0 hβ hφse hu (T := 0)
    (hSE.randomSmallEigContractAt k 12 0 (4 * S) []) (Or.inl rfl) (List.append_nil _).symm
    H V d hkn hn hN hHess hnorm hV hHV hκ hgap).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) fun _ hμ => by simpa [Mem.Live] using hμ.2.2.1

end NLAlib.ShiftedQR
