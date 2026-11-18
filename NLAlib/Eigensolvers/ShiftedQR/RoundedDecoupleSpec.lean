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
        (Nat.log 2 k) ++ qs) {ns ws : ℕ}
    (hns : shqrCap n B Γ S δ * (k + 1 + ps.length) ≤ ns) (hws : k * n ≤ ws) :
    RandomDecouplingRoutineContract law (2 * B) (Γ / 2)
      (shqrCap n B Γ S δ * (φse + shqrRegularizeFailure n B Γ S δ φ / 2 +
        shqrSmallEigFailure n B Γ S δ φ)) k (shqrCap n B Γ S δ) T n (2 * S) ps ns ws
      (shqrDecoupled n k B Γ S δ φ)
      (fun _ => shqrCap n B Γ S δ *
        ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecoupleWith SE) I := sorry
end NLAlib.ShiftedQR
