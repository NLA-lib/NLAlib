/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.DenseParameters

/-!
# A dense Schur solver

The dense Schur pipeline (`NLAlib.Schur.schurPipelineWith`) with the rounded Frobenius norm
(`NLAlib.Schur.frobNormStage`), the Ginibre regularizer (`NLAlib.SmallEig.ginibrePerturb`), the
bottom-up Hessenberg reduction with its accumulated unitary (`NLAlib.hessenbergReduceQ`) and the
rounded shifted QR algorithm of [BanksGarzaVargasSrivastava2022] as the Schur core
(`NLAlib.ShiftedQR.roundedShQRSchurWith`). The core's small-block Schur solver is a parameter: with
any solver meeting `NLAlib.Schur.RandomSchurLeafContract` (an oracle) the program is
`NLAlib.Schur.denseSchurWith`; with the small-eigenvalue program of
[BanksGarzaVargasSrivastava2025] (`NLAlib.SmallEig.smallEigProg`) it is `NLAlib.Schur.denseSchur`,
with no oracle.

For every complex $\mathbf{A}$ of order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$, at a
unit roundoff $\boldsymbol{u} \le \boldsymbol{u}_0(n, \delta, \varphi)$ with
$\log_2(1/\boldsymbol{u}_0) = O(L^4\log^2 L)$, $L = \log_2(4(n + 1)/(\delta\varphi))$, the run
stores, except with probability $\varphi$, the flag $0$ and words $\widehat{\mathbf{U}}$,
$\widehat{\mathbf{T}}$ with $\widehat{\mathbf{T}}$ exactly upper triangular,
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$ and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
\mathbf{I}\|_2 \le 58R\boldsymbol{u} \le \delta$; the orthogonality holds on every tape. The
papers compute eigenvalues only; Part I's introduction ([BanksGarzaVargasSrivastava2021]) says
the Schur form "can be obtained directly"; here it is proved.

The parameters (`NLAlib.Eigensolvers.Schur.DenseParameters`) depend on $(n, \delta, \varphi)$
only. With $\delta' = \delta/(16\sqrt{n + 1})$:
the regularizer at the words `NLAlib.SmallEig.smallEigParams` for the order $n + 1$, the norm
bound $4$, the error $\delta'$ and the failure $\varphi/2$, into the class $(B, \Gamma) =
(2/t_2, t_1/2)$; the core at the class $(2B, \Gamma/2)$, the norm bound $8$, the error $\delta'$
and the failure $\varphi/2$. The norm estimate is taken with the constants $(1/2, 2)$.

## Main definitions

* `NLAlib.Schur.denseSchurWith`, `NLAlib.Schur.denseSchur`: the programs.

## Main results

* `NLAlib.Schur.denseSchurWith_measureReal_not_schur_le`: the dense Schur theorem with any
  small-block Schur solver.
* `NLAlib.Schur.denseSchur_measureReal_not_schur_le`: the dense Schur theorem.
* `NLAlib.Schur.denseSchurAt_measureReal_not_regularizedSchur_le`: the same at two tolerances,
  with the regularized matrix exposed.
* `NLAlib.Schur.denseSchur_terminates`: termination and orthogonality on every tape.
* `NLAlib.Schur.denseSchur_measureReal_not_spectrum_le`,
  `NLAlib.Schur.denseSchur_measureReal_not_exact_schur_le`: the eigenvalues, and an exact unitary.
* `NLAlib.Schur.denseSchur_work_le`: the operation count; its polylogarithmic form and the bits
  of precision are in `NLAlib.Eigensolvers.Schur.DenseBits`.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory ProbabilityTheory ShiftedQR SmallEig
open scoped Matrix

/-! ### The programs -/

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The dense Schur solver with a small-block Schur solver `L`**: the pipeline
`NLAlib.Schur.schurPipelineWith` with the rounded Frobenius norm, the Ginibre regularizer on the
Gaussian stream `sG`, the bottom-up Hessenberg reduction with its accumulated unitary and the
rounded shifted QR algorithm with the leaf `L` as the Schur core. The interface is
`[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`.
Algorithm: dense-schur -/
def denseSchurWith (sG : ℕ) (L : Impl O Q) : Impl O Q :=
  schurPipelineWith (frobNormStage (O := O) (Q := Q)) (ginibrePerturb (O := O) (Q := Q) sG)
    (hessenbergReduceQ (O := O) (Q := Q)) (roundedShQRSchurWith L)

/-- **The dense Schur solver**: `NLAlib.Schur.denseSchurWith` with the small-eigenvalue program
`NLAlib.SmallEig.smallEigProg` as the leaf, on the Gaussian stream `sG`. No oracle. The interface
is `[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`.
Algorithm: dense-schur -/
def denseSchur (sG : ℕ) : Impl O Q :=
  denseSchurWith sG (smallEigProg (O := O) (Q := Q) sG)

end Program

/-! ### The theorems -/

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

-- The four stage contracts at their long parameters make the elaboration heavy.
set_option maxHeartbeats 1000000 in
-- (heavy elaboration, see above)
/-- **The dense Schur theorem with any small-block Schur solver.** Let the machine have the
standard model at $\boldsymbol{u}$, index literals, exact natural literals up to $n + 1$, exact
`toNat` and comparisons, a measurable interpretation reading the tape only in its windows whose
draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on
it and a stream $s_G$ with the standard real Gaussian law. Let $0 < \delta \le 1$,
$0 < \varphi \le 1$ and $k$ the shift degree. Let the leaf `L` be a randomized small-block Schur
solver on the orders at most $\min(k, n + 1)$ and norms at most $32$ with the cap $T$ and $12$
words `qs`: except with probability $\varphi_L$ it stores an upper triangular $\mathbf{T}_b$ and
an accumulator $\mathbf{U}_b$ with $\|\mathbf{U}_b - \mathbf{V}_b\|_2 \le \varepsilon_L$ and
$\mathbf{T}_b = \mathbf{V}_b^{\mathsf H}(\mathbf{B} + \mathbf{F})\mathbf{V}_b$ for an exact
unitary $\mathbf{V}_b$ and $\|\mathbf{F}\|_2 \le \beta_L$; let
$0 \le \varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$, $0 \le \beta_L \le \beta_0$,
$0 \le \varphi_L \le \varphi_0$ and $\boldsymbol{u} \le \boldsymbol{u}_0$. Then for every complex
$\mathbf{A}$ of order $n + 1$, from a memory holding $\mathbf{A}$ and the words of
`denseSchurParamsWith` with `qs`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{denseSchurWith}_L(\mathbf{A}) \text{ fails, or writes outside
  } \mathbf{A}, \widehat{\mathbf{U}} \text{ and the flag, or stores no flag } 0 \text{ and }
  \widehat{\mathbf{U}}, \widehat{\mathbf{T}} \text{ with } \widehat{\mathbf{T}} \text{ upper
  triangular},\ \|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}
  \widehat{\mathbf{U}}^{\mathsf H}\|_2 \le \delta\|\mathbf{A}\|_2,\
  \|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}
  \bigr] \le \varphi\,.$$
Here $k$ is `NLAlib.Schur.denseSchurDegree`, $\beta_0$ is `NLAlib.Schur.denseSchurLeafAccuracy`,
$\varphi_0$ is `NLAlib.Schur.denseSchurLeafFailure`, $\boldsymbol{u}_0$ is
`NLAlib.Schur.uDenseSchurWith` and $R$ is `NLAlib.Schur.denseSchurRotationsWith`, at $R_L$ and
the core's word count. No printed source: [BanksGarzaVargasSrivastava2022, Theorem 6.3] computes
eigenvalues only, with an eigenvalue oracle.

Note: The leaf is a hypothesis, `NLAlib.Schur.RandomSchurLeafContract`: this is the dense Schur
solver with a small-block Schur oracle, any solver meeting the contract. The stages compose by the
generic composition theorem `NLAlib.Schur.schurPipelineWith_measureReal_not_schur_le`, the core by
`NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`, the reducer by
`NLAlib.hessenbergReduceQ_hessenbergReducerContract`, the regularizer by
`NLAlib.Schur.ginibrePerturb_randomRegularizerContract` and the norm by
`NLAlib.Schur.frobNormStage_frobNormEstimateContract`. The instance with `SmallEig` is
`NLAlib.Schur.denseSchur_measureReal_not_schur_le`.
Result: dense-schur-small-block-oracle -/
theorem denseSchurWith_measureReal_not_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) {εL βL φL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : RandomSchurLeafContract law εL βL φL (min (denseSchurDegree n δ φ) (n + 1)) 32 qs T
      L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ denseSchurLeafAccuracy n δ φ) (hφL0 : 0 ≤ φL)
    (hφL : φL ≤ denseSchurLeafFailure n δ φ)
    (hu : u ≤ uDenseSchurWith n δ φ (denseSchurShQRParams n δ φ ++ qs).length RL)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (denseSchurParamsWith n δ φ qs) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (denseSchurWith (O := O) (Q := Q) sG L).body
      (Env.frame (denseSchurDimsWith n δ φ qs T) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOutput a uo f A δ
        (58 * denseSchurRotationsWith n δ φ (denseSchurShQRParams n δ φ ++ qs).length RL * u))
      μ} ≤ φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hd0, hd1, hg, hc, hc1, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hu1, hu2, hu3, hu4, -, hu6, -, hu8⟩ := le_of_le_uDenseSchurWith hu
  obtain ⟨-, -, hR⟩ := mul_denseSchurRotationsWith_le hδ hδ1 hu
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  set np := (denseSchurShQRParams n δ φ ++ qs).length
  set Rc := shqrSchurRotations n (denseSchurDegree n δ φ) np (denseSchurCap n δ φ) RL
  obtain ⟨hε0, hε16, hεU, hεA⟩ := denseSchur_errors_le (Rc := Rc) hδ hu0 hR hu2 hu8 hδ1
  have hN : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  have hN2 : ((n : ℝ) + 1) ^ 2 * u ≤ 1 / 51200 := by
    rw [le_div_iff₀ (by positivity)] at hu2
    have : denseSchurDelta n δ ≤ 1 / 16 := hd1
    nlinarith
  -- the four contracts
  have hNm : FrobNormEstimateContract (1 / 2) 2 (n + 1) (frobNormStage (O := O) (Q := Q)) I :=
    frobNormStage_frobNormEstimateContract_half hS hM (by rw [hN]; nlinarith)
  have hReg : RandomRegularizerContract law (denseSchurDelta n δ / 2) (3 * (φ / 2) / 4)
      (fun A => IsConditionedDiagonalizable (denseSchurB n δ φ) (denseSchurΓ n δ φ) A) (n + 1)
      (2 / (1 / 2)) (denseSchurRegParams n δ φ) (ginibrePerturb (O := O) (Q := Q) sG) I := by
    rw [show (2 : ℝ) / (1 / 2) = 4 by norm_num]
    exact ginibrePerturb_randomRegularizerContract hS hM hL hSmp hG
      boundsGinibreGap_ginibreGapTail boundsGinibreCondition_ginibreConditionTail
      ginibreGapTail_b_pos ginibreConditionTail_b_pos hd0 (by linarith) (half_pos hφ)
      (by linarith) hu1
  have hRed : HessenbergReducerContract (27 * (((n + 1 : ℕ)) : ℝ) ^ 2 * u)
      (50 * (((n + 1 : ℕ)) : ℝ) ^ 2 * u) (n + 1) (hessenbergReduceQ (O := O) (Q := Q)) I :=
    hessenbergReduceQ_hessenbergReducerContract hS hM hC hQ hL hNat (by omega)
      (by rw [hN]; nlinarith)
  have hLeaf' : Schur.RandomSchurLeafContract law εL βL φL
      (min (denseSchurDegree n δ φ) (n + 1)) (4 * 8) qs T L I := by
    rw [show (4 : ℝ) * 8 = 32 by norm_num]; exact hLeaf
  have hCore : RandomSchurCoreContract law ((1 + 24 * u) ^ Rc - 1) (denseSchurDelta n δ) (φ / 2)
      (fun H => IsConditionedDiagonalizable (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) H)
      (denseSchurDegree n δ φ) (denseSchurCap n δ φ) T (n + 1) (4 / (1 / 2))
      (denseSchurThreshold n δ φ :: (denseSchurShQRParams n δ φ ++ qs))
      (roundedShQRSchurWith L) I := by
    rw [show (4 : ℝ) / (1 / 2) = 8 by norm_num]
    exact roundedShQRSchurWith_randomSchurCoreContract hS hM hL hNat hQ hC hI hloc hDisk hU
      (by linarith) (half_pos hΓ) hd0 (by linarith) (half_pos hφ) (by linarith) rfl hLeaf' hqs
      hεL hεLR hβL0 (by rw [show (4 : ℝ) * 8 = 32 by norm_num]; exact hβL) hφL0 hφL hu4 hu6
  have hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      IsConditionedDiagonalizable (denseSchurB n δ φ) (denseSchurΓ n δ φ) A →
      IsPerturbedUnitarySimilarBy V A H
        (50 * (((n + 1 : ℕ) : ℝ)) ^ 2 * u * (2 / (1 / 2) + denseSchurDelta n δ / 2)) →
      IsConditionedDiagonalizable (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) H :=
    fun A H V hA hV => hA.of_isPerturbedUnitarySimilarBy hΓ hV (by
      rw [hN]
      set g := smallEigGap (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail
      set c := smallEigCond (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreConditionTail
      set N : ℝ := (n : ℝ) + 1 with hNdef
      have hN1 : 1 ≤ N := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      have hu3' : u * (28800 * N ^ 3) ≤ g * c := (le_div_iff₀ (by positivity)).mp hu3
      have e : denseSchurΓ n δ φ / (16 * N * denseSchurB n δ φ) = g * c / (64 * N) := by
        unfold denseSchurΓ denseSchurB; field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      have hN3 : N ^ 3 * u * (4 + denseSchurDelta n δ / 2) ≤ N ^ 3 * u * (4 + 1 / 32) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith)
  have h := schurPipelineWith_measureReal_not_schur_le (c₁ := 1 / 2) (c₂ := 2) hS hM hL hNat
    hC hI hloc hNm hReg hRed hCore hCC' (by norm_num) hu0
    (by rw [le_div_iff₀ (by positivity)] at hu8; nlinarith) (by linarith) (by positivity)
    (by rw [hN]; nlinarith) (by positivity)
    (by have := one_le_pow₀ (n := Rc) (by linarith : (1 : ℝ) ≤ 1 + 24 * u); linarith)
    (by rw [hN, show (1 : ℝ) + ((1 + 24 * u) ^ Rc - 1) = (1 + 24 * u) ^ Rc by ring]; exact hε16)
    (by positivity) (by positivity) hin hξ
  have e1 : (1 : ℝ) + ((1 + 24 * u) ^ Rc - 1) = (1 + 24 * u) ^ Rc := by ring
  rw [hN, e1] at h
  refine (measureReal_mono ?_).trans (h.trans (by linarith))
  intro ω hω hs
  exact hω (hs.mono le_rfl fun μ' _ hout => hout.mono hεA hεU)

/-- **The dense Schur theorem.** Let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_0$, index literals, exact natural literals up to $n + 1$,
exact `toNat` and comparisons, a measurable interpretation reading the tape only in its windows
whose draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk
sampler on it and a stream $s_G$ with the standard real Gaussian law. Let $0 < \delta \le 1$ and
$0 < \varphi \le 1$. Then for every complex $\mathbf{A}$ of order $n + 1$, from a memory holding
$\mathbf{A}$ and the words of `denseSchurParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{denseSchur}(\mathbf{A}) \text{ fails, or writes outside }
  \mathbf{A}, \widehat{\mathbf{U}} \text{ and the flag, or stores no flag } 0 \text{ and }
  \widehat{\mathbf{U}}, \widehat{\mathbf{T}} \text{ with } \widehat{\mathbf{T}} \text{ upper
  triangular},\ \|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}
  \widehat{\mathbf{U}}^{\mathsf H}\|_2 \le \delta\|\mathbf{A}\|_2,\
  \|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}
  \bigr] \le \varphi\,.$$
Here $\boldsymbol{u}_0$ is `NLAlib.Schur.uDenseSchur` and $R$ is
`NLAlib.Schur.denseSchurRotations`; $58R\boldsymbol{u} \le \delta$
(`NLAlib.Schur.mul_denseSchurRotations_le`).
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1];
there only the eigenvalues are computed. No hypothesis on $\mathbf{A}$.

Note: General form, any small-block Schur solver:
`NLAlib.Schur.denseSchurWith_measureReal_not_schur_le`, with the leaf contract of
`NLAlib.SmallEig.smallEigProg_randomSchurLeafContract`. The run terminates on every tape, with the
orthogonality bound whatever the tape (`NLAlib.Schur.denseSchur_terminates`). For
$\mathbf{A} = 0$ the norm estimate is $0$ and the run stores $\widehat{\mathbf{U}} = \mathbf{I}$.
Result: dense-schur-backward-error -/
theorem denseSchur_measureReal_not_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uDenseSchur n δ φ)
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ} (hin : SchurPipelineInput (denseSchurParams n δ φ) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n δ φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOutput a uo f A δ (58 * denseSchurRotations n δ φ * u)) μ} ≤ φ := by
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  have hβ := shqrSmallEigAccuracy_pos (n := n) hB1 (half_pos hΓ) hd0 (by norm_num : (0 : ℝ) < 8)
  have hβS := shqrSmallEigAccuracy_le (n := n) hB1 (half_pos hΓ) hd0
    (by linarith : denseSchurDelta n δ ≤ 8)
  have hφL := shqrSmallEigFailure_pos (n := n) (B := 2 * denseSchurB n δ φ)
    (Γ := denseSchurΓ n δ φ / 2) (S := 8) (δ := denseSchurDelta n δ) (half_pos hφ)
  have hφL1 := shqrSmallEigFailure_le (n := n) (B := 2 * denseSchurB n δ φ)
    (Γ := denseSchurΓ n δ φ / 2) (S := 8) (δ := denseSchurDelta n δ) (half_pos hφ).le
  have hLeaf : RandomSchurLeafContract law
      ((1 + 24 * u) ^ smallEigLeafRotations (denseSchurDegree n δ φ)
        (smallEigForwardCap (denseSchurDegree n δ φ) 32
          (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
            (denseSchurDelta n δ)) (denseSchurLeafFailure n δ φ) ginibreGapTail
          ginibreConditionTail) - 1)
      (forwardBackwardError (denseSchurDegree n δ φ) 32
        (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
          (denseSchurDelta n δ)))
      (denseSchurLeafFailure n δ φ) (min (denseSchurDegree n δ φ) (n + 1)) 32
      (denseSchurLeafParams n δ φ) (smallEigForwardCap (denseSchurDegree n δ φ) 32
          (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
            (denseSchurDelta n δ)) (denseSchurLeafFailure n δ φ) ginibreGapTail
          ginibreConditionTail) (smallEigProg (O := O) (Q := Q) sG) I :=
    SmallEig.smallEigProg_randomSchurLeafContract (O := O) (Q := Q) hS hM hL
    (dmax := min (denseSchurDegree n δ φ) (n + 1)) (min_le_left _ _)
    (hNat.mono (min_le_right _ _)) hQ hC hI hloc hSmp hDisk hU hG
    boundsGinibreGap_ginibreGapTail boundsGinibreCondition_ginibreConditionTail
    ginibreGapTail_b_pos ginibreConditionTail_b_pos hβ (by linarith : _ ≤ (32 : ℝ)) hφL
    (by linarith) (hu.trans (min_le_right _ _))
  rw [← denseSchurLeafCap_eq] at hLeaf
  have hR0 : 0 ≤ (1 + 24 * u) ^ smallEigLeafRotations (denseSchurDegree n δ φ)
      (denseSchurLeafCap n δ φ) - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := smallEigLeafRotations (denseSchurDegree n δ φ)
      (denseSchurLeafCap n δ φ)) (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
    linarith
  obtain ⟨hb0, -, -⟩ := forwardBackwardError_spec (kmax := denseSchurDegree n δ φ) hβ
    (by linarith : _ ≤ (32 : ℝ))
  exact denseSchurWith_measureReal_not_schur_le hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hδ
    hδ1 hφ hφ1 hLeaf (SmallEig.length_smallEigParams _ _ _ _ _ _) hR0 le_rfl hb0.le le_rfl
    hφL.le le_rfl (hu.trans (min_le_left _ _)) hin hξ

/-- **The dense Schur solver terminates on every tape**, at any $\delta$ and $\varphi$, on a
scalar machine with the standard model at $\boldsymbol{u}$, $400(n + 1)^2\boldsymbol{u} \le 1$,
index literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, draws that
store the tape entry and an exact polar disk sampler: the run of `denseSchur` from a memory
holding $\mathbf{A}$ and the words of `denseSchurParams` writes only $\mathbf{A}$,
$\widehat{\mathbf{U}}$ and the flag, and stores a matrix in the block of $\mathbf{A}$ and
$\widehat{\mathbf{U}}$ with
$\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 2\varepsilon +
\varepsilon^2$, $\varepsilon = (1 + 27(n + 1)^2\boldsymbol{u})(1 + 24\boldsymbol{u})^{R_c} - 1$,
$R_c$ the rotation count of the core. -/
theorem denseSchur_writes_orth {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ}
    (hu : 400 * ((n : ℝ) + 1) ^ 2 * u ≤ 1) {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (denseSchurParams n δ φ) a p uo f A μ) (τ : Tape ℝ) :
    Writes .total I τ (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n δ φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOrth (n := n) a uo
        (2 * ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ shqrSchurRotations n
          (denseSchurDegree n δ φ) (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length
          (denseSchurCap n δ φ) (smallEigLeafRotations (denseSchurDegree n δ φ)
            (denseSchurLeafCap n δ φ)) - 1) +
         ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ shqrSchurRotations n
          (denseSchurDegree n δ φ) (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length
          (denseSchurCap n δ φ) (smallEigLeafRotations (denseSchurDegree n δ φ)
            (denseSchurLeafCap n δ φ)) - 1) ^ 2)) μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  set Rc := shqrSchurRotations n (denseSchurDegree n δ φ)
    (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length (denseSchurCap n δ φ)
    (smallEigLeafRotations (denseSchurDegree n δ φ) (denseSchurLeafCap n δ φ))
  have hN : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hN2 : ((n : ℝ) + 1) ^ 2 * u ≤ 1 / 400 := by linarith
  have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); nlinarith
  have hNm : FrobNormEstimateContract (1 / 2) 2 (n + 1) (frobNormStage (O := O) (Q := Q)) I :=
    frobNormStage_frobNormEstimateContract_half hS hM (by rw [hN]; nlinarith)
  have hRed : HessenbergReducerContract (27 * (((n + 1 : ℕ)) : ℝ) ^ 2 * u)
      (50 * (((n + 1 : ℕ)) : ℝ) ^ 2 * u) (n + 1) (hessenbergReduceQ (O := O) (Q := Q)) I :=
    hessenbergReduceQ_hessenbergReducerContract hS hM hC hQ hL hNat (by omega)
      (by rw [hN]; nlinarith)
  have hCore : TerminatingSchurCore ((1 + 24 * u) ^ Rc - 1) (denseSchurDegree n δ φ)
      (denseSchurCap n δ φ) (denseSchurLeafCap n δ φ) (n + 1)
      (denseSchurThreshold n δ φ :: (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ))
      (roundedShQRSchur (O := O) (Q := Q) sG) I := by
    rw [← shqrSchurParams_eq, show Rc = _ from (shqrSmallEigRotations_eq n δ φ).symm]
    exact roundedShQRSchur_terminatingSchurCore hS hM (by nlinarith) hL hNat hQ hC hSmp hDisk rfl
  have hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ}
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HoldsMatrix a A μ.store →
      μ.store.readBlock q.1 q.2 (denseSchurRegParams n δ φ).length =
        some (denseSchurRegParams n δ φ) → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock q.1 q.2 (denseSchurRegParams n δ φ).length) →
      Writes .total I τ (ginibrePerturb (O := O) (Q := Q) sG).body
        (Env.frame [n + 1, (denseSchurRegParams n δ φ).length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ :=
    fun A hA hq hl _ => (SmallEig.ginibrePerturb_writes_word hS hL hSmp hl hA
      (Store.get_of_readBlock hq (j := 0) (by simp [denseSchurRegParams,
        SmallEig.length_smallEigParams]) 0)).mono le_rfl fun _ _ h => ⟨_, h.2⟩
  have hw := schurPipelineWith_terminates (c₁ := 1 / 2) (c₂ := 2) (Nm := frobNormStage)
    (Reg := ginibrePerturb (O := O) (Q := Q) sG) (Red := hessenbergReduceQ)
    (Core := roundedShQRSchur (O := O) (Q := Q) sG) hS hM hL hNat hC
    (by nlinarith) hNm hReg hRed hCore (by norm_num) (by positivity)
    (by have := one_le_pow₀ (M₀ := ℝ) (n := Rc) (by linarith : (1 : ℝ) ≤ 1 + 24 * u); linarith)
    hin τ
  rw [hN, show (1 : ℝ) + ((1 + 24 * u) ^ Rc - 1) = (1 + 24 * u) ^ Rc by ring] at hw
  exact hw

/-- **The dense Schur solver at two tolerances terminates on every tape**, at any $\delta_R$, $\delta_C$ and $\varphi$, on a
scalar machine with the standard model at $\boldsymbol{u}$, $400(n + 1)^2\boldsymbol{u} \le 1$,
index literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, draws that
store the tape entry and an exact polar disk sampler: the run of `denseSchur` from a memory
holding $\mathbf{A}$ and the words of `denseSchurParamsAt` writes only $\mathbf{A}$,
$\widehat{\mathbf{U}}$ and the flag, and stores a matrix in the block of $\mathbf{A}$ and
$\widehat{\mathbf{U}}$ with
$\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 2\varepsilon +
\varepsilon^2$, $\varepsilon = (1 + 27(n + 1)^2\boldsymbol{u})(1 + 24\boldsymbol{u})^{R_c} - 1$,
$R_c$ the rotation count of the core. -/
theorem denseSchurAt_writes_orth {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δR δC φ : ℝ}
    (hu : 400 * ((n : ℝ) + 1) ^ 2 * u ≤ 1) {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (denseSchurParamsAt n δR δC φ) a p uo f A μ) (τ : Tape ℝ) :
    Writes .total I τ (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDimsAt n δR δC φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOrth (n := n) a uo
        (2 * ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ shqrSchurRotations n
          (denseSchurDegree n δR φ) (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
          (denseSchurCapAt n δR δC φ) (smallEigLeafRotations (denseSchurDegree n δR φ)
            (denseSchurLeafCapAt n δR δC φ)) - 1) +
         ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ shqrSchurRotations n
          (denseSchurDegree n δR φ) (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
          (denseSchurCapAt n δR δC φ) (smallEigLeafRotations (denseSchurDegree n δR φ)
            (denseSchurLeafCapAt n δR δC φ)) - 1) ^ 2)) μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  set Rc := shqrSchurRotations n (denseSchurDegree n δR φ)
    (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length (denseSchurCapAt n δR δC φ)
    (smallEigLeafRotations (denseSchurDegree n δR φ) (denseSchurLeafCapAt n δR δC φ))
  have hN : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hN2 : ((n : ℝ) + 1) ^ 2 * u ≤ 1 / 400 := by linarith
  have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); nlinarith
  have hNm : FrobNormEstimateContract (1 / 2) 2 (n + 1) (frobNormStage (O := O) (Q := Q)) I :=
    frobNormStage_frobNormEstimateContract_half hS hM (by rw [hN]; nlinarith)
  have hRed : HessenbergReducerContract (27 * (((n + 1 : ℕ)) : ℝ) ^ 2 * u)
      (50 * (((n + 1 : ℕ)) : ℝ) ^ 2 * u) (n + 1) (hessenbergReduceQ (O := O) (Q := Q)) I :=
    hessenbergReduceQ_hessenbergReducerContract hS hM hC hQ hL hNat (by omega)
      (by rw [hN]; nlinarith)
  have hCore : TerminatingSchurCore ((1 + 24 * u) ^ Rc - 1) (denseSchurDegree n δR φ)
      (denseSchurCapAt n δR δC φ) (denseSchurLeafCapAt n δR δC φ) (n + 1)
      (denseSchurThresholdAt n δR δC φ :: (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ))
      (roundedShQRSchur (O := O) (Q := Q) sG) I := by
    rw [← shqrSchurParamsAt_eq, show Rc = _ from (shqrSmallEigRotationsAt_eq n δR δC φ).symm]
    exact roundedShQRSchur_terminatingSchurCore hS hM (by nlinarith) hL hNat hQ hC hSmp hDisk rfl
  have hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ}
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HoldsMatrix a A μ.store →
      μ.store.readBlock q.1 q.2 (denseSchurRegParams n δR φ).length =
        some (denseSchurRegParams n δR φ) → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock q.1 q.2 (denseSchurRegParams n δR φ).length) →
      Writes .total I τ (ginibrePerturb (O := O) (Q := Q) sG).body
        (Env.frame [n + 1, (denseSchurRegParams n δR φ).length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ :=
    fun A hA hq hl _ => (SmallEig.ginibrePerturb_writes_word hS hL hSmp hl hA
      (Store.get_of_readBlock hq (j := 0) (by simp [denseSchurRegParams,
        SmallEig.length_smallEigParams]) 0)).mono le_rfl fun _ _ h => ⟨_, h.2⟩
  have hw := schurPipelineWith_terminates (c₁ := 1 / 2) (c₂ := 2) (Nm := frobNormStage)
    (Reg := ginibrePerturb (O := O) (Q := Q) sG) (Red := hessenbergReduceQ)
    (Core := roundedShQRSchur (O := O) (Q := Q) sG) hS hM hL hNat hC
    (by nlinarith) hNm hReg hRed hCore (by norm_num) (by positivity)
    (by have := one_le_pow₀ (M₀ := ℝ) (n := Rc) (by linarith : (1 : ℝ) ≤ 1 + 24 * u); linarith)
    hin τ
  rw [hN, show (1 : ℝ) + ((1 + 24 * u) ^ Rc - 1) = (1 + 24 * u) ^ Rc by ring] at hw
  exact hw

/-- **The class of conditioned diagonalizable matrices is σ-compact**: it is the projection of the
closed set of $(\mathbf{X}, \mathbf{V}, \mathbf{W}, d)$ with $\mathbf{V}\mathbf{W} = \mathbf{I}$,
$\mathbf{X}\mathbf{V} = \mathbf{V}\operatorname{diag}(d)$, $\|\mathbf{V}\|_2\|\mathbf{W}\|_2 \le B$
and the gaps of $d$ at least $\Gamma$. -/
theorem isSigmaCompact_setOf_isConditionedDiagonalizable {N : ℕ} (B Γ : ℝ) :
    IsSigmaCompact {X : Matrix (Fin N) (Fin N) ℂ | IsConditionedDiagonalizable B Γ X} := by
  set M := Matrix (Fin N) (Fin N) ℂ
  set Z : Set (M × M × M × (Fin N → ℂ)) := {q | q.2.1 * q.2.2.1 = 1 ∧
    q.1 * q.2.1 = q.2.1 * Matrix.diagonal q.2.2.2 ∧ specNorm q.2.1 * specNorm q.2.2.1 ≤ B ∧
    ∀ i j, i ≠ j → Γ ≤ ‖q.2.2.2 i - q.2.2.2 j‖}
  have hZ : IsClosed Z := by
    have hX : Continuous fun q : M × M × M × (Fin N → ℂ) => q.1 := by fun_prop
    have hV : Continuous fun q : M × M × M × (Fin N → ℂ) => q.2.1 := by fun_prop
    have hW : Continuous fun q : M × M × M × (Fin N → ℂ) => q.2.2.1 := by fun_prop
    have hd : Continuous fun q : M × M × M × (Fin N → ℂ) => q.2.2.2 := by fun_prop
    refine (isClosed_eq (hV.matrix_mul hW) continuous_const).inter
      ((isClosed_eq (hX.matrix_mul hV)
        (hV.matrix_mul (continuous_id.matrix_diagonal.comp hd))).inter
      ((isClosed_le ((continuous_specNorm.comp hV).mul (continuous_specNorm.comp hW))
        continuous_const).inter ?_))
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const
        ((((continuous_apply i).comp hd).sub ((continuous_apply j).comp hd)).norm)
  have e : {X : M | IsConditionedDiagonalizable B Γ X} = Prod.fst '' Z := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_image, Z, IsConditionedDiagonalizable]
    constructor
    · rintro ⟨V, d, hV, hXV, hκ, hg⟩
      refine ⟨(X, V, V⁻¹, d), ⟨Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hV),
        hXV, ?_, hg⟩, rfl⟩
      rwa [← pseudoConditionNumber_of_isUnit hV]
    · rintro ⟨⟨X', V, W, d⟩, ⟨hVW, hXV, hκ, hg⟩, rfl⟩
      have hV : IsUnit V := Matrix.isUnit_of_right_inverse hVW
      have hW : V⁻¹ = W := Matrix.inv_eq_right_inv hVW
      refine ⟨V, d, hV, hXV, ?_, hg⟩
      rwa [pseudoConditionNumber_of_isUnit hV, hW]
  rw [e]
  have : SigmaCompactSpace M := inferInstanceAs (SigmaCompactSpace (Fin N → Fin N → ℂ))
  exact (isSigmaCompact_univ.of_isClosed_subset hZ (Set.subset_univ _)).image continuous_fst

-- The four stage contracts at their long parameters make the elaboration heavy.
set_option maxHeartbeats 1000000 in
-- (heavy elaboration, see above)
/-- **The dense Schur solver at two tolerances, with the regularized matrix exposed, as a
probabilistic step**: the form of `NLAlib.Schur.denseSchurAt_measureReal_not_regularizedSchur_le`
from every input memory (`NLAlib.Ops.PWrites`). No printed source. -/
theorem denseSchurAt_pwrites_regularizedSchur {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δR δC φ : ℝ}
    (hδR : 0 < δR) (hδR1 : δR ≤ 1) (hδC : 0 < δC) (hδC1 : δC ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uDenseSchurAt n δR δC φ) {a p uo f : ℕ × ℕ} :
    PWrites law I (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDimsAt n δR δC φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurPipelineInput (denseSchurParamsAt n δR δC φ) a p uo f A)
      (RegularizedSchurOutput (IsConditionedDiagonalizable (denseSchurB n δR φ)
          (denseSchurΓ n δR φ)) a uo f A (1 / 2) 2
        (2 * √((n : ℝ) + 1) * (denseSchurDelta n δR / 2) + 3 * √((n : ℝ) + 1) * u)
        (schurPipelineEX n (1 / 2) 2 u (50 * ((n : ℝ) + 1) ^ 2 * u) (denseSchurDelta n δC)
          ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ shqrSchurRotations n (denseSchurDegree n δR φ)
            (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
            (denseSchurCapAt n δR δC φ)
            (smallEigLeafRotations (denseSchurDegree n δR φ) (denseSchurLeafCapAt n δR δC φ)) - 1))
        (2 * ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ shqrSchurRotations n (denseSchurDegree n δR φ)
            (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
            (denseSchurCapAt n δR δC φ)
            (smallEigLeafRotations (denseSchurDegree n δR φ) (denseSchurLeafCapAt n δR δC φ)) - 1) +
          ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ shqrSchurRotations n (denseSchurDegree n δR φ)
            (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
            (denseSchurCapAt n δR δC φ)
            (smallEigLeafRotations (denseSchurDegree n δR φ) (denseSchurLeafCapAt n δR δC φ)) - 1) ^ 2)) φ := by
  obtain ⟨hdR0, hdR1, hg, hc, hc1, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδR hδR1 hφ hφ1
  obtain ⟨hdC0, hdC1, -⟩ := denseSchur_params_basic (n := n) hδC hδC1 hφ hφ1
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  set k := denseSchurDegree n δR φ
  set B2 := 2 * denseSchurB n δR φ
  set Γ2 := denseSchurΓ n δR φ / 2
  set δ'C := denseSchurDelta n δC
  have hB1 : (1 : ℝ) ≤ B2 := by linarith
  -- the leaf
  have hβ := shqrSmallEigAccuracy_pos (n := n) hB1 (half_pos hΓ) hdC0 (by norm_num : (0 : ℝ) < 8)
  have hβS := shqrSmallEigAccuracy_le (n := n) hB1 (half_pos hΓ) hdC0
    (by linarith : δ'C ≤ 8)
  have hφL := shqrSmallEigFailure_pos (n := n) (B := B2) (Γ := Γ2) (S := 8) (δ := δ'C)
    (half_pos hφ)
  have hφL1 := shqrSmallEigFailure_le (n := n) (B := B2) (Γ := Γ2) (S := 8) (δ := δ'C)
    (half_pos hφ).le
  set T := denseSchurLeafCapAt n δR δC φ
  set RL := smallEigLeafRotations k T
  set qs := denseSchurLeafParamsAt n δR δC φ
  set np := (denseSchurShQRParamsAt n δR δC φ ++ qs).length
  have hu' : u ≤ uDenseSchurAtWith n δR δC φ np RL := hu.trans (min_le_left _ _)
  obtain ⟨hu1, hu2, hu3, hu4, -, hu6, -, hu8⟩ := le_of_le_uDenseSchurAtWith hu'
  obtain ⟨-, hR⟩ := mul_denseSchurRotationsAtWith_le hδC hu'
  have hLeaf : RandomSchurLeafContract law ((1 + 24 * u) ^ RL - 1)
      (forwardBackwardError k 32 (shqrSmallEigAccuracy n B2 Γ2 8 δ'C))
      (denseSchurLeafFailureAt n δR δC φ) (min k (n + 1)) (4 * 8) qs T
      (smallEigProg (O := O) (Q := Q) sG) I := by
    have h := SmallEig.smallEigProg_randomSchurLeafContract (O := O) (Q := Q) hS hM hL
      (dmax := min k (n + 1)) (min_le_left _ _)
      (hNat.mono (min_le_right _ _)) hQ hC hI hloc hSmp hDisk hU hG
      boundsGinibreGap_ginibreGapTail boundsGinibreCondition_ginibreConditionTail
      ginibreGapTail_b_pos ginibreConditionTail_b_pos hβ (by linarith : _ ≤ (32 : ℝ)) hφL
      (by linarith) (hu.trans (min_le_right _ _))
    rw [← denseSchurLeafCapAt_eq] at h
    rw [show (4 : ℝ) * 8 = 32 by norm_num]
    exact h
  have hR0 : 0 ≤ (1 + 24 * u) ^ RL - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := RL) (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
    linarith
  obtain ⟨hb0, -, -⟩ := forwardBackwardError_spec (kmax := k) hβ (by linarith : _ ≤ (32 : ℝ))
  set Rc := shqrSchurRotations n k np (denseSchurCapAt n δR δC φ) RL
  have hRe : denseSchurRotationsAt n δR δC φ = (n + 1) ^ 2 + Rc := rfl
  obtain ⟨hε0, hε16, hεU, -⟩ := denseSchur_errors_le (Rc := Rc) hδC hu0
    (by rw [← hRe]; exact hR) hu2 hu8 hδC1
  have hN : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  have hN2 : ((n : ℝ) + 1) ^ 2 * u ≤ 1 / 51200 := by
    rw [le_div_iff₀ (by positivity)] at hu2
    have : δ'C ≤ 1 / 16 := hdC1
    nlinarith
  -- the four contracts
  have hNm : FrobNormEstimateContract (1 / 2) 2 (n + 1) (frobNormStage (O := O) (Q := Q)) I :=
    frobNormStage_frobNormEstimateContract_half hS hM (by rw [hN]; nlinarith)
  have hReg : RandomRegularizerContract law (denseSchurDelta n δR / 2) (3 * (φ / 2) / 4)
      (fun A => IsConditionedDiagonalizable (denseSchurB n δR φ) (denseSchurΓ n δR φ) A) (n + 1)
      (2 / (1 / 2)) (denseSchurRegParams n δR φ) (ginibrePerturb (O := O) (Q := Q) sG) I := by
    rw [show (2 : ℝ) / (1 / 2) = 4 by norm_num]
    exact ginibrePerturb_randomRegularizerContract hS hM hL hSmp hG
      boundsGinibreGap_ginibreGapTail boundsGinibreCondition_ginibreConditionTail
      ginibreGapTail_b_pos ginibreConditionTail_b_pos hdR0 (by linarith) (half_pos hφ)
      (by linarith) hu1
  have hRed : HessenbergReducerContract (27 * (((n + 1 : ℕ)) : ℝ) ^ 2 * u)
      (50 * (((n + 1 : ℕ)) : ℝ) ^ 2 * u) (n + 1) (hessenbergReduceQ (O := O) (Q := Q)) I :=
    hessenbergReduceQ_hessenbergReducerContract hS hM hC hQ hL hNat (by omega)
      (by rw [hN]; nlinarith)
  have hCore : RandomSchurCoreContract law ((1 + 24 * u) ^ Rc - 1) δ'C (φ / 2)
      (fun H => IsConditionedDiagonalizable B2 Γ2 H) k (denseSchurCapAt n δR δC φ) T (n + 1)
      (4 / (1 / 2)) (denseSchurThresholdAt n δR δC φ :: (denseSchurShQRParamsAt n δR δC φ ++ qs))
      (roundedShQRSchurWith (smallEigProg (O := O) (Q := Q) sG)) I := by
    rw [show (4 : ℝ) / (1 / 2) = 8 by norm_num]
    exact roundedShQRSchurWith_randomSchurCoreContract hS hM hL hNat hQ hC hI hloc hDisk hU
      hB1 (half_pos hΓ) hdC0 (by linarith) (half_pos hφ) (by linarith) rfl hLeaf
      (SmallEig.length_smallEigParams _ _ _ _ _ _) hR0 le_rfl hb0.le
      (by rw [show (4 : ℝ) * 8 = 32 by norm_num]) hφL.le le_rfl hu4 hu6
  have hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      IsConditionedDiagonalizable (denseSchurB n δR φ) (denseSchurΓ n δR φ) A →
      IsPerturbedUnitarySimilarBy V A H
        (50 * (((n + 1 : ℕ) : ℝ)) ^ 2 * u * (2 / (1 / 2) + denseSchurDelta n δR / 2)) →
      IsConditionedDiagonalizable B2 Γ2 H :=
    fun A H V hA hV => hA.of_isPerturbedUnitarySimilarBy hΓ hV (by
      rw [hN]
      set g := smallEigGap (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreGapTail
      set c := smallEigCond (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreConditionTail
      set N : ℝ := (n : ℝ) + 1 with hNdef
      have hN1 : 1 ≤ N := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      have hu3' : u * (28800 * N ^ 3) ≤ g * c := (le_div_iff₀ (by positivity)).mp hu3
      have e : denseSchurΓ n δR φ / (16 * N * denseSchurB n δR φ) = g * c / (64 * N) := by
        unfold denseSchurΓ denseSchurB; field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      have hN3 : N ^ 3 * u * (4 + denseSchurDelta n δR / 2) ≤ N ^ 3 * u * (4 + 1 / 32) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith)
  have hCm : MeasurableSet {X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ |
      IsConditionedDiagonalizable (denseSchurB n δR φ) (denseSchurΓ n δR φ) X} :=
    measurableSet_of_isSigmaCompact (isSigmaCompact_setOf_isConditionedDiagonalizable _ _)
  have h := schurPipelineWith_pwrites_regularizedSchur (c₁ := 1 / 2) (c₂ := 2) (a := a) (p := p)
    (uo := uo) (f := f) (A := A) hS hM hL hNat hC hI hloc hNm hReg hRed hCore hCC' hCm
    (by norm_num) hu0
    (by rw [le_div_iff₀ (by positivity)] at hu8; nlinarith) (by linarith) (by positivity)
    (by rw [hN]; nlinarith) (by positivity)
    (by have := one_le_pow₀ (n := Rc) (by linarith : (1 : ℝ) ≤ 1 + 24 * u); linarith)
    (by rw [hN, show (1 : ℝ) + ((1 + 24 * u) ^ Rc - 1) = (1 + 24 * u) ^ Rc by ring]; exact hε16)
    (by positivity) (by positivity)
  have e1 : (1 : ℝ) + ((1 + 24 * u) ^ Rc - 1) = (1 + 24 * u) ^ Rc := by ring
  rw [hN, e1] at h
  exact h.mono (fun _ h => h) le_rfl (fun _ h => h) (by linarith)

/-- **The dense Schur solver at two tolerances, with the regularized matrix exposed.** On the
machine and streams of `NLAlib.Schur.denseSchur_measureReal_not_schur_le` (the standard model at
$\boldsymbol{u}$, index literals, exact natural literals up to $n + 1$, exact `toNat` and
comparisons, a measurable interpretation reading the tape only in its windows whose draws store
the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it and a
stream $s_G$ with the standard real Gaussian law), let $0 < \delta_R, \delta_C \le 1$,
$0 < \varphi \le 1$ and $\boldsymbol{u} \le$ `NLAlib.Schur.uDenseSchurAt n δR δC φ`. Then for every
complex $\mathbf{A}$ of order $n + 1$, from a memory holding $\mathbf{A}$ and the words of
`NLAlib.Schur.denseSchurParamsAt`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{denseSchur}(\mathbf{A}) \text{ fails, writes outside }
  \mathbf{A}, \widehat{\mathbf{U}} \text{ and the flag, or stores no Schur output with a
  regularized } \mathbf{X}\bigr] \le \varphi\,:$$
$\|\mathbf{A} - \mathbf{X}\|_2 \le (\delta_R/16 + 3\sqrt{n + 1}\,\boldsymbol{u})\|\mathbf{A}\|_2$,
the error against $\mathbf{X}$ `NLAlib.Schur.schurPipelineEX` with the constants $(1/2, 2)$, the
reducer's $50(n + 1)^2\boldsymbol{u}$, the core's $\delta_C/(16\sqrt{n + 1})$ and the accumulator's
$29R\boldsymbol{u}$, the orthogonality $58R\boldsymbol{u}$, and $s^{-1}\mathbf{X}$ of the class
$(B, \Gamma)$ at $\delta_R$ unless $\mathbf{A} = 0$. Here $R$ is
`NLAlib.Schur.denseSchurRotationsAt`, $B$ `NLAlib.Schur.denseSchurB` and $\Gamma$
`NLAlib.Schur.denseSchurΓ`. No printed source. -/
theorem denseSchurAt_measureReal_not_regularizedSchur_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δR δC φ : ℝ}
    (hδR : 0 < δR) (hδR1 : δR ≤ 1) (hδC : 0 < δC) (hδC1 : δC ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uDenseSchurAt n δR δC φ) {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (denseSchurParamsAt n δR δC φ) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDimsAt n δR δC φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (RegularizedSchurOutput (IsConditionedDiagonalizable (denseSchurB n δR φ)
          (denseSchurΓ n δR φ)) a uo f A (1 / 2) 2
        (2 * √((n : ℝ) + 1) * (denseSchurDelta n δR / 2) + 3 * √((n : ℝ) + 1) * u)
        (schurPipelineEX n (1 / 2) 2 u (50 * ((n : ℝ) + 1) ^ 2 * u) (denseSchurDelta n δC)
          (29 * denseSchurRotationsAt n δR δC φ * u))
        (58 * denseSchurRotationsAt n δR δC φ * u)) μ} ≤ φ := by
  obtain ⟨hdC0, -⟩ := denseSchur_params_basic (n := n) hδC hδC1 hφ hφ1
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  set Rc := shqrSchurRotations n (denseSchurDegree n δR φ)
    (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
    (denseSchurCapAt n δR δC φ)
    (smallEigLeafRotations (denseSchurDegree n δR φ) (denseSchurLeafCapAt n δR δC φ))
  have hRe : denseSchurRotationsAt n δR δC φ = (n + 1) ^ 2 + Rc := rfl
  have hu' := hu.trans (min_le_left _ _)
  obtain ⟨-, hu2, -, -, -, -, -, hu8⟩ := le_of_le_uDenseSchurAtWith hu'
  obtain ⟨-, hR⟩ := mul_denseSchurRotationsAtWith_le hδC hu'
  obtain ⟨hε0, -, hεU, -⟩ := denseSchur_errors_le (Rc := Rc) hδC hu0
    (by rw [← hRe]; exact hR) hu2 hu8 hδC1
  rw [← hRe] at hεU
  have hε29 : (1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1 ≤
      29 * (denseSchurRotationsAt n δR δC φ : ℝ) * u := by nlinarith
  refine (measureReal_mono fun ω hω hs => hω (hs.mono le_rfl fun μ' _ hout =>
    hout.mono le_rfl ?_ hεU)).trans ((denseSchurAt_pwrites_regularizedSchur hS hM hL hNat hQ hC
      hI hloc hSmp hDisk hU hG hδR hδR1 hδC hδC1 hφ hφ1 hu).measureReal_not_writes_le hin hξ)
  unfold schurPipelineEX
  have : 0 ≤ 2 * 2 * √((n : ℝ) + 1) := by positivity
  gcongr

/-- **The dense Schur solver terminates, with a near-orthonormal accumulator, on every tape**: on
a scalar machine with the standard model at $\boldsymbol{u} \le \boldsymbol{u}_0$, index
literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, draws that store
the tape entry and an exact polar disk sampler, for $0 < \delta \le 1$, any $\varphi$ and every
complex $\mathbf{A}$ of order $n + 1$, the run of `denseSchur` from a memory holding $\mathbf{A}$
and the words of `denseSchurParams` succeeds on every tape, writes only $\mathbf{A}$,
$\widehat{\mathbf{U}}$ and the flag, and stores a matrix in the block of $\mathbf{A}$ and
$\widehat{\mathbf{U}}$ with
$\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}$.
Here $\boldsymbol{u}_0$ is `NLAlib.Schur.uDenseSchur` and $R$ is
`NLAlib.Schur.denseSchurRotations`. The orthogonality needs no shift to succeed: every replayed
rotation and every leaf product is a near-unitary update. -/
theorem denseSchur_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : u ≤ uDenseSchur n δ φ) {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (denseSchurParams n δ φ) a p uo f A μ) (τ : Tape ℝ) :
    Writes .total I τ (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n δ φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOrth (n := n) a uo (58 * denseSchurRotations n δ φ * u)) μ := by
  obtain ⟨-, hu2, -, -, -, -, -, hu8⟩ := le_of_le_uDenseSchurWith (hu.trans (min_le_left _ _))
  obtain ⟨-, -, hR⟩ := mul_denseSchurRotationsWith_le hδ hδ1 (hu.trans (min_le_left _ _))
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hd1 : denseSchurDelta n δ ≤ 1 / 16 := by
    have hs1 : (1 : ℝ) ≤ √((n : ℝ) + 1) := by
      rw [Real.one_le_sqrt]; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    unfold denseSchurDelta; rw [div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨-, -, hεU, -⟩ := denseSchur_errors_le hδ hu0 hR hu2 hu8 hδ1
  have h400 : 400 * ((n : ℝ) + 1) ^ 2 * u ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hu2; nlinarith
  exact (denseSchur_writes_orth hS hM hL hNat hQ hC hSmp hDisk h400 hin τ).mono le_rfl
    fun μ' _ ⟨hT, U, hU, ho⟩ => ⟨hT, U, hU, ho.trans hεU⟩

/-- **The dense Schur solver lists the eigenvalues of a nearby matrix.** On the machine and
streams of `NLAlib.Schur.denseSchur_measureReal_not_schur_le` (the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_0$, index literals, exact natural literals up to $n + 1$, exact
`toNat` and comparisons, a measurable interpretation reading the tape only in its windows whose
draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on
it and a stream $s_G$ with the standard real Gaussian law), for $0 < \delta \le 1$,
$0 < \varphi \le 1$ and every complex $\mathbf{A}$ of order $n + 1$, from a memory holding
$\mathbf{A}$ and the words of `denseSchurParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{denseSchur}(\mathbf{A}) \text{ fails, or writes outside }
  \mathbf{A}, \widehat{\mathbf{U}} \text{ and the flag, or stores no flag } 0 \text{ and upper
  triangular } \widehat{\mathbf{T}} \text{ whose diagonal lists }
  \operatorname{spec}(\mathbf{A} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le 2\delta\|\mathbf{A}\|_2
  \bigr] \le \varphi\,.$$
Here $\boldsymbol{u}_0$ is `NLAlib.Schur.uDenseSchur`.
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1],
relative form; there the eigenvalues are the output.

Note: From the Schur form by `NLAlib.Schur.SchurOutput.exists_isEigenvalueListing`
($\|\mathbf{E}\|_2 \le (\delta + 4 \cdot 58R\boldsymbol{u}(1 + \delta))\|\mathbf{A}\|_2$).
General form: `NLAlib.Schur.denseSchur_measureReal_not_schur_le`.
Result: dense-schur-eigenvalues -/
theorem denseSchur_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uDenseSchur n δ φ)
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ} (hin : SchurPipelineInput (denseSchurParams n δ φ) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n δ φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ T E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a T μ'.store ∧
          T.IsUpperTriangular ∧ specNorm E ≤ 2 * δ * specNorm A ∧
          IsEigenvalueListing (A + E) fun i => T i i) μ} ≤ φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hR58, hR, hE⟩ := denseSchur_orth_le (n := n) hδ hδ1 hu
  have hmain := denseSchur_measureReal_not_schur_le hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG
    hδ hδ1 hφ hφ1 hu hin hξ
  refine (measureReal_mono ?_).trans hmain
  intro ω hω hs
  refine hω (hs.mono le_rfl fun μ' _ hout => ?_)
  obtain ⟨T, E, hT, hEn, hl⟩ := hout.exists_isEigenvalueListing hR
  exact ⟨hout.1, T, E, hT, hout.isUpperTriangular_of_holdsMatrix hT,
    hEn.trans (mul_le_mul_of_nonneg_right hE (specNorm_nonneg A)), hl⟩

/-- **The dense Schur solver, exact-unitary form.** On the machine and streams of
`NLAlib.Schur.denseSchur_measureReal_not_schur_le` (the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_0$, index literals, exact natural literals up to $n + 1$, exact
`toNat` and comparisons, a measurable interpretation reading the tape only in its windows whose
draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on
it and a stream $s_G$ with the standard real Gaussian law), for $0 < \delta \le 1$,
$0 < \varphi \le 1$ and every complex $\mathbf{A}$ of order $n + 1$, from a memory holding
$\mathbf{A}$ and the words of `denseSchurParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{denseSchur}(\mathbf{A}) \text{ fails, or writes outside }
  \mathbf{A}, \widehat{\mathbf{U}} \text{ and the flag, or stores no flag } 0,\ \widehat{\mathbf{U}}
  \text{ and upper triangular } \widehat{\mathbf{T}} \text{ with }
  \mathbf{A} + \mathbf{E} = \mathbf{V}\widehat{\mathbf{T}}\mathbf{V}^{\mathsf H},\
  \|\widehat{\mathbf{U}} - \mathbf{V}\|_2 \le 58R\boldsymbol{u},\
  \|\mathbf{E}\|_2 \le 2\delta\|\mathbf{A}\|_2\bigr] \le \varphi\,,$$
for an exact unitary $\mathbf{V}$. Here $\boldsymbol{u}_0$ is `NLAlib.Schur.uDenseSchur` and $R$
is `NLAlib.Schur.denseSchurRotations`. No printed source: the papers compute eigenvalues only.

Note: From the Schur form by `NLAlib.Schur.SchurOutput.exists_hasOrthonormalCols`.
General form: `NLAlib.Schur.denseSchur_measureReal_not_schur_le`.
Result: dense-schur-exact-unitary -/
theorem denseSchur_measureReal_not_exact_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uDenseSchur n δ φ)
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ} (hin : SchurPipelineInput (denseSchurParams n δ φ) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n δ φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ U T V E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a T μ'.store ∧
          HoldsMatrix uo U μ'.store ∧ T.IsUpperTriangular ∧ HasOrthonormalCols V ∧
          specNorm (U - V) ≤ 58 * denseSchurRotations n δ φ * u ∧
          specNorm E ≤ 2 * δ * specNorm A ∧ A + E = V * T * Vᴴ) μ} ≤ φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hR58, hR, hE⟩ := denseSchur_orth_le (n := n) hδ hδ1 hu
  have hmain := denseSchur_measureReal_not_schur_le hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG
    hδ hδ1 hφ hφ1 hu hin hξ
  refine (measureReal_mono ?_).trans hmain
  intro ω hω hs
  refine hω (hs.mono le_rfl fun μ' _ hout => ?_)
  obtain ⟨U, T, V, E, hT, hUs, hV, hUV, hEn, hAE⟩ := hout.exists_hasOrthonormalCols hR
  exact ⟨hout.1, U, T, V, E, hT, hUs, hout.isUpperTriangular_of_holdsMatrix hT, hV, hUV,
    hEn.trans (mul_le_mul_of_nonneg_right hE (specNorm_nonneg A)), hAE⟩


omit [Has SampleOp O] [Has DiskSampleOp O] in
/-- The instructions of the reducer: the instrumented static count of
`NLAlib.hessenbergReduceQ` at the order $n + 1$ and zero offsets is at most $2998(n + 1)^3$ (the
monomial bound, by `kernel_rfl`). -/
theorem size_stmtCost_hessenbergReduceQ_le (n : ℕ) :
    Count.size (stmtCost (hessenbergReduceQ (O := O) (Q := Q)).body.instrument
        [n + 1, 0, 0, 0, 0]) ≤ 2998 * (n + 1) ^ 3 := by
  have hw : stmtWorkMono (hessenbergReduceQ (O := O) (Q := Q)).body.instrument
      (⟨1, [1]⟩ :: List.replicate 4 (WorkMono.const 0)) = ⟨2998, [3]⟩ := by
    rw [stmtWorkMono_instrument]; kernel_rfl
  have hσ : SlotsLe [n + 1] [n + 1, 0, 0, 0, 0]
      (⟨1, [1]⟩ :: List.replicate 4 (WorkMono.const 0)) := by
    simp [SlotsLe, WorkMono.eval, WorkMono.const]
  have h := size_stmtCost_le_stmtWorkMono (by simp)
    (hessenbergReduceQ (O := O) (Q := Q)).body.instrument hσ
  rw [hw] at h
  simpa [WorkMono.eval, mul_assoc] using h

/-- **The operation count of the dense Schur solver** (on every tape): the instrumented static
count of `NLAlib.Schur.denseSchur` at the order $n + 1$, $n_r$ regularizer words, $n_q$ core words,
the shift degree $k$, the iteration cap $F$, the leaf cap $T$ and zero offsets, every primitive,
test and structural instruction counted, is at most
$384547(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$: the core's $380748$
(`NLAlib.ShiftedQR.size_stmtCost_roundedShQRSchur_le`), the reducer's $2998$, the norm's $120$,
the regularizer's $201$ and the glue's $4 \cdot 120$
(`NLAlib.Schur.size_stmtCost_schurPipelineWith_le`). The power of $k$ is that of the eigenvalue
solver: the replays on the couplings and on the accumulator cost no more than a step. -/
theorem denseSchur_work_le (sG n nr nq k F T : ℕ) :
    Count.size (stmtCost (denseSchur (O := O) (Q := Q) sG).body.instrument
        [n + 1, nr, nq, k, F, T, 0, 0, 0, 0, 0]) ≤
      384547 * (n + 1) ^ 3 * (k + 1) ^ 4 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2 := by
  refine (size_stmtCost_schurPipelineWith_le _ _ _ _ _ _ _ _ _ _).trans ?_
  have h1 := size_stmtCost_frobNormStage_le (O := O) (Q := Q) n
  have h2 := size_stmtCost_ginibrePerturb_le (O := O) (Q := Q) sG n nr
  have h3 := size_stmtCost_hessenbergReduceQ_le (O := O) (Q := Q) n
  have h4 := size_stmtCost_roundedShQRSchur_le (O := O) (Q := Q) sG n nq k F T nr
  set X := (k + 1) ^ 4 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2
  have hX : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hN : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN2 : (n + 1 + 1) ^ 2 ≤ 4 * (n + 1) ^ 2 :=
    calc (n + 1 + 1) ^ 2 ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (n + 1) ^ 2 := by ring
  have hN3 : (n + 1) ^ 3 ≤ (n + 1) ^ 3 * X := Nat.le_mul_of_pos_right _ hX
  have e4 : 380748 * (n + 1) ^ 3 * (k + 1) ^ 4 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2 =
      380748 * ((n + 1) ^ 3 * X) := by simp only [X]; ring
  have e : 384547 * (n + 1) ^ 3 * (k + 1) ^ 4 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2 =
      384547 * ((n + 1) ^ 3 * X) := by simp only [X]; ring
  rw [e4] at h4
  rw [e]
  unfold roundedShQRSchur at h4
  omega

end Theorems

end NLAlib.Schur
