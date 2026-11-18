/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Pipeline
public import NLAlib.Eigensolvers.Schur.Regularizer
public import NLAlib.Eigensolvers.Schur.NormEstimate
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEig

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

The parameters depend on $(n, \delta, \varphi)$ only. With $\delta' = \delta/(16\sqrt{n + 1})$:
the regularizer at the words `NLAlib.SmallEig.smallEigParams` for the order $n + 1$, the norm
bound $4$, the error $\delta'$ and the failure $\varphi/2$, into the class $(B, \Gamma) =
(2/t_2, t_1/2)$; the core at the class $(2B, \Gamma/2)$, the norm bound $8$, the error $\delta'$
and the failure $\varphi/2$. The norm estimate is taken with the constants $(1/2, 2)$.

## Main definitions

* `NLAlib.Schur.denseSchurWith`, `NLAlib.Schur.denseSchur`: the programs.
* `NLAlib.Schur.denseSchurParamsWith`, `NLAlib.Schur.denseSchurDimsWith`,
  `NLAlib.Schur.denseSchurRotationsWith`, `NLAlib.Schur.uDenseSchurWith`: the words, dimensions,
  rotation count and precision threshold with a leaf's words, cap and rotation count;
  `NLAlib.Schur.denseSchurParams`, `NLAlib.Schur.denseSchurDims`,
  `NLAlib.Schur.denseSchurRotations`, `NLAlib.Schur.uDenseSchur`: those of the `SmallEig` leaf.

## Main results

* `NLAlib.Schur.denseSchurWith_measureReal_not_schur_le`: the dense Schur theorem with any
  small-block Schur solver.
* `NLAlib.Schur.denseSchur_measureReal_not_schur_le`: the dense Schur theorem.
* `NLAlib.Schur.denseSchur_terminates`: termination and orthogonality on every tape.
* `NLAlib.Schur.denseSchur_measureReal_not_spectrum_le`,
  `NLAlib.Schur.denseSchur_measureReal_not_exact_schur_le`: the eigenvalues, and an exact unitary.
* `NLAlib.Schur.logb_inv_uDenseSchur_le`: the bits of precision.
* `NLAlib.Schur.denseSchur_work_le`, `NLAlib.Schur.denseSchur_work_le_polylog`: the operation
  count.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory ProbabilityTheory ShiftedQR SmallEig
open scoped Matrix

/-! ### Parameters -/

/-- The error $\delta' = \delta/(16\sqrt{n + 1})$ of the regularizer and of the core. -/
noncomputable def denseSchurDelta (n : ℕ) (δ : ℝ) : ℝ := δ / (16 * √((n : ℝ) + 1))

/-- The words of the regularizer: `NLAlib.SmallEig.smallEigParams` at the order $n + 1$, the norm
bound $4$, the error $\delta'$, the failure $\varphi/2$ and the proved Ginibre tails. -/
noncomputable def denseSchurRegParams (n : ℕ) (δ φ : ℝ) : List ℝ :=
  smallEigParams (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail ginibreConditionTail

/-- The condition bound $B = 2/t_2$ of the regularized matrix. -/
noncomputable def denseSchurB (n : ℕ) (δ φ : ℝ) : ℝ :=
  2 / smallEigCond (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreConditionTail

/-- The separation $\Gamma = t_1/2$ of the regularized matrix. -/
noncomputable def denseSchurΓ (n : ℕ) (δ φ : ℝ) : ℝ :=
  smallEigGap (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail / 2

/-- The shift degree $k$ of the core: the degree of (eqn:setk) at $4 \cdot 2B$. -/
noncomputable def denseSchurDegree (n : ℕ) (δ φ : ℝ) : ℕ :=
  shqrDegree (4 * (2 * denseSchurB n δ φ))

/-- The iteration cap $F$ of the core. -/
noncomputable def denseSchurCap (n : ℕ) (δ φ : ℝ) : ℕ :=
  shqrCap n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ)

/-- The deflation threshold word of the core. -/
noncomputable def denseSchurThreshold (n : ℕ) (δ φ : ℝ) : ℝ :=
  shqrDeflationThreshold n (denseSchurDegree n δ φ) (2 * denseSchurB n δ φ)
    (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ) (φ / 2)

/-- The shifted QR words of the core, `NLAlib.ShiftedQR.shqrParams` at the class
$(2B, \Gamma/2)$, the norm bound $8$, the error $\delta'$ and the failure $\varphi/2$. -/
noncomputable def denseSchurShQRParams (n : ℕ) (δ φ : ℝ) : List ℝ :=
  shqrParams n (denseSchurDegree n δ φ) (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
    (denseSchurDelta n δ) (φ / 2)

/-- The backward accuracy a leaf must meet: `NLAlib.SmallEig.forwardBackwardError` at the order
bound $k$ and the norm bound $32$ of the forward accuracy `NLAlib.ShiftedQR.shqrSmallEigAccuracy`
of the core. -/
noncomputable def denseSchurLeafAccuracy (n : ℕ) (δ φ : ℝ) : ℝ :=
  forwardBackwardError (denseSchurDegree n δ φ) 32
    (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
      (denseSchurDelta n δ))

/-- The failure a leaf may have: `NLAlib.ShiftedQR.shqrSmallEigFailure` of the core. -/
noncomputable def denseSchurLeafFailure (n : ℕ) (δ φ : ℝ) : ℝ :=
  shqrSmallEigFailure n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ)
    (φ / 2)

/-- **The words of the dense Schur solver with the leaf words `qs`**: the regularizer's words,
then the core's: the deflation threshold, the shifted QR words and `qs`. -/
noncomputable def denseSchurParamsWith (n : ℕ) (δ φ : ℝ) (qs : List ℝ) : List ℝ :=
  denseSchurRegParams n δ φ ++ (denseSchurThreshold n δ φ :: (denseSchurShQRParams n δ φ ++ qs))

/-- The dimensions of a run with the leaf words `qs` and the leaf cap $T$:
`[n + 1, nr, nq, k, F, T]`. -/
noncomputable def denseSchurDimsWith (n : ℕ) (δ φ : ℝ) (qs : List ℝ) (T : ℕ) : List ℕ :=
  [n + 1, (denseSchurRegParams n δ φ).length,
    (denseSchurThreshold n δ φ :: (denseSchurShQRParams n δ φ ++ qs)).length,
    denseSchurDegree n δ φ, denseSchurCap n δ φ, T]

/-- **The rotation count** $R$ of the accumulator with a leaf of $R_L$ rotation-equivalents and
$n_p$ core words after the threshold: the $(n + 1)^2$ of the reduction and the core's
(`NLAlib.ShiftedQR.shqrSchurRotations`). -/
noncomputable def denseSchurRotationsWith (n : ℕ) (δ φ : ℝ) (np RL : ℕ) : ℕ :=
  (n + 1) ^ 2 + shqrSchurRotations n (denseSchurDegree n δ φ) np (denseSchurCap n δ φ) RL

/-- **The precision threshold** of the dense Schur solver with a leaf of $R_L$ rotation-equivalents
and $n_p$ core words after the threshold, the minimum of: the regularizer's
`NLAlib.SmallEig.uSmallEigReduce`; $\delta'/(3200(n + 1)^2)$ (the reducer's backward error
$50(n + 1)^2\boldsymbol{u} \le \delta'/64$); $t_1t_2/(28800(n + 1)^3)$ (the reducer keeps the
class);
the core's `NLAlib.ShiftedQR.uShQR`, $1/100$ and replay term; $\delta/(4096(n + 1)R)$ (the
accumulator); $\delta/(64(n + 1))$ (the scaling). -/
noncomputable def uDenseSchurWith (n : ℕ) (δ φ : ℝ) (np RL : ℕ) : ℝ :=
  min (uSmallEigReduce (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail
    ginibreConditionTail) <|
  min (denseSchurDelta n δ / (3200 * ((n : ℝ) + 1) ^ 2)) <|
  min (smallEigGap (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail *
    smallEigCond (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreConditionTail /
      (28800 * ((n : ℝ) + 1) ^ 3)) <|
  min (uShQR n (denseSchurDegree n δ φ) (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
    (denseSchurDelta n δ) (φ / 2)) <|
  min (1 / 100) <|
  min (uShQRSchurReplay n (denseSchurDegree n δ φ) np (denseSchurCap n δ φ)
    (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ)) <|
  min (δ / (4096 * ((n : ℝ) + 1) * denseSchurRotationsWith n δ φ np RL))
    (δ / (64 * ((n : ℝ) + 1)))

/-- The leaf words of the `SmallEig` leaf: `NLAlib.SmallEig.smallEigForwardParams` at the order
bound $k$, the norm bound $32$, the forward accuracy and the failure of the core. -/
noncomputable def denseSchurLeafParams (n : ℕ) (δ φ : ℝ) : List ℝ :=
  smallEigForwardParams (denseSchurDegree n δ φ) 32
    (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
      (denseSchurDelta n δ))
    (denseSchurLeafFailure n δ φ) ginibreGapTail ginibreConditionTail

/-- The cap $T$ of the `SmallEig` leaf. -/
noncomputable def denseSchurLeafCap (n : ℕ) (δ φ : ℝ) : ℕ :=
  shqrSmallEigCap n (denseSchurDegree n δ φ) (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
    (denseSchurDelta n δ) (φ / 2) ginibreGapTail ginibreConditionTail

/-- **The words of the dense Schur solver** (`SmallEig` leaf). -/
noncomputable def denseSchurParams (n : ℕ) (δ φ : ℝ) : List ℝ :=
  denseSchurParamsWith n δ φ (denseSchurLeafParams n δ φ)

/-- **The dimensions of a run** of the dense Schur solver (`SmallEig` leaf). -/
noncomputable def denseSchurDims (n : ℕ) (δ φ : ℝ) : List ℕ :=
  denseSchurDimsWith n δ φ (denseSchurLeafParams n δ φ) (denseSchurLeafCap n δ φ)

/-- **The rotation count** $R$ of the dense Schur solver (`SmallEig` leaf, whose count is
`NLAlib.SmallEig.smallEigLeafRotations` at the order bound $k$ and its cap). -/
noncomputable def denseSchurRotations (n : ℕ) (δ φ : ℝ) : ℕ :=
  denseSchurRotationsWith n δ φ (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length
    (smallEigLeafRotations (denseSchurDegree n δ φ) (denseSchurLeafCap n δ φ))

/-- **The precision threshold** $\boldsymbol{u}_0(n, \delta, \varphi)$ of the dense Schur solver:
`NLAlib.Schur.uDenseSchurWith` with the `SmallEig` leaf, and the leaf's own
`NLAlib.SmallEig.uSmallEigForward`. -/
noncomputable def uDenseSchur (n : ℕ) (δ φ : ℝ) : ℝ :=
  min (uDenseSchurWith n δ φ (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length
      (smallEigLeafRotations (denseSchurDegree n δ φ) (denseSchurLeafCap n δ φ)))
    (uSmallEigForward (denseSchurDegree n δ φ) 32
      (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
        (denseSchurDelta n δ)) (denseSchurLeafFailure n δ φ) ginibreGapTail ginibreConditionTail)

/-- The basic parameters: $0 < \delta' \le 1/16$, the gap and the condition thresholds positive,
$t_2 \le 1$, so $B = 2/t_2 \ge 2$ and $\Gamma > 0$. -/
theorem denseSchur_params_basic {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) :
    0 < denseSchurDelta n δ ∧ denseSchurDelta n δ ≤ 1 / 16 ∧
      0 < smallEigGap (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail ∧
      0 < smallEigCond (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreConditionTail ∧
      smallEigCond (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreConditionTail ≤ 1 ∧
      2 ≤ denseSchurB n δ φ ∧ 0 < denseSchurΓ n δ φ := by
  have hs1 : (1 : ℝ) ≤ √((n : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hd0 : 0 < denseSchurDelta n δ := by unfold denseSchurDelta; positivity
  have hd1 : denseSchurDelta n δ ≤ 1 / 16 := by
    unfold denseSchurDelta
    rw [div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨hg, -⟩ := smallEigGap_pos_le ginibreGapTail_b_pos (le_add_self) (S := 4)
    (by norm_num) hd0 (half_pos hφ) (by linarith) (nmax := n + 1)
  obtain ⟨hc, hc1⟩ := smallEigCond_pos_le ginibreConditionTail_b_pos (le_add_self) (S := 4)
    (by norm_num) hd0 (half_pos hφ) (by linarith) (nmax := n + 1)
  refine ⟨hd0, hd1, hg, hc, hc1, ?_, by unfold denseSchurΓ; positivity⟩
  unfold denseSchurB
  rw [le_div_iff₀ hc]; linarith

/-- The shift degree is positive. -/
theorem denseSchurDegree_pos (n : ℕ) (δ φ : ℝ) : 0 < denseSchurDegree n δ φ :=
  Nat.pos_of_ne_zero (by unfold denseSchurDegree shqrDegree; positivity)

/-- **The terms of the precision threshold**: below `NLAlib.Schur.uDenseSchurWith`,
$\boldsymbol{u}$ is below each of its eight terms. -/
theorem le_of_le_uDenseSchurWith {n : ℕ} {δ φ u : ℝ} {np RL : ℕ}
    (hu : u ≤ uDenseSchurWith n δ φ np RL) :
    u ≤ uSmallEigReduce (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail
        ginibreConditionTail ∧
      u ≤ denseSchurDelta n δ / (3200 * ((n : ℝ) + 1) ^ 2) ∧
      u ≤ smallEigGap (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail *
        smallEigCond (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreConditionTail /
          (28800 * ((n : ℝ) + 1) ^ 3) ∧
      u ≤ uShQR n (denseSchurDegree n δ φ) (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
        (denseSchurDelta n δ) (φ / 2) ∧
      u ≤ 1 / 100 ∧
      u ≤ uShQRSchurReplay n (denseSchurDegree n δ φ) np (denseSchurCap n δ φ)
        (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ) ∧
      u ≤ δ / (4096 * ((n : ℝ) + 1) * denseSchurRotationsWith n δ φ np RL) ∧
      u ≤ δ / (64 * ((n : ℝ) + 1)) := by
  unfold uDenseSchurWith at hu
  simp only [le_min_iff] at hu
  exact hu

/-- **The precision threshold with a leaf is positive** for $0 < \delta \le 1$ and
$0 < \varphi \le 1$. -/
theorem uDenseSchurWith_pos {n : ℕ} {δ φ : ℝ} (np RL : ℕ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) : 0 < uDenseSchurWith n δ φ np RL := by
  obtain ⟨hd0, hd1, hg, hc, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  have hk := denseSchurDegree_pos n δ φ
  have hR : 0 < (denseSchurRotationsWith n δ φ np RL : ℝ) := by
    unfold denseSchurRotationsWith; positivity
  have h1 : 0 < uSmallEigReduce (n + 1) 4 (denseSchurDelta n δ) (φ / 2) ginibreGapTail
      ginibreConditionTail := by unfold uSmallEigReduce; positivity
  have h4 := uShQR_pos (n := n) hk (by linarith : (1 : ℝ) ≤ 2 * denseSchurB n δ φ)
    (half_pos hΓ) hd0 (by norm_num : (0 : ℝ) < 8) (half_pos hφ)
  have h6 : 0 < uShQRSchurReplay n (denseSchurDegree n δ φ) np (denseSchurCap n δ φ)
      (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ) := by
    have := shqrBudget_pos (n := n) (by linarith : (1 : ℝ) ≤ 2 * denseSchurB n δ φ)
      (half_pos hΓ) hd0
    unfold uShQRSchurReplay; positivity
  unfold uDenseSchurWith
  simp only [lt_min_iff]
  exact ⟨h1, by positivity, by positivity, h4, by norm_num, h6, by positivity, by positivity⟩

/-- **The precision threshold is positive** for $0 < \delta \le 1$ and $0 < \varphi \le 1$: the
headline is not vacuous. -/
theorem uDenseSchur_pos {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < uDenseSchur n δ φ := by
  obtain ⟨hd0, -, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  have hk := denseSchurDegree_pos n δ φ
  have hB1 : (1 : ℝ) ≤ 2 * denseSchurB n δ φ := by linarith
  have hβ := shqrSmallEigAccuracy_pos (n := n) hB1 (half_pos hΓ) hd0 (by norm_num : (0 : ℝ) < 8)
  have hβS := shqrSmallEigAccuracy_le (n := n) hB1 (half_pos hΓ) hd0
    (by linarith [(denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1).2.1] : denseSchurDelta n δ ≤ 8)
  obtain ⟨hf0, hfS, -⟩ := forwardBackwardError_spec (kmax := denseSchurDegree n δ φ)
    hβ (by linarith : _ ≤ (32 : ℝ))
  have hφL := shqrSmallEigFailure_pos (n := n) (B := 2 * denseSchurB n δ φ)
    (Γ := denseSchurΓ n δ φ / 2) (S := 8) (δ := denseSchurDelta n δ) (half_pos hφ)
  have hφL1 := shqrSmallEigFailure_le (n := n) (B := 2 * denseSchurB n δ φ)
    (Γ := denseSchurΓ n δ φ / 2) (S := 8) (δ := denseSchurDelta n δ) (half_pos hφ).le
  refine lt_min (uDenseSchurWith_pos _ _ hδ hδ1 hφ hφ1) ?_
  exact (uSmallEig_spec ginibreGapTail_b_pos ginibreConditionTail_b_pos hk hf0 hfS hφL
    (by linarith)).1

/-- **The orthogonality bound is at most $\delta$** below the threshold of a leaf:
$58R\boldsymbol{u} \le \delta$ and $24R\boldsymbol{u} \le 1/8$, $R$ =
`NLAlib.Schur.denseSchurRotationsWith`. -/
theorem mul_denseSchurRotationsWith_le {n : ℕ} {δ φ u : ℝ} {np RL : ℕ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hu : u ≤ uDenseSchurWith n δ φ np RL) :
    58 * (denseSchurRotationsWith n δ φ np RL : ℝ) * u ≤ δ ∧
      24 * (denseSchurRotationsWith n δ φ np RL : ℝ) * u ≤ 1 / 8 ∧
      4096 * ((n : ℝ) + 1) * (denseSchurRotationsWith n δ φ np RL : ℝ) * u ≤ δ := by
  have h7 := (le_of_le_uDenseSchurWith hu).2.2.2.2.2.2.1
  have hR : 0 < (denseSchurRotationsWith n δ φ np RL : ℝ) := by
    unfold denseSchurRotationsWith; positivity
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hK : 0 < 4096 * ((n : ℝ) + 1) * (denseSchurRotationsWith n δ φ np RL : ℝ) := by
    positivity
  have hRu : 4096 * ((n : ℝ) + 1) * (denseSchurRotationsWith n δ φ np RL : ℝ) * u ≤ δ := by
    have := mul_le_mul_of_nonneg_left h7 hK.le
    rwa [mul_div_cancel₀ _ hK.ne'] at this
  have hRu' : 4096 * ((denseSchurRotationsWith n δ φ np RL : ℝ) * u) ≤ δ := by
    by_cases hu0 : u ≤ 0
    · nlinarith
    · push Not at hu0
      have : 4096 * ((denseSchurRotationsWith n δ φ np RL : ℝ) * u) ≤
          4096 * ((n : ℝ) + 1) * (denseSchurRotationsWith n δ φ np RL : ℝ) * u := by
        have := mul_le_mul_of_nonneg_right hn (by positivity :
          (0 : ℝ) ≤ 4096 * ((denseSchurRotationsWith n δ φ np RL : ℝ) * u))
        linarith
      linarith
  exact ⟨by nlinarith, by nlinarith, hRu⟩

/-- **The orthogonality bound is at most $\delta$**: below the threshold,
$58R\boldsymbol{u} \le \delta$ (and $24R\boldsymbol{u} \le 1/8$). -/
theorem mul_denseSchurRotations_le {n : ℕ} {δ φ u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : u ≤ uDenseSchur n δ φ) :
    58 * (denseSchurRotations n δ φ : ℝ) * u ≤ δ ∧
      24 * (denseSchurRotations n δ φ : ℝ) * u ≤ 1 / 8 := by
  obtain ⟨h1, h2, -⟩ := mul_denseSchurRotationsWith_le hδ hδ1 (hu.trans (min_le_left _ _))
  exact ⟨h1, h2⟩

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
      μ} ≤ φ :=
  sorry

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
      (SchurOutput a uo f A δ (58 * denseSchurRotations n δ φ * u)) μ} ≤ φ :=
  sorry

/-- **The dense Schur solver terminates, with a near-orthonormal accumulator, on every tape**: on
a scalar machine with the standard model at $\boldsymbol{u} \le \boldsymbol{u}_0$, index
literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, draws that store
the tape entry and an exact polar disk sampler, for $0 < \delta \le 1$, any $\varphi$ and every
complex $\mathbf{A}$ of order $n + 1$, the run of `denseSchur` from a memory holding $\mathbf{A}$
and the words of `denseSchurParams` succeeds on every tape, writes only $\mathbf{A}$,
$\widehat{\mathbf{U}}$ and the flag, and stores $\widehat{\mathbf{U}}$ with
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
      (SchurOrth (n := n) uo (58 * denseSchurRotations n δ φ * u)) μ :=
  sorry

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
($\|\mathbf{E}\|_2 \le (\delta + 4 \cdot 58R\boldsymbol{u})\|\mathbf{A}\|_2$).
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
          IsEigenvalueListing (A + E) fun i => T i i) μ} ≤ φ :=
  sorry

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
          specNorm E ≤ 2 * δ * specNorm A ∧ A + E = V * T * Vᴴ) μ} ≤ φ :=
  sorry

/-- **The bits of precision of the dense Schur solver**: there are absolute constants $c_1, c_2$
such that for every order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$,
$$\log_2\frac{1}{\boldsymbol{u}_0} \le c_1L^4(\log_2 L + 1)^2 + c_2, \qquad
  L = \log_2\frac{4(n + 1)}{\delta\varphi}\,,$$
$\boldsymbol{u}_0$ = `NLAlib.Schur.uDenseSchur`: $O(\log^4(n/(\delta\varphi)))$ bits up to
$(\log\log)^2$, the shift degree being $\Theta(L\log L)$.
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1]
(the bits of the eigenvalue solver); the Schur form costs no more bits. -/
theorem logb_inv_uDenseSchur_le : ∃ c₁ c₂ : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → Real.logb 2 (uDenseSchur n δ φ)⁻¹ ≤
      c₁ * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ 4 *
        (Real.logb 2 (Real.logb 2 (4 * (n + 1) / (δ * φ))) + 1) ^ 2 + c₂ :=
  sorry

/-- **The operation count of the dense Schur solver** (on every tape): there is an absolute
constant $c$ such that the static count of `NLAlib.Schur.denseSchur` at the order $n + 1$, $n_r$
regularizer words, $n_q$ core words, the shift degree $k$, the iteration cap $F$ and the leaf cap
$T$ has at most $c(n + 1)^3(k + 1)^5(n_r + n_q + 1)(F + 1)(T + 1)^2$ operations and tests: one
power of $k$ above the eigenvalue solver's, from the replays on the couplings and on the
accumulator. -/
theorem denseSchur_work_le (sG : ℕ) : ∃ c : ℕ, ∀ n nr nq k F T : ℕ,
    Count.size (stmtCost (denseSchur (O := O) (Q := Q) sG).body [n + 1, nr, nq, k, F, T]) ≤
      c * (n + 1) ^ 3 * (k + 1) ^ 5 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2 :=
  sorry

/-- **The operation count of the dense Schur solver is $n^3$ times a polylogarithm**: there are
constants $C$ and $p$ such that for every order $n + 1$, $0 < \delta \le 1$ and
$0 < \varphi \le 1$, the static count at `NLAlib.Schur.denseSchurDims` is at most
$C(n + 1)^3L^p$, $L = \log_2(4(n + 1)/(\delta\varphi))$. The exponent found by the proof is about
$12$; [BanksGarzaVargasSrivastava2022, Theorem 1.4]'s is $2$ for the eigenvalues alone, with a
run-time count over the deflation tree. -/
theorem denseSchur_work_le_polylog (sG : ℕ) : ∃ (C : ℝ) (p : ℕ), ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ →
    δ ≤ 1 → 0 < φ → φ ≤ 1 →
    (Count.size (stmtCost (denseSchur (O := O) (Q := Q) sG).body (denseSchurDims n δ φ)) : ℝ) ≤
      C * ((n : ℝ) + 1) ^ 3 * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ p :=
  sorry

end Theorems

end NLAlib.Schur
