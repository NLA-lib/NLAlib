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
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSchurLeaf
public import NLAlib.Eigensolvers.HessenbergAccumulate
public import NLAlib.Eigensolvers.Schur.Composition

/-!
# The parameters of the dense Schur solver

The words, dimensions, rotation count and precision threshold of the dense Schur solver
(`NLAlib.Eigensolvers.Schur.Dense`), as functions of $(n, \delta, \varphi)$ only. With
$\delta' = \delta/(16\sqrt{n + 1})$: the regularizer at the words `NLAlib.SmallEig.smallEigParams`
for the order $n + 1$, the norm bound $4$, the error $\delta'$ and the failure $\varphi/2$, into
the class $(B, \Gamma) = (2/t_2, t_1/2)$; the core at the class $(2B, \Gamma/2)$, the norm bound
$8$, the error $\delta'$ and the failure $\varphi/2$. The threshold is positive, and below it the
accumulator and residual errors of the composition are at most $\delta$.

## Main definitions

* `NLAlib.Schur.denseSchurParamsWith`, `NLAlib.Schur.denseSchurDimsWith`,
  `NLAlib.Schur.denseSchurRotationsWith`, `NLAlib.Schur.uDenseSchurWith`: the words, dimensions,
  rotation count and precision threshold with a leaf's words, cap and rotation count.
* `NLAlib.Schur.denseSchurParams`, `NLAlib.Schur.denseSchurDims`,
  `NLAlib.Schur.denseSchurRotations`, `NLAlib.Schur.uDenseSchur`: those of the `SmallEig` leaf.
* `NLAlib.Schur.denseSchurParamsAt`, `NLAlib.Schur.denseSchurDimsAt`,
  `NLAlib.Schur.denseSchurRotationsAt`, `NLAlib.Schur.uDenseSchurAt`,
  `NLAlib.Schur.uDenseSchurAtWith`: the same at two tolerances.

## Main results

* `NLAlib.Schur.uDenseSchurWith_pos`, `NLAlib.Schur.uDenseSchur_pos`: the threshold is positive.
* `NLAlib.Schur.mul_denseSchurRotations_le`, `NLAlib.Schur.denseSchur_errors_le`: the errors
  below the threshold.
* `NLAlib.Schur.denseSchurB_le`, `NLAlib.Schur.le_denseSchurΓ`: the class in closed form.
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
  min (uShQRSchurReplay n (denseSchurDegree n δ φ) np (denseSchurCap n δ φ) RL
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
      u ≤ uShQRSchurReplay n (denseSchurDegree n δ φ) np (denseSchurCap n δ φ) RL
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
  have h6 : 0 < uShQRSchurReplay n (denseSchurDegree n δ φ) np (denseSchurCap n δ φ) RL
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

/-- **The errors of the dense Schur solver**: below the threshold, the composed relative
accumulator error $\varepsilon = (1 + 27(n + 1)^2\boldsymbol{u})(1 + 24\boldsymbol{u})^{R_c} - 1$
of the reducer and the core is at most $1/16$, $2\varepsilon + \varepsilon^2 \le 58R\boldsymbol{u}$
($R = (n + 1)^2 + R_c$), and the residual of the generic composition at the norm-estimate
constants $(1/2, 2)$ is at most $\delta$. -/
theorem denseSchur_errors_le {n Rc : ℕ} {δ u : ℝ} (hδ : 0 < δ) (hu0 : 0 ≤ u)
    (hR : 4096 * ((n : ℝ) + 1) * (((n + 1) ^ 2 + Rc : ℕ) : ℝ) * u ≤ δ)
    (hu2 : u ≤ denseSchurDelta n δ / (3200 * ((n : ℝ) + 1) ^ 2))
    (hu8 : u ≤ δ / (64 * ((n : ℝ) + 1))) (hδ1 : δ ≤ 1) :
    0 ≤ (1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1 ∧
      (1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1 ≤ 1 / 16 ∧
      2 * ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1) +
        ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1) ^ 2 ≤
          58 * (((n + 1) ^ 2 + Rc : ℕ) : ℝ) * u ∧
      2 * 2 * √((n : ℝ) + 1) * (denseSchurDelta n δ / 2 +
        3 * (50 * ((n : ℝ) + 1) ^ 2 * u) / (1 / 2) + denseSchurDelta n δ +
          8 * ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1) / (1 / 2)) +
        8 * ((n : ℝ) + 1) * u ≤ δ := by
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  set R : ℝ := (((n + 1) ^ 2 + Rc : ℕ) : ℝ) with hRdef
  have hRe : R = N ^ 2 + Rc := by rw [hRdef, hN]; push_cast; ring
  have hRc0 : (0 : ℝ) ≤ Rc := Nat.cast_nonneg _
  have hRu : R * u ≤ 1 / 4096 := by
    have h1 : 4096 * (R * u) ≤ 4096 * N * R * u := by
      have := mul_le_mul_of_nonneg_right hN1 (by positivity : (0 : ℝ) ≤ 4096 * (R * u))
      nlinarith
    linarith
  have hz : 24 * (Rc : ℝ) * u ≤ 1 / 8 := by
    have : (Rc : ℝ) * u ≤ R * u := mul_le_mul_of_nonneg_right (by rw [hRe]; nlinarith) hu0
    linarith
  have hpow := one_add_mul_pow_sub_one_le hu0 hz
  have hpow1 : (1 : ℝ) ≤ (1 + 24 * u) ^ Rc := one_le_pow₀ (by linarith)
  set ε := (1 + 27 * N ^ 2 * u) * (1 + 24 * u) ^ Rc - 1 with hεdef
  have hε0 : 0 ≤ ε := by
    nlinarith [mul_le_mul_of_nonneg_left hpow1 (by positivity : (0 : ℝ) ≤ 1 + 27 * N ^ 2 * u)]
  -- $\varepsilon \le 28Ru$
  have hε : ε ≤ 28 * (R * u) := by
    have h1 : ε ≤ (1 + 27 * N ^ 2 * u) * (1 + 27 * Rc * u) - 1 := by
      have := mul_le_mul_of_nonneg_left (by linarith : (1 + 24 * u) ^ Rc ≤ 1 + 27 * Rc * u)
        (by positivity : (0 : ℝ) ≤ 1 + 27 * N ^ 2 * u)
      linarith
    have h2 : N ^ 2 * u * (Rc * u) ≤ (R * u) * (R * u) := by
      apply mul_le_mul <;> try positivity
      · rw [hRe]; nlinarith
      · rw [hRe]; nlinarith
    have h3 : (R * u) * (R * u) ≤ 1 / 4096 * (R * u) :=
      mul_le_mul_of_nonneg_right hRu (by positivity)
    have e : (1 + 27 * N ^ 2 * u) * (1 + 27 * Rc * u) - 1 =
        27 * (R * u) + 729 * (N ^ 2 * u * (Rc * u)) := by rw [hRe]; ring
    nlinarith
  refine ⟨hε0, by linarith, ?_, ?_⟩
  · have h1 : ε ^ 2 ≤ 28 * (R * u) * (28 / 4096) := by
      rw [sq]; exact mul_le_mul hε (by linarith) hε0 (by positivity)
    nlinarith
  · set s := √N with hs
    have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hN1
    have hsN : s ≤ N := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    set δ' := denseSchurDelta n δ with hδ'
    have hsδ : s * δ' = δ / 16 := by
      rw [hδ', denseSchurDelta, ← hN, ← hs]; field_simp
    have hNu : N ^ 2 * u ≤ δ' / 3200 := by
      rw [le_div_iff₀ (by positivity)] at hu2 ⊢; linarith
    have hNu8 : 8 * N * u ≤ δ / 8 := by
      rw [le_div_iff₀ (by positivity)] at hu8; linarith
    have hsε : s * ε ≤ 28 * (N * R * u) := by
      have := mul_le_mul hsN hε (by positivity) (by linarith)
      linarith [show N * (28 * (R * u)) = 28 * (N * R * u) by ring]
    have hNR : N * R * u ≤ δ / 4096 := by linarith
    have hs300 : s * (N ^ 2 * u) ≤ s * (δ' / 3200) := mul_le_mul_of_nonneg_left hNu (by positivity)
    have e : 2 * 2 * s * (δ' / 2 + 3 * (50 * N ^ 2 * u) / (1 / 2) + δ' + 8 * ε / (1 / 2)) +
        8 * N * u = 6 * (s * δ') + 1200 * (s * (N ^ 2 * u)) + 64 * (s * ε) + 8 * N * u := by
      ring
    rw [e]
    have : s * (δ' / 3200) = δ / 16 / 3200 := by rw [← hsδ]; ring
    nlinarith

/-- The leaf cap is the cap of the forward form at the norm bound $32$. -/
theorem denseSchurLeafCap_eq (n : ℕ) (δ φ : ℝ) : denseSchurLeafCap n δ φ =
    smallEigForwardCap (denseSchurDegree n δ φ) 32
      (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
        (denseSchurDelta n δ)) (denseSchurLeafFailure n δ φ) ginibreGapTail
      ginibreConditionTail := by
  unfold denseSchurLeafCap shqrSmallEigCap denseSchurLeafFailure
  rw [show (4 : ℝ) * 8 = 32 by norm_num]

/-- The core's words are those of the Schur core with the small-eigenvalue program. -/
theorem shqrSchurParams_eq (n : ℕ) (δ φ : ℝ) :
    shqrSchurParams n (denseSchurDegree n δ φ) (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
      (denseSchurDelta n δ) (φ / 2) ginibreGapTail ginibreConditionTail =
    denseSchurThreshold n δ φ :: (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ) := by
  unfold shqrSchurParams shqrSmallEigParams denseSchurThreshold denseSchurShQRParams
    denseSchurLeafParams denseSchurLeafFailure
  rw [show (4 : ℝ) * 8 = 32 by norm_num]

/-- The core's rotation count with the small-eigenvalue program. -/
theorem shqrSmallEigRotations_eq (n : ℕ) (δ φ : ℝ) :
    shqrSmallEigRotations n (denseSchurDegree n δ φ) (2 * denseSchurB n δ φ)
      (denseSchurΓ n δ φ / 2) 8 (denseSchurDelta n δ) (φ / 2) ginibreGapTail
      ginibreConditionTail =
    shqrSchurRotations n (denseSchurDegree n δ φ)
      (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ).length (denseSchurCap n δ φ)
      (smallEigLeafRotations (denseSchurDegree n δ φ) (denseSchurLeafCap n δ φ)) := by
  unfold shqrSmallEigRotations shqrSmallEigParams denseSchurShQRParams denseSchurLeafParams
    denseSchurCap denseSchurLeafCap denseSchurLeafFailure
  rw [show (4 : ℝ) * 8 = 32 by norm_num]

/-- The small constants of the corollaries: below the threshold, $58R\boldsymbol{u} \le 1/8$ and
$\delta + 4 \cdot 58R\boldsymbol{u}(1 + \delta) \le 2\delta$. -/
theorem denseSchur_orth_le {n : ℕ} {δ φ u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : u ≤ uDenseSchur n δ φ) :
    58 * (denseSchurRotations n δ φ : ℝ) * u ≤ δ ∧
      58 * (denseSchurRotations n δ φ : ℝ) * u ≤ 1 / 8 ∧
      δ + 4 * (58 * (denseSchurRotations n δ φ : ℝ) * u) *
        (1 + δ) ≤ 2 * δ := by
  obtain ⟨h58, -, h4096⟩ := mul_denseSchurRotationsWith_le hδ hδ1 (hu.trans (min_le_left _ _))
  have hR := (Nat.cast_nonneg (denseSchurRotations n δ φ) : (0 : ℝ) ≤ _)
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  change 58 * (denseSchurRotations n δ φ : ℝ) * u ≤ δ at h58
  change 4096 * ((n : ℝ) + 1) * (denseSchurRotations n δ φ : ℝ) * u ≤ δ at h4096
  have hRu : 4096 * ((denseSchurRotations n δ φ : ℝ) * u) ≤ δ := by
    by_cases hu0 : u ≤ 0
    · nlinarith
    · push Not at hu0
      have := mul_le_mul_of_nonneg_right hn (by positivity :
        (0 : ℝ) ≤ 4096 * ((denseSchurRotations n δ φ : ℝ) * u))
      nlinarith
  refine ⟨h58, by nlinarith, by nlinarith⟩

/-! ### Two tolerances

The regularizer at the tolerance $\delta_R$ and the core, the reducer's backward error, the
replays, the accumulator and the scaling at $\delta_C$, both in the units of the headline (each
through `NLAlib.Schur.denseSchurDelta`). The class $(B, \Gamma)$ and the shift degree depend on
$\delta_R$ only. At $\delta_R = \delta_C = \delta$ each definition is the one-tolerance definition
above (`NLAlib.Schur.denseSchurParamsAt_self` and its siblings, by `rfl`). -/

/-- The iteration cap $F$ of the core at the tolerances $(\delta_R, \delta_C)$. -/
noncomputable def denseSchurCapAt (n : ℕ) (δR δC φ : ℝ) : ℕ :=
  shqrCap n (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8 (denseSchurDelta n δC)

/-- The deflation threshold word of the core at the tolerances $(\delta_R, \delta_C)$. -/
noncomputable def denseSchurThresholdAt (n : ℕ) (δR δC φ : ℝ) : ℝ :=
  shqrDeflationThreshold n (denseSchurDegree n δR φ) (2 * denseSchurB n δR φ)
    (denseSchurΓ n δR φ / 2) 8 (denseSchurDelta n δC) (φ / 2)

/-- The shifted QR words of the core at the tolerances $(\delta_R, \delta_C)$. -/
noncomputable def denseSchurShQRParamsAt (n : ℕ) (δR δC φ : ℝ) : List ℝ :=
  shqrParams n (denseSchurDegree n δR φ) (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
    (denseSchurDelta n δC) (φ / 2)

/-- The failure a leaf may have at the tolerances $(\delta_R, \delta_C)$. -/
noncomputable def denseSchurLeafFailureAt (n : ℕ) (δR δC φ : ℝ) : ℝ :=
  shqrSmallEigFailure n (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
    (denseSchurDelta n δC) (φ / 2)

/-- **The words of the dense Schur solver at two tolerances with the leaf words `qs`**: the
regularizer's words at $\delta_R$, then the core's at $\delta_C$. -/
noncomputable def denseSchurParamsAtWith (n : ℕ) (δR δC φ : ℝ) (qs : List ℝ) : List ℝ :=
  denseSchurRegParams n δR φ ++
    (denseSchurThresholdAt n δR δC φ :: (denseSchurShQRParamsAt n δR δC φ ++ qs))

/-- The dimensions of a run at two tolerances with the leaf words `qs` and the leaf cap $T$. -/
noncomputable def denseSchurDimsAtWith (n : ℕ) (δR δC φ : ℝ) (qs : List ℝ) (T : ℕ) : List ℕ :=
  [n + 1, (denseSchurRegParams n δR φ).length,
    (denseSchurThresholdAt n δR δC φ :: (denseSchurShQRParamsAt n δR δC φ ++ qs)).length,
    denseSchurDegree n δR φ, denseSchurCapAt n δR δC φ, T]

/-- The rotation count $R$ at two tolerances, a leaf of $R_L$ rotation-equivalents and $n_p$ core
words after the threshold. -/
noncomputable def denseSchurRotationsAtWith (n : ℕ) (δR δC φ : ℝ) (np RL : ℕ) : ℕ :=
  (n + 1) ^ 2 + shqrSchurRotations n (denseSchurDegree n δR φ) np (denseSchurCapAt n δR δC φ) RL

/-- **The precision threshold at two tolerances** with a leaf of $R_L$ rotation-equivalents and
$n_p$ core words: the eight terms of `NLAlib.Schur.uDenseSchurWith`, the regularizer's at
$\delta_R$, the class transfer and $1/100$ unchanged, the reducer's, the core's, the replays', the
accumulator's and the scaling's at $\delta_C$. -/
noncomputable def uDenseSchurAtWith (n : ℕ) (δR δC φ : ℝ) (np RL : ℕ) : ℝ :=
  min (uSmallEigReduce (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreGapTail
    ginibreConditionTail) <|
  min (denseSchurDelta n δC / (3200 * ((n : ℝ) + 1) ^ 2)) <|
  min (smallEigGap (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreGapTail *
    smallEigCond (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreConditionTail /
      (28800 * ((n : ℝ) + 1) ^ 3)) <|
  min (uShQR n (denseSchurDegree n δR φ) (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
    (denseSchurDelta n δC) (φ / 2)) <|
  min (1 / 100) <|
  min (uShQRSchurReplay n (denseSchurDegree n δR φ) np (denseSchurCapAt n δR δC φ) RL
    (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8 (denseSchurDelta n δC)) <|
  min (δC / (4096 * ((n : ℝ) + 1) * denseSchurRotationsAtWith n δR δC φ np RL))
    (δC / (64 * ((n : ℝ) + 1)))

/-- The leaf words of the `SmallEig` leaf at two tolerances. -/
noncomputable def denseSchurLeafParamsAt (n : ℕ) (δR δC φ : ℝ) : List ℝ :=
  smallEigForwardParams (denseSchurDegree n δR φ) 32
    (shqrSmallEigAccuracy n (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
      (denseSchurDelta n δC))
    (denseSchurLeafFailureAt n δR δC φ) ginibreGapTail ginibreConditionTail

/-- The cap $T$ of the `SmallEig` leaf at two tolerances. -/
noncomputable def denseSchurLeafCapAt (n : ℕ) (δR δC φ : ℝ) : ℕ :=
  shqrSmallEigCap n (denseSchurDegree n δR φ) (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
    (denseSchurDelta n δC) (φ / 2) ginibreGapTail ginibreConditionTail

/-- **The words of the dense Schur solver at two tolerances** (`SmallEig` leaf). -/
noncomputable def denseSchurParamsAt (n : ℕ) (δR δC φ : ℝ) : List ℝ :=
  denseSchurParamsAtWith n δR δC φ (denseSchurLeafParamsAt n δR δC φ)

/-- **The dimensions of a run at two tolerances** (`SmallEig` leaf). -/
noncomputable def denseSchurDimsAt (n : ℕ) (δR δC φ : ℝ) : List ℕ :=
  denseSchurDimsAtWith n δR δC φ (denseSchurLeafParamsAt n δR δC φ) (denseSchurLeafCapAt n δR δC φ)

/-- **The rotation count at two tolerances** (`SmallEig` leaf). -/
noncomputable def denseSchurRotationsAt (n : ℕ) (δR δC φ : ℝ) : ℕ :=
  denseSchurRotationsAtWith n δR δC φ
    (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
    (smallEigLeafRotations (denseSchurDegree n δR φ) (denseSchurLeafCapAt n δR δC φ))

/-- **The precision threshold at two tolerances** (`SmallEig` leaf, with the leaf's own
`NLAlib.SmallEig.uSmallEigForward` at $\delta_C$). -/
noncomputable def uDenseSchurAt (n : ℕ) (δR δC φ : ℝ) : ℝ :=
  min (uDenseSchurAtWith n δR δC φ
      (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
      (smallEigLeafRotations (denseSchurDegree n δR φ) (denseSchurLeafCapAt n δR δC φ)))
    (uSmallEigForward (denseSchurDegree n δR φ) 32
      (shqrSmallEigAccuracy n (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
        (denseSchurDelta n δC)) (denseSchurLeafFailureAt n δR δC φ) ginibreGapTail
      ginibreConditionTail)

/-- The words at equal tolerances are the one-tolerance words. -/
theorem denseSchurParamsAt_self (n : ℕ) (δ φ : ℝ) :
    denseSchurParamsAt n δ δ φ = denseSchurParams n δ φ := rfl

/-- The dimensions at equal tolerances are the one-tolerance dimensions. -/
theorem denseSchurDimsAt_self (n : ℕ) (δ φ : ℝ) :
    denseSchurDimsAt n δ δ φ = denseSchurDims n δ φ := rfl

/-- The rotation count at equal tolerances is the one-tolerance count. -/
theorem denseSchurRotationsAt_self (n : ℕ) (δ φ : ℝ) :
    denseSchurRotationsAt n δ δ φ = denseSchurRotations n δ φ := rfl

/-- The threshold with a leaf at equal tolerances is the one-tolerance threshold. -/
theorem uDenseSchurAtWith_self (n : ℕ) (δ φ : ℝ) (np RL : ℕ) :
    uDenseSchurAtWith n δ δ φ np RL = uDenseSchurWith n δ φ np RL := rfl

/-- The threshold at equal tolerances is the one-tolerance threshold. -/
theorem uDenseSchurAt_self (n : ℕ) (δ φ : ℝ) : uDenseSchurAt n δ δ φ = uDenseSchur n δ φ := rfl

/-! ### Closed forms of the class -/

/-- **The condition bound in closed form**: for $0 < \delta \le 1$ and $0 < \varphi \le 1$,
$B \le 2^{36}(n + 1)^4W^2/(\delta^2\varphi)$ with $W = 3 + \sqrt{\log(8/\varphi)}$
(`NLAlib.SmallEig.smallEigNoiseLevel` at $\varphi/2$), from the inverted condition tail
$(128e, 3, 2, 2)$. -/
theorem denseSchurB_le {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    denseSchurB n δ φ ≤
      2 ^ 36 * ((n : ℝ) + 1) ^ 4 * smallEigNoiseLevel (φ / 2) ^ 2 / (δ ^ 2 * φ) := by
  sorry

/-- **The separation in closed form**: for $0 < \delta \le 1$ and $0 < \varphi \le 1$,
$\Gamma \ge \delta^7\varphi^3/(2^{134}(n + 1)^{29/2}W^7)$ with $W = 3 + \sqrt{\log(8/\varphi)}$
(`NLAlib.SmallEig.smallEigNoiseLevel` at $\varphi/2$), from the inverted gap tail
$(2048e, 11/3, 2/3, 2)$. -/
theorem le_denseSchurΓ {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    δ ^ 7 * φ ^ 3 / (2 ^ 134 * ((n : ℝ) + 1) ^ (29 / 2 : ℝ) * smallEigNoiseLevel (φ / 2) ^ 7) ≤
      denseSchurΓ n δ φ := by
  sorry

end NLAlib.Schur
