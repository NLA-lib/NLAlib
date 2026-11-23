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

/-- **The terms of the precision threshold at two tolerances**: below
`NLAlib.Schur.uDenseSchurAtWith`, $\boldsymbol{u}$ is below each of its eight terms. -/
theorem le_of_le_uDenseSchurAtWith {n : ℕ} {δR δC φ u : ℝ} {np RL : ℕ}
    (hu : u ≤ uDenseSchurAtWith n δR δC φ np RL) :
    u ≤ uSmallEigReduce (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreGapTail
        ginibreConditionTail ∧
      u ≤ denseSchurDelta n δC / (3200 * ((n : ℝ) + 1) ^ 2) ∧
      u ≤ smallEigGap (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreGapTail *
        smallEigCond (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreConditionTail /
          (28800 * ((n : ℝ) + 1) ^ 3) ∧
      u ≤ uShQR n (denseSchurDegree n δR φ) (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
        (denseSchurDelta n δC) (φ / 2) ∧
      u ≤ 1 / 100 ∧
      u ≤ uShQRSchurReplay n (denseSchurDegree n δR φ) np (denseSchurCapAt n δR δC φ) RL
        (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8 (denseSchurDelta n δC) ∧
      u ≤ δC / (4096 * ((n : ℝ) + 1) * denseSchurRotationsAtWith n δR δC φ np RL) ∧
      u ≤ δC / (64 * ((n : ℝ) + 1)) := by
  unfold uDenseSchurAtWith at hu
  simp only [le_min_iff] at hu
  exact hu

/-- **The precision threshold at two tolerances with a leaf is positive** for
$0 < \delta_R, \delta_C \le 1$ and $0 < \varphi \le 1$. -/
theorem uDenseSchurAtWith_pos {n : ℕ} {δR δC φ : ℝ} (np RL : ℕ) (hδR : 0 < δR) (hδR1 : δR ≤ 1)
    (hδC : 0 < δC) (hδC1 : δC ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < uDenseSchurAtWith n δR δC φ np RL := by
  obtain ⟨-, -, hg, hc, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδR hδR1 hφ hφ1
  obtain ⟨hd0, -⟩ := denseSchur_params_basic (n := n) hδC hδC1 hφ hφ1
  obtain ⟨hdR, -⟩ := denseSchur_params_basic (n := n) hδR hδR1 hφ hφ1
  have hk := denseSchurDegree_pos n δR φ
  have hR : 0 < (denseSchurRotationsAtWith n δR δC φ np RL : ℝ) := by
    unfold denseSchurRotationsAtWith; positivity
  have h1 : 0 < uSmallEigReduce (n + 1) 4 (denseSchurDelta n δR) (φ / 2) ginibreGapTail
      ginibreConditionTail := by unfold uSmallEigReduce; positivity
  have h4 := uShQR_pos (n := n) hk (by linarith : (1 : ℝ) ≤ 2 * denseSchurB n δR φ)
    (half_pos hΓ) hd0 (by norm_num : (0 : ℝ) < 8) (half_pos hφ)
  have h6 : 0 < uShQRSchurReplay n (denseSchurDegree n δR φ) np (denseSchurCapAt n δR δC φ) RL
      (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8 (denseSchurDelta n δC) := by
    have := shqrBudget_pos (n := n) (by linarith : (1 : ℝ) ≤ 2 * denseSchurB n δR φ)
      (half_pos hΓ) hd0
    unfold uShQRSchurReplay; positivity
  unfold uDenseSchurAtWith
  simp only [lt_min_iff]
  exact ⟨h1, by positivity, by positivity, h4, by norm_num, h6, by positivity, by positivity⟩

/-- **The orthogonality bound at two tolerances is at most $\delta_C$**: below the threshold of
a leaf, $58R\boldsymbol{u} \le \delta_C$ and $4096(n + 1)R\boldsymbol{u} \le \delta_C$, $R$ =
`NLAlib.Schur.denseSchurRotationsAtWith`. -/
theorem mul_denseSchurRotationsAtWith_le {n : ℕ} {δR δC φ u : ℝ} {np RL : ℕ} (hδC : 0 < δC)
    (hu : u ≤ uDenseSchurAtWith n δR δC φ np RL) :
    58 * (denseSchurRotationsAtWith n δR δC φ np RL : ℝ) * u ≤ δC ∧
      4096 * ((n : ℝ) + 1) * (denseSchurRotationsAtWith n δR δC φ np RL : ℝ) * u ≤ δC := by
  have h7 := (le_of_le_uDenseSchurAtWith hu).2.2.2.2.2.2.1
  have hR : 0 < (denseSchurRotationsAtWith n δR δC φ np RL : ℝ) := by
    unfold denseSchurRotationsAtWith; positivity
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hK : 0 < 4096 * ((n : ℝ) + 1) * (denseSchurRotationsAtWith n δR δC φ np RL : ℝ) := by
    positivity
  have hRu : 4096 * ((n : ℝ) + 1) * (denseSchurRotationsAtWith n δR δC φ np RL : ℝ) * u ≤ δC := by
    have := mul_le_mul_of_nonneg_left h7 hK.le
    rwa [mul_div_cancel₀ _ hK.ne'] at this
  refine ⟨?_, hRu⟩
  by_cases hu0 : u ≤ 0
  · nlinarith
  · push Not at hu0
    have := mul_le_mul_of_nonneg_right hn (by positivity :
      (0 : ℝ) ≤ 4096 * ((denseSchurRotationsAtWith n δR δC φ np RL : ℝ) * u))
    nlinarith

/-- The leaf cap at two tolerances is the cap of the forward form at the norm bound $32$. -/
theorem denseSchurLeafCapAt_eq (n : ℕ) (δR δC φ : ℝ) : denseSchurLeafCapAt n δR δC φ =
    smallEigForwardCap (denseSchurDegree n δR φ) 32
      (shqrSmallEigAccuracy n (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
        (denseSchurDelta n δC)) (denseSchurLeafFailureAt n δR δC φ) ginibreGapTail
      ginibreConditionTail := by
  unfold denseSchurLeafCapAt shqrSmallEigCap denseSchurLeafFailureAt
  rw [show (4 : ℝ) * 8 = 32 by norm_num]

/-- The core's words at two tolerances are those of the Schur core with the small-eigenvalue
program. -/
theorem shqrSchurParamsAt_eq (n : ℕ) (δR δC φ : ℝ) :
    shqrSchurParams n (denseSchurDegree n δR φ) (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2)
      8 (denseSchurDelta n δC) (φ / 2) ginibreGapTail ginibreConditionTail =
    denseSchurThresholdAt n δR δC φ ::
      (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ) := by
  unfold shqrSchurParams shqrSmallEigParams denseSchurThresholdAt denseSchurShQRParamsAt
    denseSchurLeafParamsAt denseSchurLeafFailureAt
  rw [show (4 : ℝ) * 8 = 32 by norm_num]

/-- The core's rotation count at two tolerances with the small-eigenvalue program. -/
theorem shqrSmallEigRotationsAt_eq (n : ℕ) (δR δC φ : ℝ) :
    shqrSmallEigRotations n (denseSchurDegree n δR φ) (2 * denseSchurB n δR φ)
      (denseSchurΓ n δR φ / 2) 8 (denseSchurDelta n δC) (φ / 2) ginibreGapTail
      ginibreConditionTail =
    shqrSchurRotations n (denseSchurDegree n δR φ)
      (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ).length
      (denseSchurCapAt n δR δC φ)
      (smallEigLeafRotations (denseSchurDegree n δR φ) (denseSchurLeafCapAt n δR δC φ)) := by
  unfold shqrSmallEigRotations shqrSmallEigParams denseSchurShQRParamsAt denseSchurLeafParamsAt
    denseSchurCapAt denseSchurLeafCapAt denseSchurLeafFailureAt
  rw [show (4 : ℝ) * 8 = 32 by norm_num]

/-! ### Closed forms of the class -/

/-- The inverted tail at a scale of at least $\varphi$ is $(\varphi/s)^{2/b}$. -/
private theorem polyLogTailInverse_eq_rpow {c : PolyLogTail} {N K φ : ℝ} (hb : 0 < c.b)
    (hφ : 0 < φ) (hs : φ ≤ polyLogTailScale c N K) :
    polyLogTailInverse c N K φ = (φ / polyLogTailScale c N K) ^ (2 / c.b) := by
  have hs0 : 0 < polyLogTailScale c N K := hφ.trans_le hs
  exact min_eq_right (Real.rpow_le_one (by positivity) ((div_le_one hs0).mpr hs) (by positivity))

/-- The inverted condition tail in closed form. -/
private theorem conditionTailInverse_eq {N K φ : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K + 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) : polyLogTailInverse ginibreConditionTail.normalize N K φ =
      φ / (1152 * Real.exp 1 ^ 2 * N ^ 3 * (K + 1) ^ 2) := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hC : max (128 * Real.exp 1) 1 = 128 * Real.exp 1 := max_eq_left (by linarith)
  have hs : polyLogTailScale ginibreConditionTail.normalize N K =
      1152 * Real.exp 1 ^ 2 * N ^ 3 * (K + 1) ^ 2 := by
    have hE2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    simp only [polyLogTailScale, PolyLogTail.normalize, ginibreConditionTail, hC]
    norm_num
    ring_nf
    rw [hE2]
    ring
  have h1 : 1 ≤ 1152 * Real.exp 1 ^ 2 * N ^ 3 * (K + 1) ^ 2 := by
    have h2 : 1 ≤ Real.exp 1 ^ 2 := one_le_pow₀ he
    have h3 : 1 ≤ N ^ 3 := one_le_pow₀ hN
    have h4 : 1 ≤ (K + 1) ^ 2 := one_le_pow₀ hK
    have h5 : 1 ≤ Real.exp 1 ^ 2 * N ^ 3 := one_le_mul_of_one_le_of_one_le h2 h3
    have h6 := one_le_mul_of_one_le_of_one_le h5 h4
    nlinarith
  rw [polyLogTailInverse_eq_rpow (by norm_num [PolyLogTail.normalize, ginibreConditionTail]) hφ
    (by rw [hs]; linarith), hs]
  norm_num [PolyLogTail.normalize, ginibreConditionTail]

/-- The inverted gap tail in closed form. -/
private theorem gapTailInverse_eq {N K φ : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K + 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) : polyLogTailInverse ginibreGapTail.normalize N K φ =
      φ ^ 3 / (2048 ^ 3 * 49 ^ 3 * Real.exp 1 ^ 4 * N ^ 11 * (K + 1) ^ 6) := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hC : max (2048 * Real.exp 1) 1 = 2048 * Real.exp 1 := max_eq_left (by linarith)
  have hN0 : 0 ≤ N := by linarith
  have hs : polyLogTailScale ginibreGapTail.normalize N K =
      2048 * Real.exp 1 * N ^ (11 / 3 : ℝ) * (K + 1) ^ 2 * (49 * Real.exp (1 / 3)) := by
    simp only [polyLogTailScale, PolyLogTail.normalize, ginibreGapTail, hC]
    norm_num
  have hNp : (N ^ (11 / 3 : ℝ)) ^ 3 = N ^ 11 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
  have hEp : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hs3 : polyLogTailScale ginibreGapTail.normalize N K ^ 3 =
      2048 ^ 3 * 49 ^ 3 * Real.exp 1 ^ 4 * N ^ 11 * (K + 1) ^ 6 := by
    rw [hs, mul_pow, mul_pow, mul_pow, mul_pow, hNp, mul_pow, hEp]
    ring
  have h1 : 1 ≤ polyLogTailScale ginibreGapTail.normalize N K := by
    rw [hs]
    have h2 : 1 ≤ N ^ (11 / 3 : ℝ) := Real.one_le_rpow hN (by norm_num)
    have h3 : 1 ≤ (K + 1) ^ 2 := one_le_pow₀ hK
    have h4 : 1 ≤ Real.exp (1 / 3) := Real.one_le_exp (by norm_num)
    have h5 := one_le_mul_of_one_le_of_one_le h2 h3
    have h6 := one_le_mul_of_one_le_of_one_le he h5
    have h7 := one_le_mul_of_one_le_of_one_le h6 h4
    nlinarith
  rw [polyLogTailInverse_eq_rpow (by norm_num [PolyLogTail.normalize, ginibreGapTail]) hφ
    (hφ1.trans h1)]
  have e23 : (2 : ℝ) / ginibreGapTail.normalize.b = ((3 : ℕ) : ℝ) := by
    norm_num [PolyLogTail.normalize, ginibreGapTail]
  rw [e23, Real.rpow_natCast, div_pow, hs3]

/-- The perturbation scale and the norm ratio of the regularizer: with
$X = \sqrt{n + 1}\,W/\delta \ge 3$, the scale is $\gamma/2 = \delta/(128\sqrt{n + 1}\,W)$ and the
ratio $K$ of the inverted tails satisfies $1 \le K + 1 \le 514X$. -/
private theorem denseSchur_scale_bounds {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    smallEigScale (denseSchurDelta n δ) (φ / 2) / 2 =
        δ / (128 * (√((n : ℝ) + 1) * smallEigNoiseLevel (φ / 2))) ∧
      3 ≤ √((n : ℝ) + 1) * smallEigNoiseLevel (φ / 2) / δ ∧
      1 ≤ (4 + 4 * (smallEigScale (denseSchurDelta n δ) (φ / 2) / 2)) /
        (smallEigScale (denseSchurDelta n δ) (φ / 2) / 2) + 1 ∧
      (4 + 4 * (smallEigScale (denseSchurDelta n δ) (φ / 2) / 2)) /
        (smallEigScale (denseSchurDelta n δ) (φ / 2) / 2) + 1 ≤
        514 * (√((n : ℝ) + 1) * smallEigNoiseLevel (φ / 2) / δ) := by
  have hr : 1 ≤ √((n : ℝ) + 1) := Real.one_le_sqrt.mpr (by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith)
  have hW : 3 ≤ smallEigNoiseLevel (φ / 2) := by
    unfold smallEigNoiseLevel
    linarith [Real.sqrt_nonneg (Real.log (4 / (φ / 2)))]
  have e : smallEigScale (denseSchurDelta n δ) (φ / 2) / 2 =
      δ / (128 * (√((n : ℝ) + 1) * smallEigNoiseLevel (φ / 2))) := by
    unfold smallEigScale denseSchurDelta
    field_simp
    norm_num
  rw [e]
  set r := √((n : ℝ) + 1)
  set W := smallEigNoiseLevel (φ / 2)
  have hr0 : 0 < r := by linarith
  have hW0 : 0 < W := by linarith
  have hX : 3 ≤ r * W / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have eK : (4 + 4 * (δ / (128 * (r * W)))) / (δ / (128 * (r * W))) + 1 =
      512 * (r * W / δ) + 5 := by
    field_simp
    ring
  rw [eK]
  exact ⟨rfl, hX, by linarith, by linarith⟩

/-- **The condition bound in closed form**: for $0 < \delta \le 1$ and $0 < \varphi \le 1$,
$B \le 2^{36}(n + 1)^4W^2/(\delta^2\varphi)$ with $W = 3 + \sqrt{\log(8/\varphi)}$
(`NLAlib.SmallEig.smallEigNoiseLevel` at $\varphi/2$), from the inverted condition tail
$(128e, 3, 2, 2)$. -/
theorem denseSchurB_le {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    denseSchurB n δ φ ≤
      2 ^ 36 * ((n : ℝ) + 1) ^ 4 * smallEigNoiseLevel (φ / 2) ^ 2 / (δ ^ 2 * φ) := by
  obtain ⟨-, hX, hK1, hK⟩ := denseSchur_scale_bounds (n := n) (φ := φ) hδ hδ1
  have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hNc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  have hr2 : √((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  unfold denseSchurB smallEigCond ginibreConditionThreshold
  rw [conditionTailInverse_eq hN hK1 (by positivity) (by linarith), hNc]
  rw [hNc] at hN
  set K := (4 + 4 * (smallEigScale (denseSchurDelta n δ) (φ / 2) / 2)) /
    (smallEigScale (denseSchurDelta n δ) (φ / 2) / 2)
  set r := √((n : ℝ) + 1)
  set W := smallEigNoiseLevel (φ / 2)
  set N := (n : ℝ) + 1
  have he2 : Real.exp 1 ^ 2 ≤ 7.4 := by
    have := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    nlinarith
  have hsq : (K + 1) ^ 2 ≤ 514 ^ 2 * (N * W ^ 2 / δ ^ 2) := by
    calc (K + 1) ^ 2 ≤ (514 * (r * W / δ)) ^ 2 := by gcongr
      _ = 514 ^ 2 * (N * W ^ 2 / δ ^ 2) := by rw [← hr2]; ring
  have hQ : 0 ≤ N * W ^ 2 / δ ^ 2 := by positivity
  have e : 2 / (φ / 2 / 4 / (1152 * Real.exp 1 ^ 2 * N ^ 3 * (K + 1) ^ 2)) =
      18432 * Real.exp 1 ^ 2 * N ^ 3 * (K + 1) ^ 2 / φ := by
    field_simp
    norm_num
  have e2 : 2 ^ 36 * N ^ 4 * W ^ 2 / (δ ^ 2 * φ) = 2 ^ 36 * N ^ 3 * (N * W ^ 2 / δ ^ 2) / φ := by
    field_simp
  rw [e, e2]
  gcongr ?_ / φ
  calc 18432 * Real.exp 1 ^ 2 * N ^ 3 * (K + 1) ^ 2
      ≤ 18432 * 7.4 * N ^ 3 * (514 ^ 2 * (N * W ^ 2 / δ ^ 2)) := by gcongr
    _ ≤ 2 ^ 36 * N ^ 3 * (N * W ^ 2 / δ ^ 2) := by
        have : 0 ≤ N ^ 3 * (N * W ^ 2 / δ ^ 2) := by positivity
        nlinarith

/-- **The separation in closed form**: for $0 < \delta \le 1$ and $0 < \varphi \le 1$,
$\Gamma \ge \delta^7\varphi^3/(2^{134}(n + 1)^{29/2}W^7)$ with $W = 3 + \sqrt{\log(8/\varphi)}$
(`NLAlib.SmallEig.smallEigNoiseLevel` at $\varphi/2$), from the inverted gap tail
$(2048e, 11/3, 2/3, 2)$. -/
theorem le_denseSchurΓ {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    δ ^ 7 * φ ^ 3 / (2 ^ 134 * ((n : ℝ) + 1) ^ (29 / 2 : ℝ) * smallEigNoiseLevel (φ / 2) ^ 7) ≤
      denseSchurΓ n δ φ := by
  obtain ⟨hγ, hX, hK1, hK⟩ := denseSchur_scale_bounds (n := n) (φ := φ) hδ hδ1
  have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hNc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  have hN0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hr2 : √((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt hN0
  have hrp : ((n : ℝ) + 1) ^ (29 / 2 : ℝ) = ((n : ℝ) + 1) ^ 14 * √((n : ℝ) + 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add' hN0 (by norm_num)]
    norm_num
  have hnorm : ginibreGapTail.normalize.c = 2 := by
    norm_num [PolyLogTail.normalize, ginibreGapTail]
  unfold denseSchurΓ smallEigGap ginibreGapThreshold
  set K := (4 + 4 * (smallEigScale (denseSchurDelta n δ) (φ / 2) / 2)) /
    (smallEigScale (denseSchurDelta n δ) (φ / 2) / 2)
  rw [hnorm, gapTailInverse_eq hN hK1 (by positivity) (by
    rw [div_le_one (by positivity)]
    norm_num
    linarith), hNc, hγ, hrp]
  rw [hNc] at hN
  set r := √((n : ℝ) + 1)
  set W := smallEigNoiseLevel (φ / 2)
  set N := (n : ℝ) + 1
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hW0 : 0 < W := by
    by_contra h
    have h' : W ≤ 0 := not_lt.mp h
    have : r * W / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hr0.le h') hδ.le
    linarith
  have he4 : Real.exp 1 ^ 4 ≤ 55 := by
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    calc Real.exp 1 ^ 4 ≤ 2.72 ^ 4 := by gcongr; linarith
      _ ≤ 55 := by norm_num
  have h6 : (K + 1) ^ 6 ≤ 514 ^ 6 * (N ^ 3 * W ^ 6 / δ ^ 6) := by
    calc (K + 1) ^ 6 ≤ (514 * (r * W / δ)) ^ 6 := by gcongr
      _ = 514 ^ 6 * ((r ^ 2) ^ 3 * W ^ 6 / δ ^ 6) := by ring
      _ = 514 ^ 6 * (N ^ 3 * W ^ 6 / δ ^ 6) := by rw [hr2]
  have hS : 2048 ^ 3 * 49 ^ 3 * Real.exp 1 ^ 4 * N ^ 11 * (K + 1) ^ 6 ≤
      2048 ^ 3 * 49 ^ 3 * 55 * 514 ^ 6 * (N ^ 14 * W ^ 6 / δ ^ 6) := by
    calc 2048 ^ 3 * 49 ^ 3 * Real.exp 1 ^ 4 * N ^ 11 * (K + 1) ^ 6
        ≤ 2048 ^ 3 * 49 ^ 3 * 55 * N ^ 11 * (514 ^ 6 * (N ^ 3 * W ^ 6 / δ ^ 6)) := by gcongr
      _ = _ := by ring
  have hS0 : 0 < 2048 ^ 3 * 49 ^ 3 * Real.exp 1 ^ 4 * N ^ 11 * (K + 1) ^ 6 := by
    have : 0 < K + 1 := by linarith
    positivity
  have e : δ / (128 * (r * W)) * ((φ / 2 / (4 * 2 ^ (2 : ℝ))) ^ 3 /
      (2048 ^ 3 * 49 ^ 3 * Real.exp 1 ^ 4 * N ^ 11 * (K + 1) ^ 6)) / 2 =
      δ * φ ^ 3 / (256 * 32 ^ 3 * (r * W)) /
        (2048 ^ 3 * 49 ^ 3 * Real.exp 1 ^ 4 * N ^ 11 * (K + 1) ^ 6) := by
    norm_num
    field_simp
    norm_num
  rw [e, le_div_iff₀ hS0]
  have hA : 0 ≤ δ ^ 7 * φ ^ 3 / (2 ^ 134 * (N ^ 14 * r) * W ^ 7) := by positivity
  refine (mul_le_mul_of_nonneg_left hS hA).trans ?_
  have hB : 0 ≤ δ * φ ^ 3 / (r * W) := by positivity
  have e1 : δ ^ 7 * φ ^ 3 / (2 ^ 134 * (N ^ 14 * r) * W ^ 7) *
      (2048 ^ 3 * 49 ^ 3 * 55 * 514 ^ 6 * (N ^ 14 * W ^ 6 / δ ^ 6)) =
      δ * φ ^ 3 / (r * W) * (2048 ^ 3 * 49 ^ 3 * 55 * 514 ^ 6 / 2 ^ 134) := by
    field_simp
  have e3 : δ * φ ^ 3 / (256 * 32 ^ 3 * (r * W)) =
      δ * φ ^ 3 / (r * W) * (1 / (256 * 32 ^ 3)) := by
    field_simp
  rw [e1, e3]
  exact mul_le_mul_of_nonneg_left (by norm_num) hB

end NLAlib.Schur
