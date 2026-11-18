/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination
public import NLAlib.Eigensolvers.SmallEig.Decoupler
public import NLAlib.Eigensolvers.SmallEig.Leaf
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleContract

/-!
# The core of the small-eigenvalue solver

The deflation of [BanksGarzaVargasSrivastava2025, §6] is the merged rounded worklist
(`NLAlib.ShiftedQR.solveRoundedWith`) at the bottom width $k = 1$, with the decoupler
`NLAlib.SmallEig.smallEigDecoupler` and the order-one leaf `NLAlib.SmallEig.copyLeaf`. On an upper
Hessenberg matrix in the class of the core (condition $B_c$, separation $g_c$) it stores, except
with probability at most $\varphi/4$, all eigenvalues of a matrix within $\delta/4$
(Theorem 6.1 in class form: no shattering vocabulary).

## Main definitions

* `NLAlib.SmallEig.smallEigCore`: the program `[N, k, np, F, T] (A, Thr, P) → (Out, Fl)`.
* `NLAlib.SmallEig.SmallEigCoreInput`: the memory of a call.

## Main results

* `NLAlib.ShiftedQR.solveRoundedWith_pwrites`,
  `NLAlib.SmallEig.smallEigCore_measureReal_not_spectrum_le`,
  `NLAlib.SmallEig.smallEigCore_terminates`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The core of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, Theorem 6.1]):
the rounded worklist `NLAlib.ShiftedQR.solveRoundedWith` with the decoupler
`NLAlib.SmallEig.smallEigDecoupler` and the order-one Schur leaf `NLAlib.SmallEig.identityLeaf`,
in Schur mode. Run at the bottom width $k = 1$. The interface is
`[N, k, np, F, T, ns, w] (A, Thr, P, U) → (A, U, Fl)`.
Algorithm: small-eig -/
def smallEigCore (sG : ℕ) : Impl O Q :=
  solveRoundedWith (smallEigDecoupler (O := O) (Q := Q) sG) (identityLeaf (O := O) (Q := Q))

end Program

/-- The backward error of the decoupler at the norm bound $2\Sigma$ of the core is at most
$\omega/100$: for tail records with $b_1, b_2 > 0$, $n_{\max} \ge 1$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$ and $0 \le \boldsymbol{u} \le$ `NLAlib.SmallEig.uSmallEig` (the `Decouple`
term of the threshold). -/
theorem smallEigDecoupleError_le_omega {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ u : ℝ} (hu0 : 0 ≤ u) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) :
    0 ≤ smallEigDecoupleError nmax S δ φ c₂ u (2 * S) ∧
      smallEigDecoupleError nmax S δ φ c₂ u (2 * S) ≤ smallEigOmega nmax S δ φ c₁ c₂ / 100 := by
  have hS0 : 0 < S := hδ.trans_le hδS
  obtain ⟨-, -, -, -, -, -, hg⟩ := smallEigDecoupler_precision hb₁ hb₂ hn hδ hδS hφ hφ1 hu
  obtain ⟨-, -, -, -, -, -, hω, hωδ, -⟩ := smallEigParams_spec hb₁ hb₂ hn hδ hδS hφ hφ1
  have hBc := smallEigCondition_ge hb₂ hn hS0.le hδ hφ hφ1
  have hη₁ := smallEigInnerRadius_pos hb₁ hb₂ hn hδ hδS hφ hφ1
  obtain ⟨hβ, hβS⟩ := smallEigAccuracy_le hb₁ hb₂ hn hδ hδS hφ hφ1
  have hD1 : smallEigDecouplerFailure nmax φ / 2 ≤ 1 := by
    unfold smallEigDecouplerFailure
    rw [div_div, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
    nlinarith
  have hsep := smallEigSeparation_pos hb₁ hn hS0.le hδ hφ hφ1
  have hη₁6 := oneEigInnerRadius_le hβ hβS
    (by positivity : 0 < smallEigSeparation nmax S δ φ c₁ / 4) hD1
  have hη₂β : smallEigOuterRadius nmax S δ φ c₁ c₂ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ / 40 :=
    min_le_left _ _
  have hη₁S : smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ S := by
    change oneEigInnerRadius _ _ _ _ ≤ S
    unfold smallEigOuterRadius at hη₂β
    linarith
  set m := smallEigDecoupleSteps nmax S δ φ c₂
  set y := 300 * ((nmax : ℝ) + 1) ^ 2 * u with hy
  have hy0 : 0 ≤ y := by positivity
  set r := 22 * (2 * S) / smallEigInnerRadius nmax S δ φ c₁ c₂
  have hr : 2 ≤ r := by rw [le_div_iff₀ hη₁]; linarith
  have hZ : (m : ℝ) + 1 ≤ r ^ m := by
    have h1 : ((m : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
    exact h1.trans (pow_le_pow_left₀ (by norm_num) hr m)
  have hsq : 1 ≤ √((nmax : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith [(nmax.cast_nonneg : (0 : ℝ) ≤ nmax)]
  have hD : 0 < 86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) * r ^ m *
      √((nmax : ℝ) + 1) := by positivity
  rw [le_div_iff₀ hD] at hg
  have hyZ : y * ((m : ℝ) + 1) * (11008 * S) ≤ smallEigOmega nmax S δ φ c₁ c₂ := by
    have h1 : y * ((m : ℝ) + 1) * (5504 * S) ≤ y * (86 * (8 * smallEigCondition nmax S δ φ c₂) *
        (2 * S) * r ^ m * √((nmax : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hy0 |>.trans' (by rw [mul_assoc])
      calc ((m : ℝ) + 1) * (5504 * S) ≤ r ^ m * (86 * (8 * 4) * (2 * S) * 1) := by nlinarith
        _ ≤ 86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) * r ^ m *
            √((nmax : ℝ) + 1) := by
          have : 0 ≤ r ^ m := by positivity
          have := mul_le_mul_of_nonneg_left hBc (by positivity : (0 : ℝ) ≤ 86 * 8 * (2 * S) * r ^ m)
          nlinarith [mul_le_mul_of_nonneg_left hsq
            (by positivity :
              (0 : ℝ) ≤ 86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) * r ^ m)]
    linarith
  have hωS : smallEigOmega nmax S δ φ c₁ c₂ ≤ S := by
    have : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
    nlinarith
  have hmy : (m : ℝ) * y ≤ 1 / 2 := by nlinarith
  have hpow : (1 + y) ^ m - 1 ≤ 2 * m * y := by
    linarith [ShiftedQR.one_add_pow_le_one_add_two_mul hy0 (by linarith : (m : ℝ) * y ≤ 1)]
  have hpow0 : 0 ≤ (1 + y) ^ m - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := m) (le_add_of_nonneg_right hy0); linarith
  unfold smallEigDecoupleError
  rw [← hy]
  constructor
  · positivity
  · nlinarith

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

end Theorems

end NLAlib.SmallEig
