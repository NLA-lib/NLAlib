/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Contracts
public import NLAlib.Eigensolvers.SmallEig.Perturb
public import NLAlib.Ops.MonomialWork

/-!
# The Ginibre regularizer as a pipeline stage

The Gaussian perturbation of [BanksGarzaVargasSrivastava2025, Theorem 1.1]
(`NLAlib.SmallEig.ginibrePerturb`) already has the interface of the regularizer stage,
`[N, np] (A, P) → (A)`. At the words `NLAlib.SmallEig.smallEigParams` its probabilistic lemma
(`NLAlib.SmallEig.ginibrePerturb_pwrites`) is the regularizer contract into the class
$(2/t_2, t_1/2)$, $t_1, t_2$ the gap and condition thresholds.

## Main results

* `NLAlib.Schur.ginibrePerturb_randomRegularizerContract`.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory ProbabilityTheory SmallEig

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O]

/-- **The Ginibre perturbation meets the regularizer contract**: with the error $\delta/2$, the
failure probability $3\varphi/4$ and the class `NLAlib.IsConditionedDiagonalizable` at
$(2/t_2, t_1/2)$, $t_1$ = `NLAlib.SmallEig.smallEigGap`, $t_2$ = `NLAlib.SmallEig.smallEigCond`.
The hypotheses are those of `NLAlib.SmallEig.ginibrePerturb_pwrites`, fixed outside the
contract's quantifiers. -/
theorem ginibrePerturb_randomRegularizerContract {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hSmp : IsSample I)
    {law : ℕ → Measure ℝ} {sG : ℕ} (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition) (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax : ℕ} {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigReduce nmax S δ φ c₁ c₂) :
    RandomRegularizerContract law (δ / 2) (3 * φ / 4)
      (fun A => IsConditionedDiagonalizable (2 / smallEigCond nmax S δ φ c₂)
        (smallEigGap nmax S δ φ c₁ / 2) A) nmax S (smallEigParams nmax S δ φ c₁ c₂)
      (ginibrePerturb (O := O) (Q := Q) sG) I := fun A hn hAS =>
  (ginibrePerturb_pwrites hS hM hL hSmp hG hA hB hb₁ hb₂ hδ hδS hφ hφ1 hu hn hAS).mono
    (fun _ h => h) le_rfl
    (fun _ ⟨E, V, d, hE, hEn, hV, hAV, hc, hg⟩ => ⟨E, hE, hEn, V, d, hV, hAV, hc, hg⟩) le_rfl


/-- The instructions of the Ginibre regularizer: its instrumented static count at the order
$n + 1$, $p$ words and zero offsets is at most $201(n + 1)^2$ (the monomial bound, by
`kernel_rfl`). -/
theorem size_stmtCost_ginibrePerturb_le (sG n p : ℕ) :
    Count.size (stmtCost (ginibrePerturb (O := O) (Q := Q) sG).body.instrument
        [n + 1, p, 0, 0, 0]) ≤ 201 * (n + 1) ^ 2 := by
  have hw : stmtWorkMono (ginibrePerturb (O := O) (Q := Q) sG).body.instrument
      (⟨1, [1]⟩ :: ⟨1, [0, 1]⟩ :: List.replicate 3 (WorkMono.const 0)) = ⟨201, [2]⟩ := by
    kernel_rfl
  have hσ : SlotsLe [n + 1, p + 1] [n + 1, p, 0, 0, 0]
      (⟨1, [1]⟩ :: ⟨1, [0, 1]⟩ :: List.replicate 3 (WorkMono.const 0)) := by
    simp [SlotsLe, WorkMono.eval, WorkMono.const]
  have h := size_stmtCost_le_stmtWorkMono (by simp)
    (ginibrePerturb (O := O) (Q := Q) sG).body.instrument hσ
  rw [hw] at h
  simpa [WorkMono.eval, mul_assoc] using h

end NLAlib.Schur
