/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyRangeState
public import NLAlib.Matrix.Computation.CholeskyRoundingOutput

/-!
# Outputs of finite-range rounded Cholesky

Completed factor columns determine the output packing and original-store frame independently
of how the residual's numerical error was propagated.

## Main results

* `NLAlib.Computation.CholeskyRange.State.writeBlock_pop`: the actual packed output words,
  complete original-store write, triangular shape, positive diagonal and forward error.
-/

@[expose] public section

namespace NLAlib.Computation.CholeskyRange

variable {P K : Type} [DecidableEq P] {N : ℕ}

/-- A completed finite-range Cholesky state gives the full original factor-block write and
its decoded guarantees after releasing scratch. Packing and frames use the same generic
completed-column extraction as the relative-error driver. The original input and factor may
overlap, and an empty output needs no valid handles. -/
theorem State.writeBlock_pop {dec : P → K → ℝ} {u τ μ B e : ℝ}
    {initial final : Store P K} {p : P} {L lo N : ℕ} {scratch : Array (Option K)}
    {A : Matrix (Fin N) (Fin N) ℝ}
    (hs : State dec u τ μ B e (initial.push (p, scratch)) p initial.size L lo A N final)
    (hcap : Writable initial p L lo (N * N)) :
    ∃ W : Array K, W.size = N * N ∧
      initial.writeBlock p L lo W = some final.pop ∧
      (unflatten N N (W.map (dec p))).IsLowerTriangular ∧
      (∀ i, 0 < unflatten N N (W.map (dec p)) i i) ∧
      (∀ i j, |unflatten N N (W.map (dec p)) i j - choleskyLower A i j| ≤ e) ∧
      HoldsDecoded final.pop dec p L lo (unflatten N N (W.map (dec p))) := by
  have hs' : CholeskyRounding.State dec 0 μ B e (initial.push (p, scratch)) p
      initial.size L lo A N final := by
    obtain ⟨M, hM, _⟩ := hs.residual
    refine ⟨hs.frame, ⟨M, hM, ?_⟩, hs.factor⟩
    intro i j hi
    have hh := i.isLt
    omega
  exact hs'.writeBlock_pop hcap

end NLAlib.Computation.CholeskyRange
