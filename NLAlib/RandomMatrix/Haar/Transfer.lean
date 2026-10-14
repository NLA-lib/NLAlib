/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Basic

/-!
# Transfer between Gaussian and Haar test matrices

For a fixed `A` and a Haar frame `Q`, the range projector of `A Q` has the law of the range
projector of `A G` for a standard Gaussian `G` of the same shape: `polarFactor G = G T` with `T`
invertible on the range, so `A G` and `A (polarFactor G)` have the same column space. Every
statistic of the column space of a sketch is a function of its range projector, so every
range-finder statement proved for a Gaussian test matrix (expectations, tails, ranks) holds
verbatim for a Haar test matrix, in every shape and rank.

## Main results

* `NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`: the law of `rangeProjector (A Q)`.
* `NLAlib.integral_comp_rangeProjector_mul_of_hasLaw_haarFrame`: the expectation form, with values
  in any real Banach space.
* `NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame`: `rank (A Q) = min (rank A) k` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k] {X : Ω → Matrix n k ℝ}

/-- **Transfer between Gaussian and Haar test matrices**: the range projector of `A Q` for a Haar
frame `Q` has the law of that of `A G` for a standard Gaussian `G`. Every shape and rank; no
`card k ≤ card n` is needed. A statistic of `range (A Q)` is a measurable function of the
projector, so it transfers by `HasLaw.comp`; this covers the residual `(1 - P) A` of the range
finder, the power-iteration range finder (take `(A * Aᴴ) ^ q * A` for `A`) and the Nyström
approximation of a positive semidefinite `A` (take `CFC.sqrt A` for `A`).
[HalkoMartinssonTropp2011, §4, §10], where the range finder is analysed for Gaussian test
matrices.
Result: gaussian-haar-range-transfer -/
theorem hasLaw_rangeProjector_mul_of_hasLaw_haarFrame [DecidableEq k] {m : Type*} [Fintype m]
    (A : Matrix m n ℝ) (hX : HasLaw X (haarFrame n k) μ) :
    HasLaw (fun ω => rangeProjector (A * X ω))
      ((gaussianMatrix n k).map fun G => rangeProjector (A * G)) μ := by
  -- Proof: `rangeProjector_mul_polarFactor`, `measurable_rangeProjector`, `HasLaw.comp`.
  sorry

/-- **Expectations transfer between Gaussian and Haar test matrices**: for any statistic `f` of
the range projector, with values in any real Banach space, `E f (P_{A Q}) = E f (P_{A G})` for a
Haar frame `Q` and a standard Gaussian `G` on any two probability spaces. No integrability
hypothesis: both sides integrate `f` against one law. This is the form a range-finder consumer
applies, including to the power-iteration and Nyström sketches
(`hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`). -/
theorem integral_comp_rangeProjector_mul_of_hasLaw_haarFrame [DecidableEq k] {m : Type*}
    [Fintype m] (A : Matrix m n ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Matrix m m ℝ → E} (hf : StronglyMeasurable f) (hX : HasLaw X (haarFrame n k) μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} {G : Ω' → Matrix n k ℝ}
    (hG : HasLaw G (gaussianMatrix n k) μ') :
    ∫ ω, f (rangeProjector (A * X ω)) ∂μ = ∫ ω', f (rangeProjector (A * G ω')) ∂μ' := by
  -- Proof: `HasLaw.integral_comp` on both sides of
  -- `hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`, and `integral_map`.
  sorry

/-- **The rank of a Haar sketch**: `rank (A Q) = min (rank A) (card k)` almost surely, for a Haar
frame `Q`, in every shape. The Haar twin of `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`. -/
theorem ae_rank_mul_eq_min_of_hasLaw_haarFrame [DecidableEq k] {m : Type*} [Finite m]
    (A : Matrix m n ℝ) (hX : HasLaw X (haarFrame n k) μ) :
    ∀ᵐ ω ∂μ, (A * X ω).rank = min A.rank (Fintype.card k) := by
  -- Proof: `rank_rangeProjector`, `hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`,
  -- `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix` and `measurable_rank`.
  sorry

end NLAlib
