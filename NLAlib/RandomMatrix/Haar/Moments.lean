/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Isotropic
public import NLAlib.RandomMatrix.Haar.Basic

/-!
# Second moments of Haar frames

Exact second moments of an `n × k` Haar frame `Q` (`card k ≤ card n`), from orthogonal invariance
alone: `E [Q B Qᴴ] = (tr B / n) • 1`, in particular `E [Q Qᴴ] = (k / n) • 1`;
`E [Qᴴ A Q] = (tr A / n) • 1`; `E Qᵢⱼ² = 1 / n`; and `√n` times a column is isotropic. The
integrands are bounded (`ae_specNorm_le_one_of_hasLaw_haarFrame`), so the integrability
companions hold in every shape.

These are what a Haar sketch `S = √(n / k) Qᴴ` needs for `E [Sᴴ S] = 1`, and what trace estimation
with sphere probes or an orthonormal test matrix consumes. Fourth moments are not here: they need
the independence of `g / ‖g‖` and `‖g‖`.

## Main results

* `NLAlib.integral_mul_mul_conjTranspose_of_hasLaw_haarFrame`,
  `NLAlib.integral_mul_conjTranspose_of_hasLaw_haarFrame`.
* `NLAlib.integral_conjTranspose_mul_mul_of_hasLaw_haarFrame`.
* `NLAlib.integral_apply_sq_of_hasLaw_haarFrame`.
* `NLAlib.isIsotropic_sqrt_mul_col_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k] {X : Ω → Matrix n k ℝ}

/-! ### `E [Q B Qᴴ]` -/

/-- `Q B Qᴴ` is integrable for a Haar frame `Q`, in every shape. -/
theorem integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (B : Matrix k k ℝ) :
    Integrable (fun ω => X ω * B * (X ω)ᴴ) μ := by
  -- Proof: bounded by `specNorm B` (`ae_specNorm_le_one_of_hasLaw_haarFrame`) on a probability
  -- space (`hX.isProbabilityMeasure_iff`).
  sorry

/-- **The second moment of a Haar frame**: `E [Q B Qᴴ] = (tr B / n) • 1` for an `n × k` Haar
frame `Q`, `card k ≤ card n`. [Meckes2019, Ch. 2], there entrywise for the orthogonal group; here
for frames, in matrix form.
Result: haar-frame-second-moment -/
theorem integral_mul_mul_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (B : Matrix k k ℝ) :
    ∫ ω, X ω * B * (X ω)ᴴ ∂μ = (B.trace / Fintype.card n) • (1 : Matrix n n ℝ) := by
  -- Proof: `integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`, with
  -- `tr (Q B Qᴴ) = tr (B Qᴴ Q) = tr B` a.s. (`ae_hasOrthonormalCols_of_hasLaw_haarFrame`).
  sorry

/-- **`E [Q Qᴴ] = (k / n) • 1`**: the range projector of an `n × k` Haar frame is `k / n` times the
identity in mean (the case `B = 1` of `integral_mul_mul_conjTranspose_of_hasLaw_haarFrame`, stated
because consumers rewrite with it). -/
theorem integral_mul_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    ∫ ω, X ω * (X ω)ᴴ ∂μ = ((Fintype.card k : ℝ) / Fintype.card n) • (1 : Matrix n n ℝ) := by
  sorry

/-! ### `E [Qᴴ A Q]` -/

/-- `Qᴴ A Q` is integrable for a Haar frame `Q`, in every shape. -/
theorem integrable_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (A : Matrix n n ℝ) :
    Integrable (fun ω => (X ω)ᴴ * A * X ω) μ := by
  sorry

/-- **The compression of a fixed matrix by a Haar frame**: `E [Qᴴ A Q] = (tr A / n) • 1` for an
`n × k` Haar frame `Q`, `card k ≤ card n`. [Meckes2019, Ch. 2], there entrywise; here in matrix
form.
Result: haar-frame-second-moment -/
theorem integral_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (A : Matrix n n ℝ) :
    ∫ ω, (X ω)ᴴ * A * X ω ∂μ = (A.trace / Fintype.card n) • (1 : Matrix k k ℝ) := by
  -- Proof: split on `card k = 0` (both sides are the empty matrix). Otherwise
  -- `integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant` for `Qᴴ`, of law
  -- `haarFrame k n` (`hasLaw_conjTranspose_of_hasLaw_haarFrame`), with trace
  -- `tr (A E [Q Qᴴ]) = k tr A / n` (`integral_mul_conjTranspose_of_hasLaw_haarFrame`).
  sorry

/-! ### Entries and columns -/

/-- **The entries of a Haar frame have second moment `1 / n`**: `E Qᵢⱼ² = 1 / n` for an `n × k`
Haar frame, `card k ≤ card n`. [Meckes2019, Ch. 2]. -/
theorem integral_apply_sq_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (i : n) (j : k) :
    ∫ ω, X ω i j ^ 2 ∂μ = 1 / Fintype.card n := by
  -- Proof: the `(i, i)` entry of `integral_mul_mul_conjTranspose_of_hasLaw_haarFrame` at
  -- `B = Matrix.single j j 1`, with `Matrix.integral_apply`.
  sorry

/-- **A rescaled column of a Haar frame is isotropic**: `√n · Q e_j` has second-moment matrix
the identity, for an `n × k` Haar frame `Q`, `card k ≤ card n`. It is what Hutchinson's estimator
with sphere probes takes (`IsIsotropic`). -/
theorem isIsotropic_sqrt_mul_col_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (j : k) :
    IsIsotropic (fun ω i => √(Fintype.card n : ℝ) * X ω i j) μ := by
  -- Proof: `memLp_apply_of_hasLaw_haarFrame` and the entries of
  -- `integral_mul_mul_conjTranspose_of_hasLaw_haarFrame` at `B = Matrix.single j j 1`.
  sorry

end NLAlib
