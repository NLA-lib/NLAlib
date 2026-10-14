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
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  have hm : Measurable fun Q : Matrix n k ℝ => Q * B * Qᴴ :=
    (measurable_id.matrix_mul measurable_const).matrix_mul
      (Measurable.matrix_conjTranspose continuous_star.measurable measurable_id)
  refine Integrable.of_bound (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    (specNorm B) ?_
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hX] with ω hω
  rw [← specNorm_eq_norm]
  calc specNorm (X ω * B * (X ω)ᴴ) ≤ specNorm (X ω) * specNorm B * specNorm (X ω)ᴴ :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ 1 * specNorm B * 1 := by
        rw [specNorm_conjTranspose]
        gcongr
    _ = specNorm B := by ring

/-- **The second moment of a Haar frame**: `E [Q B Qᴴ] = (tr B / n) • 1` for an `n × k` Haar
frame `Q`, `card k ≤ card n`. [Meckes2019, Ch. 2], there entrywise for the orthogonal group; here
for frames, in matrix form.
Result: haar-frame-second-moment -/
theorem integral_mul_mul_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (B : Matrix k k ℝ) :
    ∫ ω, X ω * B * (X ω)ᴴ ∂μ = (B.trace / Fintype.card n) • (1 : Matrix n n ℝ) := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  rw [integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant hX B
    (integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame hX B)]
  have htr : (fun ω => (X ω * B * (X ω)ᴴ).trace) =ᵐ[μ] fun _ => B.trace := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hX hk] with ω hω
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hasOrthonormalCols_iff.1 hω, Matrix.one_mul]
  rw [integral_congr_ae htr, integral_const, probReal_univ, one_smul]

/-- **`E [Q Qᴴ] = (k / n) • 1`**: the range projector of an `n × k` Haar frame is `k / n` times the
identity in mean (the case `B = 1` of `integral_mul_mul_conjTranspose_of_hasLaw_haarFrame`, stated
because consumers rewrite with it). -/
theorem integral_mul_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    ∫ ω, X ω * (X ω)ᴴ ∂μ = ((Fintype.card k : ℝ) / Fintype.card n) • (1 : Matrix n n ℝ) := by
  simpa only [Matrix.mul_one, Matrix.trace_one] using
    integral_mul_mul_conjTranspose_of_hasLaw_haarFrame hX hk 1

/-! ### `E [Qᴴ A Q]` -/

/-- `Qᴴ A Q` is integrable for a Haar frame `Q`, in every shape. -/
theorem integrable_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (A : Matrix n n ℝ) :
    Integrable (fun ω => (X ω)ᴴ * A * X ω) μ := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  have hm : Measurable fun Q : Matrix n k ℝ => Qᴴ * A * Q :=
    ((Measurable.matrix_conjTranspose continuous_star.measurable measurable_id).matrix_mul
      measurable_const).matrix_mul measurable_id
  refine Integrable.of_bound (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    (specNorm A) ?_
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hX] with ω hω
  rw [← specNorm_eq_norm]
  calc specNorm ((X ω)ᴴ * A * X ω) ≤ specNorm (X ω)ᴴ * specNorm A * specNorm (X ω) :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ 1 * specNorm A * 1 := by
        rw [specNorm_conjTranspose]
        gcongr
    _ = specNorm A := by ring

/-- **The compression of a fixed matrix by a Haar frame**: `E [Qᴴ A Q] = (tr A / n) • 1` for an
`n × k` Haar frame `Q`, `card k ≤ card n`. [Meckes2019, Ch. 2], there entrywise; here in matrix
form.
Result: haar-frame-second-moment -/
theorem integral_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (A : Matrix n n ℝ) :
    ∫ ω, (X ω)ᴴ * A * X ω ∂μ = (A.trace / Fintype.card n) • (1 : Matrix k k ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card k) with h0 | hpos
  · have := Fintype.card_eq_zero_iff.1 h0
    ext i
    exact isEmptyElim i
  have hY := hasLaw_conjTranspose_of_hasLaw_haarFrame hX
  have hint := integrable_conjTranspose_mul_mul_of_hasLaw_haarFrame hX A
  have hint' : Integrable (fun ω => A * (X ω * (X ω)ᴴ)) μ :=
    (integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame hX 1).const_mul A |>.congr
      (ae_of_all _ fun ω => by simp only [Matrix.mul_one])
  have h := integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant hY A
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hint)
  simp only [Matrix.conjTranspose_conjTranspose] at h
  have htr : ∫ ω, ((X ω)ᴴ * A * X ω).trace ∂μ =
      (Fintype.card k : ℝ) / Fintype.card n * A.trace := by
    have h1 : ∀ ω, ((X ω)ᴴ * A * X ω).trace = (A * (X ω * (X ω)ᴴ)).trace := fun ω => by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [h1]
    rw [Matrix.integral_trace hint', Matrix.integral_const_mul A
      (integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame hX 1 |>.congr
        (ae_of_all _ fun ω => by simp only [Matrix.mul_one])),
      integral_mul_conjTranspose_of_hasLaw_haarFrame hX hk, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, smul_eq_mul]
  rw [h, htr]
  congr 1
  have hk0 : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  field_simp

/-! ### Entries and columns -/

omit [Fintype n] in
/-- The entries of `Q (single j j 1) Qᴴ` are products of entries of the `j`-th column. -/
private theorem mul_single_mul_conjTranspose_apply (Q : Matrix n k ℝ) [DecidableEq k] (i i' : n)
    (j : k) : (Q * Matrix.single j j (1 : ℝ) * Qᴴ) i i' = Q i j * Q i' j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- The second moments of two entries of a column of a Haar frame. -/
private theorem integral_apply_mul_apply_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (i i' : n) (j : k) :
    ∫ ω, X ω i j * X ω i' j ∂μ = if i = i' then 1 / (Fintype.card n : ℝ) else 0 := by
  have h := congrFun₂ (integral_mul_mul_conjTranspose_of_hasLaw_haarFrame hX hk
    (Matrix.single j j (1 : ℝ))) i i'
  rw [Matrix.integral_apply (Matrix.integrable_iff.1
    (integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame hX _))] at h
  simp only [mul_single_mul_conjTranspose_apply] at h
  rw [h, Matrix.trace_single_eq_same, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **The entries of a Haar frame have second moment `1 / n`**: `E Qᵢⱼ² = 1 / n` for an `n × k`
Haar frame, `card k ≤ card n`. [Meckes2019, Ch. 2]. -/
theorem integral_apply_sq_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (i : n) (j : k) :
    ∫ ω, X ω i j ^ 2 ∂μ = 1 / Fintype.card n := by
  classical
  simpa only [sq, if_true] using integral_apply_mul_apply_of_hasLaw_haarFrame hX hk i i j

/-- **A rescaled column of a Haar frame is isotropic**: `√n · Q e_j` has second-moment matrix
the identity, for an `n × k` Haar frame `Q`, `card k ≤ card n`. It is what Hutchinson's estimator
with sphere probes takes (`IsIsotropic`). -/
theorem isIsotropic_sqrt_mul_col_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (j : k) :
    IsIsotropic (fun ω i => √(Fintype.card n : ℝ) * X ω i j) μ := by
  refine ⟨fun i => (memLp_apply_of_hasLaw_haarFrame hX i j 2).const_mul _, fun i i' => ?_⟩
  have : Nonempty n := ⟨i⟩
  have hn : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_ne_zero (α := n))
  have h (ω : Ω) : √(Fintype.card n : ℝ) * X ω i j * star (√(Fintype.card n : ℝ) * X ω i' j) =
      Fintype.card n * (X ω i j * X ω i' j) := by
    rw [star_trivial, mul_mul_mul_comm, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp only [h]
  rw [integral_const_mul, integral_apply_mul_apply_of_hasLaw_haarFrame hX hk i i' j]
  split_ifs
  · field_simp
  · rw [mul_zero]

end NLAlib
