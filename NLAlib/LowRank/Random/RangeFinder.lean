/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import NLAlib.LowRank.Structural.BlockKrylov
public import NLAlib.LowRank.Structural.Truncation
public import NLAlib.Probability.Measurability.Krylov
public import NLAlib.Probability.Measurability.Matrix

/-!
# The randomized SVD with any random test matrix

Facts about the randomized SVD $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$ (`NLAlib.rsvd`) that
hold for every random test matrix $\mathbf{X}$, whatever its law, over any `RCLike` field. They are
the integrability companions of the expectation bounds of the Gaussian, rotation-invariant and
oblivious range finders, and the reduction of a spectral bound for the truncated output to a
Frobenius one.

**Integrability.** Every error of the randomized SVD is a measurable function of the test matrix
and is bounded by the same quantity for $\mathbf{A}$, so it is integrable for every measurable
test matrix and every finite measure. The squared Frobenius error of the late-truncated output
`truncatedSVD (rsvd A (X ω)) k` is integrable too: it does not depend on the choice the truncation
makes (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`), which is what makes it measurable.

**Measurability of the truncated output.** The spectral error of
`truncatedSVD (rsvd A (X ω)) k` depends on the choice the truncation makes. Statements about it
are stated for any measurable choice $\mathbf{Y}$ of best approximations,
`hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)` with `hYm : AEStronglyMeasurable Y μ`, which
covers an algorithm's own tie-break, and each has its direct form at `truncatedSVD`, which is
Borel measurable (`NLAlib.measurable_truncatedSVD`), with
`hY := fun _ => isBestRankApprox_truncatedSVD _ k` and
`hYm := ((measurable_truncatedSVD k).comp_aemeasurable
((measurable_rsvd A).comp_aemeasurable hX)).aestronglyMeasurable`.


## Main results

* `NLAlib.SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd`,
  `NLAlib.SymmetricGauge.integrable_matrixNorm_sub_rsvd`,
  `NLAlib.integrable_schattenNorm_sub_rsvd_sq`,
  `NLAlib.integrable_frobNorm_sub_rsvd_sq`, `NLAlib.integrable_frobNorm_sub_rsvd`,
  `NLAlib.integrable_specNorm_sub_rsvd_sq`, `NLAlib.integrable_specNorm_sub_rsvd`: integrability of
  the error for any measurable test matrix.
* `NLAlib.integrable_frobNorm_sub_truncatedSVD_rsvd_sq`: the late-truncated output, Frobenius.
* `NLAlib.integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow`: the two-sided output of the
  late-truncated randomized SVD, $p$-th power of the Schatten $p$-norm.
* `NLAlib.integrable_frobNorm_sub_earlyTruncatedRSVD_sq`: the early-truncated output;
  `NLAlib.aestronglyMeasurable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq`, the
  measurability of its generalized Nyström completion for any pair of test matrices.
* `NLAlib.integrable_specNorm_sub_sq_of_isBestRankApprox`: the truncated output, spectral, for a
  measurable selector; `NLAlib.integrable_specNorm_sub_truncatedSVD_rsvd_sq`, its direct form.
* `NLAlib.integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox`:
  reverse Eckart–Young in expectation, for a measurable selector;
  `NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_sq_add_frobNorm_sub_truncatedSVD_sq_le`, its
  direct form.
* `NLAlib.integrable_specNorm_sub_rbki_sq`, `NLAlib.integrable_frobNorm_sub_rbki_sq`,
  `NLAlib.SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rbki`,
  `NLAlib.integrable_specNorm_sub_truncatedSVD_rbki_sq`,
  `NLAlib.integrable_frobNorm_sub_truncatedSVD_rbki_sq`: the same for randomized block Krylov
  iteration, whose test matrix $\mathbf{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{X})$ is
  measurable in $\mathbf{X}$ (`NLAlib.measurable_blockKrylovMatrix`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] {X : Ω → Matrix n l 𝕜}

/-! ### Measurability and boundedness -/

/-- The error of the randomized SVD is a measurable function of the test matrix. -/
private theorem measurable_sub_rsvd (A : Matrix m n 𝕜) :
    Measurable fun Ω : Matrix n l 𝕜 => A - rsvd A Ω :=
  measurable_const.matrix_sub (measurable_rsvd A)

/-- Every unitarily invariant norm of the error of the randomized SVD is at most that of
$\mathbf{A}$. -/
private theorem matrixNorm_sub_rsvd_le (Φ : SymmetricGauge) (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) : Φ.matrixNorm (A - rsvd A Ω) ≤ Φ.matrixNorm A :=
  Φ.matrixNorm_le_of_singularValues_le (singularValues_sub_rsvd_le A Ω)

/-! ### Integrability of the error -/

/-- The Gram matrix of the error of the randomized SVD is integrable in every unitarily invariant
norm, for every measurable test matrix $\mathbf{X}$ and finite measure: $\omega \mapsto
\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))^{\mathsf{H}}(\mathbf{A} -
\mathsf{rsvd}(\mathbf{A}, \mathbf{X}))\|_{\Phi}$ is measurable and bounded by
$\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\Phi}$. The companion of the Gram-form expectations. -/
theorem SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd (Φ : SymmetricGauge)
    [IsFiniteMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))) μ := by
  refine Integrable.of_bound ((Φ.measurable_matrixNorm.comp
    ((Measurable.matrix_conjTranspose continuous_star.measurable
      (measurable_sub_rsvd A)).matrix_mul (measurable_sub_rsvd A))).comp_aemeasurable
        hX).aestronglyMeasurable (Φ.matrixNorm (Aᴴ * A)) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (Φ.matrixNorm_nonneg _)]
  refine Φ.matrixNorm_le_of_singularValues_le fun i => ?_
  rw [singularValues_conjTranspose_mul_self, singularValues_conjTranspose_mul_self]
  exact pow_le_pow_left₀ (singularValues_nonneg _ _) (singularValues_sub_rsvd_le A (X ω) i) 2

/-- The error of the randomized SVD is integrable in every unitarily invariant norm, for every
measurable test matrix $\mathbf{X}$ and finite measure: $\omega \mapsto \|\mathbf{A} -
\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\Phi}$ is measurable and bounded by
$\|\mathbf{A}\|_{\Phi}$. -/
theorem SymmetricGauge.integrable_matrixNorm_sub_rsvd (Φ : SymmetricGauge) [IsFiniteMeasure μ]
    (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => Φ.matrixNorm (A - rsvd A (X ω))) μ :=
  Integrable.of_bound ((Φ.measurable_matrixNorm.comp (measurable_sub_rsvd A)).comp_aemeasurable
    hX).aestronglyMeasurable (Φ.matrixNorm A) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (Φ.matrixNorm_nonneg _)]
      exact matrixNorm_sub_rsvd_le Φ A (X ω))

/-- The squared Schatten $q$-norm of the error of the randomized SVD, $q \ge 1$, is integrable for
every measurable test matrix $\mathbf{X}$ and finite measure: $\omega \mapsto \|\mathbf{A} -
\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{S_q}^2$ is bounded by
$\|\mathbf{A}\|_{S_q}^2$. -/
theorem integrable_schattenNorm_sub_rsvd_sq [IsFiniteMeasure μ] {q : ℝ≥0∞} (hq : 1 ≤ q)
    (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => schattenNorm q (A - rsvd A (X ω)) ^ 2) μ := by
  have := Fact.mk hq
  have hg : Measurable fun M : Matrix m n 𝕜 => schattenNorm q M := by
    rw [show (fun M : Matrix m n 𝕜 => schattenNorm q M) = (lpGauge q).matrixNorm from
      funext fun M => (lpGauge_matrixNorm M).symm]
    exact (lpGauge q).measurable_matrixNorm
  refine Integrable.of_bound (((hg.comp (measurable_sub_rsvd A)).pow_const 2).comp_aemeasurable
    hX).aestronglyMeasurable (schattenNorm q A ^ 2) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := matrixNorm_sub_rsvd_le (lpGauge q) A (X ω)
  rw [lpGauge_matrixNorm, lpGauge_matrixNorm] at h
  exact pow_le_pow_left₀ (schattenNorm_nonneg _ _) h 2

/-- The squared Frobenius error of the randomized SVD,
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2$, is integrable for
every measurable test matrix $\mathbf{X}$ and finite measure. -/
theorem integrable_frobNorm_sub_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => frobNorm (A - rsvd A (X ω)) ^ 2) μ := by
  simpa only [schattenNorm_two] using integrable_schattenNorm_sub_rsvd_sq one_le_two A hX

/-- The Frobenius error of the randomized SVD,
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}$, is integrable for every
measurable test matrix $\mathbf{X}$ and finite measure. The companion of the expected Frobenius
error in its printed, unsquared form. -/
theorem integrable_frobNorm_sub_rsvd [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => frobNorm (A - rsvd A (X ω))) μ := by
  simpa only [lpGauge_two_matrixNorm] using
    (lpGauge 2).integrable_matrixNorm_sub_rsvd A hX

/-- The squared spectral error of the randomized SVD,
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2^2$, is integrable for every
measurable test matrix $\mathbf{X}$ and finite measure. -/
theorem integrable_specNorm_sub_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => specNorm (A - rsvd A (X ω)) ^ 2) μ := by
  simpa only [schattenNorm_top] using integrable_schattenNorm_sub_rsvd_sq le_top A hX

/-- The spectral error of the randomized SVD,
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2$, is integrable for every measurable
test matrix $\mathbf{X}$ and finite measure. -/
theorem integrable_specNorm_sub_rsvd [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => specNorm (A - rsvd A (X ω))) μ := by
  simpa only [lpGauge_top_matrixNorm] using (lpGauge ⊤).integrable_matrixNorm_sub_rsvd A hX

/-! ### The truncated output -/

/-- The squared Frobenius error of the early-truncated randomized SVD,
$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{X}, k)\|_{\mathsf{F}}^2$, is
integrable for every measurable test matrix $\mathbf{X}$ and finite measure: it is a measurable
function of the test matrix (`NLAlib.measurable_earlyTruncatedRSVD`) bounded by
$\|\mathbf{A}\|_{\mathsf{F}}^2$, for every choice of the truncation. -/
theorem integrable_frobNorm_sub_earlyTruncatedRSVD_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2) μ := by
  classical
  refine Integrable.of_bound (((measurable_frobNorm.comp (measurable_const.matrix_sub
    (measurable_earlyTruncatedRSVD A k))).pow_const 2).comp_aemeasurable hX).aestronglyMeasurable
    (frobNorm A ^ 2) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sub_earlyTruncatedRSVD]
  exact pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_one_sub_rangeProjector_mul_le _ A) 2

/-- The squared Frobenius error of early-truncated generalized Nyström,
$\|\mathbf{A} - \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{X}, \mathbf{\Psi},
k)\|_{\mathsf{F}}^2$, is almost everywhere strongly measurable for every pair of almost everywhere
measurable test matrices $\mathbf{X}$ and $\mathbf{\Psi}$, whatever their joint law: it is a
measurable function of the pair (`NLAlib.measurable_earlyTruncatedGeneralizedNystrom`). -/
theorem aestronglyMeasurable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq {p : Type*}
    [Fintype p] {Ψ : Ω → Matrix m p 𝕜} (A : Matrix m n 𝕜) (hX : AEMeasurable X μ)
    (hΨ : AEMeasurable Ψ μ) (k : ℕ) :
    AEStronglyMeasurable
      (fun ω => frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2) μ :=
  (((measurable_frobNorm.comp (measurable_const.matrix_sub
    (measurable_earlyTruncatedGeneralizedNystrom A k))).pow_const 2).comp_aemeasurable
      (hX.prodMk hΨ)).aestronglyMeasurable

/-- The squared Frobenius error of the late-truncated randomized SVD,
$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_{\mathsf{F}}^2$,
is integrable for every measurable test matrix $\mathbf{X}$ and finite measure. It does not depend
on the choice made by `truncatedSVD` (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`): it is
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2$ plus the tail sum of
squared singular values of $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$, which is what makes it
measurable; it is bounded by
$\|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$.
-/
theorem integrable_frobNorm_sub_truncatedSVD_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2) μ := by
  have he : (fun Ω : Matrix n l 𝕜 => frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2) =
      fun Ω => frobNorm (A - rsvd A Ω) ^ 2 + ∑ i ∈ Finset.Ico k (min (Fintype.card m)
        (Fintype.card n)), singularValues (rsvd A Ω) i ^ 2 := by
    funext Ω
    rw [frobNorm_sub_truncatedSVD_rsvd_sq, frobNorm_sub_truncatedSVD_sq]
  have hr : Measurable fun Ω : Matrix n l 𝕜 => rsvd A Ω := measurable_rsvd A
  have hg : Measurable fun Ω : Matrix n l 𝕜 => frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 := by
    rw [he]
    exact ((measurable_frobNorm.comp (measurable_sub_rsvd A)).pow_const 2).add
      (Finset.measurable_sum _ fun i _ => ((measurable_singularValues i).comp hr).pow_const 2)
  refine Integrable.of_bound (hg.comp_aemeasurable hX).aestronglyMeasurable
    (frobNorm A ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), frobNorm_sub_truncatedSVD_rsvd_sq]
  have h1 := matrixNorm_sub_rsvd_le (lpGauge 2) A (X ω)
  rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h1
  have h2 := frobNorm_rsvd_sub_truncatedSVD_le A (X ω) k
  have h3 := pow_le_pow_left₀ (frobNorm_nonneg _) h1 2
  have h4 := pow_le_pow_left₀ (frobNorm_nonneg _) h2 2
  linarith

/-- The $p$-th power of the Schatten error of the two-sided output of the late-truncated
randomized SVD is integrable: for a real matrix $\mathbf{A}$, every almost everywhere measurable
random test matrix $\mathbf{Y}$, every finite measure, every $p$ and $k$, with
$\mathbf{B} = \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{Y})\rrbracket_k$ and
$\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ the projector onto its row space,
$\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p}^p$ is integrable. It is
a measurable function of the test matrix (`NLAlib.measurable_truncatedSVD`,
`NLAlib.measurable_rangeProjector`) and is bounded by $\|\mathbf{A}\|_{S_p}^p$. The
integrability companion of the expectation bounds for this output. -/
theorem integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (A : Matrix m n ℝ) {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ) (k : ℕ) :
    Integrable (fun ω => schattenNorm p (A - A * rangeProjector
      (truncatedSVD (rsvd A (Y ω)) k)ᴴ) ^ p.toReal) μ := by
  classical
  rcases eq_or_ne p.toReal 0 with h0 | h0
  · simp only [h0, Real.rpow_zero]
    exact integrable_const 1
  have hpt : p ≠ ⊤ := fun h => h0 (by simp [h])
  have hp0 : p ≠ 0 := fun h => h0 (by simp [h])
  have hc : Continuous fun M : Matrix m n ℝ => schattenNorm p M := by
    have h := continuous_schattenNorm_ofReal (𝕜 := ℝ) (m := m) (n := n)
      (ENNReal.toReal_pos hp0 hpt)
    rwa [ENNReal.ofReal_toReal hpt] at h
  have hg : Measurable fun Ω : Matrix n l ℝ => schattenNorm p (A - A * rangeProjector
      (truncatedSVD (rsvd A Ω) k)ᴴ) ^ p.toReal :=
    (hc.measurable.comp (measurable_const.matrix_sub (measurable_const.matrix_mul
      (measurable_rangeProjector.comp (Measurable.matrix_conjTranspose
        continuous_star.measurable ((measurable_truncatedSVD k).comp
          (measurable_rsvd A))))))).pow_const _
  refine Integrable.of_bound (hg.comp_aemeasurable hY).aestronglyMeasurable
    (schattenNorm p A ^ p.toReal) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  refine Real.rpow_le_rpow (schattenNorm_nonneg _ _) ?_ ENNReal.toReal_nonneg
  set P := rangeProjector (truncatedSVD (rsvd A (Y ω)) k)ᴴ
  have hS : specNorm (1 - P) ≤ 1 := by
    have h := specNorm_one_sub_rangeProjector_mul_le (truncatedSVD (rsvd A (Y ω)) k)ᴴ
      (1 : Matrix n n ℝ)
    rw [Matrix.mul_one] at h
    exact h.trans specNorm_one_le
  calc schattenNorm p (A - A * P) = schattenNorm p (A * (1 - P)) := by
        rw [Matrix.mul_sub, Matrix.mul_one]
    _ ≤ schattenNorm p A * specNorm (1 - P) := schattenNorm_mul_le_mul_specNorm hp0 A _
    _ ≤ schattenNorm p A := mul_le_of_le_one_right (schattenNorm_nonneg _ _) hS

/-- For a measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of the randomized SVD,
$\mathbf{Y}(\omega)$ a best approximation of $\mathbf{P}_{\mathbf{A}\mathbf{X}(\omega)}\mathbf{A}$
of rank at most $k$, the squared spectral error $\|\mathbf{A} - \mathbf{Y}\|_2^2$ is integrable for
every finite measure; it is bounded by
$\|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$.
No measurability of $\mathbf{X}$ is needed. Direct form at `truncatedSVD`:
`NLAlib.integrable_specNorm_sub_truncatedSVD_rsvd_sq`. -/
theorem integrable_specNorm_sub_sq_of_isBestRankApprox [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    {k : ℕ} {Y : Ω → Matrix m n 𝕜} (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) : Integrable (fun ω => specNorm (A - Y ω) ^ 2) μ := by
  have hm : AEStronglyMeasurable (fun ω => specNorm (A - Y ω) ^ 2) μ :=
    ((continuous_specNorm.comp (continuous_const.sub continuous_id)).pow
      2).comp_aestronglyMeasurable hYm
  refine Integrable.of_bound hm (frobNorm A ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := matrixNorm_sub_rsvd_le (lpGauge 2) A (X ω)
  rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h1
  have h2 : frobNorm (rsvd A (X ω) - Y ω) ≤ frobNorm (A - truncatedSVD A k) :=
    (hY ω).frobNorm_sub.trans_le (frobNorm_rsvd_sub_truncatedSVD_le A (X ω) k)
  have h3 := pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm (A - Y ω)) 2
  rw [(hY ω).frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add] at h3
  have h4 := pow_le_pow_left₀ (frobNorm_nonneg _) h1 2
  have h5 := pow_le_pow_left₀ (frobNorm_nonneg _) h2 2
  linarith

/-- For a measurable test matrix and every finite measure, the squared spectral error of the
truncated randomized SVD,
$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_2^2$, is
integrable. The direct form of `NLAlib.integrable_specNorm_sub_sq_of_isBestRankApprox`. -/
theorem integrable_specNorm_sub_truncatedSVD_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => specNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2) μ :=
  integrable_specNorm_sub_sq_of_isBestRankApprox A (fun _ => isBestRankApprox_truncatedSVD _ k)
    ((measurable_truncatedSVD k).comp_aemeasurable
      ((measurable_rsvd A).comp_aemeasurable hX)).aestronglyMeasurable

/-- **Reverse Eckart–Young in expectation**: for a measurable test matrix $\mathbf{X}$ and a
measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of
$\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$,
$$\mathbb{E}\|\mathbf{A} - \mathbf{Y}\|_2^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2 \le \sigma_k(\mathbf{A})^2 + \mathbb{E}\|\mathbf{A} -
\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every law: a Frobenius bound for the truncated output becomes a spectral one at no cost.
Direct form at `truncatedSVD`:
`NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_sq_add_frobNorm_sub_truncatedSVD_sq_le`.
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a deterministic remark on truncated outputs, here in expectation
under a selector, subtraction-free, indices from $0$.
Result: reverse-eckart-young -/
theorem integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox
    [IsProbabilityMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) {k : ℕ}
    {Y : Ω → Matrix m n 𝕜} (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (A - Y ω) ^ 2 ∂μ + frobNorm (A - truncatedSVD A k) ^ 2 ≤
      singularValues A k ^ 2 + ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ := by
  have hpt : ∀ ω, specNorm (A - Y ω) ^ 2 ≤
      (singularValues A k ^ 2 - frobNorm (A - truncatedSVD A k) ^ 2) +
        frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 := by
    intro ω
    have h := (hY ω).specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le
    linarith
  have hF := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX k
  have hI : Integrable (fun ω => (singularValues A k ^ 2 - frobNorm (A - truncatedSVD A k) ^ 2) +
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2) μ := (integrable_const _).add hF
  have hle := integral_mono (integrable_specNorm_sub_sq_of_isBestRankApprox A hY hYm) hI hpt
  rw [integral_add (integrable_const _) hF, integral_const, probReal_univ, one_smul] at hle
  linarith

/-- **Reverse Eckart–Young in expectation, truncated randomized SVD**: for a measurable test
matrix $\mathbf{X}$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_2^2 +
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le \sigma_k(\mathbf{A})^2 +
\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
for every law. The direct form of
`NLAlib.integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox`.
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a deterministic remark on truncated outputs, here in expectation,
subtraction-free, indices from $0$.
Result: reverse-eckart-young -/
theorem integral_specNorm_sub_truncatedSVD_rsvd_sq_add_frobNorm_sub_truncatedSVD_sq_le
    [IsProbabilityMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) (k : ℕ) :
    ∫ ω, specNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ +
        frobNorm (A - truncatedSVD A k) ^ 2 ≤
      singularValues A k ^ 2 + ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ :=
  integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox A hX
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    ((measurable_truncatedSVD k).comp_aemeasurable
      ((measurable_rsvd A).comp_aemeasurable hX)).aestronglyMeasurable

/-! ### Randomized block Krylov iteration -/


section BlockKrylov

variable [DecidableEq n]

omit [Fintype l] in
/-- The block Krylov test matrix of a measurable test matrix is measurable. -/
private theorem aemeasurable_blockKrylovMatrix (A : Matrix m n 𝕜) (hX : AEMeasurable X μ)
    (q : ℕ) : AEMeasurable (fun ω => blockKrylovMatrix (Aᴴ * A) (X ω) q) μ :=
  (measurable_blockKrylovMatrix (Aᴴ * A) q).comp_aemeasurable hX

/-- The squared spectral error $\|\mathbf{A}-\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\|_2^2$ of
randomized block Krylov iteration is integrable, for any almost everywhere measurable test matrix
and finite measure. -/
theorem integrable_specNorm_sub_rbki_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (q : ℕ) :
    Integrable (fun ω => specNorm (A - rbki A (X ω) q) ^ 2) μ :=
  integrable_specNorm_sub_rsvd_sq A (aemeasurable_blockKrylovMatrix A hX q)

/-- The squared Frobenius error
$\|\mathbf{A}-\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\|_{\mathsf{F}}^2$ of randomized block
Krylov iteration is integrable, for any almost everywhere measurable test matrix and finite
measure. -/
theorem integrable_frobNorm_sub_rbki_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (q : ℕ) :
    Integrable (fun ω => frobNorm (A - rbki A (X ω) q) ^ 2) μ :=
  integrable_frobNorm_sub_rsvd_sq A (aemeasurable_blockKrylovMatrix A hX q)

/-- The Gram matrix of the error $\mathbf{A}-\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$ has an
integrable unitarily invariant norm, for any almost everywhere measurable test matrix and finite
measure. -/
theorem SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rbki (Φ : SymmetricGauge)
    [IsFiniteMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) (q : ℕ) :
    Integrable (fun ω => Φ.matrixNorm ((A - rbki A (X ω) q)ᴴ * (A - rbki A (X ω) q))) μ :=
  Φ.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd A
    (aemeasurable_blockKrylovMatrix A hX q)

/-- The squared spectral error
$\|\mathbf{A}-\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\rrbracket_k\|_2^2$ of
truncated randomized block Krylov iteration is integrable, for any almost everywhere measurable
test matrix and finite measure. -/
theorem integrable_specNorm_sub_truncatedSVD_rbki_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (q k : ℕ) :
    Integrable (fun ω => specNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2) μ :=
  integrable_specNorm_sub_truncatedSVD_rsvd_sq A (aemeasurable_blockKrylovMatrix A hX q) k

/-- The squared Frobenius error
$\|\mathbf{A}-\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\rrbracket_k\|_{\mathsf{F}}^2$
of truncated randomized block Krylov iteration is integrable, for any almost everywhere
measurable test matrix and finite measure. -/
theorem integrable_frobNorm_sub_truncatedSVD_rbki_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (q k : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2) μ :=
  integrable_frobNorm_sub_truncatedSVD_rsvd_sq A (aemeasurable_blockKrylovMatrix A hX q) k

end BlockKrylov

end NLAlib
