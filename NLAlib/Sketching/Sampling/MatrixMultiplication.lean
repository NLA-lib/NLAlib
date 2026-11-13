/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.BernsteinWithoutReplacement
public import NLAlib.Probability.MatrixConcentration.Variance
public import NLAlib.Probability.Tail
public import NLAlib.Sketching.Sampling.RowSampling
public import NLAlib.Sketching.Sampling.WithoutReplacement

/-!
# Approximate matrix multiplication by row sampling

For `A : Matrix n q 𝕜`, `B : Matrix n r 𝕜` (written $\mathbf{A}$, $\mathbf{B}$) and the
row-sampling sketch $\mathbf{S}$ with law `NLAlib.samplingSketch k p` (weights $p_i$), the sampled
product $\mathbf{A}^{\mathsf{H}} \mathbf{S}^{\mathsf{H}} \mathbf{S} \mathbf{B}$ is the sum of
$\lvert k \rvert$ i.i.d. rank-one atoms
$$\frac{1}{\lvert k \rvert \, p_{\iota}} (\mathbf{A}_{\iota})^{\mathsf{H}} \mathbf{B}_{\iota}$$
for i.i.d. sampled rows $\iota$ (`NLAlib.conjTranspose_samplingSketchMatrix_mul_mul`). It is
unbiased when every zero weight sits on a row where $\mathbf{A}$ or $\mathbf{B}$ vanishes, its
squared Frobenius error has the exact mean
$$\frac{1}{\lvert k \rvert} \Bigl( \sum_i \frac{\|\mathbf{A}_i\|^2 \|\mathbf{B}_i\|^2}{p_i} -
\|\mathbf{A}^{\mathsf{H}} \mathbf{B}\|_{\mathsf{F}}^2 \Bigr),$$
and under the domination $\|\mathbf{A}_i\| \, \|\mathbf{B}_i\| \le L p_i$ that mean is at most
$L \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}} / \lvert k \rvert$; Markov's
inequality gives the tail. The error and its event are those of the JL-moment form
(`NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le`), here over `𝕜`.

Degenerate cases: for empty `k`, $\mathbf{S} = \mathbf{0}$ and the sampled product is
$\mathbf{0}$, hence `[Nonempty k]` on every mean and tail; the integrability statements need
neither it nor $\sum_i p_i = 1$. A zero weight with $\mathbf{A}_i \ne \mathbf{0}$ and
$\mathbf{B}_i \ne \mathbf{0}$ biases the estimator, which the support hypothesis excludes and the
domination hypothesis implies.

In the spectral norm, matrix Bernstein for the rectangular atoms
(`NLAlib.Probability.MatrixConcentration.Bernstein`) needs a uniform atom bound and the two
one-sided variances, hence two separate dominations $\|\mathbf{A}_i\|^2 \le a\,p_i$ and
$\|\mathbf{B}_i\|^2 \le b\,p_i$: they bound the variances by
$b\|\mathbf{A}\|_2^2/\lvert k\rvert$ and $a\|\mathbf{B}\|_2^2/\lvert k\rvert$ and the atoms by
$2\sqrt{ab}/\lvert k\rvert$, and imply the product domination with $L = \sqrt{ab}$; the product
domination alone does not bound the variances (a row with $\|\mathbf{A}_i\|$ large and
$\|\mathbf{B}_i\|$ small). At $p_i \propto \|\mathbf{A}_i\|^2 + \|\mathbf{B}_i\|^2$ this is the
stable-rank form. Without replacement the weights are uniform and matrix Bernstein without
replacement (`NLAlib.Probability.MatrixConcentration.BernsteinWithoutReplacement`) gives the same
bound.

Proofs. Every expectation is transported to $\lvert k \rvert$ i.i.d. indices
(`NLAlib.samplingSketch_eq_map`), where the sampled product is a sum of i.i.d. atoms whose weighted
mean is $\mathbf{A}^{\mathsf{H}} \mathbf{B} / \lvert k \rvert$; unbiasedness is linearity, the
exact second moment is the additivity of the Frobenius variance over independent centred summands
(`NLAlib.integral_sum_mul_sum_of_iIndepFun` under the trace), the domination bound is the identity
with $w_i^2 / p_i \le L w_i$, where $w_i = \|\mathbf{A}_i\| \, \|\mathbf{B}_i\|$, and
Cauchy–Schwarz, and the tails are Markov's inequality on the square.

## Main results

* `NLAlib.integral_conjTranspose_mul_mul_of_hasLaw_samplingSketch`: unbiasedness.
* `NLAlib.integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch`: the exact second
  moment.
* `NLAlib.integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_samplingSketch`: the
  domination bound.
* `NLAlib.measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch`,
  `NLAlib.measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch_of_ne_zero`:
  tails.
* `NLAlib.measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch` and
  `measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketchWithoutReplacement`:
  approximate multiplication in the spectral norm, both sampling models.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n q r : Type*} [Fintype k] [Fintype n] [Fintype q] [Fintype r] [DecidableEq n]
  {S : Ω → Matrix k n 𝕜} {p : n → ℝ≥0} {A : Matrix n q 𝕜} {B : Matrix n r 𝕜} {L ε t : ℝ}

/-! ### Reduction to i.i.d. indices -/

variable (k) in
/-- The rank-one atom of row $i$, $(\lvert k \rvert \, p_i)^{-1} (\mathbf{A}_i)^{\mathsf{H}}
\mathbf{B}_i$; the zero matrix where $p_i = 0$. -/
private noncomputable def ammAtom (p : n → ℝ≥0) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) (i : n) :
    Matrix q r 𝕜 :=
  ((Fintype.card k : ℝ) * p i)⁻¹ • Matrix.vecMulVec (star (A i)) (B i)

omit [Fintype q] [Fintype r] in
/-- The sampled product as a sum of atoms. -/
private theorem conjTranspose_mul_samplingSketchMatrix_mul_mul (p : n → ℝ≥0) (ι : k → n)
    (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Aᴴ * (samplingSketchMatrix p ι : Matrix k n 𝕜)ᴴ * samplingSketchMatrix p ι * B =
      ∑ j, ammAtom k p A B (ι j) := by
  rw [Matrix.mul_assoc (Aᴴ * _), ← Matrix.conjTranspose_mul]
  exact conjTranspose_samplingSketchMatrix_mul_mul p ι A B

omit [Fintype q] [Fintype r] [DecidableEq n] in
/-- The weighted atoms sum to $\mathbf{A}^{\mathsf{H}} \mathbf{B} / \lvert k \rvert$ when every
zero weight sits on a row where $\mathbf{A}$ or $\mathbf{B}$ vanishes. -/
private theorem sum_smul_ammAtom (hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0) :
    ∑ i, (p i : ℝ) • ammAtom k p A B i = (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B) := by
  rw [Matrix.conjTranspose_mul_eq_sum_vecMulVec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ammAtom, smul_smul]
  by_cases hi : p i = 0
  · rcases hsupport i hi with h | h <;> ext <;> simp [h, Matrix.vecMulVec_apply]
  · have hi' : (p i : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hi
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hi', mul_one]

omit [Fintype n] [DecidableEq n] in
/-- The weighted squared Frobenius norm of an atom. -/
private theorem mul_frobNorm_ammAtom_sq (i : n) :
    (p i : ℝ) * frobNorm (ammAtom k p A B i) ^ 2 =
      ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i /
        (Fintype.card k : ℝ) ^ 2 := by
  have hstar : ‖WithLp.toLp 2 (star (A i))‖ = ‖WithLp.toLp 2 (A i)‖ := by
    simp only [EuclideanSpace.norm_eq, Pi.star_apply, norm_star]
  rw [ammAtom, frobNorm_real_smul, frobNorm_vecMulVec, hstar,
    abs_of_nonneg (by positivity)]
  by_cases hi : (p i : ℝ) = 0
  · simp [hi]
  · field_simp

/-- An expectation of a continuous function of the sketch is an expectation over i.i.d.
indices. -/
private theorem integral_comp_of_hasLaw_samplingSketch [MeasurableSpace n]
    [MeasurableSingletonClass n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : HasLaw S (samplingSketch k p) μ) {F : Matrix k n 𝕜 → E} (hF : Continuous F) :
    ∫ ω, F (S ω) ∂μ =
      ∫ ι, F (samplingSketchMatrix p ι) ∂(Measure.pi fun _ : k => samplingMeasure p) := by
  have h := hS.integral_comp hF.aestronglyMeasurable
  rw [samplingSketch_eq_map, integral_map (measurable_of_finite _).aemeasurable
    hF.aestronglyMeasurable] at h
  exact h

/-- A continuous function of the sketch is integrable. -/
private theorem integrable_comp_of_hasLaw_samplingSketch {E : Type*} [NormedAddCommGroup E]
    (hS : HasLaw S (samplingSketch k p) μ) {F : Matrix k n 𝕜 → E} (hF : Continuous F) :
    Integrable (fun ω => F (S ω)) μ := by
  let _ : MeasurableSpace n := ⊤
  have hF' : AEStronglyMeasurable F (samplingSketch k p) := hF.aestronglyMeasurable
  rw [hS.integrable_comp_iff hF', samplingSketch_eq_map,
    integrable_map_measure (by rwa [samplingSketch_eq_map] at hF')
      (measurable_of_finite _).aemeasurable]
  exact .of_finite

omit [DecidableEq n] in
/-- The expectation of a function of one i.i.d. index is the weighted sum. -/
private theorem integral_comp_eval_pi_samplingMeasure [MeasurableSpace n]
    [MeasurableSingletonClass n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hp : ∑ i, p i = 1) (G : n → E) (j : k) :
    ∫ ι, G (ι j) ∂(Measure.pi fun _ : k => samplingMeasure p) = ∑ i, (p i : ℝ) • G i := by
  have := isProbabilityMeasure_samplingMeasure p hp
  rw [← integral_samplingMeasure]
  exact (HasLaw.id.eval j).integral_comp (StronglyMeasurable.of_discrete).aestronglyMeasurable

omit [DecidableEq n] in
/-- **The Frobenius variance of an i.i.d. sum**: for $\lvert k \rvert$ i.i.d. indices $\iota_j$
and `Z` centred under the weights,
$$\mathbb{E} \Bigl\| \sum_j Z(\iota_j) \Bigr\|_{\mathsf{F}}^2
= \lvert k \rvert \sum_i p_i \|Z(i)\|_{\mathsf{F}}^2 \,.$$ -/
private theorem integral_frobNorm_sum_sq_pi [MeasurableSpace n] [MeasurableSingletonClass n]
    (hp : ∑ i, p i = 1) (Z : n → Matrix q r 𝕜) (hZ : ∑ i, (p i : ℝ) • Z i = 0) :
    ∫ ι, frobNorm (∑ j, Z (ι j)) ^ 2 ∂(Measure.pi fun _ : k => samplingMeasure p) =
      Fintype.card k * ∑ i, (p i : ℝ) * frobNorm (Z i) ^ 2 := by
  classical
  have := isProbabilityMeasure_samplingMeasure p hp
  have hind : iIndepFun (fun j (ι : k → n) => ι j) (Measure.pi fun _ : k => samplingMeasure p) :=
    iIndepFun_pi (X := fun _ => id) fun _ => measurable_id.aemeasurable
  have hZ' : ∑ i, (p i : ℝ) • (Z i)ᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hZ
    simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_zero] using h
  have hf : Measurable fun i : n => (Z i)ᴴ := measurable_of_finite _
  have hg : Measurable Z := measurable_of_finite _
  have hmf (j : k) : MemLp (fun ι : k → n => (Z (ι j))ᴴ) 2
      (Measure.pi fun _ : k => samplingMeasure p) := .of_discrete
  have hmg (j : k) : MemLp (fun ι : k → n => Z (ι j)) 2
      (Measure.pi fun _ : k => samplingMeasure p) := .of_discrete
  have h0 (j : k) : ∫ ι, (Z (ι j))ᴴ ∂(Measure.pi fun _ : k => samplingMeasure p) = 0 := by
    rw [integral_comp_eval_pi_samplingMeasure hp (fun i => (Z i)ᴴ) j, hZ']
  have key := integral_sum_mul_sum_of_iIndepFun hind hf hg hmf hmg h0
  calc ∫ ι, frobNorm (∑ j, Z (ι j)) ^ 2 ∂(Measure.pi fun _ : k => samplingMeasure p)
      = ∫ ι, RCLike.re ((∑ j, Z (ι j))ᴴ * ∑ j, Z (ι j)).trace
          ∂(Measure.pi fun _ : k => samplingMeasure p) := by
        simp only [frobNorm_sq_eq_re_trace]
    _ = RCLike.re (∫ ι, (∑ j, Z (ι j))ᴴ * ∑ j, Z (ι j)
          ∂(Measure.pi fun _ : k => samplingMeasure p)).trace := by
        rw [integral_re .of_finite, Matrix.integral_trace .of_finite]
    _ = ∑ j : k, ∑ i, (p i : ℝ) * frobNorm (Z i) ^ 2 := by
        simp only [Matrix.conjTranspose_sum]
        rw [key, Matrix.trace_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_comp_eval_pi_samplingMeasure hp (fun i => (Z i)ᴴ * Z i) j,
          Matrix.trace_sum, map_sum]
        simp only [Matrix.trace_smul, RCLike.smul_re, frobNorm_sq_eq_re_trace]
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### The sampled product -/

/-- The sampled product $\mathbf{A}^{\mathsf{H}} \mathbf{S}^{\mathsf{H}} \mathbf{S} \mathbf{B}$ of a
row-sampling sketch is integrable, for any weights and
any number of samples: the sketch takes finitely many values. -/
theorem integrable_conjTranspose_mul_mul_of_hasLaw_samplingSketch [DecidableEq r]
    (hS : HasLaw S (samplingSketch k p) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Integrable (fun ω => Aᴴ * (S ω)ᴴ * S ω * B) μ :=
  integrable_comp_of_hasLaw_samplingSketch hS (F := fun M => Aᴴ * Mᴴ * M * B) (by fun_prop)

/-- **Row sampling is unbiased for matrix products**:
$\mathbb{E}[\mathbf{A}^{\mathsf{H}} \mathbf{S}^{\mathsf{H}} \mathbf{S} \mathbf{B}]
= \mathbf{A}^{\mathsf{H}} \mathbf{B}$ for $k$ nonempty when every zero weight sits on a row
where $\mathbf{A}$ or
$\mathbf{B}$ vanishes (in particular when every weight is positive).
[MartinssonTropp2020, §7.1] (the sampled estimator, positive weights). -/
theorem integral_conjTranspose_mul_mul_of_hasLaw_samplingSketch [Nonempty k] [DecidableEq r]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0) :
    ∫ ω, Aᴴ * (S ω)ᴴ * S ω * B ∂μ = Aᴴ * B := by
  let _ : MeasurableSpace n := ⊤
  have := isProbabilityMeasure_samplingMeasure p hp
  have hK : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [integral_comp_of_hasLaw_samplingSketch hS (F := fun M => Aᴴ * Mᴴ * M * B) (by fun_prop)]
  simp only [conjTranspose_mul_samplingSketchMatrix_mul_mul]
  rw [integral_finsetSum _ fun j _ => .of_finite]
  simp only [integral_comp_eval_pi_samplingMeasure hp (ammAtom k p A B), sum_smul_ammAtom hsupport,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hK, one_smul]

/-! ### The Frobenius error -/

/-- The squared Frobenius error of the sampled product is integrable, for any weights and any
number of samples. -/
theorem integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch
    (hS : HasLaw S (samplingSketch k p) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2) μ :=
  integrable_comp_of_hasLaw_samplingSketch hS
    (F := fun M => frobNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B) ^ 2)
    ((continuous_frobNorm.comp (by fun_prop)).pow 2)

/-- **Approximate matrix multiplication by sampling, exact second moment**:
$$\mathbb{E} \|\mathbf{A}^{\mathsf{H}} \mathbf{S}^{\mathsf{H}} \mathbf{S} \mathbf{B} -
\mathbf{A}^{\mathsf{H}} \mathbf{B}\|_{\mathsf{F}}^2
= \frac{1}{\lvert k \rvert} \Bigl( \sum_i \frac{\|\mathbf{A}_i\|^2 \|\mathbf{B}_i\|^2}{p_i} -
\|\mathbf{A}^{\mathsf{H}} \mathbf{B}\|_{\mathsf{F}}^2 \Bigr)$$
for $k$ nonempty, when every zero weight sits on a row where $\mathbf{A}$ or $\mathbf{B}$ vanishes
(there the term is
$0/0 = 0$). [MartinssonTropp2020, §7.1] (the estimator);
[DrineasKannanMahoney2006, Lemma 4, equation (4)] (the identity), there for real matrices and
at most as many samples as rows; here over $\Bbbk$ and every positive sample count.
Result: amm-sampling -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch [Nonempty k]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ =
      (∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i -
        frobNorm (Aᴴ * B) ^ 2) / Fintype.card k := by
  let _ : MeasurableSpace n := ⊤
  set K : ℝ := (Fintype.card k : ℝ) with hKdef
  have hK : K ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set c : Matrix q r 𝕜 := K⁻¹ • (Aᴴ * B) with hc
  have hsum (ι : k → n) : Aᴴ * (samplingSketchMatrix p ι : Matrix k n 𝕜)ᴴ *
      samplingSketchMatrix p ι * B - Aᴴ * B = ∑ j, (ammAtom k p A B (ι j) - c) := by
    rw [conjTranspose_mul_samplingSketchMatrix_mul_mul, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, hc, smul_smul, ← hKdef, mul_inv_cancel₀ hK,
      one_smul]
  have hZ : ∑ i, (p i : ℝ) • (ammAtom k p A B i - c) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, sum_smul_ammAtom hsupport, ← Finset.sum_smul,
      ← NNReal.coe_sum, hp, NNReal.coe_one, one_smul, hc]
    exact sub_self _
  rw [integral_comp_of_hasLaw_samplingSketch hS
    (F := fun M => frobNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B) ^ 2)
    ((continuous_frobNorm.comp (by fun_prop)).pow 2)]
  simp only [hsum]
  rw [integral_frobNorm_sum_sq_pi hp _ hZ]
  have hvar : ∑ i, (p i : ℝ) * frobNorm (ammAtom k p A B i - c) ^ 2 =
      ∑ i, (p i : ℝ) * frobNorm (ammAtom k p A B i) ^ 2 - frobNorm c ^ 2 := by
    have hin : ∑ i, (p i : ℝ) * frobInner (ammAtom k p A B i) c = frobNorm c ^ 2 := by
      simp only [← frobInner_smul_left, ← frobInner_sum_left]
      rw [sum_smul_ammAtom hsupport, ← hc, frobInner_self]
    have hp' : ∑ i, (p i : ℝ) = 1 := by rw [← NNReal.coe_sum, hp, NNReal.coe_one]
    simp only [frobNorm_sub_sq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hp', one_mul]
    have h2 : ∑ i, (p i : ℝ) * (2 * frobInner (ammAtom k p A B i) c) = 2 * frobNorm c ^ 2 := by
      rw [← hin, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
    ring
  rw [hvar]
  simp only [mul_frobNorm_ammAtom_sq, ← Finset.sum_div]
  rw [hc, frobNorm_real_smul, abs_of_nonneg (by positivity)]
  field_simp
  rw [hKdef]
  ring

/-- **Approximate matrix multiplication by sampling, domination form**: if
$\|\mathbf{A}_i\| \, \|\mathbf{B}_i\| \le L p_i$ for every row, with $k$ nonempty,
$$\mathbb{E} \|\mathbf{A}^{\mathsf{H}} \mathbf{S}^{\mathsf{H}} \mathbf{S} \mathbf{B} -
\mathbf{A}^{\mathsf{H}} \mathbf{B}\|_{\mathsf{F}}^2
\le \frac{L \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}}{\lvert k \rvert} \,.$$
Zero weights are allowed. At the optimal weights $p_i \propto \|\mathbf{A}_i\| \, \|\mathbf{B}_i\|$,
where $L = \sum_i \|\mathbf{A}_i\| \, \|\mathbf{B}_i\|$, this is
$\|\mathbf{A}\|_{\mathsf{F}}^2 \|\mathbf{B}\|_{\mathsf{F}}^2 / \lvert k \rvert$ by
Cauchy–Schwarz, and $\beta$-approximations of them have $L = W/\beta$, with $W$ that sum.
[MartinssonTropp2020, §7.1]; [DrineasKannanMahoney2006, Theorem 1, equation (8)].
There the bound is
$\|\mathbf{A}\|_{\mathsf{F}}^2 \|\mathbf{B}\|_{\mathsf{F}}^2 / (\beta \lvert k \rvert)$.
Result: amm-sampling -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_samplingSketch [Nonempty k]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ L * p i) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ ≤
      L * frobNorm A * frobNorm B / Fintype.card k := by
  set w : n → ℝ := fun i => ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ with hw
  have hw0 (i : n) : 0 ≤ w i := by positivity
  have hp' : ∑ i, (p i : ℝ) = 1 := by rw [← NNReal.coe_sum, hp, NNReal.coe_one]
  have hL : 0 ≤ L := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hw0 i).trans (hdom i)
    rwa [Finset.sum_const_zero, ← Finset.mul_sum, hp', mul_one] at h
  have hsupport (i : n) (hi : p i = 0) : A i = 0 ∨ B i = 0 := by
    have h : w i = 0 := le_antisymm (by simpa [hi] using hdom i) (hw0 i)
    rcases mul_eq_zero.1 h with h | h
    · exact .inl (by simpa using h)
    · exact .inr (by simpa using h)
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  rw [integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch hS hp hsupport]
  refine div_le_div_of_nonneg_right ?_ hK.le
  have hterm (i : n) : ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i ≤ L * w i := by
    rw [← mul_pow]
    change w i ^ 2 / _ ≤ _
    rcases (p i).coe_nonneg.eq_or_lt with h0 | h0
    · rw [← h0, div_zero]
      exact mul_nonneg hL (hw0 i)
    · rw [div_le_iff₀ h0]
      calc w i ^ 2 = w i * w i := sq _
        _ ≤ w i * (L * p i) := mul_le_mul_of_nonneg_left (hdom i) (hw0 i)
        _ = L * w i * p i := by ring
  have hcs : ∑ i, w i ≤ frobNorm A * frobNorm B := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖WithLp.toLp 2 (A i)‖)
      (fun i => ‖WithLp.toLp 2 (B i)‖)
    have hA : frobNorm A ^ 2 = ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 := frobNorm_sq_eq_sum_row A
    have hB : frobNorm B ^ 2 = ∑ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 := frobNorm_sq_eq_sum_row B
    rwa [← hA, ← hB,
      Real.sqrt_sq (frobNorm_nonneg _), Real.sqrt_sq (frobNorm_nonneg _)] at h
  calc ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i - frobNorm (Aᴴ * B) ^ 2
      ≤ ∑ i, L * w i := by
        have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
        nlinarith [sq_nonneg (frobNorm (Aᴴ * B))]
    _ = L * ∑ i, w i := by rw [Finset.mul_sum]
    _ ≤ L * (frobNorm A * frobNorm B) := mul_le_mul_of_nonneg_left hcs hL
    _ = L * frobNorm A * frobNorm B := by ring

/-- **The tail of approximate matrix multiplication by sampling**: for $k$ nonempty,
under the domination
$\|\mathbf{A}_i\| \, \|\mathbf{B}_i\| \le L p_i$, the Frobenius error exceeds $t > 0$ with
probability at most
$$\frac{L \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}}{\lvert k \rvert \, t^2}$$
(Markov on the square). [MartinssonTropp2020, §7.1]. -/
theorem measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch [Nonempty k]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ L * p i) (ht : 0 < t) :
    μ.real {ω | t ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      L * frobNorm A * frobNorm B / (Fintype.card k * t ^ 2) := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  calc μ.real {ω | t ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)}
      ≤ μ.real {ω | t ^ 2 ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2} :=
        measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => pow_le_pow_left₀ ht.le hω 2)
    _ ≤ (∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ) / t ^ 2 :=
        measureReal_ge_le_integral_div (ae_of_all _ fun ω => sq_nonneg _)
          (integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch hS A B)
          (by positivity)
    _ ≤ (L * frobNorm A * frobNorm B / Fintype.card k) / t ^ 2 :=
        div_le_div_of_nonneg_right
          (integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_samplingSketch hS hp hdom)
          (by positivity)
    _ = _ := by rw [div_div]

/-- **The relative tail of approximate matrix multiplication by sampling**: for $k$ nonempty,
under the domination
$\|\mathbf{A}_i\| \, \|\mathbf{B}_i\| \le L p_i$, the Frobenius error exceeds
$\varepsilon \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}$ with probability at most
$$\frac{L}{\lvert k \rvert \, \varepsilon^2
  \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}}$$
for $\varepsilon > 0$ and nonzero $\mathbf{A}$, $\mathbf{B}$: the event of the JL-moment form
`NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le`, the instance
$t = \varepsilon \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}$ of
`NLAlib.measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch`.
[MartinssonTropp2020, §7.1]. -/
theorem measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch_of_ne_zero
    [Nonempty k] (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ L * p i) (hε : 0 < ε)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      L / (Fintype.card k * ε ^ 2 * frobNorm A * frobNorm B) := by
  have hA' : 0 < frobNorm A :=
    (frobNorm_nonneg A).lt_of_ne (Ne.symm (frobNorm_eq_zero_iff.not.2 hA))
  have hB' : 0 < frobNorm B :=
    (frobNorm_nonneg B).lt_of_ne (Ne.symm (frobNorm_eq_zero_iff.not.2 hB))
  have hK : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine (measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch hS hp hdom
    (t := ε * frobNorm A * frobNorm B) (by positivity)).trans (le_of_eq ?_)
  field_simp

/-! ### The spectral norm -/

omit [Fintype q] in
/-- A rank-one matrix times its conjugate transpose:
$\mathbf{u}\mathbf{v}^{\mathsf{T}}(\mathbf{u}\mathbf{v}^{\mathsf{T}})^{\mathsf{H}}
= \|\mathbf{v}\|^2\,\mathbf{u}\bar{\mathbf{u}}^{\mathsf{T}}$. -/
private theorem vecMulVec_mul_conjTranspose_vecMulVec (u : q → 𝕜) (v : r → 𝕜) :
    Matrix.vecMulVec u v * (Matrix.vecMulVec u v)ᴴ =
      (‖WithLp.toLp 2 v‖ ^ 2) • Matrix.vecMulVec u (star u) := by
  rw [Matrix.conjTranspose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
  have h : v ⬝ᵥ star v = ((‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) := by
    rw [EuclideanSpace.norm_sq_eq, dotProduct]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [Pi.star_apply, RCLike.star_def, RCLike.mul_conj]
  rw [h, ← RCLike.real_smul_eq_coe_smul, Matrix.vecMulVec_smul]

omit [DecidableEq n] in
/-- Under $\|\mathbf{A}_i\|^2 \le a p_i$ and $\sum_i p_i = 1$, $\|\mathbf{A}\|_2^2 \le a$. -/
private theorem specNorm_sq_le_of_norm_sq_le {a : ℝ} (hp : ∑ i, p i = 1)
    (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * p i) : specNorm A ^ 2 ≤ a := by
  have hp' : ∑ i, (p i : ℝ) = 1 := by rw [← NNReal.coe_sum, hp, NNReal.coe_one]
  refine (pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm A) 2).trans ?_
  rw [frobNorm_sq_eq_sum_row]
  calc ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ ∑ i, a * p i := Finset.sum_le_sum fun i _ => hA i
    _ = a := by rw [← Finset.mul_sum, hp', mul_one]

omit [Fintype n] [DecidableEq n] in
/-- Under the two dominations an atom has spectral norm at most $\sqrt{ab}/\lvert k\rvert$. -/
private theorem specNorm_ammAtom_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * p i)
    (hB : ∀ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ b * p i) (i : n) :
    specNorm (ammAtom k p A B i) ≤ √(a * b) / Fintype.card k := by
  rw [ammAtom, specNorm_real_smul, specNorm_vecMulVec, EuclideanSpace.norm_toLp_star]
  rcases (p i).coe_nonneg.eq_or_lt with h0 | h0
  · rw [← h0, mul_zero, inv_zero, abs_zero, zero_mul]
    positivity
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card k)).eq_or_lt with hk | hk
  · rw [← hk, zero_mul, inv_zero, abs_zero, zero_mul, div_zero]
  have hAB : ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ √(a * b) * p i := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖),
      ← Real.sqrt_sq (p i).coe_nonneg, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc (‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖) ^ 2
        = ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 := mul_pow _ _ _
      _ ≤ (a * p i) * (b * p i) := mul_le_mul (hA i) (hB i) (sq_nonneg _) (by positivity)
      _ = a * b * (p i : ℝ) ^ 2 := by ring
  rw [abs_of_pos (by positivity)]
  calc ((Fintype.card k : ℝ) * p i)⁻¹ * (‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖)
      ≤ ((Fintype.card k : ℝ) * p i)⁻¹ * (√(a * b) * p i) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
    _ = √(a * b) / Fintype.card k := by field_simp

omit [DecidableEq n] in
/-- Under the two dominations the mean atom has spectral norm at most
$\sqrt{ab}/\lvert k\rvert$. -/
private theorem specNorm_inv_smul_conjTranspose_mul_le {a b : ℝ} (hb : 0 ≤ b)
    (hp : ∑ i, p i = 1) (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * p i)
    (hB : ∀ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ b * p i) :
    specNorm ((Fintype.card k : ℝ)⁻¹ • (Aᴴ * B)) ≤ √(a * b) / Fintype.card k := by
  have hA' : specNorm A ≤ √a := Real.le_sqrt_of_sq_le (specNorm_sq_le_of_norm_sq_le hp hA)
  have hB' : specNorm B ≤ √b := Real.le_sqrt_of_sq_le (specNorm_sq_le_of_norm_sq_le hp hB)
  rw [specNorm_real_smul, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc specNorm (Aᴴ * B) ≤ specNorm Aᴴ * specNorm B := specNorm_mul_le _ _
    _ ≤ √a * √b := by
        rw [specNorm_conjTranspose]
        exact mul_le_mul hA' hB' (specNorm_nonneg _) (Real.sqrt_nonneg _)
    _ = √(a * b) := by rw [Real.sqrt_mul' _ hb]

omit [DecidableEq n] in
/-- Under the two dominations a centred atom has spectral norm at most
$2\sqrt{ab}/\lvert k\rvert$. -/
private theorem specNorm_ammAtom_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : ∑ i, p i = 1)
    (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * p i)
    (hB : ∀ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ b * p i) (i : n) :
    specNorm (ammAtom k p A B i - (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B)) ≤
      2 * √(a * b) / Fintype.card k := by
  refine (specNorm_sub_le _ _).trans ?_
  have h1 := specNorm_ammAtom_le (k := k) ha hb hA hB i
  have h2 := specNorm_inv_smul_conjTranspose_mul_le (k := k) hb hp hA hB
  rw [mul_div_assoc, two_mul]
  exact add_le_add h1 h2

omit [DecidableEq n] in
open scoped ComplexOrder in
/-- **The one-sided variance of the centred atoms**: under the two dominations,
$\|\sum_i p_i \mathbf{Z}_i\mathbf{Z}_i^{\mathsf{H}}\|_2 \le
b\|\mathbf{A}\|_2^2/\lvert k\rvert^2$. -/
private theorem specNorm_sum_smul_ammAtom_sub_mul_le {a b : ℝ} (hb : 0 ≤ b) (hp : ∑ i, p i = 1)
    (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * p i)
    (hB : ∀ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ b * p i) :
    specNorm (∑ i, (p i : ℝ) • ((ammAtom k p A B i - (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B)) *
      (ammAtom k p A B i - (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B))ᴴ)) ≤
      b * specNorm A ^ 2 / Fintype.card k ^ 2 := by
  classical
  set K : ℝ := (Fintype.card k : ℝ) with hK
  set c : Matrix q r 𝕜 := K⁻¹ • (Aᴴ * B) with hc
  set Z := ammAtom k p A B with hZ
  have hp' : ∑ i, (p i : ℝ) = 1 := by rw [← NNReal.coe_sum, hp, NNReal.coe_one]
  have hmean : ∑ i, (p i : ℝ) • Z i = c :=
    sum_smul_ammAtom fun i hi => .inl (row_eq_zero_of_norm_sq_le hA i hi)
  have hmean' : ∑ i, (p i : ℝ) • (Z i)ᴴ = cᴴ := by
    rw [← hmean, Matrix.conjTranspose_sum]
    simp only [Matrix.conjTranspose_smul, star_trivial]
  have hexp : ∑ i, (p i : ℝ) • ((Z i - c) * (Z i - c)ᴴ) =
      ∑ i, (p i : ℝ) • (Z i * (Z i)ᴴ) - c * cᴴ := by
    have h1 : ∑ i, (p i : ℝ) • (Z i * cᴴ) = c * cᴴ := by
      simp only [← Matrix.smul_mul]
      rw [← Matrix.sum_mul, hmean]
    have h2 : ∑ i, (p i : ℝ) • (c * (Z i)ᴴ) = c * cᴴ := by
      simp only [← Matrix.mul_smul]
      rw [← Matrix.mul_sum, hmean']
    have h3 : ∑ i, (p i : ℝ) • (c * cᴴ) = c * cᴴ := by
      rw [← Finset.sum_smul, hp', one_smul]
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, smul_sub,
      Finset.sum_sub_distrib, h1, h2, h3]
    abel
  have hM : (∑ i, (p i : ℝ) • ((Z i - c) * (Z i - c)ᴴ)).PosSemidef :=
    Matrix.posSemidef_sum _ fun i _ =>
      (Matrix.posSemidef_self_mul_conjTranspose _).smul (p i).coe_nonneg
  have hMN : ∑ i, (p i : ℝ) • ((Z i - c) * (Z i - c)ᴴ) ≤ ∑ i, (p i : ℝ) • (Z i * (Z i)ᴴ) := by
    rw [Matrix.le_iff, hexp, sub_sub_cancel]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hterm (i : n) : (p i : ℝ) • (Z i * (Z i)ᴴ) ≤
      (b / K ^ 2) • Matrix.vecMulVec (star (A i)) (A i) := by
    have hP := Matrix.posSemidef_vecMulVec_star_self (A i)
    have hZZ : (p i : ℝ) • (Z i * (Z i)ᴴ) =
        ((p i : ℝ) * ((K * p i)⁻¹ * (K * p i)⁻¹ * ‖WithLp.toLp 2 (B i)‖ ^ 2)) •
          Matrix.vecMulVec (star (A i)) (A i) := by
      rw [hZ, ammAtom, Matrix.conjTranspose_smul, star_trivial ((Fintype.card k : ℝ) * p i)⁻¹,
        Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_conjTranspose_vecMulVec, star_star,
        smul_smul, smul_smul, smul_smul, ← hK]
      ring_nf
    rw [hZZ, Matrix.le_iff, ← sub_smul]
    refine hP.smul (sub_nonneg.2 ?_)
    rcases (p i).coe_nonneg.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]
      positivity
    rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card k)).eq_or_lt with hk0 | hk0
    · rw [hK, ← hk0]
      simp
    calc (p i : ℝ) * ((K * p i)⁻¹ * (K * p i)⁻¹ * ‖WithLp.toLp 2 (B i)‖ ^ 2)
        = ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i / K ^ 2 := by field_simp
      _ ≤ b * p i / p i / K ^ 2 := by gcongr; exact hB i
      _ = b / K ^ 2 := by field_simp
  have hN : ∑ i, (p i : ℝ) • (Z i * (Z i)ᴴ) ≤ (b / K ^ 2) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_mul_eq_sum_vecMulVec, Finset.smul_sum]
    exact Finset.sum_le_sum fun i _ => hterm i
  refine (hM.specNorm_le_specNorm_of_le (hMN.trans hN)).trans_eq ?_
  rw [specNorm_real_smul, specNorm_conjTranspose_mul_self, abs_of_nonneg (by positivity)]
  ring

omit [Fintype q] [Fintype r] [DecidableEq n] in
/-- The conjugate transpose of a centred atom is the centred atom with the factors swapped. -/
private theorem conjTranspose_ammAtom_sub (i : n) :
    (ammAtom k p A B i - (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B))ᴴ =
      ammAtom k p B A i - (Fintype.card k : ℝ)⁻¹ • (Bᴴ * A) := by
  rw [Matrix.conjTranspose_sub, ammAtom, ammAtom, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, star_star,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    star_trivial ((Fintype.card k : ℝ) * p i)⁻¹, star_trivial (Fintype.card k : ℝ)⁻¹]

omit [DecidableEq n] in
/-- The degenerate cases of the spectral tails: $t = 0$, $\mathbf{A} = \mathbf{0}$ or
$\mathbf{B} = \mathbf{0}$. -/
private theorem measureReal_specNorm_ge_le_of_eq_zero [IsProbabilityMeasure μ] [Nonempty r]
    (T : Ω → Matrix k n 𝕜) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) (ht : 0 ≤ t)
    (h : t = 0 ∨ A = 0 ∨ B = 0) (x : ℝ) :
    μ.real {ω | t ≤ specNorm (Aᴴ * (T ω)ᴴ * T ω * B - Aᴴ * B)} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(Fintype.card k * t ^ 2 / 2) / x) := by
  have hr : (1 : ℝ) ≤ Fintype.card q + Fintype.card r := by
    have : (1 : ℝ) ≤ Fintype.card r := by exact_mod_cast Fintype.card_pos
    linarith [(Nat.cast_nonneg (α := ℝ) (Fintype.card q))]
  rcases ht.eq_or_lt with rfl | ht'
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      neg_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans hr
  have hE : {ω | t ≤ specNorm (Aᴴ * (T ω)ᴴ * T ω * B - Aᴴ * B)} = ∅ := by
    rcases h with h | h | h
    · exact absurd h ht'.ne'
    all_goals
      ext ω
      simp [h, specNorm_zero, not_le.2 ht']
  rw [hE, measureReal_empty]
  positivity

/-- The final comparison of the Bernstein exponents. -/
private theorem mul_exp_le_of_le_max_div {K v x y s c : ℝ} (hK : 0 < K) (ht : 0 < t)
    (hs : 0 < s) (hc : 0 ≤ c) (hv0 : 0 ≤ v) (hv : v ≤ max x y / K) :
    c * Real.exp (-(t ^ 2 / 2) / (v + 2 * s / K * t / 3)) ≤
      c * Real.exp (-(K * t ^ 2 / 2) / (max x y + 2 * s * t / 3)) := by
  have hD1 : 0 < v + 2 * s / K * t / 3 := by positivity
  have hle : v + 2 * s / K * t / 3 ≤ (max x y + 2 * s * t / 3) / K := by
    rw [add_div]
    have : 2 * s / K * t / 3 = 2 * s * t / 3 / K := by ring
    linarith
  have hD2 : 0 < max x y + 2 * s * t / 3 := by
    have := hD1.trans_le hle
    rwa [div_pos_iff_of_pos_right hK] at this
  have heq : K * t ^ 2 / 2 / (max x y + 2 * s * t / 3) =
      t ^ 2 / 2 / ((max x y + 2 * s * t / 3) / K) := by
    field_simp
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc
  rw [neg_div, neg_div, neg_le_neg_iff, heq]
  exact div_le_div_of_nonneg_left (by positivity) hD1 hle

omit [Fintype n] [DecidableEq n] in
/-- A positive domination constant, unless the matrix is zero. -/
private theorem pos_of_norm_sq_le {a : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * p i) (hA0 : A ≠ 0) : 0 < a :=
  ha.lt_of_ne fun h => hA0 <| funext fun i =>
    row_eq_zero_of_norm_sq_le (L := 0) (p := 0) (fun j => by simpa [← h] using hA j) i rfl

omit [Fintype q] [Fintype r] in
/-- The sampled product error as a sum of centred atoms. -/
private theorem conjTranspose_mul_samplingSketchMatrix_mul_mul_sub [Nonempty k] (ι : k → n) :
    Aᴴ * (samplingSketchMatrix p ι : Matrix k n 𝕜)ᴴ * samplingSketchMatrix p ι * B - Aᴴ * B =
      ∑ j, (ammAtom k p A B (ι j) - (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B)) := by
  have hK : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [conjTranspose_mul_samplingSketchMatrix_mul_mul, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hK, one_smul]

omit [Fintype q] [Fintype r] [DecidableEq n] in
/-- The centred atoms have weighted mean zero. -/
private theorem sum_smul_ammAtom_sub (hp : ∑ i, p i = 1)
    (hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0) :
    ∑ i, (p i : ℝ) • (ammAtom k p A B i - (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B)) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, sum_smul_ammAtom hsupport, ← Finset.sum_smul,
    ← NNReal.coe_sum, hp, NNReal.coe_one, one_smul]
  exact sub_self _

/-- The variance bound in the form the comparison takes. -/
private theorem mul_le_div_of_le_div_sq {K s x : ℝ} (hK : 0 < K) (h : s ≤ x / K ^ 2) :
    K * s ≤ x / K :=
  calc K * s ≤ K * (x / K ^ 2) := mul_le_mul_of_nonneg_left h hK.le
    _ = x / K := by field_simp

/-! ### Spectral tails -/

/-- **Approximate matrix multiplication in the spectral norm by row sampling**: for $k$ and $r$
nonempty, weights $p$ summing to $1$ with $\|\mathbf{A}_i\|^2 \le a p_i$ and
$\|\mathbf{B}_i\|^2 \le b p_i$ for every row $i$, $a, b \ge 0$, the row-sampling sketch
$\mathbf{S}$ with $\lvert k\rvert$ i.i.d. rows drawn with probabilities $p$, and $t \ge 0$,
$$\mathbb{P}\bigl[t \le \|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_2\bigr] \le (\lvert q\rvert + \lvert r\rvert)
\exp\Bigl(-\frac{\lvert k\rvert t^2/2}{\max(b\|\mathbf{A}\|_2^2, a\|\mathbf{B}\|_2^2) +
2\sqrt{ab}\,t/3}\Bigr)\,.$$
Rectangular matrix Bernstein (`NLAlib.measureReal_specNorm_sum_ge_le_bernstein`) for the
centred atoms. At $p_i \propto \|\mathbf{A}_i\|^2 + \|\mathbf{B}_i\|^2$ this is the stable-rank
form. [MartinssonTropp2020, §7.3, Theorem 7.2]; [Tropp2015, Corollary 6.2.1].
Result: amm-sampling-spectral -/
theorem measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch [Nonempty k]
    [Nonempty r] (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * p i)
    (hB : ∀ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ b * p i) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(Fintype.card k * t ^ 2 / 2) /
        (max (b * specNorm A ^ 2) (a * specNorm B ^ 2) + 2 * √(a * b) * t / 3)) := by
  classical
  let _ : MeasurableSpace n := ⊤
  have := isProbabilityMeasure_samplingMeasure p hp
  have hE : MeasurableSet {M : Matrix k n 𝕜 | t ≤ specNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B)} :=
    measurableSet_le measurable_const (continuous_specNorm.comp (by fun_prop)).measurable
  rw [hS.measureReal_eq hE, ← (hasLaw_samplingSketchMatrix (𝕜 := 𝕜) (p := p)
    (HasLaw.id (μ := Measure.pi fun _ : k => samplingMeasure p))).measureReal_eq hE]
  by_cases hdeg : t = 0 ∨ A = 0 ∨ B = 0
  · exact measureReal_specNorm_ge_le_of_eq_zero _ A B ht hdeg _
  obtain ⟨ht0, hA0, hB0⟩ : t ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 := by tauto
  have ha' := pos_of_norm_sq_le ha hA hA0
  have hb' := pos_of_norm_sq_le hb hB hB0
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  set Z := fun i => ammAtom k p A B i - (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B) with hZdef
  simp only [id, conjTranspose_mul_samplingSketchMatrix_mul_mul_sub]
  have hmean (j : k) : ∫ ι, Z (ι j) ∂(Measure.pi fun _ : k => samplingMeasure p) = 0 := by
    rw [integral_comp_eval_pi_samplingMeasure hp Z j]
    exact sum_smul_ammAtom_sub hp fun i hi => .inl (row_eq_zero_of_norm_sq_le hA i hi)
  have h := measureReal_specNorm_sum_ge_le_bernstein
    (μ := Measure.pi fun _ : k => samplingMeasure p)
    (S := fun j (ι : k → n) => Z (ι j)) (L := 2 * √(a * b) / Fintype.card k)
    (iIndepFun_pi (X := fun (_ : k) (i : n) => Z i) fun _ => (measurable_of_finite _).aemeasurable)
    (by positivity) (fun j => .of_discrete) hmean
    (fun j => ae_of_all _ fun ι => specNorm_ammAtom_sub_le ha hb hp hA hB (ι j)) ht
  refine h.trans ?_
  simp only [integral_comp_eval_pi_samplingMeasure hp (fun i => Z i * (Z i)ᴴ),
    integral_comp_eval_pi_samplingMeasure hp (fun i => (Z i)ᴴ * Z i), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, specNorm_real_smul, abs_of_pos hK]
  have hswap (i : n) : (Z i)ᴴ * Z i = (ammAtom k p B A i - (Fintype.card k : ℝ)⁻¹ • (Bᴴ * A)) *
      (ammAtom k p B A i - (Fintype.card k : ℝ)⁻¹ • (Bᴴ * A))ᴴ := by
    simp only [hZdef]
    rw [conjTranspose_ammAtom_sub, conjTranspose_ammAtom_sub]
  have h1 := specNorm_sum_smul_ammAtom_sub_mul_le (k := k) hb hp hA hB
  have h2 := specNorm_sum_smul_ammAtom_sub_mul_le (k := k) ha hp hB hA
  simp only [← hswap] at h2
  refine mul_exp_le_of_le_max_div hK (ht.lt_of_ne' ht0) (by positivity) (by positivity)
    (by positivity) (max_le ?_ ?_)
  · exact (mul_le_div_of_le_div_sq hK h1).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hK.le)
  · exact (mul_le_div_of_le_div_sq hK h2).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hK.le)

/-- **Approximate matrix multiplication in the spectral norm by row sampling without
replacement**: for $k$ and $r$ nonempty, $\|\mathbf{A}_i\|^2 \le a/\lvert n\rvert$ and
$\|\mathbf{B}_i\|^2 \le b/\lvert n\rvert$ for every row $i$, $a, b \ge 0$, the row-sampling sketch
$\mathbf{S} = \sqrt{\lvert n\rvert/\lvert k\rvert}\,\mathbf{P}^{\mathsf{H}}$ of $\lvert k\rvert$
distinct uniformly sampled rows, and $t \ge 0$,
$$\mathbb{P}\bigl[t \le \|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_2\bigr] \le (\lvert q\rvert + \lvert r\rvert)
\exp\Bigl(-\frac{\lvert k\rvert t^2/2}{\max(b\|\mathbf{A}\|_2^2, a\|\mathbf{B}\|_2^2) +
2\sqrt{ab}\,t/3}\Bigr)\,,$$
the bound with replacement at uniform weights: matrix Bernstein without replacement
(`NLAlib.measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`) for the centred
population $(\lvert n\rvert/\lvert k\rvert)\mathbf{A}_i^{\mathsf{H}}\mathbf{B}_i -
\mathbf{A}^{\mathsf{H}}\mathbf{B}/\lvert k\rvert$. For $\lvert n\rvert < \lvert k\rvert$ the law is
$0$. [MartinssonTropp2020, §7.3, Theorem 7.2] (with replacement); [GrossNesme2010, Section D] for
the comparison.
Result: amm-sampling-spectral -/
theorem
    measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketchWithoutReplacement
    [Nonempty k] [Nonempty r] (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)
    (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * (Fintype.card n : ℝ)⁻¹)
    (hB : ∀ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ b * (Fintype.card n : ℝ)⁻¹) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(Fintype.card k * t ^ 2 / 2) /
        (max (b * specNorm A ^ 2) (a * specNorm B ^ 2) + 2 * √(a * b) * t / 3)) := by
  classical
  let _ : MeasurableSpace n := ⊤
  have hE : MeasurableSet {M : Matrix k n 𝕜 | t ≤ specNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B)} :=
    measurableSet_le measurable_const (continuous_specNorm.comp (by fun_prop)).measurable
  rw [hS.measureReal_eq hE, ← (hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective (𝕜 := 𝕜)
    (HasLaw.id (μ := uniformOn {ι : k → n | Function.Injective ι}))).measureReal_eq hE]
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [uniformOn_injective_of_card_lt hk, measureReal_zero_apply]
    positivity
  have := isProbabilityMeasure_uniformOn_injective hk
  by_cases hdeg : t = 0 ∨ A = 0 ∨ B = 0
  · exact measureReal_specNorm_ge_le_of_eq_zero _ A B ht hdeg _
  obtain ⟨ht0, hA0, hB0⟩ : t ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 := by tauto
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 (Fintype.card_pos.trans_le hk)
  set w : n → ℝ≥0 := fun _ => (Fintype.card n : ℝ≥0)⁻¹ with hw
  have hwr (i : n) : ((w i : ℝ≥0) : ℝ) = (Fintype.card n : ℝ)⁻¹ := by
    rw [hw, NNReal.coe_inv, NNReal.coe_natCast]
  have hp : ∑ i, w i = 1 := by
    rw [hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fintype.card_pos.trans_le hk).ne')
  have hA' (i : n) : ‖WithLp.toLp 2 (A i)‖ ^ 2 ≤ a * w i := by rw [hwr i]; exact hA i
  have hB' (i : n) : ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ b * w i := by rw [hwr i]; exact hB i
  have ha' := pos_of_norm_sq_le ha hA' hA0
  have hb' := pos_of_norm_sq_le hb hB' hB0
  set Z := fun i => ammAtom k w A B i - (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B) with hZdef
  simp only [id, conjTranspose_mul_samplingSketchMatrix_mul_mul_sub]
  have hsum0 : ∑ i, Z i = 0 := by
    have h0 := sum_smul_ammAtom_sub (k := k) (B := B) hp
      fun i hi => .inl (row_eq_zero_of_norm_sq_le hA' i hi)
    simp only [hwr, ← Finset.smul_sum] at h0
    exact (smul_eq_zero.1 h0).resolve_left (inv_ne_zero hn.ne')
  have h := measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective
    (μ := uniformOn {ι : k → n | Function.Injective ι}) (ι := id) (S := Z)
    (L := 2 * √(a * b) / Fintype.card k) HasLaw.id (by positivity) hsum0
    (fun i => specNorm_ammAtom_sub_le ha hb hp hA' hB' i) ht
  refine h.trans ?_
  have hswap (i : n) : (Z i)ᴴ * Z i = (ammAtom k w B A i - (Fintype.card k : ℝ)⁻¹ • (Bᴴ * A)) *
      (ammAtom k w B A i - (Fintype.card k : ℝ)⁻¹ • (Bᴴ * A))ᴴ := by
    simp only [hZdef]
    rw [conjTranspose_ammAtom_sub, conjTranspose_ammAtom_sub]
  have h1 := specNorm_sum_smul_ammAtom_sub_mul_le (k := k) hb hp hA' hB'
  have h2 := specNorm_sum_smul_ammAtom_sub_mul_le (k := k) ha hp hB' hA'
  simp only [← hswap] at h2
  simp only [hwr, ← Finset.smul_sum, specNorm_real_smul, abs_inv, Nat.abs_cast] at h1 h2
  refine mul_exp_le_of_le_max_div hK (ht.lt_of_ne' ht0) (by positivity) (by positivity)
    (by positivity) ?_
  rw [mul_max_of_nonneg _ _ (by positivity)]
  refine max_le ?_ ?_
  · rw [div_mul_eq_mul_div, mul_div_assoc, div_eq_inv_mul]
    exact (mul_le_div_of_le_div_sq hK h1).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hK.le)
  · rw [div_mul_eq_mul_div, mul_div_assoc, div_eq_inv_mul]
    exact (mul_le_div_of_le_div_sq hK h2).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hK.le)

end NLAlib
