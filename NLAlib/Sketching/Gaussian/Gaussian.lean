/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.Sketching.Properties.JohnsonLindenstrauss
public import NLAlib.Sketching.Properties.Oblivious

/-!
# Gaussian sketches

The Gaussian sketch is $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{G}$ for a standard Gaussian
`G : Matrix k n ℝ` ($\lvert k \rvert$ rows). It is written out in each statement,
`fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω`, with the hypothesis `HasLaw G (gaussianMatrix k n) μ`;
there is no named sketch law.

It is an isotropic sketch, a random subspace injection and embedding for a fixed $\mathbf{U}$ with
orthonormal columns (Gordon's extreme singular values, one tail $e^{-t^2/2}$ per side), an
oblivious subspace injection and embedding, and has the distributional Johnson–Lindenstrauss
property with Dasgupta and Gupta's exponent $\varepsilon^2/4 - \varepsilon^3/6$, the exact JL
second moment $2 / \lvert k \rvert$, and the JL moment property at every exponent $p$ from its
sub-exponential JL tail, so that $O(\log(1/\delta)/\varepsilon^2)$ rows give it at
$p = \max(2, \log(1/\delta))$ and hence approximate matrix multiplication with failure
probability $\delta$: for `hG` and that size,
```
(hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le hG hε hε1 hδ hk
  ).measureReal_frobNorm_conjTranspose_mul_sub_ge_le …
```
with `le_max_left` for the side condition $2 \le p$. Its projection-cost-preserving forms are
in `NLAlib.Sketching.Gaussian.ProjectionCost`. The sample sizes are named quantities
(docs/contributing/statements.md §2, rule 2), each with its nonnegativity, monotonicity and an
explicit
comparison; the "$\lvert k \rvert \ge \ldots$ suffices" forms are corollaries of the tails.

Degenerate cases: for empty $k$, $(\sqrt{0})^{-1} = 0$ and $\mathbf{S} = \mathbf{0}$, which is not
isotropic, hence `[Nonempty k]` on isotropy, the OSI and the moments; the hypothesis
$t \le \sqrt{\lvert k \rvert} - \sqrt{\lvert p \rvert}$ then forces $p$ empty. The JL bound is $2$
for $\lvert k \rvert = 0$ and at least $2$ for $\varepsilon \ge 3/2$.

## Main definitions

* `NLAlib.gaussianEmbeddingDim`, `NLAlib.gaussianInjectionDim`, `NLAlib.jlDim`,
  `NLAlib.jlMomentDim`: the sample
  sizes, for the OSE <!-- value gaussianEmbeddingDim d \varepsilon \delta -->
  $9 (\sqrt{d} + \sqrt{2 \log(2/\delta)})^2/\varepsilon^2$,
  for the OSI <!-- value gaussianInjectionDim d \varepsilon \delta -->
  $4 (\sqrt{d} + \sqrt{2 \log(1/\delta)})^2/\varepsilon^2$, for
  JL <!-- value jlDim \varepsilon \delta -->$\log(2/\delta)/(\varepsilon^2/4 - \varepsilon^3/6)$
  and for the JL moment
  property <!-- value jlMomentDim \varepsilon \delta -->$128\max(2, \log(1/\delta))/\varepsilon^2$;
  `NLAlib.two_mul_exp_le_of_jlDim_le` inverts the JL tail at `jlDim`, and
  `NLAlib.two_mul_twentyOne_pow_mul_exp_le_of_jlDim_le` the JL-plus-a-net tail.

## Main results

* `NLAlib.isIsotropicSketch_of_hasLaw_gaussianMatrix`.
* `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_gaussianMatrix`: the fixed-subspace
  embedding, $(1 \mp (\sqrt{\lvert p \rvert} + t)/\sqrt{\lvert k \rvert})^2$ outside
  $2 e^{-t^2/2}$.
* `NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`,
  `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix`.
* `NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix`: distributional JL.
* `NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix`: the JL moment property at $p = 2$, from the
  exact variance.
* `NLAlib.hasJLMoment_subexponentialMomentBound_of_hasLaw_gaussianMatrix`: the JL moment property
  at every $p > 0$, and its size form
  `NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le` at $p = \max(2, \log(1/\delta))$.
* `NLAlib.exists_forall_abs_norm_mulVec_sq_sub_le_of_jlDim_le`: the Johnson–Lindenstrauss lemma.
* `NLAlib.exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix`,
  `NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`,
  `NLAlib.exists_forall_hasJLProperty_of_hasLaw_gaussianMatrix`,
  `NLAlib.exists_forall_hasJLMoment_of_hasLaw_gaussianMatrix`: the asymptotic forms,
  $O((d + \log(1/\delta))/\varepsilon^2)$ and $O(\log(1/\delta)/\varepsilon^2)$ rows.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n p ι : Type*} [Fintype k]
  [Fintype n] [Fintype p] {G : Ω → Matrix k n ℝ} {U : Matrix n p ℝ} {d d' : ℕ}
  {t ε ε' δ δ' : ℝ}

/-! ### Proof-local arithmetic -/

private theorem one_sub_div_sq {s b c : ℝ} (hs : 0 < s) :
    s⁻¹ ^ 2 * (s - b - c) ^ 2 = (1 - (b + c) / s) ^ 2 := by
  field_simp
  ring

private theorem one_add_div_sq {s b c : ℝ} (hs : 0 < s) :
    s⁻¹ ^ 2 * (s + b + c) ^ 2 ≤ (1 + (b + c) / s) ^ 2 := by
  apply le_of_eq
  field_simp
  ring

/-- The squared distortion of the Gaussian sketch at $\mathbf{x} = \|\mathbf{x}\| \mathbf{u}$,
expanded in $Y = \|\mathbf{G}\mathbf{u}\|^2$:
$(\|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2)^2
= \|\mathbf{x}\|^4 (Y^2 / \lvert k \rvert^2 - 2 Y / \lvert k \rvert + 1)$. -/
private theorem sq_sketch_distortion_eq {x u : n → ℝ} (hxu : ∀ A : Matrix k n ℝ,
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2 =
        ‖WithLp.toLp 2 x‖ ^ 2 * (‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 - 1)) (A : Matrix k n ℝ) :
    (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 =
      ‖WithLp.toLp 2 x‖ ^ 4 / Fintype.card k ^ 2 * (‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2) ^ 2 -
        2 * ‖WithLp.toLp 2 x‖ ^ 4 / Fintype.card k * ‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 +
          ‖WithLp.toLp 2 x‖ ^ 4 := by
  rw [← Matrix.smul_mulVec, hxu, Matrix.smul_mulVec,
    EuclideanSpace.norm_toLp_inv_sqrt_card_smul_sq]
  ring

/-- $\|\mathbf{g}\|^2$ and $\|\mathbf{g}\|^4$ of a standard Gaussian vector $\mathbf{g}$ are
integrable. -/
private theorem integrable_chiSq {g : Ω → k → ℝ} (hg : HasLaw g (gaussianVector k) μ) :
    Integrable (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2) μ ∧
      Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2) μ := by
  have hk : (0 : ℝ) ≤ Fintype.card k := Nat.cast_nonneg _
  have h1 := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 1) (by linarith)
  have h2 := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 2) (by linarith)
  simp only [Real.rpow_one, Real.rpow_two] at h1 h2
  exact ⟨h1, h2⟩

/-- $\mathbb{E}\|\mathbf{g}\|^2 = \lvert k \rvert$ and
$\mathbb{E}\|\mathbf{g}\|^4 = \lvert k \rvert (\lvert k \rvert + 2)$ for a standard Gaussian vector
$\mathbf{g}$ in $\mathbb{R}^k$. -/
private theorem integral_chiSq [Nonempty k] {g : Ω → k → ℝ}
    (hg : HasLaw g (gaussianVector k) μ) :
    ∫ ω, ‖WithLp.toLp 2 (g ω)‖ ^ 2 ∂μ = Fintype.card k ∧
      ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 ∂μ = Fintype.card k * (Fintype.card k + 2) := by
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have h1 := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 1) (by linarith)
  have h2 := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 2) (by linarith)
  simp only [Real.rpow_one, Real.rpow_two] at h1 h2
  have hΓ : Real.Gamma ((Fintype.card k : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hΓ1 : Real.Gamma ((Fintype.card k : ℝ) / 2 + 1) =
      (Fintype.card k : ℝ) / 2 * Real.Gamma ((Fintype.card k : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have hΓ2 : Real.Gamma ((Fintype.card k : ℝ) / 2 + 2) =
      ((Fintype.card k : ℝ) / 2 + 1) * Real.Gamma ((Fintype.card k : ℝ) / 2 + 1) := by
    rw [show (Fintype.card k : ℝ) / 2 + 2 = (Fintype.card k : ℝ) / 2 + 1 + 1 by ring]
    exact Real.Gamma_add_one (by positivity)
  refine ⟨?_, ?_⟩
  · rw [h1, hΓ1]
    field_simp
  · rw [h2, hΓ2, hΓ1]
    field_simp

/-- The parameter $t = \sqrt{2 \log a}$ of the sample-size corollaries, for $a \ge 1$:
$t \ge 0$ and $e^{-t^2/2} = 1/a$. -/
private theorem exists_sqrt_two_mul_log {a : ℝ} (ha : 1 ≤ a) :
    ∃ t : ℝ, 0 ≤ t ∧ √(2 * Real.log a) = t ∧ Real.exp (-t ^ 2 / 2) = a⁻¹ := by
  have hL : 0 ≤ Real.log a := Real.log_nonneg ha
  refine ⟨_, Real.sqrt_nonneg _, rfl, ?_⟩
  rw [Real.sq_sqrt (by positivity), show -(2 * Real.log a) / 2 = -Real.log a by ring,
    Real.exp_neg, Real.exp_log (by linarith)]

/-- From $c^2 (\sqrt{d} + t)^2 / \varepsilon^2 \le \lvert k \rvert$: the ratio
$(\sqrt{d} + t)/\sqrt{\lvert k \rvert}$ is nonnegative and at most $\varepsilon / c$, and
$t \le \sqrt{\lvert k \rvert} - \sqrt{d}$, for $c > 0$, $\varepsilon > 0$, $t \ge 0$ and
$\varepsilon \le c$. -/
private theorem div_sqrt_le_of_mul_sq_div_le {c : ℝ} (hc : 0 < c) (hε : 0 < ε) (ht : 0 ≤ t)
    (hεc : ε ≤ c) (hk : c ^ 2 * (√(d : ℝ) + t) ^ 2 / ε ^ 2 ≤ Fintype.card k) :
    0 ≤ (√(d : ℝ) + t) / √(Fintype.card k : ℝ) ∧
      (√(d : ℝ) + t) / √(Fintype.card k : ℝ) ≤ ε / c ∧
      t ≤ √(Fintype.card k : ℝ) - √(d : ℝ) := by
  have hsk2 : √(Fintype.card k : ℝ) ^ 2 = Fintype.card k := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsk0 : 0 ≤ √(Fintype.card k : ℝ) := Real.sqrt_nonneg _
  have hA : 0 ≤ √(d : ℝ) + t := by positivity
  rw [div_le_iff₀ (by positivity), ← hsk2] at hk
  have h2 : c * (√(d : ℝ) + t) ≤ ε * √(Fintype.card k : ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 (by
      rw [mul_pow, mul_pow]; linarith)
  refine ⟨by positivity, ?_, ?_⟩
  · rcases hsk0.eq_or_lt with h0 | h0
    · rw [← h0, div_zero]; positivity
    · rw [div_le_div_iff₀ h0 hc]; linarith
  · have : ε * √(Fintype.card k : ℝ) ≤ c * √(Fintype.card k : ℝ) :=
      mul_le_mul_of_nonneg_right hεc hsk0
    nlinarith

/-! ### Sample sizes -/

/-- The **Gaussian embedding dimension** <!-- value gaussianEmbeddingDim d \varepsilon \delta -->
$9 (\sqrt{d} + \sqrt{2 \log(2/\delta)})^2/\varepsilon^2$: a Gaussian sketch with at least this
many rows is an oblivious subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$
and failure probability $\delta$, for $0 < \varepsilon \le 1$
(`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le`). The
value the proof reaches ($t = \sqrt{2 \log(2/\delta)}$ and
$(\sqrt{d} + t)/\sqrt{\lvert k \rvert} \le \varepsilon/3$); [Woodruff2014, Theorem 6] has
$\Theta((d + \log(1/\delta))/\varepsilon^2)$ with no constant. Consumers use
`gaussianEmbeddingDim_le`, the bound $18 (d + 2 \log(2/\delta))/\varepsilon^2$. Junk values:
$0$ at $\varepsilon = 0$; for $\delta \ge 2$ the logarithm is at most $0$ and its square root is
$0$. -/
noncomputable irreducible_def gaussianEmbeddingDim (d : ℕ) (ε δ : ℝ) : ℝ :=
  9 * (√(d : ℝ) + √(2 * Real.log (2 / δ))) ^ 2 / ε ^ 2

/-- The Gaussian embedding dimension is nonnegative. -/
theorem gaussianEmbeddingDim_nonneg (d : ℕ) (ε δ : ℝ) : 0 ≤ gaussianEmbeddingDim d ε δ := by
  rw [gaussianEmbeddingDim_def]
  positivity

/-- The Gaussian embedding dimension is monotone in the dimension $d$ and antitone in the
distortion $\varepsilon > 0$ and the failure probability $\delta > 0$. -/
theorem gaussianEmbeddingDim_mono (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ)
    (hδδ' : δ ≤ δ') : gaussianEmbeddingDim d ε' δ' ≤ gaussianEmbeddingDim d' ε δ := by
  rw [gaussianEmbeddingDim_def, gaussianEmbeddingDim_def]
  have hd' : (d : ℝ) ≤ d' := by exact_mod_cast hd
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  gcongr

/-- The explicit comparison for
$0 < \delta \le 2$, <!-- value gaussianEmbeddingDim d \varepsilon \delta -->
$$\frac{9 (\sqrt{d} + \sqrt{2 \log(2/\delta)})^2}{\varepsilon^2} \le
\frac{18 (d + 2 \log(2/\delta))}{\varepsilon^2} \,,$$
the left side being `gaussianEmbeddingDim d ε δ`. -/
theorem gaussianEmbeddingDim_le (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    gaussianEmbeddingDim d ε δ ≤ 18 * (d + 2 * Real.log (2 / δ)) / ε ^ 2 := by
  rw [gaussianEmbeddingDim_def]
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg ((one_le_div₀ hδ).2 hδ2)
  have h1 := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have h2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (2 / δ))
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  nlinarith [sq_nonneg (√(d : ℝ) - √(2 * Real.log (2 / δ)))]

/-- The **Gaussian injection dimension** <!-- value gaussianInjectionDim d \varepsilon \delta -->
$4 (\sqrt{d} + \sqrt{2 \log(1/\delta)})^2/\varepsilon^2$: a Gaussian sketch with at least this
many rows is an oblivious subspace injection for dimension $d$ with constant $1 - \varepsilon$ and
failure probability $\delta$, for $0 < \varepsilon \le 2$ and $0 < \delta < 1$
(`NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le`). The
value the proof reaches ($t = \sqrt{2 \log(1/\delta)}$ and
$(\sqrt{d} + t)/\sqrt{\lvert k \rvert} \le \varepsilon/2$); one tail, against the embedding's two.
Consumers use `gaussianInjectionDim_le`. Junk values: $0$ at $\varepsilon = 0$; for
$\delta \ge 1$ the logarithm is at most $0$ and its square root is $0$. -/
noncomputable irreducible_def gaussianInjectionDim (d : ℕ) (ε δ : ℝ) : ℝ :=
  4 * (√(d : ℝ) + √(2 * Real.log (1 / δ))) ^ 2 / ε ^ 2

/-- The Gaussian injection dimension is positive for $\varepsilon \ne 0$ and
$0 < \delta < 1$; a sketch with at least this many rows has a row. -/
theorem gaussianInjectionDim_pos (d : ℕ) (hε : ε ≠ 0) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < gaussianInjectionDim d ε δ := by
  rw [gaussianInjectionDim_def]
  have hL : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div₀ hδ).2 hδ1)
  have h1 : 0 < √(2 * Real.log (1 / δ)) := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 < √(d : ℝ) + √(2 * Real.log (1 / δ)) := by positivity
  positivity

/-- The Gaussian injection dimension is monotone in the dimension $d$ and antitone in the
distortion $\varepsilon > 0$ and the failure probability $\delta > 0$. -/
theorem gaussianInjectionDim_mono (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ)
    (hδδ' : δ ≤ δ') : gaussianInjectionDim d ε' δ' ≤ gaussianInjectionDim d' ε δ := by
  rw [gaussianInjectionDim_def, gaussianInjectionDim_def]
  have hd' : (d : ℝ) ≤ d' := by exact_mod_cast hd
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  gcongr

/-- The explicit comparison for
$0 < \delta \le 1$, <!-- value gaussianInjectionDim d \varepsilon \delta -->
$$\frac{4 (\sqrt{d} + \sqrt{2 \log(1/\delta)})^2}{\varepsilon^2} \le
\frac{8 (d + 2 \log(1/\delta))}{\varepsilon^2} \,,$$
the left side being `gaussianInjectionDim d ε δ`. -/
theorem gaussianInjectionDim_le (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    gaussianInjectionDim d ε δ ≤ 8 * (d + 2 * Real.log (1 / δ)) / ε ^ 2 := by
  rw [gaussianInjectionDim_def]
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div₀ hδ).2 hδ1)
  have h1 := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have h2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (1 / δ))
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  nlinarith [sq_nonneg (√(d : ℝ) - √(2 * Real.log (1 / δ)))]

/-- The **Johnson–Lindenstrauss dimension** <!-- value jlDim \varepsilon \delta -->
$\log(2/\delta)/(\varepsilon^2/4 - \varepsilon^3/6)$: a Gaussian or Haar sketch with
at least this many rows has the distributional JL property with distortion $\varepsilon$ and failure
probability $\delta$, for $0 < \varepsilon < 3/2$
(`NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le`). The value the proof reaches, from
Dasgupta and Gupta's exponent. Consumers use `jlDim_le`, $12 \log(2/\delta) / \varepsilon^2$ for
$\varepsilon \le 1$. Junk values: for $\varepsilon \ge 3/2$ the denominator is at most $0$, and
the value is $0$ at $\varepsilon = 3/2$ and of the sign of $-\log(2/\delta)$ beyond; for
$\delta \ge 2$ the logarithm is at most $0$. -/
noncomputable irreducible_def jlDim (ε δ : ℝ) : ℝ :=
  Real.log (2 / δ) / (ε ^ 2 / 4 - ε ^ 3 / 6)

/-- The Johnson–Lindenstrauss dimension is positive for $0 < \varepsilon < 3/2$ and
$0 < \delta < 2$. -/
theorem jlDim_pos (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ) (hδ2 : δ < 2) : 0 < jlDim ε δ := by
  rw [jlDim_def]
  refine div_pos (Real.log_pos ((one_lt_div₀ hδ).2 hδ2)) ?_
  have : 0 < ε ^ 2 := by positivity
  nlinarith

/-- The Johnson–Lindenstrauss dimension is antitone in the distortion on $(0, 1]$ and in the
failure probability, for $0 < \delta \le 2$. -/
theorem jlDim_mono (hε : 0 < ε) (hεε' : ε ≤ ε') (hε'1 : ε' ≤ 1) (hδ : 0 < δ) (hδδ' : δ ≤ δ')
    (hδ2 : δ ≤ 2) : jlDim ε' δ' ≤ jlDim ε δ := by
  rw [jlDim_def, jlDim_def]
  have hε' : 0 < ε' := hε.trans_le hεε'
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg ((one_le_div₀ hδ).2 hδ2)
  have hLL : Real.log (2 / δ') ≤ Real.log (2 / δ) := by gcongr
  have hf : 0 < ε ^ 2 / 4 - ε ^ 3 / 6 := by
    have : 0 < ε ^ 2 := by positivity
    nlinarith
  have hff : ε ^ 2 / 4 - ε ^ 3 / 6 ≤ ε' ^ 2 / 4 - ε' ^ 3 / 6 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hεε') (sub_nonneg.2 hε'1), mul_pos hε hε',
      mul_nonneg (sub_nonneg.2 hεε') (mul_nonneg (sub_nonneg.2 hε'1) hε.le),
      mul_nonneg (sub_nonneg.2 hεε') (mul_nonneg (sub_nonneg.2 hε'1) hε'.le),
      mul_nonneg (sub_nonneg.2 hεε') (mul_nonneg (sub_nonneg.2 (hεε'.trans hε'1)) hε.le)]
  exact (div_le_div_of_nonneg_right hLL (hf.le.trans hff)).trans
    (div_le_div_of_nonneg_left hL hf hff)

/-- The explicit comparison for $\varepsilon \le 1$ and
$0 < \delta \le 2$, <!-- value jlDim \varepsilon \delta -->
$$\frac{\log(2/\delta)}{\varepsilon^2/4 - \varepsilon^3/6} \le
\frac{12 \log(2/\delta)}{\varepsilon^2}$$
(`jlDim ε δ` on the left), since $\varepsilon^2/4 - \varepsilon^3/6 \ge \varepsilon^2/12$. -/
theorem jlDim_le (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    jlDim ε δ ≤ 12 * Real.log (2 / δ) / ε ^ 2 := by
  rw [jlDim_def]
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg ((one_le_div₀ hδ).2 hδ2)
  rcases eq_or_ne ε 0 with rfl | hε0
  · simp
  have he2 : 0 < ε ^ 2 := by positivity
  have hf : ε ^ 2 / 12 ≤ ε ^ 2 / 4 - ε ^ 3 / 6 := by
    nlinarith [mul_nonneg he2.le (sub_nonneg.2 hε1)]
  calc Real.log (2 / δ) / (ε ^ 2 / 4 - ε ^ 3 / 6) ≤ Real.log (2 / δ) / (ε ^ 2 / 12) :=
        div_le_div_of_nonneg_left hL (by positivity) hf
    _ = 12 * Real.log (2 / δ) / ε ^ 2 := by field_simp

/-- Inverting the JL tail at `jlDim`: for $0 < \varepsilon < 3/2$, $\delta > 0$
and <!-- value jlDim \varepsilon \delta -->
$K \ge \log(2/\delta)/(\varepsilon^2/4 - \varepsilon^3/6)$ (`jlDim ε δ`),
$2 e^{-K (\varepsilon^2/4 - \varepsilon^3/6)} \le \delta$. The step from the tail of every sketch
with Dasgupta and Gupta's exponent (Gaussian, Haar, signs) to its sample-size form. -/
theorem two_mul_exp_le_of_jlDim_le {K : ℝ} (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ)
    (hK : jlDim ε δ ≤ K) : 2 * Real.exp (-(K * (ε ^ 2 / 4 - ε ^ 3 / 6))) ≤ δ := by
  have hf : 0 < ε ^ 2 / 4 - ε ^ 3 / 6 := by
    have : 0 < ε ^ 2 := by positivity
    nlinarith
  rw [jlDim_def, div_le_iff₀ hf] at hK
  calc 2 * Real.exp (-(K * (ε ^ 2 / 4 - ε ^ 3 / 6))) ≤ 2 * Real.exp (-Real.log (2 / δ)) := by
        gcongr
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp

/-- Inverting the JL-plus-a-net tail at `jlDim`: for $0 < \varepsilon < 15/8$, $\delta > 0$
and <!-- value jlDim (4\varepsilon/5) (\delta/21^d) -->
$K \ge \log(2/(\delta/21^d))/((4\varepsilon/5)^2/4 - (4\varepsilon/5)^3/6)$ (the left side is
`jlDim (4ε/5) (δ/21^d)`), $2 \cdot 21^d e^{-K(4\varepsilon^2/25 - 32\varepsilon^3/375)} \le \delta$:
the step from the OSE tail of every sketch with Dasgupta and Gupta's exponent, through JL plus a
net at $4\varepsilon/5$ (`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`; signs, Haar), to its
sample-size form. -/
theorem two_mul_twentyOne_pow_mul_exp_le_of_jlDim_le {K : ℝ} (hε : 0 < ε) (hε3 : ε < 15 / 8)
    (hδ : 0 < δ) (hk : jlDim (4 * ε / 5) (δ / 21 ^ d) ≤ K) :
    2 * 21 ^ d * Real.exp (-(K * (4 * ε ^ 2 / 25 - 32 * ε ^ 3 / 375))) ≤ δ := by
  have h21 : (0 : ℝ) < 21 ^ d := by positivity
  have h := two_mul_exp_le_of_jlDim_le (by linarith) (by linarith) (by positivity) hk
  rw [show (4 * ε / 5) ^ 2 / 4 - (4 * ε / 5) ^ 3 / 6 = 4 * ε ^ 2 / 25 - 32 * ε ^ 3 / 375 by ring,
    le_div_iff₀ h21] at h
  linarith

/-- The **JL moment dimension** <!-- value jlMomentDim \varepsilon \delta -->
$128\max(2, \log(1/\delta))/\varepsilon^2$: a Gaussian or Haar sketch with at least this many rows
has the JL moment property with distortion $0 < \varepsilon \le 1$, failure probability $\delta$
and exponent $\max(2, \log(1/\delta))$
(`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`). The value the proof reaches,
inverting the readable form $2(vp)^{p/2} + 2(2bp)^{p}$ of the sub-exponential moment bound
(`NLAlib.subexponentialMomentBound_le`) at $v = b = 4/\lvert k\rvert$; that comparison loses a
factor exponential in $p$, so a Stirling-sharp inversion would lower the $128$ by a factor of
about $e$ without a statement change. Consumers use `jlMomentDim_nonneg`, `jlMomentDim_mono` and
`jlMomentDim_le`, $384\log(1/\delta)/\varepsilon^2$ for $\delta \le 1/2$. Junk: $0$ at
$\varepsilon = 0$. -/
noncomputable irreducible_def jlMomentDim (ε δ : ℝ) : ℝ :=
  128 * max 2 (Real.log (1 / δ)) / ε ^ 2

/-- The JL moment dimension <!-- value jlMomentDim \varepsilon \delta -->
$128\max(2, \log(1/\delta))/\varepsilon^2$ is nonnegative. -/
theorem jlMomentDim_nonneg (ε δ : ℝ) : 0 ≤ jlMomentDim ε δ := by
  rw [jlMomentDim_def]
  have : (0 : ℝ) ≤ max 2 (Real.log (1 / δ)) := le_max_of_le_left zero_le_two
  positivity

/-- The JL moment dimension <!-- value jlMomentDim \varepsilon \delta -->
$128\max(2, \log(1/\delta))/\varepsilon^2$ is antitone in the distortion $\varepsilon > 0$ and
in the failure probability $\delta > 0$. -/
theorem jlMomentDim_mono (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    jlMomentDim ε' δ' ≤ jlMomentDim ε δ := by
  rw [jlMomentDim_def, jlMomentDim_def]
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  have hM : (0 : ℝ) ≤ max 2 (Real.log (1 / δ')) := le_max_of_le_left zero_le_two
  have hL : Real.log (1 / δ') ≤ Real.log (1 / δ) := by gcongr
  calc 128 * max 2 (Real.log (1 / δ')) / ε' ^ 2 ≤ 128 * max 2 (Real.log (1 / δ')) / ε ^ 2 := by
        gcongr
    _ ≤ 128 * max 2 (Real.log (1 / δ)) / ε ^ 2 := by gcongr

/-- The explicit comparison for $0 < \delta \le 1/2$, <!-- value jlMomentDim \varepsilon \delta -->
$$128\max(2, \log(1/\delta))/\varepsilon^2 \le \frac{384\log(1/\delta)}{\varepsilon^2}$$
(`jlMomentDim ε δ` on the left), since $\log(1/\delta) \ge \log 2 > 2/3$ there; the step of every
asymptotic form through `jlMomentDim`. -/
theorem jlMomentDim_le (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    jlMomentDim ε δ ≤ 384 * Real.log (1 / δ) / ε ^ 2 := by
  rw [jlMomentDim_def]
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have hl2 := Real.log_two_gt_d9
  have hmax : max 2 (Real.log (1 / δ)) ≤ 3 * Real.log (1 / δ) :=
    max_le (by linarith) (by linarith)
  calc 128 * max 2 (Real.log (1 / δ)) / ε ^ 2 ≤ 128 * (3 * Real.log (1 / δ)) / ε ^ 2 := by
        gcongr
    _ = 384 * Real.log (1 / δ) / ε ^ 2 := by ring

/-! ### Isotropy -/

/-- A Gaussian sketch is isotropic: $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$
for $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{G}$, $k$ nonempty. Its rows are isotropic
(`NLAlib.hasLaw_col_of_hasLaw_gaussianMatrix` on $\mathbf{G}^{\mathsf{H}}$) and
`NLAlib.isIsotropicSketch_smul_of_isIsotropic` scales them. -/
theorem isIsotropicSketch_of_hasLaw_gaussianMatrix [DecidableEq n] [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) :
    IsIsotropicSketch (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) μ := by
  exact isIsotropicSketch_smul_of_isIsotropic fun i =>
    isIsotropic_of_hasLaw_gaussianVector (hG.eval i)

/-! ### A fixed subspace -/

variable [DecidableEq p]

/-- The upper half for a fixed $\mathbf{U}$ with orthonormal columns, in Loewner form:
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{G}$ is a subspace embedding with constants $0$ and
$(1 + (\sqrt{\lvert p \rvert} + t)/\sqrt{\lvert k \rvert})^2$ outside probability
$e^{-t^2/2}$, for $t \ge 0$. -/
private theorem measureReal_not_upper_le (hU : HasOrthonormalCols U)
    (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t) :
    μ.real {ω | ¬ IsSubspaceEmbedding ((√(Fintype.card k : ℝ))⁻¹ • G ω) U 0
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)} ≤
      Real.exp (-t ^ 2 / 2) := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have h := measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix
    (hasLaw_mul_const_of_hasLaw_gaussianMatrix hG hU) ht
  refine (measureReal_mono (fun ω hω => ?_)).trans h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hup
  apply hω
  have hE : IsSubspaceEmbedding (G ω) U 0
      ((√(Fintype.card k : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2) :=
    ⟨isSubspaceInjection_of_nonpos _ _ le_rfl, by rwa [hU.conjTranspose_mul_self]⟩
  have h' := hE.smul_real (√(Fintype.card k : ℝ))⁻¹
  rw [mul_zero] at h'
  refine h'.mono le_rfl ?_
  rcases (Real.sqrt_nonneg (Fintype.card k : ℝ)).eq_or_lt with h0 | h0
  · rw [← h0, inv_zero, zero_pow two_ne_zero, zero_mul]
    positivity
  · exact one_add_div_sq h0

/-- **Gaussian subspace injection**: for $\mathbf{U}$ with orthonormal columns,
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{G}$ satisfies
$$\Bigl(1 - \frac{\sqrt{\lvert p \rvert} + t}{\sqrt{\lvert k \rvert}}\Bigr)^2 \mathbf{I}
\preceq (\mathbf{S}\mathbf{U})^{\mathsf{H}} (\mathbf{S}\mathbf{U})$$
outside probability $e^{-t^2/2}$, for $0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{\lvert p \rvert}$.
$\mathbf{G}\mathbf{U}$ is a $k \times p$ Gaussian and Gordon's lower tail
(`NLAlib.measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix`)
applies. [MartinssonTropp2020, §8.7.2], there
$1 - (1 + \sqrt{\lvert p \rvert})/\sqrt{\lvert k \rvert} - t/\sqrt{\lvert k \rvert}$ for our $t$,
with unsquared singular values; one-sided here, so one tail. -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_gaussianMatrix
    (hU : HasOrthonormalCols U) (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) :
    HasSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2)) μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have h := measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (hasLaw_mul_const_of_hasLaw_gaussianMatrix hG hU) ht htk
  unfold HasSubspaceInjection
  rcases Nat.eq_zero_or_pos (Fintype.card k) with hk | hk
  · have hp : √(Fintype.card p : ℝ) = 0 := by
      rw [hk, Nat.cast_zero, Real.sqrt_zero] at htk
      linarith [Real.sqrt_nonneg (Fintype.card p : ℝ)]
    have : IsEmpty p := by
      rw [← Fintype.card_eq_zero_iff]
      exact_mod_cast (Real.sqrt_eq_zero (Nat.cast_nonneg _)).1 hp
    have he (ω : Ω) : IsSubspaceInjection ((√(Fintype.card k : ℝ))⁻¹ • G ω) U
        ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2) :=
      le_of_eq (Subsingleton.elim _ _)
    simp only [he, not_true_eq_false, Set.ofPred_false, measureReal_empty]
    positivity
  have hs : 0 < √(Fintype.card k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hk)
  refine (measureReal_mono (fun ω hω => ?_)).trans h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hlow
  apply hω
  have h' := ((hU.isSubspaceInjection_iff (S := G ω)).2 hlow).smul_real (√(Fintype.card k : ℝ))⁻¹
  rwa [one_sub_div_sq hs] at h'

/-- **Gaussian subspace embedding**: for $\mathbf{U}$ with orthonormal columns,
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{G}$ is a subspace embedding for
$\operatorname{range} \mathbf{U}$ with constants
$$\Bigl(1 \mp \frac{\sqrt{\lvert p \rvert} + t}{\sqrt{\lvert k \rvert}}\Bigr)^2$$
outside probability $2 e^{-t^2/2}$, for
$0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{\lvert p \rvert}$; Gordon's Gram
sandwich for the $k \times p$ Gaussian $\mathbf{G}\mathbf{U}$.
[Woodruff2014, Theorem 6]
($\lvert k \rvert = \Theta((\lvert p \rvert + \log(1/\delta))/\varepsilon^2)$, no constant);
[MartinssonTropp2020, §8.7.2], there
$1 \mp (1 + \sqrt{\lvert p \rvert})/\sqrt{\lvert k \rvert} \mp t/\sqrt{\lvert k \rvert}$ for our
$t$.
Result: gaussian-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_gaussianMatrix
    (hU : HasOrthonormalCols U) (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) :
    HasSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      (2 * Real.exp (-t ^ 2 / 2)) μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have h1 := hU.hasSubspaceInjection_of_hasLaw_gaussianMatrix hG ht htk
  have h2 := measureReal_not_upper_le hU hG ht
  rw [two_mul]
  refine h1.hasSubspaceEmbedding ((measureReal_mono (fun ω hω => ?_)).trans h2)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact fun h' => hω h'.upper

/-- The upper half alone: for a standard Gaussian $k \times n$ matrix $\mathbf{G}$, the
sketch $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{G}$ and $\mathbf{U}$ with orthonormal
columns,
$$(\mathbf{S}\mathbf{U})^{\mathsf{H}} (\mathbf{S}\mathbf{U})
\preceq \Bigl(1 + \frac{\sqrt{\lvert p \rvert} + t}{\sqrt{\lvert k \rvert}}\Bigr)^2 \mathbf{I}$$
outside probability $e^{-t^2/2}$, for every $t \ge 0$; no condition relating $t$, $k$ and $p$, and
one tail. The lower constant $0$ is vacuous. -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_zero_of_hasLaw_gaussianMatrix
    (hU : HasOrthonormalCols U) (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t) :
    HasSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) U 0
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2)) μ := by
  exact measureReal_not_upper_le hU hG ht

/-! ### Oblivious forms -/

/-- **The Gaussian OSI**: $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{G}$ is an oblivious
subspace injection for dimension $d$ with constant
$$\Bigl(1 - \frac{\sqrt{d} + t}{\sqrt{\lvert k \rvert}}\Bigr)^2$$
and failure probability $e^{-t^2/2}$, for $k$ nonempty and
$0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{d}$; for $d > \lvert n \rvert$ the proof works at
$\min(d, \lvert n \rvert)$ and weakens.
[CamanoEpperlyMeyerTropp2025, Definition 1.6, §1.5.0], who cite [MartinssonTropp2020, §8.7.2]
for it; the one-sided tail gives the better failure probability.
Result: gaussian-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix [DecidableEq n] [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) (d : ℕ) (ht : 0 ≤ t)
    (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2) (Real.exp (-t ^ 2 / 2)) μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hs : 0 < √(Fintype.card k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hm : √((min d (Fintype.card n) : ℕ) : ℝ) ≤ √(d : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast min_le_left _ _)
  have h := IsObliviousSubspaceInjection.of_hasOrthonormalCols (p := Fin (min d (Fintype.card n)))
    (isIsotropicSketch_of_hasLaw_gaussianMatrix hG) (by simp only [Fintype.card_fin]; omega)
    fun U hU => hU.hasSubspaceInjection_of_hasLaw_gaussianMatrix hG ht
      (by simp only [Fintype.card_fin]; linarith)
  refine ⟨h.isotropic, fun U hU => ?_⟩
  have hU' : U.rank ≤ Fintype.card (Fin (min d (Fintype.card n))) := by
    rw [Fintype.card_fin]
    exact le_min hU U.rank_le_card_width
  refine (h.injection U hU').mono ?_ le_rfl
  rw [Fintype.card_fin]
  have h0 : 0 ≤ 1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ) := by
    rw [sub_nonneg, div_le_one hs]
    linarith
  have h1 : (√((min d (Fintype.card n) : ℕ) : ℝ) + t) / √(Fintype.card k : ℝ) ≤
      (√(d : ℝ) + t) / √(Fintype.card k : ℝ) := by gcongr
  exact pow_le_pow_left₀ h0 (by linarith) 2

/-- **The Gaussian OSE**: $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{G}$ is an oblivious
subspace embedding for dimension $d$ with constants
$$\Bigl(1 \mp \frac{\sqrt{d} + t}{\sqrt{\lvert k \rvert}}\Bigr)^2$$
and failure probability $2 e^{-t^2/2}$, for $0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{d}$.
[Woodruff2014, Theorem 6];
[MartinssonTropp2020, §8.7.2].
Result: gaussian-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix
    (hG : HasLaw G (gaussianMatrix k n) μ) (d : ℕ) (ht : 0 ≤ t)
    (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      ((1 + (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2) (2 * Real.exp (-t ^ 2 / 2)) μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hm : √((min d (Fintype.card n) : ℕ) : ℝ) ≤ √(d : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast min_le_left _ _)
  have h := IsObliviousSubspaceEmbedding.of_hasOrthonormalCols (p := Fin (min d (Fintype.card n)))
    (by simp only [Fintype.card_fin]; omega)
    fun U hU => hU.hasSubspaceEmbedding_of_hasLaw_gaussianMatrix hG ht
      (by simp only [Fintype.card_fin]; linarith)
  intro U hU
  have hU' : U.rank ≤ Fintype.card (Fin (min d (Fintype.card n))) := by
    rw [Fintype.card_fin]
    exact le_min hU U.rank_le_card_width
  refine (h U hU').mono ?_ ?_ le_rfl
  · rw [Fintype.card_fin]
    rcases (Real.sqrt_nonneg (Fintype.card k : ℝ)).eq_or_lt with h0 | hs
    · rw [← h0, div_zero, div_zero]
    have h0 : 0 ≤ 1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ) := by
      rw [sub_nonneg, div_le_one hs]
      linarith
    have h1 : (√((min d (Fintype.card n) : ℕ) : ℝ) + t) / √(Fintype.card k : ℝ) ≤
        (√(d : ℝ) + t) / √(Fintype.card k : ℝ) := by gcongr
    exact pow_le_pow_left₀ h0 (by linarith) 2
  · rw [Fintype.card_fin]
    gcongr

/-! ### Johnson–Lindenstrauss -/

/-- **Distributional Johnson–Lindenstrauss for a Gaussian sketch**: for every unit $\mathbf{x}$
and every $\varepsilon \ge 0$,
$$\mathbb{P}\bigl[\varepsilon \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert\bigr]
\le 2 e^{-\lvert k \rvert (\varepsilon^2/4 - \varepsilon^3/6)} \,;$$
$\|\mathbf{S}\mathbf{x}\|^2 = \|\mathbf{G}\mathbf{x}\|^2/\lvert k \rvert$ is
$\chi^2_{\lvert k \rvert} / \lvert k \rvert$
(`NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`).
[Woodruff2014, Lemma 18] (there $\varepsilon^2 \lvert k \rvert / 16$); [MartinssonTropp2020, §8.6];
the exponent of Dasgupta and Gupta. No $\varepsilon < 1$: the bound
is at least $2$ for $\varepsilon \ge 3/2$.
Result: jl-distributional -/
theorem hasJLProperty_of_hasLaw_gaussianMatrix (hG : HasLaw G (gaussianMatrix k n) μ)
    (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  intro x hx
  have h := measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector
    (hasLaw_mulVec_of_hasLaw_gaussianMatrix hG hx) hε
  simp only [Matrix.smul_mulVec, EuclideanSpace.norm_toLp_inv_sqrt_card_smul_sq]
  exact h

/-- The squared distortion $(\|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2)^2$ of a Gaussian
sketch is integrable. -/
theorem integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix
    (hG : HasLaw G (gaussianMatrix k n) μ) (x : n → ℝ) :
    Integrable (fun ω => (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Matrix.mulVec_zero, smul_zero, WithLp.toLp_zero, norm_zero]
    exact integrable_const _
  obtain ⟨u, hu, hxu⟩ := exists_norm_eq_one_and_norm_mulVec_sq_sub_norm_sq_eq (k := k) hx
  obtain ⟨h1, h2⟩ := integrable_chiSq (hasLaw_mulVec_of_hasLaw_gaussianMatrix hG hu)
  simp only [sq_sketch_distortion_eq hxu]
  exact ((h2.const_mul _).sub (h1.const_mul _)).add (integrable_const _)

/-- The JL variance of a Gaussian sketch:
$\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2)^2 = 2 \|\mathbf{x}\|^4 / \lvert k \rvert$
exactly for $k$ nonempty, from $\operatorname{Var} \chi^2_{\lvert k \rvert} = 2 \lvert k \rvert$
(`NLAlib.integral_norm_sq_rpow_of_hasLaw_gaussianVector` at $s = 1, 2$). -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ = 2 / Fintype.card k * ‖WithLp.toLp 2 x‖ ^ 4 := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Matrix.mulVec_zero, smul_zero, WithLp.toLp_zero, norm_zero]
    simp
  obtain ⟨u, hu, hxu⟩ := exists_norm_eq_one_and_norm_mulVec_sq_sub_norm_sq_eq (k := k) hx
  have hGu := hasLaw_mulVec_of_hasLaw_gaussianMatrix hG hu
  obtain ⟨h1, h2⟩ := integrable_chiSq hGu
  obtain ⟨e1, e2⟩ := integral_chiSq hGu
  simp only [sq_sketch_distortion_eq hxu]
  set r := ‖WithLp.toLp 2 x‖
  have hA : Integrable (fun ω => r ^ 4 / Fintype.card k ^ 2 *
      (‖WithLp.toLp 2 (G ω *ᵥ u)‖ ^ 2) ^ 2) μ := h2.const_mul _
  have hB : Integrable (fun ω => 2 * r ^ 4 / Fintype.card k *
      ‖WithLp.toLp 2 (G ω *ᵥ u)‖ ^ 2) μ := h1.const_mul _
  have hAB : Integrable (fun ω => r ^ 4 / Fintype.card k ^ 2 *
      (‖WithLp.toLp 2 (G ω *ᵥ u)‖ ^ 2) ^ 2 - 2 * r ^ 4 / Fintype.card k *
      ‖WithLp.toLp 2 (G ω *ᵥ u)‖ ^ 2) μ := hA.sub hB
  rw [integral_add hAB (integrable_const _), integral_sub hA hB, integral_const_mul,
    integral_const_mul, e1, e2, integral_const, probReal_univ, one_smul]
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  field_simp
  ring

/-- **The JL moment property of a Gaussian sketch** at $p = 2$, for $k$ nonempty, with
$\delta = 2 / (\lvert k \rvert \varepsilon^2)$, from the exact variance.
[Woodruff2014, Definition 12], the property there; the input of approximate matrix multiplication
at $p = 2$. -/
theorem hasJLMoment_of_hasLaw_gaussianMatrix [Nonempty k] (hG : HasLaw G (gaussianMatrix k n) μ)
    (hε : 0 < ε) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε
      (2 / (Fintype.card k * ε ^ 2)) 2 μ := by
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have e (x : n → ℝ) (hx : ‖WithLp.toLp 2 x‖ = 1) :
      (fun ω => |‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 - 1| ^ (2 : ℝ)) =
      fun ω => (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 -
        ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 := by
    funext ω
    rw [hx, one_pow, Real.rpow_two, sq_abs]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Matrix.smul_mulVec]
    rw [e x hx]
    exact integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix hG x
  · simp only [Matrix.smul_mulVec]
    rw [e x hx, integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix hG x, hx,
      Real.rpow_two]
    apply le_of_eq
    field_simp

/-- **The JL moment property of a Gaussian sketch at every order**: for $k$ nonempty,
$\varepsilon > 0$, $p > 0$ and $\mathbf{S} = \lvert k\rvert^{-1/2}\mathbf{G}$ with $\mathbf{G}$
standard Gaussian, the JL moment property holds with exponent $p$ and failure
probability <!-- value subexponentialMomentBound {(4/\lvert k \rvert)} {(4/\lvert k \rvert)} p -->
$$\delta = \frac{p(2(4/\lvert k \rvert))^{p/2}\Gamma(p/2) +
2p(2(4/\lvert k \rvert))^{p}\Gamma(p)}{\varepsilon^p}\,,$$
the numerator being `NLAlib.subexponentialMomentBound` at $v = b = 4/\lvert k\rvert$: the
Dasgupta–Gupta $\chi^2$ tails on both sides give the sub-exponential JL tail
$2e^{-(\lvert k\rvert/8)\min(t^2, t)}$ at every $t > 0$
(`NLAlib.measureReal_abs_div_sub_one_ge_le_two_mul_exp`), and
`NLAlib.hasJLMoment_of_forall_hasJLProperty` integrates it. Incomparable with
`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix` (the exact variance, better at $p = 2$).
[Woodruff2014, Definition 12] for the property; that dense sketches have it at
$p = \log(1/\delta)$ follows from [KaneNelson2014, Remark 22]. -/
theorem hasJLMoment_subexponentialMomentBound_of_hasLaw_gaussianMatrix [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) {p : ℝ} (hp : 0 < p) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε
      (subexponentialMomentBound (4 / Fintype.card k) (4 / Fintype.card k) p / ε ^ p) p μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  refine hasJLMoment_of_forall_hasJLProperty
    (hG.aemeasurable.const_smul ((√(Fintype.card k : ℝ))⁻¹)) (by positivity) (by positivity)
    (fun t ht => ?_) hε hp
  intro x hx
  have hg := hasLaw_mulVec_of_hasLaw_gaussianMatrix hG hx
  have h := measureReal_abs_div_sub_one_ge_le_two_mul_exp
    (Y := fun ω => ‖WithLp.toLp 2 (G ω *ᵥ x)‖ ^ 2) hK hK.le
    (fun β hβ => measureReal_norm_sq_ge_mul_card_le_of_hasLaw_gaussianVector hg hβ)
    (fun β hβ0 hβ => measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector hg hβ0 hβ) ht.le
  simp only [Pi.smul_apply, Matrix.smul_mulVec, EuclideanSpace.norm_toLp_inv_sqrt_card_smul_sq]
  refine h.trans (le_of_eq ?_)
  have e1 : t ^ 2 / (2 * (4 / (Fintype.card k : ℝ))) = Fintype.card k / 8 * t ^ 2 := by
    field_simp
    ring
  have e2 : t / (2 * (4 / (Fintype.card k : ℝ))) = Fintype.card k / 8 * t := by
    field_simp
    ring
  rw [e1, e2, ← mul_min_of_nonneg _ _ (by positivity)]

/-! ### Sample-size corollaries -/

/-- **Gaussian OSE, sample-size form**: at
least <!-- value gaussianEmbeddingDim d \varepsilon \delta -->
$9 (\sqrt{d} + \sqrt{2 \log(2/\delta)})^2/\varepsilon^2$ rows (`gaussianEmbeddingDim d ε δ`) give
an oblivious subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$ and failure
probability $\delta$, for $0 < \varepsilon \le 1$ and $\delta > 0$ (for $\delta \ge 2$ it is
trivial). [Woodruff2014, Theorem 6].
Asymptotic form: `NLAlib.exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix`.
Result: gaussian-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le
    (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : gaussianEmbeddingDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d (1 - ε) (1 + ε) δ
      μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases le_or_gt 2 δ with hδ2 | hδ2
  · exact fun U _ => measureReal_le_one.trans (by linarith)
  have hL : 0 < Real.log (2 / δ) := Real.log_pos ((one_lt_div₀ hδ).2 hδ2)
  obtain ⟨t, ht0, hteq, htδ⟩ := exists_sqrt_two_mul_log
    (by rw [le_div_iff₀ hδ]; linarith : 1 ≤ 2 / δ)
  rw [gaussianEmbeddingDim_def, hteq] at hk
  have hδeq : 2 * Real.exp (-t ^ 2 / 2) = δ := by rw [htδ]; field_simp
  obtain ⟨hx0, hx, htd⟩ := div_sqrt_le_of_mul_sq_div_le (c := 3) (by norm_num) hε ht0
    (by linarith) (by rw [show (3 : ℝ) ^ 2 = 9 by norm_num]; exact hk)
  refine (isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix hG d ht0 htd).mono le_rfl ?_ ?_
    hδeq.le
  · nlinarith
  · nlinarith

/-- **Gaussian OSE, asymptotic form**: $O((d + \log(1/\delta))/\varepsilon^2)$ rows suffice for
the Gaussian sketch to be an oblivious subspace embedding for dimension $d$ with constants
$1 \mp \varepsilon$ and failure probability $\delta$, for $\varepsilon$ and $\delta$ below absolute
constants; the constants come before every dimension. Proved from
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le` with
$C = 72$, $\varepsilon_0 = 1$ and $\delta \le 1/2$. [Woodruff2014, Theorem 6].
Asymptotic: NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le
-/
theorem exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      (μ : Measure Ω) (G : Ω → Matrix k n ℝ) (d : ℕ) (ε δ : ℝ),
      HasLaw G (gaussianMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((d + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card k →
      IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d (1 - ε) (1 + ε) δ
        μ := by
  refine ⟨72, 1, by norm_num, one_pos, fun μ G d ε δ hG hε hε1 hδ hδ2 hk => ?_⟩
  have hl1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := Real.log_two_div_le_two_mul_log_one_div hδ hδ2
  refine isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le hG hε hε1
    hδ ((gaussianEmbeddingDim_le d ε hδ (by linarith)).trans (le_trans ?_ hk))
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) d]) (sq_nonneg ε)

/-- **Gaussian OSI, sample-size form**: at
least <!-- value gaussianInjectionDim d \varepsilon \delta -->
$4 (\sqrt{d} + \sqrt{2 \log(1/\delta)})^2/\varepsilon^2$ rows (`gaussianInjectionDim d ε δ`) give
an oblivious subspace injection for dimension $d$ with constant $1 - \varepsilon$ and failure
probability $\delta$, for $0 < \varepsilon \le 2$ and $0 < \delta < 1$; $k$ is nonempty because
the dimension is positive. [MartinssonTropp2020, §8.7.2] (the tail form: the smallest
singular value of the sketch on the subspace is at most
$1 - (1 + \sqrt{d})/\sqrt{\lvert k \rvert} - t$ with probability at most
$e^{-\lvert k \rvert t^2/2}$); here solved for the row count. Asymptotic form:
`NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`.
Result: gaussian-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    [DecidableEq n] (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hk : gaussianInjectionDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d (1 - ε) δ μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hk0 : 0 < Fintype.card k := by
    exact_mod_cast (gaussianInjectionDim_pos d hε.ne' hδ hδ1).trans_le hk
  have : Nonempty k := Fintype.card_pos_iff.1 hk0
  have hL : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div₀ hδ).2 hδ1)
  obtain ⟨t, ht0, hteq, htδ⟩ := exists_sqrt_two_mul_log
    (by rw [le_div_iff₀ hδ]; linarith : 1 ≤ 1 / δ)
  rw [gaussianInjectionDim_def, hteq] at hk
  have hδeq : Real.exp (-t ^ 2 / 2) = δ := by rw [htδ]; field_simp
  obtain ⟨hx0, hx, htd⟩ := div_sqrt_le_of_mul_sq_div_le (c := 2) (by norm_num) hε ht0
    hε2 (by rw [show (2 : ℝ) ^ 2 = 4 by norm_num]; exact hk)
  refine (isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix hG d ht0 htd).mono le_rfl ?_
    hδeq.le
  nlinarith

/-- Gaussian OSI, asymptotic form: $O((d + \log(1/\delta))/\varepsilon^2)$ rows suffice for
the Gaussian sketch to be an oblivious subspace injection for dimension $d$ with constant
$1 - \varepsilon$ and failure probability $\delta$, for $\varepsilon$ and $\delta$ below absolute
constants; the constants come before every dimension. Proved from
`NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le` with
$C = 16$, $\varepsilon_0 = 1$ and $\delta \le 1/2$.
Asymptotic: NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
-/
theorem exists_forall_isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      [DecidableEq n] (μ : Measure Ω) (G : Ω → Matrix k n ℝ) (d : ℕ) (ε δ : ℝ),
      HasLaw G (gaussianMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((d + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card k →
      IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d (1 - ε) δ μ := by
  refine ⟨16, 1, by norm_num, one_pos, fun μ G d ε δ hG hε hε1 hδ hδ2 hk => ?_⟩
  have hl1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  refine isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le hG hε
    (by linarith) hδ (by linarith)
    ((gaussianInjectionDim_le d ε hδ (by linarith)).trans (le_trans ?_ hk))
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) d]) (sq_nonneg ε)

/-- **Gaussian distributional JL, sample-size form**: at
least <!-- value jlDim \varepsilon \delta -->$\log(2/\delta)/(\varepsilon^2/4 - \varepsilon^3/6)$
rows (`jlDim ε δ`) give the JL property with distortion $\varepsilon$ and failure
probability $\delta$, for $0 < \varepsilon < 3/2$ and $\delta > 0$. [Woodruff2014, Theorem 4]
(there $\Omega(\varepsilon^{-2} \log(f/\delta))$ rows for $f$ points, unspecified constant,
proved in Lemma 18; here $f = 1$ with Dasgupta and Gupta's exponent). Asymptotic form:
`NLAlib.exists_forall_hasJLProperty_of_hasLaw_gaussianMatrix`.
Result: jl-distributional -/
theorem hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le (hG : HasLaw G (gaussianMatrix k n) μ)
    (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ) (hk : jlDim ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε δ μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  exact (hasJLProperty_of_hasLaw_gaussianMatrix hG hε.le).mono le_rfl
    (two_mul_exp_le_of_jlDim_le hε hε1 hδ hk)

/-- Gaussian distributional JL, asymptotic form: $O(\log(1/\delta)/\varepsilon^2)$ rows
suffice for the Gaussian sketch to have the JL property with distortion $\varepsilon$ and failure
probability $\delta$, for $\varepsilon$ and $\delta$ below absolute constants; the constants come
before every dimension. Proved from `NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le`
with $C = 24$, $\varepsilon_0 = 1$ and $\delta \le 1/2$.
Asymptotic: NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le -/
theorem exists_forall_hasJLProperty_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      (μ : Measure Ω) (G : Ω → Matrix k n ℝ) (ε δ : ℝ),
      HasLaw G (gaussianMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε δ μ := by
  refine ⟨24, 1, by norm_num, one_pos, fun μ G ε δ hG hε hε1 hδ hδ2 hk => ?_⟩
  have hl2 := Real.log_two_div_le_two_mul_log_one_div hδ hδ2
  refine hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le hG hε (by linarith) hδ
    ((jlDim_le hε1 hδ (by linarith)).trans (le_trans ?_ hk))
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg ε)

/-- **Gaussian JL moments, sample-size form**: for $0 < \varepsilon \le 1$, $\delta > 0$ and at
least <!-- value jlMomentDim \varepsilon \delta -->$128\max(2, \log(1/\delta))/\varepsilon^2$ rows
(`jlMomentDim ε δ`), $\mathbf{S} = \lvert k\rvert^{-1/2}\mathbf{G}$ with $\mathbf{G}$ standard
Gaussian has the JL moment property with distortion $\varepsilon$, failure probability $\delta$
and exponent
$$\max(2, \log(1/\delta)) \,:$$
the moment bound
`NLAlib.hasJLMoment_subexponentialMomentBound_of_hasLaw_gaussianMatrix` is at most
$\varepsilon^p e^{-p} \le \varepsilon^p \delta$ there. Approximate matrix multiplication with
failure probability $\delta$ follows
(`NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le`, whose side condition
$2 \le p$ is `le_max_left`). [Woodruff2014, Definition 12 and Theorem 13],
the property and AMM from it; the size $O(\log(1/\delta)/\varepsilon^2)$ follows from
[KaneNelson2014, Remark 22], the constants are this proof's. Asymptotic form:
`NLAlib.exists_forall_hasJLMoment_of_hasLaw_gaussianMatrix`.
Result: jl-moment-gaussian -/
theorem hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
    (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : jlMomentDim ε δ ≤ Fintype.card k) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε δ (max 2 (Real.log (1 / δ))) μ := by
  set p := max 2 (Real.log (1 / δ)) with hpdef
  have hp2 : 2 ≤ p := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hK : 128 * p ≤ ε ^ 2 * Fintype.card k := by
    rw [jlMomentDim_def, div_le_iff₀ hε2] at hk
    linarith
  have hK0 : (0 : ℝ) < Fintype.card k := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hε2.le h]
  have : Nonempty k := Fintype.card_pos_iff.1 (by exact_mod_cast hK0)
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hb := subexponentialMomentBound_le_mul_exp_neg (v := 4 / (Fintype.card k : ℝ))
    (b := 4 / (Fintype.card k : ℝ)) (by positivity) (by positivity) hp2 hε
    (by rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ hK0]; linarith)
    (by rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ hK0]; nlinarith)
  refine (hasJLMoment_subexponentialMomentBound_of_hasLaw_gaussianMatrix hG hε hp0).mono le_rfl
    ?_ hε.le hp0.le (div_nonneg (subexponentialMomentBound_nonneg (by positivity)
      (by positivity) hp0.le) hεp.le)
  rw [div_le_iff₀ hεp, mul_comm δ]
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hεp.le)
  calc Real.exp (-p) ≤ Real.exp (-Real.log (1 / δ)) :=
        Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]

/-- **Gaussian JL moments, asymptotic form**:
$$O(\log(1/\delta)/\varepsilon^2)$$
rows suffice for the Gaussian sketch
$\mathbf{S} = \lvert k\rvert^{-1/2}\mathbf{G}$ to have the JL moment property
with distortion $\varepsilon$, failure probability $\delta$ and exponent
$\max(2, \log(1/\delta))$, for $\varepsilon$ and $\delta$ below absolute constants; the constants
come before every dimension. Proved from
`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le` with $C = 384$,
$\varepsilon_0 = 1$ and $\delta \le 1/2$, where $\max(2, \log(1/\delta)) \le 3\log(1/\delta)$.
[Woodruff2014, Definition 12 and Theorem 13].
Asymptotic: NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
Result: jl-moment-gaussian -/
theorem exists_forall_hasJLMoment_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      (μ : Measure Ω) (G : Ω → Matrix k n ℝ) (ε δ : ℝ),
      HasLaw G (gaussianMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε δ (max 2 (Real.log (1 / δ))) μ := by
  refine ⟨384, 1, by norm_num, one_pos, fun μ G ε δ hG hε hε1 hδ hδ2 hk => ?_⟩
  refine hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le hG hε hε1 hδ
    ((jlMomentDim_le hδ hδ2).trans (le_of_eq_of_le ?_ hk))
  ring

/-- **The Johnson–Lindenstrauss lemma**, existence form: for points $\mathbf{x}_i$ in
$\mathbb{R}^n$, $N = \lvert \iota \rvert$, $\delta = 1/(\binom{N}{2} + 1)$
and <!-- value jlDim \varepsilon \delta -->
$\lvert k \rvert \ge \log(2/\delta)/(\varepsilon^2/4 - \varepsilon^3/6)$ (`jlDim` at distortion
$\varepsilon$ and failure probability $\delta$), some $k \times n$ matrix
$\mathbf{S}$ distorts every squared distance $\|\mathbf{x}_i - \mathbf{x}_j\|^2$ by a factor within
$1 \pm \varepsilon$, for $0 < \varepsilon < 3/2$. A scaled Gaussian works with positive probability
(the union bound over pairs, failure $< 1$). [Woodruff2014, Theorem 4], in squared-norm form;
[MartinssonTropp2020, §8.6].
Result: jl-lemma -/
theorem exists_forall_abs_norm_mulVec_sq_sub_le_of_jlDim_le [Fintype ι] (x : ι → n → ℝ)
    (hε : 0 < ε) (hε1 : ε < 3 / 2)
    (hk : jlDim ε (1 / (((Fintype.card ι).choose 2 : ℕ) + 1 : ℝ)) ≤ Fintype.card k) :
    ∃ S : Matrix k n ℝ, ∀ i j, |‖WithLp.toLp 2 (S *ᵥ (x i - x j))‖ ^ 2 -
      ‖WithLp.toLp 2 (x i - x j)‖ ^ 2| ≤ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2 := by
  have hδ : (0 : ℝ) < 1 / (((Fintype.card ι).choose 2 : ℕ) + 1 : ℝ) := by positivity
  have hJL := hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le
    (HasLaw.id (μ := gaussianMatrix k n)) hε hε1 hδ hk
  have hm := hJL.measureReal_exists_abs_norm_mulVec_sq_sub_ge_le hδ.le x
  by_contra hcon
  push Not at hcon
  have huniv : {ω : Matrix k n ℝ | ∃ i j, x i ≠ x j ∧ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2 ≤
      |‖WithLp.toLp 2 (((√(Fintype.card k : ℝ))⁻¹ • id ω) *ᵥ (x i - x j))‖ ^ 2 -
        ‖WithLp.toLp 2 (x i - x j)‖ ^ 2|} = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    obtain ⟨i, j, hij⟩ := hcon ((√(Fintype.card k : ℝ))⁻¹ • ω)
    refine ⟨i, j, fun h => ?_, hij.le⟩
    rw [h, sub_self] at hij
    simp at hij
  rw [huniv, probReal_univ, mul_one_div, le_div_iff₀ (by positivity)] at hm
  linarith

end NLAlib
