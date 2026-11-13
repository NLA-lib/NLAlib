/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.QuadraticForm.Moments
public import NLAlib.RandomMatrix.Rademacher.Basic
public import NLAlib.Sketching.Gaussian.Gaussian
public import NLAlib.Sketching.Gaussian.SubGaussian

/-!
# Rademacher sketches

The sign sketch is $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ for a random
`X : Matrix k n ℝ` with independent random signs, `HasLaw X (rademacherMatrix k n) μ`, where
`rademacherMatrix k n` (in `NLAlib.RandomMatrix.Rademacher.Basic`) is the law of independent
rows, each a `rademacherVector n`. It is written out in each statement,
`fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω`, as for the Gaussian sketch.

It is an isotropic sketch, has the distributional Johnson–Lindenstrauss property with the
Gaussian sketch's exponent $\varepsilon^2/4 - \varepsilon^3/6$ (Dasgupta and Gupta's; Achlioptas's
argument, through `NLAlib.hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le`, since
$\mathbb{E} \langle \boldsymbol{\xi}, \mathbf{x} \rangle^4
= 3 \|\mathbf{x}\|^4 - 2 \sum_j \mathbf{x}_j^4 \le 3 \|\mathbf{x}\|^4$ for a vector
$\boldsymbol{\xi}$ of random signs), the exact JL second moment
$2 (\|\mathbf{x}\|^4 - \sum_j \mathbf{x}_j^4)/\lvert k \rvert$, at most the Gaussian's
$2 \|\mathbf{x}\|^4/\lvert k \rvert$, and is an oblivious subspace embedding and injection
through JL plus a net of radius $1/10$ at $4\varepsilon/5$. The sample sizes are the Gaussian
sketch's
`NLAlib.jlDim`: <!-- value jlDim \varepsilon \delta -->
$\log(2/\delta)/(\varepsilon^2/4 - \varepsilon^3/6)$ rows (`jlDim ε δ`) for JL,
and <!-- value jlDim (4\varepsilon/5) (\delta/21^d) -->
$\log(2/(\delta/21^d))/((4\varepsilon/5)^2/4 - (4\varepsilon/5)^3/6)$ rows
(`jlDim (4ε/5) (δ/21^d)`) for the OSE and OSI. For
$\varepsilon \gtrsim 1.43$ the sub-Gaussian rows theorem at $c = 1$
(`NLAlib.hasJLProperty_of_isSubgaussianVector` with
`NLAlib.isSubgaussianVector_of_hasLaw_rademacherVector`) is better; it is not restated here.

**JL moments beyond $p = 2$.** The sub-Gaussian family's JL moment at $p = \max(2,
\log(1/\delta))$ applies at proxy $1$, with no separate statement: for
`hX : HasLaw X (rademacherMatrix k n) μ`,
```
hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le hX.iIndepFun_eval
  (fun i => isSubgaussianVector_of_hasLaw_rademacherVector (hX.eval i))
  (fun i => isIsotropic_of_hasLaw_rademacherVector (hX.eval i)) hε hε1 hδ hk
```
at least <!-- value subgaussianJLMomentDim {\cdot 1} \varepsilon \delta -->
$16\cdot 1^2\max(2, \log(1/\delta))/(C\varepsilon^2)$ rows,
with <!-- value subgaussianJLConstant -->$C = 1/36$, for $0 < \varepsilon \le 1$;
approximate matrix multiplication with failure probability $\delta$ follows by
`NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le`.

Degenerate cases: for empty $k$, $\mathbf{S} = \mathbf{0}$, which is not isotropic, hence
`[Nonempty k]` on isotropy, the OSI and the moments; the JL bound is $2$ for
$\lvert k \rvert = 0$ and at least $2$ for $\varepsilon \ge 3/2$. For $\varepsilon = 1$ the lower
JL event $\{\mathbf{S}\mathbf{x} = \mathbf{0}\}$ has positive probability ($2^{-\lvert k \rvert}$
at $\mathbf{x} = (\mathbf{e}_1 + \mathbf{e}_2)/\sqrt{2}$), and the proof covers it.

## Main results

* `NLAlib.isIsotropicSketch_of_hasLaw_rademacherMatrix`.
* `NLAlib.hasJLProperty_of_hasLaw_rademacherMatrix`: distributional JL.
* `NLAlib.integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix`: the exact second
  moment of the distortion.
* `NLAlib.hasJLMoment_of_hasLaw_rademacherMatrix`: the JL moment property at $p = 2$.
* `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix`,
  `NLAlib.isObliviousSubspaceInjection_of_hasLaw_rademacherMatrix`.
* `NLAlib.exists_forall_hasJLProperty_of_hasLaw_rademacherMatrix`,
  `NLAlib.exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix`: the asymptotic
  forms of the sample sizes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n : Type*} [Fintype k]
  [Fintype n] {X : Ω → Matrix k n ℝ} {ε δ : ℝ} {d : ℕ}

/-! ### Proof-local facts -/

/-- The moments of $Q = \langle \mathbf{x}, \boldsymbol{\xi} \rangle^2$ for a vector
$\boldsymbol{\xi}$ of random signs: $Q \in L^2$, $\mathbb{E} Q = \|\mathbf{x}\|^2$ and
$\operatorname{Var} Q = 2 (\|\mathbf{x}\|^4 - \sum_j \mathbf{x}_j^4)$
(`NLAlib.variance_quadForm_of_hasLaw_rademacherVector` at `vecMulVec x x`). -/
private theorem moments_dotProduct_sq {ξ : Ω → n → ℝ} (hξ : HasLaw ξ (rademacherVector n) μ)
    (x : n → ℝ) :
    MemLp (fun ω => (x ⬝ᵥ ξ ω) ^ 2) 2 μ ∧ ∫ ω, (x ⬝ᵥ ξ ω) ^ 2 ∂μ = ‖WithLp.toLp 2 x‖ ^ 2 ∧
      variance (fun ω => (x ⬝ᵥ ξ ω) ^ 2) μ = 2 * (‖WithLp.toLp 2 x‖ ^ 4 - ∑ j, x j ^ 4) := by
  classical
  have hq : ∀ z : n → ℝ, quadForm (Matrix.vecMulVec x x) z = (x ⬝ᵥ z) ^ 2 := by
    intro z
    have h := quadForm_vecMulVec_star x z
    rw [star_trivial, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs, sq_abs] at h
    exact h
  have hA : (Matrix.vecMulVec x x).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_vecMulVec]
  have hmem := memLp_quadForm (memLp_of_hasLaw_rademacherVector hξ 4) (Matrix.vecMulVec x x)
  have hvar := variance_quadForm_of_hasLaw_rademacherVector hξ hA
  simp only [hq] at hmem hvar
  refine ⟨hmem, ?_, ?_⟩
  · have h := (isIsotropic_of_hasLaw_rademacherVector hξ).integral_norm_dotProduct_sq x
    simpa only [Real.norm_eq_abs, sq_abs] using h
  · have e : ∑ i, Matrix.vecMulVec x x i i ^ 2 = ∑ j, x j ^ 4 :=
      Finset.sum_congr rfl fun j _ => by rw [Matrix.vecMulVec_apply]; ring
    rw [hvar, frobNorm_vecMulVec, e]
    ring

/-- The fourth moment of a Rademacher combination:
$\mathbb{E} \langle \mathbf{x}, \boldsymbol{\xi} \rangle^4
= 3 \|\mathbf{x}\|^4 - 2 \sum_j \mathbf{x}_j^4$. -/
private theorem integral_dotProduct_pow_four {ξ : Ω → n → ℝ}
    (hξ : HasLaw ξ (rademacherVector n) μ) (x : n → ℝ) :
    ∫ ω, (x ⬝ᵥ ξ ω) ^ 4 ∂μ = 3 * ‖WithLp.toLp 2 x‖ ^ 4 - 2 * ∑ j, x j ^ 4 := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hmem, hmean, hvar⟩ := moments_dotProduct_sq hξ x
  rw [variance_eq_sub hmem, hmean] at hvar
  have e : ∫ ω, ((fun ω => (x ⬝ᵥ ξ ω) ^ 2) ^ 2) ω ∂μ = ∫ ω, (x ⬝ᵥ ξ ω) ^ 4 ∂μ := by
    congr 1
    ext ω
    simp only [Pi.pow_apply]
    ring
  rw [e] at hvar
  linarith

/-- **The sign sketch is isotropic**: $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$
for $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$, $k$ nonempty, from the isotropy of each
row (`NLAlib.isIsotropic_of_hasLaw_rademacherVector`). [CamanoEpperlyMeyerTropp2025, Definition
1.2] for the notion. -/
theorem isIsotropicSketch_of_hasLaw_rademacherMatrix [DecidableEq n] [Nonempty k]
    (hX : HasLaw X (rademacherMatrix k n) μ) :
    IsIsotropicSketch (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) μ := by
  exact isIsotropicSketch_smul_of_isIsotropic fun i =>
    isIsotropic_of_hasLaw_rademacherVector (hX.eval i)

/-- **Sign-sketch distributional JL** with Gaussian constants: for every unit $\mathbf{x}$ and
every $\varepsilon \ge 0$,
$$\mathbb{P}\bigl[\varepsilon \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert\bigr]
\le 2 e^{-\lvert k \rvert (\varepsilon^2/4 - \varepsilon^3/6)} \,,$$
the bound of `NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix`. From
`NLAlib.hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le`, with
$\mathbb{E} \langle \boldsymbol{\xi}, \mathbf{x} \rangle^4
= \operatorname{Var}(\langle \boldsymbol{\xi}, \mathbf{x} \rangle^2) + \|\mathbf{x}\|^4
= 3 \|\mathbf{x}\|^4 - 2 \sum_j \mathbf{x}_j^4$
(`NLAlib.variance_quadForm_of_hasLaw_rademacherVector` at `vecMulVec x x`).
[Woodruff2014, §2.1, after Theorem 6]; constants of [Achlioptas2003, Lemma 5.1].
For $\varepsilon \gtrsim 1.43$,
`NLAlib.hasJLProperty_of_isSubgaussianVector` at $c = 1$ is better.
Result: jl-rademacher -/
theorem hasJLProperty_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix k n) μ)
    (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  classical
  refine hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le hX.iIndepFun_eval
    (fun i => isSubgaussianVector_of_hasLaw_rademacherVector (hX.eval i))
    (fun i => isIsotropic_of_hasLaw_rademacherVector (hX.eval i)) (fun i x => ?_) hε
  rw [integral_dotProduct_pow_four (hX.eval i) x]
  have : 0 ≤ ∑ j, x j ^ 4 := Finset.sum_nonneg fun j _ => by positivity
  linarith

/-- The squared distortion $(\|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2)^2$ of the sign sketch
is integrable. -/
theorem integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix
    (hX : HasLaw X (rademacherMatrix k n) μ) (x : n → ℝ) :
    Integrable (fun ω => (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) μ := by
  have := hX.isProbabilityMeasure
  have hT : MemLp (fun ω => ∑ i, (x ⬝ᵥ X ω i) ^ 2) 2 μ :=
    memLp_finsetSum _ fun i _ => (moments_dotProduct_sq (hX.eval i) x).1
  have h := ((hT.const_mul (Fintype.card k : ℝ)⁻¹).sub
    (memLp_const (‖WithLp.toLp 2 x‖ ^ 2))).integrable_sq
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.sub_apply, ← Matrix.smul_mulVec, norm_inv_sqrt_card_smul_mulVec_sq,
    Real.norm_eq_abs, sq_abs, div_eq_inv_mul]

/-- Exact second moment of the sign-sketch distortion: for $k$ nonempty,
$$\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2)^2
= \frac{2}{\lvert k \rvert} \Bigl(\|\mathbf{x}\|^4 - \sum_j \mathbf{x}_j^4\Bigr) \,,$$
at most the Gaussian sketch's $2 \|\mathbf{x}\|^4/\lvert k \rvert$
(`NLAlib.integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix`). By independence of
the rows and `NLAlib.variance_quadForm_of_hasLaw_rademacherVector` at `vecMulVec x x`
($\|\mathbf{x}\mathbf{x}^{\mathsf{T}}\|_{\mathsf{F}}^2 = \|\mathbf{x}\|^4$). -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix [Nonempty k]
    (hX : HasLaw X (rademacherMatrix k n) μ) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ =
        2 / Fintype.card k * (‖WithLp.toLp 2 x‖ ^ 4 - ∑ j, x j ^ 4) := by
  have := hX.isProbabilityMeasure
  have hN0 : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hmom := fun i => moments_dotProduct_sq (hX.eval i) x
  have hind : iIndepFun (fun i ω => (x ⬝ᵥ X ω i) ^ 2) μ :=
    hX.iIndepFun_eval.comp (fun _ y => (x ⬝ᵥ y) ^ 2) fun _ => by fun_prop
  have hTvar : variance (∑ i, fun ω => (x ⬝ᵥ X ω i) ^ 2) μ =
      ∑ i, variance (fun ω => (x ⬝ᵥ X ω i) ^ 2) μ :=
    IndepFun.variance_sum (fun i _ => (hmom i).1) fun i _ j _ hij => hind.indepFun hij
  have hsumfun : (∑ i, fun ω => (x ⬝ᵥ X ω i) ^ 2) = fun ω => ∑ i, (x ⬝ᵥ X ω i) ^ 2 := by
    ext ω
    rw [Finset.sum_apply]
  have hT : MemLp (fun ω => ∑ i, (x ⬝ᵥ X ω i) ^ 2) 2 μ :=
    memLp_finsetSum _ fun i _ => (hmom i).1
  have hTmean : ∫ ω, ∑ i, (x ⬝ᵥ X ω i) ^ 2 ∂μ =
      Fintype.card k * ‖WithLp.toLp 2 x‖ ^ 2 := by
    rw [integral_finsetSum _ fun i _ => (hmom i).1.integrable one_le_two]
    simp only [fun i => (hmom i).2.1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsumfun, variance_eq_integral hT.aestronglyMeasurable.aemeasurable, hTmean] at hTvar
  simp only [fun i => (hmom i).2.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hTvar
  have e : ∀ ω, (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • (X ω *ᵥ x))‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 = (∑ i, (x ⬝ᵥ X ω i) ^ 2 -
        Fintype.card k * ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 / (Fintype.card k : ℝ) ^ 2 := by
    intro ω
    rw [← Matrix.smul_mulVec, norm_inv_sqrt_card_smul_mulVec_sq]
    simp only [Real.norm_eq_abs, sq_abs]
    field_simp
  simp only [e]
  rw [integral_div, hTvar]
  field_simp

/-- **Sign-sketch JL moment** at $p = 2$, with $\delta = 2/(\lvert k \rvert \varepsilon^2)$ for
$\varepsilon > 0$ and $k$ nonempty, the Gaussian sketch's
(`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix`). [Woodruff2014, Definition 12] for the
property. -/
theorem hasJLMoment_of_hasLaw_rademacherMatrix [Nonempty k] (hX : HasLaw X (rademacherMatrix k n) μ)
    (hε : 0 < ε) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 / (Fintype.card k * ε ^ 2)) 2 μ := by
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have e (x : n → ℝ) (hx : ‖WithLp.toLp 2 x‖ = 1) :
      (fun ω => |‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ x)‖ ^ 2 - 1| ^ (2 : ℝ)) =
      fun ω => (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ x)‖ ^ 2 -
        ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 := by
    funext ω
    rw [hx, one_pow, Real.rpow_two, sq_abs]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Matrix.smul_mulVec]
    rw [e x hx]
    exact integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix hX x
  · simp only [Matrix.smul_mulVec]
    rw [e x hx, integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix hX x, hx,
      one_pow, Real.rpow_two]
    have hs : 0 ≤ ∑ j, x j ^ 4 := Finset.sum_nonneg fun j _ => by positivity
    have h2k : 0 < 2 / (Fintype.card k : ℝ) := by positivity
    calc 2 / (Fintype.card k : ℝ) * (1 - ∑ j, x j ^ 4) ≤ 2 / Fintype.card k := by nlinarith
      _ = ε ^ 2 * (2 / (Fintype.card k * ε ^ 2)) := by field_simp

/-- **Sign-sketch OSE**: for $\varepsilon \ge 0$,
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ is an oblivious subspace embedding for
dimension $d$ with constants $1 \mp \varepsilon$ and failure probability
$$2 \cdot 21^d e^{-\lvert k \rvert (4\varepsilon^2/25 - 32\varepsilon^3/375)} \,:$$
JL plus a net of
radius $1/10$ at $4\varepsilon/5$ (`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`).
[Woodruff2014, §2.1, Theorem 6], there with $O(\varepsilon)$ and unspecified constants.
Result: rademacher-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix
    (hX : HasLaw X (rademacherMatrix k n) μ) (d : ℕ) (hε : 0 ≤ ε) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε)
      (2 * 21 ^ d * Real.exp (-(Fintype.card k * (4 * ε ^ 2 / 25 - 32 * ε ^ 3 / 375)))) μ := by
  have := hX.isProbabilityMeasure
  have h := (hasJLProperty_of_hasLaw_rademacherMatrix hX (ε := 4 * ε / 5) (by linarith))
    |>.isObliviousSubspaceEmbedding (by positivity) d
  rw [Module.finrank_self, mul_one] at h
  refine h.mono le_rfl (by linarith) (by linarith) (le_of_eq ?_)
  rw [show (4 * ε / 5) ^ 2 / 4 - (4 * ε / 5) ^ 3 / 6 = 4 * ε ^ 2 / 25 - 32 * ε ^ 3 / 375 by ring]
  ring

/-- **Sign-sketch OSI**: for $\varepsilon \ge 0$ and $k$ nonempty, $\mathbf{S}$ is an oblivious
subspace injection for dimension $d$ with constant $1 - \varepsilon$ and failure probability
$2 \cdot 21^d e^{-\lvert k \rvert (4\varepsilon^2/25 - 32\varepsilon^3/375)}$: the lower half of
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix`, with the sketch's isotropy.
[CamanoEpperlyMeyerTropp2025, Definition 1.2] for the notion. -/
theorem isObliviousSubspaceInjection_of_hasLaw_rademacherMatrix [DecidableEq n] [Nonempty k]
    (hX : HasLaw X (rademacherMatrix k n) μ) (d : ℕ) (hε : 0 ≤ ε) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε)
      (2 * 21 ^ d * Real.exp (-(Fintype.card k * (4 * ε ^ 2 / 25 - 32 * ε ^ 3 / 375)))) μ := by
  have := hX.isProbabilityMeasure
  exact (isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix hX d hε)
    |>.isObliviousSubspaceInjection (isIsotropicSketch_of_hasLaw_rademacherMatrix hX)

/-- **Sign-sketch JL, sample-size form**: for $0 < \varepsilon < 3/2$, $\delta > 0$ and at
least <!-- value jlDim \varepsilon \delta -->$\log(2/\delta)/(\varepsilon^2/4 - \varepsilon^3/6)$
rows (`jlDim ε δ`), the JL property holds with distortion $\varepsilon$ and failure probability
$\delta$; the Gaussian sketch's size (`NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le`).
[Woodruff2014, §2.1, after Theorem 6] (Achlioptas's sign entries in Theorem 4, there
$\Omega(\varepsilon^{-2} \log(f/\delta))$ rows for $f$ points, unspecified constant). Asymptotic
form: `NLAlib.exists_forall_hasJLProperty_of_hasLaw_rademacherMatrix`.
Result: jl-rademacher -/
theorem hasJLProperty_of_hasLaw_rademacherMatrix_of_jlDim_le
    (hX : HasLaw X (rademacherMatrix k n) μ) (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ)
    (hk : jlDim ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε δ μ := by
  have := hX.isProbabilityMeasure
  exact (hasJLProperty_of_hasLaw_rademacherMatrix hX hε.le).mono le_rfl
    (two_mul_exp_le_of_jlDim_le hε hε1 hδ hk)

/-- Sign-sketch JL, asymptotic form: $O(\log(1/\delta)/\varepsilon^2)$ rows suffice for the
sign sketch to have the JL property with distortion $\varepsilon$ and failure probability
$\delta$, for $\varepsilon$ and $\delta$ below absolute constants; the constants come before every
dimension. Proved from `NLAlib.hasJLProperty_of_hasLaw_rademacherMatrix_of_jlDim_le` with
$C = 24$, $\varepsilon_0 = 1$ and $\delta \le 1/2$.
Asymptotic: NLAlib.hasJLProperty_of_hasLaw_rademacherMatrix_of_jlDim_le -/
theorem exists_forall_hasJLProperty_of_hasLaw_rademacherMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      (μ : Measure Ω) (X : Ω → Matrix k n ℝ) (ε δ : ℝ),
      HasLaw X (rademacherMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε δ μ := by
  refine ⟨24, 1, by norm_num, one_pos, fun μ X ε δ hX hε hε1 hδ hδ2 hk => ?_⟩
  have hl2 := Real.log_two_div_le_two_mul_log_one_div hδ hδ2
  refine hasJLProperty_of_hasLaw_rademacherMatrix_of_jlDim_le hX hε (by linarith) hδ
    ((jlDim_le hε1 hδ (by linarith)).trans (le_trans ?_ hk))
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg ε)

/-- **Sign-sketch OSE, sample-size form**: for $0 < \varepsilon < 15/8$, $\delta > 0$ and at
least <!-- value jlDim (4\varepsilon/5) (\delta/21^d) -->
$\log(2/(\delta/21^d))/((4\varepsilon/5)^2/4 - (4\varepsilon/5)^3/6)$ rows
(`jlDim (4ε/5) (δ/21^d)`),
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ is an oblivious
subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$ and failure probability
$\delta$. [Woodruff2014, Theorem 6] (Gaussian entries,
$\Theta((d + \log(1/\delta))\varepsilon^{-2})$ rows, unspecified constants; sign entries by the
same net argument, §2.1 after Theorem 6). Asymptotic form:
`NLAlib.exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix`.
Result: rademacher-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le
    (hX : HasLaw X (rademacherMatrix k n) μ) (hε : 0 < ε) (hε3 : ε < 15 / 8) (hδ : 0 < δ)
    (hk : jlDim (4 * ε / 5) (δ / 21 ^ d) ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε) δ
      μ := by
  have := hX.isProbabilityMeasure
  refine (isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix hX d hε.le).mono le_rfl
    le_rfl le_rfl (two_mul_twentyOne_pow_mul_exp_le_of_jlDim_le hε hε3 hδ hk)

/-- Sign-sketch OSE, asymptotic form: $O((d + \log(1/\delta))/\varepsilon^2)$ rows suffice
for the sign sketch to be an oblivious subspace embedding for dimension $d$ with constants
$1 \mp \varepsilon$ and failure probability $\delta$, for $\varepsilon$ and $\delta$ below absolute
constants; the constants come before every dimension. Proved from
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le` with $C = 58$,
$\varepsilon_0 = 1$ and $\delta \le 1/2$.
Asymptotic: NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le -/
theorem exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      (μ : Measure Ω) (X : Ω → Matrix k n ℝ) (d : ℕ) (ε δ : ℝ),
      HasLaw X (rademacherMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((d + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card k →
      IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε) δ
        μ := by
  refine ⟨58, 1, by norm_num, one_pos, fun μ X d ε δ hX hε hε1 hδ hδ2 hk => ?_⟩
  have h21 : (1 : ℝ) ≤ 21 ^ d := one_le_pow₀ (by norm_num)
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have hl : Real.log (2 / (δ / 21 ^ d)) = Real.log 2 + d * Real.log 21 + Real.log (1 / δ) := by
    rw [show 2 / (δ / 21 ^ d) = 2 * 21 ^ d * (1 / δ) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
  have hd21 : (d : ℝ) * Real.log 21 ≤ d * (61 / 20) :=
    mul_le_mul_of_nonneg_left Real.log_twentyOne_le_sixtyOne_div_twenty (Nat.cast_nonneg d)
  refine isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le hX hε (by linarith) hδ
    ((jlDim_le (by linarith) (by positivity)
      ((div_le_self hδ.le h21).trans (by linarith))).trans (le_trans ?_ hk))
  have e : 12 * Real.log (2 / (δ / 21 ^ d)) / (4 * ε / 5) ^ 2 =
      75 / 4 * Real.log (2 / (δ / 21 ^ d)) / ε ^ 2 := by
    field_simp
    ring
  rw [e, hl, mul_div_assoc']
  exact div_le_div_of_nonneg_right
    (by nlinarith [Nat.cast_nonneg (α := ℝ) d, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
    (sq_nonneg ε)

/-- Sign-sketch OSI, sample-size form: for $0 < \varepsilon < 15/8$, $\delta > 0$, $k$
nonempty and at least <!-- value jlDim (4\varepsilon/5) (\delta/21^d) -->
$\log(2/(\delta/21^d))/((4\varepsilon/5)^2/4 - (4\varepsilon/5)^3/6)$ rows
(`jlDim (4ε/5) (δ/21^d)`),
$\mathbf{S}$ is an oblivious subspace injection for
dimension $d$ with constant $1 - \varepsilon$ and failure probability $\delta$; the injection twin
of `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le`. -/
theorem isObliviousSubspaceInjection_of_hasLaw_rademacherMatrix_of_jlDim_le [DecidableEq n]
    [Nonempty k] (hX : HasLaw X (rademacherMatrix k n) μ) (hε : 0 < ε) (hε3 : ε < 15 / 8)
    (hδ : 0 < δ) (hk : jlDim (4 * ε / 5) (δ / 21 ^ d) ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) δ μ := by
  have := hX.isProbabilityMeasure
  exact (isObliviousSubspaceInjection_of_hasLaw_rademacherMatrix hX d hε.le).mono le_rfl le_rfl
    (two_mul_twentyOne_pow_mul_exp_le_of_jlDim_le hε hε3 hδ hk)

end NLAlib
