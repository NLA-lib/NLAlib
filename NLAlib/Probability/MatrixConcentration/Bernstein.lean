/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Algebra.Order.Field.Basic
public import NLAlib.ForMathlib.Analysis.Real.Sqrt
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.ExpDeriv
public import NLAlib.ForMathlib.Data.Matrix.Block
public import NLAlib.Matrix.Spectral.Dilation
public import NLAlib.Probability.MatrixConcentration.MGFBound

/-!
# The matrix Bernstein inequality

For independent centred random Hermitian $d \times d$ matrices with
$\mathbf{X}_k \preceq L\mathbf{I}$ almost surely and variance
$v = \|\sum_k \mathbb{E}\mathbf{X}_k^2\|_2$,
$$\mathbb{P}\Bigl[\lambda_{\max}\Bigl(\sum_k \mathbf{X}_k\Bigr) \ge t\Bigr]
\le d \exp\Bigl(\frac{-t^2/2}{v + L t / 3}\Bigr)$$
and
$$\mathbb{E}\, \lambda_{\max}\Bigl(\sum_k \mathbf{X}_k\Bigr)
\le \sqrt{2 v \log d} + \frac{L \log d}{3}$$
(Tropp 2015, Theorem 6.6.1). Rectangular summands go through the dilation, with $v$ the larger of
the two variances and dimension $\lvert m\rvert + \lvert n\rvert$ (Tropp 2015, Theorem 6.1.1); for
square Hermitian summands this is also the two-sided Hermitian form. The $1 \times 1$ case is
Bernstein's inequality for bounded centred real variables.

## Main results

* `NLAlib.hasMatrixMGFBound_of_integral_eq_zero_of_le`: the Bernstein matrix MGF bound.
* `NLAlib.measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le`,
  `NLAlib.integral_eigenvalue_zero_le_bernstein_of_integral_le`: the tail and the mean from a
  trace bound, for sums that are not independent (sampling without replacement).
* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein`,
  `NLAlib.integral_eigenvalue_zero_sum_le_bernstein`: Hermitian summands.
* `NLAlib.measureReal_specNorm_sum_ge_le_bernstein`, `NLAlib.integral_specNorm_sum_le_bernstein`:
  rectangular summands.
* `NLAlib.measureReal_sum_ge_le_bernstein`: the scalar Bernstein inequality.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {L : ℝ}

/-! ### Scalar inequalities -/

/-- The Bernstein mean optimisation: if $x \le \theta^{-1} (a + g(\theta) v)$ on $(0, 3/L)$, then
$x \le \sqrt{2 v a} + L a / 3$ (substitute $\theta = u / (1 + L u / 3)$). -/
private theorem le_of_forall_bernstein_mean {x a v L : ℝ} (hL : 0 < L) (ha : 0 ≤ a)
    (hv : 0 ≤ v) (h : ∀ θ ∈ Set.Ioo 0 (3 / L),
      x ≤ θ⁻¹ * (a + θ ^ 2 / 2 / (1 - L * θ / 3) * v)) :
    x ≤ √(2 * v * a) + L * a / 3 := by
  have key : x - L * a / 3 ≤ √(4 * a * (v / 2)) := by
    refine Real.le_sqrt_of_forall_le_div_add_mul ha (by positivity) fun u hu => ?_
    have hw : 0 < 1 + L * u / 3 := by positivity
    have hθ : u / (1 + L * u / 3) ∈ Set.Ioo 0 (3 / L) := by
      refine ⟨div_pos hu hw, ?_⟩
      rw [div_lt_div_iff₀ hw hL]
      nlinarith
    have h1 := h _ hθ
    have hq : 1 - L * (u / (1 + L * u / 3)) / 3 = 1 / (1 + L * u / 3) := by
      field_simp
      ring
    rw [hq] at h1
    have he : (u / (1 + L * u / 3))⁻¹ *
        (a + (u / (1 + L * u / 3)) ^ 2 / 2 / (1 / (1 + L * u / 3)) * v) =
        a / u + v / 2 * u + L * a / 3 := by
      field_simp
      ring
    linarith
  have h2 : 4 * a * (v / 2) = 2 * v * a := by ring
  rw [h2] at key
  linarith

/-! ### Integrability, the dilation and $1 \times 1$ matrices -/

/-- A square-integrable random matrix times its conjugate transpose is integrable. -/
private theorem integrable_mul_conjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    {S : Ω → Matrix m n 𝕜} (hS : MemLp S 2 μ) : Integrable (fun ω => S ω * (S ω)ᴴ) μ := by
  refine (hS.integrable_norm_pow two_ne_zero).mono'
    ((continuous_id.matrix_mul continuous_id.matrix_conjTranspose).comp_aestronglyMeasurable
      hS.1) (ae_of_all _ fun ω => ?_)
  rw [← specNorm_eq_norm, ← specNorm_eq_norm, specNorm_mul_conjTranspose_self]

/-- A square-integrable random matrix times its conjugate transpose on the left is
integrable. -/
private theorem integrable_conjTranspose_mul {m : Type*} [Fintype m]
    {S : Ω → Matrix m n 𝕜} (hS : MemLp S 2 μ) : Integrable (fun ω => (S ω)ᴴ * S ω) μ := by
  refine (hS.integrable_norm_pow two_ne_zero).mono'
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).comp_aestronglyMeasurable
      hS.1) (ae_of_all _ fun ω => ?_)
  rw [← specNorm_eq_norm, ← specNorm_eq_norm, specNorm_conjTranspose_mul_self]

/-- The dilation of a random matrix in $L^p$ is in $L^p$. -/
theorem memLp_dilation {m : Type*} [Fintype m] [DecidableEq m] {p : ENNReal} {S : Ω → Matrix m n 𝕜}
    (hS : MemLp S p μ) : MemLp (fun ω => dilation (S ω)) p μ :=
  (dilationCLM (𝕜 := 𝕜) (n := n) m).comp_memLp' hS

omit [Fintype n] [DecidableEq n] in
/-- The dilations of independent random matrices are independent. -/
theorem iIndepFun_dilation {ι m : Type*} [Finite m] [Finite n] {S : ι → Ω → Matrix m n 𝕜}
    (hind : iIndepFun S μ) : iIndepFun (fun k ω => dilation (S k ω)) μ := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  exact hind.comp (fun _ A => dilation A) fun _ => (dilationCLM m).continuous.measurable

/-- The integral of the dilation of an integrable random matrix is the dilation of its
integral. -/
theorem integral_dilation {m : Type*} [Fintype m] [DecidableEq m] {S : Ω → Matrix m n 𝕜}
    (hS : Integrable S μ) : ∫ ω, dilation (S ω) ∂μ = dilation (∫ ω, S ω ∂μ) :=
  (dilationCLM m).integral_comp_comm hS

/-- The dilation of a centred integrable random matrix is centred. -/
theorem integral_dilation_eq_zero {m : Type*} [Fintype m] [DecidableEq m] {S : Ω → Matrix m n 𝕜}
    (hS : Integrable S μ) (h0 : ∫ ω, S ω ∂μ = 0) : ∫ ω, dilation (S ω) ∂μ = 0 := by
  rw [integral_dilation hS, h0, dilation_zero]

/-- The integral of the square of a dilation is block diagonal: for a square-integrable
$\mathbf{S}$,
$$\mathbb{E} \begin{bmatrix} \mathbf{0} & \mathbf{S} \\ \mathbf{S}^{\mathsf{H}} & \mathbf{0}
\end{bmatrix}^2 = \begin{bmatrix} \mathbb{E}\mathbf{S}\mathbf{S}^{\mathsf{H}} & \mathbf{0} \\
\mathbf{0} & \mathbb{E}\mathbf{S}^{\mathsf{H}}\mathbf{S} \end{bmatrix}\,.$$ -/
theorem integral_dilation_sq {m : Type*} [Fintype m] [DecidableEq m]
    {S : Ω → Matrix m n 𝕜} (hS : MemLp S 2 μ) :
    ∫ ω, dilation (S ω) ^ 2 ∂μ =
      Matrix.fromBlocks (∫ ω, S ω * (S ω)ᴴ ∂μ) 0 0 (∫ ω, (S ω)ᴴ * S ω ∂μ) := by
  let B : Matrix m m 𝕜 × Matrix n n 𝕜 →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
        map_add' := fun p q => by
          simp only [Prod.fst_add, Prod.snd_add, Matrix.fromBlocks_add, add_zero]
        map_smul' := fun c p => by
          simp only [Prod.smul_fst, Prod.smul_snd, Matrix.fromBlocks_smul, smul_zero,
            RingHom.id_apply] }
  have h1 := integrable_mul_conjTranspose hS
  have h2 := integrable_conjTranspose_mul hS
  have hpt : ∀ ω, dilation (S ω) ^ 2 =
      B ((S ω * (S ω)ᴴ, (S ω)ᴴ * S ω) : Matrix m m 𝕜 × Matrix n n 𝕜) := fun ω => by
    rw [sq, dilation_mul_dilation]
    rfl
  simp only [hpt]
  rw [B.integral_comp_comm (h1.prodMk h2), integral_pair h1 h2]
  rfl

/-- **The Bernstein matrix MGF bound**: for $L > 0$, a centred, square-integrable random matrix
with $\mathbf{X} \preceq L\mathbf{I}$ almost surely has
$$\mathbb{E} e^{\theta \mathbf{X}} \preceq
\exp\Bigl(\frac{\theta^2/2}{1 - L\theta/3}\, \mathbb{E}\mathbf{X}^2\Bigr)$$
for $0 < \theta < 3/L$. [Tropp2015, Lemma 6.6.2]. -/
theorem hasMatrixMGFBound_of_integral_eq_zero_of_le [IsProbabilityMeasure μ]
    {X : Ω → Matrix n n 𝕜} (hL : 0 < L) (hX2 : MemLp X 2 μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) :
    HasMatrixMGFBound X (fun θ => θ ^ 2 / 2 / (1 - L * θ / 3)) (∫ ω, X ω ^ 2 ∂μ)
      (Set.Ioo 0 (3 / L)) μ := by
  have hH : ∀ᵐ ω ∂μ, (X ω).IsHermitian := hle.mono fun ω h => isHermitian_of_le_smul_one h
  have hXi : Integrable X μ := hX2.integrable one_le_two
  have hX2i : Integrable (fun ω => X ω ^ 2) μ := by
    refine (hX2.integrable_norm_pow two_ne_zero).mono'
      ((continuous_pow 2).comp_aestronglyMeasurable hX2.1) (ae_of_all _ fun ω => ?_)
    rw [sq, sq]
    exact norm_mul_le _ _
  have hS : (∫ ω, X ω ^ 2 ∂μ).IsHermitian :=
    Matrix.isHermitian_integral (hH.mono fun ω h => h.pow 2)
  have hexpc : Continuous (exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  have hQ : ∀ θ c : ℝ, Integrable (fun ω => 1 + θ • X ω + c • X ω ^ 2) μ := fun θ c =>
    ((integrable_const 1).add (hXi.smul θ)).add (hX2i.smul c)
  have hpt : ∀ θ ∈ Set.Ioo 0 (3 / L), ∀ᵐ ω ∂μ,
      exp (θ • X ω) ≤ 1 + θ • X ω + (θ ^ 2 / 2 / (1 - L * θ / 3)) • X ω ^ 2 := by
    intro θ hθ
    filter_upwards [hle, hH] with ω hω hωH
    refine exp_smul_le_one_add_smul_add_smul_sq (a := -specNorm (X ω)) ?_ hω
      fun x hx => Real.exp_mul_le_bernstein hθ.1 (mul_lt_three_of_mem_Ioo hL hθ) hx.2
    rw [neg_smul]
    exact hωH.neg_specNorm_smul_one_le
  have hint : ∀ θ ∈ Set.Ioo 0 (3 / L), Integrable (fun ω => exp (θ • X ω)) μ := by
    intro θ hθ
    refine (hQ θ (θ ^ 2 / 2 / (1 - L * θ / 3))).norm.mono'
      (hexpc.comp_aestronglyMeasurable (hX2.1.const_smul θ)) ?_
    filter_upwards [hpt θ hθ, hH] with ω hω hωH
    rw [← specNorm_eq_norm, ← specNorm_eq_norm]
    have hθX : (θ • X ω).IsHermitian := (IsSelfAdjoint.all θ).smul hωH
    exact hθX.posDef_exp.posSemidef.specNorm_le_specNorm_of_le hω
  refine ⟨hH, hS, hint, fun θ hθ => ?_⟩
  have h1 := integral_mono_ae (hint θ hθ) (hQ θ _) (hpt θ hθ)
  have hA : Integrable (fun ω => (1 : Matrix n n 𝕜) + θ • X ω) μ :=
    (integrable_const 1).add (hXi.smul θ)
  have hB : Integrable (fun ω => (θ ^ 2 / 2 / (1 - L * θ / 3)) • X ω ^ 2) μ :=
    hX2i.smul (θ ^ 2 / 2 / (1 - L * θ / 3))
  have hC : Integrable (fun ω => θ • X ω) μ := hXi.smul θ
  rw [integral_add hA hB, integral_add (integrable_const 1) hC, integral_const, integral_smul,
    integral_smul, hmean, smul_zero, add_zero, probReal_univ, one_smul] at h1
  have hcS : ((θ ^ 2 / 2 / (1 - L * θ / 3)) • ∫ ω, X ω ^ 2 ∂μ).IsHermitian :=
    (IsSelfAdjoint.all _).smul hS
  exact h1.trans hcS.one_add_le_exp

/-! ### From a trace bound -/

section TraceBound

variable {Y : Ω → Matrix n n 𝕜} {W : Matrix n n 𝕜}

/-- **Matrix Bernstein from a trace bound**: under a probability measure, if $\mathbf{Y}$ is
almost surely Hermitian, $\mathbf{W}$ Hermitian, $L > 0$, and for every $0 < \theta < 3/L$ the
trace exponential is integrable with
$$\mathbb{E}\operatorname{tr}e^{\theta\mathbf{Y}} \le
\operatorname{tr}\exp\Bigl(\frac{\theta^2/2}{1 - L\theta/3}\,\mathbf{W}\Bigr)\,,$$
then for $t \ge 0$, $n$ nonempty,
$$\mathbb{P}[\lambda_0(\mathbf{Y}) \ge t] \le \lvert n\rvert
\exp\Bigl(\frac{-t^2/2}{\|\mathbf{W}\|_2 + Lt/3}\Bigr)\,.$$
The trace-form layer of `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein`, as
`NLAlib.measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le` is for the Chernoff bound; a
sum sampled without replacement satisfies the trace bound
(`NLAlib.integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective`).
[Tropp2015, Theorem 6.6.1], whose proof goes through this trace bound. -/
theorem measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le [IsProbabilityMeasure μ]
    [Nonempty n] (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hW : W.IsHermitian) (hL : 0 < L)
    (hint : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) →
      Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • W)).trace) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (specNorm W + L * t / 3)) := by
  have hd : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  rcases ht.eq_or_lt with rfl | ht'
  · rw [show -((0 : ℝ) ^ 2 / 2) / (specNorm W + L * 0 / 3) = 0 by ring, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans hd
  obtain ⟨θ, hθ, hexp⟩ := exists_bernstein_exponent hL (specNorm_nonneg W) ht'
  have hg := sq_div_two_div_nonneg_of_mem_Ioo hL hθ
  have hM : ((θ ^ 2 / 2 / (1 - L * θ / 3)) • W).IsHermitian := (IsSelfAdjoint.all _).smul hW
  have htrW := hM.re_trace_exp_le_card_mul_exp
  rw [eigenvalue_real_smul _ hg] at htrW
  have hlam : eigenvalue W 0 ≤ specNorm W :=
    (le_abs_self _).trans (hW.abs_eigenvalue_le_specNorm 0)
  refine (measureReal_eigenvalue_zero_ge_le hY hθ.1 (hint θ hθ) t).trans ?_
  calc Real.exp (-θ * t) * ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ
      ≤ Real.exp (-θ * t) * (Fintype.card n *
          Real.exp (θ ^ 2 / 2 / (1 - L * θ / 3) * eigenvalue W 0)) :=
        mul_le_mul_of_nonneg_left ((htr θ hθ).trans htrW) (Real.exp_pos _).le
    _ = Fintype.card n * Real.exp (-θ * t + θ ^ 2 / 2 / (1 - L * θ / 3) * eigenvalue W 0) := by
        rw [Real.exp_add]
        ring
    _ ≤ Fintype.card n * Real.exp (-(t ^ 2 / 2) / (specNorm W + L * t / 3)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
        exact (add_le_add_right (mul_le_mul_of_nonneg_left hlam hg) _).trans hexp

/-- **Matrix Bernstein for the mean, from a trace bound**: under a probability measure, if
$\mathbf{Y}$ is integrable and almost surely Hermitian, $\mathbf{W}$ Hermitian, $L > 0$, and for
every $0 < \theta < 3/L$ the trace exponential is integrable with
$$\mathbb{E}\operatorname{tr}e^{\theta\mathbf{Y}} \le
\operatorname{tr}\exp\Bigl(\frac{\theta^2/2}{1 - L\theta/3}\,\mathbf{W}\Bigr)\,,$$
then, $n$ nonempty,
$$\mathbb{E}\,\lambda_0(\mathbf{Y}) \le \sqrt{2\|\mathbf{W}\|_2\log\lvert n\rvert} +
\frac{L\log\lvert n\rvert}{3}\,.$$
The mean form of `NLAlib.measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le`.
[Tropp2015, Theorem 6.6.1]. -/
theorem integral_eigenvalue_zero_le_bernstein_of_integral_le [IsProbabilityMeasure μ]
    [Nonempty n] (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hYi : Integrable Y μ) (hW : W.IsHermitian)
    (hL : 0 < L)
    (hint : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) →
      Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • W)).trace) :
    ∫ ω, eigenvalue (Y ω) 0 ∂μ ≤
      √(2 * specNorm W * Real.log (Fintype.card n)) + L * Real.log (Fintype.card n) / 3 := by
  have hd : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hlam : eigenvalue W 0 ≤ specNorm W :=
    (le_abs_self _).trans (hW.abs_eigenvalue_le_specNorm 0)
  refine le_of_forall_bernstein_mean hL (Real.log_nonneg hd) (specNorm_nonneg _) fun θ hθ => ?_
  have hg := sq_div_two_div_nonneg_of_mem_Ioo hL hθ
  have hM : ((θ ^ 2 / 2 / (1 - L * θ / 3)) • W).IsHermitian := (IsSelfAdjoint.all _).smul hW
  have htrW := hM.re_trace_exp_le_card_mul_exp
  rw [eigenvalue_real_smul _ hg] at htrW
  have hpos : 0 < ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ :=
    integral_pos_of_ae_pos (hint θ hθ) (hY.mono fun ω hω =>
      Matrix.IsHermitian.re_trace_exp_pos ((IsSelfAdjoint.all θ).smul hω))
  have hle' : ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      Fintype.card n * Real.exp (θ ^ 2 / 2 / (1 - L * θ / 3) * specNorm W) :=
    (htr θ hθ).trans (htrW.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlam hg)) (Nat.cast_nonneg _)))
  refine (integral_eigenvalue_zero_le hY hYi hθ.1 (hint θ hθ)).trans ?_
  refine (mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle')
    (inv_nonneg.2 hθ.1.le)).trans_eq ?_
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]

end TraceBound

variable {ι : Type*} [Fintype ι]

section Hermitian

variable {X : ι → Ω → Matrix n n 𝕜}

/-- **Matrix Bernstein**, Hermitian summands: for $n$ nonempty, finitely many independent,
centred, square-integrable random matrices with $\mathbf{X}_k \preceq L\mathbf{I}$ almost surely,
$L > 0$, $v = \|\sum_k \mathbb{E}\mathbf{X}_k^2\|_2$ and $t \ge 0$,
$$\mathbb{P}\Bigl[\lambda_0\Bigl(\sum_k \mathbf{X}_k\Bigr) \ge t\Bigr]
\le \lvert n\rvert \exp\Bigl(\frac{-t^2/2}{v + L t / 3}\Bigr)\,.$$
[Tropp2015, Theorem 6.6.1]. -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein [Nonempty n] (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) /
        (specNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ) + L * t / 3)) := by
  have := hind.isProbabilityMeasure
  have h := fun k => hasMatrixMGFBound_of_integral_eq_zero_of_le hL (hX2 k) (hmean k) (hle k)
  have hV : (∑ k, ∫ ω, X k ω ^ 2 ∂μ).IsHermitian :=
    isSelfAdjoint_sum _ fun k _ => (h k).isHermitian_bound
  have hd : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hP : μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤ 1 := measureReal_le_one
  rcases ht.eq_or_lt with rfl | ht'
  · rw [show -((0 : ℝ) ^ 2 / 2) / (specNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ) + L * 0 / 3) = 0 by ring,
      Real.exp_zero, mul_one]
    exact hP.trans hd
  obtain ⟨θ, hθ, hexp⟩ := exists_bernstein_exponent hL
    (specNorm_nonneg (∑ k, ∫ ω, X k ω ^ 2 ∂μ)) ht'
  have hg := sq_div_two_div_nonneg_of_mem_Ioo hL hθ
  refine (HasMatrixMGFBound.measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp hind h hθ hθ.1
    hg t).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
  exact (add_le_add_right (mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (hV.abs_eigenvalue_le_specNorm 0)) hg) _).trans hexp

/-- **Matrix Bernstein** for the mean, Hermitian summands: for finitely many independent,
centred, square-integrable random $n \times n$ matrices $\mathbf{X}_k$ over $\Bbbk$, $n$ nonempty,
with $\mathbf{X}_k \preceq L\mathbf{I}$ almost surely, $L > 0$ and
$v = \|\sum_k \mathbb{E}\mathbf{X}_k^2\|_2$, the largest eigenvalue $\lambda_0$ satisfies
$$\mathbb{E}\, \lambda_0\Bigl(\sum_k \mathbf{X}_k\Bigr)
\le \sqrt{2 v \log \lvert n\rvert} + \frac{L \log \lvert n\rvert}{3}\,.$$
[Tropp2015, Theorem 6.6.1]. The mean form of
`NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein`. -/
theorem integral_eigenvalue_zero_sum_le_bernstein [Nonempty n] (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      √(2 * specNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ) * Real.log (Fintype.card n)) +
        L * Real.log (Fintype.card n) / 3 := by
  have := hind.isProbabilityMeasure
  have h := fun k => hasMatrixMGFBound_of_integral_eq_zero_of_le hL (hX2 k) (hmean k) (hle k)
  set V := ∑ k, ∫ ω, X k ω ^ 2 ∂μ with hVdef
  have hV : V.IsHermitian := isSelfAdjoint_sum _ fun k _ => (h k).isHermitian_bound
  have hd : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hlam : eigenvalue V 0 ≤ specNorm V :=
    (le_abs_self _).trans (hV.abs_eigenvalue_le_specNorm 0)
  refine le_of_forall_bernstein_mean hL (Real.log_nonneg hd) (specNorm_nonneg _) fun θ hθ => ?_
  have hg := sq_div_two_div_nonneg_of_mem_Ioo hL hθ
  refine (HasMatrixMGFBound.integral_eigenvalue_zero_sum_le hind h
    (fun k => (hX2 k).integrable one_le_two) hθ hθ.1).trans ?_
  have hM : ((θ ^ 2 / 2 / (1 - L * θ / 3)) • V).IsHermitian := (IsSelfAdjoint.all _).smul hV
  have htr := hM.re_trace_exp_le_card_mul_exp
  rw [eigenvalue_real_smul _ hg] at htr
  have hle' : RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • V)).trace ≤
      Fintype.card n * Real.exp (θ ^ 2 / 2 / (1 - L * θ / 3) * specNorm V) :=
    htr.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlam hg)) (Nat.cast_nonneg _))
  refine (mul_le_mul_of_nonneg_left (Real.log_le_log hM.re_trace_exp_pos hle')
    (inv_nonneg.2 hθ.1.le)).trans_eq ?_
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]

end Hermitian

section Rectangular

variable {m : Type*} [Fintype m] [DecidableEq m] {S : ι → Ω → Matrix m n 𝕜}

/-- **Matrix Bernstein**, rectangular summands: for $n$ nonempty, finitely many independent,
centred, square-integrable random matrices $\mathbf{S}_k$ with $\|\mathbf{S}_k\|_2 \le L$ almost
surely, $L > 0$ and $t \ge 0$,
$$\mathbb{P}\Bigl[\Bigl\|\sum_k \mathbf{S}_k\Bigr\|_2 \ge t\Bigr]
\le (\lvert m\rvert + \lvert n\rvert) \exp\Bigl(\frac{-t^2/2}{v + L t / 3}\Bigr)$$
with variance $v = \max\bigl(\|\sum_k \mathbb{E}\mathbf{S}_k\mathbf{S}_k^{\mathsf{H}}\|_2,
\|\sum_k \mathbb{E}\mathbf{S}_k^{\mathsf{H}}\mathbf{S}_k\|_2\bigr)$.
[Tropp2015, Theorem 6.1.1]. For square Hermitian summands this is the two-sided form. -/
theorem measureReal_specNorm_sum_ge_le_bernstein [Nonempty n]
    (hind : iIndepFun S μ) (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ)
    (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0) (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, S k ω)} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-(t ^ 2 / 2) /
        (max (specNorm (∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ))
          (specNorm (∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ)) + L * t / 3)) := by
  have := hind.isProbabilityMeasure
  have h := measureReal_eigenvalue_zero_sum_ge_le_bernstein (iIndepFun_dilation hind) hL
    (fun k => memLp_dilation (hS2 k))
    (fun k => integral_dilation_eq_zero ((hS2 k).integrable one_le_two) (hmean k))
    (fun k => (hle k).mono fun ω h =>
      (isHermitian_dilation _).le_smul_one_of_specNorm_le (by rwa [specNorm_dilation])) ht
  have hsq : ∀ k, ∫ ω, dilation (S k ω) ^ 2 ∂μ =
      Matrix.fromBlocks (∫ ω, S k ω * (S k ω)ᴴ ∂μ) 0 0 (∫ ω, (S k ω)ᴴ * S k ω ∂μ) := fun k =>
    integral_dilation_sq (hS2 k)
  simp only [← dilation_sum, eigenvalue_zero_dilation, hsq, Matrix.sum_fromBlocks,
    Finset.sum_const_zero, specNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum, Nat.cast_add] at h
  exact h

/-- **Matrix Bernstein** for the mean, rectangular summands: for finitely many independent,
centred, square-integrable random $m \times n$ matrices $\mathbf{S}_k$ over $\Bbbk$, $n$
nonempty, with $\|\mathbf{S}_k\|_2 \le L$ almost surely, $L > 0$, variance
$v = \max\bigl(\|\sum_k \mathbb{E}\mathbf{S}_k\mathbf{S}_k^{\mathsf{H}}\|_2,
\|\sum_k \mathbb{E}\mathbf{S}_k^{\mathsf{H}}\mathbf{S}_k\|_2\bigr)$ and
$d = \lvert m\rvert + \lvert n\rvert$,
$$\mathbb{E} \Bigl\|\sum_k \mathbf{S}_k\Bigr\|_2 \le \sqrt{2 v \log d} + \frac{L \log d}{3}\,.$$
[Tropp2015, Theorem 6.1.1]. The mean form of `NLAlib.measureReal_specNorm_sum_ge_le_bernstein`. -/
theorem integral_specNorm_sum_le_bernstein [Nonempty n] (hind : iIndepFun S μ)
    (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) :
    ∫ ω, specNorm (∑ k, S k ω) ∂μ ≤
      √(2 * max (specNorm (∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ))
          (specNorm (∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ)) *
        Real.log (Fintype.card m + Fintype.card n)) +
      L * Real.log (Fintype.card m + Fintype.card n) / 3 := by
  have := hind.isProbabilityMeasure
  have h := integral_eigenvalue_zero_sum_le_bernstein (iIndepFun_dilation hind) hL
    (fun k => memLp_dilation (hS2 k))
    (fun k => integral_dilation_eq_zero ((hS2 k).integrable one_le_two) (hmean k))
    (fun k => (hle k).mono fun ω h =>
      (isHermitian_dilation _).le_smul_one_of_specNorm_le (by rwa [specNorm_dilation]))
  have hsq : ∀ k, ∫ ω, dilation (S k ω) ^ 2 ∂μ =
      Matrix.fromBlocks (∫ ω, S k ω * (S k ω)ᴴ ∂μ) 0 0 (∫ ω, (S k ω)ᴴ * S k ω ∂μ) := fun k =>
    integral_dilation_sq (hS2 k)
  simp only [← dilation_sum, eigenvalue_zero_dilation, hsq, Matrix.sum_fromBlocks,
    Finset.sum_const_zero, specNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum, Nat.cast_add] at h
  exact h

end Rectangular

/-- **Bernstein's inequality** for bounded centred real variables, the $1 \times 1$ case of matrix
Bernstein: for finitely many independent, centred, square-integrable $X_k \le L$ almost surely,
$L > 0$ and $t \ge 0$,
$$\mathbb{P}\Bigl[\sum_k X_k \ge t\Bigr]
\le \exp\Bigl(\frac{-t^2/2}{\sum_k \mathbb{E}[X_k^2] + L t / 3}\Bigr)\,.$$
[Tropp2015, Theorem 6.6.1], specialized to a scalar self-adjoint summand. -/
theorem measureReal_sum_ge_le_bernstein {X : ι → Ω → ℝ} (hind : iIndepFun X μ) (hL : 0 < L)
    (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ k, X k ω} ≤
      Real.exp (-(t ^ 2 / 2) / (∑ k, ∫ ω, X k ω ^ 2 ∂μ + L * t / 3)) := by
  have := hind.isProbabilityMeasure
  let e : ℝ →L[ℝ] Matrix Unit Unit ℝ := (1 : ℝ →L[ℝ] ℝ).smulRight 1
  have hk1 : 0 < Fintype.card Unit := Fintype.card_pos
  have h := measureReal_eigenvalue_zero_sum_ge_le_bernstein (n := Unit) (𝕜 := ℝ)
    (X := fun k ω => X k ω • (1 : Matrix Unit Unit ℝ))
    (hind.comp (fun _ x => x • (1 : Matrix Unit Unit ℝ)) fun _ => measurable_id.smul_const _) hL
    (fun k => e.comp_memLp' (hX2 k))
    (fun k => by rw [integral_smul_const, hmean k, zero_smul])
    (fun k => (hle k).mono fun ω h => Matrix.le_iff.2 (by
      rw [← sub_smul]
      exact Matrix.PosSemidef.one.smul (sub_nonneg.2 h))) ht
  have hs : 0 ≤ ∑ k, ∫ ω, X k ω ^ 2 ∂μ :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _
  have hsq : ∀ k, ∫ ω, (X k ω • (1 : Matrix Unit Unit ℝ)) ^ 2 ∂μ =
      (∫ ω, X k ω ^ 2 ∂μ) • (1 : Matrix Unit Unit ℝ) := fun k => by
    simp only [smul_pow, one_pow]
    exact integral_smul_const _ _
  have hspec : specNorm ((∑ k, ∫ ω, X k ω ^ 2 ∂μ) • (1 : Matrix Unit Unit ℝ)) =
      ∑ k, ∫ ω, X k ω ^ 2 ∂μ := by
    rw [(Matrix.PosSemidef.one.smul hs).specNorm_eq_eigenvalue_zero,
      eigenvalue_real_smul_one _ hk1]
  simp only [hsq, ← Finset.sum_smul, eigenvalue_real_smul_one _ hk1, hspec, Fintype.card_unit,
    Nat.cast_one, one_mul] at h
  exact h

end NLAlib
