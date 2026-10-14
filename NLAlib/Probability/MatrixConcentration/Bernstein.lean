/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.Real.Sqrt
public import NLAlib.Matrix.Spectral.Dilation
public import NLAlib.Probability.MatrixConcentration.MGFBound

/-!
# The matrix Bernstein inequality

For independent centred random Hermitian matrices with `X k ≤ L • 1` almost surely and variance
`v = ‖∑ E X k²‖`, `P(t ≤ λ_max (∑ X k)) ≤ d exp (-(t²/2) / (v + L t / 3))` and
`E λ_max (∑ X k) ≤ √(2 v log d) + L log d / 3` (Tropp 2015, Theorem 6.6.1). Rectangular summands go
through the dilation, with `v` the larger of the two variances and dimension `m + n`
(Tropp 2015, Theorem 6.1.1); for square Hermitian summands this is also the two-sided
Hermitian form. The `1 × 1` case is Bernstein's inequality for bounded centred real variables.

## Main results

* `NLAlib.hasMatrixMGFBound_of_integral_eq_zero_of_le`: the Bernstein matrix MGF bound.
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

/-- The derivative of `u + (eᵘ - 1 - u)/3 - (1 - u/3)(eᵘ - 1)`. -/
private theorem hasDerivAt_bernsteinAux' (u : ℝ) :
    HasDerivAt (fun u => u + (Real.exp u - 1 - u) / 3 - (1 - u / 3) * (Real.exp u - 1))
      ((1 - Real.exp u * (1 - u)) / 3) u := by
  have h1 := (((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id' u)).div_const 3
  have h2 := ((hasDerivAt_id' u).div_const 3).const_sub 1
  have h3 := h2.mul ((Real.hasDerivAt_exp u).sub_const 1)
  refine (((hasDerivAt_id' u).add h1).sub h3).congr_deriv ?_
  ring

/-- The derivative of `u²/2 - (1 - u/3)(eᵘ - 1 - u)`. -/
private theorem hasDerivAt_bernsteinAux (u : ℝ) :
    HasDerivAt (fun u => u ^ 2 / 2 - (1 - u / 3) * (Real.exp u - 1 - u))
      (u + (Real.exp u - 1 - u) / 3 - (1 - u / 3) * (Real.exp u - 1)) u := by
  have h1 := ((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id' u)
  have h2 := ((hasDerivAt_id' u).div_const 3).const_sub 1
  refine (((hasDerivAt_pow 2 u).div_const 2).sub (h2.mul h1)).congr_deriv ?_
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- `u²/2 - (1 - u/3)(eᵘ - 1 - u) ≥ 0` for every real `u`: its derivative is monotone and
vanishes at `0`, where the function vanishes. -/
private theorem bernsteinAux_nonneg (u : ℝ) :
    0 ≤ u ^ 2 / 2 - (1 - u / 3) * (Real.exp u - 1 - u) := by
  set g : ℝ → ℝ := fun u => u ^ 2 / 2 - (1 - u / 3) * (Real.exp u - 1 - u) with hg
  set h : ℝ → ℝ := fun u => u + (Real.exp u - 1 - u) / 3 - (1 - u / 3) * (Real.exp u - 1)
    with hh
  have hmono : Monotone h := by
    refine monotone_of_deriv_nonneg (fun u => (hasDerivAt_bernsteinAux' u).differentiableAt)
      fun u => ?_
    rw [(hasDerivAt_bernsteinAux' u).deriv]
    have h1 := Real.add_one_le_exp (-u)
    have h2 : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := Real.exp_pos u
    refine div_nonneg ?_ (by norm_num)
    nlinarith
  have hd : Differentiable ℝ g := fun u => (hasDerivAt_bernsteinAux u).differentiableAt
  have hg0 : g 0 = 0 := by simp only [hg]; norm_num
  have hh0 : h 0 = 0 := by simp only [hh]; norm_num
  change 0 ≤ g u
  rcases le_total u 0 with hu | hu
  · have hanti : AntitoneOn g (Set.Iic 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hd.continuous.continuousOn
        hd.differentiableOn fun x hx => ?_
      rw [interior_Iic] at hx
      rw [(hasDerivAt_bernsteinAux x).deriv]
      exact (hmono (le_of_lt (Set.mem_Iio.mp hx))).trans_eq hh0
    have := hanti (Set.mem_Iic.mpr hu) (Set.mem_Iic.mpr le_rfl) hu
    linarith
  · have hmon : MonotoneOn g (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hd.continuous.continuousOn
        hd.differentiableOn fun x hx => ?_
      rw [interior_Ici] at hx
      rw [(hasDerivAt_bernsteinAux x).deriv]
      exact hh0.symm.trans_le (hmono (le_of_lt (Set.mem_Ioi.mp hx)))
    have := hmon (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
    linarith

/-- The one-sided Bernstein bound for the exponential ([Tropp2015], Lemma 6.6.2): for `x ≤ L`
and `0 < θ` with `Lθ < 3`, `e^{θx} ≤ 1 + θx + (θ²/2)/(1 - Lθ/3) x²`. -/
private theorem exp_mul_le_bernstein {L θ x : ℝ} (hθ : 0 < θ) (hθL : L * θ < 3) (hx : x ≤ L) :
    Real.exp (θ * x) ≤ 1 + θ * x + θ ^ 2 / 2 / (1 - L * θ / 3) * x ^ 2 := by
  have hux : θ * x ≤ L * θ := by nlinarith
  have hpos : 0 < 1 - L * θ / 3 := by linarith
  have hpos' : 0 < 1 - θ * x / 3 := by linarith
  have hg := bernsteinAux_nonneg (θ * x)
  have h1 : Real.exp (θ * x) - 1 - θ * x ≤ (θ * x) ^ 2 / 2 / (1 - θ * x / 3) := by
    rw [le_div_iff₀ hpos']
    nlinarith
  have h2 : (θ * x) ^ 2 / 2 / (1 - θ * x / 3) ≤ (θ * x) ^ 2 / 2 / (1 - L * θ / 3) :=
    div_le_div_of_nonneg_left (by positivity) hpos (by linarith)
  have h3 : θ ^ 2 / 2 / (1 - L * θ / 3) * x ^ 2 = (θ * x) ^ 2 / 2 / (1 - L * θ / 3) := by ring
  linarith

/-- On `(0, 3/L)`, `1 - Lθ/3 > 0` and the Bernstein coefficient `(θ²/2)/(1 - Lθ/3)` is
nonnegative. -/
private theorem bernsteinCoeff_nonneg {L θ : ℝ} (hL : 0 < L) (hθ : θ ∈ Set.Ioo 0 (3 / L)) :
    L * θ < 3 ∧ 0 ≤ θ ^ 2 / 2 / (1 - L * θ / 3) := by
  have h : L * θ < 3 := by
    have := hθ.2
    rw [lt_div_iff₀ hL] at this
    linarith
  exact ⟨h, div_nonneg (by positivity) (by linarith)⟩

/-- The choice of `θ` in the Bernstein tail: `θ = t / (v + Lt/3)`, or `θ = 3/(2L)` when `v = 0`,
gives `-θt + g(θ) v ≤ -(t²/2)/(v + Lt/3)`. -/
private theorem exists_bernstein_exponent {L v t : ℝ} (hL : 0 < L) (hv : 0 ≤ v) (ht : 0 < t) :
    ∃ θ ∈ Set.Ioo 0 (3 / L),
      -θ * t + θ ^ 2 / 2 / (1 - L * θ / 3) * v ≤ -(t ^ 2 / 2) / (v + L * t / 3) := by
  rcases hv.eq_or_lt with rfl | hv'
  · refine ⟨3 / (2 * L), ⟨by positivity, ?_⟩, le_of_eq ?_⟩
    · rw [div_lt_div_iff₀ (by positivity) hL]
      nlinarith
    · field_simp
      ring
  set D := v + L * t / 3 with hD
  have hD0 : 0 < D := by positivity
  refine ⟨t / D, ⟨div_pos ht hD0, ?_⟩, le_of_eq ?_⟩
  · rw [div_lt_div_iff₀ hD0 hL, hD]
    nlinarith
  · have hq : 1 - L * (t / D) / 3 = v / D := by
      field_simp
      rw [hD]
      ring
    rw [hq]
    field_simp
    ring

/-- The Bernstein mean optimisation: if `x ≤ θ⁻¹ (a + g(θ) v)` on `(0, 3/L)`, then
`x ≤ √(2 v a) + L a / 3` (substitute `θ = u / (1 + L u / 3)`). -/
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

/-! ### Integrability, the dilation and `1 × 1` matrices -/

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

/-- The Hermitian dilation as a continuous real-linear map. -/
private noncomputable def dilationCLM (m : Type*) [Fintype m] :
    Matrix m n 𝕜 →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := dilation
      map_add' := dilation_add
      map_smul' := dilation_smul_real }

/-- The integral of the dilation of an integrable random matrix is the dilation of its
integral. -/
theorem integral_dilation {m : Type*} [Fintype m] [DecidableEq m] {S : Ω → Matrix m n 𝕜}
    (hS : Integrable S μ) : ∫ ω, dilation (S ω) ∂μ = dilation (∫ ω, S ω ∂μ) :=
  (dilationCLM m).integral_comp_comm hS

/-- The integral of the square of a dilation is block diagonal. -/
private theorem integral_dilation_sq {m : Type*} [Fintype m] [DecidableEq m]
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

omit [Fintype n] [DecidableEq n] in
/-- A sum of block diagonal matrices is block diagonal. -/
private theorem sum_fromBlocks_diagonal {ι m : Type*} [Fintype ι] (P : ι → Matrix m m 𝕜)
    (Q : ι → Matrix n n 𝕜) :
    ∑ k, Matrix.fromBlocks (P k) 0 0 (Q k) = Matrix.fromBlocks (∑ k, P k) 0 0 (∑ k, Q k) := by
  ext (i | i) (j | j) <;>
    simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      Finset.sum_const_zero]

/-- **The Bernstein matrix MGF bound** ([Tropp2015], Lemma 6.6.2): a centred random matrix with
`X ≤ L • 1` almost surely has `E exp (θ X) ≤ exp (θ²/2 / (1 - Lθ/3) • E X²)` for `0 < θ < 3/L`. -/
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
      fun x hx => exp_mul_le_bernstein hθ.1 (bernsteinCoeff_nonneg hL hθ).1 hx.2
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

variable {ι : Type*} [Fintype ι]

section Hermitian

variable {X : ι → Ω → Matrix n n 𝕜}

/-- **Matrix Bernstein**, Hermitian summands ([Tropp2015], Theorem 6.6.1). -/
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
  have hg := (bernsteinCoeff_nonneg hL hθ).2
  refine (HasMatrixMGFBound.measure_eigenvalue_zero_sum_ge_le_card_mul_exp hind h hθ hθ.1
    hg t).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
  exact (add_le_add_right (mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (hV.abs_eigenvalue_le_specNorm 0)) hg) _).trans hexp

/-- **Matrix Bernstein** for the mean, Hermitian summands ([Tropp2015], Theorem 6.6.1). -/
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
  have hg := (bernsteinCoeff_nonneg hL hθ).2
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

omit [Fintype ι] in
/-- The dilations of bounded centred independent summands satisfy the hypotheses of the
Hermitian theorem. -/
private theorem dilation_hypotheses (hind : iIndepFun S μ) (hS2 : ∀ k, MemLp (S k) 2 μ)
    (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0) (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) :
    iIndepFun (fun k ω => dilation (S k ω)) μ ∧
      (∀ k, MemLp (fun ω => dilation (S k ω)) 2 μ) ∧ (∀ k, ∫ ω, dilation (S k ω) ∂μ = 0) ∧
      ∀ k, ∀ᵐ ω ∂μ, dilation (S k ω) ≤ L • (1 : Matrix (m ⊕ n) (m ⊕ n) 𝕜) := by
  have := hind.isProbabilityMeasure
  have hmeas : Measurable (fun A : Matrix m n 𝕜 => dilation A) :=
    (Continuous.matrix_fromBlocks continuous_const continuous_id
      continuous_id.matrix_conjTranspose continuous_const).measurable
  refine ⟨hind.comp (fun _ A => dilation A) fun _ => hmeas,
    fun k => (dilationCLM (𝕜 := 𝕜) (n := n) m).comp_memLp' (hS2 k),
    fun k => ?_, fun k => (hle k).mono fun ω h =>
      (isHermitian_dilation _).le_smul_one_of_specNorm_le (by rwa [specNorm_dilation])⟩
  rw [integral_dilation ((hS2 k).integrable one_le_two), hmean k, dilation_zero]

/-- **Matrix Bernstein**, rectangular summands ([Tropp2015], Theorem 6.1.1), with variance
`v = max ‖∑ E S Sᴴ‖ ‖∑ E Sᴴ S‖`. For square Hermitian summands this is the two-sided form. -/
theorem measureReal_specNorm_sum_ge_le_bernstein [Nonempty n]
    (hind : iIndepFun S μ) (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ)
    (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0) (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, S k ω)} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-(t ^ 2 / 2) /
        (max (specNorm (∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ))
          (specNorm (∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ)) + L * t / 3)) := by
  obtain ⟨h1, h2, h3, h4⟩ := dilation_hypotheses hind hS2 hmean hle
  have h := measureReal_eigenvalue_zero_sum_ge_le_bernstein h1 hL h2 h3 h4 ht
  have hsq : ∀ k, ∫ ω, dilation (S k ω) ^ 2 ∂μ =
      Matrix.fromBlocks (∫ ω, S k ω * (S k ω)ᴴ ∂μ) 0 0 (∫ ω, (S k ω)ᴴ * S k ω ∂μ) := fun k =>
    integral_dilation_sq (hS2 k)
  simp only [← dilation_sum, eigenvalue_zero_dilation, hsq, sum_fromBlocks_diagonal,
    specNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum, Nat.cast_add] at h
  exact h

/-- **Matrix Bernstein** for the mean, rectangular summands ([Tropp2015], Theorem 6.1.1). -/
theorem integral_specNorm_sum_le_bernstein [Nonempty n] (hind : iIndepFun S μ)
    (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) :
    ∫ ω, specNorm (∑ k, S k ω) ∂μ ≤
      √(2 * max (specNorm (∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ))
          (specNorm (∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ)) *
        Real.log (Fintype.card m + Fintype.card n)) +
      L * Real.log (Fintype.card m + Fintype.card n) / 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := dilation_hypotheses hind hS2 hmean hle
  have h := integral_eigenvalue_zero_sum_le_bernstein h1 hL h2 h3 h4
  have hsq : ∀ k, ∫ ω, dilation (S k ω) ^ 2 ∂μ =
      Matrix.fromBlocks (∫ ω, S k ω * (S k ω)ᴴ ∂μ) 0 0 (∫ ω, (S k ω)ᴴ * S k ω ∂μ) := fun k =>
    integral_dilation_sq (hS2 k)
  simp only [← dilation_sum, eigenvalue_zero_dilation, hsq, sum_fromBlocks_diagonal,
    specNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum, Nat.cast_add] at h
  exact h

end Rectangular

/-- **Bernstein's inequality** for bounded centred real variables, the `1 × 1` case of matrix
Bernstein: `P(t ≤ ∑ X k) ≤ exp (-(t²/2) / (∑ E X k² + L t / 3))`. -/
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
