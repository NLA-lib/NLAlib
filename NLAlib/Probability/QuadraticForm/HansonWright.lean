/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.QuadraticForm.HansonWright.OffDiagonal
public import NLAlib.Probability.SubExponential.Tail
public import NLAlib.Probability.SubGaussian.Square

/-!
# The Hanson–Wright inequality

For a real random vector `X` with independent coordinates, each sub-Gaussian with proxy `c`, and
any real matrix `A`, the quadratic form `Xᵀ A X` concentrates about its mean:

`P(t ≤ |Xᵀ A X - E Xᵀ A X|) ≤ 2 exp (-C min (t² / (c² ‖A‖_F²), t / (c ‖A‖)))`,

with the universal constant `C = NLAlib.hansonWrightConstant`, which the sources leave
unspecified. The diagonal part is Bernstein's inequality for the centred squares; the
off-diagonal part is bounded by decoupling and comparison with a Gaussian chaos
(`NLAlib/Probability/QuadraticForm/HansonWright/OffDiagonal.lean`). The two are combined by
convexity of `exp`, which needs no independence between them: the centred form is sub-exponential
with variance proxy `98 c² ‖A‖_F²` and scale `28 c ‖A‖`, which gives `C = 1/196`.

## Main definitions

* `NLAlib.hansonWrightConstant`.

## Main results

* `NLAlib.measureReal_quadForm_sub_integral_ge_le`,
  `NLAlib.measureReal_quadForm_sub_integral_le_le`: the upper and lower tails.
* `NLAlib.measureReal_abs_quadForm_sub_integral_ge_le`: **the Hanson–Wright inequality**.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Theorem 6.2.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ} {c : ℝ≥0}

/-- The Hanson–Wright constant: the universal constant in the exponent of the Hanson–Wright
inequality, which the sources ([Vershynin2018], Theorem 6.2.1; Rudelson and Vershynin 2013,
Theorem 1.1) leave unspecified. The value is what the proof here reaches; a larger value is a
better bound. Use only `hansonWrightConstant_pos` and `le_hansonWrightConstant`.

The proof reaches `1/196`: the centred quadratic form is sub-exponential with variance proxy
`98 c² ‖A‖_F²` and scale `28 c ‖A‖` (the diagonal part has `32 c² ‖A‖_F²` and `4 c ‖A‖`, the
off-diagonal part `18 c² ‖A‖_F²` and `12 c ‖A‖`, combined by convexity with weights `4/7` and
`3/7`), so its tail is at most `exp (-min (t² / (196 c² ‖A‖_F²)) (t / (56 c ‖A‖)))`. The
prototype's proof reached `1 / (256 e²)`. -/
noncomputable irreducible_def hansonWrightConstant : ℝ := 1 / 196

/-- The Hanson–Wright constant is positive. -/
theorem hansonWrightConstant_pos : 0 < hansonWrightConstant := by
  rw [hansonWrightConstant_def]
  norm_num

/-- An explicit lower bound on `hansonWrightConstant`. -/
theorem le_hansonWrightConstant : 1 / 196 ≤ hansonWrightConstant := by
  rw [hansonWrightConstant_def]

/-- The sum of two sub-exponential variables, independent or not, by convexity of `exp` with
weights `1 / p` and `1 / q`. -/
private lemma hasSubexponentialMGF_add {Y Z : Ω → ℝ} {v₁ b₁ v₂ b₂ v b : ℝ≥0}
    (hY : HasSubexponentialMGF Y v₁ b₁ μ) (hZ : HasSubexponentialMGF Z v₂ b₂ μ) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1) (hv₁ : p ^ 2 * v₁ ≤ v)
    (hv₂ : q ^ 2 * v₂ ≤ v) (hb₁ : p * b₁ ≤ b) (hb₂ : q * b₂ ≤ b) :
    HasSubexponentialMGF (fun ω => Y ω + Z ω) v b μ := by
  have hw₁ : ∀ l : ℝ, (b : ℝ) * |l| < 1 → (b₁ : ℝ) * |p * l| < 1 := fun l hl => by
    rw [abs_mul, abs_of_pos hp]
    nlinarith [mul_le_mul_of_nonneg_right hb₁ (abs_nonneg l)]
  have hw₂ : ∀ l : ℝ, (b : ℝ) * |l| < 1 → (b₂ : ℝ) * |q * l| < 1 := fun l hl => by
    rw [abs_mul, abs_of_pos hq]
    nlinarith [mul_le_mul_of_nonneg_right hb₂ (abs_nonneg l)]
  have hpt : ∀ (l : ℝ) ω, rexp (l * (Y ω + Z ω)) ≤
      1 / p * rexp (p * l * Y ω) + 1 / q * rexp (q * l * Z ω) := by
    intro l ω
    have := convexOn_exp.2 (Set.mem_univ (p * l * Y ω)) (Set.mem_univ (q * l * Z ω))
      (by positivity : (0 : ℝ) ≤ 1 / p) (by positivity : (0 : ℝ) ≤ 1 / q) hpq
    have e₁ : 1 / p * (p * l * Y ω) = l * Y ω := by field_simp
    have e₂ : 1 / q * (q * l * Z ω) = l * Z ω := by field_simp
    simp only [smul_eq_mul, e₁, e₂] at this
    rwa [mul_add]
  have hm : ∀ l : ℝ, AEStronglyMeasurable (fun ω => rexp (l * (Y ω + Z ω))) μ := fun l =>
    (measurable_exp.comp_aemeasurable
      ((hY.aemeasurable.add hZ.aemeasurable).const_mul l)).aestronglyMeasurable
  have hint : ∀ l : ℝ, (b : ℝ) * |l| < 1 →
      Integrable (fun ω => 1 / p * rexp (p * l * Y ω) + 1 / q * rexp (q * l * Z ω)) μ :=
    fun l hl => ((hY.integrable_exp_mul (p * l) (hw₁ l hl)).const_mul _).add
      ((hZ.integrable_exp_mul (q * l) (hw₂ l hl)).const_mul _)
  have hint' : ∀ l : ℝ, (b : ℝ) * |l| < 1 → Integrable (fun ω => rexp (l * (Y ω + Z ω))) μ :=
    fun l hl => (hint l hl).mono' (hm l) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (exp_pos _).le]
      exact hpt l ω)
  refine ⟨hint', fun l hl => ?_⟩
  calc mgf (fun ω => Y ω + Z ω) μ l
      ≤ ∫ ω, (1 / p * rexp (p * l * Y ω) + 1 / q * rexp (q * l * Z ω)) ∂μ :=
        integral_mono (hint' l hl) (hint l hl) (hpt l)
    _ = 1 / p * mgf Y μ (p * l) + 1 / q * mgf Z μ (q * l) := by
        rw [integral_add ((hY.integrable_exp_mul (p * l) (hw₁ l hl)).const_mul _)
          ((hZ.integrable_exp_mul (q * l) (hw₂ l hl)).const_mul _), integral_const_mul,
          integral_const_mul]
        rfl
    _ ≤ 1 / p * rexp (v₁ * (p * l) ^ 2 / 2) + 1 / q * rexp (v₂ * (q * l) ^ 2 / 2) := by
        gcongr
        · exact hY.mgf_le _ (hw₁ l hl)
        · exact hZ.mgf_le _ (hw₂ l hl)
    _ ≤ 1 / p * rexp (v * l ^ 2 / 2) + 1 / q * rexp (v * l ^ 2 / 2) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity))
          (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity))
        · nlinarith [mul_le_mul_of_nonneg_right hv₁ (sq_nonneg l)]
        · nlinarith [mul_le_mul_of_nonneg_right hv₂ (sq_nonneg l)]
    _ = rexp (v * l ^ 2 / 2) := by rw [← add_mul, hpq, one_mul]

/-- The diagonal part: Bernstein's inequality for the centred squares. -/
private lemma hasSubexponentialMGF_diag (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) :
    HasSubexponentialMGF (fun ω => ∑ i, A i i * (X ω i ^ 2 - ∫ ω', X ω' i ^ 2 ∂μ))
      (32 * c ^ 2 * (frobNorm A).toNNReal ^ 2) (4 * c * (specNorm A).toNNReal) μ := by
  have := hind.isProbabilityMeasure
  have hind' : iIndepFun (fun i ω => X ω i ^ 2 - ∫ ω', X ω' i ^ 2 ∂μ) μ :=
    hind.comp (fun i x => x ^ 2 - ∫ ω', X ω' i ^ 2 ∂μ) fun i => by fun_prop
  have hs := HasSubexponentialMGF.sum_const_mul_of_iIndepFun hind' (s := Finset.univ)
    (fun i _ => (h i).hasSubexponentialMGF_sq_sub_integral) fun i => A i i
  have hF : ((frobNorm A).toNNReal : ℝ) = frobNorm A := Real.coe_toNNReal _ (frobNorm_nonneg A)
  have hS : ((specNorm A).toNNReal : ℝ) = specNorm A := Real.coe_toNNReal _ (specNorm_nonneg A)
  refine hs.mono ?_ (Finset.sup_le fun i _ => ?_)
  · rw [← NNReal.coe_le_coe]
    push_cast
    rw [hF, frobNorm_sq_eq_sum_sq, ← Finset.sum_mul, mul_comm]
    have hd : ∑ i, ‖A i i‖ ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 := Finset.sum_le_sum fun i _ => by
      rw [Real.norm_eq_abs, sq_abs]
      exact Finset.single_le_sum (f := fun j => A i j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    gcongr
  · rw [← NNReal.coe_le_coe]
    push_cast
    rw [hS, mul_comm]
    gcongr
    exact norm_apply_le_specNorm A i i

/-- A quadratic form is its diagonal part plus its off-diagonal part. -/
private lemma quadForm_eq_sum_add [DecidableEq n] (A : Matrix n n ℝ) (x : n → ℝ) :
    quadForm A x = ∑ i, A i i * x i ^ 2 + quadForm (A - Matrix.diagonal A.diag) x := by
  rw [quadForm_sub_left, quadForm_diagonal]
  simp [Real.norm_eq_abs, sq_abs]

/-- The centred quadratic form is sub-exponential with variance proxy `98 c² ‖A‖_F²` and scale
`28 c ‖A‖`. -/
private lemma hasSubexponentialMGF_quadForm_sub_integral (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) :
    HasSubexponentialMGF (fun ω => quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ)
      (98 * c ^ 2 * (frobNorm A).toNNReal ^ 2) (28 * c * (specNorm A).toNNReal) μ := by
  classical
  have := hind.isProbabilityMeasure
  have hD := hasSubexponentialMGF_diag hind h A
  have hO := hasSubexponentialMGF_quadForm_sub_diagonal hind h A
  have hsq : ∀ i, Integrable (fun ω => A i i * X ω i ^ 2) μ := fun i =>
    (((h i).memLp 2).integrable_sq).const_mul _
  have hEQ : ∫ ω', quadForm A (X ω') ∂μ = ∑ i, A i i * ∫ ω', X ω' i ^ 2 ∂μ := by
    simp only [quadForm_eq_sum_add A]
    rw [integral_add (integrable_finsetSum _ fun i _ => hsq i) hO.integrable,
      hO.integral_eq_zero, add_zero, integral_finsetSum _ fun i _ => hsq i]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hZ : (fun ω => quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ) = fun ω =>
      (∑ i, A i i * (X ω i ^ 2 - ∫ ω', X ω' i ^ 2 ∂μ)) +
        quadForm (A - Matrix.diagonal A.diag) (X ω) := by
    ext ω
    rw [hEQ, quadForm_eq_sum_add A]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hZ]
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  refine hasSubexponentialMGF_add hD hO (p := 7 / 4) (q := 7 / 3) (by norm_num) (by norm_num)
    (by norm_num) ?_ ?_ ?_ ?_ <;> push_cast <;>
    nlinarith [mul_nonneg hc (NNReal.coe_nonneg (specNorm A).toNNReal)]

/-- The exponent of the sub-exponential tail of the centred form against the Hanson–Wright
exponent. -/
private lemma hansonWrightConstant_mul_min_le (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    hansonWrightConstant * min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)) ≤
      min (t ^ 2 / (2 * ((98 * c ^ 2 * (frobNorm A).toNNReal ^ 2 : ℝ≥0) : ℝ)))
        (t / (2 * ((28 * c * (specNorm A).toNNReal : ℝ≥0) : ℝ))) := by
  rw [hansonWrightConstant_def]
  push_cast
  rw [Real.coe_toNNReal _ (frobNorm_nonneg A), Real.coe_toNNReal _ (specNorm_nonneg A)]
  have hb : 0 ≤ t / (c * specNorm A) := div_nonneg ht (mul_nonneg c.coe_nonneg (specNorm_nonneg A))
  have h1 : t ^ 2 / (2 * (98 * c ^ 2 * frobNorm A ^ 2)) =
      1 / 196 * (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) := by
    ring
  have h2 : t / (2 * (28 * c * specNorm A)) = 1 / 56 * (t / (c * specNorm A)) := by
    ring
  rw [h1, h2]
  refine le_min ?_ ?_
  · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  · calc 1 / 196 * min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A))
        ≤ 1 / 196 * (t / (c * specNorm A)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ ≤ 1 / 56 * (t / (c * specNorm A)) := by nlinarith

/-- The upper tail of a quadratic form in independent sub-Gaussian coordinates. -/
theorem measureReal_quadForm_sub_integral_ge_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ} ≤
      rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) :=
  ((hasSubexponentialMGF_quadForm_sub_integral hind h A).measure_ge_le ht).trans
    (exp_le_exp.mpr (neg_le_neg (hansonWrightConstant_mul_min_le A ht)))

/-- The lower tail of a quadratic form in independent sub-Gaussian coordinates. -/
theorem measureReal_quadForm_sub_integral_le_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ ≤ -t} ≤
      rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) :=
  ((hasSubexponentialMGF_quadForm_sub_integral hind h A).measure_le_le ht).trans
    (exp_le_exp.mpr (neg_le_neg (hansonWrightConstant_mul_min_le A ht)))

/-- **The Hanson–Wright inequality** ([Vershynin2018], Theorem 6.2.1).
Result: hanson-wright -/
theorem measureReal_abs_quadForm_sub_integral_ge_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ|} ≤
      2 * rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) :=
  ((hasSubexponentialMGF_quadForm_sub_integral hind h A).measure_abs_ge_le ht).trans
    (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (neg_le_neg (hansonWrightConstant_mul_min_le A ht))) zero_le_two)

end NLAlib
