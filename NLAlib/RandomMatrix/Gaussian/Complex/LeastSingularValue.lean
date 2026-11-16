/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.Matrix.Perturbation.Pseudospectrum

/-!
# The smallest singular value of a complex Gaussian matrix

Small-ball bounds for standard complex Gaussian vectors and matrices
(`NLAlib.complexGaussianVector`, `NLAlib.complexGaussianMatrix`): a projection of a Gaussian
vector onto a nonzero subspace has a small norm with probability quadratic in the radius, and so
the smallest singular value $\sigma_{\min}$ of an $r \times r$ standard complex Gaussian matrix
has $\mathbb{P}[\sigma_{\min} \le x] \le \min(r^2, e\,r)\,x^2$, against Edelman's exact law
$1 - e^{-r x^2}$ [Edelman1988]. The bound $e\,r x^2$ is the probe argument of
[SankarSpielmanTeng2006, Lemma 3.2]: an independent Gaussian probe $\mathbf{g}$ sees
$\|\mathbf{G}^{-1}\|_2$ in $\|\mathbf{G}^{-1}\mathbf{g}\|$ with probability at least $e^{-1}$
(`NLAlib.measureReal_norm_sq_ge_le_of_hasLaw_complexGaussian`).

## Main results

* `NLAlib.measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector`: small ball of a
  projection.
* `NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`: Lemma 3.1, with
  $r^2x^2$.
* `NLAlib.measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix`: the probe
  bound $e\,r x^2$.
* `NLAlib.measureReal_norm_dotProduct_le_le_of_hasLaw_complexGaussianVector`: anti-concentration
  in a fixed direction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n]

/-- The disk of radius $s$ has mass at most $s^2$ under a standard complex Gaussian: $\sqrt2$
times its real and imaginary parts form a standard Gaussian vector of dimension $2$. -/
private theorem complexGaussian_real_closedBall_le {s : ℝ} (hs : 0 ≤ s) :
    complexGaussian.real (Metric.closedBall 0 s) ≤ s ^ 2 := by
  have h1 : MeasurePreserving (fun x : ℝ => √2 * x) (gaussianReal 0 2⁻¹) (gaussianReal 0 1) := by
    refine ⟨measurable_const_mul _, ?_⟩
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp
  have h2 : MeasurePreserving Complex.measurableEquivRealProd complexGaussian
      ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)) :=
    (MeasurePreserving.symm Complex.measurableEquivRealProd.symm
      ⟨Complex.measurableEquivRealProd.symm.measurable, rfl⟩)
  have hΦ := ((measurePreserving_finTwoArrow (gaussianReal 0 1)).symm.comp
    (h1.prod h1)).comp h2
  have key := measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector hΦ.hasLaw
    (u := 2 * s ^ 2) (by positivity)
  refine (le_of_eq (congrArg complexGaussian.real ?_)).trans (key.trans (le_of_eq ?_))
  · ext z
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq, Function.comp_apply]
    rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq, Fin.sum_univ_two]
    simp only [Complex.measurableEquivRealProd_apply, Prod.map_apply,
      MeasurableEquiv.finTwoArrow_symm_apply, Fin.cons_zero, Fin.cons_one, mul_pow,
      Real.sq_sqrt zero_le_two]
    rw [← sq_le_sq₀ (norm_nonneg z) hs, Complex.sq_norm, Complex.normSq_apply]
    constructor <;> intro h <;> nlinarith
  · norm_num

/-- Small ball of a projected complex Gaussian vector: for a standard complex Gaussian vector
$\mathbf{g}$, a nonzero orthogonal projector $\mathbf{\Pi}$ and $s \ge 0$,
$\mathbb{P}[\|\mathbf{\Pi}\mathbf{g}\| \le s] \le s^2$. A complex Gaussian has two real degrees of
freedom per coordinate: $\lvert z \rvert^2$ is exponential, $\mathbb{P}[\lvert z \rvert \le s] =
1 - e^{-s^2} \le s^2$. No printed source. -/
theorem measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector {g : Ω → n → ℂ}
    (hg : HasLaw g (complexGaussianVector n) μ) {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (hP₀ : P ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ‖WithLp.toLp 2 (P *ᵥ g ω)‖ ≤ s} ≤ s ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure_iff.2 inferInstance
  -- a unit vector `w` in the range of `P`
  obtain ⟨v, hv⟩ : ∃ v, P *ᵥ v ≠ 0 := by
    by_contra! h
    exact hP₀ (Matrix.ext_iff_mulVec.mpr fun x => by rw [h x, Matrix.zero_mulVec])
  have hu : ‖WithLp.toLp 2 (P *ᵥ v)‖ ≠ 0 := by simpa using hv
  set w : n → ℂ := ((‖WithLp.toLp 2 (P *ᵥ v)‖ : ℂ)⁻¹) • (P *ᵥ v) with hw_def
  have hw : ‖WithLp.toLp 2 w‖ = 1 := by simp [hw_def, norm_smul, hu]
  have hPw : Pᴴ *ᵥ w = w := by
    rw [hP.conjTranspose_eq, hw_def, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hP.mul_self]
  -- `w` as a one-column frame, and `g` as a one-column matrix
  let V : Matrix n Unit ℂ := Matrix.of fun i _ => w i
  have hV : HasOrthonormalCols V := by
    ext a b
    have h1 := EuclideanSpace.inner_toLp_toLp w w
    rw [inner_self_eq_norm_sq_to_K, hw] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply,
      Matrix.one_apply_eq]
    rw [dotProduct] at h1
    simpa [mul_comm] using h1.symm
  have hG : HasLaw (fun ω => Matrix.of fun i (_ : Unit) => g ω i)
      (complexGaussianMatrix n Unit) μ :=
    (measurePreserving_pi _ _ fun _ =>
      (measurePreserving_funUnique complexGaussian Unit).symm).comp_hasLaw hg
  have hz : HasLaw (fun ω => (Vᴴ * Matrix.of fun i (_ : Unit) => g ω i) () ())
      complexGaussian μ :=
    ((measurePreserving_funUnique complexGaussian Unit).comp
      (measurePreserving_funUnique (complexGaussianVector Unit) Unit)).comp_hasLaw
      (hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix hG hV)
  calc μ.real {ω | ‖WithLp.toLp 2 (P *ᵥ g ω)‖ ≤ s}
      ≤ μ.real {ω | ‖(Vᴴ * Matrix.of fun i (_ : Unit) => g ω i) () ()‖ ≤ s} :=
        measureReal_mono fun ω hω => by
          simp only [Set.mem_ofPred_eq] at hω ⊢
          have h1 : (Vᴴ * Matrix.of fun i (_ : Unit) => g ω i) () () =
              inner ℂ (WithLp.toLp 2 w) (WithLp.toLp 2 (P *ᵥ g ω)) := by
            rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.dotProduct_mulVec,
              ← Matrix.conjTranspose_conjTranspose P, ← Matrix.star_mulVec, hPw]
            rfl
          rw [h1]
          refine (norm_inner_le_norm _ _).trans ?_
          rwa [hw, one_mul]
    _ = complexGaussian.real (Metric.closedBall 0 s) := by
      rw [hz.measureReal_eq (p := fun z => ‖z‖ ≤ s) (measurableSet_le measurable_norm
        measurable_const)]
      congr 1
      ext z
      simp
    _ ≤ s ^ 2 := complexGaussian_real_closedBall_le hs

/-- The distance from column $j$ to the span of the other columns is at most the norm of any
combination of the columns with coefficient $1$ on column $j$. -/
private theorem iInf_norm_add_mulVec_le_iInf {r : Type*} [Fintype r] [DecidableEq r]
    (A : Matrix r r ℂ) (j : r) :
    ⨅ z : {j' // j' ≠ j} → ℂ, ‖WithLp.toLp 2 ((fun i => A i j) +
      A.submatrix id (Subtype.val : {j' // j' ≠ j} → r) *ᵥ z)‖ ≤
      ⨅ x : {x : r → ℂ // x j = 1}, ‖WithLp.toLp 2 (A *ᵥ x.1)‖ := by
  have : Nonempty {x : r → ℂ // x j = 1} := ⟨⟨Pi.single j 1, by simp⟩⟩
  refine le_ciInf fun ⟨x, hx⟩ => (ciInf_le ⟨0, ?_⟩ fun j' => x j'.1).trans_eq ?_
  · rintro _ ⟨z, rfl⟩
    positivity
  · congr 2
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.submatrix_apply, id]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j, hx, mul_one]

/-- The residual of $\mathbf{g}$ off the range of $\mathbf{Y}$ is at most its distance to
that range. -/
private theorem norm_one_sub_rangeProjector_mulVec_le_iInf {r q : Type*} [Fintype r]
    [Fintype q] [DecidableEq r] (Y : Matrix r q ℂ) (g : r → ℂ) :
    ‖WithLp.toLp 2 ((1 - rangeProjector Y) *ᵥ g)‖ ≤
      ⨅ z : q → ℂ, ‖WithLp.toLp 2 (g + Y *ᵥ z)‖ := by
  have hQY : (1 - rangeProjector Y) * Y = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_self, sub_self]
  refine le_ciInf fun z => ?_
  calc _ = ‖WithLp.toLp 2 ((1 - rangeProjector Y) *ᵥ (g + Y *ᵥ z))‖ := by
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hQY, Matrix.zero_mulVec, add_zero]
    _ ≤ _ := (isStarProjection_rangeProjector Y).one_sub.norm_toLp_mulVec_le _

/-- The projector off the range of a matrix with fewer columns than rows is nonzero. -/
private theorem one_sub_rangeProjector_ne_zero {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] (Y : Matrix r q ℂ) (h : Fintype.card q < Fintype.card r) :
    1 - rangeProjector Y ≠ 0 := by
  intro h0
  have h1 := Matrix.rank_mul_le_left Y (pinv Y)
  rw [mul_pinv, ← sub_eq_zero.mp h0, Matrix.rank_one] at h1
  exact absurd (h1.trans (Matrix.rank_le_card_width Y)) (not_le.mpr h)

/-- Column $j$ of a standard complex Gaussian square matrix is within $s$ of the span of the other
columns with probability at most $s^2$: condition on the other columns, which are independent of
it. -/
private theorem measureReal_iInf_norm_add_mulVec_le_le {r : Type*} [Fintype r]
    [DecidableEq r] {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ) (j : r)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ⨅ z : {j' // j' ≠ j} → ℂ, ‖WithLp.toLp 2 ((fun i => G ω i j) +
      (G ω).submatrix id (Subtype.val : {j' // j' ≠ j} → r) *ᵥ z)‖ ≤ s} ≤ s ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  -- split the matrix into column `j` and the other columns, which are independent
  let : Fintype {j' // j' = j} := Subtype.fintype _
  have h1 : MeasurePreserving (fun x : {j' // j' = j} → ℂ => x ⟨j, rfl⟩)
      (Measure.pi fun _ => complexGaussian) complexGaussian := by
    convert measurePreserving_funUnique complexGaussian {j' // j' = j}
    exact congrArg _ (Subsingleton.elim _ _)
  have hΨ := ((measurePreserving_pi _ _ fun _ => h1).prod
      (MeasurePreserving.id (Measure.pi fun _ : r =>
        Measure.pi fun _ : {j' // ¬j' = j} => complexGaussian))).comp
    ((measurePreserving_arrowProdEquivProdArrow _ _ r _ _).comp
      (measurePreserving_pi _ _ fun _ =>
        measurePreserving_piEquivPiSubtypeProd (fun _ : r => complexGaussian) (· = j)))
  set S : Set ((r → ℂ) × (r → {j' // ¬j' = j} → ℂ)) :=
    {p | ⨅ z : {j' // ¬j' = j} → ℂ, ‖WithLp.toLp 2 (p.1 + Matrix.of p.2 *ᵥ z)‖ ≤ s}
  have hS : MeasurableSet S := by
    refine measurableSet_le (UpperSemicontinuous.measurable (upperSemicontinuous_ciInf
      (fun p => ⟨0, ?_⟩) fun z => Continuous.upperSemicontinuous ?_)) measurable_const
    · rintro _ ⟨z, rfl⟩
      positivity
    · fun_prop
  calc _ = ((complexGaussianVector r).prod
        (Measure.pi fun _ : r => Measure.pi fun _ : {j' // ¬j' = j} => complexGaussian)).real S :=
        (hΨ.comp_hasLaw hG).measureReal_eq (p := (· ∈ S)) hS
    _ ≤ s ^ 2 := by
      rw [measureReal_def, Measure.prod_apply_symm hS]
      refine ENNReal.toReal_le_of_le_ofReal (sq_nonneg s) ?_
      refine (lintegral_mono fun y => ?_).trans_eq (by rw [lintegral_const, measure_univ, mul_one])
      have h := measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector HasLaw.id
        (isStarProjection_rangeProjector (Matrix.of y)).one_sub
        (one_sub_rangeProjector_ne_zero _ (Fintype.card_subtype_lt (x := j) (by simp))) hs
      calc _ ≤ complexGaussianVector r
            {x | ‖WithLp.toLp 2 ((1 - rangeProjector (Matrix.of y)) *ᵥ x)‖ ≤ s} :=
            measure_mono fun x hx => (norm_one_sub_rangeProjector_mulVec_le_iInf _ x).trans hx
        _ = ENNReal.ofReal ((complexGaussianVector r).real
            {x | ‖WithLp.toLp 2 ((1 - rangeProjector (Matrix.of y)) *ᵥ x)‖ ≤ s}) :=
            (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (s ^ 2) := ENNReal.ofReal_le_ofReal h

/-- **Smallest singular value of a square complex Gaussian matrix** (Lemma 3.1): for a standard
complex Gaussian $r \times r$ matrix $\mathbf{G}$, $k + 1 = \lvert r \rvert$ and $x \ge 0$,
$$\mathbb{P}[\sigma_k(\mathbf{G}) \le x] \le \lvert r \rvert^2 x^2 \,.$$
[Shah2024, Lemma 3.1], citing [Edelman1988, Theorem 3.2]: there $(\lvert r \rvert/2)x^2$ (the exact
law of $\sigma_{\min}$); this elementary bound loses a factor $2\lvert r \rvert$, which costs
$O(\log n)$ bits in the precision of the eigensolver;
`NLAlib.measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix` loses only
the factor $2e$.
Result: complex-gaussian-least-singular-value -/
theorem measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ) {k : ℕ}
    (hk : k + 1 = Fintype.card r) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (G ω) k ≤ x} ≤ (Fintype.card r : ℝ) ^ 2 * x ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  calc μ.real {ω | singularValues (G ω) k ≤ x}
      ≤ μ.real (⋃ j, {ω | ⨅ z : {j' // j' ≠ j} → ℂ, ‖WithLp.toLp 2 ((fun i => G ω i j) +
          (G ω).submatrix id (Subtype.val : {j' // j' ≠ j} → r) *ᵥ z)‖ ≤
            √(Fintype.card r) * x}) := measureReal_mono fun ω hω => by
        obtain ⟨j, hj⟩ := exists_iInf_norm_mulVec_le_of_singularValues_le (G ω) hk hω
        exact Set.mem_iUnion.2 ⟨j, (iInf_norm_add_mulVec_le_iInf _ j).trans hj⟩
    _ ≤ ∑ j : r, (√(Fintype.card r) * x) ^ 2 := (measureReal_iUnion_fintype_le _).trans
        (Finset.sum_le_sum fun j _ =>
          measureReal_iInf_norm_add_mulVec_le_le hG j (by positivity))
    _ = (Fintype.card r : ℝ) ^ 2 * x ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg _)]
      ring

/-- The realification $z \mapsto (\sqrt2\,\Re z, \sqrt2\,\Im z)$ maps a standard complex Gaussian
to a standard Gaussian vector of dimension $2$. -/
private theorem measurePreserving_complexGaussian_finTwo :
    MeasurePreserving (fun z : ℂ => (MeasurableEquiv.finTwoArrow.symm (√2 * z.re, √2 * z.im)))
      complexGaussian (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
  have h1 : MeasurePreserving (fun x : ℝ => √2 * x) (gaussianReal 0 2⁻¹) (gaussianReal 0 1) := by
    refine ⟨measurable_const_mul _, ?_⟩
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp
  have h2 : MeasurePreserving Complex.measurableEquivRealProd complexGaussian
      ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)) :=
    (MeasurePreserving.symm Complex.measurableEquivRealProd.symm
      ⟨Complex.measurableEquivRealProd.symm.measurable, rfl⟩)
  exact ((measurePreserving_finTwoArrow (gaussianReal 0 1)).symm.comp (h1.prod h1)).comp h2

private theorem sum_sq_finTwo_eq (z : ℂ) :
    ∑ i, (MeasurableEquiv.finTwoArrow.symm (√2 * z.re, √2 * z.im) : Fin 2 → ℝ) i ^ 2 =
      2 * ‖z‖ ^ 2 := by
  simp only [Fin.sum_univ_two, MeasurableEquiv.finTwoArrow_symm_apply, Fin.cons_zero,
    Fin.cons_one, mul_pow, Real.sq_sqrt zero_le_two, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- $\mathbb{P}[1 \le \lvert z\rvert^2] \ge e^{-1}$ for a standard complex Gaussian $z$:
$2\lvert z \rvert^2$ is exponential of rate $1/2$. -/
private theorem exp_neg_one_le_complexGaussian_real :
    Real.exp (-1) ≤ complexGaussian.real {z | 1 ≤ ‖z‖ ^ 2} := by
  have hY := hasLaw_sum_sq_of_hasLaw_pi_gaussianReal measurePreserving_complexGaussian_finTwo.hasLaw
  rw [Fintype.card_fin, show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num] at hY
  have hI : ∫ x in Set.Ioi (2 : ℝ), (1 / 2) * Real.exp ((-1 / 2) * x) = Real.exp (-1) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
    norm_num
    ring
  have htail : (gammaMeasure 1 (1 / 2)).real (Set.Ioi 2) = Real.exp (-1) := by
    rw [measureReal_def, gammaMeasure, withDensity_apply _ measurableSet_Ioi,
      setLIntegral_congr_fun measurableSet_Ioi (g := fun x => ENNReal.ofReal
        ((1 / 2) * Real.exp ((-1 / 2) * x))) (fun x hx => by
          rw [gammaPDF_of_nonneg (le_of_lt (lt_trans two_pos hx))]
          congr 1
          simp only [Real.rpow_one, Real.Gamma_one, sub_self, Real.rpow_zero]
          ring_nf),
      ← ofReal_integral_eq_lintegral_ofReal, hI, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    · exact (integrableOn_exp_mul_Ioi (by norm_num) _).const_mul _
    · exact Filter.Eventually.of_forall fun x => by positivity
  calc Real.exp (-1) = (gammaMeasure 1 (1 / 2)).real {y | 2 < y} := htail.symm
    _ = _ := (hY.measureReal_eq measurableSet_Ioi).symm
    _ ≤ _ := measureReal_mono fun z hz => by
      simp only [Set.mem_ofPred_eq, sum_sq_finTwo_eq] at hz ⊢
      linarith

/-- $\mathbb{E}\lvert z\rvert^2 = 1$ for a standard complex Gaussian $z$. -/
private theorem lintegral_ofReal_norm_sq_complexGaussian :
    ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂complexGaussian = 1 := by
  have h1 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero (by fun_prop) (by simp [integral_id_gaussianReal])] at h
    simpa using h
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have heval : ∀ i : Fin 2, ∫⁻ y : Fin 2 → ℝ, ENNReal.ofReal (y i ^ 2)
      ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) = 1 := fun i => by
    rw [(measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i).lintegral_comp
      (f := fun x => ENNReal.ofReal (x ^ 2)) (by fun_prop),
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => by positivity), h1, ENNReal.ofReal_one]
  calc ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂complexGaussian
      = ∫⁻ z, ENNReal.ofReal (2⁻¹) * ∑ i, ENNReal.ofReal
          ((MeasurableEquiv.finTwoArrow.symm (√2 * z.re, √2 * z.im) : Fin 2 → ℝ) i ^ 2)
          ∂complexGaussian := by
        refine lintegral_congr fun z => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _, ← ENNReal.ofReal_mul
          (by norm_num), sum_sq_finTwo_eq]
        congr 1
        ring
    _ = ENNReal.ofReal (2⁻¹) * ∑ i : Fin 2, ∫⁻ y : Fin 2 → ℝ, ENNReal.ofReal (y i ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum _ fun i _ => by fun_prop]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        exact measurePreserving_complexGaussian_finTwo.lintegral_comp
          (f := fun y : Fin 2 → ℝ => ENNReal.ofReal (y i ^ 2)) (by fun_prop)
    _ = 1 := by
      simp only [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- $\mathbb{E}\|\mathbf{g}\|^2 = \lvert r \rvert$ for a standard complex Gaussian vector. -/
private theorem lintegral_ofReal_norm_sq_complexGaussianVector (r : Type*) [Fintype r] :
    ∫⁻ v, ENNReal.ofReal (‖WithLp.toLp 2 v‖ ^ 2) ∂complexGaussianVector r =
      (Fintype.card r : ENNReal) := by
  calc ∫⁻ v, ENNReal.ofReal (‖WithLp.toLp 2 v‖ ^ 2) ∂complexGaussianVector r
      = ∫⁻ v, ∑ i, ENNReal.ofReal (‖v i‖ ^ 2) ∂complexGaussianVector r := by
        refine lintegral_congr fun v => ?_
        rw [EuclideanSpace.norm_sq_eq, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
    _ = ∑ i : r, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂complexGaussian := by
        rw [lintegral_finsetSum _ fun i _ => by fun_prop]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (measurePreserving_eval (fun _ : r => complexGaussian) i).lintegral_comp
          (f := fun z => ENNReal.ofReal (‖z‖ ^ 2)) (by fun_prop)
    _ = _ := by
        rw [lintegral_ofReal_norm_sq_complexGaussian, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]

/-- The transpose of a standard complex Gaussian matrix is standard complex Gaussian. -/
private theorem hasLaw_transpose_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) :
    HasLaw (fun ω => (G ω)ᵀ) (complexGaussianMatrix n m) μ :=
  ((measurePreserving_curry_pi (ν := fun (_ : n) (_ : m) => complexGaussian)).comp
    ((measurePreserving_arrowCongr' (fun _ : m × n => complexGaussian)
      (fun _ : n × m => complexGaussian) (Equiv.prodComm m n) (MeasurableEquiv.refl ℂ)
      fun _ => MeasurePreserving.id _).comp
    (measurePreserving_curry_pi (ν := fun (_ : m) (_ : n) => complexGaussian)).symm)).comp_hasLaw
    hG

/-- Right multiplication by a unitary matrix preserves the standard complex Gaussian law. -/
private theorem hasLaw_mul_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    [DecidableEq r] {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ)
    {V : Matrix r r ℂ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => G ω * V) (complexGaussianMatrix r r) μ := by
  have hW : HasOrthonormalCols Vᴴᵀ := by
    rw [hasOrthonormalCols_iff, show Vᴴᵀᴴ = Vᵀ by ext; simp, ← Matrix.transpose_mul,
      hV.conjTranspose_mul_self, Matrix.transpose_one]
  convert hasLaw_transpose_of_hasLaw_complexGaussianMatrix
    (hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix
      (hasLaw_transpose_of_hasLaw_complexGaussianMatrix hG) hW) using 2 with ω
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, show Vᴴᵀᴴᵀ = V by ext; simp]

/-- A unit vector is column $i$ of a unitary matrix. -/
private theorem exists_hasOrthonormalCols_col_eq {r : Type*} [Fintype r] [DecidableEq r]
    {u : r → ℂ} (hu : ‖WithLp.toLp 2 u‖ = 1) (i : r) :
    ∃ V : Matrix r r ℂ, HasOrthonormalCols V ∧ ∀ a, V a i = u a := by
  set U : Matrix r {a // a = i} ℂ := Matrix.of fun a _ => u a
  have hU : HasOrthonormalCols U := by
    rw [hasOrthonormalCols_iff]
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    have h1 := EuclideanSpace.inner_toLp_toLp u u
    rw [inner_self_eq_norm_sq_to_K, hu, dotProduct] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.of_apply,
      Matrix.one_apply_eq]
    simpa [mul_comm] using h1.symm
  obtain ⟨U', hU'⟩ := hU.exists_fromCols (p := {a // ¬a = i}) (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have := Fintype.card_pos_iff.2 ⟨i⟩
    omega)
  refine ⟨(Matrix.fromCols U U').submatrix (Equiv.refl r) (Equiv.sumCompl (· = i)).symm,
    hU'.submatrix (Equiv.refl r) (Equiv.injective _), fun a => ?_⟩
  simp only [Matrix.submatrix_apply, Equiv.refl_apply]
  rw [Equiv.sumCompl_symm_apply_of_pos (p := fun x => x = i) rfl, Matrix.fromCols_apply_inl]
  rfl

/-- Column $j$ of a standard complex Gaussian square matrix is within $s$ of a combination of the
other columns with probability at most $s^2$. -/
private theorem measureReal_exists_norm_mulVec_le_le {r : Type*} [Fintype r]
    {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ) (j : r) {s : ℝ}
    (hs : 0 ≤ s) :
    μ.real {ω | ∃ y : r → ℂ, y j = 1 ∧ ‖WithLp.toLp 2 (G ω *ᵥ y)‖ ≤ s} ≤ s ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  refine (measureReal_mono fun ω hω => ?_).trans (measureReal_iInf_norm_add_mulVec_le_le hG j hs)
  obtain ⟨y, hy, hyle⟩ := hω
  simp only [Set.mem_ofPred_eq]
  refine (ciInf_le ⟨0, ?_⟩ fun j' => y j'.1).trans (le_of_eq_of_le ?_ hyle)
  · rintro _ ⟨z, rfl⟩
    positivity
  · congr 2
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.submatrix_apply, id]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j, hy, mul_one]

/-- Cauchy–Schwarz for the bilinear dot product of complex vectors. -/
private theorem norm_dotProduct_le {r : Type*} [Fintype r] (a b : r → ℂ) :
    ‖a ⬝ᵥ b‖ ≤ ‖WithLp.toLp 2 a‖ * ‖WithLp.toLp 2 b‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 (star a)) (WithLp.toLp 2 b)
  rw [EuclideanSpace.inner_toLp_toLp, star_star, dotProduct_comm] at h
  refine h.trans_eq ?_
  congr 1
  simp [EuclideanSpace.norm_eq]

/-- For an invertible $\mathbf{A}$ and $\mathbf{a} = \mathbf{A}^{-\mathsf{T}}\mathbf{g} \ne 0$
there is $\mathbf{x}$ with $\mathbf{g}^{\mathsf{T}}\mathbf{x} = 1$ and
$\|\mathbf{A}\mathbf{x}\| = 1/\|\mathbf{a}\|$. -/
private theorem exists_dotProduct_eq_one_and_norm_mulVec_le {r : Type*} [Fintype r]
    [DecidableEq r] (A : Matrix r r ℂ) (hA : IsUnit A.det) (g : r → ℂ)
    (ha : Matrix.vecMul g A⁻¹ ≠ 0) :
    ∃ x : r → ℂ, g ⬝ᵥ x = 1 ∧
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ 1 / ‖WithLp.toLp 2 (Matrix.vecMul g A⁻¹)‖ := by
  set a := Matrix.vecMul g A⁻¹
  have hn : ‖WithLp.toLp 2 a‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact fun h => ha (congrArg WithLp.ofLp h)
  have hstar : ‖WithLp.toLp 2 (star a)‖ = ‖WithLp.toLp 2 a‖ := by
    simp [EuclideanSpace.norm_eq]
  have hdot : a ⬝ᵥ star a = (‖WithLp.toLp 2 a‖ : ℂ) ^ 2 := by
    have h1 := EuclideanSpace.inner_toLp_toLp a a
    rw [inner_self_eq_norm_sq_to_K] at h1
    exact h1.symm
  refine ⟨A⁻¹ *ᵥ (((‖WithLp.toLp 2 a‖ : ℂ) ^ 2)⁻¹ • star a), ?_, ?_⟩
  · rw [Matrix.dotProduct_mulVec, dotProduct_smul, hdot, smul_eq_mul,
      inv_mul_cancel₀ (by exact_mod_cast pow_ne_zero 2 hn)]
  · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec, WithLp.toLp_smul,
      norm_smul, hstar, norm_inv, norm_pow, Complex.norm_real, norm_norm]
    exact le_of_eq (by field_simp)

/-- For a fixed probe $\mathbf{g}$ and $T > 0$, $\mathbb{P}[T \le
\|\mathbf{G}^{-\mathsf{T}}\mathbf{g}\|^2] \le \|\mathbf{g}\|^2/T$. -/
private theorem complexGaussianMatrix_real_le_norm_vecMul_inv_sq_le {r : Type*} [Fintype r]
    [DecidableEq r] (g : r → ℂ) {T : ℝ} (hT : 0 < T) :
    (complexGaussianMatrix r r).real {A | T ≤ ‖WithLp.toLp 2 (Matrix.vecMul g A⁻¹)‖ ^ 2} ≤
      ‖WithLp.toLp 2 g‖ ^ 2 / T := by
  rcases eq_or_ne g 0 with rfl | hg
  · refine le_of_eq_of_le (by
      rw [show {A : Matrix r r ℂ | T ≤ ‖WithLp.toLp 2 (Matrix.vecMul 0 A⁻¹)‖ ^ 2} = ∅ from
        Set.eq_empty_of_forall_notMem fun A hA => by simp at hA; linarith, measureReal_empty])
      (by positivity)
  obtain ⟨j₀, -⟩ := Function.ne_iff.1 hg
  set n := ‖WithLp.toLp 2 g‖
  have hn : 0 < n := by
    rw [norm_pos_iff]
    exact fun h => hg (congrArg WithLp.ofLp h)
  have hu : ‖WithLp.toLp 2 ((n : ℂ)⁻¹ • star g)‖ = 1 := by
    rw [WithLp.toLp_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      show ‖WithLp.toLp 2 (star g)‖ = n by simp [n, EuclideanSpace.norm_eq], inv_mul_cancel₀ hn.ne']
  obtain ⟨V, hV, hVcol⟩ := exists_hasOrthonormalCols_col_eq hu j₀
  have hVV : V * Vᴴ = 1 := mul_eq_one_comm.1 hV.conjTranspose_mul_self
  refine (measureReal_mono fun A hA => ?_).trans ((measureReal_exists_norm_mulVec_le_le
    (hasLaw_mul_of_hasLaw_complexGaussianMatrix HasLaw.id hV) j₀ (s := n / √T)
    (by positivity)).trans_eq (by rw [div_pow, Real.sq_sqrt hT.le]))
  simp only [Set.mem_ofPred_eq] at hA ⊢
  have ha : Matrix.vecMul g A⁻¹ ≠ 0 := fun h => by simp [h] at hA; linarith
  have hdet : IsUnit A.det := by
    by_contra h
    exact ha (by rw [Matrix.nonsing_inv_apply_not_isUnit A h, Matrix.vecMul_zero])
  obtain ⟨x, hgx, hAx⟩ := exists_dotProduct_eq_one_and_norm_mulVec_le A hdet g ha
  have hsq : √T ≤ ‖WithLp.toLp 2 (Matrix.vecMul g A⁻¹)‖ := Real.sqrt_le_iff.2 ⟨by positivity, hA⟩
  refine ⟨(n : ℂ) • (Vᴴ *ᵥ x), ?_, ?_⟩
  · rw [← hgx, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, dotProduct,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_apply, hVcol]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', Pi.star_apply, star_inv₀,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  · rw [Matrix.mulVec_smul, show (id A * V) *ᵥ (Vᴴ *ᵥ x) = A *ᵥ x by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hVV, Matrix.mul_one]; rfl,
      WithLp.toLp_smul, norm_smul, Complex.norm_real, norm_norm, div_eq_mul_inv]
    gcongr
    exact hAx.trans (by simpa using inv_anti₀ (by positivity) hsq)

/-- If $\mathbf{A}$ is invertible and $\|\mathbf{A}\mathbf{w}\| \le x$ for a unit $\mathbf{w}$,
then $\mathbb{P}[1/x^2 \le \|\mathbf{A}^{-\mathsf{T}}\mathbf{g}\|^2] \ge e^{-1}$ for a standard
complex Gaussian vector $\mathbf{g}$. -/
private theorem exp_neg_one_le_complexGaussianVector_real {r : Type*} [Fintype r]
    [DecidableEq r] (A : Matrix r r ℂ) (hA : IsUnit A.det) {w : r → ℂ}
    (hw : ‖WithLp.toLp 2 w‖ = 1) {x : ℝ} (hx : 0 < x) (hAw : ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ x) :
    Real.exp (-1) ≤ (complexGaussianVector r).real
      {v | 1 / x ^ 2 ≤ ‖WithLp.toLp 2 (Matrix.vecMul v A⁻¹)‖ ^ 2} := by
  have : IsProbabilityMeasure (complexGaussianVector r) := inferInstance
  -- `v ⬝ᵥ w` is a standard complex Gaussian: one column of a unitary invariance
  set V : Matrix r Unit ℂ := Matrix.of fun i _ => star (w i)
  have hV : HasOrthonormalCols V := by
    rw [hasOrthonormalCols_iff]
    ext a b
    have h1 := EuclideanSpace.inner_toLp_toLp w w
    rw [inner_self_eq_norm_sq_to_K, hw, dotProduct] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply,
      Matrix.one_apply_eq, star_star]
    simpa using h1.symm
  have hM : HasLaw (fun v : r → ℂ => Matrix.of fun i (_ : Unit) => v i)
      (complexGaussianMatrix r Unit) (complexGaussianVector r) :=
    (measurePreserving_pi _ _ fun _ =>
      (measurePreserving_funUnique complexGaussian Unit).symm).comp_hasLaw HasLaw.id
  have hz : HasLaw (fun v : r → ℂ => (Vᴴ * Matrix.of fun i (_ : Unit) => v i) () ())
      complexGaussian (complexGaussianVector r) :=
    ((measurePreserving_funUnique complexGaussian Unit).comp
      (measurePreserving_funUnique (complexGaussianVector Unit) Unit)).comp_hasLaw
      (hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix hM hV)
  calc Real.exp (-1) ≤ complexGaussian.real {z | 1 ≤ ‖z‖ ^ 2} :=
        exp_neg_one_le_complexGaussian_real
    _ = (complexGaussianVector r).real
        {v | 1 ≤ ‖(Vᴴ * Matrix.of fun i (_ : Unit) => v i) () ()‖ ^ 2} :=
        (hz.measureReal_eq (p := fun z => 1 ≤ ‖z‖ ^ 2)
          (measurableSet_le measurable_const (by fun_prop))).symm
    _ ≤ _ := measureReal_mono fun v hv => by
      simp only [Set.mem_ofPred_eq] at hv ⊢
      have hvw : (Vᴴ * Matrix.of fun i (_ : Unit) => v i) () () =
          Matrix.vecMul v A⁻¹ ⬝ᵥ (A *ᵥ w) := by
        rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA,
          Matrix.one_mulVec, dotProduct_comm]
        simp [V, Matrix.mul_apply, dotProduct]
      rw [hvw] at hv
      have hcs := norm_dotProduct_le (Matrix.vecMul v A⁻¹) (A *ᵥ w)
      rw [div_le_iff₀ (by positivity)]
      have h0 := norm_nonneg (Matrix.vecMul v A⁻¹ ⬝ᵥ (A *ᵥ w))
      have h1 := norm_nonneg (WithLp.toLp 2 (Matrix.vecMul v A⁻¹))
      have h2 := norm_nonneg (WithLp.toLp 2 (A *ᵥ w))
      nlinarith [mul_le_mul_of_nonneg_left hAw h1]

/-- Markov and Fubini for the probe: the matrices $\mathbf{A}$ whose inverse is seen with
probability at least $e^{-1}$ by a Gaussian probe, $\|\mathbf{v}^{\mathsf T}\mathbf{A}^{-1}\|^2
\ge 1/x^2$, have mass at most $e\,\lvert r \rvert x^2$. -/
private theorem complexGaussianMatrix_real_exp_neg_one_le_le {r : Type*} [Fintype r]
    [DecidableEq r] {x : ℝ} (hx : 0 < x) :
    (complexGaussianMatrix r r).real {A | ENNReal.ofReal (Real.exp (-1)) ≤
      complexGaussianVector r (Prod.mk A ⁻¹'
        {p : Matrix r r ℂ × (r → ℂ) | 1 / x ^ 2 ≤ ‖WithLp.toLp 2 (Matrix.vecMul p.2 p.1⁻¹)‖ ^ 2})} ≤
      Real.exp 1 * (Fintype.card r : ℝ) * x ^ 2 := by
  set γ := complexGaussianVector r
  set ρ := complexGaussianMatrix r r
  set S : Set (Matrix r r ℂ × (r → ℂ)) :=
    {p | 1 / x ^ 2 ≤ ‖WithLp.toLp 2 (Matrix.vecMul p.2 p.1⁻¹)‖ ^ 2}
  have hS : MeasurableSet S := by
    have hv : Measurable fun q : (r → ℂ) × Matrix r r ℂ => Matrix.vecMul q.1 q.2 :=
      (continuous_fst.matrix_vecMul continuous_snd).measurable
    exact measurableSet_le measurable_const ((measurable_norm.comp
      ((PiLp.continuous_toLp 2 _).measurable.comp
        (hv.comp (measurable_snd.prodMk measurable_fst.matrix_inv)))).pow_const 2)
  set B : Set (Matrix r r ℂ) := {A | ENNReal.ofReal (Real.exp (-1)) ≤ γ (Prod.mk A ⁻¹' S)}
  -- Markov in `A`, Fubini, then the bound for a fixed probe `v`
  have hv : ∀ v, ρ ((fun A => (A, v)) ⁻¹' S) ≤
      ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (‖WithLp.toLp 2 v‖ ^ 2) := fun v => by
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal
      ((complexGaussianMatrix_real_le_norm_vecMul_inv_sq_le v (by positivity)).trans_eq ?_)
    field_simp
  have hE : ENNReal.ofReal (Real.exp (-1)) * ρ B ≤
      ENNReal.ofReal (x ^ 2) * (Fintype.card r : ENNReal) := by
    calc ENNReal.ofReal (Real.exp (-1)) * ρ B
        ≤ ∫⁻ A, γ (Prod.mk A ⁻¹' S) ∂ρ :=
          mul_meas_ge_le_lintegral₀ (measurable_measure_prodMk_left hS).aemeasurable _
      _ = ∫⁻ v, ρ ((fun A => (A, v)) ⁻¹' S) ∂γ := by
          rw [← Measure.prod_apply hS, Measure.prod_apply_symm hS]
      _ ≤ ∫⁻ v, ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (‖WithLp.toLp 2 v‖ ^ 2) ∂γ :=
          lintegral_mono hv
      _ = _ := by
          rw [lintegral_const_mul _ (by fun_prop),
            lintegral_ofReal_norm_sq_complexGaussianVector]
  have hR := ENNReal.toReal_mono (by finiteness) hE
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast, ← measureReal_def] at hR
  calc ρ.real B = Real.exp 1 * (Real.exp (-1) * ρ.real B) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp 1 * (x ^ 2 * Fintype.card r) := by gcongr
    _ = _ := by ring

/-- **Smallest singular value of a square complex Gaussian matrix, linear in the size**: for
$\mathbf{G}$ an $r \times r$ standard complex Gaussian matrix, $k + 1 = \lvert r \rvert$ and
$x \ge 0$, $\mathbb{P}[\sigma_k(\mathbf{G}) \le x] \le e\,\lvert r \rvert x^2$. Edelman's exact
law $1 - e^{-\lvert r \rvert x^2}$ (cited in [Shah2024, Lemma 3.1]) is smaller by the factor
$e$; the elementary `NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix` has
$\lvert r \rvert^2x^2$. The probe argument of [SankarSpielmanTeng2006, Lemma 3.2], complex
version. -/
theorem measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix
    {r : Type*} [Fintype r] {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ)
    {k : ℕ} (hk : k + 1 = Fintype.card r) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (G ω) k ≤ x} ≤ Real.exp 1 * (Fintype.card r : ℝ) * x ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  have h0 : μ.real {ω | singularValues (G ω) k ≤ 0} = 0 := le_antisymm (by
    simpa using measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix hG hk le_rfl)
    measureReal_nonneg
  rcases hx.eq_or_lt with rfl | hx
  · rw [h0]
    positivity
  set γ := complexGaussianVector r
  set ρ := complexGaussianMatrix r r
  set S : Set (Matrix r r ℂ × (r → ℂ)) :=
    {p | 1 / x ^ 2 ≤ ‖WithLp.toLp 2 (Matrix.vecMul p.2 p.1⁻¹)‖ ^ 2}
  have hS : MeasurableSet S := by
    have hv : Measurable fun q : (r → ℂ) × Matrix r r ℂ => Matrix.vecMul q.1 q.2 :=
      (continuous_fst.matrix_vecMul continuous_snd).measurable
    exact measurableSet_le measurable_const ((measurable_norm.comp
      ((PiLp.continuous_toLp 2 _).measurable.comp
        (hv.comp (measurable_snd.prodMk measurable_fst.matrix_inv)))).pow_const 2)
  set B : Set (Matrix r r ℂ) := {A | ENNReal.ofReal (Real.exp (-1)) ≤ γ (Prod.mk A ⁻¹' S)}
  have hB : MeasurableSet B := measurableSet_le measurable_const (measurable_measure_prodMk_left hS)
  have hsub : {ω | singularValues (G ω) k ≤ x} ⊆ {ω | singularValues (G ω) k ≤ 0} ∪ G ⁻¹' B := by
    intro ω hω
    have hG' : (0 : ℂ) • (1 : Matrix r r ℂ) - -G ω = G ω := by simp
    have hiff := fun ε => exists_norm_eq_one_and_norm_mulVec_le_iff (-G ω) 0 hk ε
    rw [hG'] at hiff
    by_cases hdet : IsUnit (G ω).det
    · right
      obtain ⟨w, hw, hAw⟩ := (hiff x).2 hω
      change ENNReal.ofReal _ ≤ γ _
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal
        (exp_neg_one_le_complexGaussianVector_real (G ω) hdet hw hx hAw)
    · left
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (by
        simpa [isUnit_iff_ne_zero] using hdet)
      have hn : ‖WithLp.toLp 2 v‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact fun h => hv0 (congrArg WithLp.ofLp h)
      refine (hiff 0).1 ⟨(‖WithLp.toLp 2 v‖ : ℂ)⁻¹ • v, ?_, ?_⟩
      · simp [norm_smul, hn]
      · simp [Matrix.mulVec_smul, hv]
  have hBle := complexGaussianMatrix_real_exp_neg_one_le_le (r := r) hx
  calc μ.real {ω | singularValues (G ω) k ≤ x}
      ≤ μ.real ({ω | singularValues (G ω) k ≤ 0} ∪ G ⁻¹' B) := measureReal_mono hsub
    _ ≤ μ.real {ω | singularValues (G ω) k ≤ 0} + μ.real (G ⁻¹' B) := measureReal_union_le _ _
    _ = ρ.real B := by rw [h0, zero_add]; exact hG.measureReal_eq (p := (· ∈ B)) hB
    _ ≤ _ := hBle

/-- **Anti-concentration of a Gaussian vector in a fixed direction**: for a standard complex
Gaussian vector $\mathbf{g}$, a unit vector $\mathbf{v}$ and $s \ge 0$,
$\mathbb{P}[\lvert\langle \mathbf{v}, \mathbf{g}\rangle\rvert \le s] \le s^2$. It replaces the
uniform direction on the sphere of [BanksGarzaVargasSrivastava2025, Lemma 5.2]: the direction of
a Gaussian vector is uniform, and its norm is controlled separately. -/
theorem measureReal_norm_dotProduct_le_le_of_hasLaw_complexGaussianVector {g : Ω → n → ℂ}
    (hg : HasLaw g (complexGaussianVector n) μ) {v : n → ℂ} (hv : ‖WithLp.toLp 2 v‖ = 1)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ‖star v ⬝ᵥ g ω‖ ≤ s} ≤ s ^ 2 := by
  sorry

end NLAlib
