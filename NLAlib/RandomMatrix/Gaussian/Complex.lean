/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Basic
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.Matrix.Spectral.LeastSingularValue
public import NLAlib.Matrix.Basic.Projector
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Complex Gaussian vectors and matrices

`NLAlib.complexGaussian` is the standard complex Gaussian law $\mathcal{N}_{\mathbb{C}}(0, 1)$ on
$\mathbb{C}$: the real and imaginary parts are independent centred Gaussians of variance $1/2$,
so that $\mathbb{E}\lvert z \rvert^2 = 1$. `NLAlib.complexGaussianVector n` and
`NLAlib.complexGaussianMatrix m n` are the laws of a vector and of a matrix with independent
standard complex Gaussian entries, written as products as the real laws
`NLAlib.gaussianVector` and `NLAlib.gaussianMatrix` are. Mathlib's `stdGaussian ℂ` is the real
two-dimensional standard Gaussian on $\mathbb{C}$, of variance $1$ in each part, which is
$\sqrt2$ times a standard complex Gaussian. These are the test matrices of randomized deflation
([Shah2024, Section 3]), whose analysis uses the norm tail of
[BanksKulkarniMukherjeeSrivastava2021] and, in place of the exact law of the smallest singular
value [Edelman1988], an elementary small-ball bound.

## Main definitions

* `NLAlib.complexGaussian`, `NLAlib.complexGaussianVector`, `NLAlib.complexGaussianMatrix`.

## Main results

* `NLAlib.isProbabilityMeasure_complexGaussian`,
  `NLAlib.isProbabilityMeasure_complexGaussianVector`,
  `NLAlib.isProbabilityMeasure_complexGaussianMatrix`.
* `NLAlib.complexGaussian_eq_map_stdGaussian`: the bridge to Mathlib.
* `NLAlib.complexGaussianMatrix_eq_map_gaussianMatrix`: the realification.
* `NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`,
  `NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix`.
* `NLAlib.measureReal_norm_sq_ge_le_of_hasLaw_complexGaussian`: the exponential tail of
  $\lvert z \rvert^2$.
* `NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`,
  `NLAlib.measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix`: Lemma 3.2, and the norm
  tail $e^{-t^2}$ from Gaussian concentration.

The smallest singular value is in `NLAlib/RandomMatrix/Gaussian/Complex/LeastSingularValue.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Matrix

namespace NLAlib

/-- The **standard complex Gaussian law** $\mathcal{N}_{\mathbb{C}}(0, 1)$: the law of
$x + iy$ for independent real $x, y \sim \mathcal{N}(0, 1/2)$. -/
noncomputable def complexGaussian : Measure ℂ :=
  ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)).map Complex.measurableEquivRealProd.symm

/-- The standard complex Gaussian law is a probability measure. -/
instance isProbabilityMeasure_complexGaussian : IsProbabilityMeasure complexGaussian :=
  Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

/-- Two independent standard real Gaussian draws divided by $\sqrt2$ give the standard
complex Gaussian law. This is the finite-product form used by Gaussian tape samplers.
No printed source. -/
theorem map_pi_fin_two_eq_complexGaussian :
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map
      (fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ)) = complexGaussian := by
  have hA : Measurable (Complex.measurableEquivRealProd.symm ∘ Prod.map (· / √2) (· / √2)) :=
    Complex.measurableEquivRealProd.symm.measurable.comp (by fun_prop)
  have hfun : (fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ)) =
      (Complex.measurableEquivRealProd.symm ∘ Prod.map (· / √2) (· / √2)) ∘
        MeasurableEquiv.finTwoArrow := rfl
  have hd : (gaussianReal 0 1).map (· / √2) = gaussianReal 0 2⁻¹ := by
    have hfn : (fun x : ℝ => x / √2) = fun x => (√2)⁻¹ * x :=
      funext fun x => div_eq_inv_mul _ _
    rw [hfn, gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.eq
      simp [mul_comm]
  rw [hfun, ← Measure.map_map hA MeasurableEquiv.finTwoArrow.measurable,
    (measurePreserving_finTwoArrow _).map_eq,
    ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), hd]
  rfl

/-- The law of a vector with independent standard complex Gaussian entries. -/
noncomputable abbrev complexGaussianVector (n : Type*) [Fintype n] : Measure (n → ℂ) :=
  Measure.pi fun _ : n => complexGaussian

/-- The complex Gaussian vector law is a probability measure. -/
instance isProbabilityMeasure_complexGaussianVector (n : Type*) [Fintype n] :
    IsProbabilityMeasure (complexGaussianVector n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : n => complexGaussian))

/-- The law of a matrix with independent standard complex Gaussian entries, written as
independent rows, each a standard complex Gaussian vector. -/
noncomputable abbrev complexGaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    Measure (Matrix m n ℂ) :=
  Measure.pi fun _ : m => complexGaussianVector n

/-- The complex Gaussian matrix law is a probability measure. -/
instance isProbabilityMeasure_complexGaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    IsProbabilityMeasure (complexGaussianMatrix m n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : m => complexGaussianVector n))

section Laws

open MeasureTheory ProbabilityTheory
open scoped Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n p q : Type*} [Fintype m]
  [Fintype n] [Fintype p] [Fintype q]

/-- Bridge to Mathlib's standard Gaussian: the standard complex Gaussian law is the image of
Mathlib's `ProbabilityTheory.stdGaussian` on $\mathbb{C}$ (the real two-dimensional standard
Gaussian, of variance $1$ in each part) under $z \mapsto z/\sqrt2$. -/
theorem complexGaussian_eq_map_stdGaussian :
    complexGaussian = (stdGaussian ℂ).map fun z => ((√2 : ℝ)⁻¹ : ℂ) * z := by
  set c : ℝ := (√2)⁻¹ with hc
  have hc2 : (⟨c ^ 2, sq_nonneg c⟩ : NNReal) * 1 = 2⁻¹ := by
    rw [mul_one]
    apply NNReal.eq
    simp [hc, inv_pow, Real.sq_sqrt]
    rfl
  have hν : (gaussianReal 0 1).map (fun x : ℝ => c * x) = gaussianReal 0 2⁻¹ := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
  have hF : (fun v : Fin 2 → ℝ => ∑ i, v i • Complex.orthonormalBasisOneI i) =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∘ MeasurableEquiv.finTwoArrow := by
    ext v
    simp [Fin.sum_univ_two, Complex.orthonormalBasisOneI]
  have hpi := (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI,
    Measure.map_map (by fun_prop) (by fun_prop), hF, ← Function.comp_assoc,
    ← Measure.map_map (by fun_prop) (by fun_prop), hpi, complexGaussian, ← hν,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  rw [← Complex.ofReal_inv, ← hc]
  apply Complex.ext <;> simp

/-- A product of images of product measures is the image of the product of the two products. -/
private lemma pi_map_prod_eq_map_prod_pi {ι α β γ : Type*} [Fintype ι] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ₁ : Measure α) (μ₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {h : α × β → γ} (hh : Measurable h) :
    Measure.pi (fun _ : ι => (μ₁.prod μ₂).map h) =
      ((Measure.pi fun _ : ι => μ₁).prod (Measure.pi fun _ : ι => μ₂)).map
        fun p i => h (p.1 i, p.2 i) := by
  have := Measure.isProbabilityMeasure_map (μ := μ₁.prod μ₂) hh.aemeasurable
  rw [← Measure.pi_map_pi fun _ => hh.aemeasurable,
    ← (measurePreserving_arrowProdEquivProdArrow α β ι (fun _ => μ₁) (fun _ => μ₂)).map_eq,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  rfl

/-- One entry: $(x + iy)/\sqrt2$ with $x, y \sim \mathcal{N}(0, 1)$ independent. -/
private lemma complexGaussian_eq_map_prod_gaussianReal :
    complexGaussian = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      fun p : ℝ × ℝ => (√2 : ℝ)⁻¹ • ((p.1 : ℂ) + Complex.I * p.2) := by
  have h : gaussianReal 0 2⁻¹ = (gaussianReal 0 1).map ((√2 : ℝ)⁻¹ * ·) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp
  rw [complexGaussian, h, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  congr 1
  ext p
  apply Complex.ext <;> simp [-Complex.ofReal_inv]

/-- A complex Gaussian matrix is a real Gaussian matrix in disguise: the standard complex
Gaussian law on $m \times n$ matrices is the law of $(\mathbf{G}_1 + i\mathbf{G}_2)/\sqrt2$,
where $\begin{bmatrix} \mathbf{G}_1 \\ \mathbf{G}_2 \end{bmatrix}$ is a $2m \times n$ standard
real Gaussian matrix (rows indexed by $m \oplus m$). No printed source. -/
theorem complexGaussianMatrix_eq_map_gaussianMatrix :
    complexGaussianMatrix m n = (gaussianMatrix (m ⊕ m) n).map fun X =>
      (√2 : ℝ)⁻¹ • ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) := by
  have hg : Measurable fun p : ℝ × ℝ => (√2 : ℝ)⁻¹ • ((p.1 : ℂ) + Complex.I * p.2) := by
    fun_prop
  have hrow : complexGaussianVector n = ((gaussianVector n).prod (gaussianVector n)).map
      fun p j => (√2 : ℝ)⁻¹ • ((p.1 j : ℂ) + Complex.I * p.2 j) := by
    rw [complexGaussianVector, complexGaussian_eq_map_prod_gaussianReal]
    exact pi_map_prod_eq_map_prod_pi _ _ hg
  have hrowm : Measurable fun (p : (n → ℝ) × (n → ℝ)) (j : n) =>
      (√2 : ℝ)⁻¹ • ((p.1 j : ℂ) + Complex.I * p.2 j) := by
    fun_prop
  rw [complexGaussianMatrix, hrow, pi_map_prod_eq_map_prod_pi _ _ hrowm, gaussianMatrix,
    ← (measurePreserving_sumPiEquivProdPi fun _ : m ⊕ m => gaussianVector n).map_eq,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  rfl

/-- **Unitary invariance of a complex Gaussian matrix**: if $\mathbf{G}$ is a standard complex
Gaussian $n \times k$ matrix and $\mathbf{V} \in \mathbb{C}^{n \times r}$ has orthonormal
columns, then $\mathbf{V}^{\mathsf{H}}\mathbf{G}$ is a standard complex Gaussian $r \times k$
matrix. [Shah2024, proof of Theorem 3.3], "by rotational invariance". -/
theorem hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    [DecidableEq r] {G : Ω → Matrix n q ℂ} (hG : HasLaw G (complexGaussianMatrix n q) μ)
    {V : Matrix n r ℂ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => Vᴴ * G ω) (complexGaussianMatrix r q) μ := by
  classical
  have hW : Vᴴ * Vᴴᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hV
  have hre : ∀ i j : r, ∑ k, ((Vᴴ i k).re * (Vᴴ j k).re + (Vᴴ i k).im * (Vᴴ j k).im) =
      (if i = j then 1 else 0) := by
    intro i j
    have := congrArg Complex.re (congrFun (congrFun hW i) j)
    simp only [Matrix.mul_apply, Complex.re_sum, Complex.mul_re, Matrix.one_apply,
      Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im] at this
    simp only [apply_ite Complex.re, Complex.one_re, Complex.zero_re, neg_mul, neg_neg,
      sub_eq_add_neg] at this
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
      neg_mul, mul_neg, neg_neg]
    linarith [this]
  have him : ∀ i j : r, ∑ k, ((Vᴴ i k).im * (Vᴴ j k).re - (Vᴴ i k).re * (Vᴴ j k).im) = 0 := by
    intro i j
    have := congrArg Complex.im (congrFun (congrFun hW i) j)
    simp only [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, Matrix.one_apply,
      apply_ite Complex.im, Complex.one_im, Complex.zero_im, ite_self] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  set U : Matrix (r ⊕ r) (n ⊕ n) ℝ :=
    Matrix.fromBlocks (Vᴴ.map Complex.re) (-(Vᴴ.map Complex.im)) (Vᴴ.map Complex.im)
      (Vᴴ.map Complex.re) with hUdef
  have hU : HasOrthonormalCols Uᴴ := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose]
    have hre' := hre
    have him' := him
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Finset.sum_add_distrib, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib,
      sub_neg_eq_add] at hre' him'
    ext (i | i) (j | j) <;>
      simp [hUdef, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.fromBlocks] <;>
      linarith [hre' i j, him' i j, him' j i, hre' j i]
  have hkey : ∀ X : Matrix (n ⊕ n) q ℝ,
      Vᴴ * ((√2 : ℝ)⁻¹ • ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ)))) =
      (√2 : ℝ)⁻¹ • (((U * X).submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • ((U * X).submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) := by
    intro X
    have hc : ∀ z : ℂ, (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := fun z => by
      apply Complex.ext <;> simp
    ext i j
    simp only [hUdef, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.submatrix_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.neg_apply, Matrix.conjTranspose_apply, id, Matrix.mul_apply, Complex.real_smul,
      smul_eq_mul]
    have key : ∀ (w x1 x2 : ℂ), w * ((((√2 : ℝ)⁻¹ : ℝ) : ℂ) * (x1 + Complex.I * x2)) =
        ((((√2 : ℝ)⁻¹ : ℝ) : ℂ)) * ((w.re : ℂ) * x1 + -(w.im : ℂ) * x2 +
          Complex.I * ((w.im : ℂ) * x1 + (w.re : ℂ) * x2)) := by
      intro w x1 x2
      linear_combination (-((((√2 : ℝ)⁻¹ : ℝ) : ℂ) * (x1 + Complex.I * x2))) * (Complex.re_add_im w)
        + ((((√2 : ℝ)⁻¹ : ℝ) : ℂ) * (w.im : ℂ) * x2) * Complex.I_sq
    simp only [Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_mul,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have k := key ((starRingEnd ℂ) (V x i)) ((X (Sum.inl x) j : ℝ) : ℂ)
      ((X (Sum.inr x) j : ℝ) : ℂ)
    simp only [Complex.conj_re, Complex.conj_im, Complex.ofReal_neg] at k
    linear_combination k
  have hUlaw : (gaussianMatrix (n ⊕ n) q).map (fun X => U * X) = gaussianMatrix (r ⊕ r) q :=
    (hasLaw_const_mul_of_hasLaw_gaussianMatrix
      (HasLaw.id (μ := gaussianMatrix (n ⊕ n) q)) hU).map_eq
  have hmeas : Measurable (fun Z : Matrix n q ℂ => Vᴴ * Z) :=
    measurable_const.matrix_mul measurable_id
  have hA : (fun ω => Vᴴ * G ω) = (fun Z : Matrix n q ℂ => Vᴴ * Z) ∘ G := rfl
  refine ⟨(hmeas.comp_aemeasurable hG.aemeasurable), ?_⟩
  rw [hA, ← AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hG.aemeasurable, hG.map_eq,
    complexGaussianMatrix_eq_map_gaussianMatrix, complexGaussianMatrix_eq_map_gaussianMatrix,
    Measure.map_map hmeas (by fun_prop), ← hUlaw, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext X
  exact hkey X

/-- A submatrix of a standard complex Gaussian matrix on injective row and column maps is a
standard complex Gaussian matrix. -/
theorem hasLaw_submatrix_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {f : p → m} (hf : Function.Injective f)
    {e : q → n} (he : Function.Injective e) :
    HasLaw (fun ω => (G ω).submatrix f e) (complexGaussianMatrix p q) μ := by
  classical
  have hsub : Function.Injective (Sum.map f f) := Sum.map_injective.mpr ⟨hf, hf⟩
  have hreal : (gaussianMatrix (m ⊕ m) n).map
      (fun X : Matrix (m ⊕ m) n ℝ => X.submatrix (Sum.map f f) e) = gaussianMatrix (p ⊕ p) q :=
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix (HasLaw.id) hsub he).map_eq
  have hcomm : ∀ X : Matrix (m ⊕ m) n ℝ,
      (√2 : ℝ)⁻¹ • (((X.submatrix (Sum.map f f) e).submatrix Sum.inl id).map
          (fun x : ℝ => (x : ℂ)) +
        Complex.I • ((X.submatrix (Sum.map f f) e).submatrix Sum.inr id).map
          (fun x : ℝ => (x : ℂ))) =
      ((√2 : ℝ)⁻¹ • ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ)))).submatrix f e := by
    intro X
    ext i j
    simp [Matrix.submatrix_apply]
  have hmeasSub : Measurable (fun Z : Matrix m n ℂ => Z.submatrix f e) := by fun_prop
  have hmeasSubR : Measurable (fun X : Matrix (m ⊕ m) n ℝ => X.submatrix (Sum.map f f) e) := by
    fun_prop
  have heq : (complexGaussianMatrix m n).map (fun Z : Matrix m n ℂ => Z.submatrix f e) =
      complexGaussianMatrix p q := by
    rw [complexGaussianMatrix_eq_map_gaussianMatrix, complexGaussianMatrix_eq_map_gaussianMatrix,
      Measure.map_map hmeasSub (by fun_prop), ← hreal, Measure.map_map (by fun_prop) hmeasSubR]
    congr 1
  refine ⟨hmeasSub.comp_aemeasurable hG.aemeasurable, ?_⟩
  rw [← heq, ← hG.map_eq, AEMeasurable.map_map_of_aemeasurable hmeasSub.aemeasurable
    hG.aemeasurable]
  rfl

/-- The squared Euclidean norm of a complex vector is the sum of those of its real and
imaginary parts. -/
private theorem norm_toLp_sq_eq_re_add_im (v : n → ℂ) : ‖WithLp.toLp 2 v‖ ^ 2 =
    ‖WithLp.toLp 2 fun j => (v j).re‖ ^ 2 + ‖WithLp.toLp 2 fun j => (v j).im‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_toLp_sq_eq_sum_sq,
    EuclideanSpace.norm_toLp_sq_eq_sum_sq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The complexification of a real matrix has spectral norm at most that of the matrix. -/
private theorem specNorm_map_ofReal_le (A : Matrix m n ℝ) :
    specNorm (A.map fun x : ℝ => (x : ℂ)) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  have hv : ∀ i, ((A.map fun r : ℝ => (r : ℂ)) *ᵥ x) i =
      ((A *ᵥ fun j => (x j).re) i : ℂ) + ((A *ᵥ fun j => (x j).im) i : ℂ) * Complex.I := by
    intro i
    apply Complex.ext <;> simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum]
  have hre := norm_toLp_mulVec_le A fun j => (x j).re
  have him := norm_toLp_mulVec_le A fun j => (x j).im
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, norm_toLp_sq_eq_re_add_im,
    norm_toLp_sq_eq_re_add_im x]
  simp only [hv, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, add_zero,
    mul_one, zero_add]
  rw [mul_add]
  gcongr
  · exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hre |>.trans_eq (mul_pow _ _ _)
  · exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 him |>.trans_eq (mul_pow _ _ _)

/-- **Norm tail of a complex Gaussian matrix** (Lemma 3.2): for a standard complex Gaussian
$m \times n$ matrix $\mathbf{G}$ and $t \ge 0$,
$$\mathbb{P}\bigl[\sqrt2\,(\sqrt{\lvert m \rvert} + \sqrt{\lvert n \rvert} + t) \le
\|\mathbf{G}\|_2\bigr] \le 2e^{-t^2/2} \,.$$
[Shah2024, Lemma 3.2], citing [BanksKulkarniMukherjeeSrivastava2021, Lemma 2.2]: there
$\mathbb{P}[\|\mathbf{G}\|_2 > (2\sqrt2 + t)\sqrt n] \le 2e^{-nt^2}$ for square $\mathbf{G}$; the
constant in the exponent differs.
Result: complex-gaussian-norm-tail -/
theorem measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ≤ specNorm (G ω)} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  have hf : Measurable fun X : Matrix (m ⊕ m) n ℝ => (√2 : ℝ)⁻¹ •
      ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) :=
    Continuous.measurable (by fun_prop)
  rw [hG.measureReal_eq (p := fun A =>
      √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ≤ specNorm A)
      (measurableSet_le measurable_const continuous_specNorm.measurable),
    complexGaussianMatrix_eq_map_gaussianMatrix,
    map_measureReal_apply hf (measurableSet_le measurable_const continuous_specNorm.measurable)]
  have hX := HasLaw.id (μ := gaussianMatrix (m ⊕ m) n)
  have h₁ := measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Sum.inl_injective Function.injective_id) ht
  have h₂ := measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Sum.inr_injective Function.injective_id) ht
  refine (measureReal_mono fun X hX => ?_).trans ((measureReal_union_le _ _).trans
    ((add_le_add h₁ h₂).trans_eq (two_mul _).symm))
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_union, id] at hX ⊢
  by_contra hcon
  simp only [not_or, not_le] at hcon
  rw [specNorm_real_smul, abs_inv, abs_of_pos (by positivity), ← div_eq_inv_mul,
    le_div_iff₀ (by positivity), mul_comm, ← mul_assoc, Real.mul_self_sqrt zero_le_two] at hX
  have hS := (specNorm_add_le _ _).trans (add_le_add
    (specNorm_map_ofReal_le (X.submatrix Sum.inl id)) (le_refl (specNorm (Complex.I •
      (X.submatrix Sum.inr id).map fun x : ℝ => (x : ℂ)))))
  rw [specNorm_smul, Complex.norm_I, one_mul] at hS
  linarith [hcon.1, hcon.2, specNorm_map_ofReal_le (X.submatrix Sum.inr id)]

private lemma gaussianPDFReal_two_inv (x : ℝ) :
    gaussianPDFReal 0 2⁻¹ x = (√Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_inv, NNReal.coe_ofNat, sub_zero]
  congr 2
  · ring_nf
  · ring

/-- The radial one-dimensional integral of the exponential tail: $\int_0^\infty r\,
\mathbf 1_{\{s \le r^2\}} e^{-r^2}\,dr = e^{-s}/2$ for $s \ge 0$. -/
private lemma integral_Ioi_radial_tail {s : ℝ} (hs : 0 ≤ s) :
    ∫ x in Set.Ioi (0 : ℝ), x * (if s ≤ x ^ 2 then Real.exp (-x ^ 2) else 0) =
      Real.exp (-s) / 2 := by
  have ha : 0 ≤ √s := Real.sqrt_nonneg s
  have hsa : (√s) ^ 2 = s := Real.sq_sqrt hs
  have key : ∀ x : ℝ, 0 < x → (s ≤ x ^ 2 ↔ √s ≤ x) := fun x hx => by
    constructor
    · intro h
      calc √s ≤ √(x ^ 2) := Real.sqrt_le_sqrt h
        _ = x := Real.sqrt_sq hx.le
    · intro h
      nlinarith [Real.sqrt_nonneg s]
  have hcongr : ∫ x in Set.Ioi (0 : ℝ), x * (if s ≤ x ^ 2 then Real.exp (-x ^ 2) else 0) =
      ∫ x in Set.Ioi (0 : ℝ), (Set.Ici (√s)).indicator (fun x => x * Real.exp (-x ^ 2)) x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    simp only [Set.indicator_apply, Set.mem_Ici, key x hx']
    split_ifs <;> simp
  rw [hcongr, setIntegral_indicator measurableSet_Ici]
  have hf : ∀ x ∈ Set.Ioi (√s), HasDerivAt (fun x : ℝ => -Real.exp (-x ^ 2) / 2)
      (x * Real.exp (-x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
      exact ((hasDerivAt_pow 2 x).neg).congr_deriv (by norm_num)
    exact ((h1.exp.neg).div_const 2).congr_deriv (by ring)
  have hlim : Filter.Tendsto (fun x : ℝ => -Real.exp (-x ^ 2) / 2) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => -x ^ 2) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_pow_atTop two_ne_zero)
    have h2 := ((Real.tendsto_exp_atBot.comp h1).neg).div_const 2
    simpa using h2
  have hI : Integrable (fun x : ℝ => x * Real.exp (-x ^ 2)) := by
    simpa using integrable_mul_exp_neg_mul_sq one_pos
  have hc : ContinuousWithinAt (fun x : ℝ => -Real.exp (-x ^ 2) / 2) (Set.Ici (√s)) (√s) :=
    Continuous.continuousWithinAt (by fun_prop)
  rcases ha.eq_or_lt with h0 | h0
  · rw [← h0] at hf hsa hc ⊢
    rw [Set.inter_eq_left.2 Set.Ioi_subset_Ici_self,
      integral_Ioi_of_hasDerivAt_of_tendsto hc hf hI.integrableOn hlim]
    norm_num at hsa
    rw [← hsa]
    norm_num
  · rw [Set.inter_eq_right.2 (Set.Ici_subset_Ioi.2 h0), integral_Ici_eq_integral_Ioi,
      integral_Ioi_of_hasDerivAt_of_tendsto hc hf hI.integrableOn hlim, hsa]
    ring

/-- The exponential tail in polar coordinates: $\int_{\{s \le \lvert p\rvert^2\}} \pi^{-1}
e^{-\lvert p\rvert^2}\,dp = e^{-s}$ for $s \ge 0$. -/
private lemma integral_tail_polar {s : ℝ} (hs : 0 ≤ s) :
    ∫ p in {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2},
      (Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) = Real.exp (-s) := by
  have hT : MeasurableSet {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [← integral_indicator hT, ← integral_comp_polarCoord_symm]
  have hpt : ∀ q : ℝ × ℝ,
      q.1 • ({p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2}.indicator
        (fun p : ℝ × ℝ => (Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2))))
        (polarCoord.symm q) =
      (Real.pi)⁻¹ * (q.1 * (if s ≤ q.1 ^ 2 then Real.exp (-q.1 ^ 2) else 0)) * 1 := by
    intro q
    have hr : (q.1 * Real.cos q.2) ^ 2 + (q.1 * Real.sin q.2) ^ 2 = q.1 ^ 2 := by
      linear_combination (q.1 ^ 2) * Real.sin_sq_add_cos_sq q.2
    rw [polarCoord_symm_apply]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hr, smul_eq_mul]
    split_ifs <;> ring
  simp only [hpt]
  rw [Measure.volume_eq_prod, polarCoord_target,
    setIntegral_prod_mul (fun x : ℝ => (Real.pi)⁻¹ * (x * if s ≤ x ^ 2 then
      Real.exp (-x ^ 2) else 0)) (fun _ : ℝ => (1 : ℝ))]
  have hvol : (volume : Measure ℝ).real (Set.Ioo (-Real.pi) Real.pi) = 2 * Real.pi := by
    rw [Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  rw [integral_const_mul, integral_Ioi_radial_tail hs, setIntegral_const, hvol, smul_eq_mul,
    mul_one]
  field_simp

/-- The tail of a standard complex Gaussian, as a Lebesgue integral over `ℝ × ℝ` of its density
in the real and imaginary parts. -/
private lemma complexGaussian_real_eq_integral (s : ℝ) :
    complexGaussian.real {w | s ≤ ‖w‖ ^ 2} =
      ∫ p in {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2},
        (Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) := by
  have hν : gaussianReal 0 2⁻¹ = volume.withDensity (gaussianPDF 0 2⁻¹) :=
    gaussianReal_of_var_ne_zero _ (by norm_num)
  have hT : MeasurableSet {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' {w : ℂ | s ≤ ‖w‖ ^ 2} =
      {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Complex.sq_norm, Complex.normSq_mk,
      Complex.measurableEquivRealProd_symm_apply]
    ring_nf
  have hpt : ∀ p : ℝ × ℝ, gaussianPDF 0 2⁻¹ p.1 * gaussianPDF 0 2⁻¹ p.2 =
      ENNReal.ofReal ((Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2))) := by
    intro p
    have h0 : 0 ≤ (√Real.pi)⁻¹ * Real.exp (-p.1 ^ 2) := by positivity
    have h1 : 0 ≤ (√Real.pi)⁻¹ * Real.exp (-p.2 ^ 2) := by positivity
    simp only [gaussianPDF_def, gaussianPDFReal_two_inv]
    rw [← ENNReal.ofReal_mul h0]
    congr 1
    have hs : (√Real.pi)⁻¹ * (√Real.pi)⁻¹ = (Real.pi)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt Real.pi_pos.le]
    rw [show (√Real.pi)⁻¹ * Real.exp (-p.1 ^ 2) * ((√Real.pi)⁻¹ * Real.exp (-p.2 ^ 2)) =
      ((√Real.pi)⁻¹ * (√Real.pi)⁻¹) * (Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) by ring,
      hs, ← Real.exp_add]
    ring_nf
  rw [complexGaussian, map_measureReal_apply Complex.measurableEquivRealProd.symm.measurable
    (measurableSet_le measurable_const (by fun_prop)), hpre, Measure.real, hν,
    MeasureTheory.prod_withDensity (by fun_prop) (by fun_prop), withDensity_apply _ hT,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun p => by positivity)
      (by fun_prop)]
  congr 2
  funext p
  exact hpt p

/-- The exponential upper tail of a standard complex Gaussian: for $z \sim
\mathcal{N}_{\mathbb C}(0, 1)$ and every real $s$, $\mathbb{P}[s \le \lvert z \rvert^2] \le
e^{-s}$ ($\lvert z\rvert^2$ is exponential of mean $1$). No printed source needed: the closed
form of the $\chi^2_2$ tail, in polar coordinates. -/
theorem measureReal_norm_sq_ge_le_of_hasLaw_complexGaussian {z : Ω → ℂ}
    (hz : HasLaw z complexGaussian μ) (s : ℝ) :
    μ.real {ω | s ≤ ‖z ω‖ ^ 2} ≤ Real.exp (-s) := by
  have : IsProbabilityMeasure μ := hz.isProbabilityMeasure_iff.2 inferInstance
  rcases lt_or_ge s 0 with hs | hs
  · exact (measureReal_le_one).trans (Real.one_le_exp (by linarith))
  · rw [hz.measureReal_eq (p := fun w : ℂ => s ≤ ‖w‖ ^ 2)
      (measurableSet_le measurable_const (measurable_norm.pow_const 2)),
      complexGaussian_real_eq_integral, integral_tail_polar hs]

/-- The complex matrix $\mathbf{X}_1 + i\mathbf{X}_2$ built from the two halves of a real
$2m \times n$ matrix $\mathbf{X}$ has the Frobenius norm of $\mathbf{X}$. -/
private theorem frobNorm_map_ofReal_add_I_smul (X : Matrix (m ⊕ m) n ℝ) :
    frobNorm ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
      Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) = frobNorm X := by
  rw [← sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _), frobNorm_sq_eq_sum,
    frobNorm_sq_eq_sum_sq, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **Norm tail of a complex Gaussian matrix with the full exponent**: for
$\mathbf{G}$ an $m \times n$ standard complex Gaussian matrix and $t \ge 0$,
$\mathbb{P}[\sqrt2(\sqrt m + \sqrt n) + t \le \|\mathbf{G}\|_2] \le e^{-t^2}$. Compared with
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`, the deviation $t$ is not
multiplied by $\sqrt2$ and there is no union bound over the two parts. The sharp mean
$\sqrt m + \sqrt n$ is not claimed (design note, item I6). [Shah2024, Lemma 3.2], with the Gaussian
concentration of the realification in place of the union bound. -/
theorem measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) + t ≤ specNorm (G ω)} ≤
      Real.exp (-t ^ 2) := by
  set φ : Matrix (m ⊕ m) n ℝ → Matrix m n ℂ := fun X => (√2 : ℝ)⁻¹ •
      ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) with hφ
  have hf : Measurable φ := Continuous.measurable (by fun_prop)
  have hS : MeasurableSet {A : Matrix m n ℂ |
      √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) + t ≤ specNorm A} :=
    measurableSet_le measurable_const continuous_specNorm.measurable
  rw [hG.measureReal_eq hS, complexGaussianMatrix_eq_map_gaussianMatrix,
    map_measureReal_apply hf hS]
  have hX := HasLaw.id (μ := gaussianMatrix (m ⊕ m) n)
  have hlip : ∀ A B, |specNorm (φ A) - specNorm (φ B)| ≤
      ((‖(√2 : ℝ)⁻¹‖₊ : ℝ)) * frobNorm (A - B) := by
    intro A B
    have hsub : φ A - φ B = φ (A - B) := by
      ext i j
      simp only [hφ, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply,
        Matrix.submatrix_apply, id, Complex.ofReal_sub, Complex.real_smul, smul_eq_mul]
      ring
    refine (abs_specNorm_sub_specNorm_le _ _).trans ?_
    rw [hsub, hφ, specNorm_real_smul, coe_nnnorm, Real.norm_eq_abs]
    gcongr
    exact (specNorm_le_frobNorm _).trans (frobNorm_map_ofReal_add_I_smul _).le
  have hmean : ∫ X, specNorm (φ X) ∂(gaussianMatrix (m ⊕ m) n) ≤
      √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) := by
    have h₁ : HasLaw (fun X : Matrix (m ⊕ m) n ℝ => X.submatrix Sum.inl id) _ _ :=
      hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Sum.inl_injective Function.injective_id
    have h₂ : HasLaw (fun X : Matrix (m ⊕ m) n ℝ => X.submatrix Sum.inr id) _ _ :=
      hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Sum.inr_injective Function.injective_id
    have hle : ∀ X : Matrix (m ⊕ m) n ℝ, specNorm (φ X) ≤
        (√2)⁻¹ * (specNorm (X.submatrix Sum.inl id) + specNorm (X.submatrix Sum.inr id)) := by
      intro X
      rw [hφ, specNorm_real_smul, abs_of_pos (by positivity)]
      gcongr
      refine (specNorm_add_le _ _).trans (add_le_add (specNorm_map_ofReal_le _) ?_)
      rw [specNorm_smul, Complex.norm_I, one_mul]
      exact specNorm_map_ofReal_le _
    calc ∫ X, specNorm (φ X) ∂(gaussianMatrix (m ⊕ m) n)
        ≤ ∫ X, (√2)⁻¹ * (specNorm (X.submatrix Sum.inl id) +
            specNorm (X.submatrix Sum.inr id)) ∂(gaussianMatrix (m ⊕ m) n) :=
          integral_mono (integrable_comp_of_hasLaw_gaussianMatrix hX hlip)
            (((integrable_specNorm_of_hasLaw_gaussianMatrix h₁).add
              (integrable_specNorm_of_hasLaw_gaussianMatrix h₂)).const_mul _) hle
      _ ≤ (√2)⁻¹ * (2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ))) := by
          rw [integral_const_mul, integral_add (integrable_specNorm_of_hasLaw_gaussianMatrix h₁)
            (integrable_specNorm_of_hasLaw_gaussianMatrix h₂)]
          gcongr
          linarith [integral_specNorm_le_of_hasLaw_gaussianMatrix h₁,
            integral_specNorm_le_of_hasLaw_gaussianMatrix h₂]
      _ = √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) := by
          field_simp; rw [Real.sq_sqrt zero_le_two]
  have h := measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix hX hlip ht
  rw [coe_nnnorm, Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt zero_le_two,
    mul_inv_cancel₀ two_ne_zero, div_one] at h
  refine (measureReal_mono fun X hX => ?_).trans h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, id] at hX ⊢
  linarith

end Laws

end NLAlib
