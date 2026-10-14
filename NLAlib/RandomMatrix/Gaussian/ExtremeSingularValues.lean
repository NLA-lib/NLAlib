/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.LeastSingularValue
public import NLAlib.Matrix.Spectral.SingularValueInequalities
public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.RandomMatrix.Gaussian.SpectralNorm

/-!
# Extreme singular values of Gaussian matrices

For a standard Gaussian matrix `G : m × n` (`N = card m` rows, `n = card n` columns): Gordon's
lower bound `√N - √n ≤ E σ_min(G)` (the upper bound `E ‖G‖ ≤ √N + √n` is in
`NLAlib/RandomMatrix/Gaussian/SpectralNorm.lean`), Gaussian concentration of every singular value
with proxy `1`, the deviation tails `P(√N + √n + t ≤ ‖G‖) ≤ e^{-t²/2}` and
`P(σ_min(G) ≤ √N - √n - t) ≤ e^{-t²/2}`, and the same conclusions as Loewner bounds on `Gᴴ G`,
the shape of the subspace-embedding predicate.

The smallest singular value of a matrix with `n` columns is `singularValues (X ω) k` with
`k + 1 = card n`. When `n > N` it is the padding `0` and `√N - √n < 0`, so the lower bounds hold
trivially and no tallness hypothesis is stated; the lower Loewner forms carry the hypothesis
`t ≤ √N - √n` that makes the squared base meaningful.

Gordon's lower bound compares, over nets of the unit spheres, the process `⟨g, u⟩ + ⟨h, v⟩`
(the `X` side of `NLAlib.integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw`) with
`⟨v, G u⟩` (its `Y` side), and uses
`NLAlib.le_integral_norm_sub_integral_norm_of_hasLaw_gaussianVector`.

## Main results

* `NLAlib.le_integral_singularValues_of_hasLaw_gaussianMatrix`: `√N - √n ≤ E σ_min(G)`.
* `NLAlib.hasSubgaussianMGF_singularValues_sub_integral_of_hasLaw_gaussianMatrix`.
* `NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix`: the deviation tails.
* The Gaussian Gram sandwich, with its one-sided forms (in namespace `NLAlib`):
  `measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

section Process

variable {ι : Type*} [Fintype ι]

private theorem abs_dotProduct_le (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rwa [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] at h

private theorem norm_toLp_sq (x : ι → ℝ) : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {Z : Ω' → ι → ℝ}

private theorem hasGaussianLaw_dotProduct {I : Type*} [Finite I]
    (hZ : HasLaw Z (gaussianVector ι) ν) (w : I → ι → ℝ) :
    HasGaussianLaw (fun ω i => w i ⬝ᵥ Z ω) ν := by
  have := Fintype.ofFinite I
  exact hZ.hasGaussianLaw.map_fun (Matrix.mulVecLin (Matrix.of w)).toContinuousLinearMap

private theorem integral_dotProduct (hZ : HasLaw Z (gaussianVector ι) ν) (w : ι → ℝ) :
    ∫ ω, w ⬝ᵥ Z ω ∂ν = 0 :=
  integral_of_hasLaw_gaussianReal (hasLaw_dotProduct_of_hasLaw_gaussianVector hZ w)

private theorem integral_dotProduct_sub_sq (hZ : HasLaw Z (gaussianVector ι) ν)
    (w w' : ι → ℝ) :
    ∫ ω, (w ⬝ᵥ Z ω - w' ⬝ᵥ Z ω) ^ 2 ∂ν = (w - w') ⬝ᵥ (w - w') := by
  simp only [← sub_dotProduct]
  rw [integral_sq_of_hasLaw_gaussianReal (hasLaw_dotProduct_of_hasLaw_gaussianVector hZ _),
    NNReal.coe_pow, coe_nnnorm, norm_toLp_sq]

private theorem hasLaw_comp_inl :
    HasLaw (fun z : n ⊕ m → ℝ => z ∘ Sum.inl) (gaussianVector n) (gaussianVector (n ⊕ m)) :=
  hasLaw_pi_iff.2 ⟨(HasLaw.id (μ := gaussianVector (n ⊕ m))).iIndepFun_eval.precomp
    Sum.inl_injective, fun i => (HasLaw.id (μ := gaussianVector (n ⊕ m))).eval (Sum.inl i)⟩

private theorem hasLaw_comp_inr :
    HasLaw (fun z : n ⊕ m → ℝ => z ∘ Sum.inr) (gaussianVector m) (gaussianVector (n ⊕ m)) :=
  hasLaw_pi_iff.2 ⟨(HasLaw.id (μ := gaussianVector (n ⊕ m))).iIndepFun_eval.precomp
    Sum.inr_injective, fun i => (HasLaw.id (μ := gaussianVector (n ⊕ m))).eval (Sum.inr i)⟩

/-- A point of the unit sphere is within `ε` of a point of an `ε`-net, in coordinates. -/
private theorem exists_mem_norm_sub_le {N : Set (EuclideanSpace ℝ ι)} {ε : NNReal}
    (hN : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace ℝ ι) 1) N) {y : ι → ℝ}
    (hy : ‖WithLp.toLp 2 y‖ = 1) : ∃ x ∈ N, ‖WithLp.toLp 2 (y - WithLp.ofLp x)‖ ≤ ε := by
  have h := hN.subset_iUnion_closedBall (mem_sphere_zero_iff_norm.2 hy)
  simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at h
  obtain ⟨x, hx, hxy⟩ := h
  refine ⟨x, hx, ?_⟩
  rwa [WithLp.toLp_sub, WithLp.toLp_ofLp, ← dist_eq_norm]

/-- Every vector has a unit vector aligned with it. -/
private theorem exists_norm_eq_one_dotProduct_eq [Nonempty ι] (h : ι → ℝ) :
    ∃ s : ι → ℝ, ‖WithLp.toLp 2 s‖ = 1 ∧ s ⬝ᵥ h = ‖WithLp.toLp 2 h‖ := by
  classical
  by_cases h0 : ‖WithLp.toLp 2 h‖ = 0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    have hh : h = 0 := by simpa using h0
    refine ⟨Pi.single i 1, ?_, ?_⟩
    · rw [PiLp.toLp_single, PiLp.norm_single, norm_one]
    · subst hh
      simp
  · refine ⟨‖WithLp.toLp 2 h‖⁻¹ • h, ?_, ?_⟩
    · rw [WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
    · rw [smul_dotProduct, ← norm_toLp_sq, smul_eq_mul]
      field_simp

end Process

/-- `x ⬝ᵥ G y` is the dot product of the flattened `G` with `x yᵀ`. -/
private theorem dotProduct_mulVec_eq (x : m → ℝ) (G : Matrix m n ℝ) (y : n → ℝ) :
    x ⬝ᵥ (G *ᵥ y) = (fun p : m × n => x p.1 * y p.2) ⬝ᵥ Function.uncurry G := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = _ * G i j
  ring

private theorem prod_dotProduct_prod (x x' : m → ℝ) (y y' : n → ℝ) :
    (fun p : m × n => x p.1 * y p.2) ⬝ᵥ (fun p => x' p.1 * y' p.2) = (x ⬝ᵥ x') * (y ⬝ᵥ y') := by
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section Gordon

/-- Within a block (`u` fixed) the increments of `⟨g, u⟩ + ⟨h, t⟩` and `⟨t, G u⟩` agree. -/
private theorem gordon_increment_same {u : n → ℝ} (hu : u ⬝ᵥ u = 1) (t s : m → ℝ) :
    (Sum.elim u t - Sum.elim u s) ⬝ᵥ (Sum.elim u t - Sum.elim u s) =
      ((fun p : m × n => t p.1 * u p.2) - fun p => s p.1 * u p.2) ⬝ᵥ
        ((fun p : m × n => t p.1 * u p.2) - fun p => s p.1 * u p.2) := by
  simp only [sub_dotProduct, dotProduct_sub, sumElim_dotProduct_sumElim, prod_dotProduct_prod]
  rw [dotProduct_comm s t, hu]
  ring

/-- Across blocks the increments of `⟨t, G u⟩` are at most those of `⟨g, u⟩ + ⟨h, t⟩`. -/
private theorem gordon_increment_le {u u' : n → ℝ} {t s : m → ℝ} (hu : u ⬝ᵥ u = 1)
    (hu' : u' ⬝ᵥ u' = 1) (ht : t ⬝ᵥ t = 1) (hs : s ⬝ᵥ s = 1) :
    ((fun p : m × n => t p.1 * u p.2) - fun p => s p.1 * u' p.2) ⬝ᵥ
        ((fun p : m × n => t p.1 * u p.2) - fun p => s p.1 * u' p.2) ≤
      (Sum.elim u t - Sum.elim u' s) ⬝ᵥ (Sum.elim u t - Sum.elim u' s) := by
  have h1 := norm_toLp_sq (u - u')
  have h2 := norm_toLp_sq (t - s)
  simp only [sub_dotProduct, dotProduct_sub, sumElim_dotProduct_sumElim,
    prod_dotProduct_prod] at h1 h2 ⊢
  rw [dotProduct_comm u' u, dotProduct_comm s t, hu, hu', ht, hs] at *
  have h3 := sq_nonneg ‖WithLp.toLp 2 (u - u')‖
  have h4 := sq_nonneg ‖WithLp.toLp 2 (t - s)‖
  nlinarith [mul_nonneg (show 0 ≤ 1 - u ⬝ᵥ u' by linarith) (show 0 ≤ 1 - t ⬝ᵥ s by linarith)]

variable {U T : Type*} [Finite U] [Finite T]

/-- Gordon's min-max comparison for the Gaussian matrix against `⟨g, u⟩ + ⟨h, t⟩`. -/
private theorem integral_iInf_iSup_le_gordon (hX : HasLaw X (gaussianMatrix m n) μ)
    (u : U → n → ℝ) (t : T → m → ℝ) (hu : ∀ i, u i ⬝ᵥ u i = 1) (ht : ∀ j, t j ⬝ᵥ t j = 1) :
    ∫ z, ⨅ i, ⨆ j, Sum.elim (u i) (t j) ⬝ᵥ z ∂gaussianVector (n ⊕ m) ≤
      ∫ ω, ⨅ i, ⨆ j, t j ⬝ᵥ (X ω *ᵥ u i) ∂μ := by
  have hU := hasLaw_uncurry_of_hasLaw_gaussianMatrix hX
  have hV : HasLaw (fun z : n ⊕ m → ℝ => z) (gaussianVector (n ⊕ m)) (gaussianVector (n ⊕ m)) :=
    HasLaw.id
  simp only [dotProduct_mulVec_eq]
  refine integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw
    (X := fun i j z => Sum.elim (u i) (t j) ⬝ᵥ z)
    (Y := fun i j ω => (fun p : m × n => t j p.1 * u i p.2) ⬝ᵥ Function.uncurry (X ω))
    (hasGaussianLaw_dotProduct hV fun p : U × T => Sum.elim (u p.1) (t p.2))
    (hasGaussianLaw_dotProduct hU fun (p : U × T) (q : m × n) => t p.2 q.1 * u p.1 q.2)
    (fun i j => integral_dotProduct hV _) (fun i j => integral_dotProduct hU _)
    (fun i j j' => ?_) (fun i i' j j' _ => ?_)
  · rw [integral_dotProduct_sub_sq hV, integral_dotProduct_sub_sq hU]
    exact (gordon_increment_same (hu i) (t j) (t j')).le
  · rw [integral_dotProduct_sub_sq hV, integral_dotProduct_sub_sq hU]
    exact gordon_increment_le (hu i) (hu i') (ht j) (ht j')

private theorem integrable_iInf_iSup_gordon (hX : HasLaw X (gaussianMatrix m n) μ)
    (u : U → n → ℝ) (t : T → m → ℝ) :
    Integrable (fun ω => ⨅ i, ⨆ j, t j ⬝ᵥ (X ω *ᵥ u i)) μ := by
  simp only [dotProduct_mulVec_eq]
  exact integrable_iInf_iSup_of_hasGaussianLaw (X := fun i j ω =>
      (fun p : m × n => t j p.1 * u i p.2) ⬝ᵥ Function.uncurry (X ω))
    (hasGaussianLaw_dotProduct (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)
      fun (p : U × T) (q : m × n) => t p.2 q.1 * u p.1 q.2)

end Gordon

/-- Every singular value is `1`-Lipschitz for the Frobenius norm. -/
private theorem abs_singularValues_sub_le (k : ℕ) (A B : Matrix m n ℝ) :
    |singularValues A k - singularValues B k| ≤ ((1 : NNReal) : ℝ) * frobNorm (A - B) := by
  rw [NNReal.coe_one, one_mul]
  exact abs_singularValues_sub_le_frobNorm A B k

/-- Every singular value of a standard Gaussian matrix is integrable. -/
theorem integrable_singularValues_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    (k : ℕ) : Integrable (fun ω => singularValues (X ω) k) μ :=
  integrable_comp_of_hasLaw_gaussianMatrix hX (f := fun A => singularValues A k)
    (abs_singularValues_sub_le k)

/-- The comparison side: `√N - √n - ε √N ≤ E min_u max_t (⟨g, u⟩ + ⟨h, t⟩)` on `ε`-nets. -/
private theorem le_integral_iInf_iSup_sumElim [Nonempty m] [Nonempty n]
    (hnm : Fintype.card n ≤ Fintype.card m) {U T : Type*} [Finite U] [Nonempty U] [Finite T]
    (u : U → n → ℝ) (t : T → m → ℝ) (hu : ∀ i, ‖WithLp.toLp 2 (u i)‖ = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : ∀ s : m → ℝ, ‖WithLp.toLp 2 s‖ = 1 → ∃ j, ‖WithLp.toLp 2 (s - t j)‖ ≤ ε) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - ε * √(Fintype.card m : ℝ) ≤
      ∫ z, ⨅ i, ⨆ j, Sum.elim (u i) (t j) ⬝ᵥ z ∂gaussianVector (n ⊕ m) := by
  classical
  have hl := hasLaw_comp_inl (n := n) (m := m)
  have hr := hasLaw_comp_inr (n := n) (m := m)
  have hV : HasLaw (fun z : n ⊕ m → ℝ => z) (gaussianVector (n ⊕ m)) (gaussianVector (n ⊕ m)) :=
    HasLaw.id
  have hil := (isIsotropic_of_hasLaw_gaussianVector hl).integrable_norm_mulVec (1 : Matrix n n ℝ)
  have hir := (isIsotropic_of_hasLaw_gaussianVector hr).integrable_norm_mulVec (1 : Matrix m m ℝ)
  have hEr := (isIsotropic_of_hasLaw_gaussianVector hr).integral_norm_mulVec_le
    (1 : Matrix m m ℝ)
  simp only [Matrix.one_mulVec] at hil hir hEr
  rw [← Real.sqrt_sq (frobNorm_nonneg (1 : Matrix m m ℝ)), frobNorm_one_sq] at hEr
  have hd := le_integral_norm_sub_integral_norm_of_hasLaw_gaussianVector hl hr Fintype.card_pos hnm
  have hpt (z : n ⊕ m → ℝ) :
      (1 - ε) * ‖WithLp.toLp 2 (z ∘ Sum.inr)‖ - ‖WithLp.toLp 2 (z ∘ Sum.inl)‖ ≤
        ⨅ i, ⨆ j, Sum.elim (u i) (t j) ⬝ᵥ z := by
    refine le_ciInf fun i => ?_
    obtain ⟨s, hs1, hsh⟩ := exists_norm_eq_one_dotProduct_eq (z ∘ Sum.inr)
    obtain ⟨j, hj⟩ := ht s hs1
    refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) j)
    have hz : Sum.elim (u i) (t j) ⬝ᵥ z = u i ⬝ᵥ (z ∘ Sum.inl) + t j ⬝ᵥ (z ∘ Sum.inr) := by
      conv_lhs => rw [← Sum.elim_comp_inl_inr z]
      exact sumElim_dotProduct_sumElim _ _ _ _
    have h1 := neg_abs_le (u i ⬝ᵥ (z ∘ Sum.inl))
    have h2 := abs_dotProduct_le (u i) (z ∘ Sum.inl)
    have h3 := (le_abs_self _).trans (abs_dotProduct_le (s - t j) (z ∘ Sum.inr))
    rw [sub_dotProduct, hsh] at h3
    have h5 := mul_le_mul_of_nonneg_right hj (norm_nonneg (WithLp.toLp 2 (z ∘ Sum.inr)))
    rw [hu i, one_mul] at h2
    rw [hz]
    linarith
  calc √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - ε * √(Fintype.card m : ℝ)
      ≤ ∫ z, ((1 - ε) * ‖WithLp.toLp 2 (z ∘ Sum.inr)‖ - ‖WithLp.toLp 2 (z ∘ Sum.inl)‖)
          ∂gaussianVector (n ⊕ m) := by
        rw [integral_sub (hir.const_mul _) hil, integral_const_mul]
        nlinarith [mul_le_mul_of_nonneg_left hEr hε]
    _ ≤ _ := integral_mono ((hir.const_mul _).sub hil)
        (integrable_iInf_iSup_of_hasGaussianLaw (X := fun i j z => Sum.elim (u i) (t j) ⬝ᵥ z)
          (hasGaussianLaw_dotProduct hV fun p : U × T => Sum.elim (u p.1) (t p.2))) hpt

/-- The matrix side: `min_u max_t ⟨t, G u⟩ ≤ σ_min(G) + ε ‖G‖` on `ε`-nets. -/
private theorem iInf_iSup_le_singularValues_add {U T : Type*} [Finite U]
    (G : Matrix m n ℝ) {k : ℕ} (hk : k + 1 = Fintype.card n) (u : U → n → ℝ) (t : T → m → ℝ)
    (ht : ∀ j, ‖WithLp.toLp 2 (t j)‖ = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hu : ∀ x : n → ℝ, ‖WithLp.toLp 2 x‖ = 1 → ∃ i, ‖WithLp.toLp 2 (x - u i)‖ ≤ ε) :
    ⨅ i, ⨆ j, t j ⬝ᵥ (G *ᵥ u i) ≤ singularValues G k + ε * specNorm G := by
  obtain ⟨x, hx1, hxσ⟩ :=
    exists_norm_eq_one_and_norm_mulVec_eq_singularValues G (k := k) (by omega)
  obtain ⟨i, hi⟩ := hu x hx1
  refine (ciInf_le (Finite.bddBelow_range _) i).trans (Real.iSup_le (fun j => ?_)
    (add_nonneg (singularValues_nonneg G k) (mul_nonneg hε (specNorm_nonneg G))))
  have h1 := (le_abs_self _).trans (abs_dotProduct_le (t j) (G *ᵥ u i))
  rw [ht j, one_mul] at h1
  have hsplit : G *ᵥ u i = G *ᵥ x + G *ᵥ (u i - x) := by
    rw [← Matrix.mulVec_add, add_sub_cancel]
  have h2 : ‖WithLp.toLp 2 (G *ᵥ u i)‖ ≤
      ‖WithLp.toLp 2 (G *ᵥ x)‖ + ‖WithLp.toLp 2 (G *ᵥ (u i - x))‖ := by
    rw [hsplit, WithLp.toLp_add]
    exact norm_add_le _ _
  have h3 := norm_toLp_mulVec_le G (u i - x)
  have h4 : ‖WithLp.toLp 2 (u i - x)‖ ≤ ε := by
    rw [← neg_sub, WithLp.toLp_neg, norm_neg]
    exact hi
  have h5 := mul_le_mul_of_nonneg_left h4 (specNorm_nonneg G)
  rw [hxσ] at h2
  linarith

/-- Gordon's lower bound on `ε`-nets, before `ε → 0`. -/
private theorem le_integral_singularValues_add (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ}
    (hk : k + 1 = Fintype.card n) (hnm : Fintype.card n ≤ Fintype.card m) {ε : ℝ}
    (hε0 : 0 < ε) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) -
        ε * (2 * √(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) ≤
      ∫ ω, singularValues (X ω) k ∂μ := by
  classical
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  have : Nonempty m := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨Nn, hNn1, hNn, -⟩ := exists_finite_isCover_sphere ℝ n (ε := ⟨ε, hε0.le⟩) hε0
  obtain ⟨Nm, hNm1, hNm, -⟩ := exists_finite_isCover_sphere ℝ m (ε := ⟨ε, hε0.le⟩) hε0
  let u : Nn → n → ℝ := fun i => WithLp.ofLp i.1
  let t : Nm → m → ℝ := fun j => WithLp.ofLp j.1
  have hu1 (i : Nn) : ‖WithLp.toLp 2 (u i)‖ = 1 := by
    simpa [u] using mem_sphere_zero_iff_norm.1 (hNn1 i.2)
  have ht1 (j : Nm) : ‖WithLp.toLp 2 (t j)‖ = 1 := by
    simpa [t] using mem_sphere_zero_iff_norm.1 (hNm1 j.2)
  have hcu (x : n → ℝ) (hx : ‖WithLp.toLp 2 x‖ = 1) : ∃ i, ‖WithLp.toLp 2 (x - u i)‖ ≤ ε := by
    obtain ⟨y, hy, hxy⟩ := exists_mem_norm_sub_le hNn hx
    exact ⟨⟨y, hy⟩, hxy⟩
  have hct (x : m → ℝ) (hx : ‖WithLp.toLp 2 x‖ = 1) : ∃ j, ‖WithLp.toLp 2 (x - t j)‖ ≤ ε := by
    obtain ⟨y, hy, hxy⟩ := exists_mem_norm_sub_le hNm hx
    exact ⟨⟨y, hy⟩, hxy⟩
  have : Nonempty Nn := by
    obtain ⟨i⟩ := ‹Nonempty n›
    obtain ⟨j, -⟩ := hcu (Pi.single i 1) (by rw [PiLp.toLp_single, PiLp.norm_single, norm_one])
    exact ⟨j⟩
  have h1 := le_integral_iInf_iSup_sumElim hnm u t hu1 hε0.le hct
  have h2 := integral_iInf_iSup_le_gordon hX u t
    (fun i => by rw [← norm_toLp_sq, hu1, one_pow]) (fun j => by rw [← norm_toLp_sq, ht1, one_pow])
  have hσ := integrable_singularValues_of_hasLaw_gaussianMatrix hX k
  have hG := (integrable_specNorm_of_hasLaw_gaussianMatrix hX).const_mul ε
  have h3 : ∫ ω, ⨅ i, ⨆ j, t j ⬝ᵥ (X ω *ᵥ u i) ∂μ ≤
      ∫ ω, (singularValues (X ω) k + ε * specNorm (X ω)) ∂μ :=
    integral_mono (integrable_iInf_iSup_gordon hX u t) (hσ.add hG)
      fun ω => iInf_iSup_le_singularValues_add (X ω) hk u t ht1 hε0.le hcu
  rw [integral_add hσ hG, integral_const_mul] at h3
  have h4 := mul_le_mul_of_nonneg_left (integral_specNorm_le_of_hasLaw_gaussianMatrix hX) hε0.le
  linarith

/-- From `x - ε C ≤ c` for all `ε > 0`, `x ≤ c`. -/
private theorem le_of_forall_sub_mul_le {x c C : ℝ} (h : ∀ ε : ℝ, 0 < ε → x - ε * C ≤ c) :
    x ≤ c := by
  have hlim : Filter.Tendsto (fun ε : ℝ => x - ε * C) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (x - 0 * C)) :=
    ((continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  rw [zero_mul, sub_zero] at hlim
  exact le_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact h ε hε)

/-- **Gordon's lower bound**: `√N - √n ≤ E σ_min(G)` for a standard Gaussian matrix `G : N × n`,
`σ_min` the singular value of index `k` with `k + 1 = n`.
[Vershynin2018, Exercise 7.3.4]; [DavidsonSzarek2001, Theorem II.13]; no tallness hypothesis
(for `n > N` the left side is negative and `σ_k` is the padding `0`). The upper bound is
`NLAlib.integral_specNorm_le_of_hasLaw_gaussianMatrix`.
Result: gaussian-matrix-extreme-singular-values -/
theorem le_integral_singularValues_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) ≤ ∫ ω, singularValues (X ω) k ∂μ := by
  by_cases hnm : Fintype.card n ≤ Fintype.card m
  · exact le_of_forall_sub_mul_le fun ε hε => le_integral_singularValues_add hX hk hnm hε
  · have h0 (ω : Ω) : singularValues (X ω) k = 0 := singularValues_of_card_rows_le _ (by omega)
    simp only [h0, integral_zero, sub_nonpos]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (not_le.1 hnm).le)

/-- Every singular value of a standard Gaussian matrix is sub-Gaussian about its mean with
proxy `1`: Gaussian concentration (`NLAlib.hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix`)
with the Frobenius-Lipschitz bound `NLAlib.abs_singularValues_sub_le_frobNorm`.
[Vershynin2018, proof of Corollary 7.3.3]. -/
theorem hasSubgaussianMGF_singularValues_sub_integral_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (k : ℕ) :
    HasSubgaussianMGF (fun ω => singularValues (X ω) k - ∫ ω', singularValues (X ω') k ∂μ) 1
      μ := by
  have h := hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix hX
    (f := fun A => singularValues A k) (abs_singularValues_sub_le k)
  rwa [one_pow] at h

/-- The upper deviation tail of the spectral norm: `P(√N + √n + t ≤ ‖G‖) ≤ e^{-t²/2}` for
`t ≥ 0`. [Vershynin2018, Corollary 7.3.3]; one-sided, hence without the factor `2` of the
source's two-sided form. -/
theorem measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t ≤ specNorm (X ω)} ≤
      Real.exp (-t ^ 2 / 2) := by
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hc := integral_specNorm_le_of_hasLaw_gaussianMatrix hX
  have h := measureReal_integral_add_le_of_hasLaw_gaussianMatrix hX (f := specNorm) (L := 1)
    (fun A B => by
      rw [NNReal.coe_one, one_mul]
      exact (abs_specNorm_sub_specNorm_le A B).trans (specNorm_le_frobNorm _)) ht
  rw [NNReal.coe_one, one_pow, mul_one] at h
  refine (measureReal_mono fun ω hω => ?_).trans h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith

/-- The lower deviation tail of the smallest singular value:
`P(σ_min(G) ≤ √N - √n - t) ≤ e^{-t²/2}` for `t ≥ 0`. [Vershynin2018, Corollary 7.3.3];
one-sided, hence without the factor `2` of the source's two-sided form. -/
theorem measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ} (hk : k + 1 = Fintype.card n) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | singularValues (X ω) k ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t} ≤
      Real.exp (-t ^ 2 / 2) := by
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hc := le_integral_singularValues_of_hasLaw_gaussianMatrix hX hk
  have h := measureReal_integral_add_le_of_hasLaw_gaussianMatrix hX
    (f := fun A => -singularValues A k) (L := 1)
    (fun A B => by
      rw [neg_sub_neg, abs_sub_comm]
      exact abs_singularValues_sub_le k A B) ht
  simp only [NNReal.coe_one, one_pow, mul_one, integral_neg] at h
  refine (measureReal_mono fun ω hω => ?_).trans h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith

variable [DecidableEq n]

/-- The upper Gram bound: `Gᴴ G ≤ (√N + √n + t)² • 1` outside probability `e^{-t²/2}`, for
`t ≥ 0`. [Vershynin2018, Corollary 7.3.3], one-sided and in Loewner form. -/
theorem measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ¬ (X ω)ᴴ * X ω ≤
      (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ^ 2 • (1 : Matrix n n ℝ)} ≤
      Real.exp (-t ^ 2 / 2) := by
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix hX ht)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt
  rw [not_le] at hlt
  exact hω ((specNorm_sq_le_iff_conjTranspose_mul_self_le (sq_nonneg _)).1
    (pow_le_pow_left₀ (specNorm_nonneg _) hlt.le 2))

/-- The lower Gram bound: `(√N - √n - t)² • 1 ≤ Gᴴ G` outside probability `e^{-t²/2}`, for
`0 ≤ t ≤ √N - √n` (the base must be nonnegative, or squaring it would make the bound false).
[Vershynin2018, Corollary 7.3.3], one-sided and in Loewner form. -/
theorem measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t) ^ 2 •
      (1 : Matrix n n ℝ) ≤ (X ω)ᴴ * X ω} ≤ Real.exp (-t ^ 2 / 2) := by
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hc : 0 ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t := by linarith
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · have : IsEmpty n := Fintype.card_eq_zero_iff.1 h0
    have he (ω : Ω) : (√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t) ^ 2 •
        (1 : Matrix n n ℝ) ≤ (X ω)ᴴ * X ω := le_of_eq (Subsingleton.elim _ _)
    simp only [he, not_true_eq_false, Set.ofPred_false, measureReal_empty]
    positivity
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by omega⟩
    refine (measureReal_mono fun ω hω => ?_).trans
      (measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix hX hk ht)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hlt
    rw [not_le] at hlt
    exact hω ((smul_one_le_smul_one (pow_le_pow_left₀ hc hlt.le 2)).trans
      (sq_singularValues_last_smul_one_le (X ω) hk))

/-- **The Gaussian Gram sandwich**: `(√N - √n - t)² • 1 ≤ Gᴴ G ≤ (√N + √n + t)² • 1` outside
probability `2 e^{-t²/2}`, for `0 ≤ t ≤ √N - √n`; the shape of the subspace-embedding predicate.
[Vershynin2018, Corollary 7.3.3], in Loewner form. -/
theorem
measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) :
    μ.real {ω | ¬ ((√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t) ^ 2 •
      (1 : Matrix n n ℝ) ≤ (X ω)ᴴ * X ω ∧ (X ω)ᴴ * X ω ≤
      (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ^ 2 • (1 : Matrix n n ℝ))} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have h1 :=
    measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix hX ht htn
  have h2 := measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix hX ht
  refine (measureReal_mono fun ω hω => ?_).trans ((measureReal_union_le _ _).trans
    (add_le_add h1 h2)) |>.trans_eq (two_mul _).symm
  simp only [Set.mem_ofPred_eq, Set.mem_union, not_and_or] at hω ⊢
  exact hω

end NLAlib
