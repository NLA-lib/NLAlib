/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Matrix.Mul
public import NLAlib.Matrix.Norms.Net
public import NLAlib.Probability.Distributions.GaussianComparison
public import NLAlib.Probability.Isotropic
public import NLAlib.RandomMatrix.Gaussian.Concentration

/-!
# The spectral norm of Gaussian matrices: Chevet's inequality

For a standard Gaussian matrix `G : m × n` and fixed `S : a × m`, `T : n × b`, Chevet's inequality
`E ‖S G T‖ ≤ ‖S‖ ‖T‖_F + ‖S‖_F ‖T‖`, its form with random factors independent of `G`, the tail of
`‖S G T‖` above that bound, and Gordon's upper bound `E ‖G‖ ≤ √N + √n` (`N = card m`,
`n = card n`) as the case `S = 1`, `T = 1`. Real throughout: the Gaussian matrix law is real.

The proof of Chevet's inequality compares, over finite symmetric nets of the unit spheres, the
process `⟨u, S G T v⟩ = ⟨Sᴴ u, G (T v)⟩` with `‖Sᴴ u‖ ⟨g, T v⟩ + ‖T v‖ ⟨h, Sᴴ u⟩` (`g`, `h`
independent standard Gaussian vectors) through the Sudakov–Fernique inequality
(`NLAlib.integral_iSup_le_integral_iSup_of_hasGaussianLaw`), then bounds the comparison process
by `NLAlib.IsIsotropic.integral_norm_mulVec_le`.

## Main results

* `NLAlib.integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix`: Chevet's inequality.
* `NLAlib.integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun`: Chevet's inequality
  with random factors independent of the Gaussian matrix.
* `NLAlib.measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix`: the tail of `‖S G T‖`.
* `NLAlib.integral_specNorm_le_of_hasLaw_gaussianMatrix`: `E ‖G‖ ≤ √N + √n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix
open EuclideanSpace (abs_dotProduct_le_norm norm_toLp_sq_eq_dotProduct_self)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n a b : Type*} [Fintype m]
  [Fintype n] [Fintype a] [Fintype b] {X : Ω → Matrix m n ℝ}

section Comparison

/-- The increments of `⟨x, G y⟩` are at most those of `‖x‖ ⟨g, y⟩ + ‖y‖ ⟨h, x⟩`. -/
private theorem chevet_increment_le (x x' : m → ℝ) (y y' : n → ℝ) :
    ((fun p : m × n => x p.1 * y p.2) - fun p => x' p.1 * y' p.2) ⬝ᵥ
        ((fun p : m × n => x p.1 * y p.2) - fun p => x' p.1 * y' p.2) ≤
      (Sum.elim (‖WithLp.toLp 2 x‖ • y) (‖WithLp.toLp 2 y‖ • x) -
          Sum.elim (‖WithLp.toLp 2 x'‖ • y') (‖WithLp.toLp 2 y'‖ • x')) ⬝ᵥ
        (Sum.elim (‖WithLp.toLp 2 x‖ • y) (‖WithLp.toLp 2 y‖ • x) -
          Sum.elim (‖WithLp.toLp 2 x'‖ • y') (‖WithLp.toLp 2 y'‖ • x')) := by
  have hp := (le_abs_self _).trans (abs_dotProduct_le_norm x x')
  have hq := (le_abs_self _).trans (abs_dotProduct_le_norm y y')
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_mul_eq_mul_dotProduct,
    sumElim_dotProduct_sumElim, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm x' x, dotProduct_comm y' y, ← norm_toLp_sq_eq_dotProduct_self x,
    ← norm_toLp_sq_eq_dotProduct_self x', ← norm_toLp_sq_eq_dotProduct_self y,
    ← norm_toLp_sq_eq_dotProduct_self y']
  nlinarith [sq_nonneg (‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ -
    ‖WithLp.toLp 2 x'‖ * ‖WithLp.toLp 2 y'‖), mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hq)]

variable {I : Type*} [Finite I]

private theorem integrable_iSup_dotProduct_mulVec (hX : HasLaw X (gaussianMatrix m n) μ)
    (x : I → m → ℝ) (y : I → n → ℝ) : Integrable (fun ω => ⨆ i, x i ⬝ᵥ (X ω *ᵥ y i)) μ := by
  simp only [Matrix.dotProduct_mulVec_eq_dotProduct_uncurry]
  exact integrable_iSup_of_hasGaussianLaw (hasGaussianLaw_dotProduct_of_hasLaw_gaussianVector
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX) _)

/-- The Sudakov–Fernique step of Chevet's inequality. -/
private theorem integral_iSup_le_integral_iSup_chevet (hX : HasLaw X (gaussianMatrix m n) μ)
    (x : I → m → ℝ) (y : I → n → ℝ) :
    ∫ ω, ⨆ i, x i ⬝ᵥ (X ω *ᵥ y i) ∂μ ≤
      ∫ z, ⨆ i, Sum.elim (‖WithLp.toLp 2 (x i)‖ • y i) (‖WithLp.toLp 2 (y i)‖ • x i) ⬝ᵥ z
        ∂gaussianVector (n ⊕ m) := by
  have hU := hasLaw_uncurry_of_hasLaw_gaussianMatrix hX
  have hV : HasLaw (fun z : n ⊕ m → ℝ => z) (gaussianVector (n ⊕ m)) (gaussianVector (n ⊕ m)) :=
    HasLaw.id
  simp only [Matrix.dotProduct_mulVec_eq_dotProduct_uncurry]
  refine integral_iSup_le_integral_iSup_of_hasGaussianLaw
    (hasGaussianLaw_dotProduct_of_hasLaw_gaussianVector hU _)
    (hasGaussianLaw_dotProduct_of_hasLaw_gaussianVector hV _)
    (fun i => integral_dotProduct_of_hasLaw_gaussianVector hU _)
    (fun i => integral_dotProduct_of_hasLaw_gaussianVector hV _) fun i j => ?_
  rw [integral_dotProduct_sub_dotProduct_sq_of_hasLaw_gaussianVector hU,
    integral_dotProduct_sub_dotProduct_sq_of_hasLaw_gaussianVector hV]
  exact chevet_increment_le _ _ _ _

/-- The comparison process is bounded by `‖S‖ ‖Tᵀ g‖ + ‖T‖ ‖S h‖` on unit vectors. -/
private theorem sumElim_dotProduct_sumElim_le (S : Matrix a m ℝ) (T : Matrix n b ℝ)
    {u : a → ℝ} {v : b → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1) (hv : ‖WithLp.toLp 2 v‖ = 1)
    (g : n → ℝ) (h : m → ℝ) :
    Sum.elim (‖WithLp.toLp 2 (u ᵥ* S)‖ • (T *ᵥ v)) (‖WithLp.toLp 2 (T *ᵥ v)‖ • (u ᵥ* S)) ⬝ᵥ
        Sum.elim g h ≤
      specNorm S * ‖WithLp.toLp 2 (Tᵀ *ᵥ g)‖ + specNorm T * ‖WithLp.toLp 2 (S *ᵥ h)‖ := by
  rw [sumElim_dotProduct_sumElim, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have h1 : ‖WithLp.toLp 2 (u ᵥ* S)‖ ≤ specNorm S := by
    have := norm_toLp_mulVec_le Sᵀ u
    rwa [Matrix.mulVec_transpose, hu, mul_one, specNorm_transpose] at this
  have h2 : ‖WithLp.toLp 2 (T *ᵥ v)‖ ≤ specNorm T := by
    have := norm_toLp_mulVec_le T v
    rwa [hv, mul_one] at this
  have h3 : (T *ᵥ v) ⬝ᵥ g ≤ ‖WithLp.toLp 2 (Tᵀ *ᵥ g)‖ := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    exact (le_abs_self _).trans ((abs_dotProduct_le_norm _ _).trans (by rw [hv, mul_one]))
  have h4 : (u ᵥ* S) ⬝ᵥ h ≤ ‖WithLp.toLp 2 (S *ᵥ h)‖ := by
    rw [← Matrix.dotProduct_mulVec]
    exact (le_abs_self _).trans ((abs_dotProduct_le_norm _ _).trans (by rw [hu, one_mul]))
  have h5 := mul_le_mul_of_nonneg_left h3 (norm_nonneg (WithLp.toLp 2 (u ᵥ* S)))
  have h6 := mul_le_mul_of_nonneg_left h4 (norm_nonneg (WithLp.toLp 2 (T *ᵥ v)))
  have h7 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (WithLp.toLp 2 (Tᵀ *ᵥ g)))
  have h8 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (WithLp.toLp 2 (S *ᵥ h)))
  linarith

end Comparison

/-- From `a (1 - 2ε) ≤ c` for all small `ε > 0`, `a ≤ c`. -/
private theorem le_of_forall_mul_one_sub_le {x c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → x * (1 - 2 * ε) ≤ c) : x ≤ c := by
  have hlim : Filter.Tendsto (fun ε : ℝ => x * (1 - 2 * ε)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (x * (1 - 2 * 0))) :=
    ((continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))).tendsto
      0).mono_left nhdsWithin_le_nhds
  rw [mul_zero, sub_zero, mul_one] at hlim
  exact le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
    exact h ε hε.1 hε.2)

/-- `‖S A T‖` is `‖S‖ ‖T‖`-Lipschitz in `A` for the Frobenius norm. -/
private theorem abs_specNorm_mul_mul_sub_le (S : Matrix a m ℝ) (T : Matrix n b ℝ)
    (A B : Matrix m n ℝ) :
    |specNorm (S * A * T) - specNorm (S * B * T)| ≤
      ((⟨specNorm S * specNorm T, by positivity⟩ : NNReal) : ℝ) * frobNorm (A - B) := by
  refine (abs_specNorm_sub_specNorm_le _ _).trans ?_
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  change _ ≤ specNorm S * specNorm T * frobNorm (A - B)
  calc specNorm (S * (A - B) * T) ≤ specNorm S * specNorm (A - B) * specNorm T :=
        (specNorm_mul_le _ _).trans (by gcongr; exact specNorm_mul_le _ _)
    _ ≤ specNorm S * frobNorm (A - B) * specNorm T := by gcongr; exact specNorm_le_frobNorm _
    _ = specNorm S * specNorm T * frobNorm (A - B) := by ring

section Fixed

/-- `‖S G T‖` is integrable for a standard Gaussian matrix `G`. -/
theorem integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    (S : Matrix a m ℝ) (T : Matrix n b ℝ) : Integrable (fun ω => specNorm (S * X ω * T)) μ :=
  integrable_comp_of_hasLaw_gaussianMatrix hX (f := fun A => specNorm (S * A * T))
    (abs_specNorm_mul_mul_sub_le S T)

/-- Chevet's inequality on `ε`-nets, before `ε → 0`. -/
private theorem integral_specNorm_mul_mul_mul_one_sub_le (hX : HasLaw X (gaussianMatrix m n) μ)
    (S : Matrix a m ℝ) (T : Matrix n b ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    (∫ ω, specNorm (S * X ω * T) ∂μ) * (1 - 2 * ε) ≤
      specNorm S * frobNorm T + frobNorm S * specNorm T := by
  classical
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  obtain ⟨Nb, hNb1, hNb, -⟩ := exists_finite_isCover_sphere ℝ b (ε := ⟨ε, hε0.le⟩) hε0
  obtain ⟨Na, hNa1, hNa, -⟩ := exists_finite_isCover_sphere ℝ a (ε := ⟨ε, hε0.le⟩) hε0
  let I := Bool × Na × Nb
  let u : I → a → ℝ := fun i => cond i.1 (WithLp.ofLp i.2.1.1) (-WithLp.ofLp i.2.1.1)
  let v : I → b → ℝ := fun i => WithLp.ofLp i.2.2.1
  let x : I → m → ℝ := fun i => u i ᵥ* S
  let y : I → n → ℝ := fun i => T *ᵥ v i
  have hun (i : I) : ‖WithLp.toLp 2 (u i)‖ = 1 := by
    have h1 := mem_sphere_zero_iff_norm.1 (hNa1 i.2.1.2)
    rcases i with ⟨_ | _, _, _⟩ <;> simpa [u] using h1
  have hvn (i : I) : ‖WithLp.toLp 2 (v i)‖ = 1 := by
    simpa [v] using mem_sphere_zero_iff_norm.1 (hNb1 i.2.2.2)
  have hpt (ω : Ω) : specNorm (S * X ω * T) * (1 - 2 * ε) ≤ ⨆ i, x i ⬝ᵥ (X ω *ᵥ y i) := by
    have hbdd : BddAbove (Set.range fun i => x i ⬝ᵥ (X ω *ᵥ y i)) := Finite.bddAbove_range _
    have key : ∀ w ∈ (Nb : Set (EuclideanSpace ℝ b)), ∀ z ∈ (Na : Set (EuclideanSpace ℝ a)),
        ‖star (WithLp.ofLp z) ⬝ᵥ ((S * X ω * T) *ᵥ WithLp.ofLp w)‖ ≤
          ⨆ i, x i ⬝ᵥ (X ω *ᵥ y i) := by
      intro w hw z hz
      have h1 := le_ciSup hbdd ((true, ⟨z, hz⟩, ⟨w, hw⟩) : I)
      have h2 := le_ciSup hbdd ((false, ⟨z, hz⟩, ⟨w, hw⟩) : I)
      simp only [x, y, u, v, cond_true, cond_false, Matrix.neg_vecMul, neg_dotProduct] at h1 h2
      rw [Real.norm_eq_abs, star_trivial, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, abs_le']
      exact ⟨h1, h2⟩
    have hM0 : 0 ≤ ⨆ i, x i ⬝ᵥ (X ω *ᵥ y i) := by
      rcases isEmpty_or_nonempty I with hI | ⟨⟨s, z, w⟩⟩
      · rw [Real.iSup_of_isEmpty]
      · exact (norm_nonneg _).trans (key w.1 w.2 z.1 z.2)
    have h := specNorm_le_div_of_isCover_of_isCover (S * X ω * T) (ε := ⟨ε, hε0.le⟩)
      (mod_cast hε) hNb hNa (hNa1.trans Metric.sphere_subset_closedBall) hM0 key
    change _ ≤ _ / (1 - 2 * ε) at h
    rwa [le_div_iff₀ (by linarith)] at h
  have hiso_l :=
    isIsotropic_of_hasLaw_gaussianVector (hasLaw_comp_inl_gaussianVector (n := n) (m := m))
  have hiso_r :=
    isIsotropic_of_hasLaw_gaussianVector (hasLaw_comp_inr_gaussianVector (n := n) (m := m))
  have hV : HasLaw (fun z : n ⊕ m → ℝ => z) (gaussianVector (n ⊕ m)) (gaussianVector (n ⊕ m)) :=
    HasLaw.id
  have hbd (z : n ⊕ m → ℝ) :
      ⨆ i, Sum.elim (‖WithLp.toLp 2 (x i)‖ • y i) (‖WithLp.toLp 2 (y i)‖ • x i) ⬝ᵥ z ≤
        specNorm S * ‖WithLp.toLp 2 (Tᵀ *ᵥ (z ∘ Sum.inl))‖ +
          specNorm T * ‖WithLp.toLp 2 (S *ᵥ (z ∘ Sum.inr))‖ := by
    refine Real.iSup_le (fun i => ?_) (by positivity)
    have h := sumElim_dotProduct_sumElim_le S T (hun i) (hvn i) (z ∘ Sum.inl) (z ∘ Sum.inr)
    rwa [Sum.elim_comp_inl_inr] at h
  calc (∫ ω, specNorm (S * X ω * T) ∂μ) * (1 - 2 * ε)
      = ∫ ω, specNorm (S * X ω * T) * (1 - 2 * ε) ∂μ := (integral_mul_const _ _).symm
    _ ≤ ∫ ω, ⨆ i, x i ⬝ᵥ (X ω *ᵥ y i) ∂μ :=
        integral_mono ((integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix hX S T).mul_const _)
          (integrable_iSup_dotProduct_mulVec hX x y) hpt
    _ ≤ ∫ z, ⨆ i, Sum.elim (‖WithLp.toLp 2 (x i)‖ • y i) (‖WithLp.toLp 2 (y i)‖ • x i) ⬝ᵥ z
          ∂gaussianVector (n ⊕ m) := integral_iSup_le_integral_iSup_chevet hX x y
    _ ≤ ∫ z, (specNorm S * ‖WithLp.toLp 2 (Tᵀ *ᵥ (z ∘ Sum.inl))‖ +
          specNorm T * ‖WithLp.toLp 2 (S *ᵥ (z ∘ Sum.inr))‖) ∂gaussianVector (n ⊕ m) :=
        integral_mono (integrable_iSup_of_hasGaussianLaw
            (hasGaussianLaw_dotProduct_of_hasLaw_gaussianVector hV _))
          (((hiso_l.integrable_norm_mulVec Tᵀ).const_mul _).add
            ((hiso_r.integrable_norm_mulVec S).const_mul _)) hbd
    _ ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by
        rw [integral_add ((hiso_l.integrable_norm_mulVec Tᵀ).const_mul _)
          ((hiso_r.integrable_norm_mulVec S).const_mul _), integral_const_mul,
          integral_const_mul]
        have h1 := hiso_l.integral_norm_mulVec_le Tᵀ
        have h2 := hiso_r.integral_norm_mulVec_le S
        rw [frobNorm_transpose] at h1
        have h3 := mul_le_mul_of_nonneg_left h1 (specNorm_nonneg S)
        have h4 := mul_le_mul_of_nonneg_left h2 (specNorm_nonneg T)
        linarith [mul_comm (frobNorm S) (specNorm T)]

/-- **Chevet's inequality**: for a standard Gaussian matrix `G` and fixed `S`, `T`,
`E ‖S G T‖ ≤ ‖S‖ ‖T‖_F + ‖S‖_F ‖T‖`.
[Vershynin2018, Theorem 8.7.1]; [HalkoMartinssonTropp2011, Proposition 10.1]; Vershynin states
it for a general bilinear supremum over two sets, here the matrix form of Halko, Martinsson and
Tropp, over any finite index types.
Result: chevet-inequality -/
theorem integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, specNorm (S * X ω * T) ∂μ ≤ specNorm S * frobNorm T + frobNorm S * specNorm T :=
  le_of_forall_mul_one_sub_le fun _ hε0 hε => integral_specNorm_mul_mul_mul_one_sub_le hX S T hε0 hε

/-- The tail of `‖S G T‖` above Chevet's bound:
`P(‖S‖ ‖T‖_F + ‖S‖_F ‖T‖ + t ≤ ‖S G T‖) ≤ exp (-t² / (2 ‖S‖² ‖T‖²))` for `t ≥ 0`, by Gaussian
concentration (`NLAlib.measureReal_integral_add_le_of_hasLaw_gaussianMatrix`) with Lipschitz
constant `‖S‖ ‖T‖` and Chevet's inequality. [HalkoMartinssonTropp2011, proof of Theorem 10.8],
the deviation step of the range finder's spectral tail. If `S = 0` or `T = 0` the right side is
`exp 0 = 1` (Lean's `x / 0 = 0`). -/
theorem measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | specNorm S * frobNorm T + frobNorm S * specNorm T + t ≤
      specNorm (S * X ω * T)} ≤ Real.exp (-t ^ 2 / (2 * (specNorm S * specNorm T) ^ 2)) := by
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hc := integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix hX S T
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_integral_add_le_of_hasLaw_gaussianMatrix hX (abs_specNorm_mul_mul_sub_le S T) ht)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith

/-- `‖G‖` is integrable for a standard Gaussian matrix `G`. -/
theorem integrable_specNorm_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    Integrable (fun ω => specNorm (X ω)) μ :=
  integrable_comp_of_hasLaw_gaussianMatrix hX (L := 1) fun A B => by
    rw [NNReal.coe_one, one_mul]
    exact (abs_specNorm_sub_specNorm_le A B).trans (specNorm_le_frobNorm _)

/-- **Gordon's upper bound**: `E ‖G‖ ≤ √N + √n` for a standard Gaussian matrix `G : N × n`, the
case `S = 1`, `T = 1` of Chevet's inequality.
[Vershynin2018, Theorem 7.3.1]; [DavidsonSzarek2001, Theorem II.13]; the lower bound
`√N - √n ≤ E σ_min(G)` is `NLAlib.le_integral_singularValues_of_hasLaw_gaussianMatrix`.
Result: gaussian-matrix-extreme-singular-values -/
theorem integral_specNorm_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∫ ω, specNorm (X ω) ∂μ ≤ √(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) := by
  classical
  have h := integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix hX (1 : Matrix m m ℝ)
    (1 : Matrix n n ℝ)
  simp only [Matrix.one_mul, Matrix.mul_one] at h
  rw [← Real.sqrt_sq (frobNorm_nonneg (1 : Matrix m m ℝ)), frobNorm_one_sq,
    ← Real.sqrt_sq (frobNorm_nonneg (1 : Matrix n n ℝ)), frobNorm_one_sq] at h
  have h1 := specNorm_one_le (n := m) (𝕜 := ℝ)
  have h2 := specNorm_one_le (n := n) (𝕜 := ℝ)
  have h3 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (Fintype.card n : ℝ))
  have h4 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (Fintype.card m : ℝ))
  linarith

end Fixed

section Independent

variable {α : Type*} [MeasurableSpace α] {Y : Ω → α} {S : α → Matrix a m ℝ}
  {T : α → Matrix n b ℝ}

private theorem measurable_specNorm_mul_mul (hS : Measurable S) (hT : Measurable T) :
    Measurable fun q : α × Matrix m n ℝ => specNorm (S q.1 * q.2 * T q.1) :=
  continuous_specNorm.measurable.comp
    (((hS.comp measurable_fst).matrix_mul measurable_snd).matrix_mul (hT.comp measurable_fst))

private theorem measurable_chevet (hS : Measurable S) (hT : Measurable T) :
    Measurable fun y => specNorm (S y) * frobNorm (T y) + frobNorm (S y) * specNorm (T y) :=
  ((continuous_specNorm.measurable.comp hS).mul (continuous_frobNorm.measurable.comp hT)).add
    ((continuous_frobNorm.measurable.comp hS).mul (continuous_specNorm.measurable.comp hT))

/-- Chevet's inequality under the joint law, as lower integrals. -/
private theorem lintegral_specNorm_mul_mul_le (hY : AEMeasurable Y μ)
    (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ) (hS : Measurable S)
    (hT : Measurable T) :
    ∫⁻ ω, ENNReal.ofReal (specNorm (S (Y ω) * X ω * T (Y ω))) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
        frobNorm (S (Y ω)) * specNorm (T (Y ω))) ∂μ := by
  have hP : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hF := ENNReal.measurable_ofReal.comp (measurable_specNorm_mul_mul hS hT)
  have hG := ENNReal.measurable_ofReal.comp (measurable_chevet hS hT)
  have hmap : μ.map (fun ω => (Y ω, X ω)) = (μ.map Y).prod (gaussianMatrix m n) := by
    rw [← hX.map_eq]
    exact (indepFun_iff_map_prod_eq_prod_map_map hY hX.aemeasurable).1 hXY
  have hid : HasLaw (fun x : Matrix m n ℝ => x) (gaussianMatrix m n) (gaussianMatrix m n) :=
    HasLaw.id
  have hinner (y : α) : ∫⁻ x, ENNReal.ofReal (specNorm (S y * x * T y)) ∂(gaussianMatrix m n) ≤
      ENNReal.ofReal (specNorm (S y) * frobNorm (T y) + frobNorm (S y) * specNorm (T y)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix hid (S y) (T y))
      (ae_of_all _ fun _ => specNorm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix hid (S y) (T y))
  calc ∫⁻ ω, ENNReal.ofReal (specNorm (S (Y ω) * X ω * T (Y ω))) ∂μ
      = ∫⁻ q, ENNReal.ofReal (specNorm (S q.1 * q.2 * T q.1)) ∂(μ.map fun ω => (Y ω, X ω)) :=
        (lintegral_map' hF.aemeasurable (hY.prodMk hX.aemeasurable)).symm
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (specNorm (S y * x * T y)) ∂(gaussianMatrix m n)
          ∂(μ.map Y) := by
        rw [hmap, lintegral_prod
          (fun q : α × Matrix m n ℝ => ENNReal.ofReal (specNorm (S q.1 * q.2 * T q.1)))
          hF.aemeasurable]
    _ ≤ ∫⁻ y, ENNReal.ofReal (specNorm (S y) * frobNorm (T y) +
          frobNorm (S y) * specNorm (T y)) ∂(μ.map Y) := lintegral_mono hinner
    _ = ∫⁻ ω, ENNReal.ofReal (specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
          frobNorm (S (Y ω)) * specNorm (T (Y ω))) ∂μ :=
        lintegral_map' hG.aemeasurable hY

/-- `‖S G T‖` is integrable when the random factors `S`, `T` are functions of a variable `Y`
independent of the Gaussian matrix `G` and Chevet's bound for them is integrable. -/
theorem integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix_of_indepFun (hY : AEMeasurable Y μ)
    (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ) (hS : Measurable S)
    (hT : Measurable T)
    (hST : Integrable (fun ω => specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
      frobNorm (S (Y ω)) * specNorm (T (Y ω))) μ) :
    Integrable (fun ω => specNorm (S (Y ω) * X ω * T (Y ω))) μ := by
  refine ⟨((measurable_specNorm_mul_mul hS hT).comp_aemeasurable
    (hY.prodMk hX.aemeasurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => specNorm_nonneg _)]
  exact (lintegral_specNorm_mul_mul_le hY hX hXY hS hT).trans_lt hST.lintegral_lt_top

/-- **Chevet's inequality with random factors** independent of the Gaussian matrix:
`E ‖S G T‖ ≤ E [‖S‖ ‖T‖_F + ‖S‖_F ‖T‖]` when `S`, `T` are functions of a variable `Y`
independent of `G`. [HalkoMartinssonTropp2011, proof of Theorem 10.6], where it is applied
conditionally on the independent block. The integrability hypothesis `hST` excludes the junk
value `0` of a non-integrable right side. -/
theorem integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun (hY : AEMeasurable Y μ)
    (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ) (hS : Measurable S)
    (hT : Measurable T)
    (hST : Integrable (fun ω => specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
      frobNorm (S (Y ω)) * specNorm (T (Y ω))) μ) :
    ∫ ω, specNorm (S (Y ω) * X ω * T (Y ω)) ∂μ ≤
      ∫ ω, (specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
        frobNorm (S (Y ω)) * specNorm (T (Y ω))) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => specNorm_nonneg _)
      ((measurable_specNorm_mul_mul hS hT).comp_aemeasurable
        (hY.prodMk hX.aemeasurable)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => by positivity)
      hST.aestronglyMeasurable]
  exact ENNReal.toReal_mono hST.lintegral_lt_top.ne (lintegral_specNorm_mul_mul_le hY hX hXY hS hT)

end Independent

end NLAlib
