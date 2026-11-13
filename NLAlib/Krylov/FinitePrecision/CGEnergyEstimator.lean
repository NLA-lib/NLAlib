/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGEnergy

/-!
# Delayed physical energy estimators for finite-precision CG

The sum of the computed decrements over a delayed interval estimates the decrease of the
actual computed iterate's energy. The error budget depends only on precision, spectral
endpoints, the right-hand side, and the interval indices. All local quadratic errors are
retained; neither physical energy nor Euclidean error monotonicity is assumed.

This adapts [StrakosTichy2002, Theorem 10.1] to the arithmetic model and proved a priori
window of `CGRun`, replacing its asymptotic errors and near-monotonicity reasoning with
explicit finite bounds. The scalar decrement sum is evaluated exactly in these statements.

## Main results

* `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le`: interval reliability.
* `NLAlib.CGRun.sum_sub_le_quadForm_sub_x`: certified delayed lower estimate.
* `NLAlib.CGRun.quadForm_sub_x_le_of_sum_add_le`: sufficient stopping criterion.
* `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_backwardH_sub_cgIterate_le`:
  absolute physical/model comparison.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The delayed-energy rounding factor, currently <!-- value cgEnergyEstimatorFactor j d -->
$150d(j+d)$. It is an input-only bound in this arithmetic model, not a literature constant. -/
noncomputable irreducible_def cgEnergyEstimatorFactor (j d : ℕ) : ℝ :=
  150 * (d : ℝ) * (j + d)

/-- The delayed-energy rounding factor is nonnegative. -/
theorem cgEnergyEstimatorFactor_nonneg (j d : ℕ) : 0 ≤ cgEnergyEstimatorFactor j d := by
  rw [cgEnergyEstimatorFactor_def]
  positivity

/-- The delayed-energy factor is at most <!-- value cgEnergyEstimatorFactor j d -->$150d(j+d)$. -/
theorem cgEnergyEstimatorFactor_le (j d : ℕ) :
    cgEnergyEstimatorFactor j d ≤ 150 * (d : ℝ) * (j + d) := by
  rw [cgEnergyEstimatorFactor_def]

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

private theorem estimator_facts {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) :
    1 ≤ a' / a ∧ specNorm C.A ≤ a' ∧ C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
  have h := C.isHermitian.spectrum_subset_iff.mp hs 0 (by
    simp only [Fintype.card_fin]; exact C.n_pos)
  have haa' := h.1.trans h.2
  have hκ : 1 ≤ a' / a := (one_le_div ha).mpr haa'
  have hm : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  have hspec : specNorm C.A ≤ a' := by
    have hc : n - 1 + 1 = Fintype.card (Fin n) := by
      simp only [Fintype.card_fin]; have := C.n_pos; omega
    have he := C.isHermitian.spectrum_subset_iff.mp hs (n - 1) (by
      simp only [Fintype.card_fin]; have := C.n_pos; omega)
    rw [C.isHermitian.specNorm_eq_max hc, abs_of_pos (ha.trans_le h.1),
      abs_of_pos (ha.trans_le he.1)]
    exact max_le h.2 he.2
  refine ⟨hκ, hspec, ?_⟩
  have hκ0 : 0 ≤ a' / a := by linarith
  have hz : 0 ≤ C.ε * (a' / a) := mul_nonneg C.ε_nonneg hκ0
  have h1 : 1 ≤ (k : ℝ) ^ 2 * Real.sqrt k * (a' / a) := by
    have hsqrt := Real.one_le_sqrt.mpr hm
    have hM : 1 ≤ (k : ℝ) ^ 2 * Real.sqrt k := by
      simpa only [one_mul] using mul_le_mul
        (by nlinarith : 1 ≤ (k : ℝ) ^ 2) hsqrt (by norm_num) (by positivity)
    simpa only [one_mul] using mul_le_mul hM hκ (by norm_num) (by positivity)
  have h2 := mul_le_mul_of_nonneg_right h1 hz
  unfold CGPrecisionHorizon at hsmall
  nlinarith

private theorem estimator_norms {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (xs - C.x j)‖ ≤ 2 * ‖WithLp.toLp 2 C.b‖ / a ∧
    ‖WithLp.toLp 2 (C.x j)‖ ≤ 3 * ‖WithLp.toLp 2 C.b‖ / a := by
  set B := ‖WithLp.toLp 2 C.b‖
  have hxs : ‖WithLp.toLp 2 xs‖ ≤ B / a := by
    have h1 := C.mul_norm_sq_le_quadForm hs xs
    rw [quadForm_def, star_trivial, hx] at h1
    have h2 := (le_abs_self _).trans (EuclideanSpace.abs_dotProduct_le_norm xs C.b)
    rw [le_div_iff₀ ha]
    rcases (norm_nonneg (WithLp.toLp 2 xs)).lt_or_eq with hpos | hzero
    · nlinarith
    · rw [← hzero, zero_mul]
      exact norm_nonneg _
  have hE0 : quadForm C.A xs ≤ B ^ 2 / a := by
    rw [quadForm_def, star_trivial, hx]
    refine (le_abs_self _).trans ((EuclideanSpace.abs_dotProduct_le_norm xs C.b).trans ?_)
    calc ‖WithLp.toLp 2 xs‖ * ‖WithLp.toLp 2 C.b‖ ≤
          (B / a) * B := mul_le_mul_of_nonneg_right hxs (norm_nonneg _)
      _ = B ^ 2 / a := by ring
  have hE := (C.quadForm_sub_x_le ha hs hsmall hx hj).trans
    (mul_le_mul_of_nonneg_left hE0 (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000))
  have he : ‖WithLp.toLp 2 (xs - C.x j)‖ ≤ 2 * B / a := by
    have hlow := C.mul_norm_sq_le_quadForm hs (xs - C.x j)
    have hsq : ‖WithLp.toLp 2 (xs - C.x j)‖ ^ 2 ≤ (2 * B / a) ^ 2 := by
      rw [← mul_le_mul_iff_right₀ ha]
      have heq : a * (2 * B / a) ^ 2 = 4 * (B ^ 2 / a) := by field_simp; ring
      rw [heq]
      nlinarith [show 0 ≤ B ^ 2 / a by positivity]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  refine ⟨he, ?_⟩
  have ht := norm_sub_le (WithLp.toLp 2 xs) (WithLp.toLp 2 (xs - C.x j))
  rw [← WithLp.toLp_sub, sub_sub_cancel] at ht
  calc ‖WithLp.toLp 2 (C.x j)‖ ≤
        ‖WithLp.toLp 2 xs‖ + ‖WithLp.toLp 2 (xs - C.x j)‖ := ht
    _ ≤ B / a + 2 * B / a := add_le_add hxs he
    _ = 3 * B / a := by ring

private theorem estimator_μ {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    |C.μ j - C.p j ⬝ᵥ (C.A *ᵥ C.p j)| ≤
      3 * (C.ε * (a' / a)) * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) := by
  obtain ⟨hκ, hspec, -⟩ := C.estimator_facts ha hs hsmall
  have hε := C.ε_nonneg
  set N := ‖WithLp.toLp 2 (C.p j)‖
  set P := C.p j ⬝ᵥ (C.A *ᵥ C.p j)
  set z := C.ε * (a' / a)
  have hPlow : a * N ^ 2 ≤ P := by
    simpa only [quadForm_def, star_trivial] using C.mul_norm_sq_le_quadForm hs (C.p j)
  have hN : a' * N ^ 2 ≤ (a' / a) * P := by
    have h := mul_le_mul_of_nonneg_left hPlow (by positivity : 0 ≤ a' / a)
    have heq : (a' / a) * (a * N ^ 2) = a' * N ^ 2 := by field_simp
    rwa [heq] at h
  have hpes : |C.p j ⬝ᵥ C.es j| ≤ C.ε * a' * N ^ 2 := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    have he := (C.norm_es_le j hj).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hspec hε) (norm_nonneg _))
    have := mul_le_mul_of_nonneg_left he (norm_nonneg (WithLp.toLp 2 (C.p j)))
    nlinarith
  have heμ : |C.eμ j| ≤ 2 * C.ε * a' * N ^ 2 := by
    have hsn : ‖WithLp.toLp 2 (C.s j)‖ ≤ 2 * a' * N := by
      refine (C.norm_s_le hj).trans ?_
      have ha' : 0 ≤ a' := by have := (one_le_div ha).mp hκ; linarith
      have h := mul_le_mul_of_nonneg_left hspec (by positivity : 0 ≤ 1 + C.ε)
      have hcoef : (1 + C.ε) * specNorm C.A ≤ 2 * a' :=
        h.trans (mul_le_mul_of_nonneg_right
          (show 1 + C.ε ≤ 2 by linarith [C.ε_le]) ha')
      nlinarith [mul_le_mul_of_nonneg_right hcoef (norm_nonneg (WithLp.toLp 2 (C.p j)))]
    have h := mul_le_mul_of_nonneg_left hsn (by positivity : 0 ≤ C.ε * N)
    exact (C.abs_eμ_le j hj).trans (by nlinarith)
  have hμeq : C.μ j = P + C.p j ⬝ᵥ C.es j + C.eμ j := by
    rw [C.μ_eq j hj, C.s_eq j hj, dotProduct_add]
  have hμ : |C.μ j - P| ≤ 3 * z * P := by
    have h := abs_add_le (C.p j ⬝ᵥ C.es j) (C.eμ j)
    rw [hμeq]
    have hN' := mul_le_mul_of_nonneg_left hN hε
    apply abs_le.mpr
    constructor <;> nlinarith [(abs_le.mp hpes).1, (abs_le.mp hpes).2,
      (abs_le.mp heμ).1, (abs_le.mp heμ).2]
  exact hμ

private theorem estimator_curvature {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    |C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) - C.γ j * C.ρ j ^ 2| ≤
      7 * (C.ε * (a' / a)) * (C.γ j * C.ρ j ^ 2) := by
  obtain ⟨hκ, -, hzle⟩ := C.estimator_facts ha hs hsmall
  have hε := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hεz : C.ε ≤ C.ε * (a' / a) := le_mul_of_one_le_right hε hκ
  set P := C.p j ⬝ᵥ (C.A *ᵥ C.p j)
  set z := C.ε * (a' / a)
  set T := C.γ j ^ 2 * P
  set s := C.γ j * C.ρ j ^ 2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hμ := C.estimator_μ ha hs hsmall hj
  have hgm := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le] at hgm
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have heγ := abs_le.mp (C.abs_eγ_le j hj)
  have hprod : |(1 + C.θ j) * (1 + C.eγ j) - 1| ≤ 3 * C.ε := by
    have hmul := mul_le_mul (C.abs_θ_le j hj.le) (C.abs_eγ_le j hj)
      (abs_nonneg _) hε
    rw [← abs_mul] at hmul
    have := abs_add_three (C.θ j) (C.eγ j) (C.θ j * C.eγ j)
    have heq : (1 + C.θ j) * (1 + C.eγ j) - 1 =
        C.θ j + C.eγ j + C.θ j * C.eγ j := by ring
    rw [heq]
    have hεsq : C.ε ^ 2 ≤ C.ε := by
      nlinarith [mul_nonneg hε (show 0 ≤ 1 - C.ε by linarith [C.ε_le])]
    nlinarith [C.abs_θ_le j hj.le, C.abs_eγ_le j hj]
  have hgmabs : |C.γ j ^ 2 * C.μ j - s| ≤ 3 * z * s := by
    have heq : C.γ j ^ 2 * C.μ j - s =
        s * ((1 + C.θ j) * (1 + C.eγ j) - 1) := by
      dsimp only [s]
      nlinarith [congrArg (fun t : ℝ => C.γ j * t) hgm]
    rw [heq, abs_mul, abs_of_nonneg hs0]
    nlinarith [mul_le_mul_of_nonneg_left hprod hs0,
      mul_le_mul_of_nonneg_right hεz hs0]
  have hTμ : |T - C.γ j ^ 2 * C.μ j| ≤ 3 * z * T := by
    have heq : T - C.γ j ^ 2 * C.μ j = -(C.γ j ^ 2 * (C.μ j - P)) := by
      dsimp only [T]; ring
    rw [heq, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg (C.γ j))]
    calc C.γ j ^ 2 * |C.μ j - P| ≤ C.γ j ^ 2 * (3 * z * P) :=
          mul_le_mul_of_nonneg_left hμ (sq_nonneg (C.γ j))
      _ = 3 * z * T := by dsimp only [T]; ring
  have hT := C.γ_sq_mul_dotProduct_mulVec_le_mul ha hs hsmall hj
  have ht := abs_add_le (T - C.γ j ^ 2 * C.μ j) (C.γ j ^ 2 * C.μ j - s)
  have hTs : |T - s| ≤ 3 * z * T + 3 * z * s := by
    have heq : T - C.γ j ^ 2 * C.μ j + (C.γ j ^ 2 * C.μ j - s) = T - s := by ring
    rw [heq] at ht
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 3 * z)
  have hbudget : 3 * z * ((1 + 6 * z) * s) + 3 * z * s ≤ 7 * z * s := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 18 - z by dsimp [z]; linarith)
      (mul_nonneg hz hs0)]
  exact hTs.trans (by nlinarith)

private theorem estimator_bilinear {a' : ℝ} (hspec : specNorm C.A ≤ a')
    (v w : Fin n → ℝ) :
    |v ⬝ᵥ (C.A *ᵥ w)| ≤ a' * ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 w‖ := by
  have hAw := (norm_toLp_mulVec_le C.A w).trans
    (mul_le_mul_of_nonneg_right hspec (norm_nonneg _))
  have h := (EuclideanSpace.abs_dotProduct_le_norm v (C.A *ᵥ w)).trans
    (mul_le_mul_of_nonneg_left hAw (norm_nonneg (WithLp.toLp 2 v)))
  nlinarith

private theorem estimator_rounding {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    |quadForm C.A (xs - C.x (j + 1)) -
      quadForm C.A (xs - C.x j - C.γ j • C.p j)| ≤
      32 * (C.ε * (a' / a)) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  obtain ⟨hκ, hspec, hzle⟩ := C.estimator_facts ha hs hsmall
  obtain ⟨he, hxj⟩ := C.estimator_norms ha hs hsmall hx hj.le
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hγp := C.γ_mul_norm_p_le ha hs hsmall hj
  set B := ‖WithLp.toLp 2 C.b‖
  set w := xs - C.x j - C.γ j • C.p j
  set V := ‖WithLp.toLp 2 (C.ex j)‖
  have ha' : 0 ≤ a' := by have := (one_le_div ha).mp hκ; linarith
  have hw : ‖WithLp.toLp 2 w‖ ≤ 7 / 2 * B / a := by
    have ht := norm_sub_le (WithLp.toLp 2 (xs - C.x j))
      (WithLp.toLp 2 (C.γ j • C.p j))
    rw [← WithLp.toLp_sub, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hγ] at ht
    change ‖WithLp.toLp 2 w‖ ≤ _ at ht
    calc ‖WithLp.toLp 2 w‖ ≤
          ‖WithLp.toLp 2 (xs - C.x j)‖ + C.γ j * ‖WithLp.toLp 2 (C.p j)‖ := ht
      _ ≤ 2 * B / a + 3 / 2 * B / a := add_le_add he hγp
      _ = 7 / 2 * B / a := by ring
  have hV : V ≤ C.ε * (9 / 2 * B / a) := by
    have ht := C.norm_ex_le j hj
    rw [abs_of_pos hγ] at ht
    have h := mul_le_mul_of_nonneg_left (show
      ‖WithLp.toLp 2 (C.x j)‖ + C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤
        9 / 2 * B / a by
          calc ‖WithLp.toLp 2 (C.x j)‖ + C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤
                3 * B / a + 3 / 2 * B / a := add_le_add hxj hγp
            _ = 9 / 2 * B / a := by ring) C.ε_nonneg
    exact ht.trans h
  have hcross : |C.ex j ⬝ᵥ (C.A *ᵥ w)| ≤
      a' * (C.ε * (9 / 2 * B / a)) * (7 / 2 * B / a) := by
    refine (C.estimator_bilinear hspec (C.ex j) w).trans ?_
    gcongr
  have hQv : |quadForm C.A (C.ex j)| ≤ a' * (C.ε * (9 / 2 * B / a)) ^ 2 := by
    have h := C.estimator_bilinear hspec (C.ex j) (C.ex j)
    rw [quadForm_def, star_trivial]
    refine h.trans ?_
    have hv0 : 0 ≤ V := norm_nonneg _
    have hh := pow_le_pow_left₀ hv0 hV 2
    nlinarith [mul_le_mul_of_nonneg_left hh ha']
  have hxe : xs - C.x (j + 1) = w - C.ex j := by
    rw [C.x_succ j hj]
    dsimp only [w]
    abel
  rw [hxe, C.quadForm_sub_eq]
  have ht := abs_add_le (-2 * (C.ex j ⬝ᵥ (C.A *ᵥ w))) (quadForm C.A (C.ex j))
  have heq : quadForm C.A w - 2 * (C.ex j ⬝ᵥ (C.A *ᵥ w)) +
      quadForm C.A (C.ex j) - quadForm C.A w =
      -2 * (C.ex j ⬝ᵥ (C.A *ᵥ w)) + quadForm C.A (C.ex j) := by ring
  rw [heq]
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  have heq' : 2 * (a' * (C.ε * (9 / 2 * B / a)) * (7 / 2 * B / a)) +
      a' * (C.ε * (9 / 2 * B / a)) ^ 2 =
      (63 / 2 + 81 / 4 * C.ε) * (C.ε * (a' / a)) * (B ^ 2 / a) := by ring
  have hε : C.ε ≤ 1 / 10 ^ 5 :=
    (le_mul_of_one_le_right C.ε_nonneg hκ).trans hzle
  have hbudget := mul_le_mul_of_nonneg_right
    (show 63 / 2 + 81 / 4 * C.ε ≤ (32 : ℝ) by linarith)
    (show 0 ≤ (C.ε * (a' / a)) * (B ^ 2 / a) by positivity)
  nlinarith

private theorem estimator_step {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    |(quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + 1))) -
      C.γ j * C.ρ j ^ 2| ≤
      150 * (j + 1) * (C.ε * (a' / a)) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  obtain ⟨hκ, -, -⟩ := C.estimator_facts ha hs hsmall
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  set s := C.γ j * C.ρ j ^ 2
  set z := C.ε * (a' / a)
  set u := ‖WithLp.toLp 2 C.b‖ ^ 2 / a
  set g := C.b - C.A *ᵥ C.x j - C.r j
  set w := xs - C.x j - C.γ j • C.p j
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hS : s ≤ 2 * u := by
    have hle := Finset.single_le_sum (f := fun i => C.γ i * C.ρ i ^ 2)
      (fun i hi => mul_nonneg (C.γ_pos (Finset.mem_range.mp hi)).le (sq_nonneg _))
      (Finset.mem_range.mpr hj)
    exact hle.trans (by simpa only [mul_div_assoc] using C.sum_γ_mul_ρ_sq_le ha hs hsmall)
  have hp := C.abs_p_dotProduct_r_sub_le ha hs hsmall hj
  have hpair : |2 * C.γ j * (C.p j ⬝ᵥ C.r j - C.ρ j ^ 2)| ≤ 52 * j * z * s := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * C.γ j)]
    have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * C.γ j)
    dsimp only [z, s]
    nlinarith
  have hcurv := C.estimator_curvature ha hs hsmall hj
  have hgap : |2 * C.γ j * (C.p j ⬝ᵥ g)| ≤ 36 * j * z * u := by
    have hpg := EuclideanSpace.abs_dotProduct_le_norm (C.p j) g
    have hg := C.norm_sub_mulVec_x_sub_r_le_norm_b ha hs hsmall hj.le
    have hγp := C.γ_mul_norm_p_le ha hs hsmall hj
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hγp (by norm_num : (0 : ℝ) ≤ 2))
      hg (norm_nonneg _) (by positivity : 0 ≤ 2 * (3 / 2 * ‖WithLp.toLp 2 C.b‖ / a))
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * C.γ j)]
    have h1 := mul_le_mul_of_nonneg_left hpg (by positivity : 0 ≤ 2 * C.γ j)
    have heq : 2 * (3 / 2 * ‖WithLp.toLp 2 C.b‖ / a) *
        (12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖) = 36 * j * z * u := by
      dsimp only [z, u]; ring
    nlinarith
  have hAe : C.A *ᵥ (xs - C.x j) = C.r j + g := by
    dsimp only [g]
    rw [Matrix.mulVec_sub, hx]
    abel
  have hQ : quadForm C.A w = quadForm C.A (xs - C.x j) -
      2 * C.γ j * (C.p j ⬝ᵥ C.r j) - 2 * C.γ j * (C.p j ⬝ᵥ g) +
      C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) := by
    dsimp only [w]
    rw [C.quadForm_sub_eq, hAe, dotProduct_add]
    simp only [quadForm_def, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  have hround := C.estimator_rounding ha hs hsmall hx hj
  have hp' := abs_le.mp hpair
  have hc' := abs_le.mp hcurv
  have hg' := abs_le.mp hgap
  have hr' := abs_le.mp hround
  have hweight := mul_le_mul_of_nonneg_left hS
    (show 0 ≤ (52 * (j : ℝ) + 7) * z by positivity)
  have hbudget : (52 * (j : ℝ) + 7) * z * (2 * u) +
      (36 * j + 32) * z * u ≤ 150 * (j + 1) * z * u := by
    nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) by positivity) (mul_nonneg hz hu)]
  apply abs_le.mpr
  constructor <;> dsimp only [w, z, s, u, g] at * <;>
    nlinarith only [hQ, hp'.1, hp'.2, hc'.1, hc'.2, hg'.1, hg'.2,
      hr'.1, hr'.2, hweight, hbudget]

/-- **Delayed physical energy reliability.** For a successful $k$-step real CG run with
spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, let
$E_i=\|\mathbf{x}_\star-\mathbf{x}_i\|_{\mathbf{A}}^2$ for a solution
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$. For $j+d\le k$, the exactly evaluated
computed decrement sum satisfies, with <!-- value cgEnergyEstimatorFactor j d -->
$R_{j,d}=150d(j+d)\varepsilon\kappa\|\mathbf{b}\|^2/a$,
$$\Bigl\lvert E_j-E_{j+d}-\sum_{i=j}^{j+d-1}\gamma_i\|\mathbf{r}_i\|^2\Bigr\rvert
\le R_{j,d} .$$
[StrakosTichy2002, Theorem 10.1 and (10.6)-(10.9)]; adapted to this arithmetic model and
proved input-only window. All quadratic errors are bounded explicitly, and no near-monotonicity
hypothesis is used. Zero delay and zero precision have zero remainder.
Result: cg-delayed-physical-energy-reliability -/
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j d : ℕ} (hjd : j + d ≤ k) :
    |(quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d))) -
      ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2| ≤
      cgEnergyEstimatorFactor j d * C.ε * (a' / a) *
        (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  obtain ⟨hκ, -, -⟩ := C.estimator_facts ha hs hsmall
  have hε0 := C.ε_nonneg
  have hz : 0 ≤ C.ε * (a' / a) := by positivity
  have hu : 0 ≤ ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by positivity
  induction d with
  | zero =>
    rw [Nat.add_zero, Finset.Ico_self, Finset.sum_empty, sub_self, sub_zero, abs_zero,
      cgEnergyEstimatorFactor_def]
    simp only [Nat.cast_zero, mul_zero, zero_mul, le_refl]
  | succ d ih =>
    have hd : j + d < k := by omega
    have hprev := ih hd.le
    have hstep := C.estimator_step ha hs hsmall hx hd
    rw [Nat.add_succ, Finset.sum_Ico_succ_top (by omega : j ≤ j + d)]
    have heq : (quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d + 1))) -
        ((∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2) + C.γ (j + d) * C.ρ (j + d) ^ 2) =
        ((quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d))) -
          ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2) +
        ((quadForm C.A (xs - C.x (j + d)) - quadForm C.A (xs - C.x (j + d + 1))) -
          C.γ (j + d) * C.ρ (j + d) ^ 2) := by ring
    rw [heq]
    refine (abs_add_le _ _).trans ((add_le_add hprev hstep).trans ?_)
    rw [cgEnergyEstimatorFactor_def, cgEnergyEstimatorFactor_def]
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by positivity) (mul_nonneg hz hu)]

/-- For a successful $k$-step CG run with spectrum in $[a,a']$, $a>0$ and
$k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$, a solution
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ and $j+d\le k$ satisfy the certified lower
estimate $\sum_{i=j}^{j+d-1}\gamma_i\|\mathbf{r}_i\|^2-R_{j,d}\le
\|\mathbf{x}_\star-\mathbf{x}_j\|_{\mathbf{A}}^2$, with remainder
specified by <!-- value cgEnergyEstimatorFactor j d -->
$R_{j,d}=150d(j+d)\varepsilon(a'/a)\|\mathbf{b}\|^2/a$.
The terminal energy is nonnegative; it need not vanish. -/
theorem sum_sub_le_quadForm_sub_x {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j d : ℕ} (hjd : j + d ≤ k) :
    (∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2) -
      cgEnergyEstimatorFactor j d * C.ε * (a' / a) *
        (‖WithLp.toLp 2 C.b‖ ^ 2 / a) ≤ quadForm C.A (xs - C.x j) := by
  have h := C.abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le ha hs hsmall hx hjd
  have hE := C.mul_norm_sq_le_quadForm hs (xs - C.x (j + d))
  have hE0 : 0 ≤ quadForm C.A (xs - C.x (j + d)) := le_trans (by positivity) hE
  linarith [(abs_le.mp h).1]

/-- For a successful $k$-step CG run with spectrum in $[a,a']$, $a>0$ and
$k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$, a solution
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ and $j+d\le k$ have absolute estimator error
at most the terminal energy plus the rounding allowance, given by
remainder <!-- value cgEnergyEstimatorFactor j d -->
$R_{j,d}=150d(j+d)\varepsilon(a'/a)\|\mathbf{b}\|^2/a$.
This exposes the accuracy needed of a delayed terminal-tail certificate. -/
theorem abs_quadForm_sub_x_sub_sum_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j d : ℕ} (hjd : j + d ≤ k) :
    |quadForm C.A (xs - C.x j) -
      ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2| ≤
      quadForm C.A (xs - C.x (j + d)) +
      cgEnergyEstimatorFactor j d * C.ε * (a' / a) *
        (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have h := C.abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le ha hs hsmall hx hjd
  have hE := C.mul_norm_sq_le_quadForm hs (xs - C.x (j + d))
  have hE0 : 0 ≤ quadForm C.A (xs - C.x (j + d)) := le_trans (by positivity) hE
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- **Certified delayed-energy stopping.** For a successful $k$-step CG run with spectrum
in $[a,a']$, $a>0$, $k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$, solution
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ and $j+d\le k$, suppose the terminal energy
is at most $T$. If the delayed decrement sum plus $T$ and the input-only rounding allowance
of <!-- value cgEnergyEstimatorFactor j d -->
$150d(j+d)\varepsilon(a'/a)\|\mathbf{b}\|^2/a$
is at most the requested tolerance, the physical energy at $j$ is at most that tolerance.
A small delayed sum alone is insufficient when the terminal tail or rounding allowance is large.
No printed source.
Result: cg-delayed-energy-stopping -/
theorem quadForm_sub_x_le_of_sum_add_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j d : ℕ} (hjd : j + d ≤ k)
    {tail tolerance : ℝ} (hterminal : quadForm C.A (xs - C.x (j + d)) ≤ tail)
    (hstop : (∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2) +
      cgEnergyEstimatorFactor j d * C.ε * (a' / a) *
        (‖WithLp.toLp 2 C.b‖ ^ 2 / a) + tail ≤ tolerance) :
    quadForm C.A (xs - C.x j) ≤ tolerance := by
  have h := C.abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le ha hs hsmall hx hjd
  linarith [(abs_le.mp h).2]

/-- The physical and full-horizon model energies differ in absolute value by the initial
model perturbation and the accumulated physical rounding error. For a successful real CG run,
spectrum in $[a,a']$, $a>0$, $k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$, physical and
model solutions and $j\le k$, the errors use <!-- value cgBackwardFactor k -->
$c=6000k^2\sqrt{k}\varepsilon(a'/a)a'$ and <!-- value cgEnergyEstimatorFactor 0 j -->
$R_{0,j}=150j(0+j)\varepsilon(a'/a)\|\mathbf{b}\|^2/a$.
No closeness of the computed and exact-model iterates is assumed. -/
theorem abs_quadForm_sub_x_sub_quadForm_backwardH_sub_cgIterate_le {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b)
    {ys : Fin n × Fin (k + 1) → ℝ} (hy : C.backwardH *ᵥ ys = C.dilatedRhs)
    {j : ℕ} (hj : j ≤ k) :
    |quadForm C.A (xs - C.x j) -
      quadForm C.backwardH (ys - cgIterate C.backwardH C.dilatedRhs 0 j)| ≤
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 +
      cgEnergyEstimatorFactor 0 j * C.ε * (a' / a) *
        (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hp := C.abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le ha hs hsmall hx
    (j := 0) (d := j) (by omega)
  rw [C.x_zero, sub_zero, zero_add, ← Finset.range_eq_Ico] at hp
  have hm := C.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate
    ha hs hsmall hy (j := 0) (d := j) (by omega)
  rw [cgIterate_zero, sub_zero, zero_add, ← Finset.range_eq_Ico] at hm
  have hi := C.abs_quadForm_backwardH_sub_quadForm_le ha hs hsmall hy hx
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hp).1, (abs_le.mp hp).2,
    (abs_le.mp hi).1, (abs_le.mp hi).2]

end CGRun

end NLAlib
