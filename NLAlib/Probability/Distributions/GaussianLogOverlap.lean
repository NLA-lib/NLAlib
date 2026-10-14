/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake
public import NLAlib.Probability.Distributions.Gaussian

/-!
# The logarithmic overlap of a Gaussian vector with a fixed direction

For a standard Gaussian vector `X` in `ℝⁿ` (`N = card n`) and a fixed unit vector `u`, the
squared overlap `(u ⬝ᵥ X)² / ‖X‖²` is the squared cosine between a random start and a fixed
direction, the quantity a random-start analysis of the power method or the Lanczos method has to
control [KuczynskiWozniakowski1992]. Its inverse `‖X‖² / (u ⬝ᵥ X)²` has infinite
mean, but its logarithm has an exponential tail beyond `log (2N)`:
`P(t ≤ log (‖X‖² / (u ⬝ᵥ X)²)) ≤ √(2N) e^{-t/2}` for every real `t`, and so finite first and
second moments, `E log (‖X‖² / (u ⬝ᵥ X)²) ≤ log (2N) + 2` and
`E log (‖X‖² / (u ⬝ᵥ X)²)² ≤ log (2N)² + 4 log (2N) + 8`.

The quantity is written out, with no definition. On the null event `u ⬝ᵥ X = 0` the quotient is
`0` (Lean's division) and its logarithm is `0`; the statements hold with this convention. The
coordinate case is `u = Pi.single i 1`, where `u ⬝ᵥ X = X i`.

The proof rotates `u` to a coordinate vector, splits that coordinate `g` from the others, whose
squared norm `R` is independent of it, and uses the small-ball bound `P(|g| ≤ a) ≤ a` (the
standard Gaussian density is at most `1/2`): `P(v ≤ R / g²) ≤ E √(R / v) ≤ √((N - 1) / v)`.

## Main results

* `NLAlib.measureReal_log_norm_sq_div_sq_ge_le_of_hasLaw_gaussianVector`: the tail.
* `NLAlib.integrable_log_norm_sq_div_sq_of_hasLaw_gaussianVector`,
  `NLAlib.integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector`: the mean.
* `NLAlib.integrable_log_norm_sq_div_sq_sq_of_hasLaw_gaussianVector`,
  `NLAlib.integral_log_norm_sq_div_sq_sq_le_of_hasLaw_gaussianVector`: the second moment.

## References

* [J. Kuczyński, H. Woźniakowski, *Estimating the largest eigenvalue by the power and Lanczos
  algorithms with a random start*][KuczynskiWozniakowski1992].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ} {u : n → ℝ}

/-! ### One coordinate against the others -/

private theorem gaussianPDFReal_le_half (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 / 2 := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hden : (2 : ℝ) ≤ √(2 * Real.pi) := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
    have hn := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.two_le_pi]
  have hinv : (√(2 * Real.pi))⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
  exact (mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
    (by simpa only [mul_one] using hinv)

/-- The small ball `P(|g| ≤ a) ≤ a` of a standard Gaussian. -/
private theorem gaussianReal_abs_le_le (a : ℝ) :
    gaussianReal 0 1 {x : ℝ | |x| ≤ a} ≤ ENNReal.ofReal a := by
  have hSet : {x : ℝ | |x| ≤ a} = Icc (-a) a := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, abs_le]
  rw [hSet, gaussianReal_apply 0 (by norm_num : (1 : NNReal) ≠ 0)]
  calc (∫⁻ x in Icc (-a) a, gaussianPDF 0 1 x)
      ≤ ∫⁻ _ in Icc (-a) a, ENNReal.ofReal (1 / 2 : ℝ) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_half x)
    _ = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 * a) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      congr 2
      ring
    _ = ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      ring

/-- `P(v ≤ s / g²) ≤ √(s / v)` for a standard Gaussian `g`. -/
private theorem gaussianReal_le_div_sq_le {s v : ℝ} (hv : 0 < v) :
    gaussianReal 0 1 {x : ℝ | v ≤ s / x ^ 2} ≤ ENNReal.ofReal √(s / v) := by
  refine (measure_mono fun x (hx : v ≤ s / x ^ 2) => ?_).trans (gaussianReal_abs_le_le _)
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at hx
    linarith
  refine Real.abs_le_sqrt ?_
  rw [le_div_iff₀ hv]
  rw [le_div_iff₀ (by positivity)] at hx
  linarith

/-- `E √R ≤ √(card m)` for the squared norm `R` of a standard Gaussian vector, in the form
`E √(R / v) ≤ √(card m / v)`. -/
private theorem lintegral_sqrt_norm_sq_div_le {m : Type*} [Fintype m] {v : ℝ}
    (hv : 0 < v) :
    ∫⁻ r, ENNReal.ofReal √(‖WithLp.toLp 2 r‖ ^ 2 / v) ∂(gaussianVector m) ≤
      ENNReal.ofReal √(Fintype.card m / v) := by
  classical
  set c : ℝ := (Fintype.card m : ℝ)
  rcases (Nat.cast_nonneg (Fintype.card m) : (0 : ℝ) ≤ c).eq_or_lt with hc | hc
  · have : IsEmpty m := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hc.symm)
    simp only [Subsingleton.elim _ (0 : EuclideanSpace ℝ m), norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Real.sqrt_zero,
      ENNReal.ofReal_zero, lintegral_const, zero_mul, zero_le]
  have hiso := isIsotropic_of_hasLaw_gaussianVector (HasLaw.id (μ := gaussianVector m))
  have hint : Integrable (fun r : m → ℝ => ‖WithLp.toLp 2 r‖ ^ 2) (gaussianVector m) := by
    have h := hiso.integrable_norm_mulVec_sq (1 : Matrix m m ℝ)
    simp only [Matrix.one_mulVec, id_eq] at h
    exact h
  have hmean : ∫ r, ‖WithLp.toLp 2 r‖ ^ 2 ∂(gaussianVector m) = c := hiso.integral_norm_sq
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  have h1 : √c * √c = c := Real.mul_self_sqrt hc.le
  set K : ℝ := 2 * √c * √v with hK_def
  have hK : 0 < K := by positivity
  have hpt (r : m → ℝ) : √(‖WithLp.toLp 2 r‖ ^ 2 / v) ≤ (‖WithLp.toLp 2 r‖ ^ 2 + c) / K := by
    rw [Real.sqrt_div' _ hv.le, Real.sqrt_sq (norm_nonneg _), div_le_div_iff₀ hsv hK, hK_def]
    have h2 : 0 ≤ (‖WithLp.toLp 2 r‖ - √c) ^ 2 * √v := mul_nonneg (sq_nonneg _) hsv.le
    linear_combination h2 + √v * h1
  have hint' : Integrable (fun r : m → ℝ => (‖WithLp.toLp 2 r‖ ^ 2 + c) / K)
      (gaussianVector m) := (hint.add (integrable_const c)).div_const K
  calc ∫⁻ r, ENNReal.ofReal √(‖WithLp.toLp 2 r‖ ^ 2 / v) ∂(gaussianVector m)
      ≤ ∫⁻ r, ENNReal.ofReal ((‖WithLp.toLp 2 r‖ ^ 2 + c) / K) ∂(gaussianVector m) :=
        lintegral_mono fun r => ENNReal.ofReal_le_ofReal (hpt r)
    _ = ENNReal.ofReal (∫ r, (‖WithLp.toLp 2 r‖ ^ 2 + c) / K ∂(gaussianVector m)) :=
        (ofReal_integral_eq_lintegral_ofReal hint' (ae_of_all _ fun r => by positivity)).symm
    _ = ENNReal.ofReal √(c / v) := by
      rw [integral_div, integral_add hint (integrable_const c), hmean, integral_const,
        probReal_univ, one_smul, Real.sqrt_div' _ hv.le]
      congr 1
      rw [div_eq_div_iff hK.ne' hsv.ne', hK_def]
      linear_combination (-2 * √v) * h1

/-- With `R` the squared norm of the coordinates other than `i`, `P(v ≤ R / g_i²) ≤ √((N-1)/v)`:
`g_i` is independent of `R`, so the small ball of `g_i` is integrated against the law of `R`. -/
private theorem gaussianVector_le_div_sq_le [DecidableEq n] (i : n) {v : ℝ} (hv : 0 < v) :
    gaussianVector n {x | v ≤ ‖WithLp.toLp 2 (fun j : {j // ¬j = i} => x j)‖ ^ 2 / x i ^ 2} ≤
      ENNReal.ofReal √(Fintype.card {j // ¬j = i} / v) := by
  let p : n → Prop := fun j => j = i
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : n => gaussianReal 0 1) p
  let T : Set (({j // p j} → ℝ) × ({j // ¬p j} → ℝ)) :=
    {q | v ≤ ‖WithLp.toLp 2 q.2‖ ^ 2 / q.1 ⟨i, rfl⟩ ^ 2}
  have hT : MeasurableSet T := measurableSet_le measurable_const (by fun_prop)
  have hpre : {x : n → ℝ | v ≤ ‖WithLp.toLp 2 (fun j : {j // ¬j = i} => x j)‖ ^ 2 / x i ^ 2} =
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : n => ℝ) p ⁻¹' T := rfl
  rw [hpre, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
  refine (lintegral_mono fun r => ?_).trans (lintegral_sqrt_norm_sq_div_le hv)
  have hslice : (fun h => (h, r)) ⁻¹' T =
      Function.eval ⟨i, rfl⟩ ⁻¹' {x : ℝ | v ≤ ‖WithLp.toLp 2 r‖ ^ 2 / x ^ 2} :=
    rfl
  have hS : MeasurableSet {x : ℝ | v ≤ ‖WithLp.toLp 2 r‖ ^ 2 / x ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [hslice]
  have key := ((measurePreserving_eval (fun _ : {j // p j} => gaussianReal 0 1) ⟨i, rfl⟩)
    |>.measure_preimage hS.nullMeasurableSet).trans_le (gaussianReal_le_div_sq_le hv)
  convert key

private theorem measurable_log_norm_sq_div_sq (i : n) :
    Measurable fun x : n → ℝ => Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2) :=
  Real.measurable_log.comp (by fun_prop)

/-- The squared norm splits off the coordinate `i`. -/
private theorem norm_sq_eq_sq_add [DecidableEq n] (i : n) (x : n → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = x i ^ 2 + ‖WithLp.toLp 2 (fun j : {j // ¬j = i} => x j)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  exact Fintype.sum_eq_add_sum_subtype_ne _ i

private theorem log_norm_sq_div_sq_nonneg (i : n) (x : n → ℝ) :
    0 ≤ Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2) := by
  classical
  by_cases hxi : x i = 0
  · simp only [hxi, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      Real.log_zero, le_refl]
  apply Real.log_nonneg
  rw [norm_sq_eq_sq_add i, add_div, div_self (pow_ne_zero 2 hxi)]
  have : 0 ≤ ‖WithLp.toLp 2 (fun j : {j // ¬j = i} => x j)‖ ^ 2 / x i ^ 2 := by positivity
  linarith

/-- The tail on the canonical space, for one coordinate. -/
private theorem gaussianVector_le_log_le (i : n) (t : ℝ) :
    (gaussianVector n).real {x | t ≤ Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2)} ≤
      √(2 * Fintype.card n) * Real.exp (-t / 2) := by
  classical
  set N : ℝ := (Fintype.card n : ℝ)
  set m : ℝ := (Fintype.card {j // ¬j = i} : ℝ)
  have hNm : N = 1 + m := by
    have h := Fintype.sum_eq_add_sum_subtype_ne (fun _ : n => (1 : ℝ)) i
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h
  have hm : 0 ≤ m := Nat.cast_nonneg _
  by_cases hC : 1 ≤ √(2 * N) * Real.exp (-t / 2)
  · exact measureReal_le_one.trans hC
  push Not at hC
  have hexp : 2 * N < Real.exp t := by
    have h1 : √(2 * N) < Real.exp (t / 2) := by
      have h := mul_lt_mul_of_pos_right hC (Real.exp_pos (t / 2))
      rwa [mul_assoc, ← Real.exp_add, show -t / 2 + t / 2 = 0 by ring, Real.exp_zero, mul_one,
        one_mul] at h
    have h2 := (Real.sqrt_lt' (Real.exp_pos _)).mp h1
    rwa [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (t / 2) = t by push_cast; ring] at h2
  have ht : 0 < t := by
    by_contra h
    have : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr (not_lt.mp h)
    linarith
  set v := Real.exp t - 1
  have hv : 0 < v := by simp only [v]; linarith
  have hsub : {x : n → ℝ | t ≤ Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2)} ⊆
      {x | v ≤ ‖WithLp.toLp 2 (fun j : {j // ¬j = i} => x j)‖ ^ 2 / x i ^ 2} := by
    intro x (hx : t ≤ Real.log _)
    have hxi : x i ≠ 0 := by
      intro h0
      simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
        Real.log_zero] at hx
      linarith
    have hpos : 0 < ‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2 := by
      rw [norm_sq_eq_sq_add i]
      positivity
    rw [Real.le_log_iff_exp_le hpos, norm_sq_eq_sq_add i, add_div,
      div_self (pow_ne_zero 2 hxi)] at hx
    change v ≤ _
    simp only [v]
    linarith
  calc (gaussianVector n).real {x | t ≤ Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2)}
      ≤ (gaussianVector n).real
          {x | v ≤ ‖WithLp.toLp 2 (fun j : {j // ¬j = i} => x j)‖ ^ 2 / x i ^ 2} :=
        measureReal_mono hsub
    _ ≤ √(m / v) :=
        ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (gaussianVector_le_div_sq_le i hv)
    _ ≤ √(2 * N) * Real.exp (-t / 2) := by
      rw [Real.exp_half, ← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ hv]
      have hw : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add, neg_add_cancel,
        Real.exp_zero]
      have hw0 := Real.exp_pos (-t)
      have h2N : 2 * N * Real.exp (-t) < 1 := by nlinarith
      simp only [v]
      nlinarith

/-! ### Moments from a half-rate exponential tail -/

private theorem lintegral_ofReal_exp_neg_half_Ioi :
    ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t / 2)) = ENNReal.ofReal 2 := by
  have he : (fun t : ℝ => Real.exp (-t / 2)) = fun t => Real.exp ((-1 / 2 : ℝ) * t) := by
    funext t
    congr 1
    ring
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-t / 2)) (Ioi 0) := by
    rw [he]
    exact integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le),
    he, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0]
  norm_num

private theorem lintegral_ofReal_two_mul_mul_exp_neg_half_Ioi :
    ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (2 * t * Real.exp (-t / 2)) = ENNReal.ofReal 8 := by
  have hG := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 / 2) (by norm_num)
    (by norm_num)
  have hgamma : Real.Gamma 2 = 1 := by norm_num
  have he : (fun t : ℝ => t ^ ((2 : ℝ) - 1) * Real.exp (-((1 / 2) * t))) =
      fun t => t * Real.exp (-t / 2) := by
    funext t
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    congr 2
    ring
  rw [he, hgamma] at hG
  norm_num at hG
  have hi : IntegrableOn (fun t : ℝ => t * Real.exp (-t / 2)) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hG]; norm_num)
  have he2 : (fun t : ℝ => 2 * t * Real.exp (-t / 2)) =
      fun t => 2 * (t * Real.exp (-t / 2)) := by funext t; ring
  rw [← ofReal_integral_eq_lintegral_ofReal (by rw [he2]; exact hi.const_mul 2)]
  · rw [he2, integral_const_mul, hG]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt ht)) (Real.exp_pos _).le

/-- A nonnegative measurable `f` with `P(t < f) ≤ e^{-t/2}` for `t > 0` has `E f ≤ 2` and
`E f² ≤ 8`. -/
private theorem moments_of_exp_neg_half_tail {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (htail : ∀ t : ℝ, 0 < t → ν {x | t < f x} ≤ ENNReal.ofReal (Real.exp (-t / 2))) :
    Integrable f ν ∧ ∫ x, f x ∂ν ≤ 2 ∧ Integrable (fun x => f x ^ 2) ν ∧
      ∫ x, f x ^ 2 ∂ν ≤ 8 := by
  have hL : ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal 2 := by
    rw [lintegral_eq_lintegral_meas_lt ν (ae_of_all _ hf0) hf.aemeasurable,
      ← lintegral_ofReal_exp_neg_half_Ioi]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact htail t ht
  have hInt (z : ℝ) : ∫ t in (0 : ℝ)..z, 2 * t = z ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hLC := lintegral_comp_eq_lintegral_meas_lt_mul ν (ae_of_all _ hf0) hf.aemeasurable
    (g := fun t : ℝ => 2 * t)
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (by norm_num) (le_of_lt ht))
  simp only [hInt] at hLC
  have hL2 : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν ≤ ENNReal.ofReal 8 := by
    rw [hLC, ← lintegral_ofReal_two_mul_mul_exp_neg_half_Ioi]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc ν {x | t < f x} * ENNReal.ofReal (2 * t)
        ≤ ENNReal.ofReal (Real.exp (-t / 2)) * ENNReal.ofReal (2 * t) := by
          gcongr
          exact htail t ht
      _ = ENNReal.ofReal (2 * t * Real.exp (-t / 2)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  have hi : Integrable f ν :=
    ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)).mpr
      (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  have hi2 : Integrable (fun x => f x ^ 2) ν :=
    ⟨(hf.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg (f x))).mpr
        (hL2.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_, hi2, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (f x))
      (hf.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL2

/-- The moments on the canonical space, for one coordinate: the excess
`Z = max (L - log (2N)) 0` has tail `e^{-t/2}`, and `L ≤ log (2N) + Z`. -/
private theorem gaussianVector_moments (i : n) :
    Integrable (fun x => Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2)) (gaussianVector n) ∧
      ∫ x, Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2) ∂(gaussianVector n) ≤
        Real.log (2 * Fintype.card n) + 2 ∧
      Integrable (fun x => Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2) ^ 2) (gaussianVector n) ∧
      ∫ x, Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2) ^ 2 ∂(gaussianVector n) ≤
        Real.log (2 * Fintype.card n) ^ 2 + 4 * Real.log (2 * Fintype.card n) + 8 := by
  set ν := gaussianVector n
  set L : (n → ℝ) → ℝ := fun x => Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2)
  set N : ℝ := (Fintype.card n : ℝ)
  set T := Real.log (2 * N)
  have hN : 1 ≤ N := by
    simp only [N]
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hT : 0 ≤ T := Real.log_nonneg (by linarith)
  have hLm : Measurable L := measurable_log_norm_sq_div_sq i
  have hL0 (x : n → ℝ) : 0 ≤ L x := log_norm_sq_div_sq_nonneg i x
  set Z : (n → ℝ) → ℝ := fun x => max (L x - T) 0
  have hZm : Measurable Z := (hLm.sub measurable_const).max measurable_const
  have hZtail (t : ℝ) (ht : 0 < t) : ν {x | t < Z x} ≤ ENNReal.ofReal (Real.exp (-t / 2)) := by
    have hsub : {x | t < Z x} ⊆ {x | T + t ≤ L x} := by
      intro x (hx : t < max (L x - T) 0)
      rw [lt_max_iff] at hx
      change T + t ≤ L x
      rcases hx with h | h <;> linarith
    have hC : √(2 * N) * Real.exp (-(T + t) / 2) = Real.exp (-t / 2) := by
      rw [show √(2 * N) = Real.exp (T / 2) by
        rw [Real.exp_half, Real.exp_log (by positivity)], ← Real.exp_add]
      congr 1
      ring
    calc ν {x | t < Z x} ≤ ν {x | T + t ≤ L x} := measure_mono hsub
      _ = ENNReal.ofReal (ν.real {x | T + t ≤ L x}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (Real.exp (-t / 2)) :=
          ENNReal.ofReal_le_ofReal (hC ▸ gaussianVector_le_log_le i (T + t))
  obtain ⟨hZI, hZv, hZI2, hZv2⟩ :=
    moments_of_exp_neg_half_tail hZm (fun _ => le_max_right _ _) hZtail
  have hLb (x : n → ℝ) : L x ≤ T + Z x := by
    have h := le_max_left (L x - T) 0
    change L x ≤ T + max (L x - T) 0
    linarith
  have hLI : Integrable L ν :=
    ((integrable_const T).add hZI).mono' hLm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hL0 x)]; exact hLb x)
  have hLsq (x : n → ℝ) : L x ^ 2 ≤ T ^ 2 + 2 * T * Z x + Z x ^ 2 := by
    have h := pow_le_pow_left₀ (hL0 x) (hLb x) 2
    nlinarith
  have hRI : Integrable (fun x => T ^ 2 + 2 * T * Z x + Z x ^ 2) ν :=
    ((integrable_const (T ^ 2)).add (hZI.const_mul (2 * T))).add hZI2
  have hLI2 : Integrable (fun x => L x ^ 2) ν :=
    hRI.mono' (hLm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hLsq x)
  refine ⟨hLI, ?_, hLI2, ?_⟩
  · have hI : Integrable (fun x => T + Z x) ν := (integrable_const T).add hZI
    have h := integral_mono hLI hI hLb
    have he : ∫ x, (T + Z x) ∂ν = T + ∫ x, Z x ∂ν := by
      rw [integral_add (integrable_const T) hZI, integral_const, probReal_univ, one_smul]
    change ∫ x, L x ∂ν ≤ T + 2
    linarith
  · have h := integral_mono hLI2 hRI hLsq
    have he : ∫ x, (T ^ 2 + 2 * T * Z x + Z x ^ 2) ∂ν =
        T ^ 2 + 2 * T * ∫ x, Z x ∂ν + ∫ x, Z x ^ 2 ∂ν := by
      rw [integral_add (f := fun x => T ^ 2 + 2 * T * Z x) (g := fun x => Z x ^ 2)
          ((integrable_const (T ^ 2)).add (hZI.const_mul (2 * T))) hZI2,
        integral_add (f := fun _ => T ^ 2) (g := fun x => 2 * T * Z x) (integrable_const (T ^ 2))
          (hZI.const_mul (2 * T)), integral_const,
        probReal_univ, one_smul, integral_const_mul]
    change ∫ x, L x ^ 2 ∂ν ≤ T ^ 2 + 4 * T + 8
    nlinarith

/-! ### Rotating a unit vector to a coordinate -/

/-- A unit vector `u` is a coordinate of a rotated copy `Y` of `X`: `Y` is again standard
Gaussian, `‖Y‖ = ‖X‖` and `Y i = u ⬝ᵥ X`. -/
private theorem exists_hasLaw_gaussianVector_eq (hX : HasLaw X (gaussianVector n) μ)
    (hu : ‖WithLp.toLp 2 u‖ = 1) :
    ∃ i : n, ∃ Y : Ω → n → ℝ, HasLaw Y (gaussianVector n) μ ∧
      ∀ ω, ‖WithLp.toLp 2 (X ω)‖ ^ 2 / (u ⬝ᵥ X ω) ^ 2 =
        ‖WithLp.toLp 2 (Y ω)‖ ^ 2 / Y ω i ^ 2 := by
  have hne : Nonempty n := by
    by_contra h
    have : IsEmpty n := not_nonempty_iff.mp h
    rw [Subsingleton.elim (WithLp.toLp 2 u) 0, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨i⟩ := hne
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := EuclideanSpace ℝ n) (ι := n) (by simp) (v := fun _ => WithLp.toLp 2 u) (s := {i})
    (by
      rw [orthonormal_iff_ite]
      intro a c
      rw [Subsingleton.elim a c, if_pos rfl]
      simp only [Set.domRestrict_apply, real_inner_self_eq_norm_sq, hu, one_pow])
  let f : (n → ℝ) → n → ℝ := fun x => (b.repr (WithLp.toLp 2 x)).ofLp
  have hf : Measurable f := by fun_prop
  have hmap : (gaussianVector n).map f = gaussianVector n := by
    have h1 : f = WithLp.ofLp ∘ b.repr ∘ WithLp.toLp 2 := rfl
    have h2 : (gaussianVector n).map (WithLp.ofLp ∘ WithLp.toLp 2) = gaussianVector n := by
      simp only [Function.comp_def, Measure.map_id']
    rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian, stdGaussian_map,
      ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop), h2]
  refine ⟨i, fun ω => f (X ω), HasLaw.fun_comp (Y := f) ⟨hf.aemeasurable, hmap⟩ hX,
    fun ω => ?_⟩
  have hnorm : ‖WithLp.toLp 2 (f (X ω))‖ = ‖WithLp.toLp 2 (X ω)‖ := by
    simp only [f, WithLp.toLp_ofLp, LinearIsometryEquiv.norm_map]
  have hi : f (X ω) i = u ⬝ᵥ X ω := by
    simp only [f, OrthonormalBasis.repr_apply_apply, hb i (mem_singleton i),
      EuclideanSpace.inner_toLp_toLp, star_trivial]
    exact dotProduct_comm _ _
  change _ = ‖WithLp.toLp 2 (f (X ω))‖ ^ 2 / f (X ω) i ^ 2
  rw [hnorm, hi]

/-! ### Main results -/

/-- **The tail of the logarithmic overlap.** For a standard Gaussian vector `X` in `ℝⁿ` and a
unit vector `u`, `P(t ≤ log (‖X‖² / (u ⬝ᵥ X)²)) ≤ √(2N) e^{-t/2}` for every real `t`, with
`N = card n`; the bound is below `1` exactly when `t > log (2N)`. The logarithm is `0` on the null
event `u ⬝ᵥ X = 0`. The random-start step of the power and Lanczos methods
[KuczynskiWozniakowski1992], in logarithmic form.
Port of `NLAlib.pi_gaussianReal_logOverlap_gt_le`, there for a coordinate of `Fin (n + 1)`, a
strict event and `t ≥ log (2N)`.
Result: random-start-log-overlap -/
theorem measureReal_log_norm_sq_div_sq_ge_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hu : ‖WithLp.toLp 2 u‖ = 1) (t : ℝ) :
    μ.real {ω | t ≤ Real.log (‖WithLp.toLp 2 (X ω)‖ ^ 2 / (u ⬝ᵥ X ω) ^ 2)} ≤
      √(2 * Fintype.card n) * Real.exp (-t / 2) := by
  classical
  obtain ⟨i, Y, hY, hXY⟩ := exists_hasLaw_gaussianVector_eq hX hu
  simp only [hXY]
  rw [hY.measureReal_eq (p := fun x => t ≤ Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2))
    (measurableSet_le measurable_const (measurable_log_norm_sq_div_sq i))]
  exact gaussianVector_le_log_le i t

/-- The logarithmic overlap `log (‖X‖² / (u ⬝ᵥ X)²)` of a standard Gaussian vector with a unit
vector is integrable (`NLAlib.integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector`). -/
theorem integrable_log_norm_sq_div_sq_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
    Integrable (fun ω => Real.log (‖WithLp.toLp 2 (X ω)‖ ^ 2 / (u ⬝ᵥ X ω) ^ 2)) μ := by
  classical
  obtain ⟨i, Y, hY, hXY⟩ := exists_hasLaw_gaussianVector_eq hX hu
  simp only [hXY]
  exact (hY.integrable_comp_iff (f := fun x => Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2))
    (measurable_log_norm_sq_div_sq i).aestronglyMeasurable).2 (gaussianVector_moments i).1

/-- **The mean logarithmic overlap.** For a standard Gaussian vector `X` in `ℝⁿ` and a unit
vector `u`, `E log (‖X‖² / (u ⬝ᵥ X)²) ≤ log (2N) + 2` with `N = card n`, although
`E ‖X‖² / (u ⬝ᵥ X)² = ∞`. Integrating the tail
`NLAlib.measureReal_log_norm_sq_div_sq_ge_le_of_hasLaw_gaussianVector`; the random-start step of
the power and Lanczos methods [KuczynskiWozniakowski1992]. The exact mean is
`ψ(N/2) - ψ(1/2) ~ log (2N) + γ`, so the additive constant is not tight.
Port of `NLAlib.integrable_and_integral_gaussianLogOverlap_le` and
`NLAlib.integrable_and_integral_log_sum_div_sq_pi_gaussianReal_le`, there for a coordinate.
Result: random-start-log-overlap -/
theorem integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
    ∫ ω, Real.log (‖WithLp.toLp 2 (X ω)‖ ^ 2 / (u ⬝ᵥ X ω) ^ 2) ∂μ ≤
      Real.log (2 * Fintype.card n) + 2 := by
  classical
  obtain ⟨i, Y, hY, hXY⟩ := exists_hasLaw_gaussianVector_eq hX hu
  simp only [hXY]
  have h := hY.integral_comp (measurable_log_norm_sq_div_sq i).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  exact (gaussianVector_moments i).2.1

/-- The square of the logarithmic overlap `log (‖X‖² / (u ⬝ᵥ X)²)` of a standard Gaussian vector
with a unit vector is integrable
(`NLAlib.integral_log_norm_sq_div_sq_sq_le_of_hasLaw_gaussianVector`). -/
theorem integrable_log_norm_sq_div_sq_sq_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
    Integrable (fun ω => Real.log (‖WithLp.toLp 2 (X ω)‖ ^ 2 / (u ⬝ᵥ X ω) ^ 2) ^ 2) μ := by
  classical
  obtain ⟨i, Y, hY, hXY⟩ := exists_hasLaw_gaussianVector_eq hX hu
  simp only [hXY]
  exact (hY.integrable_comp_iff (f := fun x => Real.log (‖WithLp.toLp 2 x‖ ^ 2 / x i ^ 2) ^ 2)
    ((measurable_log_norm_sq_div_sq i).pow_const 2).aestronglyMeasurable).2
    (gaussianVector_moments i).2.2.1

/-- **The second moment of the logarithmic overlap.** For a standard Gaussian vector `X` in `ℝⁿ`
and a unit vector `u`, with `T = log (2N)` and `N = card n`,
`E log (‖X‖² / (u ⬝ᵥ X)²)² ≤ T² + 4T + 8`, so the logarithmic overlap has variance `O(1)` around
a mean of order `log N`. Integrating the tail
`NLAlib.measureReal_log_norm_sq_div_sq_ge_le_of_hasLaw_gaussianVector` beyond `T`.
Port of `NLAlib.integrable_and_integral_gaussianLogOverlap_le` and
`NLAlib.integrable_and_integral_log_sum_div_sq_pi_gaussianReal_le`, there for a coordinate.
Result: random-start-log-overlap -/
theorem integral_log_norm_sq_div_sq_sq_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
    ∫ ω, Real.log (‖WithLp.toLp 2 (X ω)‖ ^ 2 / (u ⬝ᵥ X ω) ^ 2) ^ 2 ∂μ ≤
      Real.log (2 * Fintype.card n) ^ 2 + 4 * Real.log (2 * Fintype.card n) + 8 := by
  classical
  obtain ⟨i, Y, hY, hXY⟩ := exists_hasLaw_gaussianVector_eq hX hu
  simp only [hXY]
  have h := hY.integral_comp ((measurable_log_norm_sq_div_sq i).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  exact (gaussianVector_moments i).2.2.2

end NLAlib
