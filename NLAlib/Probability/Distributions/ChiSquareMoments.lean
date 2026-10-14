/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Gamma
public import NLAlib.Probability.Distributions.Gaussian

/-!
# Real moments of the chi-square law

For a standard Gaussian vector `X` in `ℝⁿ` (`d = card n`), `‖X‖²` has the `χ²_d` law, and
`E (‖X‖²)^s = 2^s Γ(d/2 + s) / Γ(d/2)` for every real `s > -d/2`, the integrability threshold.
The negative moments are what the inverse moments of Gaussian matrices rest on; in particular
`E 1 / ‖X‖² = 1 / (d - 2)` for `d ≥ 3`. At `X = 0` (probability zero) `0 ^ s` is Lean's junk value
for `s < 0`; the integrals are unaffected. The case `s = 1/2` gives `E ‖X‖`, whose growth in the
dimension (`√m - √n ≤ E ‖g_m‖ - E ‖g_n‖`) is the step of Gordon's lower bound for the smallest
singular value of a Gaussian matrix.

## Main results

* `NLAlib.integral_norm_sq_rpow_of_hasLaw_gaussianVector`.
* `NLAlib.integral_norm_sq_inv_of_hasLaw_gaussianVector`.
* `NLAlib.le_integral_norm_sub_integral_norm_of_hasLaw_gaussianVector`:
  `√m - √n ≤ E ‖g_m‖ - E ‖g_n‖` for `1 ≤ n ≤ m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ}

/-- The standard Gaussian vector has the density `(2π)^{-n/2} exp (-‖x‖²/2)`. -/
private theorem gaussianVector_eq_withDensity :
    gaussianVector n = volume.withDensity fun x : n → ℝ =>
      ENNReal.ofReal ((√(2 * π))⁻¹ ^ Fintype.card n * rexp (-‖WithLp.toLp 2 x‖ ^ 2 / 2)) := by
  have hprod (x : n → ℝ) : ∏ i, gaussianPDFReal 0 1 (x i) =
      (√(2 * π))⁻¹ ^ Fintype.card n * rexp (-‖WithLp.toLp 2 x‖ ^ 2 / 2) := by
    simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← Real.exp_sum, EuclideanSpace.real_norm_sq_eq, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  simp only [← hprod]
  refine Measure.pi_eq fun s hs => ?_
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  have hind (x : n → ℝ) : (Set.univ.pi s).indicator
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) x =
        ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _),
        ENNReal.ofReal_zero]
  simp only [hind]
  have hint : Integrable (fun x : n → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i))
      volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1))
      (fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _),
    integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

/-- Polar coordinates for a radial function of a standard Gaussian vector. -/
private theorem integral_radial_gaussianVector [Nonempty n] (φ : ℝ → ℝ) :
    ∫ x, φ ‖WithLp.toLp 2 x‖ ∂(gaussianVector n) =
      Fintype.card n * (volume : Measure (EuclideanSpace ℝ n)).real (Metric.ball 0 1) *
        ((√(2 * π))⁻¹ ^ Fintype.card n *
          ∫ y in Ioi (0 : ℝ), y ^ (Fintype.card n - 1) * (rexp (-y ^ 2 / 2) * φ y)) := by
  rw [gaussianVector_eq_withDensity, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hpos (x : n → ℝ) :
      0 ≤ (√(2 * π))⁻¹ ^ Fintype.card n * rexp (-‖WithLp.toLp 2 x‖ ^ 2 / 2) := by positivity
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (n → ℝ) → EuclideanSpace ℝ n) :=
    (MeasurableEquiv.toLp 2 (n → ℝ)).measurableEmbedding
  rw [(PiLp.volume_preserving_toLp n).integral_comp hemb (fun y : EuclideanSpace ℝ n =>
      (√(2 * π))⁻¹ ^ Fintype.card n * rexp (-‖y‖ ^ 2 / 2) * φ ‖y‖),
    integral_fun_norm_addHaar volume (fun r =>
      (√(2 * π))⁻¹ ^ Fintype.card n * rexp (-r ^ 2 / 2) * φ r),
    finrank_euclideanSpace, nsmul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  have e (y : ℝ) : y ^ (Fintype.card n - 1) * ((√(2 * π))⁻¹ ^ Fintype.card n *
      rexp (-y ^ 2 / 2) * φ y) = (√(2 * π))⁻¹ ^ Fintype.card n *
        (y ^ (Fintype.card n - 1) * (rexp (-y ^ 2 / 2) * φ y)) := by ring
  simp only [e, integral_const_mul]
  ring

/-- `∫₀^∞ y^q e^{-y²/2} dy = 2^{(q+1)/2} Γ((q+1)/2) / 2` for `q > -1`. -/
private theorem integral_rpow_mul_exp_neg_sq_div_two {q : ℝ} (hq : -1 < q) :
    ∫ y in Ioi (0 : ℝ), y ^ q * rexp (-y ^ 2 / 2) =
      2 ^ ((q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := q) (b := 1 / 2)
    (by norm_num) hq (by norm_num)
  have hhalf : (1 / 2 : ℝ) ^ (-(q + 1) / 2) = 2 ^ ((q + 1) / 2) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [hhalf] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [Real.rpow_two]
  congr 2
  ring

/-- The radial integral `∫₀^∞ y^{d-1} e^{-y²/2} (y²)^s dy` for `s > -d/2`. -/
private theorem integral_pow_mul_exp_mul_rpow {d : ℕ} (hd : 1 ≤ d) {s : ℝ}
    (hs : -((d : ℝ) / 2) < s) :
    ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (rexp (-y ^ 2 / 2) * (y ^ 2) ^ s) =
      2 ^ ((d : ℝ) / 2 + s) * (1 / 2) * Real.Gamma ((d : ℝ) / 2 + s) := by
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  have h := integral_rpow_mul_exp_neg_sq_div_two (q := (d : ℝ) - 1 + 2 * s) (by linarith)
  rw [show ((d : ℝ) - 1 + 2 * s + 1) / 2 = (d : ℝ) / 2 + s by ring] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  rw [← Real.rpow_natCast, hcast, ← Real.rpow_two, ← Real.rpow_mul hy.le, mul_left_comm,
    ← Real.rpow_add hy]
  ring_nf

/-- The real moments of `χ²_d` under the law itself. -/
private theorem integral_norm_sq_rpow_gaussianVector {s : ℝ}
    (hs : -((Fintype.card n : ℝ) / 2) < s) :
    ∫ x, (‖WithLp.toLp 2 x‖ ^ 2) ^ s ∂(gaussianVector n) =
      2 ^ s * Real.Gamma ((Fintype.card n : ℝ) / 2 + s) /
        Real.Gamma ((Fintype.card n : ℝ) / 2) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hs0 : 0 < s := by simpa [Fintype.card_eq_zero] using hs
    simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, zero_div, Real.Gamma_zero, div_zero]
    have h0 (x : n → ℝ) : (‖WithLp.toLp 2 x‖ ^ 2) ^ s = 0 := by
      rw [Subsingleton.elim (WithLp.toLp 2 x) 0, norm_zero, zero_pow two_ne_zero,
        Real.zero_rpow hs0.ne']
    simp only [h0, integral_zero]
  have hnorm := integral_radial_gaussianVector (n := n) (fun y => (y ^ 2) ^ (0 : ℝ))
  have hmom := integral_radial_gaussianVector (n := n) (fun y => (y ^ 2) ^ s)
  set d := Fintype.card n with hd_def
  have hd : 1 ≤ d := Fintype.card_pos
  simp only [Real.rpow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one] at hnorm
  rw [show (fun y : ℝ => y ^ (d - 1) * rexp (-y ^ 2 / 2)) =
      fun y => y ^ (d - 1) * (rexp (-y ^ 2 / 2) * (y ^ 2) ^ (0 : ℝ)) by
    simp only [Real.rpow_zero, mul_one],
    integral_pow_mul_exp_mul_rpow hd (neg_lt_zero.mpr (by positivity)), add_zero] at hnorm
  rw [hmom, integral_pow_mul_exp_mul_rpow hd hs, Real.rpow_add (by norm_num)]
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [eq_div_iff hG.ne']
  linear_combination (-(2 ^ s * Real.Gamma ((d : ℝ) / 2 + s))) * hnorm


/-- `(‖X‖²)^s` is integrable for a standard Gaussian vector exactly in the range `s > -d/2`. -/
theorem integrable_norm_sq_rpow_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {s : ℝ} (hs : -((Fintype.card n : ℝ) / 2) < s) :
    Integrable (fun ω => (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ s) μ := by
  have hf : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ s := by fun_prop
  refine (integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable).1 ?_
  rw [hX.map_eq]
  rcases isEmpty_or_nonempty n with hn | hn
  · have hs0 : 0 < s := by simpa [Fintype.card_eq_zero] using hs
    have h0 : (fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ s) = fun _ => 0 := by
      funext x
      rw [Subsingleton.elim (WithLp.toLp 2 x) 0, norm_zero, zero_pow two_ne_zero,
        Real.zero_rpow hs0.ne']
    rw [h0]
    exact integrable_zero _ _ _
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_norm_sq_rpow_gaussianVector hs]
  have h1 : 0 < Real.Gamma ((Fintype.card n : ℝ) / 2 + s) :=
    Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma ((Fintype.card n : ℝ) / 2) :=
    Real.Gamma_pos_of_pos (by have : 0 < Fintype.card n := Fintype.card_pos; positivity)
  positivity

/-- **The real moments of `χ²_d`**: `E (‖X‖²)^s = 2^s Γ(d/2 + s) / Γ(d/2)` for `s > -d/2`. -/
theorem integral_norm_sq_rpow_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {s : ℝ} (hs : -((Fintype.card n : ℝ) / 2) < s) :
    ∫ ω, (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ s ∂μ =
      2 ^ s * Real.Gamma ((Fintype.card n : ℝ) / 2 + s) /
        Real.Gamma ((Fintype.card n : ℝ) / 2) := by
  rw [← integral_norm_sq_rpow_gaussianVector hs]
  have hf : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ s := by fun_prop
  exact hX.integral_comp hf.aestronglyMeasurable

/-- `E 1 / χ²_d = 1 / (d - 2)` for `d ≥ 3`. -/
theorem integral_norm_sq_inv_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    (hn : 3 ≤ Fintype.card n) :
    ∫ ω, (‖WithLp.toLp 2 (X ω)‖ ^ 2)⁻¹ ∂μ = 1 / ((Fintype.card n : ℝ) - 2) := by
  have hd : (3 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
  simp only [← Real.rpow_neg_one]
  rw [integral_norm_sq_rpow_of_hasLaw_gaussianVector hX (by linarith),
    show (Fintype.card n : ℝ) / 2 = ((Fintype.card n : ℝ) / 2 + -1) + 1 by ring,
    Real.Gamma_add_one (by linarith), add_neg_cancel_right, Real.rpow_neg_one]
  have hG : 0 < Real.Gamma ((Fintype.card n : ℝ) / 2 + -1) := Real.Gamma_pos_of_pos (by linarith)
  have hb : (Fintype.card n : ℝ) - 2 ≠ 0 := by linarith
  rw [mul_div_assoc, mul_comm ((Fintype.card n : ℝ) / 2 + -1), ← div_div, div_self hG.ne',
    show (Fintype.card n : ℝ) / 2 + -1 = ((Fintype.card n : ℝ) - 2) / 2 by ring]
  field_simp

/-! ### The growth of `E ‖g_d‖` -/

/-- The expected norm of a standard Gaussian vector in dimension `d`:
`a_d = √2 Γ(d/2 + 1/2) / Γ(d/2)`. -/
private noncomputable def gaussNormMean (d : ℕ) : ℝ :=
  √2 * Real.Gamma ((d : ℝ) / 2 + 1 / 2) / Real.Gamma ((d : ℝ) / 2)

private theorem integral_norm_eq_gaussNormMean (hX : HasLaw X (gaussianVector n) μ) :
    ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ∂μ = gaussNormMean (Fintype.card n) := by
  have h := integral_norm_sq_rpow_of_hasLaw_gaussianVector hX (s := 1 / 2)
    (by have := (Nat.cast_nonneg (Fintype.card n) : (0 : ℝ) ≤ _); linarith)
  have e (ω : Ω) : (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ (1 / 2 : ℝ) = ‖WithLp.toLp 2 (X ω)‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  simp only [e] at h
  rw [h, gaussNormMean, ← Real.sqrt_eq_rpow]

private theorem gaussNormMean_pos {d : ℕ} (hd : 1 ≤ d) : 0 < gaussNormMean d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 + 1 / 2 by positivity)
  have h2 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by positivity)
  unfold gaussNormMean
  positivity

private theorem gaussNormMean_mul_succ {d : ℕ} (hd : 1 ≤ d) :
    gaussNormMean d * gaussNormMean (d + 1) = d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 + 1 / 2 by positivity)
  have h2 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by positivity)
  unfold gaussNormMean
  rw [Nat.cast_succ, show ((d : ℝ) + 1) / 2 = (d : ℝ) / 2 + 1 / 2 by ring,
    show (d : ℝ) / 2 + 1 / 2 + 1 / 2 = (d : ℝ) / 2 + 1 by ring,
    Real.Gamma_add_one (show (d : ℝ) / 2 ≠ 0 by positivity)]
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [show √2 * Real.Gamma ((d : ℝ) / 2 + 1 / 2) / Real.Gamma ((d : ℝ) / 2) *
      (√2 * ((d : ℝ) / 2 * Real.Gamma ((d : ℝ) / 2)) / Real.Gamma ((d : ℝ) / 2 + 1 / 2)) =
      (√2 * √2) * (d / 2) by field_simp, hs]
  ring

/-- `a_d ≤ √d`, by Jensen (`IsIsotropic.integral_norm_mulVec_le` with `A = 1`). -/
private theorem gaussNormMean_sq_le (d : ℕ) : gaussNormMean d ^ 2 ≤ d := by
  have hX : HasLaw (id : (Fin d → ℝ) → Fin d → ℝ) (gaussianVector (Fin d))
      (gaussianVector (Fin d)) := HasLaw.id
  have h := (isIsotropic_of_hasLaw_gaussianVector hX).integral_norm_mulVec_le
    (1 : Matrix (Fin d) (Fin d) ℝ)
  have h0 : 0 ≤ ∫ x, ‖WithLp.toLp 2 (id x : Fin d → ℝ)‖ ∂(gaussianVector (Fin d)) :=
    integral_nonneg fun _ => norm_nonneg _
  simp only [Matrix.one_mulVec] at h
  rw [integral_norm_eq_gaussNormMean hX, Fintype.card_fin] at h h0
  calc gaussNormMean d ^ 2 ≤ frobNorm (1 : Matrix (Fin d) (Fin d) ℝ) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = d := by rw [frobNorm_one_sq, Fintype.card_fin]

/-! ### The sequence argument -/
/-- Comparison sequence `B m = m - 1/2 + 3/(20 m)`. -/
private noncomputable def enB (m : ℝ) : ℝ := m - 1 / 2 + 3 / (20 * m)

private theorem enB_pos {m : ℝ} (hm : 1 ≤ m) : 0 < enB m := by
  unfold enB
  have : 0 < 3 / (20 * m) := by positivity
  linarith

private theorem enB_mono_step {m : ℝ} (hm : 1 ≤ m) : m ^ 2 * enB (m + 2) ≤ (m + 1) ^ 2 * enB m := by
  unfold enB
  have hm0 : 0 < m := by linarith
  rw [← sub_nonneg]
  have e : (m + 1) ^ 2 * (m - 1 / 2 + 3 / (20 * m)) - m ^ 2 * (m + 2 - 1 / 2 + 3 / (20 * (m + 2)))
      = (2 * m ^ 2 - 5 * m + 6) / (20 * m * (m + 2)) := by
    field_simp
    ring
  rw [e]
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg (m - 5 / 4)]

private theorem enB_le_div {M : ℝ} (hM : 1 ≤ M) : M / enB M ≤ 1 + 1 / M := by
  have hB := enB_pos hM
  rw [div_le_iff₀ hB]
  unfold enB
  have hM0 : 0 < M := by linarith
  have e : (1 + 1 / M) * (M - 1 / 2 + 3 / (20 * M)) - M
      = (1 / 2) - 1 / (2 * M) + 3 / (20 * M) + 3 / (20 * M ^ 2) := by
    field_simp; ring
  have h1 : 1 / (2 * M) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have : 0 ≤ 3 / (20 * M) := by positivity
  have : 0 ≤ 3 / (20 * M ^ 2) := by positivity
  nlinarith

/-- Abstract sequence argument: if `a m · a (m+1) = m`, `a m > 0` and `a m² ≤ m` for `m ≥ 1`,
then `a m² ≤ m - 1/2 + 3/(20m)`. -/
private theorem en_seq_sq_le (a : ℕ → ℝ) (hpos : ∀ m, 1 ≤ m → 0 < a m)
    (hrec : ∀ m, 1 ≤ m → a m * a (m + 1) = m) (hsq : ∀ m, 1 ≤ m → a m ^ 2 ≤ m)
    (m : ℕ) (hm : 1 ≤ m) : a m ^ 2 ≤ enB m := by
  have hstep : ∀ k, 1 ≤ k → a (k + 2) = ((k : ℝ) + 1) / k * a k := by
    intro k hk
    have h1 := hrec k hk
    have h2 := hrec (k + 1) (by omega)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have ha1 := hpos (k + 1) (by omega)
    push_cast at h2
    rw [show k + 1 + 1 = k + 2 by ring] at h2
    field_simp
    nlinarith
  -- ratio `ρ k = a k² / B k` is nondecreasing along steps of two
  have hmono : ∀ k, 1 ≤ k → a k ^ 2 / enB k ≤ a (k + 2) ^ 2 / enB ((k + 2 : ℕ)) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hB := enB_pos hk1
    have hB2 := enB_pos (show (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) by push_cast; linarith)
    rw [hstep k hk, div_le_div_iff₀ hB hB2]
    have hms := enB_mono_step hk1
    push_cast
    have e : (((k : ℝ) + 1) / k * a k) ^ 2 = ((k : ℝ) + 1) ^ 2 * a k ^ 2 / k ^ 2 := by
      field_simp
    rw [e]
    rw [show ((k : ℝ) + 1) ^ 2 * a k ^ 2 / k ^ 2 * enB k
        = a k ^ 2 * (((k : ℝ) + 1) ^ 2 * enB k) / k ^ 2 by ring]
    rw [le_div_iff₀ (by positivity)]
    have : a k ^ 2 * (k ^ 2 * enB (k + 2)) ≤ a k ^ 2 * ((k + 1) ^ 2 * enB k) :=
      mul_le_mul_of_nonneg_left hms (sq_nonneg _)
    nlinarith
  have hiter : ∀ j : ℕ, a m ^ 2 / enB m ≤ a (m + 2 * j) ^ 2 / enB ((m + 2 * j : ℕ)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine ih.trans ?_
      have := hmono (m + 2 * j) (by omega)
      rwa [show m + 2 * j + 2 = m + 2 * (j + 1) by ring] at this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hB := enB_pos hm1
  by_contra hcon
  push Not at hcon
  set ρ := a m ^ 2 / enB m with hρ
  have hρ1 : 1 < ρ := by rw [hρ, lt_div_iff₀ hB]; linarith
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / (ρ - 1))
  set M : ℕ := m + 2 * j with hM
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hBM := enB_pos hM1
  have h1 := hiter j
  rw [← hM] at h1
  have h2 : a M ^ 2 / enB M ≤ M / enB M :=
    div_le_div_of_nonneg_right (hsq M (by omega)) hBM.le
  have h3 := enB_le_div hM1
  have hj0 : (0 : ℝ) < j := lt_trans (by positivity) hj
  have hjM : (j : ℝ) ≤ M := by rw [hM]; push_cast; linarith
  have h4 : 1 / (M : ℝ) < ρ - 1 := by
    have : 1 / (M : ℝ) ≤ 1 / j := one_div_le_one_div_of_le hj0 hjM
    have : 1 / (j : ℝ) < ρ - 1 := by
      rw [div_lt_iff₀ hj0]
      rw [div_lt_iff₀ (by linarith)] at hj
      linarith
    linarith
  linarith

/-- `√(m(m+1)) ≥ m + 1/2 - 1/(8m)` for `m ≥ 1`. -/
private theorem en_sqrt_mul_ge {m : ℝ} (hm : 1 ≤ m) :
    m + 1 / 2 - 1 / (8 * m) ≤ Real.sqrt m * Real.sqrt (m + 1) := by
  rw [← Real.sqrt_mul (by linarith)]
  apply Real.le_sqrt_of_sq_le
  have hm0 : 0 < m := by linarith
  have e : (m + 1 / 2 - 1 / (8 * m)) ^ 2 = m * (m + 1) - 1 / (8 * m) + 1 / (64 * m ^ 2) := by
    field_simp; ring
  rw [e]
  have : 1 / (64 * m ^ 2) ≤ 1 / (8 * m) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

/-- One step: if `0 < a ≤ √(B m)` and `a · b = m` then `b - a ≥ √(m+1) - √m`. -/
private theorem en_step {m a b : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (hab : a * b = m)
    (hB : a ^ 2 ≤ enB m) :
    Real.sqrt (m + 1) - Real.sqrt m ≤ b - a := by
  have hm0 : 0 < m := by linarith
  have hb : b = m / a := by field_simp; linarith
  rw [hb]
  set s := Real.sqrt m with hs
  set t := Real.sqrt (m + 1) with ht
  have hs0 : 0 < s := Real.sqrt_pos.2 hm0
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = m := Real.sq_sqrt hm0.le
  have ht2 : t ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
  have hst := en_sqrt_mul_ge hm
  rw [← hs, ← ht] at hst
  have hd : t - s = 1 / (t + s) := by
    field_simp
    nlinarith
  have hts : 0 < t + s := by linarith
  have hc : 0 < 1 / 2 - 3 / (20 * m) := by
    have : 3 / (20 * m) ≤ 3 / 20 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hma : 1 / 2 - 3 / (20 * m) ≤ m - a ^ 2 := by unfold enB at hB; linarith
  have hsq : 4 * m + 2 - 1 / (4 * m) ≤ (t + s) ^ 2 := by
    have : (t + s) ^ 2 = t ^ 2 + s ^ 2 + 2 * (s * t) := by ring
    rw [this, ht2, hs2]
    have : 2 * (m + 1 / 2 - 1 / (8 * m)) = 2 * m + 1 - 1 / (4 * m) := by field_simp; ring
    linarith
  have hpoly : enB m ≤ (1 / 2 - 3 / (20 * m)) ^ 2 * (4 * m + 2 - 1 / (4 * m)) := by
    unfold enB
    rw [← sub_nonneg]
    have e : (1 / 2 - 3 / (20 * m)) ^ 2 * (4 * m + 2 - 1 / (4 * m)) - (m - 1 / 2 + 3 / (20 * m))
        = (640 * m ^ 3 - 676 * m ^ 2 + 132 * m - 9) / (1600 * m ^ 3) := by
      field_simp; ring
    rw [e]
    apply div_nonneg _ (by positivity)
    nlinarith [sq_nonneg (m - 1), mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hm)]
  have h5 : a ^ 2 ≤ ((1 / 2 - 3 / (20 * m)) * (t + s)) ^ 2 := by
    rw [mul_pow]
    refine hB.trans (hpoly.trans ?_)
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  have h6 : a ≤ (1 / 2 - 3 / (20 * m)) * (t + s) :=
    (pow_le_pow_iff_left₀ ha.le (by positivity) (by norm_num)).1 h5
  have hkey : a ≤ (m - a ^ 2) * (t + s) :=
    h6.trans (mul_le_mul_of_nonneg_right hma hts.le)
  have e2 : m / a - a = (m - a ^ 2) / a := by field_simp
  rw [hd, e2, div_le_div_iff₀ hts ha]
  linarith

/-- Telescoping: `a N - a n ≥ √N - √n` for `N ≥ n ≥ 1`. -/
private theorem en_seq_diff (a : ℕ → ℝ) (hpos : ∀ m, 1 ≤ m → 0 < a m)
    (hrec : ∀ m, 1 ≤ m → a m * a (m + 1) = m) (hsq : ∀ m, 1 ≤ m → a m ^ 2 ≤ m)
    {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    Real.sqrt N - Real.sqrt n ≤ a N - a n := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk1 : 1 ≤ k := le_trans hn hk
    have hst := en_step (m := (k : ℝ)) (by exact_mod_cast hk1) (hpos k hk1) (hrec k hk1)
      (en_seq_sq_le a hpos hrec hsq k hk1)
    push_cast
    linarith

/-- **Growth of `E ‖g_d‖`**: for standard Gaussian vectors `X` in `ℝⁿ` and `Y` in `ℝᵐ`
(possibly on different probability spaces) with `1 ≤ n ≤ m`, `√m - √n ≤ E ‖Y‖ - E ‖X‖`.
[DavidsonSzarek2001, proof of Theorem II.13]; the step of Gordon's lower bound for the smallest
singular value of a Gaussian matrix. Both hypotheses are needed: for `n = 0` it would claim
`√m ≤ E ‖Y‖`, false for `m ≥ 1`, and for `n > m` the inequality reverses. -/
theorem le_integral_norm_sub_integral_norm_of_hasLaw_gaussianVector {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {m : Type*} [Fintype m] {Y : Ω' → m → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) (hY : HasLaw Y (gaussianVector m) ν)
    (hn : 0 < Fintype.card n) (hnm : Fintype.card n ≤ Fintype.card m) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) ≤
      ∫ ω, ‖WithLp.toLp 2 (Y ω)‖ ∂ν - ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ∂μ := by
  rw [integral_norm_eq_gaussNormMean hX, integral_norm_eq_gaussNormMean hY]
  exact en_seq_diff gaussNormMean (fun _ hd => gaussNormMean_pos hd)
    (fun _ hd => gaussNormMean_mul_succ hd) (fun d _ => gaussNormMean_sq_le d) hn hnm

end NLAlib
