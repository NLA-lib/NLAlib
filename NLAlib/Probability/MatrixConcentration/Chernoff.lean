/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.MGFBound

/-!
# The matrix Chernoff inequalities: the trace form

A random positive semidefinite matrix `0 ≤ X ≤ L • 1` has the matrix MGF bound
`E exp (θ X) ≤ exp ((e^{θL} - 1)/L • E X)` (Tropp 2015, Lemma 5.4.1). The Chernoff tails follow
from the trace form of such a bound alone: if `E tr exp (θ Y) ≤ tr exp ((e^{θL} - 1)/L • V)` for
every `θ > 0` (resp. `θ < 0`), with `V` positive semidefinite, then the largest (resp. smallest)
eigenvalue of `Y` has the Chernoff upper (resp. lower) tail relative to that of `V`. Sums of
independent bounded positive semidefinite matrices are the main instance
(`NLAlib/Probability/MatrixConcentration/ChernoffSum.lean`); sampling without replacement is
another, which is why the tails are stated from the trace bound.

## Main results

* `NLAlib.hasMatrixMGFBound_of_posSemidef_of_le`: the Chernoff MGF bound.
* `NLAlib.measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le`,
  `NLAlib.measureReal_eigenvalue_le_le_chernoff_of_integral_le`: the tails, source form.
* `NLAlib.measureReal_eigenvalue_zero_ge_le_card_mul_exp_of_integral_le`,
  `NLAlib.measureReal_eigenvalue_le_le_card_mul_exp_of_integral_le`: the simplified forms.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Scalar inequalities -/

/-- The chord bound for the exponential on `[0, L]`: `e^{θx} ≤ 1 + (e^{θL} - 1) x / L`. -/
private theorem exp_mul_le_one_add_chord {L θ x : ℝ} (hL : 0 < L) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    Real.exp (θ * x) ≤ 1 + (Real.exp (θ * L) - 1) / L * x := by
  have ht0 : 0 ≤ x / L := div_nonneg hx0 hL.le
  have ht1 : x / L ≤ 1 := (div_le_one hL).mpr hxL
  have hc := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (θ * L)) (sub_nonneg.mpr ht1) ht0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have hxe : θ * x = x / L * (θ * L) := by field_simp
  rw [hxe]
  refine hc.trans_eq ?_
  field_simp
  ring

/-- `-δ - (1 - δ) log (1 - δ) ≤ -δ²/2` for `0 ≤ δ < 1`. -/
private theorem neg_sub_mul_log_one_sub_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    -δ - (1 - δ) * Real.log (1 - δ) ≤ -(δ ^ 2 / 2) := by
  let g : ℝ → ℝ := fun t => (1 - t) * Real.log (1 - t) + t - t ^ 2 / 2
  have hderiv : ∀ t, t < 1 → HasDerivAt g (-Real.log (1 - t) - t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have hprod := h1.mul (h1.log (by linarith))
    have hp : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - t) t := by
      have := (hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)
      exact this.congr_deriv (by norm_num)
    refine ((hprod.add hp).congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => ?_)
    · field_simp [show (1 - t) ≠ 0 by linarith]
      ring
    · simp only [g, Pi.add_apply, Pi.mul_apply]
      ring
  have hmono : MonotoneOn g (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1) ?_ ?_ ?_
    · exact fun t ht => (hderiv t ht.2).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      exact (hderiv t ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      rw [(hderiv t ht.2).deriv]
      have := Real.log_le_sub_one_of_pos (show 0 < 1 - t by linarith [ht.2])
      linarith
  have := hmono (Set.mem_Ico.2 ⟨le_rfl, by norm_num⟩) (Set.mem_Ico.2 ⟨hδ0, hδ1⟩) hδ0
  simp only [g, sub_zero, Real.log_one, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at this
  linarith

/-- `δ - (1 + δ) log (1 + δ) ≤ -δ²/3` for `0 ≤ δ ≤ 1`, from `log (1 + δ) ≥ 2δ / (δ + 2)`. -/
private theorem sub_mul_log_one_add_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ - (1 + δ) * Real.log (1 + δ) ≤ -(δ ^ 2 / 3) := by
  have hlow := le_hasSum (Real.hasSum_log_one_add hδ0) 0 (fun n _ => by positivity)
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, mul_one, pow_one] at hlow
  have hpos : 0 < δ + 2 := by linarith
  have key : δ + δ ^ 2 / 3 ≤ (1 + δ) * (2 * (δ / (δ + 2))) := by
    rw [← sub_nonneg]
    have : (1 + δ) * (2 * (δ / (δ + 2))) - (δ + δ ^ 2 / 3) = δ ^ 2 * (1 - δ) / (3 * (δ + 2)) := by
      field_simp
      ring
    rw [this]
    have : 0 ≤ 1 - δ := by linarith
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hlow (show 0 ≤ 1 + δ by linarith)]

/-- The Chernoff tail base in exponential form:
`(e^s / (1 + s)^{1+s})^a = e^{(s - (1 + s) log (1 + s)) a}`. -/
private theorem chernoff_base_rpow_eq {s : ℝ} (hs : 0 < 1 + s) (a : ℝ) :
    (Real.exp s / (1 + s) ^ (1 + s)) ^ a = Real.exp ((s - (1 + s) * Real.log (1 + s)) * a) := by
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hs _)),
    Real.log_div (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hs _).ne', Real.log_exp,
    Real.log_rpow hs]

/-! ### The matrix moment generating function -/

/-- The chord bound for a matrix with `0 ≤ A ≤ L • 1`: `exp (θ A) ≤ 1 + (e^{θL} - 1)/L • A`. -/
private theorem exp_smul_le_one_add_chord {A : Matrix n n 𝕜} {L : ℝ} (hL : 0 < L) (θ : ℝ)
    (hA : A.PosSemidef) (hAL : A ≤ L • (1 : Matrix n n 𝕜)) :
    exp (θ • A) ≤ 1 + ((Real.exp (θ * L) - 1) / L) • A := by
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  have hθA : θ • A = cfc (fun x : ℝ => θ * x) A := by
    rw [cfc_const_mul θ (fun x => x) A (hcont _), cfc_id' ℝ A hsa]
  have hH : (θ • A).IsHermitian := (IsSelfAdjoint.all θ).smul hA.isHermitian
  have hLe : exp (θ • A) = cfc (fun x : ℝ => Real.exp (θ * x)) A := by
    rw [hH.exp_eq_cfc, hθA, ← cfc_comp' Real.exp (fun x => θ * x) A
      ((A.finite_real_spectrum.image _).continuousOn _) (hcont _) hsa]
  have hR : cfc (fun x : ℝ => 1 + (Real.exp (θ * L) - 1) / L * x) A =
      1 + ((Real.exp (θ * L) - 1) / L) • A := by
    rw [cfc_const_add 1 (fun x : ℝ => (Real.exp (θ * L) - 1) / L * x) A (hcont _) hsa,
      cfc_const_mul _ (fun x : ℝ => x) A (hcont _), cfc_id' ℝ A hsa, map_one]
  have h0 : (0 : ℝ) • (1 : Matrix n n 𝕜) ≤ A := by
    rw [zero_smul]
    exact hA.nonneg
  rw [hLe, ← hR]
  exact cfc_le_cfc_of_forall_mem_Icc h0 hAL fun x hx => exp_mul_le_one_add_chord hL hx.1 hx.2

omit [IsProbabilityMeasure μ] in
/-- A random matrix with `0 ≤ X ≤ L • 1` almost surely is integrable. -/
theorem integrable_of_posSemidef_of_le [IsFiniteMeasure μ] {X : Ω → Matrix n n 𝕜}
    (hXm : AEMeasurable X μ) {L : ℝ} (hpsd : ∀ᵐ ω ∂μ, (X ω).PosSemidef)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) : Integrable X μ := by
  refine Integrable.of_bound hXm.aestronglyMeasurable |L| ?_
  filter_upwards [hpsd, hle] with ω h1 h2
  rw [← specNorm_eq_norm, h1.specNorm_le_iff (abs_nonneg L)]
  exact h2.trans (smul_one_le_smul_one (le_abs_self L))

omit [IsProbabilityMeasure μ] in
/-- `exp (θ X)` is integrable when `0 ≤ X ≤ L • 1` almost surely. -/
private theorem integrable_exp_smul_of_posSemidef_of_le [IsFiniteMeasure μ]
    {X : Ω → Matrix n n 𝕜} (hXm : AEMeasurable X μ) {L : ℝ}
    (hpsd : ∀ᵐ ω ∂μ, (X ω).PosSemidef) (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) (θ : ℝ) :
    Integrable (fun ω => exp (θ • X ω)) μ := by
  have hexp : Continuous (exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  refine Integrable.of_bound
    (hexp.measurable.comp_aemeasurable (hXm.const_smul θ)).aestronglyMeasurable
    (Real.exp (|θ| * |L|)) ?_
  filter_upwards [hpsd, hle] with ω h1 h2
  have hX : specNorm (X ω) ≤ |L| := by
    rw [h1.specNorm_le_iff (abs_nonneg L)]
    exact h2.trans (smul_one_le_smul_one (le_abs_self L))
  rw [← specNorm_eq_norm]
  refine (specNorm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
  rw [specNorm_eq_norm, norm_smul, Real.norm_eq_abs, ← specNorm_eq_norm]
  exact mul_le_mul_of_nonneg_left hX (abs_nonneg θ)

/-- **The Chernoff matrix MGF bound** ([Tropp2015], Lemma 5.4.1): a random matrix with
`0 ≤ X ≤ L • 1` almost surely has `E exp (θ X) ≤ exp ((e^{θL} - 1)/L • E X)` for every `θ`. -/
theorem hasMatrixMGFBound_of_posSemidef_of_le {X : Ω → Matrix n n 𝕜} (hXm : AEMeasurable X μ)
    {L : ℝ} (hL : 0 < L) (hpsd : ∀ᵐ ω ∂μ, (X ω).PosSemidef)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) :
    HasMatrixMGFBound X (fun θ => (Real.exp (θ * L) - 1) / L) (∫ ω, X ω ∂μ) Set.univ μ := by
  have hXi := integrable_of_posSemidef_of_le hXm hpsd hle
  have hEX : (∫ ω, X ω ∂μ).IsHermitian :=
    Matrix.isHermitian_integral (hpsd.mono fun _ h => h.isHermitian)
  refine ⟨hpsd.mono fun _ h => h.isHermitian, hEX,
    fun θ _ => integrable_exp_smul_of_posSemidef_of_le hXm hpsd hle θ, fun θ _ => ?_⟩
  set c := (Real.exp (θ * L) - 1) / L
  have hcX : Integrable (fun ω => c • X ω) μ := hXi.smul c
  calc ∫ ω, exp (θ • X ω) ∂μ ≤ ∫ ω, (1 + c • X ω) ∂μ := by
        refine integral_mono_ae (integrable_exp_smul_of_posSemidef_of_le hXm hpsd hle θ)
          ((integrable_const 1).add hcX) ?_
        filter_upwards [hpsd, hle] with ω h1 h2
        exact exp_smul_le_one_add_chord hL θ h1 h2
    _ = 1 + c • ∫ ω, X ω ∂μ := by
        rw [integral_add (integrable_const _) hcX, integral_const, integral_smul,
          probReal_univ, one_smul]
    _ ≤ exp (c • ∫ ω, X ω ∂μ) := Matrix.IsHermitian.one_add_le_exp ((IsSelfAdjoint.all c).smul hEX)

variable {Y : Ω → Matrix n n 𝕜} {V : Matrix n n 𝕜} {L : ℝ}

/-- **The matrix Chernoff upper tail** from a trace bound ([Tropp2015], Theorem 5.1.1):
`P((1 + δ) λ_max V ≤ λ_max Y) ≤ d (e^δ / (1 + δ)^{1+δ})^{λ_max V / L}`. -/
theorem measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le [Nonempty n]
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hV : V.PosSemidef) (hL : 0 < L)
    (hint : ∀ θ : ℝ, 0 < θ → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ, 0 < θ → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue V 0 ≤ eigenvalue (Y ω) 0} ≤
      Fintype.card n * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue V 0 / L) := by
  have hm : 0 ≤ eigenvalue V 0 := hV.eigenvalue_nonneg 0
  rcases hδ.eq_or_lt with rfl | hδ'
  · rw [add_zero, Real.exp_zero, Real.one_rpow, div_one, Real.one_rpow, mul_one]
    exact measureReal_le_one.trans (Nat.one_le_cast.mpr Fintype.card_pos)
  have h1δ : 0 < 1 + δ := by linarith
  set θ := Real.log (1 + δ) / L with hθdef
  have hθ : 0 < θ := div_pos (Real.log_pos (by linarith)) hL
  have hθL : Real.exp (θ * L) = 1 + δ := by
    rw [hθdef, div_mul_cancel₀ _ hL.ne', Real.exp_log h1δ]
  have hc : 0 ≤ (Real.exp (θ * L) - 1) / L := by
    rw [hθL]
    exact div_nonneg (by linarith) hL.le
  have htrd := Matrix.IsHermitian.re_trace_exp_le_card_mul_exp
    ((IsSelfAdjoint.all ((Real.exp (θ * L) - 1) / L)).smul hV.isHermitian)
  rw [eigenvalue_real_smul _ hc] at htrd
  calc μ.real {ω | (1 + δ) * eigenvalue V 0 ≤ eigenvalue (Y ω) 0}
      ≤ Real.exp (-θ * ((1 + δ) * eigenvalue V 0)) *
          ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ :=
        measureReal_eigenvalue_zero_ge_le hY hθ (hint θ hθ) _
    _ ≤ Real.exp (-θ * ((1 + δ) * eigenvalue V 0)) *
          (Fintype.card n * Real.exp ((Real.exp (θ * L) - 1) / L * eigenvalue V 0)) :=
        mul_le_mul_of_nonneg_left ((htr θ hθ).trans htrd) (Real.exp_pos _).le
    _ = Fintype.card n * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue V 0 / L) := by
        rw [chernoff_base_rpow_eq h1δ, hθL, mul_left_comm, ← Real.exp_add, hθdef]
        congr 2
        field_simp
        ring

/-- **The matrix Chernoff lower tail** from a trace bound ([Tropp2015], Theorem 5.1.1):
`P(λ_min Y ≤ (1 - δ) λ_min V) ≤ d (e^{-δ} / (1 - δ)^{1-δ})^{λ_min V / L}` for `0 ≤ δ < 1`. -/
theorem measureReal_eigenvalue_le_le_chernoff_of_integral_le (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hV : V.PosSemidef) (hL : 0 < L) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (hint : ∀ θ : ℝ, θ < 0 → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ, θ < 0 → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (Y ω) k ≤ (1 - δ) * eigenvalue V k} ≤
      Fintype.card n * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (eigenvalue V k / L) := by
  have hm : 0 ≤ eigenvalue V k := hV.eigenvalue_nonneg k
  rcases hδ0.eq_or_lt with rfl | hδ'
  · rw [neg_zero, sub_zero, Real.exp_zero, Real.one_rpow, div_one, Real.one_rpow, mul_one]
    exact measureReal_le_one.trans (Nat.one_le_cast.mpr (by omega))
  have h1δ : 0 < 1 - δ := by linarith
  set θ := Real.log (1 - δ) / L with hθdef
  have hθ : θ < 0 := div_neg_of_neg_of_pos (Real.log_neg h1δ (by linarith)) hL
  have hθL : Real.exp (θ * L) = 1 - δ := by
    rw [hθdef, div_mul_cancel₀ _ hL.ne', Real.exp_log h1δ]
  set c := (Real.exp (θ * L) - 1) / L with hcdef
  have hc : c ≤ 0 := by
    rw [hcdef, hθL]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le
  have htrd :=
    Matrix.IsHermitian.re_trace_exp_le_card_mul_exp ((IsSelfAdjoint.all c).smul hV.isHermitian)
  have heig : eigenvalue (c • V) 0 = c * eigenvalue V k := by
    rw [show c • V = -((-c) • V) by rw [neg_smul, neg_neg],
      eigenvalue_neg _ (show 0 + k + 1 = Fintype.card n by omega),
      eigenvalue_real_smul _ (neg_nonneg.mpr hc), neg_mul, neg_neg]
  rw [heig] at htrd
  have hbase := chernoff_base_rpow_eq (s := -δ) (by linarith) (eigenvalue V k / L)
  rw [← sub_eq_add_neg] at hbase
  calc μ.real {ω | eigenvalue (Y ω) k ≤ (1 - δ) * eigenvalue V k}
      ≤ Real.exp (-θ * ((1 - δ) * eigenvalue V k)) *
          ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ :=
        measureReal_eigenvalue_le_le hY hk hθ (hint θ hθ) _
    _ ≤ Real.exp (-θ * ((1 - δ) * eigenvalue V k)) *
          (Fintype.card n * Real.exp (c * eigenvalue V k)) :=
        mul_le_mul_of_nonneg_left ((htr θ hθ).trans htrd) (Real.exp_pos _).le
    _ = Fintype.card n * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (eigenvalue V k / L) := by
        rw [hbase, hcdef, hθL, mul_left_comm, ← Real.exp_add, hθdef]
        congr 2
        field_simp
        ring

/-- The simplified Chernoff upper tail from a trace bound, `≤ d e^{-δ² λ_max V / (3L)}` for
`0 ≤ δ ≤ 1`; weaker than the source form in every regime and proved from it. -/
theorem measureReal_eigenvalue_zero_ge_le_card_mul_exp_of_integral_le [Nonempty n]
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hV : V.PosSemidef) (hL : 0 < L)
    (hint : ∀ θ : ℝ, 0 < θ → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ, 0 < θ → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    μ.real {ω | (1 + δ) * eigenvalue V 0 ≤ eigenvalue (Y ω) 0} ≤
      Fintype.card n * Real.exp (-δ ^ 2 * eigenvalue V 0 / (3 * L)) := by
  have hm : 0 ≤ eigenvalue V 0 := hV.eigenvalue_nonneg 0
  refine (measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le hY hV hL hint htr
    hδ0).trans ?_
  rw [chernoff_base_rpow_eq (by linarith)]
  gcongr
  calc (δ - (1 + δ) * Real.log (1 + δ)) * (eigenvalue V 0 / L)
      ≤ -(δ ^ 2 / 3) * (eigenvalue V 0 / L) :=
        mul_le_mul_of_nonneg_right (sub_mul_log_one_add_le hδ0 hδ1) (div_nonneg hm hL.le)
    _ = -δ ^ 2 * eigenvalue V 0 / (3 * L) := by ring

/-- The simplified Chernoff lower tail from a trace bound, `≤ d e^{-δ² λ_min V / (2L)}` for
`0 ≤ δ < 1`; weaker than the source form in every regime and proved from it. -/
theorem measureReal_eigenvalue_le_le_card_mul_exp_of_integral_le
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hV : V.PosSemidef) (hL : 0 < L) {k : ℕ}
    (hk : k + 1 = Fintype.card n)
    (hint : ∀ θ : ℝ, θ < 0 → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ, θ < 0 → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (Y ω) k ≤ (1 - δ) * eigenvalue V k} ≤
      Fintype.card n * Real.exp (-δ ^ 2 * eigenvalue V k / (2 * L)) := by
  have hm : 0 ≤ eigenvalue V k := hV.eigenvalue_nonneg k
  refine (measureReal_eigenvalue_le_le_chernoff_of_integral_le hY hV hL hk hint htr hδ0
    hδ1).trans ?_
  have hbase := chernoff_base_rpow_eq (s := -δ) (by linarith) (eigenvalue V k / L)
  rw [← sub_eq_add_neg] at hbase
  rw [hbase]
  gcongr
  calc (-δ - (1 - δ) * Real.log (1 - δ)) * (eigenvalue V k / L)
      ≤ -(δ ^ 2 / 2) * (eigenvalue V k / L) :=
        mul_le_mul_of_nonneg_right (neg_sub_mul_log_one_sub_le hδ0 hδ1) (div_nonneg hm hL.le)
    _ = -δ ^ 2 * eigenvalue V k / (2 * L) := by ring

end NLAlib
