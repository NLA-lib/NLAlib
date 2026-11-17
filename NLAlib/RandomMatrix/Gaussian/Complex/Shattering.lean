/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex.LeastSingularValue
public import NLAlib.RandomMatrix.Gaussian.Complex.SimpleSpectrum
public import NLAlib.Matrix.Perturbation.PseudospectralArea
public import NLAlib.Matrix.Perturbation.EigenvalueClustering
public import NLAlib.Matrix.QRIteration.SquareGrid
public import NLAlib.ForMathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Spectral regularization by complex Gaussian perturbations

Area estimates and eigenvector conditioning for a deterministic matrix plus a normalized
complex Gaussian matrix. All Gaussian entries are independent and have mean square modulus one.

## Main results

* The polynomial eigenvector-conditioning tail has constants $(128e,3,2,2)$.
* The polynomial eigenvalue-gap tail has constants $(10000e,5,1/2,2)$.

Both use the normalization $(\gamma/\sqrt n)\mathbf{G}$ and the existing listing and
diagonalizer events, without defining new random spectral statistics.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology ENNReal

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem measureReal_le_liminf_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) {C b : ℝ}
    (hC : 0 ≤ C) (hb : 0 < b) (hE : ∀ j, ∫⁻ ω, f j ω ∂μ ≤ ENNReal.ofReal C) :
    μ.real {ω | ENNReal.ofReal b ≤ liminf (fun j => f j ω) atTop} ≤ C / b := by
  have hFatou : ∫⁻ ω, liminf (fun j => f j ω) atTop ∂μ ≤ ENNReal.ofReal C :=
    (lintegral_liminf_le hf).trans ((liminf_le_liminf
      (Eventually.of_forall hE)).trans_eq (liminf_const _))
  have hMarkov := (mul_meas_ge_le_lintegral₀ (Measurable.liminf hf).aemeasurable
    (ENNReal.ofReal b)).trans hFatou
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMarkov
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.le,
    ENNReal.toReal_ofReal hC, ← measureReal_def] at hreal
  exact (le_div_iff₀ hb).2 (by simpa only [mul_comm] using hreal)

private theorem lintegral_area_le (M : Matrix n n ℂ) {k : ℕ} (hk : k + 1 = Fintype.card n)
    {γ ε R : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε) :
    ∫⁻ G : Matrix n n ℂ, volume
      ({z : ℂ | singularValues (z • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G)) k ≤ ε}
        ∩ Metric.ball 0 R) ∂complexGaussianMatrix n n ≤
      ENNReal.ofReal (Real.exp 1 * (Fintype.card n : ℝ) ^ 2 * ε ^ 2 / γ ^ 2) *
        volume (Metric.ball (0 : ℂ) R) := by
  let c : ℝ := γ / √(Fintype.card n : ℝ)
  let S : Set (Matrix n n ℂ × ℂ) :=
    {p | singularValues (p.2 • 1 - (M + c • p.1)) k ≤ ε ∧ p.2 ∈ Metric.ball 0 R}
  have hS : MeasurableSet S := by
    have hmat : Continuous (fun p : Matrix n n ℂ × ℂ => p.2 • 1 - (M + c • p.1)) :=
      (continuous_snd.smul continuous_const).sub
        (continuous_const.add (continuous_fst.const_smul c))
    exact (measurableSet_le ((continuous_singularValues k).comp hmat).measurable
      measurable_const).inter (measurable_snd measurableSet_ball)
  change ∫⁻ G, volume (Prod.mk G ⁻¹' S) ∂complexGaussianMatrix n n ≤ _
  rw [← Measure.prod_apply hS, Measure.prod_apply_symm hS]
  calc
    _ ≤ ∫⁻ z in Metric.ball (0 : ℂ) R,
        ENNReal.ofReal (Real.exp 1 * (Fintype.card n : ℝ) ^ 2 * ε ^ 2 / γ ^ 2) := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_mono
      intro z
      change (complexGaussianMatrix n n) ((fun G => (G,z)) ⁻¹' S) ≤ _
      by_cases hz : z ∈ Metric.ball (0 : ℂ) R
      · rw [Set.indicator_of_mem hz]
        have heq : (fun G : Matrix n n ℂ => (G,z)) ⁻¹' S =
            {G : Matrix n n ℂ | singularValues (M - z • 1 + c • G) k ≤ ε} := by
          ext G
          have he : z • (1 : Matrix n n ℂ) - (M + c • G) = -(M - z • 1 + c • G) := by abel
          simp only [Set.mem_preimage, S, Set.mem_ofPred_eq, hz, and_true, he,
            singularValues_neg]
        rw [heq, ← ofReal_measureReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal
          (measureReal_singularValues_add_smul_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix
            HasLaw.id (M - z • 1) hk hγ hε)
      · rw [Set.indicator_of_notMem hz]
        have he : (fun G : Matrix n n ℂ => (G,z)) ⁻¹' S = ∅ := by
          ext G
          simp only [Set.mem_preimage, S, Set.mem_ofPred_eq, hz, and_false,
            Set.mem_empty_iff_false]
        rw [he, measure_empty]
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]

private theorem measurable_area (ε R : ℝ) {k : ℕ} :
    Measurable (fun A : Matrix n n ℂ => volume
      ({z : ℂ | singularValues (z • 1 - A) k ≤ ε} ∩ Metric.ball 0 R)) := by
  let S : Set (Matrix n n ℂ × ℂ) :=
    {p | singularValues (p.2 • 1 - p.1) k ≤ ε ∧ p.2 ∈ Metric.ball 0 R}
  have hS : MeasurableSet S :=
    (measurableSet_le ((continuous_singularValues k).comp
      ((continuous_snd.smul continuous_const).sub continuous_fst)).measurable
        measurable_const).inter (measurable_snd measurableSet_ball)
  exact measurable_measure_prodMk_left hS

private theorem lintegral_normalized_area_le (M : Matrix n n ℂ) {k : ℕ}
    (hk : k + 1 = Fintype.card n) {γ ε R : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hR : 0 ≤ R) :
    ∫⁻ G : Matrix n n ℂ, ENNReal.ofReal (4 / (Real.pi * ε ^ 2)) * volume
      ({z : ℂ | singularValues (z • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G)) k ≤ ε}
        ∩ Metric.ball 0 R) ∂complexGaussianMatrix n n ≤
      ENNReal.ofReal (4 * Real.exp 1 * (Fintype.card n : ℝ) ^ 2 * R ^ 2 / γ ^ 2) := by
  have hm : Measurable (fun G : Matrix n n ℂ => volume
      ({z : ℂ | singularValues (z • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G)) k ≤ ε}
        ∩ Metric.ball 0 R)) := (measurable_area ε R (k := k)).comp
      (show Measurable (fun G : Matrix n n ℂ => M + (γ / √(Fintype.card n : ℝ)) • G) from
        measurable_const.add (measurable_id.const_smul (γ / √(Fintype.card n : ℝ))))
  rw [lintegral_const_mul _ hm]
  calc
    _ ≤ ENNReal.ofReal (4 / (Real.pi * ε ^ 2)) *
        (ENNReal.ofReal (Real.exp 1 * (Fintype.card n : ℝ) ^ 2 * ε ^ 2 / γ ^ 2) *
          volume (Metric.ball (0 : ℂ) R)) :=
      mul_le_mul le_rfl (lintegral_area_le M hk hγ hε.le) (by positivity) (by positivity)
    _ = _ := by
      rw [Complex.volume_ball, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
        ← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (sq_nonneg R),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp


private theorem measureReal_le_liminf_normalized_area_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {γ R b : ℝ}
    (hγ : 0 < γ) (hR : 0 ≤ R) (hb : 0 < b) {e : ℕ → ℝ} (he : ∀ j, 0 < e j) :
    μ.real {ω | ENNReal.ofReal b ≤ liminf (fun j =>
      ENNReal.ofReal (4 / (Real.pi * e j ^ 2)) * volume
        ({z : ℂ | singularValues
          (z • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ e j} ∩ Metric.ball 0 R)) atTop} ≤
      (4 * Real.exp 1 * (Fintype.card n : ℝ) ^ 2 * R ^ 2 / γ ^ 2) / b := by
  let f : ℕ → Matrix n n ℂ → ℝ≥0∞ := fun j X =>
    ENNReal.ofReal (4 / (Real.pi * e j ^ 2)) * volume
      ({z : ℂ | singularValues
        (z • 1 - (M + (γ / √(Fintype.card n : ℝ)) • X)) k ≤ e j} ∩ Metric.ball 0 R)
  have hf (j : ℕ) : Measurable (f j) := measurable_const.mul
    ((measurable_area (e j) R (k := k)).comp
      (measurable_const.add ((measurable_id : Measurable
      (id : Matrix n n ℂ → Matrix n n ℂ)).const_smul (γ / √(Fintype.card n : ℝ)))))
  have hE := measureReal_le_liminf_le (complexGaussianMatrix n n) f hf
    (by positivity) hb (fun j => lintegral_normalized_area_le M hk hγ (he j) hR)
  change μ.real {ω | ENNReal.ofReal b ≤ liminf (fun j => f j (G ω)) atTop} ≤ _
  rw [hG.measureReal_eq (p := fun X => ENNReal.ofReal b ≤ liminf (fun j => f j X) atTop)
    (measurableSet_le measurable_const (Measurable.liminf hf))]
  exact hE

private theorem measureReal_norm_lt_and_not_exists_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {γ R B : ℝ}
    (hγ : 0 < γ) (hR : 0 ≤ R) (hB : 0 < B) :
    μ.real {ω | specNorm (M + (γ / √(Fintype.card n : ℝ)) • G ω) < R ∧
      ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
        (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ B} ≤
      4 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * R ^ 2 / (γ ^ 2 * B ^ 2) := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  have hn : (0 : ℝ) < Fintype.card n := by
    exact_mod_cast (show 0 < Fintype.card n by omega)
  have hc : 0 < γ / √(Fintype.card n : ℝ) := by positivity
  have hs : ∀ᵐ ω ∂μ, (M + (γ / √(Fintype.card n : ℝ)) • G ω).charpoly.Separable := by
    have hh := ae_charpoly_separable_of_hasLaw_complexGaussianMatrix hG M
      (Complex.ofReal_ne_zero.mpr hc.ne')
    filter_upwards [hh] with ω hω
    have heq : M + (↑(γ / √(Fintype.card n : ℝ)) : ℂ) • G ω =
        M + (γ / √(Fintype.card n : ℝ)) • G ω := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [← heq]
    exact hω
  let e : ℕ → ℝ := fun j => 1 / (j + 1)
  have he (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsub : {ω | specNorm (M + (γ / √(Fintype.card n : ℝ)) • G ω) < R ∧
      ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
        (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ B} ≤ᵐ[μ]
      {ω | ENNReal.ofReal (B ^ 2 / Fintype.card n) ≤ liminf (fun j =>
        ENNReal.ofReal (4 / (Real.pi * e j ^ 2)) * volume
          ({z : ℂ | singularValues
            (z • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ e j} ∩
              Metric.ball 0 R)) atTop} := by
    filter_upwards [hs] with ω hω hbad
    exact ofReal_sq_div_card_le_liminf_measure_inter_ball_of_not_exists
      hω hbad.1 hB hbad.2 hk he he0
  refine (measureReal_mono_ae hsub).trans
    ((measureReal_le_liminf_normalized_area_le hG M hk hγ hR
      (b := B ^ 2 / Fintype.card n) (by positivity) he).trans_eq ?_)
  field_simp


omit [DecidableEq n] in
private theorem measureReal_specNorm_add_ge_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {γ u : ℝ} (hγ : 0 < γ) (hu : 0 ≤ u) :
    μ.real {ω | specNorm M + γ * (2 * √2 + u / √(Fintype.card n : ℝ)) ≤
      specNorm (M + (γ / √(Fintype.card n : ℝ)) • G ω)} ≤ Real.exp (-u ^ 2) := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  have hn : (0 : ℝ) < Fintype.card n := by
    exact_mod_cast (show 0 < Fintype.card n by omega)
  have hc : 0 < γ / √(Fintype.card n : ℝ) := by positivity
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix hG hu)
  change √2 * (√(Fintype.card n : ℝ) + √(Fintype.card n : ℝ)) + u ≤ specNorm (G ω)
  simp only [Set.mem_ofPred_eq] at hω
  have hupper := specNorm_add_le M ((γ / √(Fintype.card n : ℝ)) • G ω)
  rw [specNorm_real_smul, abs_of_pos hc] at hupper
  have heq : γ * (2 * √2 + u / √(Fintype.card n : ℝ)) =
      (γ / √(Fintype.card n : ℝ)) *
        (√2 * (√(Fintype.card n : ℝ) + √(Fintype.card n : ℝ)) + u) := by
    field_simp
    ring
  rw [heq] at hω
  exact (mul_le_mul_iff_right₀ hc).1 (by linarith :
    (γ / √(Fintype.card n : ℝ)) *
      (√2 * (√(Fintype.card n : ℝ) + √(Fintype.card n : ℝ)) + u) ≤
      (γ / √(Fintype.card n : ℝ)) * specNorm (G ω))


private theorem measureReal_not_exists_le_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {γ B u : ℝ}
    (hγ : 0 < γ) (hB : 0 < B) (hu : 0 ≤ u) :
    μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
      (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ B} ≤
      4 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 *
        (specNorm M + γ * (2 * √2 + u / √(Fintype.card n : ℝ))) ^ 2 /
          (γ ^ 2 * B ^ 2) + Real.exp (-u ^ 2) := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  let R := specNorm M + γ * (2 * √2 + u / √(Fintype.card n : ℝ))
  let X (ω : Ω) := M + (γ / √(Fintype.card n : ℝ)) • G ω
  let E := {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
    X ω * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B}
  have hsub : E ⊆ {ω | specNorm (X ω) < R ∧ ω ∈ E} ∪
      {ω | R ≤ specNorm (X ω)} := by
    intro ω hω
    by_cases h : specNorm (X ω) < R
    · exact Or.inl ⟨h, hω⟩
    · exact Or.inr (le_of_not_gt h)
  calc μ.real E ≤ μ.real ({ω | specNorm (X ω) < R ∧ ω ∈ E} ∪
        {ω | R ≤ specNorm (X ω)}) := measureReal_mono hsub
    _ ≤ μ.real {ω | specNorm (X ω) < R ∧ ω ∈ E} +
        μ.real {ω | R ≤ specNorm (X ω)} := measureReal_union_le _ _
    _ ≤ _ := add_le_add (measureReal_norm_lt_and_not_exists_le hG M hk hγ
      (by dsimp [R]; positivity) hB) (measureReal_specNorm_add_ge_le hG M hk hγ hu)

private theorem sqrt_cutoff_le {N m L : ℝ} (hN : 1 ≤ N) (hm : 2 ≤ m) (hL : 0 ≤ L) :
    m + 2 * √2 + √(2 * L) / √N ≤ 3 * (m + L) := by
  have hNs : 1 ≤ √N := Real.one_le_sqrt.mpr hN
  have hNp : 0 < √N := by linarith
  have hu : √(2 * L) ≤ L + 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hud : √(2 * L) / √N ≤ √(2 * L) := by
    rw [div_le_iff₀ hNp]
    exact le_mul_of_one_le_right (by positivity) hNs
  have htwo : 2 * √2 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  linarith

/-- **Polynomial eigenvector-conditioning tail for a Ginibre perturbation.** For independent
standard complex Gaussian entries, $0<2\gamma\le\|\mathbf{M}\|_2$ and $0<t\le1$, the failure
to admit a diagonalizer of condition at most $1/t$ has probability at most
$128e n^3 t^2(\|\mathbf{M}\|_2/\gamma+\log(1/t))^2$.
[BanksKulkarniMukherjeeSrivastava2021, Theorem 1.5], with the local area inequality and a
norm cutoff giving an elementary polynomial-tail form. -/
theorem measureReal_not_exists_pseudoConditionNumber_le_le_log_sq_of_hasLaw_complexGaussianMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {γ t : ℝ} (hγ : 0 < γ) (hγM : 2 * γ ≤ specNorm M) (ht : 0 < t) (ht1 : t ≤ 1) :
    μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
      (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ t⁻¹} ≤
      (128 * Real.exp 1) * (Fintype.card n : ℝ) ^ 3 * t ^ 2 *
        (specNorm M / γ + Real.log t⁻¹) ^ 2 := by
  have hn : 0 < Fintype.card n := by
    by_contra h
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp (by omega)
    have hM : M = 0 := Subsingleton.elim _ _
    simp only [hM, specNorm_zero] at hγM
    linarith
  have hn1 : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < Fintype.card n := by positivity
  have hk : Fintype.card n - 1 + 1 = Fintype.card n := by omega
  let L := Real.log t⁻¹
  let K := specNorm M / γ + L
  let u := √(2 * L)
  let R := specNorm M + γ * (2 * √2 + u / √(Fintype.card n : ℝ))
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ ht).2 ht1)
  have hm : 2 ≤ specNorm M / γ := (le_div_iff₀ hγ).2 hγM
  have hK : 2 ≤ K := by dsimp [K]; linarith
  have hR : 0 ≤ R := by dsimp [R, u]; positivity
  have hRupper : R ≤ 3 * γ * K := by
    have hh := sqrt_cutoff_le hn1 hm hL
    have heq : R = γ * (specNorm M / γ + 2 * √2 + √(2 * L) / √(Fintype.card n : ℝ)) := by
      dsimp [R, u]
      field_simp
      ring
    rw [heq]
    dsimp [K]
    nlinarith [mul_le_mul_of_nonneg_left hh hγ.le]
  have hexp : Real.exp (-u ^ 2) = t ^ 2 := by
    have hlog : -u ^ 2 = Real.log (t ^ 2) := by
      dsimp [u, L]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log t⁻¹), Real.log_pow, Real.log_inv]
      ring
    rw [hlog, Real.exp_log (by positivity)]
  have htail := measureReal_not_exists_le_cutoff hG M hk hγ (inv_pos.mpr ht)
    (Real.sqrt_nonneg (2 * L))
  rw [hexp] at htail
  calc
    _ ≤ 4 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * R ^ 2 /
        (γ ^ 2 * (t⁻¹) ^ 2) + t ^ 2 := htail
    _ ≤ 4 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * (3 * γ * K) ^ 2 /
        (γ ^ 2 * (t⁻¹) ^ 2) + t ^ 2 := by gcongr
    _ = 36 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * t ^ 2 * K ^ 2 + t ^ 2 := by
      field_simp
      ring
    _ ≤ _ := by
      have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
      have hn3 : (1 : ℝ) ≤ (Fintype.card n : ℝ) ^ 3 := one_le_pow₀ hn1
      have hK2 : (1 : ℝ) ≤ K ^ 2 := by nlinarith
      have hprod : 1 ≤ Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * K ^ 2 :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he1 hn3) hK2
      have hh := mul_le_mul_of_nonneg_right hprod (sq_nonneg t)
      change _ ≤ (128 * Real.exp 1) * (Fintype.card n : ℝ) ^ 3 * t ^ 2 * K ^ 2
      nlinarith

/-- **Polynomial eigenvector-conditioning tail.** An
$O(n^3 t^2(\|\mathbf{M}\|_2/\gamma+\log(1/t))^2)$ tail suffices for independent
standard complex Gaussian entries, $0<2\gamma\le\|\mathbf{M}\|_2$ and $0<t\le1$.
The constants are absolute.
[BanksKulkarniMukherjeeSrivastava2021, Theorem 1.5], via the pseudospectral area argument. -/
theorem
  exists_forall_measureReal_not_exists_pseudoConditionNumber_le_le_of_hasLaw_complexGaussianMatrix :
    ∃ (C a b c : ℝ), 0 < b ∧ ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
      {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
      HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
      0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ 1 →
      μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
        (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ t⁻¹} ≤
        C * (Fintype.card n : ℝ) ^ a * t ^ b * (specNorm M / γ + Real.log t⁻¹) ^ c := by
  refine ⟨128 * Real.exp 1, 3, 2, 2, by norm_num, ?_⟩
  intro Ω _mΩ μ n _ _ G hG M γ t hγ hγM ht ht1
  simpa only [Real.rpow_ofNat] using
    measureReal_not_exists_pseudoConditionNumber_le_le_log_sq_of_hasLaw_complexGaussianMatrix
      hG M hγ hγM ht ht1

private theorem measureReal_exists_mem_singularValues_le_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 2 = Fintype.card n) {γ x : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x)
    (Z : Finset ℂ) :
    μ.real {ω | ∃ y ∈ Z,
      singularValues (y • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ x} ≤
      (Z.card : ℝ) * (Fintype.card n : ℝ) ^ 5 * (x / γ) ^ 4 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  have heq : {ω | ∃ y ∈ Z,
      singularValues (y • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ x} =
      ⋃ y : Z, {ω | singularValues ((y : ℂ) • 1 -
        (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ x} := by
    ext ω
    simp
  rw [heq]
  calc
    _ ≤ ∑ y : Z, μ.real {ω | singularValues ((y : ℂ) • 1 -
        (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ x} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _y : Z, (Fintype.card n : ℝ) ^ 5 * (x / γ) ^ 4 := by
      apply Finset.sum_le_sum
      intro y _
      have he (ω : Ω) : (y : ℂ) • (1 : Matrix n n ℂ) -
          (M + (γ / √(Fintype.card n : ℝ)) • G ω) =
          -(M - (y : ℂ) • 1 + (γ / √(Fintype.card n : ℝ)) • G ω) := by abel
      simp_rw [he, singularValues_neg]
      exact measureReal_singularValues_add_smul_le_le_pow_four_of_hasLaw_complexGaussianMatrix
        hG _ hk hγ hx
    _ = _ := by simp [mul_assoc]

private theorem measureReal_gap_le_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 2 = Fintype.card n) {γ r R B : ℝ}
    (hγ : 0 < γ) (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) (hB : 0 < B) :
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → r < ‖d i - d j‖} ≤
      μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
        (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ B} +
      μ.real {ω | R ≤ specNorm (M + (γ / √(Fintype.card n : ℝ)) • G ω)} +
      (36 * R ^ 2 / r ^ 2) * (Fintype.card n : ℝ) ^ 5 * (2 * r * B / γ) ^ 4 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  obtain ⟨Z, hcard, hZ⟩ := exists_finset_card_mul_sq_le_and_forall_norm_sub_le 0 hR hr hrR
  simp only [sub_zero] at hZ
  let S := {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
    (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
      pseudoConditionNumber V ≤ B}
  let T := {ω | R ≤ specNorm (M + (γ / √(Fintype.card n : ℝ)) • G ω)}
  let U := {ω | ∃ y ∈ Z, singularValues (y • 1 -
    (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ 2 * r * B}
  have hsub : {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → r < ‖d i - d j‖} ⊆ (S ∪ T) ∪ U := by
    intro ω hω
    by_cases hS : ω ∈ S
    · exact Or.inl (Or.inl hS)
    by_cases hT : ω ∈ T
    · exact Or.inl (Or.inr hT)
    right
    obtain ⟨V, d, hV, hAV, hVB⟩ := not_not.mp hS
    exact exists_mem_singularValues_le_of_not_exists_isEigenvalueListing hV hAV hk hr
      (lt_of_not_ge hT) hVB Z hZ hω
  have hcount : (Z.card : ℝ) ≤ 36 * R ^ 2 / r ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hr)).2 hcard
  calc
    _ ≤ μ.real ((S ∪ T) ∪ U) := measureReal_mono hsub
    _ ≤ μ.real (S ∪ T) + μ.real U := measureReal_union_le _ _
    _ ≤ μ.real S + μ.real T + μ.real U := by
      exact add_le_add (measureReal_union_le S T) le_rfl
    _ ≤ μ.real S + μ.real T +
        (Z.card : ℝ) * (Fintype.card n : ℝ) ^ 5 * (2 * r * B / γ) ^ 4 := by
      exact add_le_add le_rfl
        (measureReal_exists_mem_singularValues_le_le hG M hk hγ (x := 2 * r * B)
          (by positivity) Z)
    _ ≤ _ := by gcongr

private theorem gap_tail_combine {N K τ R γ q : ℝ}
    (hN : 1 ≤ N) (hK : 2 ≤ K) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hγ : 0 < γ) (hR : 0 ≤ R) (hRupper : R ≤ 3 * γ * K)
    (hq : 0 < q) (hq4 : q ^ 4 = τ) :
    128 * Real.exp 1 * N ^ 3 * √τ * K ^ 2 + τ ^ 2 +
        (36 * R ^ 2 / (γ * τ) ^ 2) * N ^ 5 * (2 * (γ * τ) * q⁻¹ / γ) ^ 4 ≤
      (10000 * Real.exp 1) * N ^ 5 * √τ * K ^ 2 := by
  have hτsqrt : τ ≤ √τ := Real.le_sqrt_self_iff.mpr hτ1
  have hτ2 : τ ^ 2 ≤ √τ := (by nlinarith : τ ^ 2 ≤ τ).trans hτsqrt
  have hnet : (36 * R ^ 2 / (γ * τ) ^ 2) * N ^ 5 *
      (2 * (γ * τ) * q⁻¹ / γ) ^ 4 = 576 * N ^ 5 * (R / γ) ^ 2 * τ := by
    field_simp
    rw [hq4]
    ring
  rw [hnet]
  have hRdiv : R / γ ≤ 3 * K := by
    rw [div_le_iff₀ hγ]
    nlinarith
  have hRdiv0 : 0 ≤ R / γ := by positivity
  have hnetle : 576 * N ^ 5 * (R / γ) ^ 2 * τ ≤ 5184 * N ^ 5 * √τ * K ^ 2 := by
    calc
      _ ≤ 576 * N ^ 5 * (3 * K) ^ 2 * √τ := by gcongr
      _ = _ := by ring
  have hn35 : N ^ 3 ≤ N ^ 5 := pow_le_pow_right₀ hN (by norm_num)
  have hκ : 128 * Real.exp 1 * N ^ 3 * √τ * K ^ 2 ≤
      128 * Real.exp 1 * N ^ 5 * √τ * K ^ 2 := by gcongr
  have hNK : 1 ≤ N ^ 5 * K ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (by nlinarith)
  have hrest : τ ^ 2 ≤ N ^ 5 * √τ * K ^ 2 := by
    calc
      _ ≤ √τ := hτ2
      _ ≤ (N ^ 5 * K ^ 2) * √τ := le_mul_of_one_le_left (by positivity) hNK
      _ = _ := by ring
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hprod : 0 ≤ N ^ 5 * √τ * K ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right he hprod]

private theorem measureReal_gap_le_log_sq_of_card_eq_add_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 2 = Fintype.card n) {γ r : ℝ}
    (hγ : 0 < γ) (hγM : 2 * γ ≤ specNorm M) (hr : 0 < r) (hrγ : r ≤ γ) :
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → r < ‖d i - d j‖} ≤
      (10000 * Real.exp 1) * (Fintype.card n : ℝ) ^ 5 * √(r / γ) *
        (specNorm M / γ + Real.log (r / γ)⁻¹) ^ 2 := by
  let τ := r / γ
  let q := √(√τ)
  let L := Real.log τ⁻¹
  let K := specNorm M / γ + L
  let u := √(2 * L)
  let R := specNorm M + γ * (2 * √2 + u / √(Fintype.card n : ℝ))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := (div_le_one hγ).2 hrγ
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr hτ1)
  have hτq : τ ≤ q := (Real.le_sqrt_self_iff.mpr hτ1).trans
    (Real.le_sqrt_self_iff.mpr (Real.sqrt_le_one.mpr hτ1))
  have hq2 : q ^ 2 = √τ := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hq4 : q ^ 4 = τ := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hq2, Real.sq_sqrt hτ.le]
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hτ).2 hτ1)
  have hm : 2 ≤ specNorm M / γ := (le_div_iff₀ hγ).2 hγM
  have hK : 2 ≤ K := by dsimp [K]; linarith
  have hn : (1 : ℝ) ≤ Fintype.card n := by
    exact_mod_cast (show 1 ≤ Fintype.card n by omega)
  have hR : 0 < R := by dsimp [R, u]; positivity
  have hRupper : R ≤ 3 * γ * K := by
    have hh := mul_le_mul_of_nonneg_left (sqrt_cutoff_le hn hm hL) hγ.le
    have heq : R = γ * (specNorm M / γ + 2 * √2 + √(2 * L) / √(Fintype.card n : ℝ)) := by
      dsimp [R, u]
      field_simp
      ring
    rw [heq]
    dsimp [K]
    nlinarith
  have hlog : Real.log q⁻¹ ≤ L :=
    Real.log_le_log (inv_pos.mpr hq) ((inv_le_inv₀ hq hτ).2 hτq)
  have hκ :=
    measureReal_not_exists_pseudoConditionNumber_le_le_log_sq_of_hasLaw_complexGaussianMatrix
    hG M hγ hγM hq hq1
  have hκbound : 128 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * q ^ 2 *
      (specNorm M / γ + Real.log q⁻¹) ^ 2 ≤
      128 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * √τ * K ^ 2 := by
    rw [hq2]
    have hlog0 : 0 ≤ Real.log q⁻¹ := Real.log_nonneg ((one_le_inv₀ hq).2 hq1)
    dsimp [K]
    gcongr
  have hκupper := hκ.trans hκbound
  have hexp : Real.exp (-u ^ 2) = τ ^ 2 := by
    have hh : -u ^ 2 = Real.log (τ ^ 2) := by
      dsimp [u, L]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log τ⁻¹), Real.log_pow, Real.log_inv]
      ring
    rw [hh, Real.exp_log (by positivity)]
  have hnorm := measureReal_specNorm_add_ge_le hG M (k := k + 1) (by omega) hγ
    (Real.sqrt_nonneg (2 * L))
  rw [hexp] at hnorm
  have hrR : r ≤ R := by
    calc
      r ≤ γ := hrγ
      _ ≤ specNorm M := by linarith
      _ ≤ R := le_add_of_nonneg_right (by dsimp [u]; positivity)
  have hgap := measureReal_gap_le_cutoff hG M hk hγ hr hR hrR (inv_pos.mpr hq)
  have hrτ : r = γ * τ := by dsimp [τ]; field_simp
  refine (hgap.trans (add_le_add (add_le_add hκupper hnorm) le_rfl)).trans ?_
  change _ ≤ (10000 * Real.exp 1) * (Fintype.card n : ℝ) ^ 5 * √τ * K ^ 2
  conv_lhs => rw [hrτ]
  exact gap_tail_combine hn hK hτ hτ1 hγ hR.le hRupper hq hq4

/-- **Polynomial eigenvalue-gap tail for a Ginibre perturbation.** For independent standard
complex Gaussian entries, $0<2\gamma\le\|\mathbf{M}\|_2$ and $0<t\le\gamma$, the failure to
admit an eigenvalue listing with all distinct-index gaps exceeding $t$ has probability at most
$10000e n^5\sqrt{t/\gamma}(\|\mathbf{M}\|_2/\gamma+\log(\gamma/t))^2$.
[BanksGarzaVargasKulkarniSrivastava2023, Theorem 3.6], with an elementary polynomial tail
obtained from the second-singular-value estimate and eigenvector conditioning. -/
theorem measureReal_not_exists_isEigenvalueListing_le_le_log_sq_of_hasLaw_complexGaussianMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {γ t : ℝ} (hγ : 0 < γ) (hγM : 2 * γ ≤ specNorm M) (ht : 0 < t) (htγ : t ≤ γ) :
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
      (10000 * Real.exp 1) * (Fintype.card n : ℝ) ^ 5 * √(t / γ) *
        (specNorm M / γ + Real.log (γ / t)) ^ 2 := by
  by_cases hn : 2 ≤ Fintype.card n
  · simpa only [inv_div] using measureReal_gap_le_log_sq_of_card_eq_add_two
      hG M (k := Fintype.card n - 2) (by omega) hγ hγM ht htγ
  · have hnle : Fintype.card n ≤ 1 := by omega
    have : Subsingleton n := ⟨Fintype.card_le_one_iff.mp hnle⟩
    have he : {ω | ¬ ∃ d : n → ℂ,
        IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
          ∀ i j, i ≠ j → t < ‖d i - d j‖} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω hω
      obtain ⟨d, hd⟩ := exists_isEigenvalueListing
        (M + (γ / √(Fintype.card n : ℝ)) • G ω)
      exact hω ⟨d, hd, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩
    rw [he, measureReal_empty]
    positivity

/-- **Polynomial eigenvalue-gap tail.** An
$O(n^5(t/\gamma)^{1/2}(\|\mathbf{M}\|_2/\gamma+\log(\gamma/t))^2)$ tail suffices for independent
standard complex Gaussian entries, $0<2\gamma\le\|\mathbf{M}\|_2$ and $0<t\le\gamma$.
The constants are absolute. [BanksGarzaVargasKulkarniSrivastava2023, Theorem 3.6], via a disk net
and the conditioning tail. -/
theorem
  exists_forall_measureReal_not_exists_isEigenvalueListing_le_of_hasLaw_complexGaussianMatrix :
    ∃ (C a b c : ℝ), 0 < b ∧ ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
      {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
      HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
      0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ γ →
      μ.real {ω | ¬ ∃ d : n → ℂ,
        IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
          ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
        C * (Fintype.card n : ℝ) ^ a * (t / γ) ^ b *
          (specNorm M / γ + Real.log (γ / t)) ^ c := by
  refine ⟨10000 * Real.exp 1, 5, 1 / 2, 2, by norm_num, ?_⟩
  intro Ω _mΩ μ n _ _ G hG M γ t hγ hγM ht htγ
  simpa only [Real.rpow_ofNat, Real.sqrt_eq_rpow] using
    measureReal_not_exists_isEigenvalueListing_le_le_log_sq_of_hasLaw_complexGaussianMatrix
      hG M hγ hγM ht htγ

end NLAlib
