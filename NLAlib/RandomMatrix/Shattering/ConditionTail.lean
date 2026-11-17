/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex.LeastSingularValue
public import NLAlib.RandomMatrix.Gaussian.Complex.SimpleSpectrum
public import NLAlib.Matrix.Perturbation.PseudospectralArea
public import NLAlib.ForMathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Eigenvector condition of a Ginibre perturbation

For a deterministic complex matrix $\mathbf{M}$ of order $n$, $\gamma > 0$ and a standard
complex Gaussian matrix $\mathbf{G}$ (independent entries of mean square modulus one), the
perturbation $\mathbf{M} + \gamma n^{-1/2}\mathbf{G}$ is diagonalizable by an eigenvector matrix
of condition number at most $1/t$ except with probability
$128e\,n^3t^2(\|\mathbf{M}\|_2/\gamma + \log(1/t))^2$: the eigenvector half of pseudospectral
shattering [BanksKulkarniMukherjeeSrivastava2021, Theorem 1.5].

The proof integrates the area of the $\varepsilon$-pseudospectrum inside a disk over the Gaussian
law (Fubini and the shifted least-singular-value tail), and bounds the expected liminf of the
normalized areas by Fatou. On the norm cutoff event, failure to admit a diagonalizer of condition
at most $B$ lies almost surely in a superlevel set of that liminf
(`NLAlib.ofReal_sq_div_card_le_liminf_measure_inter_ball_of_not_exists`, the local area
inequality near simple eigenvalues), so Markov's inequality applies without selecting
eigenvectors measurably.

## Main results

* `measureReal_not_exists_pseudoConditionNumber_le_le_log_sq_of_hasLaw_complexGaussianMatrix`:
  the condition tail with constants $(128e, 3, 2, 2)$.
* Its asymptotic form:
  `exists_forall_measureReal_not_exists_pseudoConditionNumber_le_le_of_hasLaw_complexGaussianMatrix`
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



private theorem measureReal_not_exists_le_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {γ B R : ℝ}
    (hγ : 0 < γ) (hB : 0 < B) (hR : 0 ≤ R) :
    μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
      (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ B} ≤
      4 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * R ^ 2 / (γ ^ 2 * B ^ 2) +
        μ.real {ω | R ≤ specNorm (M + (γ / √(Fintype.card n : ℝ)) • G ω)} := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
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
    _ ≤ _ := add_le_add (measureReal_norm_lt_and_not_exists_le hG M hk hγ hR hB) le_rfl

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
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ ht).2 ht1)
  have hm : 2 ≤ specNorm M / γ := (le_div_iff₀ hγ).2 hγM
  have hK : 2 ≤ K := by dsimp [K]; linarith
  have hR : 0 ≤ 3 * γ * K := mul_nonneg (by positivity) (by linarith)
  have htail := (measureReal_not_exists_le_cutoff hG M hk hγ (inv_pos.mpr ht) hR).trans
    (add_le_add le_rfl
      (measureReal_specNorm_add_smul_ge_mul_le_of_hasLaw_complexGaussianMatrix hG M hγ hγM ht
        ht1))
  calc
    _ ≤ 4 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * (3 * γ * K) ^ 2 /
        (γ ^ 2 * (t⁻¹) ^ 2) + t ^ 2 := htail
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

end NLAlib
