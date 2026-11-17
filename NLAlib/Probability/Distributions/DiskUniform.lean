/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Probability.ConditionalProbability

/-!
# The uniform law on a disk

The uniform law on the closed disk $\mathbb{D}(c, R) \subset \mathbb{C}$ is Lebesgue measure
conditioned on the disk. A sample lands in a disk of radius $\eta$ with probability
at most $(\eta / R)^2$ (`NLAlib.measureReal_diskUniform_closedBall_le`). Two consequences, the
probabilistic part of a random regularization of shifts such as that of
[BanksGarzaVargasSrivastava2022, Lemma 3.10, Lemma 5.3]:

* $k$ independent perturbations $r_i + w_i$, $w_i \sim \mathrm{Unif}(\mathbb{D}(0, R))$, of
  arbitrary centres avoid the $\eta$-neighbourhood of a finite set $\Lambda$ whose points are
  $2(\eta + R)$-separated, except with probability $k(\eta / R)^2$
  (`NLAlib.measureReal_exists_norm_add_sub_lt_le`);
* one common translate $w \sim \mathrm{Unif}(\mathbb{D}(0, R))$ of a $0.99R$-separated finite net
  $S$ keeps every point of $S + w$ at distance at least $\eta \le 0.14R$ from a finite set
  $\Lambda$, except with probability $11\lvert\Lambda\rvert(\eta / R)^2$
  (`NLAlib.measureReal_exists_norm_add_sub_lt_le_of_separated`). For a point
  $\lambda$, only net points in $\mathbb{D}(\lambda, R + \eta)$ can come within $\eta$, and a
  packing count bounds them by $11$; the sharp count for a separated set is $7$ (attained, Pirl's
  packing theorem), not the paper's "at most three".

## Main definitions

* `NLAlib.diskUniform`: the uniform law on a closed disk.
* `NLAlib.polarDisk`: the polar sampler, uniform on the disk by
  `NLAlib.map_polarDisk_eq_diskUniform`.

## Main results

* `NLAlib.measureReal_diskUniform_closedBall_le`: the mass of a small disk.
* `NLAlib.measureReal_exists_norm_add_sub_lt_le`: independent perturbations avoid a separated set.
* `NLAlib.measureReal_exists_norm_add_sub_lt_le_of_separated`: a translated separated net avoids
  a finite set.
* `NLAlib.map_polarDisk_eq_diskUniform`: the polar sampler is uniform on the disk.
* `NLAlib.measureReal_polarDisk_bad_le`: one polar sample keeps several centres away from a
  separated set.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib

/-- The **uniform law on the closed disk** $\mathbb{D}(c, R)$: Lebesgue measure on $\mathbb{C}$
conditioned on the disk (Mathlib's `ProbabilityTheory.cond`), i.e. restricted to the disk and
divided by its area $\pi R^2$. -/
noncomputable abbrev diskUniform (c : ℂ) (R : ℝ) : Measure ℂ :=
  ProbabilityTheory.cond volume (Metric.closedBall c R)

/-- The uniform law on a disk of positive radius is a probability measure. -/
theorem isProbabilityMeasure_diskUniform (c : ℂ) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (diskUniform c R) := by
  unfold diskUniform
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (Metric.measure_closedBall_pos volume c hR).ne' measure_closedBall_lt_top.ne

/-- **A disk sample lands in a small disk with probability at most the area ratio**:
$\mathbb{P}[w \in \mathbb{D}(z, \eta)] \le (\eta / R)^2$ for $w \sim \mathrm{Unif}(\mathbb{D}(c,
R))$, $\eta \ge 0$, $R > 0$. [BanksGarzaVargasSrivastava2022, proof of Lemma 3.10]. -/
theorem measureReal_diskUniform_closedBall_le (c z : ℂ) {R η : ℝ} (hR : 0 < R) (hη : 0 ≤ η) :
    (diskUniform c R).real (Metric.closedBall z η) ≤ (η / R) ^ 2 := by
  unfold diskUniform
  have h2 : Module.finrank ℝ ℂ = 2 := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI]; simp
  have hI : volume (Metric.closedBall c R ∩ Metric.closedBall z η) ≤
      volume (Metric.closedBall z η) := measure_mono Set.inter_subset_right
  rw [Measure.addHaar_closedBall' volume z hη, h2] at hI
  rw [measureReal_def, ProbabilityTheory.cond_apply measurableSet_closedBall,
    Measure.addHaar_closedBall' volume c hR.le, h2]
  have hP0 : volume (Metric.closedBall (0 : ℂ) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hPt : volume (Metric.closedBall (0 : ℂ) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  calc (ENNReal.ofReal (R ^ 2) * volume (Metric.closedBall (0 : ℂ) 1))⁻¹ *
        volume (Metric.closedBall c R ∩ Metric.closedBall z η)
      ≤ (ENNReal.ofReal (R ^ 2) * volume (Metric.closedBall (0 : ℂ) 1))⁻¹ *
          (ENNReal.ofReal (η ^ 2) * volume (Metric.closedBall (0 : ℂ) 1)) := by
        gcongr
    _ = ENNReal.ofReal ((η / R) ^ 2) := by
        rw [← ENNReal.div_eq_inv_mul, ENNReal.mul_div_mul_right _ _ hP0 hPt,
          div_pow, ENNReal.ofReal_div_of_pos (pow_pos hR 2)]

/-- A set whose trace on the disk lies in a small closed ball has small uniform mass. -/
private theorem diskUniform_real_le_of_inter {c z : ℂ} {R η : ℝ} (hR : 0 < R) (hη : 0 ≤ η)
    {S : Set ℂ} (hS : Metric.closedBall c R ∩ S ⊆ Metric.closedBall z η) :
    (diskUniform c R).real S ≤ (η / R) ^ 2 := by
  have h2 : Module.finrank ℝ ℂ = 2 := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI]; simp
  have hI : volume (Metric.closedBall c R ∩ S) ≤ volume (Metric.closedBall z η) :=
    measure_mono hS
  rw [Measure.addHaar_closedBall' volume z hη, h2] at hI
  rw [measureReal_def, ProbabilityTheory.cond_apply measurableSet_closedBall,
    Measure.addHaar_closedBall' volume c hR.le, h2]
  have hP0 : volume (Metric.closedBall (0 : ℂ) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hPt : volume (Metric.closedBall (0 : ℂ) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  calc (ENNReal.ofReal (R ^ 2) * volume (Metric.closedBall (0 : ℂ) 1))⁻¹ *
        volume (Metric.closedBall c R ∩ S)
      ≤ (ENNReal.ofReal (R ^ 2) * volume (Metric.closedBall (0 : ℂ) 1))⁻¹ *
          (ENNReal.ofReal (η ^ 2) * volume (Metric.closedBall (0 : ℂ) 1)) := by
        gcongr
    _ = ENNReal.ofReal ((η / R) ^ 2) := by
        rw [← ENNReal.div_eq_inv_mul, ENNReal.mul_div_mul_right _ _ hP0 hPt,
          div_pow, ENNReal.ofReal_div_of_pos (pow_pos hR 2)]

/-- **Independent disk perturbations avoid a separated finite set** (shift regularization,
[BanksGarzaVargasSrivastava2022, Lemma 3.10]): for independent $w_i \sim
\mathrm{Unif}(\mathbb{D}(0, R))$, $i < k$ (the product law), arbitrary centres $r_i$ and a finite
set $\Lambda$ whose distinct points are at distance at least $2(\eta + R)$,
$\mathbb{P}[\exists i,\ \exists \lambda \in \Lambda,\ \lvert r_i + w_i - \lambda\rvert < \eta] \le
k(\eta / R)^2$. The paper also assumes $\eta \le R$, which is not needed. -/
theorem measureReal_exists_norm_add_sub_lt_le {k : ℕ} (r : Fin k → ℂ) (Λ : Finset ℂ)
    {R η : ℝ} (hR : 0 < R) (hη : 0 ≤ η)
    (hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → 2 * (η + R) ≤ ‖a - b‖) :
    (Measure.pi fun _ : Fin k => diskUniform 0 R).real
        {w | ∃ i, ∃ a ∈ Λ, ‖r i + w i - a‖ < η} ≤ k * (η / R) ^ 2 := by
  have hmarg : ∀ i : Fin k, (diskUniform 0 R).real {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η} ≤
      (η / R) ^ 2 := by
    intro i
    by_cases hne : ∃ x : ℂ, x ∈ Metric.closedBall (0 : ℂ) R ∧ ∃ a ∈ Λ, ‖r i + x - a‖ < η
    · obtain ⟨x0, hx0D, a0, ha0, hx0a0⟩ := hne
      refine diskUniform_real_le_of_inter (c := 0) (z := a0 - r i) hR hη ?_
      rintro x ⟨hxD, a, ha, hxa⟩
      by_cases hae : a = a0
      · subst hae
        rw [Metric.mem_closedBall, dist_eq_norm, show x - (a - r i) = r i + x - a by ring]
        exact hxa.le
      · exfalso
        have hsep := hΛ a ha a0 ha0 hae
        have hx : ‖x‖ ≤ R := by simpa using hxD
        have hx0 : ‖x0‖ ≤ R := by simpa using hx0D
        have key : a - a0 = -(r i + x - a) + (r i + x0 - a0) + (x - x0) := by ring
        have h1 : ‖a - a0‖ ≤ ‖-(r i + x - a)‖ + ‖r i + x0 - a0‖ + ‖x - x0‖ := by
          rw [key]
          linarith [norm_add_le (-(r i + x - a) + (r i + x0 - a0)) (x - x0),
            norm_add_le (-(r i + x - a)) (r i + x0 - a0)]
        have h2 : ‖x - x0‖ ≤ ‖x‖ + ‖x0‖ := norm_sub_le _ _
        rw [norm_neg] at h1
        linarith
    · refine diskUniform_real_le_of_inter (c := 0) (z := 0) hR hη ?_
      rintro x ⟨hxD, a, ha, hxa⟩
      exact absurd ⟨x, hxD, a, ha, hxa⟩ hne
  have hsub : {w : Fin k → ℂ | ∃ i, ∃ a ∈ Λ, ‖r i + w i - a‖ < η} =
      ⋃ i : Fin k, (fun w : Fin k → ℂ => w i) ⁻¹' {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η} := by
    ext w; simp
  have hmeas : ∀ i : Fin k, MeasurableSet {x : ℂ | ∃ a ∈ Λ, ‖r i + x - a‖ < η} := by
    intro i
    have hset : {x : ℂ | ∃ a ∈ Λ, ‖r i + x - a‖ < η} =
        ⋃ a ∈ Λ, {x : ℂ | ‖r i + x - a‖ < η} := by
      ext x; simp
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun a _ =>
      (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hpre : ∀ i : Fin k, (Measure.pi fun _ : Fin k => diskUniform 0 R).real
      ((fun w : Fin k → ℂ => w i) ⁻¹' {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η}) =
      (diskUniform 0 R).real {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η} := by
    intro i
    have : IsProbabilityMeasure (diskUniform 0 R) := isProbabilityMeasure_diskUniform 0 hR
    exact ((measurePreserving_eval (fun _ : Fin k => diskUniform 0 R) i).measureReal_preimage
      (hmeas i).nullMeasurableSet)
  rw [hsub]
  have hfin : ∀ i : Fin k, (Measure.pi fun _ : Fin k => diskUniform 0 R)
      ((fun w : Fin k → ℂ => w i) ⁻¹' {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η}) ≠ ⊤ :=
    fun _ => measure_ne_top _ _
  calc (Measure.pi fun _ : Fin k => diskUniform 0 R).real
        (⋃ i : Fin k, (fun w : Fin k → ℂ => w i) ⁻¹' {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η})
      = ((Measure.pi fun _ : Fin k => diskUniform 0 R)
          (⋃ i : Fin k, (fun w : Fin k → ℂ => w i) ⁻¹' {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η})).toReal :=
        measureReal_def _ _
    _ ≤ (∑ i : Fin k, (Measure.pi fun _ : Fin k => diskUniform 0 R)
          ((fun w : Fin k → ℂ => w i) ⁻¹' {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η})).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => hfin i)
          (measure_iUnion_fintype_le _ _)
    _ = ∑ i : Fin k, (Measure.pi fun _ : Fin k => diskUniform 0 R).real
          ((fun w : Fin k → ℂ => w i) ⁻¹' {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η}) := by
        rw [ENNReal.toReal_sum fun i _ => hfin i]
        rfl
    _ = ∑ i : Fin k, (diskUniform 0 R).real {x | ∃ a ∈ Λ, ‖r i + x - a‖ < η} :=
        Finset.sum_congr rfl fun i _ => hpre i
    _ ≤ ∑ _i : Fin k, (η / R) ^ 2 := Finset.sum_le_sum fun i _ => hmarg i
    _ = k * (η / R) ^ 2 := by simp

/-- Union bound for the real measure of a finite union. -/
private theorem measureReal_biUnion_finset_le_sum {ι : Type*} (μ : Measure ℂ) [IsFiniteMeasure μ]
    (I : Finset ι) (f : ι → Set ℂ) :
    μ.real (⋃ i ∈ I, f i) ≤ ∑ i ∈ I, μ.real (f i) := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum fun i _ => measure_ne_top μ (f i)]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => measure_ne_top μ (f i))
    (measure_biUnion_finset_le I f)

/-- A $0.99R$-separated set has at most $11$ points within $R + \eta$ of a centre (packing). -/
private theorem card_filter_le_eleven {S : Finset ℂ} {a : ℂ} {R η : ℝ} (hR : 0 < R)
    (hηR : η ≤ 0.14 * R)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 0.99 * R ≤ ‖s - t‖) :
    (S.filter fun s => ‖s - a‖ < R + η).card ≤ 11 := by
  classical
  set T := S.filter fun s => ‖s - a‖ < R + η with hT
  have hρ : (0 : ℝ) < 0.495 * R := by positivity
  have hdisj : (T : Set ℂ).PairwiseDisjoint fun s => Metric.ball s (0.495 * R) := by
    intro s hs t ht hst
    have hs' := (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).1
    have ht' := (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).1
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    linarith [hS s hs' t ht' hst]
  have hsub : ∀ s ∈ T, Metric.ball s (0.495 * R) ⊆ Metric.ball a (1.635 * R) := by
    intro s hs
    apply Metric.ball_subset_ball'
    rw [dist_eq_norm]
    have := (Finset.mem_filter.1 hs).2
    linarith
  have hvol := measure_biUnion_finset (μ := volume) hdisj (fun s _ => measurableSet_ball)
  have hle : volume (⋃ s ∈ T, Metric.ball s (0.495 * R)) ≤
      volume (Metric.ball a (1.635 * R)) :=
    measure_mono (Set.iUnion₂_subset fun s hs => hsub s hs)
  rw [hvol] at hle
  have h2 : Module.finrank ℝ ℂ = 2 := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI]; simp
  simp only [Measure.addHaar_ball volume _ hρ.le,
    Measure.addHaar_ball volume _ (by positivity : (0:ℝ) ≤ 1.635 * R), h2,
    Finset.sum_const, nsmul_eq_mul] at hle
  have hP0 : volume (Metric.ball (0 : ℂ) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hPt : volume (Metric.ball (0 : ℂ) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have h3 := (ENNReal.mul_le_mul_iff_left hP0 hPt).1 hle
  have h4 : (T.card : ℝ) * (0.495 * R) ^ 2 ≤ (1.635 * R) ^ 2 := by
    have h5 : ENNReal.ofReal ((T.card : ℝ) * (0.495 * R) ^ 2) ≤
        ENNReal.ofReal ((1.635 * R) ^ 2) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      exact h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h5
  have hn : (T.card : ℝ) ≤ 11 := by
    nlinarith [mul_pos hR hR]
  exact_mod_cast hn

/-- **A randomly translated separated net avoids a finite set** (the random translate of the
exceptional shifts, [BanksGarzaVargasSrivastava2022, Lemma 5.3]): for a finite set $S$ whose
distinct points are at distance at least $0.99R$, one translate $w \sim
\mathrm{Unif}(\mathbb{D}(0, R))$, a finite set $\Lambda$ and $0 \le \eta \le 0.14R$,
$\mathbb{P}[\exists s \in S,\ \exists \lambda \in \Lambda,\ \lvert s + w - \lambda\rvert < \eta]
\le
11\lvert\Lambda\rvert(\eta / R)^2$. -/
theorem measureReal_exists_norm_add_sub_lt_le_of_separated (S Λ : Finset ℂ) {R η : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η) (hηR : η ≤ 0.14 * R)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 0.99 * R ≤ ‖a - b‖) :
    (diskUniform 0 R).real {w | ∃ s ∈ S, ∃ a ∈ Λ, ‖s + w - a‖ < η} ≤
      11 * Λ.card * (η / R) ^ 2 := by
  classical
  have : IsProbabilityMeasure (diskUniform 0 R) := isProbabilityMeasure_diskUniform 0 hR
  have hV0 : volume (Metric.closedBall (0 : ℂ) R) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 hR).ne'
  have hVt : volume (Metric.closedBall (0 : ℂ) R) ≠ ⊤ :=
    (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
  -- monotonicity of the uniform law on the disk
  have hmono : ∀ {E U : Set ℂ}, Metric.closedBall (0 : ℂ) R ∩ E ⊆
      Metric.closedBall (0 : ℂ) R ∩ U → (diskUniform 0 R).real E ≤ (diskUniform 0 R).real U := by
    intro E U h
    have hIt : volume (Metric.closedBall (0 : ℂ) R ∩ U) ≠ ⊤ :=
      ne_top_of_le_ne_top hVt (measure_mono Set.inter_subset_left)
    unfold diskUniform
    simp only [measureReal_def, ProbabilityTheory.cond_apply measurableSet_closedBall]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hV0) hIt)
      (mul_le_mul_of_nonneg_left (measure_mono h) (zero_le))
  -- one ball bound
  have hball : ∀ s a : ℂ, (diskUniform 0 R).real {w | ‖s + w - a‖ < η} ≤ (η / R) ^ 2 := by
    intro s a
    refine le_trans (hmono (E := {w | ‖s + w - a‖ < η}) (U := Metric.closedBall (a - s) η)
      (Set.inter_subset_inter_right _ fun w hw => ?_))
      (measureReal_diskUniform_closedBall_le 0 (a - s) hR hη)
    rw [Metric.mem_closedBall, dist_eq_norm, show w - (a - s) = s + w - a by ring]
    exact hw.le
  set U : Set ℂ := ⋃ a ∈ Λ, ⋃ s ∈ S.filter (fun s => ‖s - a‖ < R + η), {w | ‖s + w - a‖ < η}
    with hU
  have hsub : Metric.closedBall (0 : ℂ) R ∩ {w | ∃ s ∈ S, ∃ a ∈ Λ, ‖s + w - a‖ < η} ⊆
      Metric.closedBall (0 : ℂ) R ∩ U := by
    rintro w ⟨hwD, s, hs, a, ha, hsa⟩
    refine ⟨hwD, ?_⟩
    have hw : ‖w‖ ≤ R := by simpa using hwD
    have htri : ‖s - a‖ ≤ ‖s + w - a‖ + ‖w‖ := by
      calc ‖s - a‖ = ‖(s + w - a) - w‖ := by ring_nf
        _ ≤ ‖s + w - a‖ + ‖w‖ := norm_sub_le _ _
    simp only [hU, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_filter]
    exact ⟨a, ha, s, ⟨hs, by linarith⟩, hsa⟩
  calc (diskUniform 0 R).real {w | ∃ s ∈ S, ∃ a ∈ Λ, ‖s + w - a‖ < η}
      ≤ (diskUniform 0 R).real U := hmono hsub
    _ ≤ ∑ a ∈ Λ, (diskUniform 0 R).real
          (⋃ s ∈ S.filter (fun s => ‖s - a‖ < R + η), {w | ‖s + w - a‖ < η}) :=
        measureReal_biUnion_finset_le_sum _ _ _
    _ ≤ ∑ a ∈ Λ, ∑ s ∈ S.filter (fun s => ‖s - a‖ < R + η),
          (diskUniform 0 R).real {w | ‖s + w - a‖ < η} :=
        Finset.sum_le_sum fun a _ => measureReal_biUnion_finset_le_sum _ _ _
    _ ≤ ∑ a ∈ Λ, ∑ _s ∈ S.filter (fun s => ‖s - a‖ < R + η), (η / R) ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun s _ => hball s a
    _ ≤ ∑ _a ∈ Λ, 11 * (η / R) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_filter_le_eleven hR hηR hS) (by positivity)
    _ = 11 * Λ.card * (η / R) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The polar sampler**: two draws $x_0, x_1 \in [0, 1]$ give the point
$c + R\sqrt{x_0}\,e^{2\pi i x_1}$ of the closed disk $\mathbb{D}(c, R)$. -/
noncomputable def polarDisk (c : ℂ) (R : ℝ) (x : Fin 2 → ℝ) : ℂ :=
  c + ((R * Real.sqrt (x 0) : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * x 1 : ℝ) : ℂ) * Complex.I)

section PolarSampler

open Set Real

/-- The polar coordinates $(R\sqrt{x_0}, 2\pi x_1 - \pi)$ of a point of the unit square. -/
private noncomputable def squarePolar (R : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (R * √x.1, 2 * π * x.2 - π)

/-- The derivative of `squarePolar`, a diagonal matrix. -/
private noncomputable def squarePolarDeriv (R : ℝ) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![R * (1 / (2 * √x.1)), 0; 0, 2 * π]).toContinuousLinearMap

/-- `squarePolar` has derivative `squarePolarDeriv` off $x_0 = 0$. -/
private theorem hasFDerivAt_squarePolar (R : ℝ) {x : ℝ × ℝ} (hx : x.1 ≠ 0) :
    HasFDerivAt (squarePolar R) (squarePolarDeriv R x) x := by
  unfold squarePolarDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert! HasFDerivAt.prodMk (𝕜 := ℝ)
    (((Real.hasDerivAt_sqrt hx).const_mul R).comp_hasFDerivAt x hasFDerivAt_fst)
    ((hasFDerivAt_snd.const_mul (2 * π)).sub_const π) using 2 <;> simp

/-- The Jacobian of `squarePolar`. -/
private theorem det_squarePolarDeriv (R : ℝ) (x : ℝ × ℝ) :
    (squarePolarDeriv R x).det = R * (1 / (2 * √x.1)) * (2 * π) := by
  simp [squarePolarDeriv, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]

/-- `squarePolar` maps the open unit square onto $(0, R) \times (-\pi, \pi)$. -/
private theorem image_squarePolar {R : ℝ} (hR : 0 < R) :
    squarePolar R '' (Ioo 0 1 ×ˢ Ioo 0 1) = Ioo 0 R ×ˢ Ioo (-π) π := by
  ext ⟨r, θ⟩
  simp only [mem_image, mem_prod, mem_Ioo, Prod.exists, squarePolar, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨⟨ha0, ha1⟩, hb0, hb1⟩, rfl, rfl⟩
    have hs0 : 0 < √a := Real.sqrt_pos.mpr ha0
    have hs1 : √a < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using ha1)
    refine ⟨⟨by positivity, by nlinarith⟩, by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
  · rintro ⟨⟨hr0, hrR⟩, hθ0, hθ1⟩
    refine ⟨(r / R) ^ 2, (θ + π) / (2 * π), ⟨⟨by positivity, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · rw [div_pow, div_lt_one (by positivity)]; nlinarith
    · have := pi_pos; apply div_pos <;> linarith
    · have := pi_pos; rw [div_lt_one (by positivity)]; linarith
    · rw [Real.sqrt_sq (by positivity)]; field_simp
    · have := pi_pos; field_simp; ring

/-- `squarePolar` is injective on the open unit square. -/
private theorem injOn_squarePolar {R : ℝ} (hR : 0 < R) :
    InjOn (squarePolar R) (Ioo 0 1 ×ˢ Ioo 0 1) := by
  rintro ⟨a, b⟩ ⟨ha, -⟩ ⟨a', b'⟩ ⟨ha', -⟩ h
  simp only [squarePolar, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hs : √a = √a' := mul_left_cancel₀ hR.ne' h1
  have ha0 : 0 ≤ a := ha.1.le
  have ha0' : 0 ≤ a' := ha'.1.le
  have haa : a = a' := by
    rw [← Real.sq_sqrt ha0, ← Real.sq_sqrt ha0', hs]
  have := pi_pos
  have hbb : b = b' := by
    have : 2 * π * b = 2 * π * b' := by linarith
    exact mul_left_cancel₀ (by positivity) this
  rw [haa, hbb]

/-- The change of variables from the open unit square to the disk $\mathbb{D}(0, R)$: the
Jacobian of the polar sampler is the constant $\pi R^2$. -/
private theorem lintegral_squarePolar {R : ℝ} (hR : 0 < R) (f : ℂ → ENNReal) :
    ∫⁻ x in Ioo 0 1 ×ˢ Ioo 0 1, f (Complex.polarCoord.symm (squarePolar R x)) =
      ENNReal.ofReal (1 / (π * R ^ 2)) * ∫⁻ z in Metric.ball 0 R, f z := by
  have hT : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have h1 := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT
    (fun x hx => (hasFDerivAt_squarePolar R (ne_of_gt hx.1.1)).hasFDerivWithinAt)
    (injOn_squarePolar hR)
    (fun y => ENNReal.ofReal (1 / (π * R ^ 2)) *
      (ENNReal.ofReal y.1 * f (Complex.polarCoord.symm y)))
  rw [image_squarePolar hR] at h1
  have h2 : ∫⁻ x in Ioo 0 1 ×ˢ Ioo 0 1, f (Complex.polarCoord.symm (squarePolar R x)) =
      ∫⁻ x in Ioo 0 1 ×ˢ Ioo 0 1, ENNReal.ofReal |(squarePolarDeriv R x).det| *
        (ENNReal.ofReal (1 / (π * R ^ 2)) *
          (ENNReal.ofReal (squarePolar R x).1 *
            f (Complex.polarCoord.symm (squarePolar R x)))) := by
    refine setLIntegral_congr_fun hT fun x hx => ?_
    have hs : 0 < √x.1 := Real.sqrt_pos.mpr hx.1.1
    have := pi_pos
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), det_squarePolarDeriv, squarePolar]
    have : |R * (1 / (2 * √x.1)) * (2 * π)| * (1 / (π * R ^ 2)) * (R * √x.1) = 1 := by
      rw [abs_of_pos (by positivity)]; field_simp
    rw [this, ENNReal.ofReal_one, one_mul]
  rw [h2, ← h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [← lintegral_indicator measurableSet_ball, ← Complex.lintegral_comp_polarCoord_symm,
    show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl,
    ← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo),
    ← lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  congr 1
  ext ⟨r, θ⟩
  by_cases hr : 0 < r
  · have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    simp only [indicator, mem_prod, mem_Ioo, mem_Ioi, Metric.mem_ball, dist_zero_right, hn, hr,
      true_and, smul_eq_mul]
    by_cases hrR : r < R <;> by_cases hθ : -π < θ ∧ θ < π <;> simp [hrR, hθ]
  · simp [indicator, hr]

/-- The polar sampler through `squarePolar` and Mathlib's polar coordinates. -/
private theorem polarDisk_eq (c : ℂ) (R : ℝ) (x : Fin 2 → ℝ) :
    polarDisk c R x =
      c - Complex.polarCoord.symm (squarePolar R (MeasurableEquiv.finTwoArrow x)) := by
  simp only [polarDisk, squarePolar, MeasurableEquiv.finTwoArrow_apply,
    Complex.polarCoord_symm_apply,
    Real.cos_sub_pi, Real.sin_sub_pi, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- The open and the closed disk differ by a null set. -/
private theorem volume_inter_ball_eq (c : ℂ) (R : ℝ) {S : Set ℂ} :
    volume (S ∩ Metric.ball c R) = volume (Metric.closedBall c R ∩ S) := by
  have hae : Metric.ball c R =ᵐ[volume] Metric.closedBall c R :=
    ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
      (Measure.addHaar_closedBall_eq_addHaar_ball volume c R).le
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  rw [inter_comm]
  exact measure_congr (hae.inter (Filter.EventuallyEq.refl _ S))

/-- The polar sampler is uniform on the disk: the image of the uniform law on $[0, 1]^2$
under `NLAlib.polarDisk c R` is the uniform law on $\mathbb{D}(c, R)$, for $R > 0$ (the area
element $r\,dr\,d\vartheta$ becomes $\pi R^2\,dx_0\,dx_1$). -/
theorem map_polarDisk_eq_diskUniform (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)).map
      (polarDisk c R) = diskUniform c R := by
  have hmeas : Measurable (polarDisk c R) := by unfold polarDisk; fun_prop
  set g : ℝ × ℝ → ℂ := fun y => c - Complex.polarCoord.symm (squarePolar R y) with hgdef
  have hg : Measurable g := by
    simp only [hgdef, Complex.polarCoord_symm_apply, squarePolar]; fun_prop
  have hres : ((volume : Measure ℝ).restrict (Icc 0 1)).prod
      ((volume : Measure ℝ).restrict (Icc 0 1)) = volume.restrict (Ioo 0 1 ×ˢ Ioo 0 1) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc, Measure.prod_restrict]; rfl
  ext S hS
  have hpre : polarDisk c R ⁻¹' S = MeasurableEquiv.finTwoArrow ⁻¹' (g ⁻¹' S) := by
    ext x; simp only [mem_preimage, polarDisk_eq, hgdef]
  rw [Measure.map_apply hmeas hS, hpre,
    (measurePreserving_finTwoArrow _).measure_preimage (hg hS).nullMeasurableSet, hres,
    ← lintegral_indicator_one (hg hS)]
  have hind : ∀ y, (g ⁻¹' S).indicator 1 y =
      ((fun w => c - w) ⁻¹' S).indicator (1 : ℂ → ENNReal)
        (Complex.polarCoord.symm (squarePolar R y)) :=
    fun y => by
      by_cases h : g y ∈ S
      · rw [Set.indicator_of_mem (show y ∈ g ⁻¹' S from h),
          Set.indicator_of_mem (show _ ∈ (fun w => c - w) ⁻¹' S from h)]
        rfl
      · rw [Set.indicator_of_notMem (show y ∉ g ⁻¹' S from h),
          Set.indicator_of_notMem (show _ ∉ (fun w => c - w) ⁻¹' S from h)]
  have hcS : MeasurableSet ((fun w : ℂ => c - w) ⁻¹' S) :=
    measurableSet_preimage (by fun_prop) hS
  rw [lintegral_congr hind, lintegral_squarePolar hR, lintegral_indicator_one hcS,
    Measure.restrict_apply hcS]
  have hset : (fun w => c - w) ⁻¹' S ∩ Metric.ball 0 R =
      (fun w => c - w) ⁻¹' (S ∩ Metric.ball c R) := by
    ext z; simp [dist_eq_norm]
  rw [hset, (Measure.measurePreserving_sub_left volume c).measure_preimage
    (hS.inter measurableSet_ball).nullMeasurableSet, volume_inter_ball_eq, diskUniform,
    ProbabilityTheory.cond_apply measurableSet_closedBall, Complex.volume_closedBall]
  congr 1
  rw [← ENNReal.ofReal_pow hR.le, one_div, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_mul pi_pos.le, mul_comm]
  congr 2
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- **A common polar disk sample keeps $k$ centres away from a separated family**
([BanksGarzaVargasSrivastava2022, Lemma 3.10], one sample for several centres): for centres
$c_1, \dots, c_k$, complex numbers $e_1, \dots, e_N$ whose distinct values are at distance at least
$2(\eta + R)$, $R > 0$ and $\eta \ge 0$, the window $x \in \mathbb{R}^2$ of two uniform draws on
$[0, 1]$ lies off the unit square or makes the polar sample $w$ of radius $R$ bring some
$c_j + w$ within $\eta$ of some $e_i$ with probability at most $k(\eta/R)^2$. -/
theorem measureReal_polarDisk_bad_le {k N : ℕ} (c : Fin k → ℂ) (e : Fin N → ℂ) {R η : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η) (hsep : ∀ i j, e i ≠ e j → 2 * (η + R) ≤ ‖e i - e j‖) :
    (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)).real
      {x | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
        ∃ j i, ‖c j + polarDisk 0 R x - e i‖ < η} ≤ k * (η / R) ^ 2 := by
  classical
  set Λ : Finset ℂ := Finset.univ.image e
  have hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → 2 * (η + R) ≤ ‖a - b‖ := by
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    exact hsep i j hab
  set U : Fin k → Set ℂ := fun j => {w | ∃ a ∈ Λ, ‖c j + w - a‖ < η}
  have hU : ∀ j, MeasurableSet (U j) := fun j => by
    have : U j = ⋃ a ∈ Λ, {w | ‖c j + w - a‖ < η} := by ext; simp [U]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun a _ => measurableSet_lt (by fun_prop)
      measurable_const
  have h1 : ∀ j, (diskUniform 0 R).real (U j) ≤ (η / R) ^ 2 := fun j => by
    have hD := measureReal_exists_norm_add_sub_lt_le (fun _ : Fin 1 => c j) Λ hR hη hΛ
    have hmp := measurePreserving_funUnique (diskUniform 0 R) (Fin 1)
    rw [← hmp.measureReal_preimage (hU j).nullMeasurableSet]
    refine le_trans (le_of_eq ?_) (by simpa using hD)
    congr 1
  set μ := Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)
  set A : Set (Fin 2 → ℝ) := ⋃ j, (fun x : Fin 2 → ℝ => x j) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ
  have hmeas : Measurable (polarDisk 0 R) := by unfold polarDisk; fun_prop
  have hset : {x : Fin 2 → ℝ | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ j i, ‖c j + polarDisk 0 R x - e i‖ < η} = A ∪ ⋃ j, polarDisk 0 R ⁻¹' U j := by
    ext x; simp [A, U, Λ]
  have hA0 : μ A = 0 := by
    refine measure_iUnion_null fun j => Measure.pi_eval_preimage_null _ ?_
    rw [Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self, measure_empty]
  have hmap : ∀ j, μ.real (polarDisk 0 R ⁻¹' U j) = (diskUniform 0 R).real (U j) := fun j => by
    rw [← map_measureReal_apply hmeas (hU j), map_polarDisk_eq_diskUniform 0 hR]
  rw [hset]
  have : IsProbabilityMeasure μ := by
    unfold μ
    have : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Icc 0 1)) :=
      ⟨by simp⟩
    infer_instance
  calc μ.real (A ∪ ⋃ j, polarDisk 0 R ⁻¹' U j)
      ≤ μ.real A + μ.real (⋃ j, polarDisk 0 R ⁻¹' U j) := measureReal_union_le _ _
    _ ≤ 0 + ∑ j, μ.real (polarDisk 0 R ⁻¹' U j) := by
        rw [measureReal_def, hA0, ENNReal.toReal_zero]
        gcongr
        exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin k, (η / R) ^ 2 := by
        rw [zero_add]
        exact Finset.sum_le_sum fun j _ => (hmap j).trans_le (h1 j)
    _ = k * (η / R) ^ 2 := by simp

end PolarSampler

end NLAlib
