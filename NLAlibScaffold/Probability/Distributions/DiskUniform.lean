/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Probability.ConditionalProbability

/-!
# The uniform law on a disk

The uniform law on the closed disk $\mathbb{D}(c, R) \subset \mathbb{C}$ is Lebesgue measure
conditioned on the disk. A sample lands in a disk of radius $\eta$ with probability
at most $(\eta / R)^2$ (`NLAlib.measureReal_diskUniform_closedBall_le`). Two consequences are
the probabilistic part of the random shift regularization of shifted QR
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
    simp only [hU, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter]
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

end NLAlib
