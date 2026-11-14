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
  sorry

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
  sorry

end NLAlib
