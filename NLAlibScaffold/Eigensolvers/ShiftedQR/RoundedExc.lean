/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Probability.Distributions.DiskUniform

/-!
# The rounded exceptional shifts

The exceptional shifts $\mathrm{Exc}$ of [BanksGarzaVargasSrivastava2022, Lemma 5.3] are a net
of a disk around the promising Ritz value $r$, translated by one uniform sample $w$ of a small
disk and rounded. The translate makes every shift forward stable: a separated net, translated
at random, keeps away from the $n$ eigenvalues except with a small probability.

## Main results

* `NLAlib.ShiftedQR.excTranslate_bad_window_le`: the window of two uniform draws that the polar
  sampler maps to a translate bringing some net point within
  $\eta = \varepsilon R\sqrt{\varphi/(11n)}$ of an eigenvalue has probability at most
  $\varphi$.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.ShiftedQR

/-- **The translate of the exceptional shifts fails with probability at most $\varphi$**
(the random translate of [BanksGarzaVargasSrivastava2022, Lemma 5.3], with the packing count
$11$ of errata G13iii for the paper's $3$): let $S$ be a finite set whose distinct points are at
distance at least $0.99\,\varepsilon R$, $\varepsilon R > 0$, $\lambda_1, \dots, \lambda_n$
complex numbers, $0 \le \varphi \le 1/5$ and $\eta = \varepsilon R\sqrt{\varphi/(11n)}$. For two
independent uniform draws $x_0, x_1 \in [0, 1]$ and the polar sample
$w = \varepsilon R\sqrt{x_0}\,e^{2\pi i x_1}$, uniform on $\mathbb{D}(0, \varepsilon R)$,
$$\mathbb{P}[\exists s \in S,\ \exists i,\ \lvert s + w - \lambda_i\rvert < \eta] \le
\varphi.$$
The bound $\varphi \le 1/5$ makes $\eta \le 0.14\,\varepsilon R$, the radius up to which the
packing count holds. -/
theorem excTranslate_bad_window_le (S : Finset ℂ) {N : ℕ} (e : Fin N → ℂ) {ε R φ : ℝ}
    (hεR : 0 < ε * R) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1 / 5)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 0.99 * (ε * R) ≤ ‖a - b‖) :
    (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)).real
      {x | ∃ s ∈ S, ∃ i, ‖s + polarDisk 0 (ε * R) x - e i‖ < ε * R * √(φ / (11 * N))} ≤ φ := by
  classical
  set η := ε * R * √(φ / (11 * N)) with hη_def
  set Λ : Finset ℂ := Finset.univ.image e
  have hΛ : (Λ.card : ℝ) ≤ N := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin N))) (f := e)
    simpa [Λ] using (Nat.cast_le (α := ℝ)).mpr this
  have hη0 : 0 ≤ η := by positivity
  have hq0 : 0 ≤ φ / (11 * N) := by positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [measureReal_def, hφ]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : φ / (11 * N) ≤ 0.14 ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsq : √(φ / (11 * N)) ≤ 0.14 := by
    rw [show (0.14 : ℝ) = √(0.14 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hq
  have hηR : η ≤ 0.14 * (ε * R) := by
    rw [hη_def, mul_comm (0.14 : ℝ)]; exact mul_le_mul_of_nonneg_left hsq hεR.le
  have hD4 := measureReal_exists_norm_add_sub_lt_le_of_separated S Λ hεR hη0 hηR hS
  set U : Set ℂ := {w | ∃ s ∈ S, ∃ a ∈ Λ, ‖s + w - a‖ < η}
  have hU : MeasurableSet U := by
    have : U = ⋃ s ∈ S, ⋃ a ∈ Λ, {w | ‖s + w - a‖ < η} := by ext; simp [U]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun s _ => Finset.measurableSet_biUnion _ fun a _ =>
      measurableSet_lt (by fun_prop) measurable_const
  have hmeas : Measurable (polarDisk 0 (ε * R)) := by unfold polarDisk; fun_prop
  have hpre : {x | ∃ s ∈ S, ∃ i, ‖s + polarDisk 0 (ε * R) x - e i‖ < η} =
      polarDisk 0 (ε * R) ⁻¹' U := by
    ext x; simp [U, Λ]
  rw [hpre, ← map_measureReal_apply hmeas hU, map_polarDisk_eq_diskUniform 0 hεR]
  refine hD4.trans ?_
  have hratio : (η / (ε * R)) ^ 2 = φ / (11 * N) := by
    rw [hη_def, mul_div_cancel_left₀ _ hεR.ne', Real.sq_sqrt hq0]
  rw [hratio]
  calc 11 * (Λ.card : ℝ) * (φ / (11 * N)) ≤ 11 * N * (φ / (11 * N)) := by gcongr
    _ = φ := by field_simp

end NLAlib.ShiftedQR
