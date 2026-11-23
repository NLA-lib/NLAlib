/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import NLAlib.Matrix.QRIteration.InverseIteration

/-!
# The search of `OneEig` on an abstract run

`OneEig` ([BanksGarzaVargasSrivastava2025, §3.2]) moves a point $s_i$ towards the spectrum
$\Lambda$: from an estimate $\tau_i$ of its distance within $10\%$, it estimates the distances of
the six points $s_i + \tau_i e^{i\pi j/3} + w_i$ ($w_i$ a small disk sample) and moves to the best
one if its estimate is at most $0.66\,\tau_i$. This file states the arithmetic of the search on an
abstract run (a sequence of points and estimates with these properties, as the merged abstract
loop of the shifted QR iteration): the estimates decrease geometrically and the points stay in
the disk of radius $10\Sigma$ (Lemma 3.7, adapted to a start at a disk sample),
a round with accurate estimates at every net point makes progress (Lemma 3.8, its statement
corrected), and after the round cap some estimate is below $0.9\beta$.

## Main definitions

* `NLAlib.SmallEig.OneEigRun`: an abstract run.

## Main results

* `NLAlib.SmallEig.OneEigRun.dist_le_and_norm_le`: Lemma 3.7.
* `NLAlib.SmallEig.exists_hexNet_le`: Lemma 3.8.
* `NLAlib.SmallEig.OneEigRun.exists_le_of_rounds`: the success after the round cap.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Metric

/-- **An abstract run of `OneEig`** of $t$ rounds on the set $\Lambda$ (the spectrum), with the
disk radius $\eta$: the estimates $\tau_i$, $i \le t$, are within $10\%$ of the distance from
$s_i$ to $\Lambda$; each round moves to a perturbed net point
$s_{i+1} = s_i + \tau_i e^{i\pi j/3} + w$ with $\lvert w\rvert \le \eta$, and contracts the
estimate, $\tau_{i+1} \le 0.66\,\tau_i$. -/
structure OneEigRun (Λ : Set ℂ) (η : ℝ) (t : ℕ) (s : ℕ → ℂ) (τ : ℕ → ℝ) : Prop where
  /-- The estimates are within $10\%$ of the distance to $\Lambda$. -/
  accurate : ∀ i ≤ t, 0.9 * infDist (s i) Λ ≤ τ i ∧ τ i ≤ 1.1 * infDist (s i) Λ
  /-- Each round moves to a perturbed net point. -/
  step : ∀ i < t, ∃ (j : Fin 6) (w : ℂ), ‖w‖ ≤ η ∧ s (i + 1) = s i + τ i * hexDir j + w
  /-- Each round contracts the estimate. -/
  contract : ∀ i < t, τ (i + 1) ≤ 0.66 * τ i

/-- **The estimates of `OneEig` decrease and its points stay in a disk**
([BanksGarzaVargasSrivastava2025, Lemma 3.7], with the start a disk sample of radius $\eta$): for
an abstract run (`NLAlib.SmallEig.OneEigRun`) of $t$ rounds on a nonempty $\Lambda$ inside the
disk of radius $R$, with $\lvert s_0\rvert \le \eta$, $\eta \le 0.02R$, $\eta \le \beta/5$,
$\beta > 0$ and every estimate at least $0.9\beta$, for every $i \le t$:
$\tau_i \le 2.3 \cdot 0.66^i R$, and every perturbed net point
$s_i + \tau_i e^{i\pi j/3} + w$, $\lvert w\rvert \le \eta$, lies in the disk of radius $10R$, as
does $s_i$. -/
theorem OneEigRun.dist_le_and_norm_le {Λ : Set ℂ} {η R β : ℝ} {t : ℕ} {s : ℕ → ℂ} {τ : ℕ → ℝ}
    (h : OneEigRun Λ η t s τ) (hΛ : Λ.Nonempty) (hR : ∀ z ∈ Λ, ‖z‖ ≤ R) (hs0 : ‖s 0‖ ≤ η)
    (hηR : η ≤ 0.02 * R) (hηβ : η ≤ β / 5) (hβ : 0 < β) (hτβ : ∀ i ≤ t, 0.9 * β ≤ τ i) :
    ∀ i ≤ t, τ i ≤ 2.3 * 0.66 ^ i * R ∧ ‖s i‖ ≤ 10 * R ∧
      ∀ (j : Fin 6) (w : ℂ), ‖w‖ ≤ η → ‖s i + τ i * hexDir j + w‖ ≤ 10 * R := by
  obtain ⟨z, hz⟩ := hΛ
  have hR0 : 0 ≤ R := (norm_nonneg z).trans (hR z hz)
  -- the first estimate: `τ₀ ≤ 1.1 (η + R)`
  have hτ0 : τ 0 ≤ 1.1 * (η + R) := by
    have hd : infDist (s 0) Λ ≤ η + R := (infDist_le_dist_of_mem hz).trans
      ((dist_le_norm_add_norm (s 0) z).trans (add_le_add hs0 (hR z hz)))
    linarith [(h.accurate 0 (Nat.zero_le t)).2]
  -- a net point moves by at most `τᵢ + η ≤ (11/9) τᵢ`
  have hnet : ∀ i ≤ t, ∀ (j : Fin 6) (w : ℂ), ‖w‖ ≤ η →
      ‖s i + τ i * hexDir j + w‖ ≤ ‖s i‖ + 11 / 9 * τ i := by
    intro i hi j w hw
    have hτi := hτβ i hi
    have hτ0' : 0 ≤ τ i := by linarith
    calc ‖s i + τ i * hexDir j + w‖ ≤ ‖s i‖ + ‖(τ i : ℂ) * hexDir j‖ + ‖w‖ := norm_add₃_le
      _ = ‖s i‖ + τ i + ‖w‖ := by
          rw [norm_mul, norm_hexDir, mul_one, Complex.norm_real, Real.norm_of_nonneg hτ0']
      _ ≤ ‖s i‖ + 11 / 9 * τ i := by linarith
  -- the potential `‖sᵢ‖ + 3.6 τᵢ` does not increase, and `τᵢ ≤ 0.66ⁱ τ₀`
  have key : ∀ i ≤ t, τ i ≤ 0.66 ^ i * τ 0 ∧ ‖s i‖ + 3.6 * τ i ≤ η + 3.6 * τ 0 := by
    intro i
    induction i with
    | zero => intro _; simp only [pow_zero, one_mul, le_refl, true_and]; linarith
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨j, w, hw, hs⟩ := h.step i (by omega)
      have hc := h.contract i (by omega)
      have hm := hnet i (by omega) j w hw
      have hτi := hτβ i (by omega)
      refine ⟨by rw [pow_succ]; nlinarith, ?_⟩
      rw [hs]; nlinarith
  refine fun i hi => ⟨?_, ?_, fun j w hw => ?_⟩
  · have h1 := (key i hi).1
    have hp : (0 : ℝ) ≤ 0.66 ^ i := by positivity
    nlinarith
  · have h2 := (key i hi).2
    nlinarith [hτβ i hi]
  · have h2 := (key i hi).2
    nlinarith [hτβ i hi, hnet i hi j w hw]

/-- **A round with accurate estimates makes progress** ([BanksGarzaVargasSrivastava2025,
Lemma 3.8], its statement corrected): let $\Lambda$ be finite and nonempty, the estimate
$\tau > 0$ of the distance from $s$ to $\Lambda$ within $10\%$, $\lvert w\rvert \le \eta \le
0.039\,\tau$, and the estimates $\tau'_j$ of the six net points $s + \tau e^{i\pi j/3} + w$ at
most $1.1$ times their distances to $\Lambda$. Then some $\tau'_j \le 0.66\,\tau$. -/
theorem exists_hexNet_le {Λ : Set ℂ} (hΛ : Λ.Nonempty) (hΛf : Λ.Finite) {s w : ℂ} {τ η : ℝ}
    (hτ : 0.9 * infDist s Λ ≤ τ ∧ τ ≤ 1.1 * infDist s Λ) (hτ0 : 0 < τ) (hw : ‖w‖ ≤ η)
    (hη : η ≤ 0.039 * τ) {τ' : Fin 6 → ℝ}
    (hτ' : ∀ j, τ' j ≤ 1.1 * infDist (s + τ * hexDir j + w) Λ) :
    ∃ j, τ' j ≤ 0.66 * τ := by
  obtain ⟨z, hz, hdz⟩ := hΛf.isCompact.exists_infDist_eq_dist hΛ s
  rw [hdz] at hτ
  have hz1 : τ / 1.1 ≤ ‖z - s‖ := by
    rw [div_le_iff₀ (by norm_num), ← dist_eq_norm, dist_comm]; linarith
  have hz2 : ‖z - s‖ ≤ τ / 0.9 := by
    rw [le_div_iff₀ (by norm_num), ← dist_eq_norm, dist_comm]; linarith
  obtain ⟨j, hj⟩ := exists_norm_hexNet_add_sub_le (r := τ) (by positivity)
    (div_le_self hτ0.le (by norm_num)) (le_div_self hτ0.le (by norm_num) (by norm_num)) hz1 hz2 hw
  refine ⟨j, (hτ' j).trans ?_⟩
  have hd : infDist (s + τ * hexDir j + w) Λ ≤ ‖s + τ * hexDir j + w - z‖ := by
    rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hz
  have hρ := hexNetRadius_le hτ0.le
  nlinarith

/-- **`OneEig` succeeds within its round cap** ([BanksGarzaVargasSrivastava2025,
Proposition 3.5], the paragraph "Probability of success", with the corrected cap): for an
abstract run of $t$ rounds on a nonempty $\Lambda$ inside the disk of radius $R$, with
$\lvert s_0\rvert \le \eta$, $\eta \le 0.02R$, $\eta \le \beta/5$, $\beta > 0$ and
$2.3 \cdot 0.66^t R \le 0.9\beta$, some round $i \le t$ has $\tau_i \le 0.9\beta$, and then the
distance from $s_i$ to $\Lambda$ is at most $\beta$. -/
theorem OneEigRun.exists_le_of_rounds {Λ : Set ℂ} {η R β : ℝ} {t : ℕ} {s : ℕ → ℂ} {τ : ℕ → ℝ}
    (h : OneEigRun Λ η t s τ) (hΛ : Λ.Nonempty) (hR : ∀ z ∈ Λ, ‖z‖ ≤ R) (hs0 : ‖s 0‖ ≤ η)
    (hηR : η ≤ 0.02 * R) (hηβ : η ≤ β / 5) (hβ : 0 < β) (ht : 2.3 * 0.66 ^ t * R ≤ 0.9 * β) :
    ∃ i ≤ t, τ i ≤ 0.9 * β ∧ infDist (s i) Λ ≤ β := by
  by_cases hex : ∃ i ≤ t, τ i ≤ 0.9 * β
  · obtain ⟨i, hi, hτi⟩ := hex
    exact ⟨i, hi, hτi, by linarith [(h.accurate i hi).1]⟩
  · push Not at hex
    have h5 := (h.dist_le_and_norm_le hΛ hR hs0 hηR hηβ hβ (fun i hi => (hex i hi).le) t le_rfl).1
    linarith [hex t le_rfl]

/-- The distance to the range of a finite family is the least distance to its points. -/
theorem infDist_range_eq_iInf {ι : Type*} [Finite ι] [Nonempty ι] (d : ι → ℂ) (z : ℂ) :
    infDist z (Set.range d) = ⨅ i, ‖z - d i‖ := by
  refine le_antisymm ?_ ((le_infDist (Set.range_nonempty d)).mpr ?_)
  · obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => ‖z - d i‖)
    rw [← hi, ← dist_eq_norm]
    exact infDist_le_dist_of_mem ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    rw [dist_eq_norm]
    exact ciInf_le (Set.finite_range _).bddBelow i

/-- The potential of `OneEig` does not increase: for an abstract run of $t$ rounds on
$\Lambda$ with a point $z \in \Lambda$ of modulus at most $R$, $\lvert s_0\rvert \le \eta_0$ and
$\eta \le 0.2\,\tau_i$ for $i < t$, every $i \le t$ has
$\lvert s_i\rvert + 3.6\,\tau_i \le \eta_0 + 3.96(\eta_0 + R)$. -/
theorem OneEigRun.norm_add_le {Λ : Set ℂ} {η η₀ R : ℝ} {t : ℕ} {s : ℕ → ℂ} {τ : ℕ → ℝ}
    (h : OneEigRun Λ η t s τ) {z : ℂ} (hz : z ∈ Λ) (hR : ‖z‖ ≤ R) (hs0 : ‖s 0‖ ≤ η₀)
    (hητ : ∀ i < t, η ≤ 0.2 * τ i) :
    ∀ i ≤ t, ‖s i‖ + 3.6 * τ i ≤ η₀ + 3.96 * (η₀ + R) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hd : infDist (s 0) Λ ≤ η₀ + R := (infDist_le_dist_of_mem hz).trans
      ((dist_le_norm_add_norm (s 0) z).trans (add_le_add hs0 hR))
    linarith [(h.accurate 0 (Nat.zero_le t)).2]
  | succ i ih =>
    intro hi
    obtain ⟨j, w, hw, hs⟩ := h.step i (by omega)
    have hc := h.contract i (by omega)
    have hητi := hητ i (by omega)
    have hτ0 : 0 ≤ τ i := by linarith [norm_nonneg w]
    have hm : ‖s (i + 1)‖ ≤ ‖s i‖ + τ i + η := by
      rw [hs]
      calc ‖s i + τ i * hexDir j + w‖ ≤ ‖s i‖ + ‖(τ i : ℂ) * hexDir j‖ + ‖w‖ := norm_add₃_le
        _ = ‖s i‖ + τ i + ‖w‖ := by
            rw [norm_mul, norm_hexDir, mul_one, Complex.norm_real, Real.norm_of_nonneg hτ0]
        _ ≤ ‖s i‖ + τ i + η := by linarith
    linarith [ih (by omega)]

/-- A run of `OneEig` extends by one round: a perturbed net point $p$ of the last point with an
estimate within $10\%$ of its distance and at most $0.66$ times the last estimate. -/
theorem OneEigRun.snoc {Λ : Set ℂ} {η : ℝ} {t : ℕ} {s : ℕ → ℂ} {τ : ℕ → ℝ}
    (h : OneEigRun Λ η t s τ) {p w : ℂ} {τ' : ℝ} {j : Fin 6} (hw : ‖w‖ ≤ η)
    (hp : p = s t + τ t * hexDir j + w) (hc : τ' ≤ 0.66 * τ t)
    (ha : 0.9 * infDist p Λ ≤ τ' ∧ τ' ≤ 1.1 * infDist p Λ) :
    OneEigRun Λ η (t + 1) (fun k => if k ≤ t then s k else p)
      (fun k => if k ≤ t then τ k else τ') where
  accurate i hi := by
    rcases Nat.lt_or_ge t i with hti | hti
    · have : ¬ i ≤ t := by omega
      simpa only [this, if_false] using ha
    · simpa only [hti, if_true] using h.accurate i hti
  step i hi := by
    rcases Nat.lt_or_ge i t with hit | hit
    · obtain ⟨j', w', hw', hs⟩ := h.step i hit
      exact ⟨j', w', hw', by simpa only [show i + 1 ≤ t by omega, show i ≤ t by omega,
        if_true] using hs⟩
    · obtain rfl : i = t := by omega
      exact ⟨j, w, hw, by simpa only [show ¬ i + 1 ≤ i by omega, le_refl, if_true,
        if_false] using hp⟩
  contract i hi := by
    rcases Nat.lt_or_ge i t with hit | hit
    · simpa only [show i + 1 ≤ t by omega, show i ≤ t by omega, if_true] using h.contract i hit
    · obtain rfl : i = t := by omega
      simpa only [show ¬ i + 1 ≤ i by omega, le_refl, if_true, if_false] using hc

/-- A run of no rounds: a start point with an estimate within $10\%$ of its distance. -/
theorem oneEigRun_zero {Λ : Set ℂ} {η : ℝ} {s₀ : ℂ} {τ₀ : ℝ}
    (ha : 0.9 * infDist s₀ Λ ≤ τ₀ ∧ τ₀ ≤ 1.1 * infDist s₀ Λ) :
    OneEigRun Λ η 0 (fun _ => s₀) (fun _ => τ₀) where
  accurate _ _ := ha
  step _ hi := absurd hi (Nat.not_lt_zero _)
  contract _ hi := absurd hi (Nat.not_lt_zero _)

/-- **A net point near the spectrum** ([BanksGarzaVargasSrivastava2025, Observation 3.2]): for a
finite nonempty $\Lambda$ and an estimate $\tau > 0$ of the distance from $s$ to $\Lambda$ within
$10\%$, some unperturbed net point $s + \tau e^{i\pi j/3}$ is within $0.561\,\tau$ of
$\Lambda$. -/
theorem exists_infDist_hexNet_le {Λ : Set ℂ} (hΛ : Λ.Nonempty) (hΛf : Λ.Finite) {s : ℂ} {τ : ℝ}
    (hτ : 0.9 * infDist s Λ ≤ τ ∧ τ ≤ 1.1 * infDist s Λ) (hτ0 : 0 < τ) :
    ∃ j, infDist (s + τ * hexDir j) Λ ≤ 0.561 * τ := by
  obtain ⟨z, hz, hdz⟩ := hΛf.isCompact.exists_infDist_eq_dist hΛ s
  rw [hdz] at hτ
  have hz1 : τ / 1.1 ≤ ‖z - s‖ := by
    rw [div_le_iff₀ (by norm_num), ← dist_eq_norm, dist_comm]; linarith
  have hz2 : ‖z - s‖ ≤ τ / 0.9 := by
    rw [le_div_iff₀ (by norm_num), ← dist_eq_norm, dist_comm]; linarith
  obtain ⟨j, hj⟩ := exists_norm_hexNet_add_sub_le (r := τ) (η := 0) (w := 0) (by positivity)
    (div_le_self hτ0.le (by norm_num)) (le_div_self hτ0.le (by norm_num) (by norm_num)) hz1 hz2
    (by simp)
  refine ⟨j, (infDist_le_dist_of_mem hz).trans ?_⟩
  rw [dist_eq_norm]
  have hρ := hexNetRadius_le hτ0.le
  simp only [add_zero] at hj
  linarith

end NLAlib.SmallEig
