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
the disk of radius $10\Sigma$ (Lemma 3.7, with the start a disk sample, the paper's erratum B3),
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
  sorry

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
  sorry

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
  sorry

end NLAlib.SmallEig
