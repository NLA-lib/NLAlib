/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import NLAlib.Matrix.QRIteration.EigenvectorWeights
public import NLAlib.Matrix.QRIteration.ShiftedQR

/-!
# Inverse iteration estimates of the distance to the spectrum

For a diagonalizable $\mathbf{H} = \mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ and a
shift $s$ off the spectrum, the last row of $(s\mathbf{I} - \mathbf{H})^{-m}$ measures the
distance from $s$ to the spectrum: its norm is at most $\kappa(\mathbf{V})$ times the $m$-th power
of the inverse distance, and at least the weighted inverse distance to every eigenvalue, divided
by $\kappa(\mathbf{V})$ (the row form of [BanksGarzaVargasSrivastava2025, Proposition 3.1]). Its
consequence for the exact shifted QR iteration with one repeated shift
[BanksGarzaVargasSrivastava2025, Lemma 4.1]: one of the first $m$ iterates has its last
subdiagonal entry at most the distance to a weighted eigenvalue, up to the factor
$(\kappa(\mathbf{V})/\sqrt{w_i})^{1/m}$. The six-point net of an annulus
([BanksGarzaVargasSrivastava2025, Observation 3.2], with the radii as parameters) is the geometry
of the search for a point near the spectrum.

## Main definitions

* `NLAlib.hexDir`: the sixth roots of unity $e^{i\pi j/3}$.
* `NLAlib.hexNetRadius`: the covering radius of the six-point net of an annulus.

## Main results

* `NLAlib.norm_lastRow_inv_pow_le`, `NLAlib.sqrt_lastRowWeights_mul_le_norm_lastRow_inv_pow`: the
  two sides of the row form of Proposition 3.1.
* `NLAlib.exists_le_norm_subdiag_shiftedQR_pow`: Lemma 4.1.
* `NLAlib.exists_norm_hexNet_add_sub_le`, `NLAlib.hexNetRadius_le`: the six-point net.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-! ### The distance to the spectrum from the last row of a resolvent power -/

/-- **The last row of a resolvent power is at most $\kappa(\mathbf{V})$ times the inverse
distance to the spectrum, to the power $m$** ([BanksGarzaVargasSrivastava2025, Proposition 3.1],
the lower bound on $\tau$, in row form): for
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
a shift $s \ne d_i$ for every $i$ and $m \ge 1$,
$$\|\mathbf{e}_n^{\mathsf{T}}(s\mathbf{I} - \mathbf{H})^{-m}\| \le
  \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\,\bigl(\min_i \lvert s - d_i\rvert\bigr)^{-m}.$$ -/
theorem norm_lastRow_inv_pow_le {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {s : ℂ} {m : ℕ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hs : ∀ i, s ≠ d i) (hm : 1 ≤ m) :
    ‖WithLp.toLp 2 (((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - H)⁻¹ ^ m) (Fin.last n))‖ ≤
      pseudoConditionNumber V * (⨅ i, ‖s - d i‖)⁻¹ ^ m := by
  sorry

/-- **The last row of a resolvent power is at least every weighted inverse distance, divided by
$\kappa(\mathbf{V})$** ([BanksGarzaVargasSrivastava2025, Proposition 3.1], the upper bound on
$\tau$, in row form): for $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\mathbf{V}$ invertible, a shift $s \ne d_i$ for every $i$, $m \ge 1$ and the last-row weights
$w_i$ of $\mathbf{V}$, for every $i$
$$\sqrt{w_i}\,\lvert s - d_i\rvert^{-m} \le \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2
  \|\mathbf{e}_n^{\mathsf{T}}(s\mathbf{I} - \mathbf{H})^{-m}\|.$$ -/
theorem sqrt_lastRowWeights_mul_le_norm_lastRow_inv_pow
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {s : ℂ} {m : ℕ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) (hs : ∀ i, s ≠ d i) (hm : 1 ≤ m)
    (i : Fin (n + 1)) :
    √(lastRowWeights V i) * ‖s - d i‖⁻¹ ^ m ≤
      pseudoConditionNumber V *
        ‖WithLp.toLp 2 (((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - H)⁻¹ ^ m)
          (Fin.last n))‖ := by
  sorry

/-- **Exact decoupling by a repeated shift** ([BanksGarzaVargasSrivastava2025, Lemma 4.1]): let
$\mathbf{H}$ of order $n + 2$ be upper Hessenberg, $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and last-row weights $w$,
$s \ne d_i$ for every $i$, and $m \ge 1$. Then for every $i$ some $\ell$ with
$1 \le \ell \le m$ has the last subdiagonal entry $h_\ell$ of the $\ell$-th exact shifted QR
iterate with the shift $s$ satisfying
$$\lvert h_\ell\rvert^m\sqrt{w_i} \le \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\,
  \lvert s - d_i\rvert^m.$$
Stated with powers, so that a zero weight makes it vacuous instead of dividing by zero. -/
theorem exists_le_norm_subdiag_shiftedQR_pow {H V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    {d : Fin (n + 2) → ℂ} {s : ℂ} {m : ℕ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hs : ∀ i, s ≠ d i) (hm : 1 ≤ m) (i : Fin (n + 2)) :
    ∃ ℓ ∈ Finset.Icc 1 m,
      ‖multiShiftedQRStep H (List.replicate ℓ s) (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ m *
          √(lastRowWeights V i) ≤
        pseudoConditionNumber V * ‖s - d i‖ ^ m := by
  sorry

/-! ### The six-point net of an annulus -/

/-- The sixth roots of unity $e^{i\pi j/3}$, $j < 6$: the directions of the six-point net. -/
noncomputable def hexDir (j : Fin 6) : ℂ := Complex.exp (((Real.pi * j / 3 : ℝ) : ℂ) * Complex.I)

/-- The covering radius of the six-point net $\{s + r e^{i\pi j/3}\}$ on the annulus
$r_1 \le \lvert z - s\rvert \le r_2$:
$\max\bigl(\sqrt{r_1^2 + r^2 - \sqrt3\,r_1 r}, \sqrt{r_2^2 + r^2 - \sqrt3\,r_2 r}\bigr)$, the
distance at the angle $\pi/6$ from the nearest net point, largest on one of the two circles. -/
noncomputable def hexNetRadius (r₁ r₂ r : ℝ) : ℝ :=
  max (√(r₁ ^ 2 + r ^ 2 - √3 * r₁ * r)) (√(r₂ ^ 2 + r ^ 2 - √3 * r₂ * r))

/-- **The perturbed six-point net covers an annulus**
([BanksGarzaVargasSrivastava2025, Observation 3.2], with the radii as parameters): for
$0 < r_1 \le r \le r_2$, every $z$ with $r_1 \le \lvert z - s\rvert \le r_2$ and every
$\lvert w\rvert \le \eta$, some $j < 6$ has
$\lvert s + r e^{i\pi j/3} + w - z\rvert \le \rho + \eta$, where $\rho$ is
`NLAlib.hexNetRadius` $r_1$ $r_2$ $r$. -/
theorem exists_norm_hexNet_add_sub_le {r₁ r r₂ η : ℝ} (h₁ : 0 < r₁) (h₁r : r₁ ≤ r)
    (hr₂ : r ≤ r₂) {s z w : ℂ} (hz₁ : r₁ ≤ ‖z - s‖) (hz₂ : ‖z - s‖ ≤ r₂) (hw : ‖w‖ ≤ η) :
    ∃ j : Fin 6, ‖s + r * hexDir j + w - z‖ ≤ hexNetRadius r₁ r₂ r + η := by
  sorry

/-- **The covering radius on the annulus of a $10\%$ distance estimate**
([BanksGarzaVargasSrivastava2025, Observation 3.2], corrected): on
$\tau/1.1 \le \lvert z - s\rvert \le \tau/0.9$ the six points $s + \tau e^{i\pi j/3}$ cover within
$0.561\,\tau$, for $\tau \ge 0$. The paper's $0.57\tau$ for the annulus $[0.9\tau, 1.12\tau]$ is
not the annulus a $10\%$ estimate gives. -/
theorem hexNetRadius_le {τ : ℝ} (hτ : 0 ≤ τ) : hexNetRadius (τ / 1.1) (τ / 0.9) τ ≤ 0.561 * τ := by
  sorry

end NLAlib
