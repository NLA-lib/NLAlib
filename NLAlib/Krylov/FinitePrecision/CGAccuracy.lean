/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import NLAlib.Krylov.FinitePrecision.CGRunSpectrum

/-!
# The residual gap and the attainable accuracy of finite-precision CG, a priori

For a conjugate gradient run `C : NLAlib.CGRun n k` on a matrix with spectrum in $[a, a']$,
$a > 0$, $\kappa = a'/a$, under (H) $k^2\sqrt{k}\,\varepsilon\kappa^2 \le 10^{-5}$ and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, the computed iterates, the $\mathbf{A}$-norm error of
the computed run and the residual gap $\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j -
\mathbf{r}_j$ are bounded a priori: with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{x}_j\| \le 1.001\,M,\qquad
\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le 1.001\,\|\mathbf{x}_\star\|_{\mathbf{A}}^2,
\qquad \|\mathbf{g}_k\| \le 11\,k\,\varepsilon\,a'M .$$
The gap estimate of [MeurantStrakos2006, §5.4] depends on the maximum norm of an iterate;
its a priori form there is heuristic. Here the iterate bound is proved under (H).

The proof is one joint induction (the private theorem `gapErrorInduction`) on the gap and the
true $\mathbf{A}$-norm error $E_j$ of the computed run: the descent
$\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j \ge 0.999\rho_j^2$ (G1, from the line search defect), the
step $\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \le 1.001\gamma_j\rho_j^2$ (G2),
$\gamma_j\|\mathbf{p}_j\| \le 1.5\|\mathbf{b}\|/a$ through the model's
$\sum_j\gamma_j\rho_j^2 \le 2\|\mathbf{b}\|^2/a$ (G2′), and the one-step inequality for
$E_{j+1}$ (G3).

The **attainable accuracy** for $\varepsilon > 0$: after
$k_\star = \lceil\tfrac12(\sqrt{\kappa'} + 1)\ell\rceil$ steps,
$\kappa' = 2\kappa + 1$, $\ell = \ln(\sqrt{\kappa'}/(4\varepsilon))$, the computed residual is
below $8\varepsilon\|\mathbf{b}\|$ (`NLAlib.CGRun.ρ_le_of_cgKStar_le`, the Chebyshev bound of the
model), so the true residual is the gap up to $8\varepsilon\|\mathbf{b}\|$. Exact arithmetic is
an admissible run with zero gap, so the computed residual is not necessarily smaller than the
true residual. For any $\delta > 0$, the theorem gives
$\|\mathbf{r}_j\| \le 8\delta\varepsilon\|\mathbf{b}\|$ once
$j \ge k_\star(\kappa, \varepsilon, \delta)$, provided $j \le k$ and (H) holds. Choosing a
smaller $\delta$ costs logarithmically more iterations. This is a decreasing upper envelope,
not a claim that the residual norm decreases at every step or tends to zero at fixed precision.
The gap estimate does not assert stagnation or a positive lower bound for the true residual.

Validity: for $\varepsilon > 0$, (H) requires
$k \le (10^{-5}/(\varepsilon\kappa^2))^{2/5}$. Every requested residual tolerance must fit
this finite horizon. The stronger cubic condition in
`NLAlib.cgKStar_cube_mul_le` remains a sufficient condition at $k_\star$.

Related attainable-accuracy analysis for mixed-precision preconditioned CG appears in
[BakeCarsonMa2025, Theorem 2]. Their argument uses an existential auxiliary-energy index,
subject to their condition (91), and retains a maximum-iterate factor. Here unpreconditioned
CG has an explicit Chebyshev threshold and a proved iterate bound under (H). The error models
and hypotheses differ; this is not a formalization of their theorem or a comparison of its
constants. Citation numbering refers to version 3 of that preprint.

Constants are unoptimised (maintainer, 2026-10-29: "do whatever is cleanest proof-wise").

## Main definitions

* `NLAlib.cgKStar`: the number of steps after which the computed residual is at gap level.

## Main results

* `NLAlib.CGRun.p_dotProduct_r_ge`, `NLAlib.CGRun.γ_sq_mul_dotProduct_mulVec_le`,
  `NLAlib.CGRun.γ_mul_norm_p_le`, `NLAlib.CGRun.quadForm_sub_x_succ_le`: the one-step lemmas.
* `NLAlib.CGRun.quadForm_sub_x_le_sub_sum`, `NLAlib.CGRun.quadForm_sub_x_le`,
  `NLAlib.CGRun.norm_x_le`: the computed run's error and iterates, a priori.
* `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy`,
  `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_sol`,
  `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_b`: the residual gap, a priori.
* `NLAlib.CGRun.norm_sub_mulVec_x_le`: the true residual.
* `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.abs_norm_sub_mulVec_x_sub_norm_gap_le`,
  `NLAlib.CGRun.norm_sub_mulVec_x_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_x_le_of_cgKStar_le`,
  `NLAlib.CGRun.norm_sub_mulVec_x_cgKStar_le`: the attainable accuracy.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The number of steps to gap level**: with $\kappa' = 2\kappa + 1$,
$k_\star(\kappa, \varepsilon, \delta) = \bigl\lceil\tfrac12(\sqrt{2\kappa+1} + 1)
\ln\bigl(\sqrt{2\kappa+1}/(4\delta\varepsilon)\bigr)\bigr\rceil$. After $k_\star$ steps the
Chebyshev factor $2\sqrt{\kappa'}q^{k}$, $q = (\sqrt{\kappa'} - 1)/(\sqrt{\kappa'} + 1)$, is at
most $8\delta\varepsilon$ (`NLAlib.pow_le_of_cgKStar_le`). Here $q \le e^{-2/(\sqrt{\kappa'} +
1)}$. -/
noncomputable def cgKStar (κ ε δ : ℝ) : ℕ :=
  ⌈(Real.sqrt (2 * κ + 1) + 1) / 2 * Real.log (Real.sqrt (2 * κ + 1) / (4 * δ * ε))⌉₊

/-- **The Chebyshev factor after $k_\star$ steps**: for $\varepsilon, \delta > 0$, $\kappa \ge 0$
and $m \ge k_\star(\kappa, \varepsilon, \delta)$, with $\kappa' = 2\kappa + 1$,
$$\Bigl(\frac{\sqrt{\kappa'} - 1}{\sqrt{\kappa'} + 1}\Bigr)^m \le
\frac{4\delta\varepsilon}{\sqrt{\kappa'}} \,.$$ -/
theorem pow_le_of_cgKStar_le {κ ε δ : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : cgKStar κ ε δ ≤ m) :
    ((Real.sqrt (2 * κ + 1) - 1) / (Real.sqrt (2 * κ + 1) + 1)) ^ m ≤
      4 * δ * ε / Real.sqrt (2 * κ + 1) := by
  set s := Real.sqrt (2 * κ + 1) with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; linarith
  set q := (s - 1) / (s + 1) with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  have hq1 : q ≤ Real.exp (-(2 / (s + 1))) := by
    have h := Real.add_one_le_exp (-(2 / (s + 1)))
    have : q = -(2 / (s + 1)) + 1 := by rw [hq]; field_simp; ring
    rw [this]
    exact h
  have hm' : (s + 1) / 2 * Real.log (s / (4 * δ * ε)) ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have h1 : q ^ m ≤ Real.exp (-(2 / (s + 1))) ^ m := pow_le_pow_left₀ hq0 hq1 m
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp (m * -(2 / (s + 1))) ≤ Real.exp (-Real.log (s / (4 * δ * ε))) := by
    apply Real.exp_le_exp.mpr
    have : Real.log (s / (4 * δ * ε)) ≤ m * (2 / (s + 1)) := by
      rw [mul_div_assoc', le_div_iff₀ (by linarith)]
      linarith
    linarith
  have h3 : Real.exp (-Real.log (s / (4 * δ * ε))) = 4 * δ * ε / s := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  linarith

/-- $k_\star \ge 1$ for $\kappa \ge 0$, $0 < \delta \le 1$ and $0 < \varepsilon \le 1/100$:
the logarithm is at least $\ln 25 > 0$. -/
theorem cgKStar_pos {κ ε δ : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 0 < cgKStar κ ε δ := by
  apply Nat.ceil_pos.mpr
  have hs1 : 1 ≤ Real.sqrt (2 * κ + 1) := by rw [Real.one_le_sqrt]; linarith
  have h : 1 < Real.sqrt (2 * κ + 1) / (4 * δ * ε) := by
    rw [one_lt_div (by positivity)]
    nlinarith
  exact mul_pos (by linarith) (Real.log_pos h)

/-- **A sufficient cubic window condition for $k_\star$**: for $\kappa \ge 1$ and
$0 < \varepsilon \le 1/100$,
with $\ell = \ln(\sqrt{2\kappa + 1}/(4\varepsilon))$,
$\kappa^3\sqrt{\kappa}\,\varepsilon\,\ell^3 \le 7 \cdot 10^{-7}$ implies
$(k_\star)^3\varepsilon\kappa^2 \le 10^{-5}$. This stronger condition also implies (H),
$(k_\star)^2\sqrt{k_\star}\,\varepsilon\kappa^2 \le 10^{-5}$, since
$\sqrt{k_\star} \le k_\star$ for $k_\star \ge 1$. -/
theorem cgKStar_cube_mul_le {κ ε : ℝ} (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (h : κ ^ 3 * Real.sqrt κ * ε *
      Real.log (Real.sqrt (2 * κ + 1) / (4 * 1 * ε)) ^ 3 ≤ 7 / 10 ^ 7) :
    (cgKStar κ ε 1 : ℝ) ^ 3 * ε * κ ^ 2 ≤ 1 / 10 ^ 5 := by
  set s := Real.sqrt (2 * κ + 1) with hsdef
  set ℓ := Real.log (s / (4 * 1 * ε)) with hℓ
  have hκ0 : 0 ≤ κ := by linarith
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; linarith
  have hsk : Real.sqrt κ ≥ 1 := by rw [ge_iff_le, Real.one_le_sqrt]; exact hκ
  -- `ℓ ≥ 1`
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have he := Real.exp_one_lt_d9
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `s ≤ 1.74 √κ`
  have hs3 : s ≤ 174 / 100 * Real.sqrt κ := by
    have h3 : Real.sqrt 3 ≤ 174 / 100 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    calc s ≤ Real.sqrt (3 * κ) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt 3 * Real.sqrt κ := Real.sqrt_mul (by norm_num) κ
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
  have hK : (cgKStar κ ε 1 : ℝ) ≤ 237 / 100 * Real.sqrt κ * ℓ := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ (s + 1) / 2 * ℓ)
    have : (s + 1) / 2 * ℓ + 1 ≤ 237 / 100 * Real.sqrt κ * ℓ := by nlinarith
    exact (le_of_lt h).trans this
  have hK0 : (0 : ℝ) ≤ cgKStar κ ε 1 := Nat.cast_nonneg _
  have hK3 : (cgKStar κ ε 1 : ℝ) ^ 3 ≤ (237 / 100 * Real.sqrt κ * ℓ) ^ 3 :=
    pow_le_pow_left₀ hK0 hK 3
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ0
  have e : (237 / 100 * Real.sqrt κ * ℓ) ^ 3 * ε * κ ^ 2 =
      (237 / 100) ^ 3 * (κ ^ 3 * Real.sqrt κ * ε * ℓ ^ 3) := by
    have : Real.sqrt κ ^ 3 = κ * Real.sqrt κ := by rw [pow_succ, hsq]
    rw [mul_pow, mul_pow, this]
    ring
  calc (cgKStar κ ε 1 : ℝ) ^ 3 * ε * κ ^ 2 ≤ (237 / 100 * Real.sqrt κ * ℓ) ^ 3 * ε * κ ^ 2 := by
        gcongr
    _ = _ := e
    _ ≤ (237 / 100) ^ 3 * (7 / 10 ^ 7) := by gcongr
    _ ≤ 1 / 10 ^ 5 := by norm_num

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-! ### Helpers -/

private theorem acc_εκ {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) :
    C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
  obtain ⟨-, hκ, -, -, hkεκ, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have h1k : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  have := mul_le_mul_of_nonneg_right h1k (by have := C.ε_nonneg; positivity :
    0 ≤ C.ε * (a' / a))
  nlinarith

/-! ### One step -/

/-- The absolute direction-residual pairing defect retains its precision dependence: for a
successful run with spectrum in $[a,a']$, $a>0$ and $k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$,
$\lvert\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j-\|\mathbf{r}_j\|^2\rvert\le
26j\varepsilon(a'/a)\|\mathbf{r}_j\|^2$ for $j<k$. -/
theorem abs_p_dotProduct_r_sub_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {j : ℕ} (hj : j < k) :
    |C.p j ⬝ᵥ C.r j - C.ρ j ^ 2| ≤ 26 * j * C.ε * (a' / a) * C.ρ j ^ 2 := by
  obtain ⟨-, hκ, -, hε5, hkεκ, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hwindow : (k : ℝ) * C.ε ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_left hκ (by positivity : 0 ≤ (k : ℝ) * C.ε)
    nlinarith
  have hP : ∀ i < k, ‖WithLp.toLp 2 (C.p i)‖ ≤ 2 * (a' / a) * C.ρ i := fun i hi => by
    have h := C.norm_p_sq_le ha hs hsmall hi
    have h2 : ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ (2 * (a' / a) * C.ρ i) ^ 2 := by
      have := C.ρ_nonneg i
      nlinarith [sq_nonneg (C.ρ i)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := C.ρ_nonneg i; positivity)
      two_ne_zero).mp h2
  have hK := fun i (hi : i < k) => C.specNorm_mul_γ_mul_norm_p_sq_le ha hs hsmall hi
  rcases j with _ | i
  · rw [C.p_zero, ← C.r_zero, ρ, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    simp only [sub_self, abs_zero, Nat.cast_zero, mul_zero, zero_mul, le_refl]
  · have hi : i < k := by omega
    have hτ := C.abs_p_dotProduct_r_succ_le hwindow hP hK hi
    obtain ⟨hδ0, hδ1, -⟩ := C.δ_bounds hi
    have hep := C.norm_ep_le_of_lt hi
    have hD := C.δ_mul_norm_p_le hi
    have hPi := hP (i + 1) hj
    have hid : C.p (i + 1) ⬝ᵥ C.r (i + 1) =
        C.ρ (i + 1) ^ 2 + C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) + C.ep i ⬝ᵥ C.r (i + 1) := by
      rw [C.p_succ i hi, add_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul, ρ,
        EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    rw [hid]
    set ρ1 := C.ρ (i + 1)
    have hρ1 : 0 ≤ ρ1 := C.ρ_nonneg _
    have hY : 5 * ((i : ℝ) + 1) * C.ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤
        41 / 2 * ((i : ℝ) + 1) * C.ε * (a' / a) := by
      have h1 : 1 + 2 * (a' / a) + 21 / 20 * (a' / a) ≤ 41 / 10 * (a' / a) := by linarith
      exact (mul_le_mul_of_nonneg_left h1
        (by positivity : 0 ≤ 5 * ((i : ℝ) + 1) * C.ε)).trans_eq (by ring)
    have hτ' : |C.p i ⬝ᵥ C.r (i + 1)| ≤
        (41 / 2 * ((i : ℝ) + 1) * C.ε * (a' / a)) * C.ρ i ^ 2 := by
      refine hτ.trans ?_
      have := mul_le_mul_of_nonneg_right hY (sq_nonneg (C.ρ i))
      linarith
    have hδτ : |C.δ i * (C.p i ⬝ᵥ C.r (i + 1))| ≤
        (43 / 2 * ((i : ℝ) + 1) * C.ε * (a' / a)) * ρ1 ^ 2 := by
      rw [abs_mul, abs_of_nonneg hδ0]
      calc C.δ i * |C.p i ⬝ᵥ C.r (i + 1)| ≤
            C.δ i * ((41 / 2 * ((i : ℝ) + 1) * C.ε * (a' / a)) * C.ρ i ^ 2) :=
            mul_le_mul_of_nonneg_left hτ' hδ0
        _ = (41 / 2 * ((i : ℝ) + 1) * C.ε * (a' / a)) * (C.δ i * C.ρ i ^ 2) := by ring
        _ ≤ (41 / 2 * ((i : ℝ) + 1) * C.ε * (a' / a)) *
            ((1 + 31 / 10 * C.ε) * ρ1 ^ 2) := by gcongr
        _ ≤ (43 / 2 * ((i : ℝ) + 1) * C.ε * (a' / a)) * ρ1 ^ 2 := by
          have hz : 0 ≤ ((i : ℝ) + 1) * C.ε * (a' / a) * ρ1 ^ 2 := by positivity
          nlinarith [mul_nonneg (show 0 ≤ 1 / 10 ^ 5 - C.ε by linarith) hz]
    have hepr : |C.ep i ⬝ᵥ C.r (i + 1)| ≤ (17 / 4 * (C.ε * (a' / a))) * ρ1 ^ 2 := by
      refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
      have h1 : ‖WithLp.toLp 2 (C.ep i)‖ ≤ C.ε * (ρ1 + 21 / 20 * (2 * (a' / a) * ρ1 + ρ1)) := by
        refine hep.trans (mul_le_mul_of_nonneg_left ?_ hε0)
        linarith
      have h2 : C.ε * (ρ1 + 21 / 20 * (2 * (a' / a) * ρ1 + ρ1)) ≤
          (17 / 4 * (C.ε * (a' / a))) * ρ1 := by
        have : C.ε * (ρ1 + 21 / 20 * (2 * (a' / a) * ρ1 + ρ1)) =
            ρ1 * (41 / 20 * C.ε + 21 / 10 * (C.ε * (a' / a))) := by ring
        rw [this]
        have hεκ : C.ε ≤ C.ε * (a' / a) := le_mul_of_one_le_right hε0 hκ
        nlinarith
      calc ‖WithLp.toLp 2 (C.ep i)‖ * ‖WithLp.toLp 2 (C.r (i + 1))‖ ≤
            (17 / 4 * (C.ε * (a' / a))) * ρ1 * ρ1 := mul_le_mul_of_nonneg_right (h1.trans h2) hρ1
        _ = _ := by ring
    have hδτ' := abs_le.mp hδτ
    have hepr' := abs_le.mp hepr
    have hz : 0 ≤ C.ε * (a' / a) * ρ1 ^ 2 := by positivity
    have hi0 : 0 ≤ (i : ℝ) := by positivity
    apply abs_le.mpr
    push_cast
    constructor <;> nlinarith [mul_nonneg hi0 hz]

/-- For a successful run with spectrum in $[a,a']$, $a>0$ and
$k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$, the pairing is at least
$(1-26j\varepsilon a'/a)\|\mathbf{r}_j\|^2$ for $j<k$. -/
theorem p_dotProduct_r_ge_mul {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {j : ℕ} (hj : j < k) :
    (1 - 26 * j * C.ε * (a' / a)) * C.ρ j ^ 2 ≤ C.p j ⬝ᵥ C.r j := by
  have h := (abs_le.mp (C.abs_p_dotProduct_r_sub_le ha hs hsmall hj)).1
  nlinarith

/-- **Descent (G1)**: under (H), $\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j \ge
0.999\,\|\mathbf{r}_j\|^2$ for $j < k$. Exact CG has equality; here the line search defect
$\mathbf{p}_{j-1}^{\mathsf{T}}\mathbf{r}_j$ enters through
$\mathbf{p}_j = \mathbf{r}_j + \delta_{j-1}\mathbf{p}_{j-1} + \mathbf{e}^p_{j-1}$. -/
theorem p_dotProduct_r_ge {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {j : ℕ} (hj : j < k) :
    (1 - 1 / 1000) * C.ρ j ^ 2 ≤ C.p j ⬝ᵥ C.r j := by
  have h := C.p_dotProduct_r_ge_mul ha hs hsmall hj
  have ht := (C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall).2.2.2.2.1
  have hjr : (j : ℝ) ≤ k := by exact_mod_cast hj.le
  have hz : 0 ≤ C.ε * (a' / a) := by
    have := C.ε_nonneg
    have := (C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall).2.1
    positivity
  have hle := mul_le_mul_of_nonneg_right hjr hz
  nlinarith [sq_nonneg (C.ρ j)]

/-- The quadratic contribution of a step retains its precision dependence: for a successful
run with spectrum in $[a,a']$, $a>0$ and $k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$,
$\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j\le
(1+6\varepsilon a'/a)\gamma_j\|\mathbf{r}_j\|^2$ for $j<k$. -/
theorem γ_sq_mul_dotProduct_mulVec_le_mul {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) ≤ (1 + 6 * (C.ε * (a' / a))) * (C.γ j * C.ρ j ^ 2) := by
  obtain ⟨haa', hκ, hspec, hε5, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hεκ := C.acc_εκ ha hs hsmall
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hN0 := specNorm_nonneg C.A
  set N := ‖WithLp.toLp 2 (C.p j)‖ with hN
  have hNn : 0 ≤ N := norm_nonneg _
  set P := C.p j ⬝ᵥ (C.A *ᵥ C.p j) with hPdef
  have hP0 : a * N ^ 2 ≤ P := by
    have := (C.mul_norm_sq_le_quadForm hs (C.p j))
    rwa [C.quadForm_eq_dotProduct_mulVec] at this
  have hμ : C.μ j = P + C.p j ⬝ᵥ C.es j + C.eμ j := by
    rw [C.μ_eq j hj, C.s_eq j hj, dotProduct_add]
  have h1 : |C.p j ⬝ᵥ C.es j| ≤ C.ε * a' * N ^ 2 := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    have := C.norm_es_le j hj
    calc N * ‖WithLp.toLp 2 (C.es j)‖ ≤ N * (C.ε * specNorm C.A * N) :=
          mul_le_mul_of_nonneg_left this hNn
      _ ≤ N * (C.ε * a' * N) := by gcongr
      _ = _ := by ring
  have h2 : |C.eμ j| ≤ 2 * C.ε * a' * N ^ 2 := by
    refine (C.abs_eμ_le j hj).trans ?_
    have hs' := C.norm_s_le hj
    have : ‖WithLp.toLp 2 (C.s j)‖ ≤ 2 * a' * N := by
      refine hs'.trans ?_
      have : (1 + C.ε) * specNorm C.A ≤ 2 * a' := by nlinarith
      exact mul_le_mul_of_nonneg_right this hNn
    calc C.ε * N * ‖WithLp.toLp 2 (C.s j)‖ ≤ C.ε * N * (2 * a' * N) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have h3 : a' * N ^ 2 ≤ a' / a * P := by
    have := mul_le_mul_of_nonneg_left hP0 (by positivity : 0 ≤ a' / a)
    calc a' * N ^ 2 = a' / a * (a * N ^ 2) := by field_simp
      _ ≤ _ := this
  have hPμ : P * (1 - 3 * (C.ε * (a' / a))) ≤ C.μ j := by
    have := (abs_le.mp h1).1
    have := (abs_le.mp h2).1
    have h4 : C.ε * (a' * N ^ 2) ≤ C.ε * (a' / a * P) := mul_le_mul_of_nonneg_left h3 hε0
    have hP0' : 0 ≤ P := le_trans (by positivity) hP0
    nlinarith
  have hgm := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le] at hgm
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have he := abs_le.mp (C.abs_eγ_le j hj)
  have hρ2 : 0 ≤ C.ρ j ^ 2 := sq_nonneg _
  have h6 : C.γ j * C.μ j ≤ (1 + C.ε * (a' / a)) ^ 2 * C.ρ j ^ 2 := by
    rw [hgm]
    have hez : C.ε ≤ C.ε * (a' / a) := le_mul_of_one_le_right hε0 hκ
    have : (1 + C.θ j) * (1 + C.eγ j) ≤ (1 + C.ε * (a' / a)) ^ 2 := by nlinarith
    nlinarith
  have h7 : C.γ j ^ 2 * P * (1 - 3 * (C.ε * (a' / a))) ≤
      C.γ j * ((1 + C.ε * (a' / a)) ^ 2 * C.ρ j ^ 2) := by
    calc C.γ j ^ 2 * P * (1 - 3 * (C.ε * (a' / a))) =
          C.γ j * (C.γ j * (P * (1 - 3 * (C.ε * (a' / a))))) := by ring
      _ ≤ C.γ j * (C.γ j * C.μ j) := by gcongr
      _ ≤ _ := by gcongr
  have hγρ : 0 ≤ C.γ j * C.ρ j ^ 2 := by positivity
  set z := C.ε * (a' / a)
  have hz : 0 ≤ z := by positivity
  have hm : 0 < 1 - 3 * z := by dsimp [z]; linarith
  have hc : (1 + z) ^ 2 ≤ (1 + 6 * z) * (1 - 3 * z) := by
    have hz1 : z ≤ 1 / 19 := by dsimp [z]; linarith
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hz1)]
  have hh := mul_le_mul_of_nonneg_right hc hγρ
  have hcancel : (C.γ j ^ 2 * P) * (1 - 3 * z) ≤
      ((1 + 6 * z) * (C.γ j * C.ρ j ^ 2)) * (1 - 3 * z) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hm).mp hcancel

/-- **The step against the residual (G2)**: under (H), for $j < k$,
$\gamma_j^2\,\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \le
1.001\,\gamma_j\|\mathbf{r}_j\|^2$. -/
theorem γ_sq_mul_dotProduct_mulVec_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) ≤ (1 + 1 / 1000) * (C.γ j * C.ρ j ^ 2) := by
  have h := C.γ_sq_mul_dotProduct_mulVec_le_mul ha hs hsmall hj
  have hz := C.acc_εκ ha hs hsmall
  have hγρ : 0 ≤ C.γ j * C.ρ j ^ 2 :=
    mul_nonneg (C.γ_pos hj).le (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hz hγρ]

/-- **The step length, a priori (G2′)**: under (H), $\gamma_j\|\mathbf{p}_j\| \le
1.5\|\mathbf{b}\|/a$ for $j < k$. -/
theorem γ_mul_norm_p_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {j : ℕ} (hj : j < k) :
    C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 3 / 2 * ‖WithLp.toLp 2 C.b‖ / a := by
  have hsum := C.sum_γ_mul_ρ_sq_le ha hs hsmall
  have hγ := C.γ_pos hj
  have hle : C.γ j * C.ρ j ^ 2 ≤ ∑ i ∈ Finset.range k, C.γ i * C.ρ i ^ 2 :=
    Finset.single_le_sum (f := fun i => C.γ i * C.ρ i ^ 2)
      (fun i hi => mul_nonneg (C.γ_pos (Finset.mem_range.mp hi)).le (sq_nonneg _))
      (Finset.mem_range.mpr hj)
  have h2 := C.γ_sq_mul_dotProduct_mulVec_le ha hs hsmall hj
  have hP0 : a * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ C.p j ⬝ᵥ (C.A *ᵥ C.p j) := by
    have := (C.mul_norm_sq_le_quadForm hs (C.p j))
    rwa [C.quadForm_eq_dotProduct_mulVec] at this
  set B := ‖WithLp.toLp 2 C.b‖
  set X := C.γ j * ‖WithLp.toLp 2 (C.p j)‖
  have hX0 : 0 ≤ X := by positivity
  have h3 : a * X ^ 2 ≤ (1 + 1 / 1000) * (2 * B ^ 2 / a) := by
    have := mul_le_mul_of_nonneg_left hP0 (sq_nonneg (C.γ j))
    have h4 : (1 + 1 / 1000) * (C.γ j * C.ρ j ^ 2) ≤ (1 + 1 / 1000) * (2 * B ^ 2 / a) := by
      gcongr
      exact hle.trans hsum
    have : a * X ^ 2 = C.γ j ^ 2 * (a * ‖WithLp.toLp 2 (C.p j)‖ ^ 2) := by
      simp only [X]
      ring
    linarith
  have h5 : X ^ 2 ≤ (3 / 2 * B / a) ^ 2 := by
    have : (3 / 2 * B / a) ^ 2 = 9 / 4 * B ^ 2 / a ^ 2 := by ring
    rw [this, le_div_iff₀ (by positivity)]
    have h6 : (1 + 1 / 1000) * (2 * B ^ 2 / a) * a = (1 + 1 / 1000) * 2 * B ^ 2 := by
      field_simp
    nlinarith [sq_nonneg B]
  exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).mp h5

/-- G3 with the nonnegativity of the bracket, for the induction. -/
private theorem quadForm_sub_x_succ_le_of_descent {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) {c : ℝ}
    (hd : C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) -
      2 * C.γ j * (C.p j ⬝ᵥ C.r j) ≤ -c * (C.γ j * C.ρ j ^ 2)) :
    0 ≤ quadForm C.A (xs - C.x j) - c * (C.γ j * C.ρ j ^ 2) +
          2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ∧
    quadForm C.A (xs - C.x (j + 1)) ≤
      (Real.sqrt (quadForm C.A (xs - C.x j) - c * (C.γ j * C.ρ j ^ 2) +
          2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖) +
        Real.sqrt a' * ‖WithLp.toLp 2 (C.ex j)‖) ^ 2 := by
  have haa' := C.le_of_spectrum_subset_Icc hs
  have ha' : 0 ≤ a' := ha.le.trans haa'
  have hγ := C.γ_pos hj
  set g := C.b - C.A *ᵥ C.x j - C.r j with hg
  set e := xs - C.x j with he
  set w := e - C.γ j • C.p j with hw
  set v := C.ex j
  set X := quadForm C.A e - c * (C.γ j * C.ρ j ^ 2) +
    2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 g‖ with hX
  have hxe : xs - C.x (j + 1) = w - v := by
    rw [C.x_succ j hj, hw, he]
    abel
  have hpg : |C.p j ⬝ᵥ g| ≤ ‖WithLp.toLp 2 (C.p j)‖ * ‖WithLp.toLp 2 g‖ :=
    EuclideanSpace.abs_dotProduct_le_norm _ _
  have hQw0 : 0 ≤ quadForm C.A w := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs w)
  have hQw : quadForm C.A w ≤ X := by
    rw [C.quadForm_sub_x_sub_smul_p_eq hx j, hX]
    have h1 := (abs_le.mp hpg).1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * C.γ j)
    have h4 : 0 ≤ C.γ j * C.ρ j ^ 2 := by positivity
    nlinarith
  refine ⟨hQw0.trans hQw, ?_⟩
  set W := Real.sqrt (quadForm C.A w)
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hW2 : W ^ 2 = quadForm C.A w := Real.sq_sqrt hQw0
  have hsa : Real.sqrt a' ^ 2 = a' := Real.sq_sqrt ha'
  have hsa0 : 0 ≤ Real.sqrt a' := Real.sqrt_nonneg _
  have hAw : ‖WithLp.toLp 2 (C.A *ᵥ w)‖ ≤ Real.sqrt a' * W := by
    have h := C.norm_mulVec_sq_le_mul_quadForm ha hs w
    have h' : ‖WithLp.toLp 2 (C.A *ᵥ w)‖ ^ 2 ≤ (Real.sqrt a' * W) ^ 2 := by
      rw [mul_pow, hsa, hW2]
      exact h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'
  have hvw : |v ⬝ᵥ (C.A *ᵥ w)| ≤ ‖WithLp.toLp 2 v‖ * (Real.sqrt a' * W) :=
    (EuclideanSpace.abs_dotProduct_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hAw (norm_nonneg _))
  have hQv : quadForm C.A v ≤ (Real.sqrt a' * ‖WithLp.toLp 2 v‖) ^ 2 := by
    rw [mul_pow, hsa]
    exact (C.quadForm_le_mul_norm_sq hs v)
  have hWX : W ≤ Real.sqrt X := Real.sqrt_le_sqrt hQw
  have hv0 := norm_nonneg (WithLp.toLp 2 v)
  rw [hxe, C.quadForm_sub_eq w v]
  calc quadForm C.A w - 2 * (v ⬝ᵥ (C.A *ᵥ w)) + quadForm C.A v ≤
        (W + Real.sqrt a' * ‖WithLp.toLp 2 v‖) ^ 2 := by
        have := (abs_le.mp hvw).1
        nlinarith
    _ ≤ _ := by gcongr

/-- **One step of the computed run's $\mathbf{A}$-norm error (G3)**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j < k$, with the gap
$\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j$,
$$\|\mathbf{x}_\star - \mathbf{x}_{j+1}\|_{\mathbf{A}} \le
\sqrt{\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 - 0.99\,\gamma_j\|\mathbf{r}_j\|^2 +
2\gamma_j\|\mathbf{p}_j\|\|\mathbf{g}_j\|} + \sqrt{a'}\,\|\mathbf{e}^x_j\| \,.$$
Compare [BakeCarsonMa2025, Lemma 4], a perturbed energy-descent estimate for an auxiliary
iterate with the accumulated iterate-update rounding removed. Here the estimate concerns
the actual computed iterate and explicitly includes its update error. -/
theorem quadForm_sub_x_succ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    quadForm C.A (xs - C.x (j + 1)) ≤
      (Real.sqrt (quadForm C.A (xs - C.x j) - 99 / 100 * (C.γ j * C.ρ j ^ 2) +
          2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖) +
        Real.sqrt a' * ‖WithLp.toLp 2 (C.ex j)‖) ^ 2 := by
  have hγ := C.γ_pos hj
  have h1 := C.p_dotProduct_r_ge ha hs hsmall hj
  have h2 := C.γ_sq_mul_dotProduct_mulVec_le ha hs hsmall hj
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * C.γ j)
  exact (C.quadForm_sub_x_succ_le_of_descent ha hs hx hj (c := 99 / 100)
    (by nlinarith)).2

/-! ### The joint induction -/

private theorem acc_norm_sq_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 ≤ quadForm C.A v / a := by
  rw [le_div_iff₀ ha, mul_comm]
  exact (C.mul_norm_sq_le_quadForm hs v)

/-- The crude a priori bounds at step $j$ used by the induction: from $E_j^2 \le
2\|\mathbf{b}\|^2/a$ and $\|\mathbf{g}_j\| \le 12j\varepsilon\kappa\|\mathbf{b}\|$,
$\|\mathbf{x}_\star - \mathbf{x}_j\| \le 2\|\mathbf{b}\|/a$, $\|\mathbf{x}_j\| \le
3\|\mathbf{b}\|/a$ and $\rho_j \le 3\kappa\|\mathbf{b}\|$. -/
private theorem acc_step_facts {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k)
    (hG : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖)
    (hQ : quadForm C.A (xs - C.x j) ≤ 2 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)) :
    ‖WithLp.toLp 2 (xs - C.x j)‖ ≤ 2 * ‖WithLp.toLp 2 C.b‖ / a ∧
      ‖WithLp.toLp 2 (C.x j)‖ ≤ 3 * ‖WithLp.toLp 2 C.b‖ / a ∧
      C.ρ j ≤ 3 * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  obtain ⟨haa', hκ, hspec, _, hkεκ, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hwindow : (k : ℝ) * C.ε ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_left hκ (by positivity : 0 ≤ (k : ℝ) * C.ε)
    nlinarith
  have hjε : (j : ℝ) * C.ε ≤ 1 / 100 := C.mul_ε_le_of_le hwindow hj
  set κ := a' / a with hκdef
  set B := ‖WithLp.toLp 2 C.b‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have ha'κ : a' = κ * a := by rw [hκdef]; field_simp
  have hxs := C.norm_le_norm_b_div_of_mulVec_eq ha hs hx
  have he : ‖WithLp.toLp 2 (xs - C.x j)‖ ≤ 2 * B / a := by
    have h1 := C.acc_norm_sq_le ha hs (xs - C.x j)
    have h2 : ‖WithLp.toLp 2 (xs - C.x j)‖ ^ 2 ≤ (2 * B / a) ^ 2 := by
      refine h1.trans ?_
      rw [div_le_iff₀ ha]
      have : (2 * B / a) ^ 2 * a = 4 * (B ^ 2 / a) := by field_simp; ring
      rw [this]
      have : 0 ≤ B ^ 2 / a := by positivity
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  refine ⟨he, ?_, ?_⟩
  · have h := norm_sub_le (WithLp.toLp 2 xs) (WithLp.toLp 2 (xs - C.x j))
    rw [← WithLp.toLp_sub, sub_sub_cancel] at h
    have : 3 * B / a = B / a + 2 * B / a := by ring
    linarith
  · have hAe : ‖WithLp.toLp 2 (C.A *ᵥ (xs - C.x j))‖ ≤ a' * (2 * B / a) :=
      (norm_toLp_mulVec_le _ _).trans (mul_le_mul hspec he (norm_nonneg _) (by linarith))
    have hid : C.r j = C.A *ᵥ (xs - C.x j) - (C.b - C.A *ᵥ C.x j - C.r j) := by
      rw [Matrix.mulVec_sub, hx]
      abel
    have h := norm_sub_le (WithLp.toLp 2 (C.A *ᵥ (xs - C.x j)))
      (WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j))
    rw [← WithLp.toLp_sub, ← hid] at h
    have h2 : a' * (2 * B / a) = 2 * κ * B := by rw [ha'κ]; field_simp
    have hκB : 0 ≤ κ * B := by positivity
    have h3 : 12 * (j : ℝ) * C.ε * κ * B ≤ 12 / 100 * κ * B := by
      have := mul_le_mul_of_nonneg_right hjε hκB
      linarith
    change ‖WithLp.toLp 2 (C.r j)‖ ≤ _
    linarith

/-- The gap step of the induction. -/
private theorem acc_gap_step {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k)
    (hG : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖)
    (hQ : quadForm C.A (xs - C.x j) ≤ 2 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x (j + 1) - C.r (j + 1))‖ ≤
      12 * ((j + 1 : ℕ) : ℝ) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  obtain ⟨haa', hκ, hspec, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  obtain ⟨-, hxj, hρ⟩ := C.acc_step_facts ha hs hsmall hx hj.le hG hQ
  have hε0 := C.ε_nonneg
  have hγp := C.γ_mul_norm_p_le ha hs hsmall hj
  set κ := a' / a with hκdef
  set B := ‖WithLp.toLp 2 C.b‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have ha'κ : a' = κ * a := by rw [hκdef]; field_simp
  have h := C.norm_sub_mulVec_x_sub_r_succ_le hj
  have h0 : ‖WithLp.toLp 2 (C.x j)‖ + 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 9 * B / a := by
    have : 9 * B / a = 3 * B / a + 4 * (3 / 2 * B / a) := by ring
    have : 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ = 4 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) := by
      ring
    linarith
  have h1 : specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ + 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) ≤
      a' * (9 * B / a) :=
    mul_le_mul hspec h0 (by have := C.γ_pos hj; positivity) (by linarith)
  have h2 : a' * (9 * B / a) = 9 * κ * B := by rw [ha'κ]; field_simp
  have h3 : C.ε * (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
      4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) ≤ C.ε * (12 * κ * B) := by
    refine mul_le_mul_of_nonneg_left ?_ hε0
    linarith
  push_cast
  linarith

-- The descent parameter enlarges the polynomial rounding-error calculation.
set_option maxHeartbeats 400000 in
-- The variable descent coefficient adds polynomial atoms to the rounding-error arithmetic.
/-- The error step of the induction for an arbitrary nonnegative descent coefficient. -/
private theorem acc_err_step {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) {c : ℝ} (hc : 0 ≤ c)
    (hd : C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) -
      2 * C.γ j * (C.p j ⬝ᵥ C.r j) ≤ -c * (C.γ j * C.ρ j ^ 2))
    (hG : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖)
    (hQ : quadForm C.A (xs - C.x j) ≤ 2 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)) :
    quadForm C.A (xs - C.x (j + 1)) ≤ quadForm C.A (xs - C.x j) -
      c * (C.γ j * C.ρ j ^ 2) +
        (36 * j + 19) * (C.ε * (a' / a)) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  obtain ⟨haa', hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  obtain ⟨hjT, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le_of_le ha hs hsmall hj.le
  obtain ⟨-, hxj, -⟩ := C.acc_step_facts ha hs hsmall hx hj.le hG hQ
  obtain ⟨hX0, hstep⟩ := C.quadForm_sub_x_succ_le_of_descent ha hs hx hj hd
  have hε0 := C.ε_nonneg
  have hε1 := C.ε_le
  have hγ := C.γ_pos hj
  have hγp := C.γ_mul_norm_p_le ha hs hsmall hj
  have hγρ : 0 ≤ C.γ j * C.ρ j ^ 2 := by positivity
  set κ := a' / a with hκdef
  set B := ‖WithLp.toLp 2 C.b‖ with hB
  set u := B ^ 2 / a with hu
  have hB0 : 0 ≤ B := norm_nonneg _
  have hu0 : 0 ≤ u := by positivity
  have hT0 : 0 ≤ C.ε * κ := by positivity
  have ha'κ : a' = κ * a := by rw [hκdef]; field_simp
  have ha' : 0 ≤ a' := by linarith
  set G := ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ with hGdef
  set Qj := quadForm C.A (xs - C.x j) with hQj
  set X := Qj - c * (C.γ j * C.ρ j ^ 2) +
    2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * G with hX
  have hX1 : X ≤ Qj - c * (C.γ j * C.ρ j ^ 2) + 36 * j * (C.ε * κ) * u := by
    have h1 : 2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * G ≤
        2 * (3 / 2 * B / a) * (12 * j * C.ε * κ * B) :=
      mul_le_mul (by linarith) hG (norm_nonneg _) (by positivity)
    have h2 : 2 * (3 / 2 * B / a) * (12 * j * C.ε * κ * B) = 36 * j * (C.ε * κ) * u := by
      rw [hu]
      ring
    linarith
  have hX4 : X ≤ 4 * u := by
    have : 36 * (j : ℝ) * (C.ε * κ) * u ≤ 36 / 10 ^ 5 * u := by
      have := mul_le_mul_of_nonneg_right hjT hu0
      linarith
    nlinarith [mul_nonneg hc hγρ]
  set t := Real.sqrt a' * ‖WithLp.toLp 2 (C.ex j)‖ with ht
  have hex : ‖WithLp.toLp 2 (C.ex j)‖ ≤ C.ε * (9 / 2 * B / a) := by
    refine (C.norm_ex_le j hj).trans (mul_le_mul_of_nonneg_left ?_ hε0)
    rw [abs_of_pos hγ]
    have : 9 / 2 * B / a = 3 * B / a + 3 / 2 * B / a := by ring
    linarith
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t ^ 2 ≤ 81 / 4 * C.ε ^ 2 * κ * u := by
    rw [ht, mul_pow, Real.sq_sqrt ha']
    have h1 : ‖WithLp.toLp 2 (C.ex j)‖ ^ 2 ≤ (C.ε * (9 / 2 * B / a)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hex 2
    have h2 : a' * (C.ε * (9 / 2 * B / a)) ^ 2 = 81 / 4 * C.ε ^ 2 * κ * u := by
      rw [hu, ha'κ]
      field_simp
      ring
    calc a' * ‖WithLp.toLp 2 (C.ex j)‖ ^ 2 ≤ a' * (C.ε * (9 / 2 * B / a)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 ha'
      _ = _ := h2
  have hXt : Real.sqrt X * t ≤ 9 * (C.ε * κ) * u := by
    have h1 : (Real.sqrt X * t) ^ 2 ≤ (9 * (C.ε * κ) * u) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hX0]
      have h2 : X * t ^ 2 ≤ 4 * u * (81 / 4 * C.ε ^ 2 * κ * u) :=
        mul_le_mul hX4 ht2 (sq_nonneg _) (by positivity)
      have h3 : 4 * u * (81 / 4 * C.ε ^ 2 * κ * u) ≤ (9 * (C.ε * κ) * u) ^ 2 := by
        have e1 : 4 * u * (81 / 4 * C.ε ^ 2 * κ * u) = 81 * C.ε ^ 2 * u ^ 2 * κ := by ring
        have e2 : (9 * (C.ε * κ) * u) ^ 2 = 81 * C.ε ^ 2 * u ^ 2 * κ ^ 2 := by ring
        rw [e1, e2]
        have : κ ≤ κ ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have ht2' : t ^ 2 ≤ 1 / 4 * (C.ε * κ) * u := by
    have e : 81 / 4 * C.ε ^ 2 * κ * u = 81 / 4 * C.ε * (C.ε * κ * u) := by ring
    have := mul_le_mul_of_nonneg_right (by linarith : 81 / 4 * C.ε ≤ 1 / 4)
      (by positivity : 0 ≤ C.ε * κ * u)
    have e2 : 1 / 4 * (C.ε * κ * u) = 1 / 4 * (C.ε * κ) * u := by ring
    linarith
  have e : (Real.sqrt X + t) ^ 2 = X + 2 * (Real.sqrt X * t) + t ^ 2 := by
    rw [add_sq, Real.sq_sqrt hX0]
    ring
  rw [e] at hstep
  have e2 : (36 * (j : ℝ) + 19) * (C.ε * κ) * u =
      36 * j * (C.ε * κ) * u + 19 * (C.ε * κ) * u := by ring
  have : 0 ≤ (C.ε * κ) * u := by positivity
  linarith

/-- The joint induction on the gap and the computed run's error (G4). -/
private theorem gapErrorInduction {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
        12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ ∧
      quadForm C.A (xs - C.x j) + 99 / 100 * ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 ≤
        quadForm C.A xs + 25 * j ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hQ0 := C.quadForm_le_norm_b_sq_div_of_mulVec_eq ha hs hx
  have hε0 := C.ε_nonneg
  induction j with
  | zero =>
    rw [C.x_zero, C.r_zero, Matrix.mulVec_zero, sub_zero, sub_self, WithLp.toLp_zero, norm_zero,
      sub_zero, Finset.sum_range_zero]
    push_cast
    constructor <;> linarith
  | succ j ih =>
    have hjk : j < k := by omega
    obtain ⟨hG, hQ⟩ := ih hjk.le
    obtain ⟨hjT, hj2T, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le_of_le ha hs hsmall hjk.le
    set u := ‖WithLp.toLp 2 C.b‖ ^ 2 / a with hu
    have hu0 : 0 ≤ u := by positivity
    have hS0 : 0 ≤ ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 := Finset.sum_nonneg fun i hi =>
      mul_nonneg (C.γ_pos (by have := Finset.mem_range.mp hi; omega)).le (sq_nonneg _)
    have hQ2 : quadForm C.A (xs - C.x j) ≤ 2 * u := by
      have : 25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * u ≤ 25 / 10 ^ 5 * u := by
        have := mul_le_mul_of_nonneg_right hj2T hu0
        linarith
      linarith
    refine ⟨C.acc_gap_step ha hs hsmall hx hjk hG hQ2, ?_⟩
    have hγ := C.γ_pos hjk
    have h1 := C.p_dotProduct_r_ge ha hs hsmall hjk
    have h2 := C.γ_sq_mul_dotProduct_mulVec_le ha hs hsmall hjk
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * C.γ j)
    have h := C.acc_err_step ha hs hsmall hx hjk (c := 99 / 100) (by norm_num)
      (by nlinarith) hG hQ2
    rw [Finset.sum_range_succ]
    have hT : 0 ≤ C.ε * (a' / a) * u := by
      have := (C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall).2.1
      have : 0 ≤ a' / a := by linarith
      positivity
    have e : 25 * (((j + 1 : ℕ) : ℝ)) ^ 2 * C.ε * (a' / a) * u =
        25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * u + (50 * j + 25) * (C.ε * (a' / a) * u) := by
      push_cast
      ring
    have e2 : (36 * (j : ℝ) + 19) * (C.ε * (a' / a)) * u =
        (36 * j + 19) * (C.ε * (a' / a) * u) := by ring
    have hjj : (36 * (j : ℝ) + 19) * (C.ε * (a' / a) * u) ≤
        (50 * j + 25) * (C.ε * (a' / a) * u) :=
      mul_le_mul_of_nonneg_right (by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith) hT
    rw [e]
    linarith

/-- **The residual gap, a priori, in $\|\mathbf{b}\|$**: for a $k$-step CG run with spectrum in
$[a,a']$, $a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $j \le k$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j\| \le 12\,j\,\varepsilon\,\kappa\,
\|\mathbf{b}\| .$$
No solution is needed in the statement.
No printed source.
Result: cg-residual-gap -/
theorem norm_sub_mulVec_x_sub_r_le_norm_b {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  have hherm := C.isHermitian
  have hPD : C.A.PosDef := hherm.posDef_of_spectrum_subset_Icc ha hs
  have hx : C.A *ᵥ (C.A⁻¹ *ᵥ C.b) = C.b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hPD.isUnit), Matrix.one_mulVec]
  exact (C.gapErrorInduction ha hs hsmall hx hj).1

/-- **The computed estimator bounds the computed run's error decrease (one-sided ER3)**: under
(H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j \le k$,
$$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le \|\mathbf{x}_\star\|_{\mathbf{A}}^2 -
0.99\sum_{i<j}\gamma_i\|\mathbf{r}_i\|^2 + 25\,j^2\varepsilon\kappa\,\frac{\|\mathbf{b}\|^2}{a}
\,.$$
The exact relation, for the model, is `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_eq`; this
is the computed run's own error. -/
theorem quadForm_sub_x_le_sub_sum {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤ quadForm C.A xs -
      99 / 100 * ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 +
        25 * j ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have h := (C.gapErrorInduction ha hs hsmall hx hj).2
  linarith

/-- **The computed run's $\mathbf{A}$-norm error, a priori**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j \le k$,
$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le
1.001\,\|\mathbf{x}_\star\|_{\mathbf{A}}^2$. -/
theorem quadForm_sub_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤ (1 + 1 / 1000) * quadForm C.A xs := by
  have h := (C.gapErrorInduction ha hs hsmall hx hj).2
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  obtain ⟨-, -, hj2⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le_of_le ha hs hsmall hj
  have hge := C.norm_b_sq_div_le_mul_quadForm_of_mulVec_eq ha hs hx
  have hε0 := C.ε_nonneg
  have hQ0 : 0 ≤ quadForm C.A xs := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs xs)
  have hS0 : 0 ≤ ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 := Finset.sum_nonneg fun i hi =>
    mul_nonneg (C.γ_pos (by have := Finset.mem_range.mp hi; omega)).le (sq_nonneg _)
  have h1 : 25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) ≤
      25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * (a' / a * quadForm C.A xs) :=
    mul_le_mul_of_nonneg_left hge (by positivity)
  have h2 : 25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * (a' / a * quadForm C.A xs) =
      25 * ((j : ℝ) ^ 2 * C.ε * (a' / a) ^ 2) * quadForm C.A xs := by ring
  have h3 : 25 * ((j : ℝ) ^ 2 * C.ε * (a' / a) ^ 2) * quadForm C.A xs ≤
      25 * (1 / 10 ^ 5) * quadForm C.A xs := by gcongr
  linarith

/-- For a successful run with spectrum in $[a,a']$, $a>0$ and
$k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$, the physical energy decreases by the
computed decrement, up to precision-dependent local errors. Here
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ and $j<k$. -/
theorem quadForm_sub_x_succ_le_sub_add {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    quadForm C.A (xs - C.x (j + 1)) ≤ quadForm C.A (xs - C.x j) -
      (C.γ j * C.ρ j ^ 2) + (52 * j + 6) * (C.ε * (a' / a)) *
        (C.γ j * C.ρ j ^ 2) +
      (36 * j + 19) * (C.ε * (a' / a)) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hγ := C.γ_pos hj
  have h1 := C.p_dotProduct_r_ge_mul ha hs hsmall hj
  have h2 := C.γ_sq_mul_dotProduct_mulVec_le_mul ha hs hsmall hj
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * C.γ j)
  have hz := C.acc_εκ ha hs hsmall
  have hjz := (C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le_of_le ha hs hsmall hj.le).1
  have hc : 0 ≤ 1 - (52 * (j : ℝ) + 6) * (C.ε * (a' / a)) := by nlinarith
  have hQ := C.quadForm_sub_x_le ha hs hsmall hx hj.le
  have hQ0 := C.quadForm_le_norm_b_sq_div_of_mulVec_eq ha hs hx
  have hu : 0 ≤ ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by positivity
  have h := C.acc_err_step ha hs hsmall hx hj hc (by nlinarith)
    (C.norm_sub_mulVec_x_sub_r_le_norm_b ha hs hsmall hj.le) (by linarith)
  nlinarith

/-- **The computed iterates, a priori**: under (H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$
and $j \le k$,
$$\|\mathbf{x}_j\| \le 1.001\Bigl(\|\mathbf{x}_\star\| +
\frac{\|\mathbf{x}_\star\|_{\mathbf{A}}}{\sqrt{a}}\Bigr) ,$$
the exact-arithmetic bound on $\max_j\|\mathbf{x}_j\|$ through the $\mathbf{A}$-norm.
[MeurantStrakos2006, §5.4] assert $\|\mathbf{x}_j\| \le 2\|\mathbf{x}_\star\|$ "to within a
small error" for finite-precision CG without proof; this is $\sqrt{\kappa}$ weaker and proved. -/
theorem norm_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (C.x j)‖ ≤
      (1 + 1 / 1000) * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have hQ := C.quadForm_sub_x_le ha hs hsmall hx hj
  have hQ0 : 0 ≤ quadForm C.A xs := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs xs)
  have he2 := C.acc_norm_sq_le ha hs (xs - C.x j)
  set M := Real.sqrt (quadForm C.A xs) / Real.sqrt a
  have hM0 : 0 ≤ M := by positivity
  have hM2 : M ^ 2 = quadForm C.A xs / a := by
    rw [div_pow, Real.sq_sqrt hQ0, Real.sq_sqrt ha.le]
  have he : ‖WithLp.toLp 2 (xs - C.x j)‖ ≤ (1 + 1 / 1000) * M := by
    have h : ‖WithLp.toLp 2 (xs - C.x j)‖ ^ 2 ≤ ((1 + 1 / 1000) * M) ^ 2 := by
      rw [mul_pow, hM2]
      refine he2.trans ?_
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ ha.le
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  have h := norm_sub_le (WithLp.toLp 2 xs) (WithLp.toLp 2 (xs - C.x j))
  rw [← WithLp.toLp_sub, sub_sub_cancel] at h
  have := norm_nonneg (WithLp.toLp 2 xs)
  nlinarith

/-- The error of the computed iterate, a priori:
$\|\mathbf{x}_\star - \mathbf{x}_j\| \le 1.001\|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$. -/
private theorem acc_norm_sub_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (xs - C.x j)‖ ≤
      (1 + 1 / 1000) * (Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have hQ := C.quadForm_sub_x_le ha hs hsmall hx hj
  have hQ0 : 0 ≤ quadForm C.A xs := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs xs)
  have he2 := C.acc_norm_sq_le ha hs (xs - C.x j)
  have hM2 : (Real.sqrt (quadForm C.A xs) / Real.sqrt a) ^ 2 = quadForm C.A xs / a := by
    rw [div_pow, Real.sq_sqrt hQ0, Real.sq_sqrt ha.le]
  have h : ‖WithLp.toLp 2 (xs - C.x j)‖ ^ 2 ≤
      ((1 + 1 / 1000) * (Real.sqrt (quadForm C.A xs) / Real.sqrt a)) ^ 2 := by
    rw [mul_pow, hM2]
    refine he2.trans ?_
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- $a\|\mathbf{v}\| \le \|\mathbf{A}\mathbf{v}\|$. -/
private theorem acc_mul_norm_le {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : a * ‖WithLp.toLp 2 v‖ ≤ ‖WithLp.toLp 2 (C.A *ᵥ v)‖ := by
  have h1 := (C.mul_norm_sq_le_quadForm hs v)
  rw [C.quadForm_eq_dotProduct_mulVec] at h1
  have h2 := (le_abs_self _).trans (EuclideanSpace.abs_dotProduct_le_norm v (C.A *ᵥ v))
  rcases (norm_nonneg (WithLp.toLp 2 v)).lt_or_eq with hpos | hzero
  · exact le_of_mul_le_mul_left (by nlinarith) hpos
  · rw [← hzero, mul_zero]
    exact norm_nonneg _

/-- $\|\mathbf{b}\| \le a'\|\mathbf{x}_\star\|$. -/
private theorem acc_norm_b_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) : ‖WithLp.toLp 2 C.b‖ ≤ a' * ‖WithLp.toLp 2 xs‖ := by
  rw [← hx]
  exact (norm_toLp_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_right (C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall).2.2.1
      (norm_nonneg _))

/-! ### The residual gap -/

/-- **The residual gap, a priori**: for a $k$-step CG run with spectrum in $[a,a']$, $a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$,
with $M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k - \mathbf{r}_k\| \le 11\,k\,\varepsilon\,a'M .$$
[Greenbaum1997SIMAX]; [StrakosTichy2002, (7.16)], there with $\|\mathbf{x}_\star\| +
\max_j\|\mathbf{x}_j\|$ (a posteriori) and $+O(\varepsilon^2)$; here
$\max_j\|\mathbf{x}_j\| \le 1.001M$ is proved (`NLAlib.CGRun.norm_x_le`).
Result: cg-residual-gap -/
theorem norm_sub_mulVec_x_sub_r_le_energy {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      11 * k * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  obtain ⟨haa', hκ, hspec, hε5, hkεκ, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hε1 := C.ε_le
  set M := ‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a with hM
  have hxs0 := norm_nonneg (WithLp.toLp 2 xs)
  have hM' : Real.sqrt (quadForm C.A xs) / Real.sqrt a ≤ M := by linarith
  have hxsM : ‖WithLp.toLp 2 xs‖ ≤ M := by
    have : 0 ≤ Real.sqrt (quadForm C.A xs) / Real.sqrt a := by positivity
    linarith
  have hM0 : 0 ≤ M := by positivity
  have ha' : 0 ≤ a' := by linarith
  have hB := C.acc_norm_b_le ha hs hsmall hx
  have hterm : ∀ j < k, specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
      4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j ≤ 11 * (a' * M) := fun j hj => by
    have hxj := C.norm_x_le ha hs hsmall hx hj.le
    have hxj1 := C.norm_x_le ha hs hsmall hx (j := j + 1) hj
    have hγ := C.γ_pos hj
    -- the step through the iterate update
    have hγp : C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 201 / 100 * M := by
      have hid : C.γ j • C.p j = C.x (j + 1) - C.x j - C.ex j := by
        rw [C.x_succ j hj]
        abel
      have h1 : C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ ‖WithLp.toLp 2 (C.x (j + 1))‖ +
          ‖WithLp.toLp 2 (C.x j)‖ + ‖WithLp.toLp 2 (C.ex j)‖ := by
        have := norm_sub_le (WithLp.toLp 2 (C.x (j + 1) - C.x j)) (WithLp.toLp 2 (C.ex j))
        have h2 := norm_sub_le (WithLp.toLp 2 (C.x (j + 1))) (WithLp.toLp 2 (C.x j))
        rw [← WithLp.toLp_sub, ← hid, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos hγ] at this
        rw [← WithLp.toLp_sub] at h2
        linarith
      have h3 := C.norm_ex_le j hj
      rw [abs_of_pos hγ] at h3
      have h4 : C.ε * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) ≤ 1 / 10 ^ 5 *
          (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) :=
        mul_le_mul_of_nonneg_right hε5 (by positivity)
      have h5 : C.ε * ‖WithLp.toLp 2 (C.x j)‖ ≤ 1 / 10 ^ 5 * ((1 + 1 / 1000) * M) :=
        mul_le_mul hε5 hxj (norm_nonneg _) (by norm_num)
      nlinarith
    -- the residual through the true residual and the gap
    have hρ : C.ρ j ≤ 1002 / 1000 * (a' * M) := by
      have he := C.acc_norm_sub_x_le ha hs hsmall hx hj.le
      have hG := C.norm_sub_mulVec_x_sub_r_le_norm_b ha hs hsmall hj.le
      have hid : C.r j = C.A *ᵥ (xs - C.x j) - (C.b - C.A *ᵥ C.x j - C.r j) := by
        rw [Matrix.mulVec_sub, hx]
        abel
      have h := norm_sub_le (WithLp.toLp 2 (C.A *ᵥ (xs - C.x j)))
        (WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j))
      rw [← WithLp.toLp_sub, ← hid] at h
      have hAe : ‖WithLp.toLp 2 (C.A *ᵥ (xs - C.x j))‖ ≤ a' * ((1 + 1 / 1000) * M) :=
        (norm_toLp_mulVec_le _ _).trans (mul_le_mul hspec (he.trans (by nlinarith))
          (norm_nonneg _) ha')
      have hjT : (j : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
        (C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le_of_le ha hs hsmall hj.le).1
      have hG' : 12 * (j : ℝ) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ ≤
          12 * (1 / 10 ^ 5) * (a' * M) := by
        have : 12 * (j : ℝ) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ =
            12 * ((j : ℝ) * C.ε * (a' / a)) * ‖WithLp.toLp 2 C.b‖ := by ring
        rw [this]
        exact mul_le_mul (by linarith) (hB.trans (mul_le_mul_of_nonneg_left hxsM ha'))
          (norm_nonneg _) (by norm_num)
      change ‖WithLp.toLp 2 (C.r j)‖ ≤ _
      nlinarith
    have h1 : ‖WithLp.toLp 2 (C.x j)‖ + 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 905 / 100 * M := by
      nlinarith
    have h2 := mul_le_mul hspec h1 (by positivity) ha'
    nlinarith
  refine (C.norm_sub_mulVec_x_sub_r_le).trans ?_
  have hsum : ∑ j ∈ Finset.range k, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
      4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) ≤ k * (11 * (a' * M)) := by
    have := Finset.sum_le_sum fun j (hj : j ∈ Finset.range k) => hterm j (Finset.mem_range.mp hj)
    simpa using this
  calc C.ε * ∑ j ∈ Finset.range k, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
        4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) ≤ C.ε * (k * (11 * (a' * M))) :=
        mul_le_mul_of_nonneg_left hsum hε0
    _ = _ := by ring

/-- **The residual gap, a priori, in $\|\mathbf{x}_\star\|$**: for a $k$-step CG run with spectrum
in $[a,a']$, $a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k - \mathbf{r}_k\| \le 22\,k\,\varepsilon\sqrt{\kappa}\,
a'\|\mathbf{x}_\star\| .$$
$\sqrt{\kappa}$ worse than the folklore $O(k\varepsilon)a'\|\mathbf{x}_\star\|$, which rests on
a Euclidean monotonicity of the errors not known in finite precision.
No printed source.
Result: cg-residual-gap -/
theorem norm_sub_mulVec_x_sub_r_le_norm_sol {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      22 * k * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by
  have h := C.norm_sub_mulVec_x_sub_r_le_energy ha hs hsmall hx
  obtain ⟨haa', hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have ha' : 0 ≤ a' := by linarith
  have hQ := (C.quadForm_le_mul_norm_sq hs xs)
  have hs1 : 1 ≤ Real.sqrt (a' / a) := by rw [Real.one_le_sqrt]; exact hκ
  have hxs0 := norm_nonneg (WithLp.toLp 2 xs)
  have hq : Real.sqrt (quadForm C.A xs) ≤ Real.sqrt a' * ‖WithLp.toLp 2 xs‖ := by
    rw [← Real.sqrt_sq hxs0, ← Real.sqrt_mul ha']
    exact Real.sqrt_le_sqrt hQ
  have h1 : Real.sqrt (quadForm C.A xs) / Real.sqrt a ≤
      Real.sqrt (a' / a) * ‖WithLp.toLp 2 xs‖ := by
    rw [Real.sqrt_div' a' ha.le, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hq (Real.sqrt_nonneg _)
  have h2 : ‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a ≤
      2 * Real.sqrt (a' / a) * ‖WithLp.toLp 2 xs‖ := by nlinarith
  refine h.trans ?_
  have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 11 * (k : ℝ) * C.ε * a')
  linarith

/-- **The true residual**: for a $k$-step CG run with spectrum in $[a,a']$, $a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$, with
$\kappa' = 2\kappa + 1$, $q = (\sqrt{\kappa'} - 1)/(\sqrt{\kappa'} + 1)$ and
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le 2\sqrt{\kappa'}\,q^k\|\mathbf{b}\| +
11\,k\,\varepsilon\,a'M .$$
No printed source.
Result: cg-finite-precision-accuracy -/
theorem norm_sub_mulVec_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      2 * Real.sqrt (2 * (a' / a) + 1) *
          ((Real.sqrt (2 * (a' / a) + 1) - 1) / (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ k *
          ‖WithLp.toLp 2 C.b‖ +
        11 * k * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have hid : C.b - C.A *ᵥ C.x k = C.r k + (C.b - C.A *ᵥ C.x k - C.r k) := by abel
  rw [hid, WithLp.toLp_add]
  refine (norm_add_le _ _).trans ?_
  have h1 := C.ρ_le_chebyshev ha hs hsmall le_rfl
  have h2 := C.norm_sub_mulVec_x_sub_r_le_energy ha hs hsmall hx
  change C.ρ k + _ ≤ _
  linarith

/-! ### Attainable accuracy -/

private theorem acc_norm_true_le (j : ℕ) : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j)‖ ≤
    C.ρ j + ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ := by
  set g := C.b - C.A *ᵥ C.x j - C.r j with hg
  have hid : C.b - C.A *ᵥ C.x j = C.r j + g := by rw [hg]; abel
  rw [hid, WithLp.toLp_add]
  exact norm_add_le _ _

/-- **The computed residual at gap level**: for a $k$-step CG run with spectrum in $[a,a']$, $a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $\varepsilon, \delta > 0$ and
$k_\star(\kappa, \varepsilon, \delta) \le j \le k$ (`NLAlib.cgKStar`),
$\|\mathbf{r}_j\| \le 8\delta\varepsilon\|\mathbf{b}\|$. With $\delta = 1$ this is the level of
the a priori gap scale. Smaller $\delta$ gives a smaller
upper bound on the computed residual, but the increased $k_\star$ must still fit the stated
horizon. This does not assert monotonicity, infinite-horizon convergence, or a nonzero gap.
No printed source.
Result: cg-computed-residual-bound -/
theorem ρ_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) (hε : 0 < C.ε) {δ : ℝ}
    (hδ : 0 < δ) {j : ℕ} (hkj : cgKStar (a' / a) C.ε δ ≤ j) (hj : j ≤ k) :
    C.ρ j ≤ 8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖ := by
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have h1 := C.ρ_le_chebyshev ha hs hsmall hj
  have h2 := pow_le_of_cgKStar_le (by linarith : 0 ≤ a' / a) hε hδ hkj
  set s := Real.sqrt (2 * (a' / a) + 1) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hB := norm_nonneg (WithLp.toLp 2 C.b)
  have e : 2 * s * (4 * δ * C.ε / s) = 8 * δ * C.ε := by field_simp; ring
  calc C.ρ j ≤ _ := h1
    _ ≤ 2 * s * (4 * δ * C.ε / s) * ‖WithLp.toLp 2 C.b‖ := by gcongr
    _ = 8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖ := by rw [e]

/-- **Past $k_\star(\delta)$ the true residual is the gap** up to $\delta$ times the gap's
level: for a $k$-step CG run with spectrum in $[a,a']$, $a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $\varepsilon, \delta > 0$ and
$k_\star(\kappa, \varepsilon, \delta) \le j
\le k$,
$$\bigl\lvert\|\mathbf{b} - \mathbf{A}\mathbf{x}_j\| -
\|\mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j\|\bigr\rvert \le
8\delta\varepsilon\|\mathbf{b}\| .$$
No printed source.
Result: cg-residual-gap -/
theorem abs_norm_sub_mulVec_x_sub_norm_gap_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    (hε : 0 < C.ε) {δ : ℝ} (hδ : 0 < δ) {j : ℕ} (hkj : cgKStar (a' / a) C.ε δ ≤ j)
    (hj : j ≤ k) :
    |‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j)‖ - ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖| ≤
      8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖ := by
  have h := C.ρ_le_of_cgKStar_le ha hs hsmall hε hδ hkj hj
  set g := C.b - C.A *ᵥ C.x j - C.r j with hg
  have hid : C.b - C.A *ᵥ C.x j = C.r j + g := by rw [hg]; abel
  rw [hid, WithLp.toLp_add]
  have := abs_norm_sub_norm_le (WithLp.toLp 2 (C.r j) + WithLp.toLp 2 g) (WithLp.toLp 2 g)
  rw [add_sub_cancel_right] at this
  exact this.trans h

/-- **Attainable accuracy at a prescribed step**: for a $k$-step CG run with spectrum in $[a,a']$,
$a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k_\star(\kappa, \varepsilon, 1)$, with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (11k + 8)\,\varepsilon\,a'M .$$
The bound grows linearly in $k$: the iterate-update contribution to the gap is not bounded
by the decaying computed residual (as in [Greenbaum1997SIMAX]). The bound is smallest at
$k_\star$ (`NLAlib.CGRun.norm_sub_mulVec_x_cgKStar_le`); this does not identify the iterate
with the smallest actual error. Related attainable-accuracy bounds appear in
[BakeCarsonMa2025, Theorem 2], for mixed-precision PCG at some iterate up to a conditional
existential index; here the step is prescribed and the finite-horizon condition is explicit.
Result: cg-finite-precision-accuracy -/
theorem norm_sub_mulVec_x_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    (hε : 0 < C.ε) {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      (11 * k + 8) * C.ε * a' *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have h1 := C.acc_norm_true_le k
  have h2 := C.ρ_le_of_cgKStar_le ha hs hsmall hε one_pos hk le_rfl
  have h3 := C.norm_sub_mulVec_x_sub_r_le_energy ha hs hsmall hx
  have hB := C.acc_norm_b_le ha hs hsmall hx
  have ha' : 0 ≤ a' := ha.le.trans (C.le_of_spectrum_subset_Icc hs)
  have hM : ‖WithLp.toLp 2 xs‖ ≤
      ‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a := by
    have : 0 ≤ Real.sqrt (quadForm C.A xs) / Real.sqrt a := by positivity
    linarith
  have h4 : 8 * 1 * C.ε * ‖WithLp.toLp 2 C.b‖ ≤
      8 * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
    have := mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_left hM ha'))
      (by have := C.ε_nonneg; positivity : (0 : ℝ) ≤ 8 * C.ε)
    linarith
  have e : (11 * (k : ℝ) + 8) * C.ε * a' *
      (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) =
      11 * k * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) +
        8 * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
    ring
  rw [e]
  linarith

/-- **Attainable accuracy in $\|\mathbf{x}_\star\|$**: for a $k$-step CG run with spectrum in
$[a,a']$, $a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k_\star(\kappa, \varepsilon, 1)$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (22k + 8)\,\varepsilon\sqrt{\kappa}\,a'
\|\mathbf{x}_\star\| .$$
No printed source.
Result: cg-finite-precision-accuracy -/
theorem norm_sub_mulVec_x_le_norm_sol_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    (hε : 0 < C.ε) {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      (22 * k + 8) * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have h1 := C.acc_norm_true_le k
  have h2 := C.ρ_le_of_cgKStar_le ha hs hsmall hε one_pos hk le_rfl
  have h3 := C.norm_sub_mulVec_x_sub_r_le_norm_sol ha hs hsmall hx
  have hB := C.acc_norm_b_le ha hs hsmall hx
  have ha' : 0 ≤ a' := ha.le.trans (C.le_of_spectrum_subset_Icc hs)
  have hs1 : 1 ≤ Real.sqrt (a' / a) := by rw [Real.one_le_sqrt]; exact hκ
  have h4 : 8 * 1 * C.ε * ‖WithLp.toLp 2 C.b‖ ≤
      8 * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by
    have h5 : a' * ‖WithLp.toLp 2 xs‖ ≤ Real.sqrt (a' / a) * (a' * ‖WithLp.toLp 2 xs‖) :=
      le_mul_of_one_le_left (by positivity) hs1
    have := mul_le_mul_of_nonneg_left (hB.trans h5)
      (by have := C.ε_nonneg; positivity : (0 : ℝ) ≤ 8 * C.ε)
    linarith
  have e : (22 * (k : ℝ) + 8) * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ =
      22 * k * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ +
        8 * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by ring
  rw [e]
  linarith

/-- **Attainable accuracy in $\|\mathbf{b}\|$**: for a $k$-step CG run with spectrum in $[a,a']$,
$a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $\varepsilon > 0$ and
$k \ge k_\star(\kappa, \varepsilon, 1)$,
$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (12k + 8)\,\varepsilon\,\kappa\,\|\mathbf{b}\|$.
No printed source.
Result: cg-finite-precision-accuracy -/
theorem norm_sub_mulVec_x_le_norm_b_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    (hε : 0 < C.ε) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤ (12 * k + 8) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have h1 := C.acc_norm_true_le k
  have h2 := C.ρ_le_of_cgKStar_le ha hs hsmall hε one_pos hk le_rfl
  have h3 := C.norm_sub_mulVec_x_sub_r_le_norm_b ha hs hsmall le_rfl
  have hB := norm_nonneg (WithLp.toLp 2 C.b)
  have h4 : 8 * 1 * C.ε * ‖WithLp.toLp 2 C.b‖ ≤ 8 * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
    have h5 : C.ε * ‖WithLp.toLp 2 C.b‖ ≤ (a' / a) * (C.ε * ‖WithLp.toLp 2 C.b‖) :=
      le_mul_of_one_le_left (by have := C.ε_nonneg; positivity) hκ
    linarith
  have e : (12 * (k : ℝ) + 8) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ =
      12 * k * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ +
        8 * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by ring
  rw [e]
  linarith

/-- **The forward error at a prescribed step**: for a $k$-step CG run with spectrum in $[a,a']$,
$a>0$,
$\kappa=a'/a$ and $k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k_\star(\kappa, \varepsilon, 1)$, with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$\|\mathbf{x}_\star - \mathbf{x}_k\| \le (11k + 8)\,\varepsilon\,\kappa\,M$.
No printed source.
Result: cg-finite-precision-accuracy -/
theorem norm_sub_x_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) (hε : 0 < C.ε)
    {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (xs - C.x k)‖ ≤
      (11 * k + 8) * C.ε * (a' / a) *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have h := C.norm_sub_mulVec_x_le_of_cgKStar_le ha hs hsmall hε hx hk
  have h1 := C.acc_mul_norm_le hs (xs - C.x k)
  rw [Matrix.mulVec_sub, hx] at h1
  rw [← div_le_div_iff_of_pos_right ha] at h1
  rw [mul_div_cancel_left₀ _ ha.ne'] at h1
  refine h1.trans ?_
  rw [div_le_iff₀ ha]
  have e : (11 * (k : ℝ) + 8) * C.ε * (a' / a) *
      (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) * a =
      (11 * k + 8) * C.ε * a' *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
    field_simp
  rw [e]
  exact h

/-- **Attainable accuracy, a priori**: for a CG run with spectrum in $[a,a']$, $a>0$,
$\kappa=a'/a$, $\varepsilon > 0$, $\mathbf{A}\mathbf{x}_\star =\mathbf{b}$,
$k \ge k_\star = k_\star(\kappa, \varepsilon, 1)$ and the horizon condition **at $k_\star$ only**,
$(k_\star)^2\sqrt{k_\star}\,\varepsilon\kappa^2 \le 10^{-5}$, with $\kappa' = 2\kappa + 1$,
$\ell = \ln(\sqrt{\kappa'}/(4\varepsilon))$ and
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_{k_\star}\| \le
\Bigl(\frac{11}{2}(\sqrt{\kappa'} + 1)\,\ell + 19\Bigr)\varepsilon\,a'M ,$$
an attainable relative residual of order $\kappa\ln(1/\varepsilon)\,\varepsilon$ (one
$\sqrt{\kappa}$ from $M \le (1 + \sqrt{\kappa})\|\mathbf{x}_\star\|$, one from
$k_\star \propto \sqrt{\kappa}$). `NLAlib.cgKStar_cube_mul_le` gives a stronger sufficient
condition at $k_\star$ from $\kappa^{7/2}\varepsilon\ell^3 \le 7 \cdot 10^{-7}$.
No printed source.
Result: cg-finite-precision-accuracy -/
theorem norm_sub_mulVec_x_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hε : 0 < C.ε) (hk : cgKStar (a' / a) C.ε 1 ≤ k)
    (hsmall : CGPrecisionHorizon (cgKStar (a' / a) C.ε 1) C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x (cgKStar (a' / a) C.ε 1))‖ ≤
      (11 / 2 * (Real.sqrt (2 * (a' / a) + 1) + 1) *
          Real.log (Real.sqrt (2 * (a' / a) + 1) / (4 * 1 * C.ε)) + 19) * C.ε * a' *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have haa' := C.le_of_spectrum_subset_Icc hs
  have ha' : 0 ≤ a' := ha.le.trans haa'
  have hκ0 : 0 ≤ a' / a := div_nonneg ha' ha.le
  have hε1 := C.ε_le
  set K := cgKStar (a' / a) C.ε 1 with hKdef
  have hK0 : 0 < K := cgKStar_pos hκ0 hε hε1 one_pos le_rfl
  set M := ‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a with hM
  have h : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x K)‖ ≤ (11 * K + 8) * C.ε * a' * M :=
    (C.take K hK0 hk).norm_sub_mulVec_x_le_of_cgKStar_le ha hs hsmall hε hx le_rfl
  set s := Real.sqrt (2 * (a' / a) + 1) with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; linarith
  set ℓ := Real.log (s / (4 * 1 * C.ε)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith)
  have hK : (K : ℝ) ≤ (s + 1) / 2 * ℓ + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (s + 1) / 2 * ℓ)).le
  have hM0 : 0 ≤ M := by positivity
  have hεaM : 0 ≤ C.ε * a' * M := by positivity
  refine h.trans ?_
  have e1 : (11 * (K : ℝ) + 8) * C.ε * a' * M = (11 * K + 8) * (C.ε * a' * M) := by ring
  have e2 : (11 / 2 * (s + 1) * ℓ + 19) * C.ε * a' * M =
      (11 / 2 * (s + 1) * ℓ + 19) * (C.ε * a' * M) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by linarith) hεaM

end CGRun

end NLAlib
