/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosPrecision
public import NLAlib.Krylov.FinitePrecision.LanczosReorthRun
public import NLAlib.Matrix.FinitePrecision.ClassicalGramSchmidt
public import NLAlib.ForMathlib.Analysis.Real.Sqrt

/-!
# Precision regimes for two-pass reorthogonalized Lanczos

Pure coefficient indexing and parameter inequalities relate the ordinary Lanczos budget to
classical two-pass orthogonalization. No store, execution or program contract is assumed.

## Main results

* `NLAlib.lanczosCoeffTridiagonal` forms the coefficient tridiagonal matrix.
* `NLAlib.LanczosReorthRegime` specifies the generic orthogonalization regime.
* `NLAlib.lanczosReorthRoundoffBound` is the two-pass budget,
  shown by <!-- value lanczosReorthRoundoffBound N q u -->
  $$(101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$
* `NLAlib.lanczosReorthRegime_cgsPassBound` derives the regime from that budget.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix
open Computation

/-- The **symmetric tridiagonal matrix of coefficients** $\alpha$, $\beta$ has entries
$$\mathsf{lanczosCoeffTridiagonal}(\alpha,\beta,k)_{ij}:=
\begin{cases}
\alpha_{i+1} & i=j,\\
\beta_i & i=j+1,\\
\beta_j & j=i+1,\\
0 & \text{otherwise}
\end{cases}
\qquad(0\le i,j<k).$$
This is the coefficient indexing of `NLAlib.LanczosData.tridiagonal`. -/
def lanczosCoeffTridiagonal (α β : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then α ((i : ℕ) + 1)
    else if (i : ℕ) = j + 1 then β i
    else if (j : ℕ) = i + 1 then β j
    else 0

/-- **The parameter regime of Lanczos with full reorthogonalization** for $q$ steps, local
accuracy $\varepsilon$, threshold $\tau$ and an orthogonalization scheme certified at
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$: with the per-column orthogonality level
$\mu = 2(\varepsilon_1 + \varepsilon_3/\tau + \varepsilon)$, it asks $\eta_0 \le 1/100$,
$\tau \le 1$, the fixed-point condition $\sqrt{3(q+1)}\,\mu \le \eta_0$ and
$\mu + \varepsilon + \varepsilon_2 \le 1/100$. It involves the parameters only. -/
def LanczosReorthRegime (q : ℕ) (ε τ η₀ ε₁ ε₂ ε₃ : ℝ) : Prop :=
  η₀ ≤ 1 / 100 ∧ τ ≤ 1 ∧ Real.sqrt (3 * ((q : ℝ) + 1)) * (2 * (ε₁ + ε₃ / τ + ε)) ≤ η₀ ∧
    2 * (ε₁ + ε₃ / τ + ε) + ε + ε₂ ≤ 1 / 100


/-- **The CGS2 budget of Lanczos with full reorthogonalization** for $q$ steps of length $N$
at unit roundoff $u$: twice the coefficient of one rounded CGS pass at $\eta_0 = 1/100$ plus the
local budget of the Lanczos implementation, shown
by <!-- value lanczosReorthRoundoffBound N q u -->
$$(101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$ -/
noncomputable irreducible_def lanczosReorthRoundoffBound (N q : ℕ) (u : ℝ) : ℝ :=
  101 / 25 * Real.sqrt ((q : ℝ) + 1) * ((N + q + 2 : ℕ) : ℝ) * u + 16 * ((N : ℝ) + 1) ^ 2 * u

/-- For dimension $N$, $q$ steps and nonnegative unit roundoff $u$, the CGS2 budget
is nonnegative. Its current value is <!-- value lanczosReorthRoundoffBound N q u -->
$$(101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$
No printed source. -/
theorem lanczosReorthRoundoffBound_nonneg (N q : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ lanczosReorthRoundoffBound N q u := by
  rw [lanczosReorthRoundoffBound_def]
  positivity

/-- The CGS2 budget for dimension $N$, $q$ steps and roundoff parameter $u$ is at
most <!-- value lanczosReorthRoundoffBound N q u -->
$$(101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$
No printed source. -/
theorem lanczosReorthRoundoffBound_le (N q : ℕ) (u : ℝ) :
    lanczosReorthRoundoffBound N q u ≤
      101 / 25 * Real.sqrt ((q : ℝ) + 1) * ((N + q + 2 : ℕ) : ℝ) * u + 16 * ((N : ℝ) + 1) ^ 2 * u :=
  (lanczosReorthRoundoffBound_def N q u).le

/-- The budget is the sum of its two parts. -/
private theorem lanczosReorthRoundoffBound_eq (N q : ℕ) (u : ℝ) :
    lanczosReorthRoundoffBound N q u =
      2 * cgsPassBound N q u (1 / 100) + lanczosImplementationRoundoffBound N u := by
  rw [lanczosReorthRoundoffBound_def, cgsPassBound_def, lanczosImplementationRoundoffBound_def]
  ring

/-- The arithmetic of the CGS2 regime: with $\rho$ the CGS2 budget, $(q+1)\rho \le 1/1000$,
$132(q+1)\rho \le \tau$, $\tau > 0$, $\eta_0 = 4\sqrt{3(q+1)}\,\rho$ and $c_1$ the pass
coefficient at $\eta_0$: the hypotheses of the CGS2 run,
$\mu = 2(2c_1 + 2(\eta_0 + c_1)^2/\tau + \varepsilon) \le 4\rho$ and
$\varepsilon + 3c_1 \le (3/2)\rho$. -/
theorem cgs2_regime_bounds {N q : ℕ} {u τ η₀ : ℝ} (hu : 0 ≤ u)
    (hsmall : ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ 1 / 1000)
    (hτ : 0 < τ) (hτlo : 132 * ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ τ)
    (hη₀ : η₀ = 4 * Real.sqrt (3 * ((q : ℝ) + 1)) * lanczosReorthRoundoffBound N q u) :
    0 ≤ η₀ ∧ η₀ ≤ 1 / 100 ∧ ((N + q + 2 : ℕ) : ℝ) * u ≤ 1 / 100 ∧
      cgsPassBound N q u η₀ ≤ 1 / 100 ∧ lanczosImplementationRoundoffBound N u ≤ 1 / 100 ∧
      0 ≤ lanczosReorthRoundoffBound N q u ∧
      lanczosImplementationRoundoffBound N u ≤ lanczosReorthRoundoffBound N q u ∧
      2 * (2 * cgsPassBound N q u η₀ + 2 * (η₀ + cgsPassBound N q u η₀) ^ 2 / τ +
        lanczosImplementationRoundoffBound N u) ≤ 4 * lanczosReorthRoundoffBound N q u ∧
      lanczosImplementationRoundoffBound N u + 3 * cgsPassBound N q u η₀ ≤
        3 / 2 * lanczosReorthRoundoffBound N q u ∧
      Real.sqrt (3 * ((q : ℝ) + 1)) * (4 * lanczosReorthRoundoffBound N q u) = η₀ := by
  set x : ℝ := (q : ℝ) + 1 with hx
  set ρ := lanczosReorthRoundoffBound N q u with hρ
  set ε := lanczosImplementationRoundoffBound N u with hεd
  set c := cgsPassBound N q u (1 / 100) with hcd
  set c₁ := cgsPassBound N q u η₀ with hc₁d
  set s := Real.sqrt (3 * x) with hs
  have hx1 : 1 ≤ x := by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ≤ 2 * x := (Real.sqrt_three_mul_le hx1).1
  have hε0 : 0 ≤ ε := lanczosImplementationRoundoffBound_nonneg N hu
  have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
  have hM0 : 0 ≤ ((N + q + 2 : ℕ) : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hcM : ((N + q + 2 : ℕ) : ℝ) * u ≤ c := by
    rw [hcd, cgsPassBound_def]
    nlinarith [mul_le_mul_of_nonneg_right hsq1 hM0]
  have hc0 : 0 ≤ c := hM0.trans hcM
  have hρeq : ρ = 2 * c + ε := lanczosReorthRoundoffBound_eq N q u
  have hρ0 : 0 ≤ ρ := lanczosReorthRoundoffBound_nonneg N q hu
  have hρle : ρ ≤ 1 / 1000 := by nlinarith
  have hη0 : 0 ≤ η₀ := by rw [hη₀]; positivity
  have hsρ : s * ρ ≤ 2 * x * ρ := mul_le_mul_of_nonneg_right hs2 hρ0
  have hηle : η₀ ≤ 8 / 1000 := by rw [hη₀]; nlinarith
  have hc₁c : c₁ ≤ c := by
    rw [hc₁d, hcd, cgsPassBound_def, cgsPassBound_def]
    gcongr
    linarith
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁d, cgsPassBound_def]; positivity
  -- $(\eta_0 + c_1)^2 \le (4s\rho + \rho/2)^2 \le 56.25\,x\rho^2$
  have hsum : η₀ + c₁ ≤ 4 * s * ρ + ρ / 2 := by rw [hη₀]; linarith
  have hsq : (η₀ + c₁) ^ 2 ≤ 57 * x * ρ ^ 2 := by
    have hss : s ^ 2 = 3 * x := Real.sq_sqrt (by linarith)
    have h1 := pow_le_pow_left₀ (by positivity) hsum 2
    have h2 : (4 * s * ρ + ρ / 2) ^ 2 = 48 * x * ρ ^ 2 + 4 * (s * ρ) * ρ + ρ ^ 2 / 4 := by
      rw [show (4 * s * ρ + ρ / 2) ^ 2 = 16 * s ^ 2 * ρ ^ 2 + 4 * (s * ρ) * ρ + ρ ^ 2 / 4 by
        ring, hss]
      ring
    have h3 : 4 * (s * ρ) * ρ ≤ 8 * x * ρ ^ 2 := by nlinarith
    have h4 : ρ ^ 2 / 4 ≤ x * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
    nlinarith [sq_nonneg ρ]
  have hdiv : 2 * (η₀ + c₁) ^ 2 / τ ≤ ρ := by
    rw [div_le_iff₀ hτ]
    have := mul_le_mul_of_nonneg_left hτlo hρ0
    nlinarith [sq_nonneg ρ, mul_nonneg (by linarith : (0 : ℝ) ≤ x) (sq_nonneg ρ)]
  refine ⟨hη0, by linarith, by linarith, by linarith, by linarith, hρ0, by linarith,
    by linarith, by linarith, by rw [hη₀]; ring⟩

/-- CGS2 is in the regime: with $\rho$ = `NLAlib.lanczosReorthRoundoffBound` $N\,q\,u$, that
is <!-- value lanczosReorthRoundoffBound N q u -->
$$\rho = (101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u,$$
for $u \ge 0$, $(q+1)\rho \le 1/1000$ and $132(q+1)\rho \le \tau \le 1$,
$\tau > 0$, the CGS2 parameters $(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$ at
$\eta_0 = 4\sqrt{3(q+1)}\,\rho$, $c_1$ = `NLAlib.cgsPassBound` $N\,q\,u\,\eta_0$, that
is <!-- value cgsPassBound N q u \eta_0 -->$2(1+\eta_0)\sqrt{q+1}\,(N+q+2)\,u$, and
$\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound` $N\,u$, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u$, satisfy
`NLAlib.LanczosReorthRegime` for $q$ steps: $\eta_0 \le 1/100$, $\tau \le 1$,
$\sqrt{3(q+1)}\,\mu \le \eta_0$ and $\mu + \varepsilon + 3c_1 \le 1/100$ for
$\mu = 2(2c_1 + 2(\eta_0 + c_1)^2/\tau + \varepsilon)$. No printed source. -/
theorem lanczosReorthRegime_cgsPassBound {N q : ℕ} {u τ η₀ : ℝ} (hu : 0 ≤ u)
    (hsmall : ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ 1 / 1000)
    (hτ : 0 < τ) (hτlo : 132 * ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ τ)
    (hτ1 : τ ≤ 1)
    (hη₀ : η₀ = 4 * Real.sqrt (3 * ((q : ℝ) + 1)) * lanczosReorthRoundoffBound N q u) :
    LanczosReorthRegime q (lanczosImplementationRoundoffBound N u) τ η₀
      (2 * cgsPassBound N q u η₀) (3 * cgsPassBound N q u η₀)
      (2 * (η₀ + cgsPassBound N q u η₀) ^ 2) := by
  obtain ⟨-, hη, -, -, -, hρ0, -, hμ, hε₂, hfix⟩ := cgs2_regime_bounds hu hsmall hτ hτlo hη₀
  have hs0 : 0 ≤ Real.sqrt (3 * ((q : ℝ) + 1)) := Real.sqrt_nonneg _
  refine ⟨hη, hτ1, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hμ hs0).trans_eq hfix
  · have : lanczosReorthRoundoffBound N q u ≤ 1 / 1000 := by
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith
    linarith


end NLAlib
