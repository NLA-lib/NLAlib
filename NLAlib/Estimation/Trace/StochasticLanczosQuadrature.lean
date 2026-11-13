/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Orthogonal.Gauss
public import NLAlib.Estimation.Trace.GirardHutchinson
public import NLAlib.Polynomial.Approximation.AnalyticApproximation
public import NLAlib.Krylov.Functions.Quadrature
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# Stochastic Lanczos quadrature

For a square $\mathbf{A}$, a function $f : \mathbb{R} \to \mathbb{R}$ and a test matrix
$\mathbf{\Omega}$ whose $m$ columns $\boldsymbol{\omega}_1, \dots, \boldsymbol{\omega}_m$ are the
probes, the **stochastic Lanczos quadrature** estimate of $\operatorname{tr} f(\mathbf{A})$
replaces each single-probe Girard–Hutchinson term
$\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j = \int f\,d\mu_j$ by its
$q$-point Gauss rule, $\mu_j = \mu_{\mathbf{A},\boldsymbol{\omega}_j}$ the probe's spectral
measure, and averages over the probes. For Hermitian $\mathbf{A}$ this is what $q$ Lanczos steps
per probe compute. Its error is the Girard–Hutchinson error plus the averaged Gauss error, so
every Girard–Hutchinson result (unbiasedness, variance, tails) composes with every Gauss-rule
error bound (uniform approximation, Lipschitz, analytic). Exact arithmetic throughout.
[UbaruChenSaad2017]; [MartinssonTropp2020].

The error splits into the Girard–Hutchinson error of $f(\mathbf{A})$ plus the averaged per-probe
Gauss error $2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2/m$, $\varepsilon$ the uniform distance
from $f$ to polynomials of degree less than $2q$ on an interval containing the spectrum, with the
Lipschitz (Jackson) and analytic (Bernstein ellipse) rates; composing with the Hanson–Wright tail
of Girard–Hutchinson gives the tails with independent sub-Gaussian entries, the quadrature term
random inside the event. [CortinovisKressner2022].

For every test matrix, SLQ with $q$ Lanczos steps is below the Girard–Hutchinson estimate when
$f^{(2q)} \ge 0$ on an interval containing the spectrum, and above it when $f^{(2q)} \le 0$: the
Gauss error has a sign probe by probe, so the SLQ bias is one-signed.

## Main definitions

* `NLAlib.slq`: the stochastic Lanczos quadrature estimate.

## Main results

* `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_continuousOn`: the deterministic split.
* `NLAlib.measureReal_abs_trace_cfc_sub_slq_ge_le_of_continuousOn`: the tail.
* `NLAlib.re_slq_le_re_girardHutchinson_cfc_of_iteratedDeriv_nonneg`,
  `NLAlib.re_girardHutchinson_cfc_le_re_slq_of_iteratedDeriv_nonpos`: the sign of the SLQ bias.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The **stochastic Lanczos quadrature** estimate of $\operatorname{tr} f(\mathbf{A})$ from the
test matrix $\mathbf{\Omega}$, whose $m$ columns $\boldsymbol{\omega}_1, \dots,
\boldsymbol{\omega}_m$ are the probes: the average over the probes of the $q$-point Gauss rule of
each probe's spectral measure $\mu_j = \mu_{\mathbf{A},\boldsymbol{\omega}_j}$ applied to $f$,
$$\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q) := \frac{1}{m}\sum_{j=1}^m
\int f\,d\,\mathsf{gaussQuadrature}(\mu_j, q)\,,$$
the Girard–Hutchinson estimate with each
$\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j = \int f\,d\mu_j$ replaced
by its Gauss quadrature. For Hermitian $\mathbf{A}$ this is what $q$ Lanczos steps per probe
compute, $\tfrac{1}{m}\sum_j\boldsymbol{\omega}_j^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f,
\boldsymbol{\omega}_j, q) = \tfrac{1}{m}\sum_j\|\boldsymbol{\omega}_j\|^2\mathbf{e}_1^{\mathsf{T}}
f(\mathbf{T}_j)\mathbf{e}_1$ (`Matrix.IsHermitian.slq_eq_sum_lanczosFA`), with $mq$ products with
$\mathbf{A}$. A real number in `𝕜`. Junk value: $0$ when $\mathbf{\Omega}$ has no columns, when
$q = 0$ and when $\mathbf{A}$ is not Hermitian.
[UbaruChenSaad2017, §3, Algorithm 1]; [MartinssonTropp2020, §6.6, Algorithm 6].
Algorithm: stochastic-lanczos-quadrature -/
noncomputable def slq (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) : 𝕜 :=
  ((∑ j, ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q : ℝ) : 𝕜) /
    Fintype.card m

/-! ### The algorithm -/

/-- A probe's Lanczos-FA quadratic form is real, for Hermitian $\mathbf{A}$. -/
private theorem coe_re_star_dotProduct_lanczosFA {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    ((RCLike.re (star b ⬝ᵥ lanczosFA A f b q) : ℝ) : 𝕜) = star b ⬝ᵥ lanczosFA A f b q := by
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  have key : star b ⬝ᵥ lanczosFA A f b q = quadForm (cfc f (Qᴴ * A * Q)) (Qᴴ *ᵥ b) := by
    rw [hQ.lanczosFA_eq hK f, quadForm_def, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose]
  have hH : (cfc f (Qᴴ * A * Q)).IsHermitian := cfc_predicate (p := IsSelfAdjoint) f _
  rw [key, hH.coe_re_quadForm]

/-- **SLQ is what the Lanczos algorithm computes**: for Hermitian $\mathbf{A}$, every
$f : \mathbb{R} \to \mathbb{R}$, every test matrix $\mathbf{\Omega}$ with $m$ columns
$\boldsymbol{\omega}_j$ and every $q$,
$$\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q) = \frac{1}{m}\sum_{j=1}^m
\boldsymbol{\omega}_j^{\mathsf{H}}\,\mathsf{lanczosFA}(\mathbf{A}, f, \boldsymbol{\omega}_j, q)\,:$$
each probe's Gauss rule is its Lanczos rule
(`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`) and the Lanczos rule
integrates $f$ to the Lanczos-FA quadratic form, which is real.
[MartinssonTropp2020, §6.6, Algorithm 6]; there as the definition. -/
theorem _root_.Matrix.IsHermitian.slq_eq_sum_lanczosFA {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) :
    slq A f Ω q =
      (∑ j, star (fun i => Ω i j) ⬝ᵥ lanczosFA A f (fun i => Ω i j) q) / Fintype.card m := by
  unfold slq
  congr 1
  rw [RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hA.lanczosQuadrature_eq_gaussQuadrature, integral_lanczosQuadrature,
    coe_re_star_dotProduct_lanczosFA hA]

/-! ### The error, deterministically -/

/-- The error of SLQ from a per-probe bound $C\|\mathbf{b}\|^2$ on the Lanczos quadrature
error, for Hermitian $\mathbf{A}$: the Girard–Hutchinson error plus $C$ times
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/m$. -/
private theorem norm_trace_cfc_sub_slq_le_of_forall {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : ℝ → ℝ} {q : ℕ} {C : ℝ} (hC : ∀ b : n → 𝕜,
      ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b q)‖ ≤ C * ‖WithLp.toLp 2 b‖ ^ 2)
    (Ω : Matrix n m 𝕜) :
    ‖(cfc f A).trace - slq A f Ω q‖ ≤ ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
      C * (frobNorm Ω ^ 2 / Fintype.card m) := by
  have hsplit : (cfc f A).trace - slq A f Ω q =
      ((cfc f A).trace - girardHutchinson (cfc f A) Ω) +
        (∑ j, star (fun i => Ω i j) ⬝ᵥ
          (cfc f A *ᵥ (fun i => Ω i j) - lanczosFA A f (fun i => Ω i j) q)) / Fintype.card m := by
    simp only [hA.slq_eq_sum_lanczosFA, girardHutchinson_eq_sum, quadForm_def, dotProduct_sub,
      Finset.sum_sub_distrib]
    ring
  rw [hsplit, mul_div_assoc', frobNorm_sq_eq_sum_col, Finset.mul_sum]
  grw [norm_add_le, norm_div, RCLike.norm_natCast, norm_sum_le]
  gcongr with j
  exact hC _

/-- **The error of stochastic Lanczos quadrature splits** into the Girard–Hutchinson error and a
quadrature error: for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$, if a real polynomial $p$
of degree less than $2q$ is within $\varepsilon$ of $f$ on $[a, a']$, then for every test matrix
$\mathbf{\Omega}$ with $m$ columns
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)\bigr\rvert \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}\,.$$
Probe by probe, $\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j =
\int f\,d\mu_j$, $\mu_j$ the spectral measure of $\mathbf{A}$ and $\boldsymbol{\omega}_j$, is
replaced by its Gauss rule, whose error is at most
$2\varepsilon\mu_j(\mathbb{R}) = 2\varepsilon\|\boldsymbol{\omega}_j\|^2$; the errors are
averaged. With no columns both sides reduce to $\lvert\operatorname{tr} f(\mathbf{A})\rvert$.
[UbaruChenSaad2017, §4.2, Lemma 4.4]; [MartinssonTropp2020, §6.6]; there with the
quadrature error bounded through analytic $f$ and Chebyshev approximation.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) (Ω : Matrix n m 𝕜) :
    ‖(cfc f A).trace - slq A f Ω q‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        2 * ε * frobNorm Ω ^ 2 / Fintype.card m := by
  have h := norm_trace_cfc_sub_slq_le_of_forall hA
    (hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp hε) Ω
  refine h.trans_eq ?_
  ring

/-- **The error of stochastic Lanczos quadrature for Lipschitz functions**: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, $a < a'$, $f$ $L$-Lipschitz on $[a, a']$, every test
matrix $\mathbf{\Omega}$ with $m$ columns and every $q$, with $q + 1$ Lanczos steps per
probe, <!-- value jacksonApproximationConstant -->
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{\pi L(a' - a)}{2q + 3}\cdot
\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}\,;$$
the constant is `jacksonApproximationConstant`. Per probe, the Gauss-rule error for Lipschitz
functions (Jackson's theorem in degree $2q + 1$), averaged.
[UbaruChenSaad2017, §4.2, Lemma 4.4]; the rate uses the local Jackson approximation bound.
[ChenTrogdonUbaru2022, Appendix C, Theorem 38] uses the damped-Chebyshev route
with the larger printed constant $\pi^2/2$.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) *
          (frobNorm Ω ^ 2 / Fintype.card m) := by
  exact norm_trace_cfc_sub_slq_le_of_forall hA (fun b =>
    hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_lipschitzOnWith haa hs hf b q) Ω

/-- **The error of stochastic Lanczos quadrature for analytic functions**: let $\mathbf{A}$ be
Hermitian with spectrum in $[a, a']$, $a < a'$, and let $f$, transported to $[-1, 1]$ by the
affine map onto $[a, a']$, extend to a function $F$ holomorphic on the open Bernstein ellipse
$E_\rho$, $\rho > 1$, with $\lvert F\rvert \le M$ there. Then for every test matrix
$\mathbf{\Omega}$ with $m$ columns and every $q$, with $q + 1$ Lanczos steps per probe,
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{4M}{\rho^{2q + 1}(\rho - 1)}\cdot
\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}\,,$$
from the Chebyshev truncation of degree $2q + 1$.
[UbaruChenSaad2017, Theorem 4.1]; the setting of their analysis, there with
relative error for positive definite $\mathbf{A}$.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_differentiableOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1))
    (Ω : Matrix n m 𝕜) (q : ℕ) :
    ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * (frobNorm Ω ^ 2 / Fintype.card m) := by
  exact norm_trace_cfc_sub_slq_le_of_forall hA (fun b =>
    hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_differentiableOn haa hs hρ hFd hM hExt
      b q) Ω

/-! ### Tails with independent sub-Gaussian entries -/

/-- A tail of SLQ from a split of its error into the Girard–Hutchinson error and a term
$E(\mathbf{\Omega})$: the event $\tau + E(\mathbf{\Omega}) \le \lvert\cdot\rvert$ lies in the
Girard–Hutchinson event at $\tau$. -/
private theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_forall {X : Ω → Matrix n m ℝ}
    {c : ℝ≥0} (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} {f : ℝ → ℝ} {q : ℕ}
    {E : Matrix n m ℝ → ℝ} (hE : ∀ Y, ‖(cfc f A).trace - slq A f Y q‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Y‖ + E Y) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + E (X ω) ≤ |(cfc f A).trace - slq A f (X ω) q|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  have := hind.isProbabilityMeasure
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_abs_trace_sub_girardHutchinson_ge_le hind hsub hvar (cfc f A) hτ)
  have h := hE (X ω)
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω h ⊢
  linarith

/-- **The tail of stochastic Lanczos quadrature with sub-Gaussian probes.** Let the entries of the
real $n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and having second
moment $1$. Let $\mathbf{A}$ be real symmetric with spectrum in $[a, a']$ and let a real
polynomial $p$ of degree less than $2q$ be within $\varepsilon$ of $f$ on $[a, a']$. Then for
every $\tau \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m} \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)\bigr\rvert\Bigr]
\le 2\exp\Bigl(-\frac{1}{196}\min\Bigl(\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`; the quadrature term is random, inside the event. No
definiteness of $f(\mathbf{A})$ is needed. Gaussian and sign test matrices are the case $c = 1$.
No measurability of the estimate is needed: the event lies in the Girard–Hutchinson event.
[UbaruChenSaad2017, Theorem 4.1], there for positive definite $\mathbf{A}$
with Rademacher probes and relative error; [CortinovisKressner2022, §4, Theorems 19 and 20], for
the analogous
combination in log-determinant estimation, where the logarithm can be indefinite.
Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]}
    (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | τ + 2 * ε * frobNorm (X ω) ^ 2 / Fintype.card m ≤
        |(cfc f A).trace - slq A f (X ω) q|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  exact measureReal_abs_trace_cfc_sub_slq_ge_le_of_forall hind hsub hvar
    (hA.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn hs hp hε) hτ

/-- **The tail of stochastic Lanczos quadrature for Lipschitz functions.** Let the entries of the
real $n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ and having second moment $1$. Let
$\mathbf{A}$ be real symmetric with spectrum in $[a, a']$, $a < a'$, and $f$ $L$-Lipschitz on
$[a, a']$. Then for every $q$ and $\tau \ge 0$, with $q + 1$ Lanczos steps per probe and
quadrature term <!-- value jacksonApproximationConstant -->$\pi L(a' - a)/(2q + 3)$ per unit
of mass, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{\pi L(a' - a)}{2q + 3}\cdot
\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}
\le \bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega},
q + 1)\bigr\rvert\Bigr] \le 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constants are `hansonWrightConstant` and `jacksonApproximationConstant`; the quadrature term
is random, inside the event. Gaussian and sign test matrices are the case $c = 1$.
[UbaruChenSaad2017, Theorem 4.1], there for analytic $f$;
[CortinovisKressner2022, §4, Theorems 19 and 20], for the log-determinant specialization.
Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_lipschitzOnWith
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (haa : a < a') (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) *
          (frobNorm (X ω) ^ 2 / Fintype.card m) ≤
        |(cfc f A).trace - slq A f (X ω) (q + 1)|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  exact measureReal_abs_trace_cfc_sub_slq_ge_le_of_forall hind hsub hvar
    (fun Y => hA.norm_trace_cfc_sub_slq_le_of_lipschitzOnWith haa hs hf Y q) hτ

/-- **The tail of stochastic Lanczos quadrature for analytic functions**, the setting of Ubaru,
Chen and Saad for any real symmetric matrix, in absolute error. Let the entries of the real
$n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ and having second moment $1$. Let
$\mathbf{A}$ be real symmetric with spectrum in $[a, a']$, $a < a'$, and let $f$, transported to
$[-1, 1]$ by the affine map onto $[a, a']$, extend to a function $F$ holomorphic on the open
Bernstein ellipse $E_\rho$, $\rho > 1$, with $\lvert F\rvert \le M$ there. Then for every $q$ and
$\tau \ge 0$, with $q + 1$ Lanczos steps per probe, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{4M}{\rho^{2q + 1}(\rho - 1)}\cdot
\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m} \le \bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert\Bigr] \le
2\exp\Bigl(-\frac{1}{196}\min\Bigl(\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`; the quadrature term is random, inside the event.
[UbaruChenSaad2017, Theorem 4.1], there for positive definite $\mathbf{A}$
with Rademacher probes and relative error; [CortinovisKressner2022, §4, Theorems 19 and 20], for
the log-determinant specialization.
Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_differentiableOn
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (haa : a < a') (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ}
    {ρ M : ℝ} (hρ : 1 < ρ) (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1)) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + 4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * (frobNorm (X ω) ^ 2 / Fintype.card m) ≤
        |(cfc f A).trace - slq A f (X ω) (q + 1)|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  exact measureReal_abs_trace_cfc_sub_slq_ge_le_of_forall hind hsub hvar
    (fun Y => hA.norm_trace_cfc_sub_slq_le_of_differentiableOn haa hs hρ hFd hM hExt Y q) hτ

/-- **The error of stochastic Lanczos quadrature and the minimax error**: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, $f$ continuous on $[a, a']$, every test matrix
$\mathbf{\Omega}$ with $m$ columns and $q + 1$ Lanczos steps per probe,
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{2E_{2q + 1}(f; [a, a'])\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}
\,,$$
$E_{2q + 1}$ the error of the best uniform approximation of $f$ on $[a, a']$ by polynomials of
degree at most $2q + 1$ (`minimaxError`). [UbaruChenSaad2017, §4.2, Lemma 4.4]; there
with the quadrature error bounded through analytic $f$ and Chebyshev approximation.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_continuousOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        2 * minimaxError f (Set.Icc a a') (2 * q + 1) * frobNorm Ω ^ 2 / Fintype.card m := by
  have hdeg : ∀ p : ℝ[X], p.degree ≤ ↑(2 * q + 1) → p.degree < ↑(2 * (q + 1)) := fun p hp =>
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc hf (2 * q + 1)
  exact_mod_cast hA.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn hs (hdeg p hp) hε Ω

/-- **The tail of stochastic Lanczos quadrature and the minimax error.** Let the entries of the
real $n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and having second
moment $1$. Let $\mathbf{A}$ be real symmetric with spectrum in $[a, a']$ and $f$ continuous on
$[a, a']$. Then for every $q$ and $\tau \ge 0$, with $q + 1$ Lanczos steps per
probe, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{2E_{2q + 1}(f; [a, a'])\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}
\le \bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert\Bigr]
\le 2\exp\Bigl(-\frac{1}{196}\min\Bigl(\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`; $E_{2q + 1}$ is the error of the best uniform
approximation of $f$ on $[a, a']$ by polynomials of degree at most $2q + 1$ (`minimaxError`), and
the quadrature term is random, inside the event. Gaussian and sign test matrices are the case
$c = 1$. [UbaruChenSaad2017, Theorem 4.1], there for positive definite
$\mathbf{A}$ with Rademacher probes and relative error; [CortinovisKressner2022, §4, Theorems 19
and 20] treats the log-determinant specialization.
Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_continuousOn
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + 2 * minimaxError f (Set.Icc a a') (2 * q + 1) * frobNorm (X ω) ^ 2 /
        Fintype.card m ≤ |(cfc f A).trace - slq A f (X ω) (q + 1)|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc hf (2 * q + 1)
  have hp' : p.degree < (2 * (q + 1) : ℕ) := hp.trans_lt (Nat.cast_lt.mpr (by omega))
  exact measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn hind hsub hvar hA hs
    (by exact_mod_cast hp') hε hτ

/-! ### The sign of the bias -/

/-- The real part of SLQ is the average over the probes of the Gauss-rule integrals of $f$. -/
private lemma re_slq_eq (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) :
    RCLike.re (slq A f Ω q) =
      (∑ j, ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q) / Fintype.card m := by
  unfold slq
  rw [← RCLike.ofReal_natCast, RCLike.div_re_ofReal, RCLike.ofReal_re]

/-- The real part of the Girard–Hutchinson estimate of $\operatorname{tr}f(\mathbf{A})$ is the
average over the probes of the integrals of $f$ against their spectral measures. -/
private lemma re_girardHutchinson_cfc_eq (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) :
    RCLike.re (girardHutchinson (cfc f A) Ω) =
      (∑ j, ∫ x, f x ∂spectralMeasure A (fun i => Ω i j)) / Fintype.card m := by
  rw [girardHutchinson_eq_sum, ← RCLike.ofReal_natCast, RCLike.div_re_ofReal, map_sum]
  simp only [integral_spectralMeasure]

/-- **SLQ underestimates for $f$ with nonnegative derivative of order $2q$**: for
$\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$), $a < a'$,
$q > 0$, $f$ continuous on $[a, a']$,
$C^{2q}$ on $(a, a')$ with $f^{(2q)} \ge 0$ there, and every test matrix $\mathbf{\Omega}$,
$$\operatorname{Re}\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q) \le
\operatorname{Re}\mathsf{girardHutchinson}(f(\mathbf{A}), \mathbf{\Omega})\,.$$
[UbaruChenSaad2017, §4.1, equation (4.2)]; [GolubMeurant2010, (6.4) with no prescribed nodes]
gives the sign of the Gauss remainder;
the per-probe Gauss
bound summed. -/
theorem re_slq_le_re_girardHutchinson_cfc_of_iteratedDeriv_nonneg {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (haa' : a < a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} (hq : 0 < q)
    (hf' : ContDiffOn ℝ (2 * q : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', 0 ≤ iteratedDeriv (2 * q) f x) (Ω : Matrix n m 𝕜) :
    RCLike.re (slq A f Ω q) ≤ RCLike.re (girardHutchinson (cfc f A) Ω) := by
  rw [re_slq_eq, re_girardHutchinson_cfc_eq]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg _)
  exact integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg
    (ae_mem_Icc_spectralMeasure A hs _) haa' hq hf hf' hD

/-- **SLQ overestimates for $f$ with nonpositive derivative of order $2q$**: for
$\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$), $a < a'$,
$q > 0$, $f$ continuous on $[a, a']$,
$C^{2q}$ on $(a, a')$ with $f^{(2q)} \le 0$ there (such as $\log$ on $[a, a']$, $a > 0$), and
every test matrix $\mathbf{\Omega}$,
$$\operatorname{Re}\mathsf{girardHutchinson}(f(\mathbf{A}), \mathbf{\Omega}) \le
\operatorname{Re}\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)\,.$$
[UbaruChenSaad2017, §4.1, equation (4.2)]; [GolubMeurant2010, (6.4) with no prescribed nodes]
gives the sign of the Gauss remainder. -/
theorem re_girardHutchinson_cfc_le_re_slq_of_iteratedDeriv_nonpos {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (haa' : a < a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} (hq : 0 < q)
    (hf' : ContDiffOn ℝ (2 * q : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', iteratedDeriv (2 * q) f x ≤ 0) (Ω : Matrix n m 𝕜) :
    RCLike.re (girardHutchinson (cfc f A) Ω) ≤ RCLike.re (slq A f Ω q) := by
  rw [re_slq_eq, re_girardHutchinson_cfc_eq]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg _)
  exact integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos
    (ae_mem_Icc_spectralMeasure A hs _) haa' hq hf hf' hD

end NLAlib
