/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Spectral.SpectralDensity
public import NLAlib.ForMathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Spectral density estimation: tails with independent sub-Gaussian entries

With independent sub-Gaussian entries of unit variance in the test matrix, the distribution
functions of the probe spectral measure and of the empirical spectral measure are uniformly close
at the eigenvalues except with probability
$2\lvert n\rvert\exp(-\tfrac{1}{196}m\lvert n\rvert\min(\tau^2/c^2, \tau/c))$: each is a
Girard–Hutchinson estimate of a spectral projector. On that event the deterministic bounds of
`NLAlib/Estimation/Spectral/SpectralDensity.lean` control every Lipschitz test function at once,
for the probe measure, for SLQ (adding the Gauss error) and for the mass-normalised SLQ measure.
[ChenTrogdonUbaru2021].

## Main results

* `NLAlib.measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le`:
  the Kolmogorov-distance tail.
* `NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le`:
  SLQ approximates the spectral density uniformly in Lipschitz test functions; its asymptotic
  form and the mass-normalised form follow it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The exponent of the Girard–Hutchinson tail dominates the exponent of the spectral tail: if
$F^2 \le 1/N$ and $S \le 1/N$ with $F, S > 0$, then $M N \min(\tau^2/c^2, \tau/c)$ is at most
$\min(M\tau^2/(c^2F^2), M\tau/(cS))$. -/
private lemma card_mul_min_le_min_girardHutchinson {M N τ c F S : ℝ} (hM : 0 ≤ M) (hN : 0 < N)
    (hc : 0 < c) (hτ : 0 ≤ τ) (hF : 0 < F) (hS : 0 < S) (hF2 : F ^ 2 ≤ 1 / N) (hS1 : S ≤ 1 / N) :
    M * N * min (τ ^ 2 / c ^ 2) (τ / c) ≤ min (M * τ ^ 2 / (c ^ 2 * F ^ 2)) (M * τ / (c * S)) := by
  have hNF : N * F ^ 2 ≤ 1 := (le_div_iff₀' hN).1 hF2
  have hNS : N * S ≤ 1 := (le_div_iff₀' hN).1 hS1
  refine le_min ?_ ?_
  · rw [le_div_iff₀ (by positivity)]
    calc M * N * min (τ ^ 2 / c ^ 2) (τ / c) * (c ^ 2 * F ^ 2)
        ≤ M * N * (τ ^ 2 / c ^ 2) * (c ^ 2 * F ^ 2) := by
          gcongr
          exact min_le_left _ _
      _ = M * τ ^ 2 * (N * F ^ 2) := by field_simp
      _ ≤ M * τ ^ 2 * 1 := by gcongr
      _ = M * τ ^ 2 := mul_one _
  · rw [le_div_iff₀ (by positivity)]
    calc M * N * min (τ ^ 2 / c ^ 2) (τ / c) * (c * S)
        ≤ M * N * (τ / c) * (c * S) := by
          gcongr
          exact min_le_right _ _
      _ = M * τ * (N * S) := by field_simp
      _ ≤ M * τ * 1 := by gcongr
      _ = M * τ := mul_one _

/-- The distribution of the probe spectral measure, at one set: let the entries of the real
$n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and having second
moment $1$. Then for real symmetric $\mathbf{A}$, every $S \subseteq \mathbb{R}$ and every
$\tau \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\tau \le \lvert\nu_{\mathbf{A}}(S) - \mathsf{probeSpectralMeasure}(\mathbf{A},
\mathbf{\Omega})(S)\rvert\bigr] \le 2\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert
\min\Bigl(\frac{\tau^2}{c^2}, \frac{\tau}{c}\Bigr)\Bigr)\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant is `hansonWrightConstant`. The
error is that of Girard–Hutchinson on $\mathbf{1}_S(\mathbf{A})/\lvert n\rvert$, a projector
divided by $\lvert n\rvert$, of squared Frobenius norm at most $1/\lvert n\rvert$ and spectral
norm at most $1/\lvert n\rvert$; the factor $\lvert n\rvert$ in the exponent is the "dimension
helps" effect. -/
theorem measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Set ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
        (probeSpectralMeasure A (X ω)).real S|} ≤
      2 * Real.exp (-(hansonWrightConstant * (Fintype.card m * Fintype.card n *
        min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have := hind.isProbabilityMeasure
  set P : Matrix n n ℝ := cfc (S.indicator fun _ => (1 : ℝ)) A with hPdef
  have hP : IsStarProjection P := isStarProjection_cfc_indicator A S
  set B : Matrix n n ℝ := (1 / (Fintype.card n : ℝ)) • P with hBdef
  have hset : {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
      (probeSpectralMeasure A (X ω)).real S|} =
      {ω | τ ≤ |B.trace - girardHutchinson B (X ω)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hBdef, hPdef, hA.empiricalSpectralMeasure_real,
      probeSpectralMeasure_real, girardHutchinson_smul, Matrix.trace_smul, smul_eq_mul,
      RCLike.re_to_real]
    ring_nf
  rw [hset]
  -- for `τ = 0` or `c = 0` the bound is `2`
  have h2 : μ.real {ω | τ ≤ |B.trace - girardHutchinson B (X ω)|} ≤ 2 :=
    measureReal_le_one.trans one_le_two
  rcases eq_or_lt_of_le hτ with rfl | hτpos
  · simp
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using h2
  have hc' : (0:ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  by_cases hB : B = 0
  · have hempty : {ω | τ ≤ |B.trace - girardHutchinson B (X ω)|} = ∅ := by
      ext ω
      simp [hB, girardHutchinson, not_le.2 hτpos]
    rw [hempty, measureReal_empty]
    positivity
  have hN : (0:ℝ) < Fintype.card n := by
    refine Nat.cast_pos.2 (Fintype.card_pos_iff.2 (not_isEmpty_iff.1 fun _ => ?_))
    exact hB (Subsingleton.elim _ _)
  have hF : 0 < frobNorm B :=
    lt_of_le_of_ne (frobNorm_nonneg _) (fun h => hB (frobNorm_eq_zero_iff.1 h.symm))
  have hS : 0 < specNorm B :=
    lt_of_le_of_ne (specNorm_nonneg _) (fun h => hB (specNorm_eq_zero_iff.1 h.symm))
  have hF2 : frobNorm B ^ 2 ≤ 1 / (Fintype.card n : ℝ) := by
    rw [hBdef, frobNorm_smul, mul_pow, hP.frobNorm_sq_eq_rank,
      Real.norm_of_nonneg (by positivity)]
    have hr : (P.rank : ℝ) ≤ Fintype.card n := by exact_mod_cast Matrix.rank_le_card_width P
    calc (1 / (Fintype.card n : ℝ)) ^ 2 * (P.rank : ℝ) ≤ (1 / (Fintype.card n : ℝ)) ^ 2 *
          (Fintype.card n : ℝ) := by gcongr
      _ = 1 / (Fintype.card n : ℝ) := by field_simp
  have hS1 : specNorm B ≤ 1 / (Fintype.card n : ℝ) := by
    rw [hBdef, specNorm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) hP.specNorm_le_one
  have hmin := card_mul_min_le_min_girardHutchinson (M := (Fintype.card m : ℝ))
    (Nat.cast_nonneg _) hN hc' hτ hF hS hF2 hS1
  calc μ.real {ω | τ ≤ |B.trace - girardHutchinson B (X ω)|}
      ≤ 2 * Real.exp (-(hansonWrightConstant *
          min ((Fintype.card m : ℝ) * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm B ^ 2))
            ((Fintype.card m : ℝ) * τ / ((c : ℝ) * specNorm B)))) :=
        measureReal_abs_trace_sub_girardHutchinson_ge_le hind hsub hvar B hτpos.le
    _ ≤ 2 * Real.exp (-(hansonWrightConstant * ((Fintype.card m : ℝ) * Fintype.card n *
          min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
        gcongr
        exact hansonWrightConstant_pos.le

/-- **The Kolmogorov-distance tail of the probe spectral measure.** Let the entries of the real
$n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ and having second moment $1$. Then for
real symmetric $\mathbf{A}$ and every $\tau \ge 0$, the distribution functions of
$\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by more than $\tau$ at some
eigenvalue with probability at most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
the constant being `hansonWrightConstant`: a union bound over the at most $\lvert n\rvert$
eigenvalues; both distribution functions are constant between eigenvalues, and
`Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le`
extends the bound to every threshold. [ChenTrogdonUbaru2021, Theorem 2 and §4.1]; there for
probes uniform on the sphere.
Result: spectral-density-kolmogorov-tail -/
theorem measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
        (probeSpectralMeasure A (X ω)).real (Set.Iic x)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have := hind.isProbabilityMeasure
  -- union bound over the eigenvalues, indexed by `n`
  calc _ ≤ μ.real (⋃ i ∈ (Finset.univ : Finset n), {ω | τ ≤
          |(empiricalSpectralMeasure A).real (Set.Iic (hA.eigenvalues i)) -
            (probeSpectralMeasure A (X ω)).real (Set.Iic (hA.eigenvalues i))|}) := by
        refine measureReal_mono (fun ω ⟨x, hx, hlt⟩ => ?_) (measure_ne_top _ _)
        obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
        exact Set.mem_biUnion (Finset.mem_univ i) hlt.le
    _ ≤ ∑ i : n, μ.real {ω | τ ≤
          |(empiricalSpectralMeasure A).real (Set.Iic (hA.eigenvalues i)) -
            (probeSpectralMeasure A (X ω)).real (Set.Iic (hA.eigenvalues i))|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i : n, 2 * Real.exp (-(hansonWrightConstant * (Fintype.card m *
          Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) :=
        Finset.sum_le_sum fun i _ =>
          measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le
            hind hsub hvar hA _ hτ
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **The probe spectral measure approximates the spectral density, uniformly in Lipschitz test
functions.** Let the entries of the real $n \times m$ test matrix $\mathbf{\Omega}$ be
independent, each satisfying the sub-Gaussian moment generating function bound with variance
proxy $c$ and having second moment $1$; let $\mathbf{A}$ be real symmetric with spectrum in
$[a, b]$, $a \le b$, and let $L \ge 0$ and $\tau \ge 0$. Then, except with probability at
most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
every $f$ that is $L$-Lipschitz on $[a, b]$ satisfies
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} -
\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})\Bigr\rvert \le
(\lvert f(b)\rvert + L(b - a))\tau\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant is `hansonWrightConstant`. This is
SLQ with exact quadrature. [ChenTrogdonUbaru2021, Theorem 2 and §4.1]; there for probes
uniform on the sphere.
Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a ≤ b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂probeSpectralMeasure A (X ω)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have := hind.isProbabilityMeasure
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
      hind hsub hvar hA hτ)
  obtain ⟨f, hf, hlt⟩ := hω
  by_contra hK
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hK
  exact hlt.not_ge
    (hA.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le hab hs hτ hK hf)

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Stochastic Lanczos quadrature approximates the spectral density, uniformly in Lipschitz
test functions.** Let the entries of the real $n \times m$ test matrix $\mathbf{\Omega}$ be
independent, each satisfying the sub-Gaussian moment generating function bound with variance
proxy $c$ and having second moment $1$; let $\mathbf{A}$ be real symmetric with spectrum in
$[a, b]$, $a < b$; let $L \ge 0$, $q \in \mathbb{N}$ and $\tau \ge 0$. Then, except with
probability at most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
every $f$ that is $L$-Lipschitz on $[a, b]$ satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega},
q + 1)\Bigr\rvert \le (\lvert f(b)\rvert + L(b - a))\tau +
\frac{\pi L(b - a)}{2q + 3}(1 + \tau)\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constants are `hansonWrightConstant` and
`jacksonApproximationConstant`. For test functions with $f(b) = 0$ and equal masses this is a
Wasserstein-1 bound. The factor $1 + \tau$ bounds the random mass
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$ on the same event. Gaussian and sign test
matrices are the case $c = 1$.
Asymptotic form:
`NLAlib.exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le`.
[ChenTrogdonUbaru2021, Theorem 1]; there for probes
uniform on the sphere, with the sharper sub-Gaussian constant of Beta laws and the bound in the
Wasserstein distance; the Jackson step uses the local Jackson approximation bound;
[ChenTrogdonUbaru2022, Appendix C, Theorem 38] uses the damped-Chebyshev route
with the larger printed constant $\pi^2/2$.
Result: spectral-density-lipschitz-tail -/
theorem measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) (q : ℕ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ +
          jacksonApproximationConstant * L * (b - a) / (2 * q + 3) * (1 + τ) <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂slqMeasure A (X ω) (q + 1)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have := hind.isProbabilityMeasure
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
      hind hsub hvar hA hτ)
  obtain ⟨f, hf, hlt⟩ := hω
  by_contra hK
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hK
  have hmass : frobNorm (X ω) ^ 2 / (Fintype.card n * Fintype.card m) ≤ 1 + τ := by
    rcases isEmpty_or_nonempty n with hn | hn
    · simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul, div_zero]
      linarith
    · rw [← hA.probeSpectralMeasure_real_univ (X ω)]
      linarith [abs_le.mp (hA.abs_one_sub_probeSpectralMeasure_real_univ_le hK)]
  have h1 := hA.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le
    hab.le hs hτ hK hf
  have h2 := hA.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith
    hab hs (X ω) q hf
  have hJ : 0 ≤ jacksonApproximationConstant * L * (b - a) / (2 * q + 3) := by
    have := jacksonApproximationConstant_pos
    have : 0 ≤ b - a := by linarith
    positivity
  have h3 := abs_sub_le (∫ x, f x ∂empiricalSpectralMeasure A)
    (∫ x, f x ∂probeSpectralMeasure A (X ω)) (∫ x, f x ∂slqMeasure A (X ω) (q + 1))
  nlinarith [mul_le_mul_of_nonneg_left hmass hJ]

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(c^2\log(\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2))$ probes suffice for SLQ to
approximate the spectral density, uniformly in Lipschitz test functions**: there is an absolute
constant $C > 0$ such that the following holds. Let the entries of the real $n \times m$ test
matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian moment generating
function bound with variance proxy $c > 0$ and having second moment $1$; let $\mathbf{A}$ be real
symmetric with spectrum in $[a, b]$, $a < b$; let $L \ge 0$, $q \in \mathbb{N}$,
$0 < \tau \le 1$ and $0 < \delta \le 1$. If
$m \ge C c^2\log(2\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2)$, then except with probability
at most $\delta$ every $f$ that is $L$-Lipschitz on $[a, b]$
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega},
q + 1)\Bigr\rvert \le (\lvert f(b)\rvert + L(b - a))\tau +
\frac{\pi L(b - a)}{2q + 3}(1 + \tau)\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant of the Gauss term is
`jacksonApproximationConstant`. The constant $C$ comes before every dimension, matrix and
parameter. With $\lvert n\rvert$ in the denominator, for large $n$ a single probe suffices.
Proved from
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le`
with $C = 196$. [ChenTrogdonUbaru2021, Theorem 1];
there for probes uniform on the sphere.
Asymptotic:
NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
Result: spectral-density-lipschitz-tail -/
theorem
exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω n m : Type} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
      [Fintype m] (μ : Measure Ω) (X : Ω → Matrix n m ℝ) (c : ℝ≥0)
      (A : Matrix n n ℝ) (a b : ℝ) (L : ℝ≥0) (q : ℕ) (τ δ : ℝ), 0 < c →
      iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ →
      (∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ) →
      (∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) → A.IsHermitian → a < b →
      spectrum ℝ A ⊆ Set.Icc a b → 0 < τ → τ ≤ 1 → 0 < δ → δ ≤ 1 →
      C * (c : ℝ) ^ 2 * Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) ≤
        Fintype.card m →
      μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ +
          jacksonApproximationConstant * L * (b - a) / (2 * q + 3) * (1 + τ) <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂slqMeasure A (X ω) (q + 1)|} ≤ δ := by
  refine ⟨196, by norm_num, ?_⟩
  intro Ω n m _ _ _ _ μ X c A a b L q τ δ hc hind hsub hvar hA hab hs hτ hτ1 hδ hδ1 hsize
  have := hind.isProbabilityMeasure
  refine (measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
    hind hsub hvar hA hab hs L q hτ.le).trans ?_
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, mul_zero, zero_mul]
    exact hδ.le
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hn)
  have hlog : 0 < Real.log (2 * Fintype.card n / δ) := Real.log_pos (by
    rw [one_lt_div hδ]; nlinarith [(Nat.one_le_cast (α := ℝ)).mpr (Fintype.card_pos_iff.mpr hn)])
  rcases isEmpty_or_nonempty m with hm | hm
  · exfalso
    rw [Fintype.card_eq_zero (α := m), Nat.cast_zero] at hsize
    have : 0 < 196 * (c : ℝ) ^ 2 * Real.log (2 * Fintype.card n / δ) /
        (Fintype.card n * τ ^ 2) := by positivity
    linarith
  obtain ⟨i⟩ := hn
  obtain ⟨j⟩ := hm
  have hc1 : (1 : ℝ) ≤ c := hvar i j ▸ (hsub i j).integral_sq_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hτc : τ ^ 2 / (c : ℝ) ^ 2 ≤ τ / c := by
    rw [sq, sq, ← div_mul_div_comm]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one hc0).mpr (hτ1.trans hc1))
  have hle : Real.log (2 * Fintype.card n / δ) ≤
      hansonWrightConstant * (Fintype.card m * Fintype.card n * (τ ^ 2 / (c : ℝ) ^ 2)) := by
    rw [div_le_iff₀ (by positivity)] at hsize
    have hy : Real.log (2 * Fintype.card n / δ) ≤
        1 / 196 * (Fintype.card m * Fintype.card n * (τ ^ 2 / (c : ℝ) ^ 2)) := by
      rw [mul_div_assoc', mul_div_assoc', le_div_iff₀ (by positivity)]
      linarith
    exact hy.trans (by gcongr; exact le_hansonWrightConstant)
  calc 2 * (Fintype.card n : ℝ) * Real.exp (-(hansonWrightConstant *
        (Fintype.card m * Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) ≤
      2 * Fintype.card n * Real.exp (-Real.log (2 * Fintype.card n / δ)) := by
        rw [min_eq_left hτc]; gcongr
    _ = δ := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

/-- Scaling a measure by the inverse of the mass of the probe spectral measure. -/
private theorem measureReal_inv_mass_smul (P R : Measure ℝ) (S : Set ℝ) :
    ((P Set.univ)⁻¹ • R).real S = (P.real Set.univ)⁻¹ * R.real S := by
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

/-- Scaling a measure by the inverse of the mass of $P$ gives mass $1$ when the masses agree. -/
private theorem measureReal_inv_mass_smul_univ {P R : Measure ℝ}
    (hPR : R.real Set.univ = P.real Set.univ) (hP : 0 < P.real Set.univ) :
    ((P Set.univ)⁻¹ • R).real Set.univ = 1 := by
  rw [measureReal_inv_mass_smul, hPR]
  exact inv_mul_cancel₀ hP.ne'

/-- On the good event, the empirical measure and the normalised probe measure are close against
Lipschitz test functions: the distribution functions differ by at most $2\tau$. -/
private theorem abs_integral_empirical_sub_normalised_probe_le [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m ℝ) {τ : ℝ}
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ)
    (hτ : 0 ≤ τ) (hMpos : 0 < (probeSpectralMeasure A Ω).real Set.univ) {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂empiricalSpectralMeasure A -
      ∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω)| ≤
      L * (b - a) * (2 * τ) := by
  have hM : |(probeSpectralMeasure A Ω).real Set.univ - 1| ≤ τ := by
    rw [abs_sub_comm]
    exact hA.abs_one_sub_probeSpectralMeasure_real_univ_le hK
  have hfin := Matrix.finite_real_spectrum (A := A)
  have hνs : ∀ᵐ x ∂empiricalSpectralMeasure A, x ∈ hfin.toFinset :=
    (hA.ae_mem_spectrum_empiricalSpectralMeasure).mono fun x hx => hfin.mem_toFinset.mpr hx
  have hρs : ∀ᵐ x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω),
      x ∈ hfin.toFinset := Measure.ae_smul_measure
    ((ae_mem_spectrum_probeSpectralMeasure A Ω).mono fun x hx => hfin.mem_toFinset.mpr hx) _
  -- normalising moves the probe distribution function by `(u / M) |M - 1| ≤ τ`
  have hK2 : ∀ x ∈ hfin.toFinset, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      ((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω).real (Set.Iic x)| ≤
        2 * τ := by
    intro x hx
    rw [measureReal_inv_mass_smul]
    set M := (probeSpectralMeasure A Ω).real Set.univ
    set u := (probeSpectralMeasure A Ω).real (Set.Iic x)
    set v := (empiricalSpectralMeasure A).real (Set.Iic x)
    have hinv : |M⁻¹ * u| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), inv_mul_le_iff₀ hMpos, mul_one]
      exact measureReal_mono (Set.subset_univ _)
    have e : v - M⁻¹ * u = (v - u) + M⁻¹ * u * (M - 1) := by
      field_simp
      ring
    calc |v - M⁻¹ * u| ≤ |v - u| + |M⁻¹ * u| * |M - 1| := by
          rw [e, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ τ + 1 * τ := add_le_add (hK x (hfin.mem_toFinset.mp hx))
          (mul_le_mul hinv hM (abs_nonneg _) zero_le_one)
      _ = 2 * τ := by ring
  have hfν := hf.continuousOn.integrable_of_ae_mem_Icc
    ((hA.ae_mem_spectrum_empiricalSpectralMeasure).mono fun x hx => hs hx)
  have hfρ := hf.continuousOn.integrable_of_ae_mem_Icc
    (Measure.ae_smul_measure (ae_mem_Icc_probeSpectralMeasure A hs Ω)
      (probeSpectralMeasure A Ω Set.univ)⁻¹)
  have hg : LipschitzOnWith L (fun x => f x - f b) (Set.Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    simpa only [dist_sub_right] using hf.dist_le_mul x hx y hy
  have hmain := MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith hνs hρs
    (fun x hx => hs (hfin.mem_toFinset.mp hx)) hab.le hg (by linarith) hK2
  simp only [sub_self, abs_zero, zero_add] at hmain
  rw [integral_sub hfν (integrable_const _), integral_sub hfρ (integrable_const _)] at hmain
  have hρ1 : ((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω).real Set.univ =
      1 := measureReal_inv_mass_smul_univ rfl hMpos
  simpa [integral_const, hρ1, sub_sub_sub_cancel_right] using hmain

/-- The normalised probe measure and the normalised SLQ measure differ, against Lipschitz test
functions, by the Gauss-rule term: Jackson's polynomial and moment matching. -/
private theorem abs_integral_normalised_probe_sub_slq_le
    {A : Matrix n n ℝ} {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m ℝ) (q : ℕ)
    (hMpos : 0 < (probeSpectralMeasure A Ω).real Set.univ)
    (hQM : (slqMeasure A Ω (q + 1)).real Set.univ = (probeSpectralMeasure A Ω).real Set.univ)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω) -
      ∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • slqMeasure A Ω (q + 1))| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * q + 3) := by
  have hmatch := (matchesMoments_probeSpectralMeasure_slqMeasure A Ω (q + 1)).smul
    (probeSpectralMeasure A Ω Set.univ)⁻¹
  have hPne : probeSpectralMeasure A Ω Set.univ ≠ 0 := fun h => by
    simp [measureReal_def, h] at hMpos
  have := (slqMeasure A Ω (q + 1)).smul_finite (ENNReal.inv_ne_top.2 hPne)
  have hPab := Measure.ae_smul_measure (ae_mem_Icc_probeSpectralMeasure A hs Ω)
    (probeSpectralMeasure A Ω Set.univ)⁻¹
  have hQab := Measure.ae_smul_measure (ae_mem_Icc_slqMeasure A hs Ω (q + 1))
    (probeSpectralMeasure A Ω Set.univ)⁻¹
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) hab hf (2 * q + 1)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  have h := hmatch.abs_integral_sub_integral_le_of_isUniformApproxOn hPab hQab
    (hf.continuousOn.integrable_of_ae_mem_Icc hPab) (hf.continuousOn.integrable_of_ae_mem_Icc hQab)
    hp' hε
  rw [measureReal_inv_mass_smul_univ rfl hMpos, measureReal_inv_mass_smul_univ hQM hMpos] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

/-- Deterministic step for the normalised SLQ measure: on the Kolmogorov-good event, every
Lipschitz test function is within the normalised SLQ error. -/
private theorem abs_integral_sub_integral_slq_le_of_hK
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m ℝ) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hτ1 : τ < 1)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂empiricalSpectralMeasure A -
        ∫ x, f x ∂((slqMeasure A Ω (q + 1) Set.univ)⁻¹ • slqMeasure A Ω (q + 1))| ≤
      L * (b - a) * (2 * τ) + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : empiricalSpectralMeasure A = 0 := by simp [empiricalSpectralMeasure]
    have h1 : slqMeasure A Ω (q + 1) = 0 := by simp [slqMeasure]
    simp only [h0, h1, integral_zero_measure, sub_zero, abs_zero, smul_zero]
    have := jacksonApproximationConstant_pos
    have : 0 ≤ b - a := by linarith
    positivity
  have hM : |1 - (probeSpectralMeasure A Ω).real Set.univ| ≤ τ :=
    Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le hA hK
  have hMpos : 0 < (probeSpectralMeasure A Ω).real Set.univ := by linarith [abs_le.mp hM]
  have hQM : (slqMeasure A Ω (q + 1)).real Set.univ = (probeSpectralMeasure A Ω).real Set.univ :=
    ((matchesMoments_probeSpectralMeasure_slqMeasure A Ω (q + 1)).measureReal_univ_eq
      (by omega)).symm
  have hQP : slqMeasure A Ω (q + 1) Set.univ = probeSpectralMeasure A Ω Set.univ :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hQM
  rw [hQP]
  have h1 := abs_integral_empirical_sub_normalised_probe_le hA hab hs Ω hK hτ hMpos hf
  have h2 := abs_integral_normalised_probe_sub_slq_le hab hs Ω q hMpos hQM hf
  have h3 := abs_sub_le (∫ x, f x ∂empiricalSpectralMeasure A)
    (∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω))
    (∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • slqMeasure A Ω (q + 1)))
  linarith

/-- **The mass-normalised SLQ measure approximates the spectral density, uniformly in Lipschitz
test functions.** Let the entries of the real $n \times m$ test matrix $\mathbf{\Omega}$ be
independent, each satisfying the sub-Gaussian moment generating function bound with variance
proxy $c$ and having second moment $1$; let $\mathbf{A}$ be real symmetric with spectrum in
$[a, b]$, $a < b$; let $L \ge 0$, $q \in \mathbb{N}$ and $0 \le \tau < 1$. Then, except with
probability at most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
the SLQ measure divided by its mass satisfies, for every $f$ that is $L$-Lipschitz on
$[a, b]$, <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\frac{\mathsf{slqMeasure}(\mathbf{A},
\mathbf{\Omega},q+1)}{\mathsf{slqMeasure}(\mathbf{A},\mathbf{\Omega},q+1)(\mathbb{R})}\Bigr\rvert
\le 2L(b - a)\tau + \frac{\pi L(b - a)}{2q + 3}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constants are `hansonWrightConstant` and
`jacksonApproximationConstant`. Both measures are probability measures, so there is no term in
$\lvert f(b)\rvert$; $\tau < 1$ keeps the mass positive. Junk: for empty $n$ the normalisation is
$\infty \cdot 0 = 0$ and the event is empty.
[ChenTrogdonUbaru2021, Theorem 1]; there for probes
uniform on the sphere, whose SLQ measure has mass $1$.
Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_smul_slqMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) (q : ℕ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * (2 * τ) + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂((slqMeasure A (X ω) (q + 1) Set.univ)⁻¹ • slqMeasure A (X ω) (q + 1))|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have hEv : {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * (2 * τ) + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂((slqMeasure A (X ω) (q + 1) Set.univ)⁻¹ • slqMeasure A (X ω) (q + 1))|} ⊆
      {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
        (probeSpectralMeasure A (X ω)).real (Set.Iic x)|} := by
    rintro ω ⟨f, hf, hlt⟩
    by_contra hcon
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hcon
    exact absurd hlt (not_lt.mpr (abs_integral_sub_integral_slq_le_of_hK hA hab hs (X ω) q hτ hτ1
      hcon hf))
  have := hind.isProbabilityMeasure
  refine (measureReal_mono hEv).trans ?_
  exact measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
    hind hsub hvar hA hτ

end NLAlib
