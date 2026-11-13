/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Orthogonal.Gauss
public import NLAlib.Estimation.Trace.GirardHutchinson
public import NLAlib.Estimation.Trace.StochasticLanczosQuadrature
public import NLAlib.ForMathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Spectral density estimation

Two random estimates of the empirical spectral measure $\nu_{\mathbf{A}}$ of a Hermitian
$\mathbf{A}$ from a test matrix $\mathbf{\Omega}$ whose $m$ columns are the probes. The **probe
spectral measure** is the average of the probes' spectral measures (probe densities)
$\mu_j = \mu_{\mathbf{A},\boldsymbol{\omega}_j}$, scaled by $1/(\lvert n\rvert m)$: its integral
of $f$ is the Girard–Hutchinson estimate of $\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$, and
for isotropic probes it is $\nu_{\mathbf{A}}$ in expectation. The **SLQ spectral-density
estimate** is the same average of the $q$-point Gauss rules of the probe densities, what $q$
Lanczos steps per probe compute: atoms at each probe's Ritz values. It is not the Gauss rule of
the probe spectral measure: it has up to $mq$ nodes and matches $2q$ moments of it. Neither is a
probability measure in general; their masses are
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$.
[ChenTrogdonUbaru2021]; [UbaruChenSaad2017].

The probe spectral measure integrates $f$ to the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$, so its distribution function at $x$ is a
Girard–Hutchinson estimate of a spectral projector; it is unbiased for isotropic probes. The SLQ
estimate is the average of the Lanczos rules, matches $2q$ moments of the probe spectral measure
and equals it for $q \ge \lvert n\rvert$. If the distribution functions of the probe spectral
measure and of the empirical spectral measure are close at the eigenvalues, a finite Abel
summation bounds the error on every Lipschitz test function at once. The random tails are in
`NLAlib/Estimation/Spectral/SpectralDensitySubgaussian.lean` (independent sub-Gaussian entries)
and `NLAlib/Estimation/Spectral/SpectralDensitySphere.lean` (probes uniform on the sphere).

## Main definitions

* `NLAlib.probeSpectralMeasure`: the average of the probe densities.
* `NLAlib.slqMeasure`: the average of their Gauss rules.

## Main results

* `NLAlib.isFiniteMeasure_probeSpectralMeasure`, `NLAlib.isFiniteMeasure_slqMeasure`: both are
  finite measures.
* `NLAlib.integral_probeSpectralMeasure`, `NLAlib.integral_slqMeasure`: the integrals are the
  Girard–Hutchinson and SLQ trace estimates, divided by $\lvert n\rvert$.
* `Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature`: the SLQ measure is what the Lanczos
  algorithm computes.
* `NLAlib.probeSpectralMeasure_real`: the probe spectral measure of a set is a Girard–Hutchinson
  estimate.
* `NLAlib.matchesMoments_probeSpectralMeasure_slqMeasure`,
  `Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le`: moment matching and
  exactness.
* `NLAlib.integral_integral_probeSpectralMeasure`: unbiasedness for isotropic probes.
* `Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le`:
  the deterministic bound over Lipschitz test functions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The **probe spectral measure**: the average of the probes' spectral measures (probe
densities), scaled so that isotropic probes give the empirical spectral measure in expectation,
$$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) :=
\frac{1}{\lvert n\rvert m}\sum_{j=1}^m \mu_{\mathbf{A},\boldsymbol{\omega}_j}\,,$$
$\boldsymbol{\omega}_1, \dots, \boldsymbol{\omega}_m$ the columns of $\mathbf{\Omega}$. It is SLQ
with exact quadrature (`Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le`); its
integral of $f$ is the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$ (`integral_probeSpectralMeasure`). Mass
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$. Junk value: $0$ when $n$ or $m$ is empty
($0^{-1} = 0$ in $\mathbb{R}_{\ge 0}$) and when $\mathbf{A}$ is not Hermitian.
[ChenTrogdonUbaru2021, §1.1]. -/
noncomputable def probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) : Measure ℝ :=
  ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) • ∑ j, spectralMeasure A (fun i => Ω i j)

/-- The **SLQ spectral-density estimate**: the average, scaled as `probeSpectralMeasure`, of the
$q$-point Gauss rules of the probe densities,
$$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) := \frac{1}{\lvert n\rvert m}\sum_{j=1}^m
\mathsf{gaussQuadrature}(\mu_{\mathbf{A},\boldsymbol{\omega}_j}, q)\,,$$
$\boldsymbol{\omega}_1, \dots, \boldsymbol{\omega}_m$ the columns of $\mathbf{\Omega}$. It is not
the Gauss rule of `probeSpectralMeasure`: it has up to $mq$ nodes and matches $2q$ moments of it.
For Hermitian $\mathbf{A}$ it is the average of the Lanczos rules, atoms at each probe's Ritz
values (`Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature`). Its integral of $f$ is
$\operatorname{Re}\,\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)/\lvert n\rvert$
(`integral_slqMeasure`). Junk value: $0$ when $n$ or $m$ is empty or $q = 0$.
[ChenTrogdonUbaru2021, §1.1]; [UbaruChenSaad2017, §3, Algorithm 1]. -/
noncomputable def slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) : Measure ℝ :=
  ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) •
    ∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q

/-- The probe spectral measure is a finite measure (the definition is not reducible, so the
instances for sums and scalar multiples are not found through it). -/
instance isFiniteMeasure_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    IsFiniteMeasure (probeSpectralMeasure A Ω) := by
  unfold probeSpectralMeasure
  infer_instance

/-- The SLQ spectral-density estimate is a finite measure. -/
instance isFiniteMeasure_slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) :
    IsFiniteMeasure (slqMeasure A Ω q) := by
  unfold slqMeasure
  infer_instance

/-! ### Integrals and the Lanczos form -/

private lemma re_div_natCast (z : 𝕜) (k : ℕ) : RCLike.re (z / (k : 𝕜)) = RCLike.re z / k := by
  rw [← RCLike.ofReal_natCast, RCLike.div_re_ofReal]

/-- Every function is integrable against the probe spectral measure: for every square
$\mathbf{A}$, every test matrix $\mathbf{\Omega}$ and every $f : \mathbb{R} \to \mathbb{R}$, $f$
is integrable against $\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$, a finite atomic
measure. -/
theorem integrable_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (f : ℝ → ℝ) :
    Integrable f (probeSpectralMeasure A Ω) := by
  unfold probeSpectralMeasure
  exact (integrable_finsetSum_measure.2 fun j _ =>
    integrable_spectralMeasure _ _ f).smul_measure_nnreal

/-- Every function is integrable against the SLQ spectral-density estimate: for every square
$\mathbf{A}$, every test matrix $\mathbf{\Omega}$, every $q$ and every
$f : \mathbb{R} \to \mathbb{R}$, $f$ is integrable against
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)$, a finite sum of Dirac masses. -/
theorem integrable_slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) (f : ℝ → ℝ) :
    Integrable f (slqMeasure A Ω q) := by
  unfold slqMeasure
  exact (integrable_finsetSum_measure.mpr fun j _ =>
    integrable_gaussQuadrature _ _ _).smul_measure_nnreal

/-- The probe spectral measure integrates every $f$ to the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$: for every square $\mathbf{A}$, every
$f : \mathbb{R} \to \mathbb{R}$ and every test matrix $\mathbf{\Omega}$,
$$\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) =
\frac{\operatorname{Re}\,\mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})}{\lvert n\rvert}\,;$$
both sides vanish off Hermitian. With $f = T_k$ these are the moments of the kernel polynomial
method. -/
theorem integral_probeSpectralMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) :
    ∫ x, f x ∂probeSpectralMeasure A Ω =
      RCLike.re (girardHutchinson (cfc f A) Ω) / Fintype.card n := by
  unfold probeSpectralMeasure
  rw [integral_smul_nnreal_measure, integral_finsetSum_measure, girardHutchinson_eq_sum,
    re_div_natCast,
    map_sum]
  · simp only [integral_spectralMeasure, NNReal.smul_def, smul_eq_mul, NNReal.coe_inv,
      NNReal.coe_mul, NNReal.coe_natCast]
    ring
  · exact fun i _ => integrable_spectralMeasure _ _ _

/-- The SLQ spectral-density estimate integrates every $f$ to the SLQ trace estimate divided by
$\lvert n\rvert$: for every square $\mathbf{A}$, every $f : \mathbb{R} \to \mathbb{R}$, every
test matrix $\mathbf{\Omega}$ and every $q$,
$$\int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) =
\frac{\operatorname{Re}\,\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)}{\lvert n\rvert}\,.$$ -/
theorem integral_slqMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ∫ x, f x ∂slqMeasure A Ω q = RCLike.re (slq A f Ω q) / Fintype.card n := by
  unfold slqMeasure slq
  rw [integral_smul_nnreal_measure, integral_finsetSum_measure]
  · rw [← RCLike.ofReal_natCast (Fintype.card m), ← RCLike.ofReal_div, RCLike.ofReal_re]
    simp only [NNReal.smul_def, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast, smul_eq_mul]
    field_simp
  · exact fun j _ => integrable_gaussQuadrature _ _ _

/-- **The SLQ measure is the average of the probes' Lanczos rules**: for Hermitian $\mathbf{A}$,
every test matrix $\mathbf{\Omega}$ with columns $\boldsymbol{\omega}_j$ and every $q$,
$$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) = \frac{1}{\lvert n\rvert m}\sum_{j=1}^m
\mathsf{lanczosQuadrature}(\mathbf{A}, \boldsymbol{\omega}_j, q)\,,$$
the identification of each probe's Gauss rule with its Lanczos rule; atoms at the Ritz values,
weights from the tridiagonal matrices (`Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`).
[MartinssonTropp2020, §6.6]; there for the trace estimate. -/
theorem _root_.Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) (q : ℕ) :
    slqMeasure A Ω q = ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) •
      ∑ j, lanczosQuadrature A (fun i => Ω i j) q := by
  unfold slqMeasure
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (hA.lanczosQuadrature_eq_gaussQuadrature _ q).symm

/-! ### Distribution functions, masses and supports -/

/-- The probe spectral measure of every set is a Girard–Hutchinson estimate: for every square
$\mathbf{A}$, every test matrix $\mathbf{\Omega}$ and every $S \subseteq \mathbb{R}$,
$$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})(S) =
\frac{\operatorname{Re}\,\mathsf{girardHutchinson}(\mathbf{1}_S(\mathbf{A}),
\mathbf{\Omega})}{\lvert n\rvert}\,,$$
$\mathbf{1}_S(\mathbf{A})$ the spectral projector of $S$, an orthogonal projector
(`isStarProjection_cfc_indicator`). No measurability of $S$ is needed. -/
theorem probeSpectralMeasure_real (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (S : Set ℝ) :
    (probeSpectralMeasure A Ω).real S =
      RCLike.re (girardHutchinson (cfc (S.indicator fun _ => (1 : ℝ)) A) Ω) /
        Fintype.card n := by
  unfold probeSpectralMeasure
  rw [measureReal_def, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_smul, ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)]
  simp only [← measureReal_def, spectralMeasure_real, girardHutchinson_eq_sum, Finset.sum_div,
    map_sum]
  simp only [re_div_natCast, Finset.smul_sum, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The mass of the probe spectral measure: for Hermitian $\mathbf{A}$ and every test matrix
$\mathbf{\Omega}$,
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})(\mathbb{R}) =
\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$. -/
theorem _root_.Matrix.IsHermitian.probeSpectralMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) :
    (probeSpectralMeasure A Ω).real Set.univ =
      frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m) := by
  unfold probeSpectralMeasure
  simp only [Measure.real, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_smul, ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)]
  have h : ∑ j, ((spectralMeasure A fun i => Ω i j) Set.univ).toReal = frobNorm Ω ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    exact Finset.sum_congr rfl fun j _ => hA.spectralMeasure_real_univ (fun i => Ω i j)
  rw [h, NNReal.smul_def, NNReal.coe_inv, NNReal.coe_mul, smul_eq_mul, div_eq_inv_mul]
  push_cast
  rfl

/-- The mass of the SLQ spectral-density estimate: for Hermitian $\mathbf{A}$, every test matrix
$\mathbf{\Omega}$ and $q > 0$,
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)(\mathbb{R}) =
\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$, the mass of the probe spectral measure. -/
theorem _root_.Matrix.IsHermitian.slqMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) {q : ℕ} (hq : 0 < q) :
    (slqMeasure A Ω q).real Set.univ =
      frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m) := by
  obtain ⟨a, a', hs⟩ := exists_spectrum_subset_Icc A
  have hg : ∀ j, (gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q).real Set.univ =
      ‖WithLp.toLp 2 (Ω.col j)‖ ^ 2 := fun j => by
    rw [gaussQuadrature_real_univ (ae_mem_Icc_spectralMeasure A hs _) hq,
      hA.spectralMeasure_real_univ]
    rfl
  have hsum : (∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q).real Set.univ =
      ∑ j, (gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q).real Set.univ := by
    simp only [measureReal_def, Measure.coe_finsetSum, Finset.sum_apply,
      ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)]
  unfold slqMeasure
  rw [measureReal_nnreal_smul_apply, hsum, Finset.sum_congr rfl fun j _ => hg j,
    ← frobNorm_sq_eq_sum_col, NNReal.coe_inv, NNReal.coe_mul]
  push_cast
  ring

/-- The probe spectral measure lives on the spectrum: for every square $\mathbf{A}$ and every
test matrix $\mathbf{\Omega}$, almost every point of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ is an eigenvalue of $\mathbf{A}$. -/
theorem ae_mem_spectrum_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    ∀ᵐ x ∂probeSpectralMeasure A Ω, x ∈ spectrum ℝ A := by
  unfold probeSpectralMeasure
  rw [ae_iff, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_zero]
  right
  exact Finset.sum_eq_zero fun j _ => spectralMeasure_compl_spectrum_eq_zero A _

/-- The probe spectral measure lives in every interval containing the spectrum: for every square
$\mathbf{A}$ with spectrum in $[a, a']$ and every test matrix $\mathbf{\Omega}$, almost every
point of $\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ lies in $[a, a']$. -/
theorem ae_mem_Icc_probeSpectralMeasure (A : Matrix n n 𝕜) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (Ω : Matrix n m 𝕜) :
    ∀ᵐ x ∂probeSpectralMeasure A Ω, x ∈ Set.Icc a a' := by
  filter_upwards [ae_mem_spectrum_probeSpectralMeasure A Ω] with x hx
  exact hs hx

/-- The SLQ spectral-density estimate lives in every interval containing the spectrum: for
$\mathbf{A}$ with spectrum in $[a, a']$, every test matrix $\mathbf{\Omega}$ and every
$q$, almost every point of $\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)$ lies in
$[a, a']$: the Ritz values lie between the extreme eigenvalues. -/
theorem ae_mem_Icc_slqMeasure (A : Matrix n n 𝕜) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (Ω : Matrix n m 𝕜) (q : ℕ) :
    ∀ᵐ x ∂slqMeasure A Ω q, x ∈ Set.Icc a a' := by
  have hprobe : ∀ j, ∀ᵐ x ∂spectralMeasure A (fun i => Ω i j), x ∈ Set.Icc a a' :=
    fun j => ae_mem_Icc_spectralMeasure A hs _
  have hgauss : ∀ j, ∀ᵐ x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q,
      x ∈ Set.Icc a a' := fun j => ae_mem_Icc_gaussQuadrature (hprobe j) q
  have hsum : ∀ᵐ x ∂(∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q),
      x ∈ Set.Icc a a' := by
    simp only [ae_iff, Measure.coe_finsetSum, Finset.sum_apply] at hgauss ⊢
    exact Finset.sum_eq_zero fun j _ => hgauss j
  unfold slqMeasure
  rw [ae_iff] at hsum ⊢
  rw [Measure.smul_apply, hsum, smul_zero]

/-! ### Moments and exactness -/

/-- **SLQ matches $2q$ moments of the probe spectral measure**: for every $\mathbf{A}$, every
test matrix $\mathbf{\Omega}$ and every $q$,
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ and
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)$ give every real polynomial of degree less
than $2q$ the same integral: each probe density matches $2q$ moments of its Gauss rule, and the
averages match. [Gautschi2004, Theorem 1.45]; [GolubMeurant2010, Ch. 6]; there for one measure,
here probe by probe and averaged.
Result: gauss-quadrature -/
theorem matchesMoments_probeSpectralMeasure_slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜)
    (q : ℕ) :
    MatchesMoments (probeSpectralMeasure A Ω) (slqMeasure A Ω q) (2 * q) := by
  obtain ⟨a, a', hs⟩ := exists_spectrum_subset_Icc A
  have hprobe : ∀ j, ∀ᵐ x ∂spectralMeasure A (fun i => Ω i j), x ∈ Set.Icc a a' :=
    fun j => ae_mem_Icc_spectralMeasure A hs _
  have hper : ∀ j, MatchesMoments (spectralMeasure A (fun i => Ω i j))
      (gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q) (2 * q) :=
    fun j => matchesMoments_gaussQuadrature (hprobe j) q
  have hsum : MatchesMoments (∑ j, spectralMeasure A (fun i => Ω i j))
      (∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q) (2 * q) :=
    MatchesMoments.finsetSum (fun j _ => hprobe j)
      (fun j _ => ae_mem_Icc_gaussQuadrature (hprobe j) q) (fun j _ => hper j)
  unfold probeSpectralMeasure slqMeasure
  exact MatchesMoments.smul hsum _

/-- With at least $\lvert n\rvert$ nodes SLQ is exact: for Hermitian $\mathbf{A}$, every test
matrix $\mathbf{\Omega}$ and $q \ge \lvert n\rvert$,
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) =
\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$: each probe density lives on at most
$\lvert n\rvert \le q$ points, so it is its own $q$-point Gauss rule. -/
theorem _root_.Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) {q : ℕ}
    (hq : Fintype.card n ≤ q) : slqMeasure A Ω q = probeSpectralMeasure A Ω := by
  obtain ⟨a, a', hs⟩ := exists_spectrum_subset_Icc A
  have hcard : A.finite_real_spectrum.toFinset.card ≤ q :=
    (Set.ncard_eq_toFinset_card _ _ ▸ hA.ncard_spectrum_le).trans hq
  unfold slqMeasure probeSpectralMeasure
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  symm
  refine MatchesMoments.eq_gaussQuadrature (a := a) (b := a') (MatchesMoments.refl _ _)
    ?_ ?_ hcard
  · exact ae_mem_Icc_spectralMeasure A hs _
  · have h0 := spectralMeasure_compl_spectrum_eq_zero A (fun i => Ω i j)
    exact (ae_iff.mpr h0).mono fun x hx => by simpa using hx

/-! ### Unbiasedness -/

/-- **The probe spectral measure is unbiased**: if every probe (column of the random test matrix
$\mathbf{\Omega}$) is isotropic and $m$ is nonempty, then for Hermitian $\mathbf{A}$ and every
$f : \mathbb{R} \to \mathbb{R}$,
$$\mathbb{E}\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) =
\int f\,d\nu_{\mathbf{A}}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure. No independence of the probes is needed:
Gaussian, sign, and $\sqrt{\lvert n\rvert}$ times uniform-sphere or Haar-frame probes are
instances. With $f = \mathbf{1}_S$, the expected measure of every Borel set is
$\nu_{\mathbf{A}}(S)$. [ChenTrogdonUbaru2021, §1.1].
Result: probe-spectral-measure-unbiased -/
theorem integral_integral_probeSpectralMeasure [Nonempty m] {X : Ω → Matrix n m 𝕜}
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    ∫ ω, (∫ x, f x ∂probeSpectralMeasure A (X ω)) ∂μ = ∫ x, f x ∂empiricalSpectralMeasure A := by
  have hint : Integrable (fun ω => girardHutchinson (cfc f A) (X ω)) μ := by
    simp only [girardHutchinson_eq_sum]
    exact (integrable_finsetSum _ fun j _ => (hX j).integrable_quadForm (cfc f A)).div_const _
  calc ∫ ω, (∫ x, f x ∂probeSpectralMeasure A (X ω)) ∂μ
      = ∫ ω, RCLike.re (girardHutchinson (cfc f A) (X ω)) / Fintype.card n ∂μ := by
        simp only [integral_probeSpectralMeasure]
    _ = (∫ ω, RCLike.re (girardHutchinson (cfc f A) (X ω)) ∂μ) / Fintype.card n :=
        integral_div _ _
    _ = RCLike.re (∫ ω, girardHutchinson (cfc f A) (X ω) ∂μ) / Fintype.card n := by
        rw [integral_re hint]
    _ = RCLike.re (cfc f A).trace / Fintype.card n := by
        rw [integral_girardHutchinson hX]
    _ = ∫ x, f x ∂empiricalSpectralMeasure A := (hA.integral_empiricalSpectralMeasure f).symm

/-! ### Deterministic bounds over Lipschitz test functions -/

/-- Distribution functions control Lipschitz test functions: for Hermitian $\mathbf{A}$ with
spectrum in $[a, b]$, $a \le b$, a test matrix $\mathbf{\Omega}$ and $\tau \ge 0$: if at every
eigenvalue $x$ the distribution functions of $\nu_{\mathbf{A}}$ (the empirical spectral measure)
and of $\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$,
then every $f$ that is $L$-Lipschitz on $[a, b]$ has
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} -
\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})\Bigr\rvert \le
(\lvert f(b)\rvert + L(b - a))\tau\,.$$ -/
theorem
_root_.Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a b : ℝ} (hab : a ≤ b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) {Ω : Matrix n m 𝕜} {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂probeSpectralMeasure A Ω| ≤
      (|f b| + L * (b - a)) * τ := by
  exact MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith
    (by
      filter_upwards [hA.ae_mem_spectrum_empiricalSpectralMeasure] with x hx
      exact A.finite_real_spectrum.mem_toFinset.2 hx)
    (by
      filter_upwards [ae_mem_spectrum_probeSpectralMeasure A Ω] with x hx
      exact A.finite_real_spectrum.mem_toFinset.2 hx)
    (fun x hx => hs (A.finite_real_spectrum.mem_toFinset.1 hx)) hab hf hτ
    (fun x hx => hK x (A.finite_real_spectrum.mem_toFinset.1 hx))

/-- The Kolmogorov event controls the mass: for Hermitian $\mathbf{A}$, $n$ nonempty, and a
test matrix $\mathbf{\Omega}$: if at every eigenvalue the distribution functions of
$\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$, then
$\lvert 1 - \mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})(\mathbb{R})\rvert \le
\tau$, the mass being $\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$: at the largest
eigenvalue both distribution functions equal the masses. -/
theorem _root_.Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Ω : Matrix n m 𝕜} {τ : ℝ}
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ) :
    |1 - (probeSpectralMeasure A Ω).real Set.univ| ≤ τ := by
  classical
  have hpos : 0 < Fintype.card n := Fintype.card_pos
  have hx : eigenvalue A 0 ∈ spectrum ℝ A := hA.eigenvalue_mem_spectrum hpos
  have hle : ∀ y ∈ spectrum ℝ A, y ≤ eigenvalue A 0 := by
    rw [hA.spectrum_eq_image_eigenvalue]
    rintro _ ⟨k, hk, rfl⟩
    exact hA.eigenvalue_le_eigenvalue (Nat.zero_le k) (Set.mem_Iio.mp hk)
  have h1 : (empiricalSpectralMeasure A).real (Set.Iic (eigenvalue A 0)) = 1 :=
    (measureReal_congr (Filter.eventuallyEq_set.2
      ((hA.ae_mem_spectrum_empiricalSpectralMeasure).mono fun y hy =>
        ⟨fun _ => Set.mem_univ _, fun _ => hle y hy⟩))).trans probReal_univ
  have h2 : (probeSpectralMeasure A Ω).real (Set.Iic (eigenvalue A 0)) =
      (probeSpectralMeasure A Ω).real Set.univ :=
    measureReal_congr (Filter.eventuallyEq_set.2
      ((ae_mem_spectrum_probeSpectralMeasure A Ω).mono fun y hy =>
        ⟨fun _ => Set.mem_univ _, fun _ => hle y hy⟩))
  have := hK _ hx
  rwa [h1, h2] at this

/-- From the eigenvalues to every threshold: for Hermitian $\mathbf{A}$, a test matrix
$\mathbf{\Omega}$ and $\tau \ge 0$, if at every eigenvalue the distribution functions of
$\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$, then they
differ by at most $\tau$ at every $x \in \mathbb{R}$: both are constant between eigenvalues and
$0$ below the smallest. -/
theorem
_root_.Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Ω : Matrix n m 𝕜} {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ) (x : ℝ) :
    |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ := by
  -- both measures live on the spectrum, so sets agreeing there have the same mass
  have hcongr : ∀ (μ : Measure ℝ) (S T : Set ℝ), (∀ᵐ y ∂μ, y ∈ spectrum ℝ A) →
      (∀ y ∈ spectrum ℝ A, y ∈ S ↔ y ∈ T) → μ.real S = μ.real T := by
    intro μ S T hμ hST
    refine MeasureTheory.measureReal_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hμ] with y hy
    exact hST y hy
  have hE : ∀ᵐ y ∂empiricalSpectralMeasure A, y ∈ spectrum ℝ A :=
    hA.ae_mem_spectrum_empiricalSpectralMeasure
  have hP : ∀ᵐ y ∂probeSpectralMeasure A Ω, y ∈ spectrum ℝ A :=
    ae_mem_spectrum_probeSpectralMeasure A Ω
  by_cases hex : ∃ y ∈ spectrum ℝ A, y ≤ x
  · -- x' is the largest eigenvalue ≤ x; Iic x and Iic x' agree on the spectrum
    set F := A.finite_real_spectrum.toFinset.filter (· ≤ x) with hF
    have hne : F.Nonempty := by
      obtain ⟨y, hy, hyx⟩ := hex
      exact ⟨y, Finset.mem_filter.2 ⟨A.finite_real_spectrum.mem_toFinset.2 hy, hyx⟩⟩
    have hmem := Finset.mem_filter.1 (F.max'_mem hne)
    have hmax : ∀ y ∈ spectrum ℝ A, y ≤ x ↔ y ≤ F.max' hne := by
      intro y hy
      exact ⟨fun hyx => Finset.le_max' _ _
          (Finset.mem_filter.2 ⟨A.finite_real_spectrum.mem_toFinset.2 hy, hyx⟩),
        fun h => le_trans h hmem.2⟩
    have hx' : F.max' hne ∈ spectrum ℝ A := A.finite_real_spectrum.mem_toFinset.1 hmem.1
    rw [hcongr _ (Set.Iic x) (Set.Iic (F.max' hne)) hE (fun y hy => by simpa using hmax y hy),
      hcongr _ (Set.Iic x) (Set.Iic (F.max' hne)) hP (fun y hy => by simpa using hmax y hy)]
    exact hK _ hx'
  · -- no eigenvalue is ≤ x: both masses of Iic x vanish
    have hno : ∀ y ∈ spectrum ℝ A, y ∉ Set.Iic x := fun y hy h => hex ⟨y, hy, h⟩
    rw [hcongr _ (Set.Iic x) ∅ hE (fun y hy => by simp [hno y hy]),
      hcongr _ (Set.Iic x) ∅ hP (fun y hy => by simp [hno y hy])]
    simpa using hτ

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The quadrature term, uniformly in Lipschitz test functions.** For Hermitian $\mathbf{A}$
with spectrum in $[a, b]$, $a < b$, every test matrix $\mathbf{\Omega}$, every $q$, and every $f$
that is $L$-Lipschitz on $[a, b]$, <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) -
\int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q + 1)\Bigr\rvert \le
\frac{\pi L(b - a)}{2q + 3}\cdot\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{\lvert n\rvert m}\,;$$
the constant is `jacksonApproximationConstant`. Per probe, the Gauss-rule error for Lipschitz
functions (Jackson's polynomial of degree $2q + 1$) is at most
$\pi L(b - a)\mu_j(\mathbb{R})/(2q + 3)$, $\mu_j$ the probe density; averaging gives the bound.
[ChenTrogdonUbaru2025, Lemma 3.7 and Theorem 3.10], for the quadrature-to-polynomial
comparison. The local Jackson approximation bound improves the constant after interval rescaling;
[ChenTrogdonUbaru2022, Appendix C, Theorem 38] uses the damped-Chebyshev route
with the larger printed constant $\pi^2/2$. -/
theorem
_root_.Matrix.IsHermitian.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m 𝕜) (q : ℕ) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂probeSpectralMeasure A Ω - ∫ x, f x ∂slqMeasure A Ω (q + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
        (frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m)) := by
  have hper : ∀ j ∈ Finset.univ,
      |∫ x, f x ∂spectralMeasure A (fun i => Ω i j) -
        ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) (q + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
        (spectralMeasure A (fun i => Ω i j)).real Set.univ := fun j _ =>
    abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith
      (ae_mem_Icc_spectralMeasure A hs _) hab hf q
  have hP : ∫ x, f x ∂probeSpectralMeasure A Ω =
      ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ) *
        ∑ j, ∫ x, f x ∂spectralMeasure A (fun i => Ω i j) := by
    unfold probeSpectralMeasure
    rw [integral_smul_nnreal_measure, integral_finsetSum_measure fun j _ =>
      integrable_spectralMeasure _ _ _]
    simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_inv]
  have hQ : ∫ x, f x ∂slqMeasure A Ω (q + 1) =
      ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ) *
        ∑ j, ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) (q + 1) := by
    unfold slqMeasure
    rw [integral_smul_nnreal_measure, integral_finsetSum_measure fun j _ =>
      integrable_gaussQuadrature _ _ _]
    simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_inv]
  have hmass : ∑ j, (spectralMeasure A (fun i => Ω i j)).real Set.univ = frobNorm Ω ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    exact Finset.sum_congr rfl fun j _ => hA.spectralMeasure_real_univ _
  rw [hP, hQ, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ))]
  calc ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ) *
        |∑ j, (∫ x, f x ∂spectralMeasure A (fun i => Ω i j) -
          ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) (q + 1))|
      ≤ ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ) *
          ∑ j, jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
            (spectralMeasure A (fun i => Ω i j)).real Set.univ := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hper)
    _ = jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
          (frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m)) := by
        rw [← Finset.mul_sum, hmass]
        push_cast
        ring

end NLAlib
