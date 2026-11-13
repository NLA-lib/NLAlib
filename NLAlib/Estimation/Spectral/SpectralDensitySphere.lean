/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Spectral.SpectralDensity
public import NLAlib.RandomMatrix.Haar.Sphere

/-!
# Spectral density estimation: sphere probes

With probes $\sqrt{\lvert n\rvert}\,\mathbf{u}_j$, $\mathbf{u}_j$ independent and uniform on
the unit sphere, the probe spectral measure and the SLQ estimate are probability measures, and
the sharp sub-Gaussian proxy of Beta laws gives the failure probability
$2\lvert n\rvert\exp(-m(\lvert n\rvert + 2)\tau^2)$, with no unknown constant.
[ChenTrogdonUbaru2025].

## Main results

* The tails at one set and at every eigenvalue, the Lipschitz tail, the sample size and its
  asymptotic form (the names are too long for this list).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

-- The declaration name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The distribution of the probe spectral measure with sphere probes, at one set.** Let the
columns $\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$
be independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law
`uniformSphereVector n`), and take the probes $\sqrt{\lvert n\rvert}\,\mathbf{u}_j$. Then for
real symmetric $\mathbf{A}$, every $S \subseteq \mathbb{R}$ and every $\tau \ge 0$,
$$\mathbb{P}\bigl[\tau \le \lvert\nu_{\mathbf{A}}(S) - \mathsf{probeSpectralMeasure}(\mathbf{A},
\sqrt{\lvert n\rvert}\,\mathbf{U})(S)\rvert\bigr] \le 2\exp(-m(\lvert n\rvert + 2)\tau^2)\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure. The error is a centred mean of $m$ independent
$\mathrm{Beta}(r/2, (\lvert n\rvert - r)/2)$ variables, $r$ the rank of the spectral projector
$\mathbf{1}_S(\mathbf{A})$, with sub-Gaussian proxy $1/(2(\lvert n\rvert + 2))$; ranks $0$ and
$\lvert n\rvert$ are deterministic. Compared with
`NLAlib.measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le`
(independent sub-Gaussian entries) the exponent has no unknown constant and no minimum.
[ChenTrogdonUbaru2021, Theorem 2 and §4.1]. -/
theorem
measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (S : Set ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
        (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real S|} ≤
      2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  classical
  have hP := isStarProjection_cfc_indicator A S
  obtain ⟨V, hV, hVV⟩ := hP.exists_hasOrthonormalCols_mul_conjTranspose_eq
    (p := Fin (cfc (S.indicator fun _ => (1 : ℝ)) A).rank) (by simp)
  have hquad : ∀ z : n → ℝ, quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A) z =
      ‖WithLp.toLp 2 (Vᴴ *ᵥ z)‖ ^ 2 := fun z => by
    have h := quadForm_mul_conjTranspose_self V z
    rw [hVV] at h
    simpa using h
  have hemp : (empiricalSpectralMeasure A).real S =
      (Fintype.card (Fin (cfc (S.indicator fun _ => (1 : ℝ)) A).rank) : ℝ) / Fintype.card n := by
    rw [hA.empiricalSpectralMeasure_real S, RCLike.re_to_real, hP.trace_eq_rank, Fintype.card_fin]
  have hprobe : ∀ ω, (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real S =
      (∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ fun i => U ω i j)‖ ^ 2) / Fintype.card m := by
    intro ω
    rw [probeSpectralMeasure_real, girardHutchinson_eq_sum, RCLike.re_to_real]
    rcases eq_or_ne (Fintype.card n) 0 with h0 | h0
    · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
      have hz : ∀ z : n → ℝ, Vᴴ *ᵥ z = 0 := fun z => by
        rw [Subsingleton.elim z 0, Matrix.mulVec_zero]
      simp only [hz]
      simp
    · have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast h0
      have hcol : ∀ j, quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A)
          (√(Fintype.card n : ℝ) • fun i => U ω i j) =
          (Fintype.card n : ℝ) * ‖WithLp.toLp 2 (Vᴴ *ᵥ fun i => U ω i j)‖ ^ 2 := by
        intro j
        rw [quadForm_smul_right, hquad, star_trivial, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      have hcol' : ∀ j, (fun i => (√(Fintype.card n : ℝ) • U ω) i j) =
          √(Fintype.card n : ℝ) • fun i => U ω i j := fun j => rfl
      simp only [hcol', hcol]
      rw [← Finset.mul_sum]
      field_simp
  have key : ∀ ω, (empiricalSpectralMeasure A).real S -
      (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real S =
      -((∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ fun i => U ω i j)‖ ^ 2) / Fintype.card m -
        (Fintype.card (Fin (cfc (S.indicator fun _ => (1 : ℝ)) A).rank) : ℝ) / Fintype.card n) := by
    intro ω
    rw [hemp, hprobe ω]
    ring
  simp only [key, abs_neg]
  exact
    measureReal_abs_sum_norm_conjTranspose_mulVec_sq_div_card_sub_div_card_ge_le_of_hasLaw_uniformSphereVector
      (u := fun j ω i => U ω i j) hind hU hV hτ

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The Kolmogorov-distance tail of the probe spectral measure with sphere probes.** Let the
columns $\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$
be independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law
`uniformSphereVector n`). Then for real symmetric $\mathbf{A}$ and every $\tau \ge 0$, the
distribution functions of $\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \sqrt{\lvert n\rvert}\,\mathbf{U})$ differ by more
than $\tau$ at some eigenvalue with probability at most
$$2\lvert n\rvert\exp(-m(\lvert n\rvert + 2)\tau^2)\,:$$
a union bound over the at most $\lvert n\rvert$ eigenvalues; both distribution functions are
constant between eigenvalues, and
`Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le`
extends the bound to every threshold. [ChenTrogdonUbaru2021, Theorem 2 and §4.1].
Result: spectral-density-kolmogorov-tail -/
theorem
measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
        (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x)|} ≤
      2 * Fintype.card n * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  have hcard : A.finite_real_spectrum.toFinset.card ≤ Fintype.card n :=
    Set.ncard_eq_toFinset_card _ _ ▸ hA.ncard_spectrum_le
  have hpt := fun x =>
    measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le_of_hasLaw_uniformSphereVector
      hind hU hA (Set.Iic x) hτ
  have := hind.isProbabilityMeasure
  calc _ ≤ μ.real (⋃ x ∈ A.finite_real_spectrum.toFinset, {ω | τ ≤
          |(empiricalSpectralMeasure A).real (Set.Iic x) -
            (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x)|}) := by
        refine measureReal_mono (fun ω ⟨x, hx, h⟩ => ?_) (measure_ne_top _ _)
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
        exact ⟨x, hx, h.le⟩
    _ ≤ ∑ x ∈ A.finite_real_spectrum.toFinset, μ.real {ω | τ ≤
          |(empiricalSpectralMeasure A).real (Set.Iic x) -
            (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x)|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ A.finite_real_spectrum.toFinset.card •
          (2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2))) :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => hpt x
    _ ≤ _ := by
        rw [nsmul_eq_mul, ← mul_assoc, mul_comm (_ : ℝ) 2]
        gcongr

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **SLQ with sphere probes, uniformly in Lipschitz test functions.** Let the columns
$\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$ be
independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`);
let $\mathbf{A}$ be real symmetric with spectrum in $[a, b]$, $a < b$; let $L \ge 0$,
$q \in \mathbb{N}$ and $\tau \ge 0$. Then, except with probability at most
$2\lvert n\rvert\exp(-m(\lvert n\rvert + 2)\tau^2)$, every $f$ that is $L$-Lipschitz on
$[a, b]$ satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A},
\sqrt{\lvert n\rvert}\,\mathbf{U}, q + 1)\Bigr\rvert \le L(b - a)\tau +
\frac{\pi L(b - a)}{2q + 3}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant of the Gauss term is
`jacksonApproximationConstant`. With sphere probes the probe and SLQ measures have mass exactly
$1$, so there is no term in $\lvert f(b)\rvert$ and no factor $1 + \tau$: this is a
Wasserstein-1 bound.
Asymptotic form:
`NLAlib.exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector`.
[ChenTrogdonUbaru2021, Theorem 1]; the Jackson
step uses the local Jackson approximation bound. [ChenTrogdonUbaru2022, Appendix C, Theorem 38]
uses the damped-Chebyshev route with the larger printed constant $\pi^2/2$.
Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0)
    (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1)|} ≤
      2 * Fintype.card n * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · refine le_trans (le_of_eq ?_) (by positivity)
    convert measureReal_empty (μ := μ)
    refine Set.eq_empty_of_forall_notMem fun ω ⟨f, _, hlt⟩ => ?_
    rw [integral_empiricalSpectralMeasure, integral_slqMeasure] at hlt
    simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, div_zero, sub_zero, abs_zero] at hlt
    have := jacksonApproximationConstant_pos
    have : 0 ≤ b - a := by linarith
    have : 0 ≤ L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) := by
      positivity
    linarith
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty m with hm | hm
  · refine measureReal_le_one.trans ?_
    have : (1 : ℝ) ≤ Fintype.card n := Nat.one_le_cast.mpr Fintype.card_pos
    simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, zero_mul, neg_zero, Real.exp_zero]
    linarith
  -- Almost surely every probe has squared norm `card n`, so the probe measure has mass `1`.
  have hmass : ∀ᵐ ω ∂μ,
      (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real Set.univ = 1 := by
    have hcol : ∀ᵐ ω ∂μ, ∀ j, ‖WithLp.toLp 2 (fun i => U ω i j)‖ = 1 :=
      ae_all_iff.mpr fun j => ae_of_ae_map (hU j).aemeasurable
        ((hU j).map_eq ▸ ae_norm_eq_one_uniformSphereVector)
    filter_upwards [hcol] with ω hω
    have hn0 : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
    have h (j : m) : ‖WithLp.toLp 2 ((√(Fintype.card n : ℝ) • U ω).col j)‖ ^ 2 =
        Fintype.card n := by
      rw [show (√(Fintype.card n : ℝ) • U ω).col j = √(Fintype.card n : ℝ) • fun i => U ω i j
        from rfl, WithLp.toLp_smul, norm_smul, hω j, mul_one,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hn0.le]
    rw [hA.probeSpectralMeasure_real_univ, frobNorm_sq_eq_sum_col]
    simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  refine (measureReal_mono_ae ?_).trans
    (measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le_of_hasLaw_uniformSphereVector
      hind hU hA hτ)
  filter_upwards [hmass] with ω hω ⟨f, hf, hlt⟩
  by_contra hK
  change ¬∃ x ∈ spectrum ℝ A, _ at hK
  push Not at hK
  -- The Kolmogorov bound for `f - f b`; equal masses remove the shift.
  have h1 := hA.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le hab.le
    hs hτ hK (f := fun x => f x - f b)
    (fun x hx y hy => by simpa only [edist_sub_right] using hf hx hy)
  have h2 :=
    hA.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith hab hs
      (√(Fintype.card n : ℝ) • U ω) q hf
  rw [← hA.probeSpectralMeasure_real_univ, hω, mul_one] at h2
  have hE : ∫ x, f x - f b ∂empiricalSpectralMeasure A =
      ∫ x, f x ∂empiricalSpectralMeasure A - f b := by
    have : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [integral_empiricalSpectralMeasure, integral_empiricalSpectralMeasure,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hE, integral_sub (integrable_probeSpectralMeasure _ _ _) (integrable_const _),
    integral_const, smul_eq_mul, hω, one_mul, sub_sub_sub_cancel_right, sub_self, abs_zero,
    zero_add] at h1
  linarith [abs_sub_le (∫ x, f x ∂empiricalSpectralMeasure A)
    (∫ x, f x ∂probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω))
    (∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1))]

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **A sample size for SLQ with sphere probes.** Let the columns
$\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$ be
independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`);
let $\mathbf{A}$ be real symmetric with spectrum in $[a, b]$, $a < b$; let $L \ge 0$,
$q \in \mathbb{N}$, $\tau > 0$ and $\delta > 0$. If
$$m \ge \frac{\log(2\lvert n\rvert/\delta)}{(\lvert n\rvert + 2)\tau^2}\,,$$
then except with probability at most $\delta$ every $f$ that is $L$-Lipschitz on $[a, b]$
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A},
\sqrt{\lvert n\rvert}\,\mathbf{U}, q + 1)\Bigr\rvert \le L(b - a)\tau +
\frac{\pi L(b - a)}{2q + 3}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant of the Gauss term is
`jacksonApproximationConstant`. The sharp Beta proxy leaves no unknown constant in the sample
size. The tail form is
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector`,
and its asymptotic form is
`NLAlib.exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector`.
[ChenTrogdonUbaru2021, Theorem 1]. -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector_of_log_div_le
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0)
    (q : ℕ) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hm : Real.log (2 * Fintype.card n / δ) / ((Fintype.card n + 2) * τ ^ 2) ≤ Fintype.card m) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1)|} ≤ δ := by
  refine
    (measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector
      hind hU hA hab hs L q hτ.le).trans ?_
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · simp [hn, hδ.le]
  · have hnR : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr hn
    have hτ2 : 0 < ((Fintype.card n : ℝ) + 2) * τ ^ 2 := by positivity
    have hlog : Real.log (2 * Fintype.card n / δ) ≤
        Fintype.card m * ((Fintype.card n + 2) * τ ^ 2) := (div_le_iff₀ hτ2).mp hm
    have hpos : 0 < 2 * (Fintype.card n : ℝ) / δ := by positivity
    have hexp : Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) ≤
        δ / (2 * Fintype.card n) := by
      calc Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2))
          ≤ Real.exp (-Real.log (2 * Fintype.card n / δ)) :=
            Real.exp_le_exp.mpr (neg_le_neg (by
              linarith [mul_assoc (Fintype.card m : ℝ) (Fintype.card n + 2) (τ ^ 2)]))
        _ = δ / (2 * Fintype.card n) := by
            rw [Real.exp_neg, Real.exp_log hpos]; field_simp
    calc _ ≤ 2 * (Fintype.card n : ℝ) * (δ / (2 * Fintype.card n)) := by gcongr
      _ = δ := by field_simp

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2))$ sphere probes suffice for SLQ to
approximate the spectral density, uniformly in Lipschitz test functions**: there is an absolute
constant $C > 0$ such that the following holds. Let the columns
$\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$ be
independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`);
let $\mathbf{A}$ be real symmetric with spectrum in $[a, b]$, $a < b$; let $L \ge 0$,
$q \in \mathbb{N}$, $\tau > 0$ and $\delta > 0$. If
$m \ge C\log(2\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2)$, then except with probability at
most $\delta$ every $f$ that is $L$-Lipschitz on $[a, b]$
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A},
\sqrt{\lvert n\rvert}\,\mathbf{U}, q + 1)\Bigr\rvert \le L(b - a)\tau +
\frac{\pi L(b - a)}{2q + 3}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant of the Gauss term is
`jacksonApproximationConstant`. The constant $C$ comes before every dimension, matrix and
parameter; $C = 1$ works. Proved from
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector`
through its sample-size form
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector_of_log_div_le`.
[ChenTrogdonUbaru2021, Theorem 1].
Asymptotic:
NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector
Result: spectral-density-lipschitz-tail -/
theorem
exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω n m : Type} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
      [Fintype m] (μ : Measure Ω) (U : Ω → Matrix n m ℝ) (A : Matrix n n ℝ) (a b : ℝ)
      (L : ℝ≥0) (q : ℕ) (τ δ : ℝ),
      iIndepFun (fun j ω i => U ω i j) μ →
      (∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) → A.IsHermitian → a < b →
      spectrum ℝ A ⊆ Set.Icc a b → 0 < τ → 0 < δ →
      C * Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) ≤ Fintype.card m →
      μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1)|} ≤ δ := by
  refine ⟨1, one_pos, ?_⟩
  intro Ω n m _ _ _ _ μ U A a b L q τ δ hind hU hA hab hs hτ hδ hm
  have hm' : Real.log (2 * Fintype.card n / δ) / ((Fintype.card n + 2) * τ ^ 2) ≤
      Fintype.card m := by
    rcases le_or_gt (Real.log (2 * Fintype.card n / δ)) 0 with hl | hl
    · exact (div_nonpos_of_nonpos_of_nonneg hl (by positivity)).trans (Nat.cast_nonneg _)
    · rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
      · simp [h0]
      · have hn : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr hpos
        calc Real.log (2 * Fintype.card n / δ) / ((Fintype.card n + 2) * τ ^ 2)
            ≤ Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) :=
              div_le_div_of_nonneg_left hl.le (by positivity) (by gcongr; linarith)
          _ = 1 * Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) := by ring
          _ ≤ Fintype.card m := hm
  exact
    measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector_of_log_div_le
      hind hU hA hab hs L q hτ hδ hm'

end NLAlib
