/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.ForMathlib.Probability.Moments.Variance
public import NLAlib.LowRank.Gaussian.GeneralizedNystrom
public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Structural.Truncation

/-!
# Truncated generalized Nyström in expectation

For independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$, the Lean
`X`) and $\mathbf{\Psi}$ ($m \times p$), the late truncation
$\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k$ of generalized
Nyström (`NLAlib.generalizedNystrom`, `NLAlib.truncatedSVD`) reaches relative error
$1 + \varepsilon$ in expectation with $\ell = O(k/\varepsilon)$ and $p = O(k/\varepsilon^2)$:
for $4k \le \ell$ and $4\ell \le p$ the expected squared Frobenius error is at most a named
factor times $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, a factor at
most $1 + \varepsilon$ at $\ell \ge 6k/\varepsilon$, $p \ge 8000\ell/\varepsilon$. Both sizes
$O(k/\varepsilon)$ suffice by the localized perturbed truncation, in
`NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystromRate`
(in namespace `NLAlib`,
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_of_hasLaw_gaussianMatrix` and
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_of_hasLaw_gaussianMatrix`).
The proof
combines the perturbed truncation lemma
`NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm` (the spectral norm of
the core noise enters with weight $\sqrt{k}$), the expected error of the truncated randomized SVD,
the spectral core noise of Gaussian sketch-and-solve
(`integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix`)
conditionally on $\mathbf{\Omega}$, and the second spectral moment of the range finder at a
comparison rank near $\ell/2$
(`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound`). A second
bound, through the Frobenius norm of the core noise, has milder size conditions and better
constants at practical sizes but needs $p = O(k/\varepsilon^3)$. Every rank of $\mathbf{A}$; the
truncation is `truncatedSVD`, measurable (`NLAlib.measurable_truncatedSVD`), and both bounds hold
for every best rank-$k$ approximation of the output. Real throughout.

## Main definitions

* `NLAlib.truncatedGNFactor k l p`: the factor of the expected error, at
  present <!-- value truncatedGNFactor k \ell p -->
  $$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) +
  484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)\,.$$

## Main results

* `NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`:
  the expected error.
* [relative-error bound](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix):
  relative error $1 + \varepsilon$; its asymptotic form is
  [asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix).
* the Frobenius core-noise form:
  `integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_sqrt_of_hasLaw_gaussianMatrix`.

The exact identities for the noise in the dominant subspace and the oracle truncation are in
`NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystromOracle`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

/-! ### The truncated generalized Nyström factor -/

/-- **The truncated generalized Nyström factor**: the multiplier of
$\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ in the expected squared
Frobenius error of truncated generalized Nyström with independent Gaussian test matrices of sizes
$\ell$ and $p$, for $4k \le \ell$ and $4\ell \le p$
(`NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`),
at present <!-- value truncatedGNFactor k \ell p -->
$$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) +
484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)\,.$$
For $0 < \varepsilon \le 1$, it is at most $1 + \varepsilon$ at $\ell \ge 6k/\varepsilon$,
$p \ge 8000\ell/\varepsilon$ (`NLAlib.truncatedGNFactor_le_one_add`).
Source value: none; proved here without a matching published bound. Value proved: as displayed;
the triangle inequality alone gives a squared-error factor of $9$
(`NLAlib.IsBestRankApprox.matrixNorm_sub_le_add_two_mul`).
Consumers use `NLAlib.one_le_truncatedGNFactor` and `NLAlib.truncatedGNFactor_le_one_add`.
Junk for $\ell \le k + 1$ with $k \ge 1$; the theorems carry `4 * k ≤ l`. -/
noncomputable irreducible_def truncatedGNFactor (k l p : ℕ) : ℝ :=
  gaussianProjectionFactor k l +
    4 * √(2 * k * ((25 * gaussianProjectionFactor k l + 484) / p)) +
      8 * k * ((25 * gaussianProjectionFactor k l + 484) / p)

/-- The explicit value the documentation displays: the truncated generalized Nyström factor is at
most <!-- value truncatedGNFactor k \ell p -->
$$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) +
484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)$$
(at present an equality). -/
theorem truncatedGNFactor_le (k l p : ℕ) :
    truncatedGNFactor k l p ≤
      1 + (k : ℝ) / ((l : ℝ) - k - 1) +
        4 * √(2 * k * ((25 * (1 + (k : ℝ) / ((l : ℝ) - k - 1)) + 484) / p)) +
          8 * k * ((25 * (1 + (k : ℝ) / ((l : ℝ) - k - 1)) + 484) / p) := by
  rw [truncatedGNFactor_def, gaussianProjectionFactor_def]

/-- The truncated generalized Nyström factor is at least $1$: for
$4k \le \ell$, <!-- value truncatedGNFactor k \ell p -->
$$1 \le 1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}
\Bigr) + 484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)\,.$$ -/
theorem one_le_truncatedGNFactor {k l p : ℕ} (h : 4 * k ≤ l) : 1 ≤ truncatedGNFactor k l p := by
  rw [truncatedGNFactor_def]
  have hg : 1 ≤ gaussianProjectionFactor k l := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [gaussianProjectionFactor_def, Nat.cast_zero, zero_div, add_zero, le_refl]
    · exact one_le_gaussianProjectionFactor (by omega)
  have hc : 0 ≤ (25 * gaussianProjectionFactor k l + 484) / p :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h1 : 0 ≤ 4 * √(2 * k * ((25 * gaussianProjectionFactor k l + 484) / p)) := by positivity
  have h2 : 0 ≤ 8 * k * ((25 * gaussianProjectionFactor k l + 484) / p) := by positivity
  linarith

/-- The explicit comparison of the truncated generalized Nyström factor: for
$0 < \varepsilon \le 1$, $6k \le \varepsilon\ell$ and
$8000\,\ell \le \varepsilon p$, <!-- value truncatedGNFactor k \ell p -->
$$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}
\Bigr) + 484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr) \le
1 + \varepsilon\,.$$ -/
theorem truncatedGNFactor_le_one_add {k l p : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hl : 6 * (k : ℝ) ≤ ε * l) (hp : 8000 * (l : ℝ) ≤ ε * p) :
    truncatedGNFactor k l p ≤ 1 + ε := by
  rw [truncatedGNFactor_def]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [gaussianProjectionFactor_def, Nat.cast_zero, zero_div, add_zero, mul_zero,
      zero_mul, Real.sqrt_zero]
    linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : 6 * (k : ℝ) ≤ l := by nlinarith
  have hp0 : (0 : ℝ) < p := by nlinarith
  have hden : 0 < (l : ℝ) - k - 1 := by linarith
  set g := gaussianProjectionFactor k l with hgdef
  have hg : g ≤ 1 + ε / 4 := by
    rw [hgdef, gaussianProjectionFactor_def, add_le_add_iff_left,
      div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have hk2 : k + 2 ≤ l := by
    have : (k : ℝ) + 2 ≤ l := by linarith
    exact_mod_cast this
  have hg1 : 1 ≤ g := one_le_gaussianProjectionFactor hk2
  set c := (25 * g + 484) / p with hcdef
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hp0.le
  have hkp : 48000 * (k : ℝ) ≤ ε ^ 2 * p := by nlinarith
  have hkc : (k : ℝ) * c ≤ 515.25 / 48000 * ε ^ 2 := by
    rw [hcdef, mul_div_assoc', div_le_iff₀ hp0]
    nlinarith
  have hs : √(2 * k * c) ≤ 0.15 * ε := by
    rw [show (0.15 : ℝ) * ε = √((0.15 * ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h8 : 8 * k * c ≤ 0.09 * ε := by nlinarith
  rw [show 2 * (k : ℝ) * c = 2 * k * c from rfl] at hs
  linarith

/-- The shared-size comparison of the truncated generalized Nyström factor, for the asymptotic
form: for $0 < \varepsilon \le 1$, $160k \le \varepsilon\ell$ and
$160\ell \le \varepsilon p$, <!-- value truncatedGNFactor k \ell p -->
$$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}
\Bigr) + 484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr) \le
1 + \varepsilon\,:$$
$k/(\ell - k - 1) \le \varepsilon/150$, $k/p \le \varepsilon^2/25600$, and
$\varepsilon/150 + 4\sqrt{1020/25600}\,\varepsilon + 8 \cdot 510\,\varepsilon^2/25600 \le
\varepsilon$. -/
private theorem truncatedGNFactor_le_one_add_of_mul_le {k l p : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hl : 160 * (k : ℝ) ≤ ε * l) (hp : 160 * (l : ℝ) ≤ ε * p) :
    truncatedGNFactor k l p ≤ 1 + ε := by
  rw [truncatedGNFactor_def]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [gaussianProjectionFactor_def, Nat.cast_zero, zero_div, add_zero, mul_zero,
      zero_mul, Real.sqrt_zero]
    linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : 160 * (k : ℝ) ≤ l := by nlinarith
  have hp0 : (0 : ℝ) < p := by nlinarith
  have hden : 0 < (l : ℝ) - k - 1 := by linarith
  set g := gaussianProjectionFactor k l with hgdef
  have hg : g ≤ 1 + ε / 150 := by
    rw [hgdef, gaussianProjectionFactor_def, add_le_add_iff_left,
      div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  set c := (25 * g + 484) / p with hcdef
  have hkp : 25600 * (k : ℝ) ≤ ε ^ 2 * p := by nlinarith
  have hkc : (k : ℝ) * c ≤ 510 / 25600 * ε ^ 2 := by
    rw [hcdef, mul_div_assoc', div_le_iff₀ hp0]
    nlinarith
  have hs : √(2 * k * c) ≤ 0.2 * ε := by
    rw [show (0.2 : ℝ) * ε = √((0.2 * ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h8 : 8 * k * c ≤ 0.16 * ε := by nlinarith
  linarith

/-! ### Helpers: the joint rank event -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

/-- The joint rank event of the two test matrices: almost surely
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}) =
\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, for any law of $\mathbf{\Omega}$ independent of a
standard Gaussian $\mathbf{\Psi}$, when every $\operatorname{rank}(\mathbf{A}\mathbf{x}) \le p$.
Proved without a literature source. -/
theorem ae_rank_conjTranspose_mul_mul_eq (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    (hr : ∀ x : Matrix n l ℝ, (A * x).rank ≤ Fintype.card p) :
    ∀ᵐ ω ∂μ, ((Ψ ω)ᴴ * (A * X ω)).rank = (A * X ω).rank := by
  have := hΨ.isProbabilityMeasure
  set E : Set (Matrix m p ℝ × Matrix n l ℝ) := {q | (q.1ᴴ * (A * q.2)).rank ≠ (A * q.2).rank}
    with hEdef
  have hE : MeasurableSet E := by
    have h1 : Measurable fun q : Matrix m p ℝ × Matrix n l ℝ => (q.1ᴴ * (A * q.2)).rank :=
      measurable_rank.comp ((continuous_id.matrix_conjTranspose.measurable.comp
        measurable_fst).matrix_mul (measurable_const.matrix_mul measurable_snd))
    have h2 : Measurable fun q : Matrix m p ℝ × Matrix n l ℝ => (A * q.2).rank :=
      measurable_rank.comp (measurable_const.matrix_mul measurable_snd)
    exact (measurableSet_eq_fun h1 h2).compl
  have hsec (x : Matrix n l ℝ) (_ : x ∈ Set.univ) : μ.real {ω | (Ψ ω, x) ∈ E} ≤ 0 := by
    have h := ae_iff.mp (ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (A * x) hΨ (hr x))
    change (μ {a | ¬((Ψ a)ᴴ * (A * x)).rank = (A * x).rank}).toReal ≤ 0
    rw [h, ENNReal.toReal_zero]
  have h := hXΨ.symm.measureReal_mem_le_add hΨ.aemeasurable hX hE MeasurableSet.univ le_rfl hsec
    (δ₂ := 0) (by simp)
  rw [add_zero] at h
  have h0 : μ {ω | (Ψ ω, X ω) ∈ E} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top μ _)).mp (le_antisymm h measureReal_nonneg)
  exact ae_iff.mpr (by simpa only [hEdef, Set.mem_ofPred_eq] using h0)

/-! ### The spectral core noise and the spectral residual -/

/-- The core noise $\mathbf{\Pi}_{\mathbf{A}\mathbf{x},\mathbf{\psi}^{\mathsf{H}}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{x}))$ is measurable in the pair. -/
theorem measurable_obliqueProjector_mul_sub_rsvd (A : Matrix m n ℝ) :
    Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      obliqueProjector (A * q.1) q.2ᴴ * (A - rsvd A q.1) := by
  have hΨ : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ => q.2ᴴ :=
    (continuous_id.matrix_conjTranspose.measurable).comp measurable_snd
  have hAX : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ => A * q.1 :=
    measurable_const.matrix_mul measurable_fst
  simp only [obliqueProjector]
  exact ((hAX.matrix_mul (measurable_pinv.comp (hΨ.matrix_mul hAX))).matrix_mul hΨ).matrix_mul
    (measurable_const.sub ((measurable_rsvd A).comp measurable_fst))

/-- The squared spectral norm of the core noise is measurable in the pair. -/
private theorem measurable_specNorm_obliqueProjector_sub_rsvd_sq (A : Matrix m n ℝ) :
    Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      specNorm (obliqueProjector (A * q.1) q.2ᴴ * (A - rsvd A q.1)) ^ 2 :=
  (continuous_specNorm.measurable.comp (measurable_obliqueProjector_mul_sub_rsvd A)).pow_const 2

-- The names of the sketch-and-solve lemmas used exceed 100 characters with their indentation.
set_option linter.style.longLine false in
/-- **The spectral core noise of generalized Nyström**: for independent standard Gaussian test
matrices, $k \ge 1$, $4k \le \ell$ and $4\ell \le p$, the core noise
$e = \|\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\|_2$ is square integrable with
$\mathbb{E}e^2 \le ((25g + 484)/p)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2$, $g$ the value of the Gaussian projection factor at $(k, \ell)$. -/
private theorem integral_specNorm_obliqueProjector_sub_rsvd_sq_le (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hk : 1 ≤ k) (hkl : 4 * k ≤ Fintype.card l)
    (hlp : 4 * Fintype.card l ≤ Fintype.card p) :
    Integrable (fun ω =>
      specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2) μ ∧
    ∫ ω, specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 ∂μ ≤
      (25 * gaussianProjectionFactor k (Fintype.card l) + 484) / Fintype.card p *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  set L := Fintype.card l with hLdef
  set P := Fintype.card p with hPdef
  have hP0 : (0 : ℝ) < P := by
    have : 0 < P := by omega
    exact_mod_cast this
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  set H : Matrix n l ℝ → ℝ := fun x => 25 / (P : ℝ) * frobNorm (A - rsvd A x) ^ 2 +
    4 * (L : ℝ) / P * specNorm (A - rsvd A x) ^ 2 with hHdef
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hS := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hid
  have hrank (x : Matrix n l ℝ) : 4 * (A * x).rank ≤ P := by
    have := Matrix.rank_le_card_width (A * x)
    omega
  have hint (x : Matrix n l ℝ) : Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p) := by
    rw [sub_rsvd]
    exact
      integrable_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_of_hasLaw_gaussianMatrix
        hS (A * x) (by have := hrank x; omega) A
  have hle (x : Matrix n l ℝ) : ∫ ψ, specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2
      ∂(gaussianMatrix m p) ≤ H x := by
    have h :=
      integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_div_card_of_hasLaw_gaussianMatrix
        hS (A * x) (hrank x) A
    rw [← sub_rsvd] at h
    refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
    have : ((A * x).rank : ℝ) ≤ L := by exact_mod_cast Matrix.rank_le_card_width (A * x)
    gcongr
  have hHi : Integrable (fun ω => H (X ω)) μ :=
    ((integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _).add
      ((integrable_specNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _)
  have hF := measurable_specNorm_obliqueProjector_sub_rsvd_sq (l := l) (p := p) A
  refine ⟨hXΨ.integrable_comp_of_integral_le hX.aemeasurable hΨ hF (fun _ => sq_nonneg _)
      (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) hHi,
    (hXΨ.integral_comp_le_of_integral_le hX.aemeasurable hΨ hF (fun _ => sq_nonneg _)
      (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) hHi).trans ?_⟩
  have hG2 := integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX
    (k := k) (by omega)
  have hR := integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix A hX hk hkl
  simp only [hHdef]
  rw [integral_add ((integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _)
      ((integrable_specNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _), integral_const_mul,
    integral_const_mul]
  have e1 : 25 / (P : ℝ) * ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      25 / (P : ℝ) * (gaussianProjectionFactor k L * frobNorm (A - truncatedSVD A k) ^ 2) :=
    mul_le_mul_of_nonneg_left hG2 (by positivity)
  have e2 : 4 * (L : ℝ) / P * ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      4 * (L : ℝ) / P * (121 / (L : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2) :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have e3 : 4 * (L : ℝ) / P * (121 / (L : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2) =
      484 / P * frobNorm (A - truncatedSVD A k) ^ 2 := by
    field_simp
    ring
  have e4 : (25 * gaussianProjectionFactor k L + 484) / P * frobNorm (A - truncatedSVD A k) ^ 2 =
      25 / (P : ℝ) * (gaussianProjectionFactor k L * frobNorm (A - truncatedSVD A k) ^ 2) +
        484 / P * frobNorm (A - truncatedSVD A k) ^ 2 := by
    ring
  linarith

/-- The Frobenius core noise of generalized Nyström: for independent standard Gaussian test
matrices, any law of the range test matrix and $\ell + 2 \le p$, the core noise
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))$ is square integrable with
$\mathbb{E}\|\mathbf{N}\|_{\mathsf{F}}^2 \le (\ell/(p - \ell - 1))\,
\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2$. -/
private theorem integral_frobNorm_obliqueProjector_sub_rsvd_sq_le (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    Integrable (fun ω =>
      frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2) μ ∧
    ∫ ω, frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 ∂μ ≤
      (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  classical
  have := hΨ.isProbabilityMeasure
  set h := (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) with hhdef
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hS := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hid
  have hr (x : Matrix n l ℝ) : (A * x).rank + 2 ≤ Fintype.card p := by
    have := Matrix.rank_le_card_width (A * x)
    omega
  have hsplit (x : Matrix n l ℝ) : ∀ᵐ ψ ∂(gaussianMatrix m p),
      frobNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2 =
        frobNorm (A - generalizedNystrom A x ψ) ^ 2 - frobNorm (A - rsvd A x) ^ 2 := by
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (A * x) hid
      (by have := hr x; omega)] with ψ hψ
    rw [frobNorm_sub_generalizedNystrom_sq hψ]
    ring
  have hgn (x : Matrix n l ℝ) : Integrable (fun ψ : Matrix m p ℝ =>
      frobNorm (A - generalizedNystrom A x ψ) ^ 2) (gaussianMatrix m p) := by
    simp only [sub_generalizedNystrom]
    exact integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix hS (A * x)
      (hr x) A
  have hint (x : Matrix n l ℝ) : Integrable (fun ψ : Matrix m p ℝ =>
      frobNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p) :=
    ((hgn x).sub (integrable_const _)).congr ((hsplit x).mono fun _ h => h.symm)
  have hle (x : Matrix n l ℝ) : ∫ ψ, frobNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2
      ∂(gaussianMatrix m p) ≤ h * frobNorm (A - rsvd A x) ^ 2 := by
    rw [integral_congr_ae (hsplit x), integral_sub (hgn x) (integrable_const _),
      integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix A x hid (hr x),
      integral_const, probReal_univ, one_smul]
    have hq := gaussianProjectionFactor_le_gaussianProjectionFactor
      (Matrix.rank_le_card_width (A * x)) hlp
    rw [gaussianProjectionFactor_def, gaussianProjectionFactor_def] at hq
    rw [gaussianProjectionFactor_def]
    nlinarith [sq_nonneg (frobNorm (A - rsvd A x))]
  have hF := (continuous_frobNorm.measurable.comp
    (measurable_obliqueProjector_mul_sub_rsvd (l := l) (p := p) A)).pow_const 2
  have hHi := (integrable_frobNorm_sub_rsvd_sq A hX).const_mul h
  exact ⟨hXΨ.integrable_comp_of_integral_le hX hΨ hF (fun _ => sq_nonneg _)
      (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) hHi,
    (hXΨ.integral_comp_le_of_integral_le hX hΨ hF (fun _ => sq_nonneg _)
      (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) hHi).trans_eq
      (integral_const_mul _ _)⟩

/-! ### Truncated generalized Nyström -/

/-- The squared Frobenius error of truncated generalized Nyström is integrable for any law of the
range test matrix independent of a Gaussian co-range test matrix, when $\ell + 2 \le p$. It is at
most $2\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
8\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2$. -/
theorem integrable_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hlp : Fintype.card l + 2 ≤ Fintype.card p) (k : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2)
      μ := by
  have := hΨ.isProbabilityMeasure
  have hgn := integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix A hX hΨ hXΨ
    (ae_of_all _ fun ω => by have := Matrix.rank_le_card_width (A * X ω); omega)
  have hm : AEStronglyMeasurable
      (fun ω => frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2) μ :=
    (((continuous_frobNorm.measurable.comp (measurable_const.sub
      ((measurable_truncatedSVD k).comp
        (measurable_generalizedNystrom A)))).pow_const 2).comp_aemeasurable
        (hX.prodMk hΨ.aemeasurable)).aestronglyMeasurable
  have hB : Integrable (fun ω => 8 * frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 +
      2 * frobNorm (A - truncatedSVD A k) ^ 2) μ :=
    (hgn.const_mul 8).add (integrable_const _)
  refine hB.mono' hm (ae_of_all _ fun ω => ?_)
  have h := (isBestRankApprox_truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k
    ).matrixNorm_sub_le_add_two_mul (lpGauge 2) A
  simp only [lpGauge_two_matrixNorm] at h
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h2 := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
  nlinarith [sq_nonneg (frobNorm (A - truncatedSVD A k) -
    2 * frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)))]

/-- **The expected error of truncated generalized Nyström**: for independent standard Gaussian
test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$) with
$4k \le \ell$ and $4\ell \le p$, <!-- value truncatedGNFactor k \ell p -->
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1} +
4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)} +
\frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
that is, $g + 4\sqrt{2kc} + 8kc$ with
$g = 1 + k/(\ell - k - 1)$ and $c = (25g + 484)/p$.
Every rank of $\mathbf{A}$; the truncation is `truncatedSVD`, and the bound holds for every best
rank-$k$ approximation of the output. Proved without a literature source; inputs
[HalkoMartinssonTropp2011, Theorems 9.1, 10.5]; [TroppWebber2023, Lemmas B.1, B.3];
[HornJohnson2013, Theorem 7.4.1.1] (through the perturbed truncation lemma). Comparison points:
[TroppYurtseverUdellCevher2017, Corollary 6.4] (the constant-2 triangle bound, first moment, never
below $3\,\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$); the Frobenius-noise
bound
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_sqrt_of_hasLaw_gaussianMatrix`
(relative error $1 + \varepsilon$ only at $p = O(k/\varepsilon^3)$, better constants below
$\ell \approx 10^3 k$); [CamanoEpperlyMeyerTropp2025, Remark 2.9] concerns a different,
core-truncated estimator and states no bound.
Result: tgn-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : 4 * k ≤ Fintype.card l) (hlp : 4 * Fintype.card l ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      truncatedGNFactor k (Fintype.card l) (Fintype.card p) *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    simp only [truncatedSVD_zero, sub_zero, integral_const, probReal_univ, one_smul]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_truncatedGNFactor hkl)
  obtain ⟨he2i, he2⟩ := integral_specNorm_obliqueProjector_sub_rsvd_sq_le A hX hΨ hXΨ hk hkl hlp
  set O := frobNorm (A - truncatedSVD A k) with hOdef
  set g := gaussianProjectionFactor k (Fintype.card l) with hgdef
  set c := (25 * g + 484) / (Fintype.card p : ℝ) with hcdef
  have hk2 : k + 2 ≤ Fintype.card l := by omega
  have hc0 : 0 ≤ c := div_nonneg (by linarith [one_le_gaussianProjectionFactor hk2])
    (Nat.cast_nonneg _)
  have hO0 : 0 ≤ O := frobNorm_nonneg _
  have hem : AEStronglyMeasurable
      (fun ω => specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) μ :=
    ((continuous_specNorm.measurable.comp
      (measurable_obliqueProjector_mul_sub_rsvd A)).comp_aemeasurable
        (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable
  have heL := (memLp_two_iff_integrable_sq hem).2 he2i
  have hei := heL.integrable one_le_two
  have hE1 : ∫ ω, specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      √c * O := by
    refine (integral_le_sqrt_integral_sq heL).trans ?_
    rw [← Real.sqrt_sq hO0, ← Real.sqrt_mul hc0]
    exact Real.sqrt_le_sqrt he2
  have hlpw : Fintype.card l ≤ Fintype.card p := by omega
  have hJ := ae_rank_conjTranspose_mul_mul_eq A hX.aemeasurable hΨ hXΨ
    fun x => (Matrix.rank_le_card_width _).trans hlpw
  have hpt : ∀ᵐ ω ∂μ, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
        4 * √(2 * (k : ℝ)) * O *
          specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) +
        8 * k * specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 := by
    filter_upwards [hJ] with ω hω
    have h := frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm hω k
    have h3 := frobNorm_sub_truncatedSVD_rsvd_sq A (X ω) k
    have hγ := frobNorm_rsvd_sub_truncatedSVD_le A (X ω) k
    have hs : √(2 * (k : ℝ)) ^ 2 = 2 * k := Real.sq_sqrt (by positivity)
    have he0 := specNorm_nonneg (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))
    have hγ' := mul_le_mul_of_nonneg_right hγ (mul_nonneg (Real.sqrt_nonneg (2 * (k : ℝ))) he0)
    nlinarith
  have hU := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k
  have hR1 : Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      4 * √(2 * (k : ℝ)) * O *
        specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) μ :=
    hU.add (hei.const_mul _)
  have hRi : Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      4 * √(2 * (k : ℝ)) * O *
        specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) +
      8 * k * specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2) μ :=
    hR1.add (he2i.const_mul _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hRi hpt).trans ?_
  rw [integral_add hR1 (he2i.const_mul _), integral_add hU (hei.const_mul _), integral_const_mul,
    integral_const_mul]
  have hU1 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk2
  have hsq : √(2 * (k : ℝ) * c) = √(2 * (k : ℝ)) * √c := Real.sqrt_mul (by positivity) c
  have h4 : 0 ≤ 4 * √(2 * (k : ℝ)) * O :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hO0
  have e1 := mul_le_mul_of_nonneg_left hE1 h4
  have e2 := mul_le_mul_of_nonneg_left he2 (by positivity : (0 : ℝ) ≤ 8 * k)
  rw [truncatedGNFactor_def, ← hgdef, ← hcdef, hsq]
  nlinarith

-- A docstring line names a declaration whose name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Truncated generalized Nyström reaches relative error $1 + \varepsilon$** with
independent standard Gaussian test matrices of sizes $\ell \ge 6k/\varepsilon$ and
$p \ge 8000\,\ell/\varepsilon$, $0 < \varepsilon \le 1$:
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`.
The bound with both sizes $O(k/\varepsilon)$ ($\ell \ge 3500004\,k/\varepsilon$, $p \ge 4\ell$) is
`NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_of_hasLaw_gaussianMatrix`
(`NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystromRate`); this one has the smaller constant for
$\ell$. Proved without a literature source.
Result: tgn-expected-error -/
theorem
    integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 6 * (k : ℝ) ≤ ε * Fintype.card l)
    (hp : 8000 * (Fintype.card l : ℝ) ≤ ε * Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hkl : 4 * k ≤ Fintype.card l := by
    have : 4 * (k : ℝ) ≤ Fintype.card l := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    exact_mod_cast this
  have hlp : 4 * Fintype.card l ≤ Fintype.card p := by
    have : 4 * (Fintype.card l : ℝ) ≤ Fintype.card p := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card l),
        Nat.cast_nonneg (α := ℝ) (Fintype.card p)]
    exact_mod_cast this
  exact (integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix A hX
    hΨ hXΨ hkl hlp).trans (mul_le_mul_of_nonneg_right (truncatedGNFactor_le_one_add hε hε1 hl hp)
      (sq_nonneg _))

-- A docstring line names a declaration whose name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(k/\varepsilon)$ and $O(\ell/\varepsilon)$ samples suffice for truncated generalized
Nyström**: there are absolute constants $C, \varepsilon_0 > 0$ such that for independent standard
Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$),
$0 < \varepsilon \le \varepsilon_0$, $\ell \ge Ck/\varepsilon$ and $p \ge C\ell/\varepsilon$,
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`
through the factor's comparison at one shared $C$; the proof takes $C = 160$ and
$\varepsilon_0 = 1$, against the explicit theorem's $6$ and $8000$ for the two sizes. It is
dominated by
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_of_hasLaw_gaussianMatrix`,
where $p = O(\ell)$ suffices.
Asymptotic:
NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: tgn-expected-error -/
theorem
    exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l p : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [Fintype l] [Fintype p] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (Ψ : Ω → Matrix m p ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → HasLaw Ψ (gaussianMatrix m p) μ → IndepFun X Ψ μ →
      0 < ε → ε ≤ ε₀ → C * ((k : ℝ) / ε) ≤ Fintype.card l →
      C * ((Fintype.card l : ℝ) / ε) ≤ Fintype.card p →
      ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨160, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l p _ _ _ _ _ μ A X Ψ k ε hX hΨ hXΨ hε hε1 hl hp
  rw [← mul_div_assoc, div_le_iff₀ hε] at hl hp
  have hl' : 160 * (k : ℝ) ≤ ε * Fintype.card l := by linarith
  have hp' : 160 * (Fintype.card l : ℝ) ≤ ε * Fintype.card p := by linarith
  have hkl : 4 * k ≤ Fintype.card l := by
    have : 4 * (k : ℝ) ≤ Fintype.card l := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    exact_mod_cast this
  have hlp : 4 * Fintype.card l ≤ Fintype.card p := by
    have : 4 * (Fintype.card l : ℝ) ≤ Fintype.card p := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card l)]
    exact_mod_cast this
  exact (integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix A hX
    hΨ hXΨ hkl hlp).trans (mul_le_mul_of_nonneg_right
      (truncatedGNFactor_le_one_add_of_mul_le hε hε1 hl' hp') (sq_nonneg _))

/-- **Truncated generalized Nyström, Frobenius core-noise form**: for independent standard Gaussian
test matrices, $k + 2 \le \ell$ and $\ell + 2 \le p$, writing $h = \ell/(p - \ell - 1)$,
the bound is <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1} +
4\sqrt{h\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)} +
4h\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Incomparable with
`NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`:
milder size conditions and better constants at practical sizes (below $\ell \approx 10^3 k$), but
relative error $1 + \varepsilon$ only at $p = O(k/\varepsilon^3)$. Proved without a literature
source; [TroppYurtseverUdellCevher2017, Corollary 6.4] is the published first-moment bound of
this kind (constant 2, triangle inequality).
Result: tgn-expected-error -/
theorem
    integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_sqrt_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (gaussianProjectionFactor k (Fintype.card l) +
          4 * √((Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
            gaussianProjectionFactor k (Fintype.card l)) +
          4 * ((Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1)) *
            gaussianProjectionFactor k (Fintype.card l)) *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  obtain ⟨hN2i, hN2⟩ := integral_frobNorm_obliqueProjector_sub_rsvd_sq_le A hX.aemeasurable hΨ hXΨ
    hlp
  set O := frobNorm (A - truncatedSVD A k) with hOdef
  set g := gaussianProjectionFactor k (Fintype.card l) with hgdef
  set h := (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) with hhdef
  have hlp' : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
  have hh0 : 0 ≤ h := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hg1 : 1 ≤ g := one_le_gaussianProjectionFactor hk
  have hO0 : 0 ≤ O := frobNorm_nonneg _
  have hG2 := integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk
  have hN2' : ∫ ω, frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 ∂μ ≤
      h * g * O ^ 2 := by
    rw [mul_assoc]
    exact hN2.trans (mul_le_mul_of_nonneg_left hG2 hh0)
  have hNm : AEStronglyMeasurable
      (fun ω => frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) μ :=
    ((continuous_frobNorm.measurable.comp
      (measurable_obliqueProjector_mul_sub_rsvd A)).comp_aemeasurable
        (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable
  have hNL := (memLp_two_iff_integrable_sq hNm).2 hN2i
  have hNi := hNL.integrable one_le_two
  have hE1 : ∫ ω, frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      √(h * g) * O := by
    refine (integral_le_sqrt_integral_sq hNL).trans ?_
    rw [← Real.sqrt_sq hO0, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hN2'
  have hlpw : Fintype.card l ≤ Fintype.card p := by omega
  have hJ := ae_rank_conjTranspose_mul_mul_eq A hX.aemeasurable hΨ hXΨ
    fun x => (Matrix.rank_le_card_width _).trans hlpw
  have hpt : ∀ᵐ ω ∂μ, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
        4 * O * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) +
        4 * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 := by
    filter_upwards [hJ] with ω hω
    have h1 := frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD hω k
    have h3 := frobNorm_sub_truncatedSVD_rsvd_sq A (X ω) k
    have hγ := frobNorm_rsvd_sub_truncatedSVD_le A (X ω) k
    have hT := frobNorm_truncatedSVD_le
      (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) (2 * k)
    have hγ0 := frobNorm_nonneg (rsvd A (X ω) - truncatedSVD (rsvd A (X ω)) k)
    have hT0 := frobNorm_nonneg
      (truncatedSVD (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) (2 * k))
    have hb := add_le_add hγ (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 2))
    have hb2 := pow_le_pow_left₀ (add_nonneg hγ0 (by positivity)) hb 2
    nlinarith
  have hU := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k
  have hR1 : Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      4 * O * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) μ :=
    hU.add (hNi.const_mul _)
  have hRi : Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      4 * O * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) +
      4 * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2) μ :=
    hR1.add (hN2i.const_mul _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hRi hpt).trans ?_
  rw [integral_add hR1 (hN2i.const_mul _), integral_add hU (hNi.const_mul _), integral_const_mul,
    integral_const_mul]
  have hU1 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk
  have e1 := mul_le_mul_of_nonneg_left hE1 (mul_nonneg (by norm_num) hO0 : 0 ≤ 4 * O)
  have e2 := mul_le_mul_of_nonneg_left hN2' (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith

end NLAlib
