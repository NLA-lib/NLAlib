/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowRank.Gaussian.EarlyTruncationRSVD
public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Random.RangeFinder
public import NLAlib.LowRank.Structural.EarlyTruncation
public import NLAlib.RandomMatrix.Gaussian.ClippedInverseMoments
public import NLAlib.Sketching.Gaussian.Gaussian
public import NLAlib.Regression.SketchAndSolve
public import NLAlib.Sketching.Properties.MatrixMultiplication

/-!
# Early-truncated generalized Nyström with Gaussian completion

The Gaussian co-range sketch completes the early-truncated sampled range by sketch-and-solve.
The range and co-range sketches are independent. Completion costs the exact Gaussian
regression factor at the actual rank of the truncated sketch, for any law of the range sketch.
For two Gaussian sketches, relative expected squared error $1+\varepsilon$ follows either at
$\ell\ge1600k/\varepsilon^2$, $p\ge k+1+(2+\varepsilon)k/\varepsilon$, or at
$\ell\ge\max\{900,500k/\varepsilon^2\}$, $p\ge10k/\varepsilon+10k+1$.
Standalone randomized SVD bounds are in EarlyTruncationRSVD; Haar completion is in
EarlyTruncationHaar. Design: docs/design/research/Nystrom-Constants.md.

## Main results

* [Exact completion](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix).
* [Completion for any range law](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix).
* [Relative-error composition](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le).
* [Relative-error bound](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix).
* [Range/co-range width bound](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_earlyTruncatedGNRangeDim_le).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

/-! ### A fixed range test matrix -/

/-- The squared error of early-truncated generalized Nyström with a fixed range test matrix and
a Gaussian co-range test matrix is integrable for $k + 2 \le p$. -/
private theorem integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_fixed
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - earlyTruncatedGeneralizedNystrom A X₀ (Ψ ω) k) ^ 2) μ := by
  classical
  have hr := rank_truncatedSVD_le (A * X₀) k
  simp only [sub_earlyTruncatedGeneralizedNystrom]
  exact integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hΨ) (truncatedSVD (A * X₀) k) (by omega) A

/-- **Early-truncated generalized Nyström conditionally on the range test matrix**: for a fixed
$\mathbf{\Omega}$, a standard Gaussian $m \times p$ co-range test matrix $\mathbf{\Psi}$,
$q = \operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k \le k$ and
$k + 2 \le p$, <!-- value gaussianProjectionFactor q p -->
$$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{q}{p - q - 1}\Bigr)\|\mathbf{A}-
\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2\,,$$
the factor at the actual rank $q$. Proved without a literature
source, as a composition: the completion step is [EpperlyWebber2026, Theorem 2.1]; the algorithm
is [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A X₀ (Ψ ω) k) ^ 2 ∂μ =
      gaussianProjectionFactor (truncatedSVD (A * X₀) k).rank (Fintype.card p) *
        frobNorm (A - earlyTruncatedRSVD A X₀ k) ^ 2 := by
  classical
  have hr := rank_truncatedSVD_le (A * X₀) k
  simp only [sub_earlyTruncatedGeneralizedNystrom, sub_earlyTruncatedRSVD]
  exact integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hΨ) (truncatedSVD (A * X₀) k) (by omega) A

/-! ### Any law of the range test matrix -/

/-- The completion factor at the rank of the truncated sketch is measurable in the range test
matrix. -/
private theorem measurable_gaussianProjectionFactor_rank_truncatedSVD (A : Matrix m n ℝ) (k c : ℕ) :
    Measurable fun x : Matrix n l ℝ =>
      gaussianProjectionFactor (truncatedSVD (A * x) k).rank c :=
  (measurable_from_nat (f := fun q => gaussianProjectionFactor q c)).comp
    (measurable_rank.comp ((measurable_truncatedSVD k).comp
      (measurable_const.matrix_mul measurable_id)))

/-- The completion factor at the rank of the truncated sketch lies in $[1, 1 + p]$. -/
private theorem gaussianProjectionFactor_rank_truncatedSVD_mem (A : Matrix m n ℝ)
    (x : Matrix n l ℝ) {k c : ℕ} (h : k + 2 ≤ c) :
    1 ≤ gaussianProjectionFactor (truncatedSVD (A * x) k).rank c ∧
      gaussianProjectionFactor (truncatedSVD (A * x) k).rank c ≤ 1 + c := by
  have hq : (truncatedSVD (A * x) k).rank + 2 ≤ c := by
    have := rank_truncatedSVD_le (A * x) k
    omega
  exact ⟨one_le_gaussianProjectionFactor hq, gaussianProjectionFactor_le_one_add hq⟩

/-- The right side of the conditional identity, integrated over $\mathbf{\Omega}$, is
integrable. -/
private theorem integrable_gaussianProjectionFactor_mul_earlyTruncatedRSVD [IsFiniteMeasure μ]
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω =>
      gaussianProjectionFactor (truncatedSVD (A * X ω) k).rank (Fintype.card p) *
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2) μ := by
  refine (integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX k).bdd_mul
    (c := 1 + Fintype.card p)
    ((measurable_gaussianProjectionFactor_rank_truncatedSVD A k _).comp_aemeasurable
      hX).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  obtain ⟨h1, h2⟩ := gaussianProjectionFactor_rank_truncatedSVD_mem A (X ω) hkp
  rwa [Real.norm_of_nonneg (zero_le_one.trans h1)]

/-- The conditional identity as lower integrals, over the independent pair. -/
private theorem lintegral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    ∫⁻ ω, ENNReal.ofReal (frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2)
        ∂μ =
      ∫⁻ ω, ENNReal.ofReal
        (gaussianProjectionFactor (truncatedSVD (A * X ω) k).rank (Fintype.card p) *
          frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2) ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  refine (hXΨ.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hX hΨ
    (F := fun q : Matrix n l ℝ × Matrix m p ℝ =>
      frobNorm (A - earlyTruncatedGeneralizedNystrom A q.1 q.2 k) ^ 2)
    ((continuous_frobNorm.measurable.comp
      (measurable_const.sub (measurable_earlyTruncatedGeneralizedNystrom A k))).pow_const 2)
    (fun _ => sq_nonneg _) (ae_of_all _ fun ω =>
      integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_fixed A (X ω) hid hkp)).trans
    (lintegral_congr fun ω => congrArg ENNReal.ofReal
      (integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix A (X ω)
        hid hkp))

set_option linter.style.longLine false in
-- The theorem's name alone exceeds 100 characters.
/-- **Early-truncated generalized Nyström = early-truncated randomized SVD × completion**: for any
law of $\mathbf{\Omega}$ independent of a standard Gaussian $\mathbf{\Psi}$ and
$k + 2 \le p$, <!-- value gaussianProjectionFactor k p -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{p - k - 1}\Bigr)\,\mathbb{E}\|\mathbf{A}-
\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2\,.$$
Every bound on the early-truncated randomized SVD (the subspace-embedding and
projection-cost-preserving routes, and its expectation) becomes one on early-truncated
generalized Nyström. Proved without a literature source, as a composition:
[EpperlyWebber2026, Theorem 2.1] for the completion; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card p) *
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hR := integrable_gaussianProjectionFactor_mul_earlyTruncatedRSVD A hX hkp
  have hR0 : 0 ≤ᵐ[μ] fun ω =>
      gaussianProjectionFactor (truncatedSVD (A * X ω) k).rank (Fintype.card p) *
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 :=
    ae_of_all _ fun ω => mul_nonneg (zero_le_one.trans
      (gaussianProjectionFactor_rank_truncatedSVD_mem A (X ω) hkp).1) (sq_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (aestronglyMeasurable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX
        hΨ.aemeasurable k),
    lintegral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX hΨ hXΨ hkp,
    ← integral_eq_lintegral_of_nonneg_ae hR0 hR.aestronglyMeasurable, ← integral_const_mul]
  refine integral_mono_of_nonneg hR0
    ((integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX k).const_mul _)
    (ae_of_all _ fun ω => ?_)
  exact mul_le_mul_of_nonneg_right (gaussianProjectionFactor_le_gaussianProjectionFactor
    (rank_truncatedSVD_le _ k) hkp) (sq_nonneg _)

/-- The squared error of $\mathsf{earlyTruncatedGeneralizedNystrom}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)$ is integrable for any law of $\mathbf{\Omega}$ independent of a standard
Gaussian $\mathbf{\Psi}$ and $k + 2 \le p$. -/
theorem integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2)
      μ := by
  have := hΨ.isProbabilityMeasure
  refine ⟨aestronglyMeasurable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX
    hΨ.aemeasurable k, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _),
    lintegral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX hΨ hXΨ hkp]
  exact (integrable_gaussianProjectionFactor_mul_earlyTruncatedRSVD A hX hkp).lintegral_lt_top

/-- The arithmetic of the $(1+\varepsilon)$ form: for $k \ge 1$, $\varepsilon > 0$ and
$p \ge k + 1 + (2+\varepsilon)k/\varepsilon$, $k + 2 \le p$ and
$(1 + \varepsilon/2)\,(1 + k/(p - k - 1)) \le 1 + \varepsilon$. -/
private theorem one_add_half_mul_gaussianProjectionFactor_le {k c : ℕ} {ε : ℝ} (hk : 1 ≤ k)
    (hε : 0 < ε) (hp : (k : ℝ) + 1 + (2 + ε) * k / ε ≤ c) :
    k + 2 ≤ c ∧ (1 + ε / 2) * gaussianProjectionFactor k c ≤ 1 + ε := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (2 + ε) * k / ε := by positivity
  have hd : (2 + ε) * k / ε ≤ (c : ℝ) - k - 1 := by linarith
  have hd0 : 0 < (c : ℝ) - k - 1 := hpos.trans_le hd
  have hkc : k + 2 ≤ c := by
    have h1 : (1 : ℝ) < (2 + ε) * k / ε := by
      rw [lt_div_iff₀ hε]; nlinarith
    have : (k : ℝ) + 2 < c + 1 := by linarith
    have : k + 2 < c + 1 := by exact_mod_cast this
    omega
  refine ⟨hkc, ?_⟩
  rw [gaussianProjectionFactor_def]
  have hq : (k : ℝ) / ((c : ℝ) - k - 1) ≤ ε / (2 + ε) := by
    rw [div_le_div_iff₀ hd0 (by positivity)]
    rw [div_le_iff₀ hε] at hd
    nlinarith
  calc (1 + ε / 2) * (1 + (k : ℝ) / ((c : ℝ) - k - 1)) ≤ (1 + ε / 2) * (1 + ε / (2 + ε)) := by
        gcongr
    _ = 1 + ε := by field_simp; ring

set_option linter.style.longLine false in
-- The theorem's name alone exceeds 100 characters.
/-- **Early-truncated generalized Nyström reaches relative error $1 + \varepsilon$ from a bound
on the early-truncated randomized SVD**: for any law of
$\mathbf{\Omega}$ independent of a standard Gaussian $\mathbf{\Psi}$, if the early-truncated
randomized SVD with the same $\mathbf{\Omega}$ has expected error at most
$(1 + \varepsilon/2)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ and
$p \ge k + 1 + (2+\varepsilon)k/\varepsilon$, then
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The hypothesis holds for a Gaussian $\mathbf{\Omega}$ with $\ell \ge 1600k/\varepsilon^2$ columns
(`NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`);
in this form it composes with any other bound on the early-truncated randomized SVD. Proved
without a literature source; the algorithm is [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hp : (k : ℝ) + 1 + (2 + ε) * k / ε ≤ Fintype.card p)
    (hRSVD : ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      (1 + ε / 2) * frobNorm (A - truncatedSVD A k) ^ 2) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hΨ.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) (ψ : Matrix m p ℝ) :
        earlyTruncatedGeneralizedNystrom A x ψ 0 = 0 := by
      simp only [earlyTruncatedGeneralizedNystrom, truncatedSVD_zero, obliqueProjector,
        Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  obtain ⟨hkp, hfac⟩ := one_add_half_mul_gaussianProjectionFactor_le hk hε hp
  have h1 :=
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix
      A hX hΨ hXΨ hkp
  have hg : 0 ≤ gaussianProjectionFactor k (Fintype.card p) :=
    zero_le_one.trans (one_le_gaussianProjectionFactor hkp)
  calc _ ≤ _ := h1
    _ ≤ gaussianProjectionFactor k (Fintype.card p) *
          ((1 + ε / 2) * frobNorm (A - truncatedSVD A k) ^ 2) :=
        mul_le_mul_of_nonneg_left hRSVD hg
    _ = ((1 + ε / 2) * gaussianProjectionFactor k (Fintype.card p)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by ring
    _ ≤ (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 :=
        mul_le_mul_of_nonneg_right hfac (sq_nonneg _)

set_option linter.style.longLine false in
-- The theorem's name alone exceeds 100 characters.
/-- **Early-truncated generalized Nyström reaches relative error $1 + \varepsilon$**: for
independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($m \times p$) with $\ell \ge 1600k/\varepsilon^2$,
$p \ge k + 1 + (2+\varepsilon)k/\varepsilon$ and $0 < \varepsilon \le 1$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi},
k)\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,:$$
one pass, output rank at most $k$. The early-truncated randomized SVD at accuracy
$\varepsilon/2$
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`)
composed with the Gaussian completion
(`NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le`).
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_of_hasLaw_gaussianMatrix`.
Proved without a literature source; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 1600 * (k : ℝ) ≤ ε ^ 2 * Fintype.card l)
    (hp : (k : ℝ) + 1 + (2 + ε) * k / ε ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) (ψ : Matrix m p ℝ) :
        earlyTruncatedGeneralizedNystrom A x ψ 0 = 0 := by
      simp only [earlyTruncatedGeneralizedNystrom, truncatedSVD_zero, obliqueProjector,
        Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  have hsize : earlyTruncatedRSVDRelativeErrorDim k (ε / 2) ≤ Fintype.card l := by
    rw [earlyTruncatedRSVDRelativeErrorDim_def]
    apply max_le
    · have he : ε ^ 2 ≤ 1 := by nlinarith
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    · rw [div_le_iff₀ (sq_pos_of_pos (half_pos hε))]
      nlinarith
  exact
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le
      A hX.aemeasurable hΨ hXΨ hε hp
      (integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_earlyTruncatedRSVDRelativeErrorDim_le
        A hX (half_pos hε) (by linarith) hsize)

-- A docstring line names a declaration whose name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(k/\varepsilon^2)$ and $O(k/\varepsilon)$ samples suffice for early-truncated generalized
Nyström**: there are absolute constants $C, \varepsilon_0 > 0$ such that for independent standard
Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$),
$0 < \varepsilon \le \varepsilon_0$, $\ell \ge Ck/\varepsilon^2$ and $p \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi},
k)\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`;
the proof takes $C = 1600$ and $\varepsilon_0 = 1$.
Asymptotic:
NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: etgn -/
theorem
    exists_forall_integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l p : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [Fintype l] [Fintype p] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (Ψ : Ω → Matrix m p ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → HasLaw Ψ (gaussianMatrix m p) μ → IndepFun X Ψ μ →
      0 < ε → ε ≤ ε₀ → C * ((k : ℝ) / ε ^ 2) ≤ Fintype.card l →
      C * ((k : ℝ) / ε) ≤ Fintype.card p →
      ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨1600, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l p _ _ _ _ _ μ A X Ψ k ε hX hΨ hXΨ hε hε1 hl hp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := hX.isProbabilityMeasure
    have h0 (x : Matrix n l ℝ) (ψ : Matrix m p ℝ) :
        earlyTruncatedGeneralizedNystrom A x ψ 0 = 0 := by
      simp only [earlyTruncatedGeneralizedNystrom, truncatedSVD_zero, obliqueProjector,
        Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : (k : ℝ) ≤ k / ε := (le_div_iff₀ hε).2 (by nlinarith)
  have he : (2 + ε) * k / ε = 2 * (k / ε) + k := by
    rw [add_mul, add_div, mul_div_assoc, mul_div_cancel_left₀ _ hε.ne']
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at hl
  exact
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
      A hX hΨ hXΨ hε hε1 (by linarith) (by rw [he]; linarith)

/-- The sufficient Gaussian range width for early-truncated generalized Nyström is at
present <!-- value earlyTruncatedGNRangeDim k \varepsilon -->
$\max\{900,500k/\varepsilon^2\}$.
The relative-error theorem assumes $0<\varepsilon\le1$; at $\varepsilon=0$ this total
expression equals $900$ by the inverse-of-zero convention. No printed source. -/
noncomputable irreducible_def earlyTruncatedGNRangeDim (k : ℕ) (ε : ℝ) : ℝ :=
  max 900 (500 * (k : ℝ) / ε ^ 2)

/-- The sufficient Gaussian co-range width for early-truncated generalized Nyström is at
present <!-- value earlyTruncatedGNCorangeDim k \varepsilon -->
$10k/\varepsilon+10k+1$.
The relative-error theorem assumes $0<\varepsilon\le1$; at $\varepsilon=0$ this total
expression equals $10k+1$ by the inverse-of-zero convention. No printed source. -/
noncomputable irreducible_def earlyTruncatedGNCorangeDim (k : ℕ) (ε : ℝ) : ℝ :=
  10 * (k : ℝ) / ε + 10 * k + 1

/-- The explicit value the documentation displays: the sufficient Gaussian range width is at
most <!-- value earlyTruncatedGNRangeDim k \varepsilon -->$\max\{900,500k/\varepsilon^2\}$ (at
present an equality). -/
theorem earlyTruncatedGNRangeDim_le (k : ℕ) (ε : ℝ) :
    earlyTruncatedGNRangeDim k ε ≤ max 900 (500 * (k : ℝ) / ε ^ 2) := by
  rw [earlyTruncatedGNRangeDim_def]

/-- The explicit value the documentation displays: the sufficient Gaussian co-range width is at
most <!-- value earlyTruncatedGNCorangeDim k \varepsilon -->$10k/\varepsilon+10k+1$ (at present
an equality). -/
theorem earlyTruncatedGNCorangeDim_le (k : ℕ) (ε : ℝ) :
    earlyTruncatedGNCorangeDim k ε ≤ 10 * (k : ℝ) / ε + 10 * k + 1 := by
  rw [earlyTruncatedGNCorangeDim_def]

/-- The Gaussian completion factor with nine tenths of the accuracy allocated to the range. -/
private theorem gaussianProjectionFactor_mul_one_add_nine_div_ten_le {k c : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hkc : k + 2 ≤ c)
    (hc : 10 * (k : ℝ) / ε + 10 * k + 1 ≤ c) :
    gaussianProjectionFactor k c * (1 + 9 * ε / 10) ≤ 1 + ε := by
  have hkc' : (k : ℝ) + 2 ≤ c := by exact_mod_cast hkc
  have hd : 0 < (c : ℝ) - k - 1 := by linarith
  have hh := mul_le_mul_of_nonneg_right hc hε.le
  have hcancel : (10 * (k : ℝ) / ε) * ε = 10 * k := div_mul_cancel₀ _ hε.ne'
  have hcross : (k : ℝ) * (10 + 9 * ε) ≤ ε * ((c : ℝ) - k - 1) := by
    nlinarith
  have hf : (k : ℝ) / ((c : ℝ) - k - 1) ≤ ε / (10 + 9 * ε) :=
    (div_le_div_iff₀ hd (by linarith)).2 hcross
  have hmul := mul_le_mul_of_nonneg_right hf
    (show 0 ≤ 1 + 9 * ε / 10 by linarith)
  have he : ε / (10 + 9 * ε) * (1 + 9 * ε / 10) = ε / 10 := by
    field_simp
  rw [he] at hmul
  rw [gaussianProjectionFactor_def]
  nlinarith

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Early-truncated generalized Nyström reaches relative error** with independent standard
Gaussian range and co-range matrices: for $0<\varepsilon\le1$,
$\ell\ge\max\{900,500k/\varepsilon^2\}$ and $p\ge10k/\varepsilon+10k+1$, its expected squared
Frobenius error is at most $(1+\varepsilon)$ times the optimal squared error.
$$\mathbb E\|\mathbf A-\mathsf{earlyTruncatedGN}(\mathbf A,\mathbf\Omega,\mathbf\Psi,k)
\|_{\mathsf F}^2\le(1+\varepsilon)
\|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2\,.$$
No printed source.
Result: etgn -/
theorem
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_earlyTruncatedGNRangeDim_le
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hl : earlyTruncatedGNRangeDim k ε ≤ Fintype.card l)
    (hp : earlyTruncatedGNCorangeDim k ε ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) (ψ : Matrix m p ℝ) :
        earlyTruncatedGeneralizedNystrom A x ψ 0 = 0 := by
      simp only [earlyTruncatedGeneralizedNystrom, truncatedSVD_zero, obliqueProjector,
        Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  rw [earlyTruncatedGNRangeDim_def] at hl
  rw [earlyTruncatedGNCorangeDim_def] at hp
  have hsize : earlyTruncatedRSVDRelativeErrorDim k (9 * ε / 10) ≤ Fintype.card l := by
    rw [earlyTruncatedRSVDRelativeErrorDim_def]
    apply max_le ((le_max_left _ _).trans hl)
    rw [div_le_iff₀ (by positivity : 0 < (9 * ε / 10) ^ 2)]
    have hh := (le_max_right (900 : ℝ) _).trans hl
    rw [div_le_iff₀ (sq_pos_of_pos hε)] at hh
    nlinarith
  have hkc : k + 2 ≤ Fintype.card p := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hh : 0 ≤ 10 * (k : ℝ) / ε := by positivity
    have ht : (k : ℝ) + 2 ≤ Fintype.card p := by linarith
    exact_mod_cast ht
  have hR :=
    integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_earlyTruncatedRSVDRelativeErrorDim_le
      A hX (by positivity : 0 < 9 * ε / 10) (by linarith) hsize
  have hC :=
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix
      A hX.aemeasurable hΨ hXΨ hkc
  have hg := zero_le_one.trans (one_le_gaussianProjectionFactor hkc)
  have hh := mul_le_mul_of_nonneg_left hR hg
  have hf := gaussianProjectionFactor_mul_one_add_nine_div_ten_le hε hkc hp
  have hfinal := mul_le_mul_of_nonneg_right hf
    (sq_nonneg (frobNorm (A - truncatedSVD A k)))
  nlinarith [hC, hh, hfinal]

end NLAlib
