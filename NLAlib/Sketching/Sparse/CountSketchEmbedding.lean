/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Subspaces.Leverage
public import NLAlib.Sketching.Properties.JohnsonLindenstrauss
public import NLAlib.Sketching.Properties.Oblivious
public import NLAlib.Sketching.Properties.ProjectionCost
public import NLAlib.Sketching.Properties.TraceMoment
public import NLAlib.Sketching.Sparse.CountSketch

/-!
# CountSketch as a subspace embedding

The embedding guarantees of the CountSketch `NLAlib.countSketch` of
`NLAlib/Sketching/Sparse/CountSketch.lean`, from the exact second moment of approximate matrix
multiplication proved there: the exact mean of the squared Gram error of an orthonormal
$\mathbf{U}$, the trace moment at $q = 1$ with bound $(d^2 + d)/\lvert k \rvert$, the oblivious
subspace embedding and injection with failure probability
$(d^2 + d)/(\lvert k \rvert \varepsilon^2)$, the JL moment at $p = 2$, the sizes, and the
projection-cost-preserving sketch. Every bound is the same over $\mathbb{R}$ and $\mathbb{C}$.

Degenerate cases are those of the law (`NLAlib/Sketching/Sparse/CountSketch.lean`): for empty `k`
and nonempty `n`, `HasLaw` forces $\mu = 0$ and every tail holds; when both are empty the law
is Dirac at the empty matrix. Hence `[Nonempty k]` on the OSI only; dimension
$d = 0$ makes every bound $0$, and for $d > \lvert n \rvert$ the OSE at $d$ is the one at
$\lvert n \rvert$. Split from `NLAlib/Sketching/Sparse/CountSketch.lean` (2026-10-16),
the `Haar.lean` and `HaarEmbedding.lean` precedent.

## Main definitions

* `NLAlib.countSketchEmbeddingDim`: the number of rows; for dimension $d$ the OSE
  needs <!-- value countSketchEmbeddingDim d \varepsilon \delta -->
  $\lvert k \rvert \ge (d^2 + d)/(\delta \varepsilon^2)$.

## Main results

* `HasOrthonormalCols.integral_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch`
  (in `NLAlib`), `NLAlib.hasGramTraceMoment_of_hasLaw_countSketch`: the Gram error and the
  trace moment.
* `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch`,
  `NLAlib.isObliviousSubspaceInjection_of_hasLaw_countSketch`: the CountSketch OSE and OSI.
* `NLAlib.hasJLMoment_of_hasLaw_countSketch`: the JL moment at $p = 2$.
* `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le`,
  `NLAlib.isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le`,
  `NLAlib.hasJLMoment_of_hasLaw_countSketch_of_le_card`: sizes.
* `NLAlib.exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_countSketch`: the asymptotic
  form, $O(d^2/(\delta \varepsilon^2))$ rows.
* `NLAlib.hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card`,
  `NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_countSketch`: a CountSketch is a
  projection-cost-preserving sketch, $O((d + 1)^2/(\varepsilon^2\delta))$ rows.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n q r : Type*} [Fintype k] [Fintype n] [DecidableEq k]
  {S : Ω → Matrix k n 𝕜} {ε δ : ℝ}

/-! ### The Gram error and the embedding -/

section Gram

variable [Fintype r] [DecidableEq r] {U : Matrix n r 𝕜}

omit [DecidableEq k] [Fintype r] [DecidableEq r] in
/-- The sketched Gram matrix, expanded. -/
private theorem conjTranspose_mul_mul_self_eq (A : Matrix k n 𝕜) (U : Matrix n r 𝕜) :
    (A * U)ᴴ * (A * U) = Uᴴ * Aᴴ * A * U := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The squared Gram error of a CountSketch on the columns of any $\mathbf{U}$ is integrable. -/
theorem integrable_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch k n) μ) (U : Matrix n r 𝕜) :
    Integrable (fun ω => frobNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ 2) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  have hX := integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch hS U U
  refine ((hX.const_mul 2).add (integrable_const (2 * frobNorm (Uᴴ * U - 1) ^ 2))).mono' ?_ ?_
  · have hc : Continuous fun A : Matrix k n 𝕜 => frobNorm ((A * U)ᴴ * (A * U) - 1) ^ 2 :=
      (continuous_frobNorm.comp (by fun_prop)).pow 2
    exact (hc.measurable.comp_aemeasurable hS.aemeasurable).aestronglyMeasurable
  · refine ae_of_all _ fun ω => ?_
    have e : (S ω * U)ᴴ * (S ω * U) - 1 =
        (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U) + (Uᴴ * U - 1) := by
      rw [conjTranspose_mul_mul_self_eq]
      abel
    have h := frobNorm_add_le (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U) (Uᴴ * U - 1)
    have h0 := frobNorm_nonneg (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U)
    have h1 := frobNorm_nonneg (Uᴴ * U - 1)
    have hsq := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), e, Pi.add_apply]
    nlinarith [sq_nonneg (frobNorm (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U) - frobNorm (Uᴴ * U - 1))]

/-- **The exact mean of the squared Gram error** of a CountSketch for $\mathbf{U}$ with orthonormal
columns, $d = \lvert r \rvert$:
$$\mathbb{E}\|(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U} - \mathbf{I}\|_{\mathsf{F}}^2
= \frac{d^2 + \|\mathbf{U}^{\mathsf{T}}\mathbf{U}\|_{\mathsf{F}}^2 -
2 \sum_i \ell_i^2}{\lvert k \rvert}\,,$$
$\ell_i$ the leverage scores (`NLAlib.leverageScore`); over $\mathbb{R}$ the middle term is $d$.
The AMM identity at $\mathbf{A} = \mathbf{B} = \mathbf{U}$. Proved without a literature source.
Result: countsketch-second-moment -/
theorem HasOrthonormalCols.integral_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    (hU : HasOrthonormalCols U) (hS : HasLaw S (countSketch k n) μ) :
    ∫ ω, frobNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ 2 ∂μ =
      ((Fintype.card r : ℝ) ^ 2 + frobNorm (Uᵀ * U) ^ 2 - 2 * ∑ i, leverageScore U i ^ 2) /
        Fintype.card k := by
  have e (ω : Ω) : (S ω * U)ᴴ * (S ω * U) - 1 = Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U := by
    rw [conjTranspose_mul_mul_self_eq, show Uᴴ * U = 1 from hU]
  have hl (i : n) : ‖WithLp.toLp 2 (U i)‖ ^ 2 * ‖WithLp.toLp 2 (U i)‖ ^ 2 =
      leverageScore U i ^ 2 := by
    rw [hU.leverageScore_eq]
    ring
  simp only [e]
  rw [integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch hS U U,
    hU.frobNorm_sq]
  simp only [hl]
  ring

/-- **The trace moment of a CountSketch** at $q = 1$: for $\mathbf{U}$ with orthonormal columns
and $d = \lvert r \rvert$,
$$\mathbb{E}\|(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U} - \mathbf{I}\|_{\mathsf{F}}^2
\le \frac{d^2 + d}{\lvert k \rvert}\,.$$
[Woodruff2014, Theorem 9 and the discussion following it] (the
proof of Meng and Mahoney and of Nelson and Nguyen, as Woodruff describes it). The exact mean
with $\|\mathbf{U}^{\mathsf{T}}\mathbf{U}\|_{\mathsf{F}}^2 \le d$. -/
theorem hasGramTraceMoment_of_hasLaw_countSketch (hS : HasLaw S (countSketch k n) μ)
    (hU : HasOrthonormalCols U) :
    HasGramTraceMoment S U 1 (((Fintype.card r : ℝ) ^ 2 + Fintype.card r) / Fintype.card k) μ := by
  have e (ω : Ω) : RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * 1)).trace =
      frobNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ 2 := by
    have hH : ((S ω * U)ᴴ * (S ω * U) - 1).IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_self _).sub Matrix.isHermitian_one
    rw [frobNorm_sq_eq_re_trace, hH.eq, mul_one, sq]
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact integrable_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch hS U
  · simp only [e]
    rw [hU.integral_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch hS]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have h1 : frobNorm (Uᵀ * U) ^ 2 ≤ Fintype.card r := by
      rw [← hU.frobNorm_sq]
      have h := frobNorm_mul_le_specNorm_mul_frobNorm Uᵀ U
      rw [specNorm_transpose] at h
      exact pow_le_pow_left₀ (frobNorm_nonneg _)
        (h.trans (mul_le_of_le_one_left (frobNorm_nonneg _) hU.specNorm_le_one)) 2
    have h2 : 0 ≤ ∑ i, leverageScore U i ^ 2 := by positivity
    linarith

end Gram

/-- **CountSketch OSE**: for $\varepsilon > 0$, a CountSketch is an oblivious subspace embedding
for dimension $d$ with constants $1 \mp \varepsilon$ and failure probability
$$\frac{d^2 + d}{\lvert k \rvert \varepsilon^2}\,.$$
[Woodruff2014, Theorem 9] (there $O(d^2/(\delta\varepsilon^2))$ rows, after Meng and Mahoney and
Nelson and Nguyen; Woodruff's own route through Theorems 13 and 14 reaches
$18 d^2/(\delta\varepsilon^2)$). The constant is the proof's; the second-moment route is Meng and
Mahoney 2013 and Nelson and Nguyen 2013 (Woodruff, Theorem 9), neither in hand, so the constant is
not attributed.
Result: sparse-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_countSketch (hS : HasLaw S (countSketch k n) μ)
    (d : ℕ) (hε : 0 < ε) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε)
      (((d : ℝ) ^ 2 + d) / (Fintype.card k * ε ^ 2)) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  have h := isObliviousSubspaceEmbedding_of_hasGramTraceMoment (S := S)
    (p := Fin (min d (Fintype.card n))) (q := 1)
    (by rw [Fintype.card_fin]; exact min_le_right _ _)
    (fun U hU => hasGramTraceMoment_of_hasLaw_countSketch hS hU) hε
  intro U hU
  refine (h U ?_).mono le_rfl le_rfl ?_
  · rw [Fintype.card_fin]
    exact le_min hU (Matrix.rank_le_card_width U)
  · have hc : ((min d (Fintype.card n) : ℕ) : ℝ) ≤ d := Nat.cast_le.2 (min_le_left _ _)
    rw [Fintype.card_fin, mul_one, div_div]
    exact div_le_div_of_nonneg_right (by gcongr) (by positivity)

/-- **CountSketch OSI**: for $\varepsilon > 0$ and nonempty `k`, a CountSketch is an oblivious
subspace injection for dimension $d$ with constant $1 - \varepsilon$ and failure probability
$$(d^2 + d)/(\lvert k \rvert \varepsilon^2) \,:$$
the lower half of the OSE, with isotropy.
[CamanoEpperlyMeyerTropp2025, Definition 1.2] for the notion; their Table 3 lists CountSketch only
as an OSE, with $k = O(r^2)$.
Result: countsketch-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_countSketch [Nonempty k] [DecidableEq n]
    (hS : HasLaw S (countSketch k n) μ) (d : ℕ) (hε : 0 < ε) :
    IsObliviousSubspaceInjection S d (1 - ε) (((d : ℝ) ^ 2 + d) / (Fintype.card k * ε ^ 2)) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  exact (isObliviousSubspaceEmbedding_of_hasLaw_countSketch hS d hε).isObliviousSubspaceInjection
    (isIsotropicSketch_of_hasLaw_countSketch hS)

omit [DecidableEq k] in
/-- The Gram entry of a one-column matrix is the squared norm of its column. -/
private theorem conjTranspose_replicateCol_mul_self_apply {m : Type*} [Fintype m] (v : m → 𝕜) :
    ((Matrix.replicateCol Unit v)ᴴ * Matrix.replicateCol Unit v) () () =
      ((‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) := by
  rw [Matrix.mul_apply, EuclideanSpace.norm_sq_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Matrix.replicateCol_apply, RCLike.star_def, RCLike.conj_mul]

omit [DecidableEq k] in
/-- At a one-column matrix $\mathbf{x}$, the AMM error is the distortion
$\|\mathbf{A}\mathbf{x}\|^2 - \|\mathbf{x}\|^2$. -/
private theorem frobNorm_replicateCol_sq (A : Matrix k n 𝕜) (x : n → 𝕜) :
    frobNorm ((Matrix.replicateCol Unit x)ᴴ * Aᴴ * A * Matrix.replicateCol Unit x -
      (Matrix.replicateCol Unit x)ᴴ * Matrix.replicateCol Unit x) ^ 2 =
      |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ 2 := by
  have e : (Matrix.replicateCol Unit x)ᴴ * Aᴴ * A * Matrix.replicateCol Unit x =
      (Matrix.replicateCol Unit (A *ᵥ x))ᴴ * Matrix.replicateCol Unit (A *ᵥ x) := by
    rw [Matrix.replicateCol_mulVec, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e, frobNorm_sq_eq_sum, Fintype.sum_unique, Fintype.sum_unique, Matrix.sub_apply,
    conjTranspose_replicateCol_mul_self_apply, conjTranspose_replicateCol_mul_self_apply,
    ← RCLike.ofReal_sub, RCLike.norm_ofReal]

/-- **CountSketch JL moment** at $p = 2$ with
$$\delta = 2/(\lvert k \rvert \varepsilon^2) \,,$$
any
field: $\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - 1)^2 \le 2/\lvert k \rvert$ for unit
$\mathbf{x}$, the AMM bound at a one-column matrix. [Woodruff2014, Theorem 14] (after Thorup and
Zhang, not in hand; over $\mathbb{R}$, there in size form).
Result: countsketch-jl-moment -/
theorem hasJLMoment_of_hasLaw_countSketch (hS : HasLaw S (countSketch k n) μ) (hε : 0 < ε) :
    HasJLMoment S ε (2 / (Fintype.card k * ε ^ 2)) 2 μ := by
  have e (x : n → 𝕜) (hx : ‖WithLp.toLp 2 x‖ = 1) (ω : Ω) :
      |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ (2 : ℝ) =
        frobNorm ((Matrix.replicateCol Unit x)ᴴ * (S ω)ᴴ * S ω * Matrix.replicateCol Unit x -
          (Matrix.replicateCol Unit x)ᴴ * Matrix.replicateCol Unit x) ^ 2 := by
    rw [Real.rpow_two, frobNorm_replicateCol_sq, hx, one_pow]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [e x hx]
    exact integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch hS _ _
  · simp only [e x hx]
    have hX : frobNorm (Matrix.replicateCol Unit x) ^ 2 = 1 := by
      rw [frobNorm_sq_eq_re_trace, Matrix.trace, Fintype.sum_unique, Matrix.diag_apply,
        conjTranspose_replicateCol_mul_self_apply, RCLike.ofReal_re, hx, one_pow]
    refine (integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_countSketch hS _ _).trans
      (le_of_eq ?_)
    rw [hX, Real.rpow_two]
    rcases eq_or_ne (Fintype.card k : ℝ) 0 with hk | hk
    · simp [hk]
    · field_simp

/-! ### Sizes -/

/-- The **CountSketch embedding
dimension** <!-- value countSketchEmbeddingDim d \varepsilon \delta -->
$(d^2 + d)/(\delta \varepsilon^2)$: a CountSketch with at least this
many rows is an OSE (and, with a row, an OSI) for dimension $d$ with constants $1 \mp \varepsilon$
and failure probability $\delta$
(`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le`). The
value the proof reaches; [Woodruff2014, Theorem 9] has $O(d^2/(\delta\varepsilon^2))$ with no
constant. Consumers use `NLAlib.countSketchEmbeddingDim_le`. Junk value: $0$ at $\varepsilon = 0$ or
$\delta = 0$. -/
noncomputable irreducible_def countSketchEmbeddingDim (d : ℕ) (ε δ : ℝ) : ℝ :=
  ((d : ℝ) ^ 2 + d) / (δ * ε ^ 2)

/-- The number of CountSketch rows is nonnegative for $\delta \ge 0$. -/
theorem countSketchEmbeddingDim_nonneg (d : ℕ) (ε : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ countSketchEmbeddingDim d ε δ := by
  rw [countSketchEmbeddingDim_def]
  positivity

/-- The number of CountSketch rows is monotone in the dimension $d$ and antitone in the
distortion $\varepsilon > 0$ and the failure probability $\delta > 0$. -/
theorem countSketchEmbeddingDim_mono {d d' : ℕ} {ε' δ' : ℝ} (hd : d ≤ d') (hε : 0 < ε)
    (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    countSketchEmbeddingDim d ε' δ' ≤ countSketchEmbeddingDim d' ε δ := by
  rw [countSketchEmbeddingDim_def, countSketchEmbeddingDim_def]
  have hdd : (d : ℝ) ≤ d' := Nat.cast_le.2 hd
  exact div_le_div₀ (by positivity) (by gcongr) (by positivity)
    (mul_le_mul hδδ' (pow_le_pow_left₀ hε.le hεε' 2) (by positivity) (hδ.le.trans hδδ'))

/-- The explicit comparison: `NLAlib.countSketchEmbeddingDim d ε δ` is at
most <!-- value countSketchEmbeddingDim d \varepsilon \delta -->
$(d^2 + d)/(\delta \varepsilon^2)$, the value consumers invert with (at present an equality); an
improved definition keeps it true. -/
theorem countSketchEmbeddingDim_le (d : ℕ) (ε δ : ℝ) :
    countSketchEmbeddingDim d ε δ ≤ ((d : ℝ) ^ 2 + d) / (δ * ε ^ 2) := by
  rw [countSketchEmbeddingDim_def]

omit [DecidableEq k] in
/-- For $\varepsilon, \delta > 0$ and <!-- value countSketchEmbeddingDim d \varepsilon \delta -->
$\lvert k \rvert \ge (d^2 + d)/(\delta \varepsilon^2)$ rows
(`NLAlib.countSketchEmbeddingDim d ε δ`),
$(d^2 + d)/(\lvert k \rvert \varepsilon^2) \le \delta$: the rows give the failure probability
$\delta$. -/
private theorem div_card_mul_sq_le_of_countSketchRows_le {d : ℕ} (hε : 0 < ε) (hδ : 0 < δ)
    (hk : countSketchEmbeddingDim d ε δ ≤ Fintype.card k) :
    ((d : ℝ) ^ 2 + d) / (Fintype.card k * ε ^ 2) ≤ δ := by
  rw [countSketchEmbeddingDim_def] at hk
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, zero_div]
    exact hδ.le
  · have hd' : (0 : ℝ) < (d : ℝ) ^ 2 + d := by positivity
    have hm : (0 : ℝ) < Fintype.card k := (div_pos hd' (by positivity)).trans_le hk
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hk
    nlinarith

/-- **CountSketch OSE, size form**: with <!-- value countSketchEmbeddingDim d \varepsilon \delta -->
$\lvert k \rvert \ge (d^2 + d)/(\delta \varepsilon^2)$ rows
(`NLAlib.countSketchEmbeddingDim d ε δ`), for
$\varepsilon, \delta > 0$, a CountSketch is an oblivious subspace embedding for dimension $d$ with
constants $1 \mp \varepsilon$ and failure probability $\delta$. [Woodruff2014, Theorem 9] (there
$O(d^2/(\delta\varepsilon^2))$ rows). Asymptotic form:
`NLAlib.exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_countSketch`.
Result: sparse-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le
    (hS : HasLaw S (countSketch k n) μ) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : countSketchEmbeddingDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  exact (isObliviousSubspaceEmbedding_of_hasLaw_countSketch hS d hε).mono le_rfl le_rfl le_rfl
    (div_card_mul_sq_le_of_countSketchRows_le hε hδ hk)

/-- **CountSketch OSE, asymptotic form**: $O(d^2/(\delta \varepsilon^2))$ rows suffice for a
CountSketch to be an oblivious subspace embedding for dimension $d$ with constants
$1 \mp \varepsilon$ and failure probability $\delta$, for $\varepsilon$ below an absolute constant;
the constants come before every dimension. Proved from
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le` with
$C = 2$ and $\varepsilon_0 = 1$. [Woodruff2014, Theorem 9].
Asymptotic: NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le
-/
theorem exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_countSketch :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype k]
      [Fintype n] [DecidableEq k] (μ : Measure Ω) (S : Ω → Matrix k n 𝕜) (d : ℕ) (ε δ : ℝ),
      HasLaw S (countSketch k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ →
      C * ((d : ℝ) ^ 2 / (δ * ε ^ 2)) ≤ Fintype.card k →
      IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ := by
  refine ⟨2, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 k n _ _ _ _ _ μ S d ε δ hS hε _ hδ hk
  refine isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le hS d hε hδ
    ((countSketchEmbeddingDim_le d ε δ).trans (le_trans ?_ hk))
  rw [mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · nlinarith [(Nat.one_le_cast (α := ℝ)).2 hd]
  linarith

/-- CountSketch OSI, size form: with <!-- value countSketchEmbeddingDim d \varepsilon \delta -->
$\lvert k \rvert \ge (d^2 + d)/(\delta \varepsilon^2)$ rows
(`NLAlib.countSketchEmbeddingDim d ε δ`), for
$\varepsilon, \delta > 0$ and nonempty `k`, a CountSketch is an oblivious subspace injection for
dimension $d$ with constant $1 - \varepsilon$ and failure probability $\delta$. -/
theorem isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le
    [Nonempty k]
    [DecidableEq n] (hS : HasLaw S (countSketch k n) μ) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : countSketchEmbeddingDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection S d (1 - ε) δ μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  exact (isObliviousSubspaceInjection_of_hasLaw_countSketch hS d hε).mono le_rfl le_rfl
    (div_card_mul_sq_le_of_countSketchRows_le hε hδ hk)

/-- **CountSketch JL moment, size form**, Woodruff's Theorem 14 as stated: at least
$2/(\varepsilon^2\delta)$ rows give the $(\varepsilon, \delta, 2)$ JL moment, for
$\varepsilon, \delta > 0$. The source's formula, so not a named size. [Woodruff2014, Theorem 14]
(over $\mathbb{R}$). -/
theorem hasJLMoment_of_hasLaw_countSketch_of_le_card (hS : HasLaw S (countSketch k n) μ)
    (hε : 0 < ε) (hδ : 0 < δ) (hk : 2 / (ε ^ 2 * δ) ≤ Fintype.card k) :
    HasJLMoment S ε δ 2 μ := by
  have hm : (0 : ℝ) < Fintype.card k := (by positivity : (0 : ℝ) < 2 / (ε ^ 2 * δ)).trans_le hk
  refine (hasJLMoment_of_hasLaw_countSketch hS hε).mono le_rfl ?_ hε.le zero_le_two
    (by positivity)
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hk
  nlinarith

/-! ### Projection-cost-preserving sketches -/

/-- The CountSketch projection-cost-preserving sketch at a given frame: C6 with the CountSketch
approximate-multiplication and Frobenius tails at the budget $\varepsilon_J$. -/
private theorem hasProjectionCostPreserving_of_hasLaw_countSketch_of_frame [Fintype r]
    [DecidableEq r] {m : Type*} [Fintype m] (hS : HasLaw S (countSketch k n) μ) {d : ℕ}
    {a b δ₁ εJ : ℝ} (h : IsObliviousSubspaceEmbedding S d a b δ₁ μ) (ha : a ≤ 1) (hb : 1 ≤ b)
    (hεJ : 0 < εJ) {A : Matrix m n 𝕜} {Z : Matrix n r 𝕜} (hZ : HasOrthonormalCols Z)
    (hZA : frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A d))
    (hrd : Fintype.card r ≤ d) :
    HasProjectionCostPreserving S A d (a - 3 * √(d : ℝ) * εJ) (b + 3 * √(d : ℝ) * εJ + εJ)
      (δ₁ + 3 * (2 / (Fintype.card k * εJ ^ 2))) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  have hδ' : 0 ≤ 2 / (Fintype.card k * εJ ^ 2) := by positivity
  have hhead : HasSubspaceEmbedding S Z a b δ₁ μ :=
    h.hasSubspaceEmbedding (by rw [hZ.rank_eq]; exact hrd)
  apply hhead.hasProjectionCostPreserving_of_hasApproximateMatrixMultiplication
    (hasJLMoment_of_hasLaw_countSketch hS hεJ) hS.aemeasurable ha hb hεJ one_le_two hδ' hZ hZA hrd
  all_goals
    apply hasApproximateMatrixMultiplication_of_measureReal_ge_le hδ'
    intro hA hB
    exact measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch hS hεJ hA hB

/-- **A CountSketch is a projection-cost-preserving sketch**, size form, over any field: for
$\varepsilon, \delta > 0$, at
least <!-- value countSketchEmbeddingDim d (\varepsilon/2) (\delta/2) -->
$(d^2 + d)/((\delta/2) (\varepsilon/2)^2)$ rows (`countSketchEmbeddingDim d (ε / 2) (δ / 2)`) and at
least <!-- value projectionCostTailDim 2 d \varepsilon \delta -->
$384 \cdot 2 (d + 1)/(\varepsilon^2 \delta)$ rows (`projectionCostTailDim 2 d ε δ`),
$\mathbf{A}\mathbf{S}^{\mathsf{H}}$ is a rank-$d$ projection-cost-preserving sketch of $\mathbf{A}$
with constants $1 \mp \varepsilon$, for every $\mathbf{A}$, except with probability $\delta$. The
head is the OSE size form at $(\varepsilon/2, \delta/2)$, the tail CountSketch's own
approximate-multiplication tail and its JL moment at $\varepsilon/(8\sqrt{d+1})$, through
`NLAlib.HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasOrthonormalCols`.
[CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 2], $O(k^2/(\varepsilon^2\delta))$
there as here; here any field, explicit. Asymptotic form:
`NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_countSketch`.
Result: sparse-pcp -/
theorem hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card {m : Type*} [Fintype m]
    (hS : HasLaw S (countSketch k n) μ) (A : Matrix m n 𝕜) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk₁ : countSketchEmbeddingDim d (ε / 2) (δ / 2) ≤ Fintype.card k)
    (hk₂ : projectionCostTailDim 2 d ε δ ≤ Fintype.card k) :
    HasProjectionCostPreserving S A d (1 - ε) (1 + ε) δ μ := by
  classical
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  have hpos : 0 < projectionCostTailDim 2 d ε δ := by
    rw [projectionCostTailDim_def]; positivity
  have hK : (0 : ℝ) < Fintype.card k := hpos.trans_le hk₂
  have hJ0 : 0 < ε / (8 * √((d : ℝ) + 1)) := by positivity
  have hbud : 1 - ε ≤ 1 - ε / 2 - 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ∧
      1 + ε / 2 + 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) + ε / (8 * √((d : ℝ) + 1)) ≤
        1 + ε ∧
      δ / 2 + 3 * (2 / (Fintype.card k * (ε / (8 * √((d : ℝ) + 1))) ^ 2)) ≤ δ := by
    have hs1 : 1 ≤ √((d : ℝ) + 1) :=
      Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) d])
    have hds : √(d : ℝ) ≤ √((d : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hss : √((d : ℝ) + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hJ : ε / (8 * √((d : ℝ) + 1)) * √((d : ℝ) + 1) = ε / 8 := by field_simp
    have hJ1 : ε / (8 * √((d : ℝ) + 1)) ≤ ε / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h3 : 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ≤ 3 * (ε / 8) := by
      rw [← hJ, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hds hJ0.le) (by norm_num)
    refine ⟨by linarith, by linarith, ?_⟩
    have hk := hk₂
    rw [projectionCostTailDim_def, div_le_iff₀ (by positivity)] at hk
    have e : 2 / (Fintype.card k * (ε / (8 * √((d : ℝ) + 1))) ^ 2) =
        64 * 2 * ((d : ℝ) + 1) / (Fintype.card k * ε ^ 2) := by
      rw [div_pow, mul_pow, hss]
      field_simp
      ring
    have h4 : 3 * (64 * 2 * ((d : ℝ) + 1) / (Fintype.card k * ε ^ 2)) ≤ δ / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨h₁, h₂, h₃⟩ := hbud
  have hose := isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le hS d
    (half_pos hε) (half_pos hδ) hk₁
  rcases le_or_gt d (Fintype.card n) with hd | hd
  · obtain ⟨Z, hZ, hAZ⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD (p := Fin d) A
        (Fintype.card_fin d) hd
    exact (hasProjectionCostPreserving_of_hasLaw_countSketch_of_frame hS hose (by linarith)
      (by linarith) hJ0 hZ (by rw [hAZ]) (by rw [Fintype.card_fin])).mono le_rfl h₁ h₂ h₃
  · refine (hasProjectionCostPreserving_of_hasLaw_countSketch_of_frame hS hose (by linarith)
      (by linarith) hJ0 (hasOrthonormalCols_one (𝕜 := 𝕜) (n := n)) ?_ hd.le).mono le_rfl h₁ h₂
      h₃
    rw [Matrix.mul_one, Matrix.conjTranspose_one, Matrix.mul_one, sub_self, frobNorm_zero]
    exact frobNorm_nonneg _

/-- **CountSketch rows suffice for a rank-$d$ projection-cost-preserving sketch**:
$$O((d+1)^2/(\varepsilon^2\delta))$$
rows give one, with constants $1 \mp \varepsilon$ and failure probability
$\delta$, over any field, for $\varepsilon$ below an absolute constant; the constants come before
every dimension. Proved from `NLAlib.hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card`
with $C = 768$ and $\varepsilon_0 = 1$. [CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11
family 2].
Asymptotic: NLAlib.hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card
Result: sparse-pcp -/
theorem exists_forall_hasProjectionCostPreserving_of_hasLaw_countSketch :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k m n : Type} [MeasurableSpace Ω] [RCLike 𝕜]
      [Fintype k] [Fintype m] [Fintype n] [DecidableEq k] (μ : Measure Ω)
      (S : Ω → Matrix k n 𝕜) (A : Matrix m n 𝕜) (d : ℕ) (ε δ : ℝ),
      HasLaw S (countSketch k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ →
      C * (((d : ℝ) + 1) ^ 2 / (ε ^ 2 * δ)) ≤ Fintype.card k →
      HasProjectionCostPreserving S A d (1 - ε) (1 + ε) δ μ := by
  refine ⟨768, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 k m n _ _ _ _ _ _ μ S A d ε δ hS hε _ hδ hk
  have hD : 0 < ε ^ 2 * δ := by positivity
  have hd0 := Nat.cast_nonneg (α := ℝ) d
  refine hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card hS A d hε hδ ?_ ?_
  · refine (countSketchEmbeddingDim_le d (ε / 2) (δ / 2)).trans (le_trans ?_ hk)
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hD]
    nlinarith [mul_pos hD hD]
  · refine (projectionCostTailDim_le 2 d ε δ).trans (le_trans ?_ hk)
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hD.le
    nlinarith

end NLAlib
