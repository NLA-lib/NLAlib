/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Algebra.Order.Field.Basic
public import NLAlib.LowRank.Random.RangeFinder
public import NLAlib.LowRank.Structural.RangeFinder
public import NLAlib.Matrix.Norms.GaugeExamples
public import NLAlib.RandomMatrix.Gaussian.BlockMoments
public import NLAlib.RandomMatrix.Gaussian.Rank

/-!
# The expected error of the Gaussian randomized SVD

For a real $\mathbf{A}$ and a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, the
randomized SVD $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$ (`NLAlib.rsvd`) has, for a target rank
$k$ with $k + 2 \le \ell$ and $\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{E}\|_{\mathsf{F}}^2\,,$$
Halko, Martinsson and Tropp's Theorem 10.5, and its Gram form in every quadratic unitarily
invariant norm, of which the Schatten forms of Tropp and Webber's Theorem 8.1 (RSVD2) and the
squared spectral form are corollaries. The first spectral moment (HMT Theorem 10.6), its
second-moment form, in which the Frobenius tail enters with weight $O(1/\ell)$, and the
late-truncated output `truncatedSVD (rsvd A (X ω)) k` in the Frobenius norm, with HMT's constant,
are here too. Every error is $\mathbf{A}$ minus the named output.

The proof completes a top-$k$ frame $\mathbf{Z}$ by $\mathbf{V}$ to an orthogonal matrix
(`NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion`), so that
the structural bounds of `NLAlib.LowRank.Structural.RangeFinder` hold almost surely with
$\mathbf{M} = (\mathbf{E}\mathbf{V})(\mathbf{V}^{\mathsf{H}}\mathbf{X})
(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}$, and integrates them with the block moments of
`NLAlib.RandomMatrix.Gaussian.BlockMoments`. No hypothesis on the shape of $\mathbf{A}$ is needed:
if $k$ exceeds the number of columns, $\operatorname{rank}\mathbf{A} \le \ell$ and the error is
$\mathbf{0}$ almost surely (`NLAlib.ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`). The hypothesis
$k + 2 \le \ell$ is necessary: at $\ell = k + 1$ the expectation is not bounded by any multiple of
$\|\mathbf{E}\|_{\mathsf{F}}^2$.

The spectral error of the truncated output depends on the choice `truncatedSVD` makes; its
expectation is stated for any measurable choice of best approximations and, directly, for
`truncatedSVD`, which is Borel measurable (`NLAlib.measurable_truncatedSVD`). The integrability
companions are law-free, in `NLAlib.LowRank.Random.RangeFinder`.

## Main results

* `NLAlib.ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`: exact recovery at
  $\operatorname{rank}\mathbf{A} \le \ell$.
* `NLAlib.integrable_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_frobNorm_sub_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix`: the sketch
  residual $(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{X}
  (\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}$ against a frame $\mathbf{Z}$: integrable, its second
  moment, and its Markov tail.
* the Gram form, every quadratic unitarily invariant norm, in the `NLAlib.SymmetricGauge`
  namespace:
  `integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`: HMT Theorem 10.5, squared
  (the printed first-moment form follows by Jensen).
* `NLAlib.integral_schattenNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`: TW Theorem 8.1 (RSVD2).
* `NLAlib.rangeFinderTailRatio`: the spectral bound of TW Theorem 8.1 (RSVD2) divided by
  $\sigma_k(\mathbf{A})^2$, with `NLAlib.one_le_rangeFinderTailRatio` and
  `NLAlib.singularValues_sq_mul_rangeFinderTailRatio`. <!-- mention rangeFinderTailRatio -->
* `NLAlib.rangeFinderTailRatio_le_one_add_card_sq` and the two tail-weight bounds before it:
  dimension bounds for the asymptotic forms of the block Krylov and subspace iteration bounds.
* `NLAlib.integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix`: HMT Theorem 10.6;
  `NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound`: its
  second-moment form.
* `NLAlib.integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix`: the second spectral
  moment is at most $121/\ell$ times the optimal Frobenius error, for $4k \le \ell$.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`: the truncated
  output, Frobenius norm.
* the asymptotic forms of the two Frobenius bounds above (HMT Theorem 10.5 squared and the
  truncated output), $O(k/\varepsilon)$ samples for relative error $1 + \varepsilon$:
  `NLAlib.exists_forall_` followed by their names.
* `NLAlib.integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix`: the truncated
  output, spectral norm, for a measurable selector;
  `NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`, its direct
  form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

/-! ### The completed top-`k` frame -/

omit [Fintype m] in
/-- The block of the structural bound in the completed frame:
$$\mathbf{E}\mathbf{X}(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+} =
(\mathbf{E}\mathbf{V})(\mathbf{V}^{\mathsf{H}}\mathbf{X})
(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}\,.$$ -/
private theorem sub_mul_mul_pinv_eq_block {E : Matrix m n ℝ} {p q : Type*} [Fintype p]
    [Fintype q] {V : Matrix n q ℝ} (hEV : E * V * Vᴴ = E) (Z : Matrix n p ℝ)
    (Ω : Matrix n l ℝ) : E * Ω * pinv (Zᴴ * Ω) = E * V * (Vᴴ * Ω) * pinv (Zᴴ * Ω) := by
  rw [← Matrix.mul_assoc (E * V), hEV]

/-! ### Exact recovery -/

/-- A Gaussian sketch at least as wide as the rank recovers the matrix: if
$\operatorname{rank}\mathbf{A} \le \ell$, then $\mathsf{rsvd}(\mathbf{A}, \mathbf{X}) =
\mathbf{A}$ almost surely, for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$. -/
theorem ae_rsvd_eq_self_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hA : A.rank ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, rsvd A (X ω) = A := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX] with ω hω
  exact rsvd_eq_self_of_rank_eq (hω.trans (min_eq_left hA))

/-- If the target rank exceeds the number of columns, the optimal error is $\mathbf{0}$ and so is
the error of the randomized SVD, almost surely. -/
private theorem ae_sub_rsvd_eq_zero_of_card_lt (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hkn : Fintype.card n < k)
    (hkl : k ≤ Fintype.card l) :
    A - truncatedSVD A k = 0 ∧ ∀ᵐ ω ∂μ, A - rsvd A (X ω) = 0 := by
  have hr : A.rank ≤ k := (A.rank_le_card_width).trans hkn.le
  refine ⟨by rw [truncatedSVD_of_rank_le A hr, sub_self], ?_⟩
  filter_upwards [ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX (hr.trans hkl)] with ω hω
  rw [hω, sub_self]

/-! ### The sketch residual against a frame -/

omit [Fintype m] in
/-- An arbitrary frame $\mathbf{Z}$ completed by $\mathbf{V}$: the residual
$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ lives on the completion,
$\mathbf{E}\mathbf{V}\mathbf{V}^{\mathsf{H}} = \mathbf{E}$. -/
private theorem exists_completion_sub_mul_mul_conjTranspose {s : Type*} [Fintype s]
    [DecidableEq s] (A : Matrix m n ℝ) {Z : Matrix n s ℝ} (hZ : HasOrthonormalCols Z) :
    ∃ V : Matrix n (Fin (Fintype.card n - Fintype.card s)) ℝ, HasOrthonormalCols V ∧
      Zᴴ * V = 0 ∧ (A - A * Z * Zᴴ) * V * Vᴴ = A - A * Z * Zᴴ := by
  classical
  have hpq : Fintype.card s + Fintype.card (Fin (Fintype.card n - Fintype.card s)) =
      Fintype.card n := by rw [Fintype.card_fin]; have := hZ.card_le; omega
  obtain ⟨V, hZV⟩ := hZ.exists_fromCols hpq
  obtain ⟨-, hV, h0⟩ := hasOrthonormalCols_fromCols_iff.mp hZV
  refine ⟨V, hV, h0, ?_⟩
  have hV' : V * Vᴴ = 1 - Z * Zᴴ :=
    eq_sub_of_add_eq' (hZV.mul_conjTranspose_add_mul_conjTranspose hpq)
  have hP : A * Z * Zᴴ * (Z * Zᴴ) = A * (Z * Zᴴ) := by
    rw [Matrix.mul_assoc A Z Zᴴ, Matrix.mul_assoc A, Matrix.mul_assoc Z Zᴴ,
      ← Matrix.mul_assoc Zᴴ Z Zᴴ, hZ.conjTranspose_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, hV', Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul A (A * Z * Zᴴ), hP,
    Matrix.mul_assoc A Z Zᴴ, sub_self, sub_zero]

/-- The sketch residual of a Gaussian block against a frame is square integrable: for a real
matrix $\mathbf{A}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ (independent
standard normal entries) and a frame $\mathbf{Z}$ of $\lvert s \rvert$ orthonormal columns with
$\lvert s \rvert + 2 \le \ell$, the squared Frobenius norm of the residual
$(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{X}
(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}$ is integrable. The frame need not consist of singular
vectors. -/
theorem integrable_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix {s : Type*} [Fintype s]
    [DecidableEq s] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {Z : Matrix n s ℝ}
    (hZ : HasOrthonormalCols Z) (hs : Fintype.card s + 2 ≤ Fintype.card l) :
    Integrable (fun ω => frobNorm ((A - A * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2) μ := by
  obtain ⟨V, hV, hZV, hEV⟩ := exists_completion_sub_mul_mul_conjTranspose A hZ
  simp only [sub_mul_mul_pinv_eq_block hEV]
  exact integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hs _

/-- **The second moment of the sketch residual of a Gaussian block against a frame**: for a real
matrix $\mathbf{A}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ (independent
standard normal entries) and a frame $\mathbf{Z}$ of $\lvert s \rvert$ orthonormal columns with
$\lvert s \rvert + 2 \le \ell$,
$$\mathbb{E}\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{X}
(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}\|_{\mathsf{F}}^2 =
\frac{\lvert s \rvert}{\ell - \lvert s \rvert - 1}\,
\|\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\|_{\mathsf{F}}^2\,.$$
The blocks $\mathbf{Z}^{\mathsf{H}}\mathbf{X}$ and
$(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{X}$ are independent; this is the
residual that the structural bounds for a sketch carry, stated through a frame and with no
completion of the frame in the statement.
[HalkoMartinssonTropp2011, Theorem 10.5]; the computation in the proof there, for the frame of
the top $k$ right singular vectors, here for any frame. -/
theorem integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix {s : Type*} [Fintype s]
    [DecidableEq s] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {Z : Matrix n s ℝ}
    (hZ : HasOrthonormalCols Z) (hs : Fintype.card s + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm ((A - A * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2 ∂μ =
      frobNorm (A - A * Z * Zᴴ) ^ 2 * Fintype.card s /
        ((Fintype.card l : ℝ) - Fintype.card s - 1) := by
  obtain ⟨V, hV, hZV, hEV⟩ := exists_completion_sub_mul_mul_conjTranspose A hZ
  simp only [sub_mul_mul_pinv_eq_block hEV]
  rw [integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hs,
    ← lpGauge_two_matrixNorm, (lpGauge 2).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV,
    lpGauge_two_matrixNorm]

/-- The Markov tail of the sketch residual of a Gaussian block against a frame: for a real matrix
$\mathbf{A}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ (independent standard
normal entries), a frame $\mathbf{Z}$ of $\lvert s \rvert$ orthonormal columns with
$\lvert s \rvert + 2 \le \ell$, and $\tau > 0$,
$$\mathbb{P}\Bigl[\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{X}
(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}\|_{\mathsf{F}}^2 >
\tau\,\frac{\lvert s \rvert}{\ell - \lvert s \rvert - 1}\,
\|\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\|_{\mathsf{F}}^2\Bigr] \le
\frac{1}{\tau}\,.$$
Markov's inequality for
`NLAlib.integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`. -/
theorem measureReal_frobNorm_sub_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix {s : Type*}
    [Fintype s] [DecidableEq s] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    {Z : Matrix n s ℝ} (hZ : HasOrthonormalCols Z) (hs : Fintype.card s + 2 ≤ Fintype.card l)
    {τ : ℝ} (hτ : 0 < τ) :
    μ.real {ω | τ * (frobNorm (A - A * Z * Zᴴ) ^ 2 * Fintype.card s /
        ((Fintype.card l : ℝ) - Fintype.card s - 1)) <
      frobNorm ((A - A * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2} ≤ τ⁻¹ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  set f := fun ω => frobNorm ((A - A * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2
  set E := frobNorm (A - A * Z * Zᴴ) ^ 2 * Fintype.card s /
    ((Fintype.card l : ℝ) - Fintype.card s - 1)
  have hint : Integrable f μ :=
    integrable_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix A hX hZ hs
  have hE : ∫ ω, f ω ∂μ = E :=
    integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix A hX hZ hs
  have hden : (0 : ℝ) < (Fintype.card l : ℝ) - Fintype.card s - 1 := by
    have : ((Fintype.card s + 2 : ℕ) : ℝ) ≤ Fintype.card l := by exact_mod_cast hs
    push_cast at this
    linarith
  have hf0 : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun ω => sq_nonneg _
  rcases (show 0 ≤ E by positivity).eq_or_lt with h0 | hpos
  · have hae : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1
      (hE.trans h0.symm)
    have hnull : μ {ω | τ * E < f ω} = 0 := by
      refine measure_mono_null (fun ω (hω : τ * E < f ω) => ?_) hae
      change f ω ≠ 0
      rw [← h0, mul_zero] at hω
      exact hω.ne'
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    exact (inv_pos.mpr hτ).le
  · refine (measureReal_mono fun ω (hω : τ * E < f ω) => hω.le).trans ?_
    refine (measureReal_ge_le_integral_div hf0 hint (mul_pos hτ hpos)).trans_eq ?_
    rw [hE]
    field_simp

/-! ### The Gram form and its corollaries -/

namespace SymmetricGauge

/-- **The expected error of the randomized SVD, Gram form**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, $k + 2 \le \ell$ and every unitarily invariant norm,
$$\mathbb{E}\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{k}{\ell - k - 1}\,
\|\mathbf{E}\|_{\mathsf{F}}^2\,,\qquad
\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,,$$
with $\mathbf{e}_0$ the first unit coordinate sequence ($\Phi(\mathbf{e}_0) = 1$ for every
Schatten gauge, `NLAlib.lpGauge_apply_single_zero`). This covers every quadratic unitarily
invariant norm: squared Schatten $p$-norms for $p \ge 2$, the squared Frobenius norm at the
nuclear gauge, the squared spectral norm. No hypothesis on the shape of $\mathbf{A}$.
[TroppWebber2023, Theorem 8.1 (RSVD2)]; [HalkoMartinssonTropp2011, Theorem 10.5 (proof)];
[MartinssonTropp2020, Theorem 11.4 and remark]; there for Schatten $p \ge 2$ (TW), here every
quadratic unitarily invariant norm, with the factor $\Phi(\mathbf{e}_0)$.
Result: randomized-svd-expected-error -/
theorem integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V, hZ, hV, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hk' : Fintype.card (Fin k) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
    have hMi := integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hM := integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hpt : ∀ᵐ ω ∂μ, Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ≤
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
          Φ (Finsupp.single 0 1) *
            frobNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2 := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)]
        with ω hω
      have h := Φ.matrixNorm_conjTranspose_mul_self_sub_rsvd_le hZ hω A
      rw [hZA, sub_mul_mul_pinv_eq_block hEV] at h
      refine h.trans (add_le_add le_rfl ?_)
      rw [← nuclearNorm_conjTranspose_mul_self]
      exact Φ.matrixNorm_le_apply_single_mul_nuclearNorm _
    have hI : Integrable (fun ω => Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) *
          frobNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2) μ :=
      (integrable_const _).add (hMi.const_mul _)
    refine (integral_mono_ae (Φ.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd A
      hX.aemeasurable) hI hpt).trans_eq ?_
    rw [integral_add (integrable_const _) (hMi.const_mul _), integral_const, probReal_univ,
      one_smul, integral_const_mul, hM, Fintype.card_fin]
    have hF := (lpGauge 2).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hF
    rw [hF]
    ring
  · obtain ⟨hE, hae⟩ := ae_sub_rsvd_eq_zero_of_card_lt A hX hkn (by omega)
    rw [integral_congr_ae (hae.mono fun ω hω => by
      simp only [hω, Matrix.conjTranspose_zero, Matrix.zero_mul, Φ.matrixNorm_zero]; rfl)]
    simp only [hE, Matrix.conjTranspose_zero, Matrix.zero_mul, Φ.matrixNorm_zero, frobNorm_zero,
      integral_zero]
    norm_num

end SymmetricGauge

open SymmetricGauge in
/-- **The expected error of the randomized SVD, Frobenius norm** (HMT Theorem 10.5, squared):
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$, <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The Frobenius instance of the Gram-form bound above;
Epperly and Webber's sharper factor, with a rank parameter, is
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le`.
Asymptotic form: `NLAlib.exists_forall_integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`.
[HalkoMartinssonTropp2011, Theorem 10.5]; [TroppWebber2023, Theorem 8.7]; HMT assume $k \ge 2$
and $k + p \le \min\{m, n\}$, neither needed here. [HalkoMartinssonTropp2011, Theorem 10.5]
prints the first-moment form <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}} \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)^{1/2}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}\,,$$
which follows from this bound by Jensen's inequality
(`ProbabilityTheory.integral_le_sqrt_integral_sq`).
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have h := integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (lpGauge 1) A hX hk
  simp only [lpGauge_one_matrixNorm, nuclearNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero, one_mul] at h
  rw [gaussianProjectionFactor_def]
  linarith

/-- **$O(k/\varepsilon)$ samples suffice for the randomized SVD**, Frobenius norm: there are
absolute constants $C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$ test
matrix $\mathbf{X}$, $k \ge 1$, $0 < \varepsilon \le \varepsilon_0$ and $\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The asymptotic form of `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (HMT
Theorem 10.5); the proof takes $C = 3$ and $\varepsilon_0 = 1$.
[EpperlyWebber2026, §4.2]; there as the count $2\ell \ge (2/\varepsilon + 2)k$ of products.
Asymptotic: NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix
Result: randomized-svd-expected-error -/
theorem exists_forall_integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < k → 0 < ε → ε ≤ ε₀ →
      C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤ (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ μ A X k ε hX hk hε hε1 hl
  obtain ⟨hkl, hg⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le hk hε hε1 hl
  exact (integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hkl).trans
    (mul_le_mul_of_nonneg_right hg (sq_nonneg _))

open SymmetricGauge in
/-- **The expected error of the randomized SVD, Schatten norms** (TW Theorem 8.1 (RSVD2)): for a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $k + 2 \le \ell$ and
$2 \le p \le \infty$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{S_p}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^2 + \frac{k}{\ell - k - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The Gram form at the Schatten gauge of order $p/2$.
[TroppWebber2023, Theorem 8.1 (RSVD2)]; [HalkoMartinssonTropp2011, Theorem 10.5 (proof)].
Result: randomized-svd-expected-error -/
theorem integral_schattenNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) {p : ℝ≥0∞}
    (hp : 2 ≤ p) :
    ∫ ω, schattenNorm p (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      schattenNorm p (A - truncatedSVD A k) ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hq : 1 ≤ p / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), one_mul]
    exact hp
  have hq0 : p / 2 ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have h2 : 2 * (p / 2) = p := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  have := Fact.mk hq
  have h := integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (lpGauge (p / 2)) A hX hk
  simp only [lpGauge_matrixNorm, schattenNorm_conjTranspose_mul_self hq0, h2,
    lpGauge_apply_single_zero, one_mul] at h
  exact h

open SymmetricGauge in
/-- **The expected error of the randomized SVD, squared spectral norm** (TW Theorem 8.1 (RSVD2) at
$p = \infty$): for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2^2 \le
\sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Incomparable with `NLAlib.integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix` (the first
moment, HMT Theorem 10.6): this one is better for small $k$ and is the form with a Nyström twin.
[TroppWebber2023, Theorem 8.1 (RSVD2)]; [MartinssonTropp2020, Theorem 11.4 and remark].
Result: randomized-svd-expected-error -/
theorem integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have h := integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (lpGauge ⊤) A hX hk
  simp only [lpGauge_top_matrixNorm, specNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero, one_mul, specNorm_sub_truncatedSVD] at h
  exact h

/-! ### The first spectral moment -/

/-- **The average spectral error of the randomized SVD** (HMT Theorem 10.6): for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$, <!-- value gaussianPinvSpecNormBound k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2 \le
\Bigl(1 + \sqrt{\tfrac{k}{\ell - k - 1}}\Bigr)\sigma_k(\mathbf{A}) +
\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\,,$$
whose constant is at most HMT's $e\sqrt{\ell}/(\ell - k)$
(`NLAlib.gaussianPinvSpecNormBound_le`). Incomparable with the squared form
`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`: this one is better for large
$k$.
[HalkoMartinssonTropp2011, Theorem 10.6]; [MartinssonTropp2020, Theorem 11.5]; there with the
constant $e\sqrt{k + p}/p$, $p = \ell - k$, and $k \ge 2$, here any $k$ with $k + 2 \le \ell$.
Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ∂μ ≤
      (1 + √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1))) * singularValues A k +
        gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k) := by
  classical
  have := hX.isProbabilityMeasure
  have hC : 0 ≤ gaussianPinvSpecNormBound k (Fintype.card l) :=
    gaussianPinvSpecNormBound_nonneg (by omega)
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V, hZ, hV, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hk' : Fintype.card (Fin k) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
    have hMi := integrable_specNorm_mul_mul_pinv_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hM := integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hpt : ∀ᵐ ω ∂μ, specNorm (A - rsvd A (X ω)) ≤ singularValues A k +
        specNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)]
        with ω hω
      have h := hZ.specNorm_sub_rsvd_le hω A
      rwa [hZA, sub_mul_mul_pinv_eq_block hEV, specNorm_sub_truncatedSVD] at h
    have hI : Integrable (fun ω => singularValues A k +
        specNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω))) μ :=
      (integrable_const _).add hMi
    refine (integral_mono_ae (integrable_specNorm_sub_rsvd A hX.aemeasurable) hI hpt).trans ?_
    rw [integral_add (integrable_const _) hMi, integral_const, probReal_univ, one_smul]
    have hF := (lpGauge 2).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hF
    have hS := (lpGauge ⊤).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm, specNorm_sub_truncatedSVD] at hS
    rw [hF, hS, Fintype.card_fin, ← gaussianPinvSpecNormBound_def] at hM
    linarith
  · obtain ⟨hE, hae⟩ := ae_sub_rsvd_eq_zero_of_card_lt A hX hkn (by omega)
    have hσ : singularValues A k = 0 := by rw [← specNorm_sub_truncatedSVD, hE, specNorm_zero]
    rw [integral_congr_ae (hae.mono fun ω hω => by simp only [hω, specNorm_zero]; rfl)]
    simp only [hE, hσ, frobNorm_zero, integral_zero, mul_zero, add_zero, le_refl]

/-- **The expected squared spectral error of the randomized SVD, HMT 10.6 form**: for a standard
Gaussian $n \times \ell$ test matrix and
$k + 2 \le \ell$, <!-- value gaussianPinvSpecNormBound k \ell -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le \sigma_k^2 +
\Bigl(\sigma_k\sqrt{\tfrac{k}{\ell-k-1}} + \frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\Bigr)^2 +
\sigma_k^2\Bigl(\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\Bigr)^2\,,$$
singular values of $\mathbf{A}$ from $0$; the bound is written in HMT's pseudoinverse
constant, whence the name's suffix. The last factor being $O(1/\ell)$,
the Frobenius tail enters with weight $O(1/\ell)$, against $k/(\ell-k-1)$ in
`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`; the two are incomparable
(this one is better when the tail is heavy and $\ell \gg k$). Applied at a comparison rank near
$\ell/2$ with the tail flattening
`NLAlib.natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq`, it bounds the
spectral error by $O(1/\ell)$ times the Frobenius tail at any $k \le \ell/4$.
[HalkoMartinssonTropp2011, Theorem 10.6]; there the first moment; proved without a literature
source in this second-moment form.
Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (singularValues A k * √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) +
          gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k)) ^ 2 +
        (singularValues A k * gaussianPinvSpecNormBound k (Fintype.card l)) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V, hZ, hV, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hk' : Fintype.card (Fin k) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
    have hMi := integrable_specNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hM := integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hpt : ∀ᵐ ω ∂μ, specNorm (A - rsvd A (X ω)) ^ 2 ≤ singularValues A k ^ 2 +
        specNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2 := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)]
        with ω hω
      have h := hZ.specNorm_sub_rsvd_sq_le hω A
      rw [hZA, specNorm_sub_truncatedSVD] at h
      rwa [← Matrix.mul_assoc ((A - truncatedSVD A k) * V), hEV]
    have hI : Integrable (fun ω => singularValues A k ^ 2 +
        specNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2) μ :=
      (integrable_const _).add hMi
    refine (integral_mono_ae (integrable_specNorm_sub_rsvd_sq A hX.aemeasurable) hI hpt).trans ?_
    rw [integral_add (integrable_const _) hMi, integral_const, probReal_univ, one_smul]
    have hF := (lpGauge 2).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hF
    have hS := (lpGauge ⊤).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm, specNorm_sub_truncatedSVD] at hS
    rw [hF, hS, Fintype.card_fin] at hM
    linarith
  · obtain ⟨hE, hae⟩ := ae_sub_rsvd_eq_zero_of_card_lt A hX hkn (by omega)
    rw [integral_congr_ae (hae.mono fun ω hω => by simp only [hω, specNorm_zero]; rfl)]
    simp only [integral_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

/-- The arithmetic of the spectral residual: from $\ell\sigma^2 \le 4\,\mathrm{OPT}^2$,
$w \le \mathrm{OPT}$, $h \le 3$ and $\ell\beta^2 \le 32.4$ with $\ell \ge 4$, the second-moment
bound $\sigma^2 + (\sigma\sqrt h + \beta w)^2 + \sigma^2\beta^2$ is at most
$(121/\ell)\mathrm{OPT}^2$. -/
private theorem residual_arith {L u w O h β : ℝ} (hL : 4 ≤ L) (hw0 : 0 ≤ w)
    (hwO : w ≤ O) (hu : L * u ^ 2 ≤ 4 * O ^ 2) (hh0 : 0 ≤ h) (hh : h ≤ 3)
    (hβ : L * β ^ 2 ≤ 32.4) :
    u ^ 2 + (u * √h + β * w) ^ 2 + (u * β) ^ 2 ≤ 121 / L * O ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hs : √h ^ 2 = h := Real.sq_sqrt hh0
  have hw2 : w ^ 2 ≤ O ^ 2 := pow_le_pow_left₀ hw0 hwO 2
  have hcross : (u * √h + β * w) ^ 2 ≤ 2.6 * (u ^ 2 * h) + 1.625 * (β ^ 2 * w ^ 2) := by
    nlinarith [sq_nonneg (1.6 * (u * √h) - β * w)]
  have h1 : L * (2.6 * (u ^ 2 * h)) ≤ 31.2 * O ^ 2 := by
    have : L * u ^ 2 * h ≤ 4 * O ^ 2 * 3 :=
      mul_le_mul hu hh hh0 (by positivity)
    nlinarith
  have h2 : L * (1.625 * (β ^ 2 * w ^ 2)) ≤ 52.65 * O ^ 2 := by
    have : L * β ^ 2 * w ^ 2 ≤ 32.4 * O ^ 2 :=
      mul_le_mul hβ hw2 (sq_nonneg _) (by norm_num)
    nlinarith
  have h3 : L * (u * β) ^ 2 ≤ 32.4 * O ^ 2 := by
    have hb : β ^ 2 ≤ 8.1 := by nlinarith
    have : L * u ^ 2 * β ^ 2 ≤ 4 * O ^ 2 * 8.1 := mul_le_mul hu hb (sq_nonneg _) (by positivity)
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
  nlinarith [mul_le_mul_of_nonneg_left hcross hL0.le]

/-- The constants of the range finder at the comparison rank $j = \lceil \ell/2 \rceil$: for
$\ell \ge 4$, $j/(\ell - j - 1) \le 3$. -/
private theorem div_le_three_of_half {L j : ℕ} (hL : 4 ≤ L) (hj : j = (L + 1) / 2) :
    (j : ℝ) / ((L : ℝ) - j - 1) ≤ 3 := by
  rcases (by omega : L = 4 ∨ 5 ≤ L) with h | h
  · subst h
    have : j = 2 := by omega
    subst this
    norm_num
  · have h1 : 2 * j ≤ L + 1 := by omega
    have h1' : 2 * (j : ℝ) ≤ L + 1 := by exact_mod_cast h1
    have h5 : (5 : ℝ) ≤ L := by exact_mod_cast h
    rw [div_le_iff₀ (by linarith)]
    linarith

/-- The constants of the range finder at the comparison rank $j = \lceil \ell/2 \rceil$: for
$\ell \ge 4$, <!-- value gaussianPinvSpecNormBound j \ell -->
$\ell\bigl(e\sqrt{(\ell + j - 1)/2}/(\ell - j)\bigr)^2 \le 32.4$. -/
private theorem mul_gaussianPinvSpecNormBound_sq_le_of_half {L j : ℕ} (hL : 4 ≤ L)
    (hj : j = (L + 1) / 2) : (L : ℝ) * gaussianPinvSpecNormBound j L ^ 2 ≤ 32.4 := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have he2 : Real.exp 1 ^ 2 ≤ 7.3891 := by nlinarith
  have h1 : 2 * j ≤ L + 1 := by omega
  have h2 : L ≤ 2 * j := by omega
  have h1' : 2 * (j : ℝ) ≤ L + 1 := by exact_mod_cast h1
  have h2' : (L : ℝ) ≤ 2 * j := by exact_mod_cast h2
  have hL' : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : 0 < (L : ℝ) - j := by linarith
  rw [gaussianPinvSpecNormBound_def, mul_pow, div_pow, Real.sq_sqrt (by linarith),
    show (L : ℝ) * (Real.exp 1 ^ 2 / ((L : ℝ) - j) ^ 2 * (((L : ℝ) + j - 1) / 2)) =
      Real.exp 1 ^ 2 * ((L : ℝ) * ((L : ℝ) + j - 1)) / (2 * ((L : ℝ) - j) ^ 2) by
      field_simp, div_le_iff₀ (by positivity)]
  rcases (by omega : L = 4 ∨ 5 ≤ L) with h | h
  · subst h
    have : j = 2 := by omega
    subst this
    push_cast
    nlinarith
  · have h5 : (5 : ℝ) ≤ L := by exact_mod_cast h
    have hA : (L : ℝ) * ((L : ℝ) + j - 1) ≤ (L : ℝ) * ((3 * L - 1) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hB : ((L : ℝ) - 1) ^ 2 / 4 ≤ ((L : ℝ) - j) ^ 2 := by nlinarith
    have hC : 7.3891 * ((L : ℝ) * ((3 * L - 1) / 2)) ≤ 64.8 * (((L : ℝ) - 1) ^ 2 / 4) := by
      nlinarith
    have hD := mul_le_mul he2 hA (by nlinarith) (by norm_num)
    nlinarith

/-- **The spectral residual of the range finder is $O(1/\ell)$ of the optimal Frobenius
error**: for a standard Gaussian test matrix $\mathbf{\Omega} \in \mathbb{R}^{n \times \ell}$,
$1 \le k$ and $4k \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le
\frac{121}{\ell}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
No printed source; the comparison-rank argument of [HalkoMartinssonTropp2011, Theorem 10.6]. -/
theorem integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k) (hkl : 4 * k ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      121 / (Fintype.card l : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  set L := Fintype.card l with hLdef
  set j := (L + 1) / 2 with hjdef
  have hL4 : 4 ≤ L := by omega
  have hj2 : j + 2 ≤ L := by omega
  have hkj : k ≤ j := by omega
  refine (integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound A hX
    hj2).trans ?_
  have hL' : (4 : ℝ) ≤ L := by exact_mod_cast hL4
  -- the tail flattening at `d = j - k`
  have hflat := natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq A k (j - k)
  rw [Nat.add_sub_cancel' hkj] at hflat
  have hd : (L : ℝ) ≤ 4 * ((j - k : ℕ) : ℝ) := by
    have : L ≤ 4 * (j - k) := by omega
    exact_mod_cast this
  have hu : (L : ℝ) * singularValues A j ^ 2 ≤ 4 * frobNorm (A - truncatedSVD A k) ^ 2 := by
    nlinarith [sq_nonneg (singularValues A j)]
  -- the optimal error is antitone in the rank
  have hw : frobNorm (A - truncatedSVD A j) ≤ frobNorm (A - truncatedSVD A k) := by
    refine (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (frobNorm_nonneg _) two_ne_zero).mp ?_
    rw [frobNorm_sub_truncatedSVD_sq, frobNorm_sub_truncatedSVD_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hkj)
      fun _ _ _ => sq_nonneg _
  exact residual_arith hL' (frobNorm_nonneg _) hw hu
    (div_nonneg (Nat.cast_nonneg _) (by
      have : (j : ℝ) + 2 ≤ L := by exact_mod_cast hj2
      linarith))
    (div_le_three_of_half hL4 rfl) (mul_gaussianPinvSpecNormBound_sq_le_of_half hL4 rfl)

/-! ### The late-truncated output -/

/-- **The expected error of the truncated randomized SVD, Frobenius norm**: the late truncation
keeps HMT's constant,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $k + 2 \le \ell$ and every
choice of the truncation (the squared Frobenius error does not depend on it,
`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`). Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`.
[HalkoMartinssonTropp2011, Theorem 10.5]; [Woodruff2014, Lemma 48];
[CamanoEpperlyMeyerTropp2025, remark after Theorem 2.2]; there the untruncated bound with the
truncation for free of Woodruff, or the truncation through the spectral HMT Theorem 9.3 (CEMT).
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V, hZ, hV, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hk' : Fintype.card (Fin k) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
    have hMi := integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hM := integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hpt : ∀ᵐ ω ∂μ, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ≤
        frobNorm (A - truncatedSVD A k) ^ 2 +
          frobNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2 := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)]
        with ω hω
      have h := hZ.frobNorm_sub_truncatedSVD_rsvd_sq_le hω A
        (by rw [Fintype.card_fin] : Fintype.card (Fin k) ≤ k)
      rwa [hZA, sub_mul_mul_pinv_eq_block hEV] at h
    have hI : Integrable (fun ω => frobNorm (A - truncatedSVD A k) ^ 2 +
        frobNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2) μ :=
      (integrable_const _).add hMi
    refine (integral_mono_ae (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k)
      hI hpt).trans_eq ?_
    rw [integral_add (integrable_const _) hMi, integral_const, probReal_univ, one_smul, hM,
      Fintype.card_fin, gaussianProjectionFactor_def]
    have hF := (lpGauge 2).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hF
    rw [hF]
    ring
  · obtain ⟨hE, hae⟩ := ae_sub_rsvd_eq_zero_of_card_lt A hX hkn (by omega)
    have hpt : ∀ᵐ ω ∂μ, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 = 0 := by
      filter_upwards [hae] with ω hω
      have h := frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add A (X ω) k
      rw [hω, hE, frobNorm_zero] at h
      exact le_antisymm (by linarith) (sq_nonneg _)
    rw [integral_congr_ae hpt]
    simp only [hE, frobNorm_zero, integral_zero]
    norm_num

/-- **$O(k/\varepsilon)$ samples suffice for the truncated randomized SVD**, Frobenius norm: there
are absolute constants $C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$
test matrix $\mathbf{X}$, $0 < \varepsilon \le \varepsilon_0$ and $\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k
\|_{\mathsf{F}}^2 \le (1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`; the proof takes
$C = 3$ and $\varepsilon_0 = 1$.
[Woodruff2014, Lemma 45 and Remark 46]; there with constant probability, here in expectation.
Asymptotic: NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix
Result: randomized-svd-expected-error -/
theorem exists_forall_integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ → C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ μ A X k ε hX hε hε1 hl
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := hX.isProbabilityMeasure
    simp only [truncatedSVD_zero, sub_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  obtain ⟨hkl, hg⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le hk hε hε1 hl
  exact (integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hkl).trans
    (mul_le_mul_of_nonneg_right hg (sq_nonneg _))

/-- **The expected spectral error of the truncated randomized SVD**, for a measurable choice
$\mathbf{Y}$ of best rank-$k$ approximations of $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$: for
a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathbf{Y}\|_2^2 \le \sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
the bound of the untruncated output
(`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`). Direct form at
`truncatedSVD`: `NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`.
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a remark on truncated outputs, here explicit, under a selector.
Result: randomized-svd-expected-error -/
theorem integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) {Y : Ω → Matrix m n ℝ}
    (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (A - Y ω) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  have h1 := integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox A
    hX.aemeasurable hY hYm
  have h2 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk
  have h3 : gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 =
      frobNorm (A - truncatedSVD A k) ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
    rw [gaussianProjectionFactor_def]
    ring
  linarith

/-- **The expected spectral error of the truncated randomized SVD**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_2^2 \le
\sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
the bound of the untruncated output. The direct form of
`NLAlib.integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix`, which covers any
other measurable choice of the truncation.
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a remark on truncated outputs, here explicit.
Result: randomized-svd-expected-error -/
theorem integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 :=
  integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix A hX hk
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    ((measurable_truncatedSVD k).comp_aemeasurable
      ((measurable_rsvd A).comp_aemeasurable hX.aemeasurable)).aestronglyMeasurable

/-! ### The normalised spectral bound -/


/-- The **range-finder tail ratio** (casts to $\mathbb{R}$),
the number <!-- value rangeFinderTailRatio \mathbf{A} r \ell -->
$$1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2}{\sigma_r(\mathbf{A})^2}\,:$$
the expected squared spectral error bound of the randomized SVD with a Gaussian $n \times \ell$
test matrix at rank $r$ (TW Theorem 8.1 (RSVD2),
`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`) divided by
$\sigma_r(\mathbf{A})^2$. It is the quantity whose logarithm the gapless bounds of randomized block
Krylov and subspace iteration shrink. Junk values: $1$ when $\sigma_r(\mathbf{A}) = 0$ (Lean's
$x/0 = 0$), and possibly below $1$ for $\ell \le r + 1$; theorems carry $0 < \sigma_r(\mathbf{A})$
and $r + 2 \le \ell$. A plain definition, because its body is the source's formula.
[TroppWebber2023, Theorem 9.1]. -/
noncomputable def rangeFinderTailRatio {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (r l : ℕ) : ℝ :=
  1 + (r : ℝ) / ((l : ℝ) - r - 1) * frobNorm (A - truncatedSVD A r) ^ 2 / singularValues A r ^ 2

/-- The range-finder tail ratio is at least $1$ for $r + 2 \le \ell$:
in full, <!-- value rangeFinderTailRatio \mathbf{A} r \ell -->
$$1 \le 1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2}{\sigma_r(\mathbf{A})^2}\,.$$
-/
theorem one_le_rangeFinderTailRatio {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) {r l : ℕ}
    (hl : r + 2 ≤ l) : 1 ≤ rangeFinderTailRatio A r l := by
  have hk := natCast_div_sub_sub_one_nonneg (K := ℝ) hl
  have h := div_nonneg (mul_nonneg hk (sq_nonneg (frobNorm (A - truncatedSVD A r))))
    (sq_nonneg (singularValues A r))
  rw [rangeFinderTailRatio]
  linarith

/-- The range-finder tail ratio times $\sigma_r(\mathbf{A})^2$ is the spectral bound of the
randomized SVD: for $\sigma_r(\mathbf{A}) > 0$,
the identity <!-- value rangeFinderTailRatio \mathbf{A} r \ell -->
$$\sigma_r(\mathbf{A})^2\Bigl(1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2}{\sigma_r(\mathbf{A})^2}
\Bigr) = \sigma_r(\mathbf{A})^2 + \frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$ -/
theorem singularValues_sq_mul_rangeFinderTailRatio {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜)
    {r : ℕ} (l : ℕ) (hσ : 0 < singularValues A r) :
    singularValues A r ^ 2 * rangeFinderTailRatio A r l =
      singularValues A r ^ 2 +
        (r : ℝ) / ((l : ℝ) - r - 1) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  rw [rangeFinderTailRatio, mul_add, mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 hσ.ne')]

/-- The tail term of the Gaussian range-finder bounds is at most $\lvert n \rvert^2$ times the best
squared spectral error at a smaller rank: for $r \le t$ and $t + 2 \le \ell$ (casts to
$\mathbb{R}$), with $\lvert n \rvert$ the number of columns,
$$\frac{t}{\ell - t - 1}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2 \le
\lvert n \rvert^2\sigma_r(\mathbf{A})^2\,,$$
from $t/(\ell - t - 1) \le t$ and $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2
\le (\min(\lvert m \rvert, \lvert n \rvert) - t)\,\sigma_r(\mathbf{A})^2$. It turns the gapped and
gapless spectral bounds of randomized block Krylov and subspace iteration into relative errors, for
their asymptotic forms. -/
theorem
natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) {r t l : ℕ} (hrt : r ≤ t) (hl : t + 2 ≤ l) :
    (t : ℝ) / ((l : ℝ) - t - 1) * frobNorm (A - truncatedSVD A t) ^ 2 ≤
      (Fintype.card n : ℝ) ^ 2 * singularValues A r ^ 2 := by
  set N := min (Fintype.card m) (Fintype.card n) with hN
  have hκ : (t : ℝ) / ((l : ℝ) - t - 1) ≤ t := div_le_self (Nat.cast_nonneg _) (by
    have : (t : ℝ) + 2 ≤ l := by exact_mod_cast hl
    linarith)
  have hF : frobNorm (A - truncatedSVD A t) ^ 2 ≤ ((N - t : ℕ) : ℝ) * singularValues A r ^ 2 := by
    rw [frobNorm_sub_truncatedSVD_sq]
    calc ∑ i ∈ Finset.Ico t N, singularValues A i ^ 2
        ≤ ∑ _i ∈ Finset.Ico t N, singularValues A r ^ 2 :=
          Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (singularValues_nonneg _ _)
            (singularValues_antitone A (hrt.trans (Finset.mem_Ico.1 hi).1)) 2
      _ = _ := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have htN : t * (N - t) ≤ Fintype.card n * Fintype.card n := by
    have := min_le_right (Fintype.card m) (Fintype.card n)
    rcases le_or_gt N t with h | h
    · rw [Nat.sub_eq_zero_of_le h, mul_zero]
      exact Nat.zero_le _
    · exact Nat.mul_le_mul (by omega) (by omega)
  have htNR : (t : ℝ) * ((N - t : ℕ) : ℝ) ≤ (Fintype.card n : ℝ) ^ 2 := by
    rw [sq]
    exact_mod_cast htN
  calc (t : ℝ) / ((l : ℝ) - t - 1) * frobNorm (A - truncatedSVD A t) ^ 2
      ≤ t * frobNorm (A - truncatedSVD A t) ^ 2 := mul_le_mul_of_nonneg_right hκ (sq_nonneg _)
    _ ≤ t * (((N - t : ℕ) : ℝ) * singularValues A r ^ 2) :=
        mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)
    _ ≤ (Fintype.card n : ℝ) ^ 2 * singularValues A r ^ 2 := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right htNR (sq_nonneg _)

/-- The tail term of the Gaussian range-finder bounds is at most $\lvert n \rvert$ times the best
squared Frobenius error at a smaller rank: for $r \le t$ and $t + 2 \le \ell$ (casts to
$\mathbb{R}$), with $\lvert n \rvert$ the number of columns,
$$\frac{t}{\ell - t - 1}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2 \le
\lvert n \rvert\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
For $t$ at least the rank bound $\min(\lvert m \rvert, \lvert n \rvert)$ the left side is $0$;
otherwise $t/(\ell - t - 1) \le t < \lvert n \rvert$. The Frobenius companion of
`NLAlib.natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq`,
for the asymptotic forms of the Frobenius bounds of randomized block Krylov and subspace
iteration. -/
theorem
natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_mul_frobNorm_sub_truncatedSVD_sq
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) {r t l : ℕ} (hrt : r ≤ t) (hl : t + 2 ≤ l) :
    (t : ℝ) / ((l : ℝ) - t - 1) * frobNorm (A - truncatedSVD A t) ^ 2 ≤
      (Fintype.card n : ℝ) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  set N := min (Fintype.card m) (Fintype.card n) with hN
  rw [frobNorm_sub_truncatedSVD_sq, frobNorm_sub_truncatedSVD_sq]
  rcases le_or_gt N t with h | h
  · rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun i _ => sq_nonneg (singularValues A i))
  · have hκ : (t : ℝ) / ((l : ℝ) - t - 1) ≤ Fintype.card n := by
      have hl' : (t : ℝ) + 2 ≤ l := by exact_mod_cast hl
      have htn : (t : ℝ) ≤ Fintype.card n := by
        have := min_le_right (Fintype.card m) (Fintype.card n)
        exact_mod_cast (show t ≤ Fintype.card n by omega)
      exact (div_le_self (Nat.cast_nonneg _) (by linarith)).trans htn
    calc (t : ℝ) / ((l : ℝ) - t - 1) * ∑ i ∈ Finset.Ico t N, singularValues A i ^ 2
        ≤ (Fintype.card n : ℝ) * ∑ i ∈ Finset.Ico t N, singularValues A i ^ 2 :=
          mul_le_mul_of_nonneg_right hκ (Finset.sum_nonneg fun i _ => sq_nonneg _)
      _ ≤ (Fintype.card n : ℝ) * ∑ i ∈ Finset.Ico r N, singularValues A i ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Ico_subset_Ico_left hrt) fun i _ _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- The range-finder tail ratio is at most $1 + \lvert n \rvert^2$, with $\lvert n \rvert$ the
number of columns: for $r + 2 \le \ell$ and $\sigma_r(\mathbf{A}) > 0$,
in full, <!-- value rangeFinderTailRatio \mathbf{A} r \ell -->
$$1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2}{\sigma_r(\mathbf{A})^2}
\le 1 + \lvert n \rvert^2\,,$$
by the spectral tail-weight bound above at $t = r$. It bounds the logarithm in the gapless
bounds by $O(\log\lvert n \rvert)$. -/
theorem rangeFinderTailRatio_le_one_add_card_sq {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜)
    {r l : ℕ} (hl : r + 2 ≤ l) (hσ : 0 < singularValues A r) :
    rangeFinderTailRatio A r l ≤ 1 + (Fintype.card n : ℝ) ^ 2 := by
  rw [rangeFinderTailRatio, add_le_add_iff_left, div_le_iff₀ (pow_pos hσ 2)]
  exact
    natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq A
      le_rfl hl

end NLAlib
