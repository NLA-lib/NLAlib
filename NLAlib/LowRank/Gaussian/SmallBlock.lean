/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.BlockKrylovGapless
public import NLAlib.LowRank.Structural.SmallBlock
public import NLAlib.Probability.Distributions.GaussianLogOverlap

/-!
# Randomized block Krylov iteration with a small block

Tail bounds for randomized block Krylov iteration
$\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)$ started from one standard Gaussian vector
$\mathbf{x}$, and, by monotonicity in the block, from a standard Gaussian block of any size. The
existing bounds (`NLAlib.LowRank.Gaussian.BlockKrylov`) need a block of at least $t + 2$ columns
for a tail index $t$. Here the first $t$ Krylov vectors
$[\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$,
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, play the part of the block, and the remaining
depth $q - t$ carries the Chebyshev filter
(`NLAlib.exists_degree_lt_div_sq_le_exp_singularGapRatio`). The price is a gap hypothesis on the
top $t$ singular values, $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$: the
coordinates of the simulated block in the top $t$ right singular vectors are
$\operatorname{diag}(\mathbf{g})$ times a Vandermonde matrix in $\sigma_0^2, \dots,
\sigma_{t-1}^2$, with $\mathbf{g}$ the coordinates of $\mathbf{x}$, and its inverse costs
$\Delta^{-2(t-1)}\sum_{i<t} g_i^{-2}$. With probability at least $1 - \delta$,
$$\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2 \le \sigma_r(\mathbf{A})^2 +
32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
with $\gamma = (\sigma_{r-1} - \sigma_t)/(\sigma_{r-1} + \sigma_t)$. Since
$\mathbb{E}\,g_i^{-2} = \infty$ the route bounds no expectation of the error; the two forms stated
are the tail bound and the expectation restricted to the event that every head coordinate
exceeds $\delta/t$ in absolute value.

No positivity of the head singular values is assumed in the probabilistic statements: when
$\operatorname{rank}\mathbf{A} < t$ the gap hypothesis makes the positive singular values
distinct, the Krylov space of depth $q \ge t$ of almost every start vector contains the row
space of $\mathbf{A}$, and the error vanishes almost surely.

## Main results

* `NLAlib.measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector`,
  `NLAlib.sum_inv_sq_le_card_div_sq_of_forall_le_abs`: the head coordinates.
* `NLAlib.measureReal_norm_mulVec_sq_gt_le_of_hasLaw_gaussianVector`: the tail energy.
* `NLAlib.specNorm_sub_rbki_replicateCol_sq_le_of_forall_le_abs`,
  `NLAlib.frobNorm_sub_rbki_replicateCol_sq_le_of_forall_le_abs`,
  `NLAlib.specNorm_sub_truncatedSVD_rbki_sq_le_of_forall_le_abs`: the deterministic bounds off
  the head event; `NLAlib.rbki_replicateCol_eq_self_of_rank_le`,
  `NLAlib.ae_rbki_replicateCol_eq_self_of_hasLaw_gaussianVector`: the rank-deficient case.
* `NLAlib.measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector`,
  `NLAlib.measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector`,
  `NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianVector`: the
  gapped tail bounds for one start vector.
* `NLAlib.integral_setOf_specNorm_sub_rbki_sq_le_of_hasLaw_gaussianVector`: the expectation on the
  head event.
* the gapless $(1 + \varepsilon)$ tail bound for one start vector:
`NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianVector`
* the same bounds for a Gaussian block of any size:
  `NLAlib.measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianMatrix`,
`NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianMatrix`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l k : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype k] [DecidableEq n] {x : Ω → n → ℝ} {X : Ω → Matrix n l ℝ}

/-! ### The head coordinates and the tail energy -/

omit [DecidableEq n] in
/-- The head event of a Gaussian start vector: for a standard Gaussian vector $\mathbf{x}$ in
$\mathbb{R}^n$ (independent standard normal entries), a real matrix $\mathbf{Z}$ with orthonormal
columns indexed by $k$, and $a \ge 0$,
$$\mathbb{P}\bigl[\exists i,\ \lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert \le a\bigr] \le
\lvert k \rvert\, a\,.$$
Each coordinate $(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i$ is a standard normal variable, so the
small-ball bound `NLAlib.gaussianReal_abs_le_le` and a union bound apply; independence of the
coordinates is not used. For $\lvert k \rvert = t$ the threshold $a = \delta/(2t)$ gives
probability at most $\delta/2$ and $a = \delta/t$ gives $\delta$. -/
theorem measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector
    [DecidableEq k] (hx : HasLaw x (gaussianVector n) μ) {Z : Matrix n k ℝ}
    (hZ : HasOrthonormalCols Z) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ i, |(Zᴴ *ᵥ x ω) i| ≤ a} ≤ Fintype.card k * a := by
  have := hx.isProbabilityMeasure
  have hset : {ω | ∃ i, |(Zᴴ *ᵥ x ω) i| ≤ a} = ⋃ i, {ω | |(Zᴴ *ᵥ x ω) i| ≤ a} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  have hi : ∀ i, μ.real {ω | |(Zᴴ *ᵥ x ω) i| ≤ a} ≤ a := fun i => by
    have h := hasLaw_dotProduct_of_hasLaw_gaussianVector hx (Z.col i)
    have hv : ‖WithLp.toLp 2 (Z.col i)‖₊ ^ 2 = 1 := by
      rw [← NNReal.coe_inj, NNReal.coe_pow, coe_nnnorm, hZ.norm_toLp_col, one_pow, NNReal.coe_one]
    rw [hv] at h
    have he := h.measureReal_eq (p := fun y : ℝ => |y| ≤ a)
      (isClosed_le continuous_abs continuous_const).measurableSet
    have hcoord : ∀ ω, (Zᴴ *ᵥ x ω) i = Z.col i ⬝ᵥ x ω := fun ω => by
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
    simp only [hcoord]
    rw [he]
    exact ENNReal.toReal_le_of_le_ofReal ha (gaussianReal_abs_le_le a)
  rw [hset]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ a fun i _ => hi i).trans (le_of_eq ?_)
  rw [Finset.card_univ, nsmul_eq_mul]

/-- Off the head event the inverse head coordinates are bounded: for real numbers $g_i$, $i$ in a
finite type $\iota$, with $\lvert g_i \rvert \ge a > 0$ for every $i$,
$$\sum_i g_i^{-2} \le \frac{\lvert\iota\rvert}{a^2}\,.$$
For $\lvert\iota\rvert = t$ the threshold $a = \delta/(2t)$ gives $4t^3/\delta^2$ and
$a = \delta/t$ gives $t^3/\delta^2$. -/
theorem sum_inv_sq_le_card_div_sq_of_forall_le_abs {ι : Type*} [Fintype ι] {g : ι → ℝ} {a : ℝ}
    (ha : 0 < a) (hg : ∀ i, a ≤ |g i|) : ∑ i, (g i)⁻¹ ^ 2 ≤ Fintype.card ι / a ^ 2 := by
  have h : ∀ i ∈ Finset.univ, (g i)⁻¹ ^ 2 ≤ 1 / a ^ 2 := fun i _ => by
    rw [inv_pow, ← sq_abs (g i), ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ha.le (hg i) 2)
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans (le_of_eq ?_)
  rw [Finset.card_univ, nsmul_eq_mul, mul_one_div]

omit [DecidableEq n] in
/-- The tail energy of a Gaussian start vector: for a standard Gaussian vector $\mathbf{x}$ in
$\mathbb{R}^n$ (independent standard normal entries), a real matrix $\mathbf{M}$ and $\eta > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{M}\mathbf{x}\|_2^2 >
\frac{\|\mathbf{M}\|_{\mathsf{F}}^2}{\eta}\Bigr] \le \eta\,.$$
Markov's inequality for
$\mathbb{E}\|\mathbf{M}\mathbf{x}\|_2^2 = \|\mathbf{M}\|_{\mathsf{F}}^2$
(`NLAlib.IsIsotropic.integral_norm_mulVec_sq`); when $\mathbf{M} = 0$ the event is null. -/
theorem measureReal_norm_mulVec_sq_gt_le_of_hasLaw_gaussianVector
    (hx : HasLaw x (gaussianVector n) μ) (M : Matrix m n ℝ) {η : ℝ} (hη : 0 < η) :
    μ.real {ω | frobNorm M ^ 2 / η < ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2} ≤ η := by
  classical
  have := hx.isProbabilityMeasure
  have hiso := isIsotropic_of_hasLaw_gaussianVector hx
  have hint := hiso.integrable_norm_mulVec_sq M
  have hE := hiso.integral_norm_mulVec_sq M
  rcases (sq_nonneg (frobNorm M)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_div]
    have hae : (fun ω => ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1 (hE.trans h0.symm)
    have hnull : μ {ω | 0 < ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2} = 0 :=
      measure_mono_null (fun ω (hω : 0 < ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2) => hω.ne') hae
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    exact hη.le
  · have hmk := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => sq_nonneg ‖WithLp.toLp 2 (M *ᵥ x ω)‖) hint
      (frobNorm M ^ 2 / η)
    rw [hE, div_mul_eq_mul_div, div_le_iff₀ hη] at hmk
    refine (measureReal_mono fun ω (hω : frobNorm M ^ 2 / η < _) => hω.le).trans ?_
    exact le_of_mul_le_mul_left hmk hpos

/-! ### Deterministic reductions for one start vector -/

omit [DecidableEq n] in
/-- A gap makes positive singular values distinct: if
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$ with $\Delta > 0$, then
$\sigma_j < \sigma_i$ for $i < j < t$ and $\sigma_i > 0$. -/
private theorem singularValues_lt_of_gap (A : Matrix m n ℝ) {t : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    {i j : ℕ} (hij : i < j) (hj : j < t) (hi : 0 < singularValues A i) :
    singularValues A j < singularValues A i := by
  have h1 := hgap i (by omega)
  have h2 : singularValues A (i + 1) ^ 2 < singularValues A i ^ 2 := by
    have := mul_pos hΔ (pow_pos hi 2)
    linarith
  exact (singularValues_antitone A (by omega : i + 1 ≤ j)).trans_lt
    (lt_of_pow_lt_pow_left₀ 2 (singularValues_nonneg A i) h2)

/-- Randomized block Krylov iteration from one start vector is exact for a gapped matrix of low
rank: for a real matrix $\mathbf{A}$ of rank at most $t$, an orthonormal frame $\mathbf{Z}$ of
$t$ columns with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, a vector $\mathbf{x}$ with no
vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$ and $q \ge t$,
$$\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q) = \mathbf{A}\,.$$
The head singular values may vanish: `NLAlib.rbki_replicateCol_eq_self` is applied to the first
$\operatorname{rank}\mathbf{A}$ columns of $\mathbf{Z}$, whose singular values are positive and so
distinct. -/
theorem rbki_replicateCol_eq_self_of_rank_le {t : ℕ} (A : Matrix m n ℝ) (x : n → ℝ)
    {Z : Matrix n (Fin t) ℝ} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i : Fin t => singularValues A i ^ 2)
    (hrank : A.rank ≤ t) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q : ℕ} (hq : t ≤ q) :
    rbki A (Matrix.replicateCol Unit x) q = A := by
  set W := Z.submatrix id (Fin.castLE hrank)
  have hW : HasOrthonormalCols W := hZ.submatrix (Equiv.refl _) (Fin.castLE_injective hrank)
  have hAW : Aᴴ * A * W =
      W * Matrix.diagonal fun i : Fin A.rank => ((singularValues A i ^ 2 : ℝ) : ℝ) := by
    ext y j
    have h := congrFun (congrFun hAZ y) (Fin.castLE hrank j)
    simp only [Matrix.mul_diagonal] at h ⊢
    exact h
  refine rbki_replicateCol_eq_self A x hW hAW le_rfl (fun i j hij hj => ?_)
    (fun i => hx (Fin.castLE hrank i)) (hrank.trans hq)
  exact singularValues_lt_of_gap A hΔ hgap hij (hj.trans_le hrank)
    ((singularValues_pos_iff A).2 (hij.trans hj))

omit [DecidableEq n] in
/-- The Frobenius error of the projection onto a frame of top right singular vectors: for a real
matrix $\mathbf{A}$ and an orthonormal frame $\mathbf{Z}$ of $t$ columns with
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\|_{\mathsf{F}} =
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}\,,$$
whichever eigenvectors the frame picks: both squares are $\sum_{j \ge t} \sigma_j^2$. -/
theorem frobNorm_sub_mul_mul_conjTranspose_eq_frobNorm_sub_truncatedSVD {t : ℕ}
    (A : Matrix m n ℝ) {Z : Matrix n (Fin t) ℝ} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i : Fin t => singularValues A i ^ 2) :
    frobNorm (A - A * Z * Zᴴ) = frobNorm (A - truncatedSVD A t) := by
  classical
  refine (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
  set P := Z * Zᴴ with hPdef
  have hPP : P * P = P := by
    rw [hPdef, Matrix.mul_assoc Z, ← Matrix.mul_assoc Zᴴ, hZ.conjTranspose_mul_self,
      Matrix.one_mul]
  have hP1 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]
    simp
  have hPh : (1 - P)ᴴ = 1 - P := by
    simp [hPdef]
  have hA : A - A * Z * Zᴴ = A * (1 - P) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have htr : ((A * (1 - P))ᴴ * (A * (1 - P))).trace =
      (Aᴴ * A).trace - ∑ i : Fin t, singularValues A i ^ 2 := by
    have h1 : (A * (1 - P))ᴴ * (A * (1 - P)) = (1 - P) * (Aᴴ * A) * (1 - P) := by
      rw [Matrix.conjTranspose_mul, hPh]
      simp only [Matrix.mul_assoc]
    have h2 : (Aᴴ * A * P).trace = ∑ i : Fin t, singularValues A i ^ 2 := by
      rw [hPdef, ← Matrix.mul_assoc, hAZ, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        hZ.conjTranspose_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
    rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP1, Matrix.trace_mul_comm,
      Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, h2]
  have hL : frobNorm (A - A * Z * Zᴴ) ^ 2 =
      frobNorm A ^ 2 - ∑ i ∈ Finset.range t, singularValues A i ^ 2 := by
    rw [hA, frobNorm_sq_eq_re_trace, htr, frobNorm_sq_eq_re_trace, Fin.sum_univ_eq_sum_range
      (fun i => singularValues A i ^ 2) t]
    simp
  set μ' := min (Fintype.card m) (Fintype.card n)
  have hrank : A.rank ≤ max t μ' :=
    (le_min A.rank_le_card_height A.rank_le_card_width).trans (le_max_right _ _)
  rw [hL, frobNorm_sub_truncatedSVD_sq, frobNorm_sq_eq_sum_range_singularValues_sq A hrank,
    ← Finset.sum_range_add_sum_Ico _ (le_max_left t μ'), add_sub_cancel_left]
  rcases le_total t μ' with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, Finset.Ico_self, Finset.Ico_eq_empty (by omega)]

/-- The starting-block factor off the head event: for real numbers $g_i$, $i < t$, with
$\lvert g_i \rvert \ge a > 0$, $\Delta > 0$, $K \le E$ with $E \ge 0$, and $N \ge 0$,
$$K\,\Delta^{-2(t-1)}\Bigl(\sum_{i<t} \lvert g_i \rvert^{-2}\Bigr) N \le
E\,\Delta^{-2(t-1)}\,\frac{t}{a^2}\,N\,.$$ -/
private theorem mul_inv_pow_mul_sum_inv_sq_mul_le {t : ℕ} {Δ a K E N : ℝ} (hΔ : 0 < Δ)
    {g : Fin t → ℝ} (ha : 0 < a) (hg : ∀ i, a ≤ |g i|) (hK : K ≤ E) (hE : 0 ≤ E) (hN : 0 ≤ N) :
    K * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖g i‖⁻¹ ^ 2) * N ≤
      E * Δ⁻¹ ^ (2 * (t - 1)) * (t / a ^ 2) * N := by
  have hs : ∑ i, ‖g i‖⁻¹ ^ 2 ≤ t / a ^ 2 := by
    have h := sum_inv_sq_le_card_div_sq_of_forall_le_abs ha hg
    rw [Fintype.card_fin] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) h
    rw [Real.norm_eq_abs, inv_pow, inv_pow, sq_abs]
  have hD : 0 ≤ Δ⁻¹ ^ (2 * (t - 1)) := by positivity
  have hs0 : 0 ≤ ∑ i, ‖g i‖⁻¹ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right hK hD) hs hs0 (mul_nonneg hE hD)) hN

/-- The gapped bound for randomized block Krylov iteration from one start vector off the head
event, spectral norm: for a real matrix $\mathbf{A}$, an orthonormal frame $\mathbf{Z}$ of $t$
columns with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$, $\sigma_i > 0$ for $i < t$,
a head of $r = h + 1$ singular values, $r \le t \le q$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and a vector $\mathbf{x}$ with
$\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert \ge a > 0$ for every $i$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2 \le \sigma_r^2 +
4e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t}{a^2}\,
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$ -/
theorem specNorm_sub_rbki_replicateCol_sq_le_of_forall_le_abs {t : ℕ} (A : Matrix m n ℝ)
    (x : n → ℝ) {Z : Matrix n (Fin t) ℝ} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i : Fin t => singularValues A i ^ 2)
    {h r q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t) (hq : t ≤ q) {Δ a : ℝ} (hΔ : 0 < Δ)
    (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (ha : 0 < a) (hg : ∀ i, a ≤ |(Zᴴ *ᵥ x) i|) :
    specNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * (t / a ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  obtain ⟨f, hf, c, b, hc, hhead, htail, hK⟩ :=
    exists_degree_lt_div_sq_le_exp_singularGapRatio A hr hrt (q - t)
  rw [Nat.cast_sub hq] at hK
  have hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0 := fun i => abs_pos.1 (ha.trans_le (hg i))
  refine (specNorm_sub_rbki_replicateCol_sq_le A x hZ hAZ hΔ hpos hgap hx hf (by omega) hrt hc
    hhead htail).trans (add_le_add le_rfl ?_)
  exact mul_inv_pow_mul_sum_inv_sq_mul_le hΔ ha hg hK (by positivity) (sq_nonneg _)

/-- The gapped bound for randomized block Krylov iteration from one start vector off the head
event, Frobenius norm: for a real matrix $\mathbf{A}$, an orthonormal frame $\mathbf{Z}$ of $t$
columns with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$, $\sigma_i > 0$ for $i < t$,
a head of $r = h + 1$ singular values, $r \le t \le q$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and a vector $\mathbf{x}$ with
$\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert \ge a > 0$ for every $i$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
4e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t}{a^2}\,
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$ -/
theorem frobNorm_sub_rbki_replicateCol_sq_le_of_forall_le_abs {t : ℕ} (A : Matrix m n ℝ)
    (x : n → ℝ) {Z : Matrix n (Fin t) ℝ} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i : Fin t => singularValues A i ^ 2)
    {h r q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t) (hq : t ≤ q) {Δ a : ℝ} (hΔ : 0 < Δ)
    (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (ha : 0 < a) (hg : ∀ i, a ≤ |(Zᴴ *ᵥ x) i|) :
    frobNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * (t / a ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  obtain ⟨f, hf, c, b, hc, hhead, htail, hK⟩ :=
    exists_degree_lt_div_sq_le_exp_singularGapRatio A hr hrt (q - t)
  rw [Nat.cast_sub hq] at hK
  have hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0 := fun i => abs_pos.1 (ha.trans_le (hg i))
  refine (frobNorm_sub_rbki_replicateCol_sq_le A x hZ hAZ hΔ hpos hgap hx hf (by omega) hrt hc
    hhead htail).trans (add_le_add le_rfl ?_)
  exact mul_inv_pow_mul_sum_inv_sq_mul_le hΔ ha hg hK (by positivity) (sq_nonneg _)

omit [DecidableEq n] in
/-- A frame of the top $t$ right singular vectors when $\sigma_{t-1} > 0$: orthonormal, with
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\sigma_i^2)$, whose
first $r$ columns give $\llbracket\mathbf{A}\rrbracket_r$ for $r \le t$, and
$\sigma_i > 0$ for $i < t$. -/
private theorem exists_frame_of_singularValues_pos (A : Matrix m n ℝ) {t : ℕ} (ht : 0 < t)
    (h0 : 0 < singularValues A (t - 1)) :
    ∃ Z : Matrix n (Fin t) ℝ, HasOrthonormalCols Z ∧
      Aᴴ * A * Z = Z * Matrix.diagonal (fun i : Fin t => singularValues A i ^ 2) ∧
      (∀ r (hr : r ≤ t), A * Z.submatrix id (Fin.castLE hr) * (Z.submatrix id (Fin.castLE hr))ᴴ =
        truncatedSVD A r) ∧
      frobNorm (A - A * Z * Zᴴ) = frobNorm (A - truncatedSVD A t) ∧
      ∀ i < t, 0 < singularValues A i := by
  classical
  have htn : t ≤ Fintype.card n := by
    have h1 := (singularValues_pos_iff A).1 h0
    have h2 := A.rank_le_card_width
    omega
  obtain ⟨Z, V, hZ, -, -, -, hAZ, -, hpre⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A htn
  exact ⟨Z, hZ, hAZ, hpre, frobNorm_sub_mul_mul_conjTranspose_eq_frobNorm_sub_truncatedSVD A hZ hAZ,
    fun i hi => h0.trans_le (singularValues_antitone A (by omega))⟩

/-! ### The events of one Gaussian start vector -/

omit [DecidableEq n] in
/-- The head coordinates of a Gaussian start vector do not vanish: for a standard Gaussian vector
$\mathbf{x}$ in $\mathbb{R}^n$ and a real matrix $\mathbf{Z}$ with orthonormal columns, almost
surely $(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i \ne 0$ for every $i$. -/
theorem ae_forall_conjTranspose_mulVec_ne_zero_of_hasLaw_gaussianVector
    (hx : HasLaw x (gaussianVector n) μ) {t : ℕ} {Z : Matrix n (Fin t) ℝ}
    (hZ : HasOrthonormalCols Z) :
    ∀ᵐ ω ∂μ, ∀ i, (Zᴴ *ᵥ x ω) i ≠ 0 := by
  classical
  have := hx.isProbabilityMeasure
  have h := measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector hx hZ
    (le_refl (0 : ℝ))
  rw [mul_zero] at h
  have h0 : μ {ω | ∃ i, |(Zᴴ *ᵥ x ω) i| ≤ 0} = 0 :=
    (measureReal_eq_zero_iff).1 (le_antisymm h measureReal_nonneg)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hω ⊢
  obtain ⟨i, hi⟩ := hω
  exact ⟨i, by rw [hi, abs_zero]⟩

/-- Randomized block Krylov iteration from one Gaussian start vector is almost surely exact for a
gapped matrix of low rank: for a real matrix $\mathbf{A}$ of rank at most $t$, a standard Gaussian
vector $\mathbf{x}$ in $\mathbb{R}^n$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$ and $q \ge t$, almost surely
$$\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q) = \mathbf{A}\,.$$ -/
theorem ae_rbki_replicateCol_eq_self_of_hasLaw_gaussianVector (A : Matrix m n ℝ)
    (hx : HasLaw x (gaussianVector n) μ) {t q : ℕ} (hrank : A.rank ≤ t) (hq : t ≤ q) {Δ : ℝ}
    (hΔ : 0 < Δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    ∀ᵐ ω ∂μ, rbki A (Matrix.replicateCol Unit (x ω)) q = A := by
  obtain ⟨Z, V, hZ, -, -, -, hAZ, -, -⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A A.rank_le_card_width
  filter_upwards [ae_forall_conjTranspose_mulVec_ne_zero_of_hasLaw_gaussianVector hx hZ] with ω hω
  exact rbki_replicateCol_eq_self_of_rank_le A (x ω) hZ hAZ le_rfl hΔ
    (fun i hi => hgap i (by omega)) hω (hrank.trans hq)

omit [DecidableEq n] in
/-- A set that is almost surely avoided has probability at most any $\delta \ge 0$. -/
private theorem measureReal_le_of_ae_notMem {S : Set Ω} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ᵐ ω ∂μ, ω ∉ S) : μ.real S ≤ δ := by
  rw [measureReal_def, measure_eq_zero_iff_ae_notMem.2 h, ENNReal.toReal_zero]
  exact hδ

omit [DecidableEq n] in
/-- The bad event of a Gaussian start vector: for a standard Gaussian vector $\mathbf{x}$ in
$\mathbb{R}^n$, a real matrix $\mathbf{Z}$ with $t \ge 1$ orthonormal columns, a real matrix
$\mathbf{M}$ and $\delta > 0$, with probability at least $1 - \delta$ every head coordinate has
$\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert > \delta/(2t)$ and
$\|\mathbf{M}\mathbf{x}\|_2^2 \le 2\|\mathbf{M}\|_{\mathsf{F}}^2/\delta$. -/
theorem measureReal_not_forall_lt_abs_and_norm_mulVec_sq_le_le_of_hasLaw_gaussianVector
    (hx : HasLaw x (gaussianVector n) μ) {t : ℕ} {Z : Matrix n (Fin t) ℝ}
    (hZ : HasOrthonormalCols Z) (M : Matrix m n ℝ) (ht : 0 < t) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | ¬((∀ i, δ / (2 * t) < |(Zᴴ *ᵥ x ω) i|) ∧
      ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2 ≤ frobNorm M ^ 2 / (δ / 2))} ≤ δ := by
  classical
  have := hx.isProbabilityMeasure
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 := measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector hx hZ
    (a := δ / (2 * t)) (by positivity)
  have h2 := measureReal_norm_mulVec_sq_gt_le_of_hasLaw_gaussianVector hx M (half_pos hδ)
  rw [Fintype.card_fin] at h1
  have h3 : (t : ℝ) * (δ / (2 * t)) = δ / 2 := by field_simp
  refine (measureReal_mono (s₂ := {ω | ∃ i, |(Zᴴ *ᵥ x ω) i| ≤ δ / (2 * t)} ∪
    {ω | frobNorm M ^ 2 / (δ / 2) < ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2}) (fun ω hω => ?_)).trans
    ((measureReal_union_le _ _).trans (by linarith))
  simp only [Set.mem_ofPred_eq, not_and_or, not_forall, not_lt, not_le] at hω
  exact hω

omit [DecidableEq n] in
/-- From a bound off the head event to a tail bound: if an error is at most
$b + C\,(t/a^2)\,\|\mathbf{M}\mathbf{x}\|_2^2$ whenever every head coordinate of the Gaussian
start vector is at least $a = \delta/(2t)$ in absolute value, then it exceeds
$b + 8C\,(t^3/\delta^3)\,\|\mathbf{M}\|_{\mathsf{F}}^2$ with probability at most $\delta$. -/
private theorem measureReal_gt_le_of_forall_le_abs (hx : HasLaw x (gaussianVector n) μ) {t : ℕ}
    {Z : Matrix n (Fin t) ℝ} (hZ : HasOrthonormalCols Z) (M : Matrix m n ℝ) (ht : 0 < t)
    {δ b C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) {err : Ω → ℝ}
    (h : ∀ ω, (∀ i, δ / (2 * t) ≤ |(Zᴴ *ᵥ x ω) i|) → err ω ≤
      b + C * (t / (δ / (2 * t)) ^ 2) * ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2) :
    μ.real {ω | b + 8 * C * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm M ^ 2 < err ω} ≤ δ := by
  classical
  have := hx.isProbabilityMeasure
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_not_forall_lt_abs_and_norm_mulVec_sq_le_le_of_hasLaw_gaussianVector hx hZ M ht hδ)
  rintro ⟨h1, h2⟩
  have h3 := h ω fun i => (h1 i).le
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have h4 : C * (t / (δ / (2 * t)) ^ 2) * ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2 ≤
      C * (t / (δ / (2 * t)) ^ 2) * (frobNorm M ^ 2 / (δ / 2)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : C * (t / (δ / (2 * t)) ^ 2) * (frobNorm M ^ 2 / (δ / 2)) =
      8 * C * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm M ^ 2 := by
    field_simp
    ring
  have h6 : b + 8 * C * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm M ^ 2 < err ω := hω
  linarith

/-! ### The truncated output through a range-monotone quantity -/

/-- The truncated block Krylov output against a filtered single-vector sketch: for a real matrix
$\mathbf{A}$, $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, a vector $\mathbf{x}$ in the range
of a block $\mathbf{Y}$, $t \ge 1$, a real polynomial $f$ of degree less than $d$ with
$t + d \le q + 1$ and $\mathbf{K} = [\mathbf{x}, \mathbf{H}\mathbf{x}, \dots,
\mathbf{H}^{t-1}\mathbf{x}]$, for every rank $r$,
$$\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{Y}, q)\rrbracket_r\|_2^2 \le
\sigma_r^2 + \bigl\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}f(\mathbf{H})\mathbf{K}})
\llbracket\mathbf{A}\rrbracket_r\bigr\|_{\mathsf{F}}^2\,.$$
Reverse Eckart–Young and Gu's projected form are applied to
$\mathsf{rbki}(\mathbf{A}, \mathbf{Y}, q)$ itself; the right side is monotone in the range of the
sketch, which contains that of the filtered simulated sketch. -/
theorem specNorm_sub_truncatedSVD_rbki_sq_le_add_frobNorm_one_sub_rangeProjector_mul_sq
    {k' : Type*} [Fintype k'] [DecidableEq m] (A : Matrix m n ℝ) (x : n → ℝ) {Y : Matrix n k' ℝ}
    (hxY : LinearMap.range (Matrix.replicateCol Unit x).mulVecLin ≤
      LinearMap.range Y.mulVecLin) {t q d : ℕ} (r : ℕ) (ht : 0 < t) {f : Polynomial ℝ}
    (hf : f.degree < d) (hd : t + d ≤ q + 1) :
    specNorm (A - truncatedSVD (rbki A Y q) r) ^ 2 ≤ singularValues A r ^ 2 +
      frobNorm ((1 - rangeProjector (A * Polynomial.aeval (Aᴴ * A) f *
        blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)) * truncatedSVD A r) ^ 2 := by
  classical
  have h1 := (isBestRankApprox_truncatedSVD (rsvd A (blockKrylovMatrix (Aᴴ * A) Y q))
    r).specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le
  have h2 := frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add A
    (blockKrylovMatrix (Aᴴ * A) Y q) r
  have hrange : LinearMap.range (A * Polynomial.aeval (Aᴴ * A) f *
      blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t).mulVecLin ≤
      LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) Y q).mulVecLin := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    rw [Matrix.mul_assoc, Matrix.mulVecLin_mul A, LinearMap.range_comp, Matrix.mulVecLin_mul A,
      LinearMap.range_comp]
    refine Submodule.map_mono ?_
    rcases d with _ | d
    · rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, Polynomial.degree_eq_bot] at hf
      rw [hf, map_zero, Matrix.zero_mul, Matrix.mulVecLin_zero, LinearMap.range_zero]
      exact bot_le
    refine (range_aeval_mul_le_blockKrylovSpace (Aᴴ * A) _ hf).trans ?_
    rw [blockKrylovSpace_blockKrylovMatrix]
    exact (blockKrylovSpace_mono _ _ (by omega)).trans (blockKrylovSpace_le_of_range_le hxY q)
  have h3 : frobNorm (truncatedSVD A r -
      rangeProjector (A * blockKrylovMatrix (Aᴴ * A) Y q) * truncatedSVD A r) ≤
      frobNorm ((1 - rangeProjector (A * Polynomial.aeval (Aᴴ * A) f *
        blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)) * truncatedSVD A r) := by
    have h := (lpGauge 2).matrixNorm_le_of_singularValues_le
      (singularValues_one_sub_rangeProjector_mul_le_of_range_le hrange (truncatedSVD A r))
    rwa [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm, Matrix.sub_mul, Matrix.one_mul] at h
  have h4 := pow_le_pow_left₀ (frobNorm_nonneg _) h3 2
  rw [rbki_def]
  linarith

/-- Head capture by the filtered single-vector simulated block: for a real matrix $\mathbf{A}$,
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, an orthonormal frame $\mathbf{Z}$ of $t$ columns
with $\mathbf{H}\mathbf{Z} = \mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$
whose first $r \le t$ columns $\mathbf{W}$ give
$\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_r$, $\sigma_i > 0$
for $i < t$, a gap $\Delta > 0$ with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$,
a vector $\mathbf{x}$ with no vanishing coordinate of $\mathbf{Z}^{\mathsf{H}}\mathbf{x}$, and a
real polynomial $f$ with $\lvert f(\sigma_i^2)\rvert \ge c > 0$ for $i < r$ and
$\lvert f \rvert \le b$ on $[0, \sigma_t^2]$, with
$\mathbf{K} = [\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$,
$$\bigl\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}f(\mathbf{H})\mathbf{K}})
\llbracket\mathbf{A}\rrbracket_r\bigr\|_{\mathsf{F}}^2 \le
\Bigl(\frac{b}{c}\Bigr)^2\Delta^{-2(t-1)}
\Bigl(\sum_{i<t}\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert^{-2}\Bigr)
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$ -/
theorem frobNorm_one_sub_rangeProjector_mul_blockKrylovMatrix_mul_truncatedSVD_sq_le
    [DecidableEq m] {t r : ℕ}
    (A : Matrix m n ℝ) (x : n → ℝ) {Z : Matrix n (Fin t) ℝ} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i : Fin t => singularValues A i ^ 2)
    (hrt : r ≤ t)
    (hAW : A * Z.submatrix id (Fin.castLE hrt) * (Z.submatrix id (Fin.castLE hrt))ᴴ =
      truncatedSVD A r) {Δ : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) (f : Polynomial ℝ) {c b : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ b) :
    frobNorm ((1 - rangeProjector (A * Polynomial.aeval (Aᴴ * A) f *
        blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)) * truncatedSVD A r) ^ 2 ≤
      (b / c) ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
        ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  classical
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have hG : cfc (fun y => f.eval y) (Aᴴ * A) = Polynomial.aeval (Aᴴ * A) f :=
    cfc_polynomial f (Aᴴ * A) hH
  set W := Z.submatrix id (Fin.castLE hrt)
  have hW : HasOrthonormalCols W := hZ.submatrix (Equiv.refl _) (Fin.castLE_injective hrt)
  have hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin :=
    range_le_iff_exists_mul.mpr
      ⟨(1 : Matrix (Fin t) (Fin t) ℝ).submatrix (Equiv.refl _) (Fin.castLE hrt), by
        rw [Matrix.mul_submatrix_one]; rfl⟩
  have hAW' : Aᴴ * A * W =
      W * Matrix.diagonal fun i : Fin r => ((singularValues A i ^ 2 : ℝ) : ℝ) := by
    ext y j
    have h := congrFun (congrFun hAZ y) (Fin.castLE hrt j)
    simp only [Matrix.mul_diagonal] at h ⊢
    exact h
  have hd : Function.Injective fun i : Fin t => singularValues A i ^ 2 := by
    intro i j hij
    have hij' : singularValues A i ^ 2 = singularValues A j ^ 2 := hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have h1 := singularValues_lt_of_gap A hΔ hgap hlt j.2 (hpos i i.2)
      have h2 := pow_lt_pow_left₀ h1 (singularValues_nonneg A j) two_ne_zero
      linarith
    · have h1 := singularValues_lt_of_gap A hΔ hgap hlt i.2 (hpos j j.2)
      have h2 := pow_lt_pow_left₀ h1 (singularValues_nonneg A i) two_ne_zero
      linarith
  have hrank : ((blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t)ᴴ * Z).rank =
      Z.rank := by
    rw [hZ.rank_eq, Fintype.card_fin]
    exact hH.rank_conjTranspose_mul_blockKrylovMatrix_replicateCol hAZ hd hx
  have h4 := hW.matrixNorm_one_sub_rangeProjector_mul_mul_le (lpGauge 2)
    (fun y => f.eval y) hAW' hZ hrank hWZ hc (fun i => hhead i i.2)
  rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm, hG, hAW] at h4
  have h5 := frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le A x hZ hAZ hΔ hpos hgap hx f
    htail
  calc _ ≤ (c⁻¹ * frobNorm ((A * Polynomial.aeval (Aᴴ * A) f -
          A * Polynomial.aeval (Aᴴ * A) f * Z * Zᴴ) *
          blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t *
          pinv (Zᴴ * blockKrylovMatrix (Aᴴ * A) (Matrix.replicateCol Unit x) t))) ^ 2 :=
        pow_le_pow_left₀ (frobNorm_nonneg _) h4 2
    _ ≤ c⁻¹ ^ 2 * (b ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
    _ = _ := by
        rw [div_eq_mul_inv]
        ring

/-- The gapped bound for truncated randomized block Krylov iteration off the head event of a
vector in the range of the block, spectral norm: for a real matrix $\mathbf{A}$, a block
$\mathbf{Y}$ whose range contains $\mathbf{x}$, an orthonormal frame $\mathbf{Z}$ of $t$ columns
with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$ whose first $r$ columns
$\mathbf{W}$ give $\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_r$,
$\sigma_i > 0$ for $i < t$, a head of $r = h + 1$ singular values, $r \le t \le q$, a gap
$\Delta > 0$ with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and
$\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert \ge a > 0$ for every $i$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{Y}, q)\rrbracket_r\|_2^2 \le
\sigma_r^2 + 4e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t}{a^2}\,
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{x}\|_2^2\,.$$ -/
theorem specNorm_sub_truncatedSVD_rbki_sq_le_of_forall_le_abs {k' : Type*} [Fintype k'] {t : ℕ}
    (A : Matrix m n ℝ) (x : n → ℝ) {Y : Matrix n k' ℝ}
    (hxY : LinearMap.range (Matrix.replicateCol Unit x).mulVecLin ≤
      LinearMap.range Y.mulVecLin) {Z : Matrix n (Fin t) ℝ} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i : Fin t => singularValues A i ^ 2)
    {h r q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t) (hq : t ≤ q)
    (hAW : A * Z.submatrix id (Fin.castLE hrt) * (Z.submatrix id (Fin.castLE hrt))ᴴ =
      truncatedSVD A r) {Δ a : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (ha : 0 < a) (hg : ∀ i, a ≤ |(Zᴴ *ᵥ x) i|) :
    specNorm (A - truncatedSVD (rbki A Y q) r) ^ 2 ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * (t / a ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2 := by
  classical
  obtain ⟨f, hf, c, b, hc, hhead, htail, hK⟩ :=
    exists_degree_lt_div_sq_le_exp_singularGapRatio A hr hrt (q - t)
  rw [Nat.cast_sub hq] at hK
  have hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0 := fun i => abs_pos.1 (ha.trans_le (hg i))
  have h1 := specNorm_sub_truncatedSVD_rbki_sq_le_add_frobNorm_one_sub_rangeProjector_mul_sq A x
    hxY r (by omega : 0 < t) hf (by omega : t + (q - t + 1) ≤ q + 1)
  have h2 := frobNorm_one_sub_rangeProjector_mul_blockKrylovMatrix_mul_truncatedSVD_sq_le A x hZ
    hAZ hrt hAW hΔ hpos hgap hx f hc hhead htail
  have h3 := mul_inv_pow_mul_sum_inv_sq_mul_le hΔ ha hg hK (by positivity)
    (sq_nonneg ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖)
  linarith

/-- The gapped tail bound for truncated randomized block Krylov iteration at any block whose
range contains a standard Gaussian vector: the bound of
`NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianVector` for
$\mathsf{rbki}(\mathbf{A}, \mathbf{Y}, q)$ with $\mathbf{x}(\omega)$ in the range of
$\mathbf{Y}(\omega)$. -/
private theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_range_le {k' : Type*}
    [Fintype k'] (A : Matrix m n ℝ) (hx : HasLaw x (gaussianVector n) μ)
    {Y : Ω → Matrix n k' ℝ}
    (hxY : ∀ ω, LinearMap.range (Matrix.replicateCol Unit (x ω)).mulVecLin ≤
      LinearMap.range (Y ω).mulVecLin) {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Y ω) q) r) ^ 2} ≤ δ := by
  have := hx.isProbabilityMeasure
  have ht : 0 < t := by omega
  rcases (singularValues_nonneg A (t - 1)).eq_or_lt with h0 | h0
  · refine measureReal_le_of_ae_notMem hδ.le ?_
    have hrank : A.rank ≤ t := ((singularValues_eq_zero_iff A).1 h0.symm).trans (Nat.sub_le t 1)
    filter_upwards [ae_rbki_replicateCol_eq_self_of_hasLaw_gaussianVector A hx hrank hq hΔ hgap]
      with ω hω hmem
    have hY : rbki A (Y ω) q = A := by
      have h1 := singularValues_sub_rbki_le_of_range_le A (hxY ω) q 0
      rw [hω, sub_self, singularValues_zero_eq_specNorm, singularValues_zero_eq_specNorm,
        specNorm_zero] at h1
      exact (sub_eq_zero.1 (specNorm_eq_zero_iff.1 (le_antisymm h1 (specNorm_nonneg _)))).symm
    rw [hY, specNorm_sub_truncatedSVD] at hmem
    have : 0 ≤ 32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
        Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 := by
      positivity
    linarith
  · obtain ⟨Z, hZ, hAZ, hpre, hF, hpos⟩ := exists_frame_of_singularValues_pos A ht h0
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have key := measureReal_gt_le_of_forall_le_abs hx hZ (A - A * Z * Zᴴ) ht hδ
      (b := singularValues A r ^ 2)
      (C := 4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
        Δ⁻¹ ^ (2 * (t - 1))) (by positivity)
      (err := fun ω => specNorm (A - truncatedSVD (rbki A (Y ω) q) r) ^ 2)
      fun ω hg => specNorm_sub_truncatedSVD_rbki_sq_le_of_forall_le_abs A (x ω) (hxY ω) hZ hAZ
        hr hrt hq (hpre r hrt) hΔ hpos hgap (by positivity) hg
    rw [hF] at key
    refine (measureReal_mono (h₂ := measure_ne_top _ _) fun ω hω => ?_).trans key
    rw [Set.mem_ofPred_eq] at hω ⊢
    linarith

/-! ### One Gaussian start vector, gapped -/

/-- **The gapped tail bound for randomized block Krylov iteration from one start vector, spectral
norm**: for a real matrix $\mathbf{A}$ with singular values $\sigma_0 \ge \sigma_1 \ge \dots$, a
standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$ (independent standard normal entries), a
head of $r = h + 1$ singular values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$
with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2 >
\sigma_r^2 + 32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The start vector is the one-column block `Matrix.replicateCol Unit (x ω)`. The first $t$ Krylov
vectors act as a block of $t$ columns and the Chebyshev filter has degree $q - t$. No positivity
of $\sigma_{t-1}$ is assumed: when $\operatorname{rank}\mathbf{A} < t$ the gap hypothesis makes
the positive singular values distinct and the error is zero almost surely. No gap between
$\sigma_{t-1}$ and $\sigma_t$ is assumed.
[MeyerMuscoMusco2023, Theorem 6], there for the projection onto the output basis with a factor
$1 + \varepsilon$, as a number of iterations in $O(\cdot)$ form with unspecified constants, in
the gap between two singular values and the smallest relative gap among the leading ones; here a
tail bound with explicit constants.
Result: rbki-single-vector-gapped-error -/
theorem measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector (A : Matrix m n ℝ)
    (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2} ≤ δ := by
  have := hx.isProbabilityMeasure
  have ht : 0 < t := by omega
  rcases (singularValues_nonneg A (t - 1)).eq_or_lt with h0 | h0
  · refine measureReal_le_of_ae_notMem hδ.le ?_
    have hrank : A.rank ≤ t := ((singularValues_eq_zero_iff A).1 h0.symm).trans (Nat.sub_le t 1)
    filter_upwards [ae_rbki_replicateCol_eq_self_of_hasLaw_gaussianVector A hx hrank hq hΔ hgap]
      with ω hω hmem
    rw [hω, sub_self, specNorm_zero] at hmem
    have : 0 ≤ singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 := by
      positivity
    linarith
  · obtain ⟨Z, hZ, hAZ, -, hF, hpos⟩ := exists_frame_of_singularValues_pos A ht h0
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have key := measureReal_gt_le_of_forall_le_abs hx hZ (A - A * Z * Zᴴ) ht hδ
      (b := singularValues A r ^ 2)
      (C := 4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
        Δ⁻¹ ^ (2 * (t - 1))) (by positivity)
      (err := fun ω => specNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2)
      fun ω hg => specNorm_sub_rbki_replicateCol_sq_le_of_forall_le_abs A (x ω) hZ hAZ hr hrt hq
        hΔ hpos hgap (by positivity) hg
    rw [hF] at key
    refine (measureReal_mono (h₂ := measure_ne_top _ _) fun ω hω => ?_).trans key
    rw [Set.mem_ofPred_eq] at hω ⊢
    linarith

/-- **The gapped tail bound for randomized block Krylov iteration from one start vector, Frobenius
norm**: for a real matrix $\mathbf{A}$ with singular values $\sigma_0 \ge \sigma_1 \ge \dots$, a
standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$ (independent standard normal entries), a
head of $r = h + 1$ singular values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$
with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_{\mathsf{F}}^2 >
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The start vector is the one-column block `Matrix.replicateCol Unit (x ω)`. No positivity of
$\sigma_{t-1}$ is assumed: when $\operatorname{rank}\mathbf{A} < t$ the error is zero almost
surely.
[MeyerMuscoMusco2023, Theorem 6], there for the projection onto the output basis with a factor
$1 + \varepsilon$, as a number of iterations in $O(\cdot)$ form with unspecified constants, in
the gap between two singular values and the smallest relative gap among the leading ones; here a
tail bound with explicit constants.
Result: rbki-single-vector-gapped-error -/
theorem measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector (A : Matrix m n ℝ)
    (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | frobNorm (A - truncatedSVD A r) ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        frobNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2} ≤ δ := by
  have := hx.isProbabilityMeasure
  have ht : 0 < t := by omega
  rcases (singularValues_nonneg A (t - 1)).eq_or_lt with h0 | h0
  · refine measureReal_le_of_ae_notMem hδ.le ?_
    have hrank : A.rank ≤ t := ((singularValues_eq_zero_iff A).1 h0.symm).trans (Nat.sub_le t 1)
    filter_upwards [ae_rbki_replicateCol_eq_self_of_hasLaw_gaussianVector A hx hrank hq hΔ hgap]
      with ω hω hmem
    rw [hω, sub_self, frobNorm_zero] at hmem
    have : 0 ≤ frobNorm (A - truncatedSVD A r) ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 := by
      positivity
    linarith
  · obtain ⟨Z, hZ, hAZ, -, hF, hpos⟩ := exists_frame_of_singularValues_pos A ht h0
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have key := measureReal_gt_le_of_forall_le_abs hx hZ (A - A * Z * Zᴴ) ht hδ
      (b := frobNorm (A - truncatedSVD A r) ^ 2)
      (C := 4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
        Δ⁻¹ ^ (2 * (t - 1))) (by positivity)
      (err := fun ω => frobNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2)
      fun ω hg => frobNorm_sub_rbki_replicateCol_sq_le_of_forall_le_abs A (x ω) hZ hAZ hr hrt hq
        hΔ hpos hgap (by positivity) hg
    rw [hF] at key
    refine (measureReal_mono (h₂ := measure_ne_top _ _) fun ω hω => ?_).trans key
    rw [Set.mem_ofPred_eq] at hω ⊢
    linarith

/-- **The gapped tail bound for truncated randomized block Krylov iteration from one start
vector, spectral norm**: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$
(independent standard normal entries), a head of $r = h + 1$ singular values, a tail index
$t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, the rank-$r$ truncation keeps the right
side of the untruncated form,
$$\mathbb{P}\Bigl[\|\mathbf{A} -
\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\rrbracket_r\|_2^2 >
\sigma_r^2 + 32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The start vector is the one-column block `Matrix.replicateCol Unit (x ω)`. No positivity of
$\sigma_{t-1}$ is assumed: when $\operatorname{rank}\mathbf{A} < t$ the output is $\mathbf{A}$
almost surely.
[MeyerMuscoMusco2023, Theorem 6], there for the projection onto the output basis with a factor
$1 + \varepsilon$, as a number of iterations in $O(\cdot)$ form with unspecified constants, in
the gap between two singular values and the smallest relative gap among the leading ones; here a
tail bound with explicit constants.
Result: rbki-single-vector-gapped-error -/
theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianVector
    (A : Matrix m n ℝ) (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Matrix.replicateCol Unit (x ω)) q) r) ^ 2} ≤ δ := by
  exact measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_range_le A hx (fun _ => le_rfl) hr
    hrt hq hΔ hδ hgap

/-- **The expectation of the error of randomized block Krylov iteration from one start vector
on the head event**: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$
(independent standard normal entries), an orthonormal frame $\mathbf{Z}$ of $t$ columns with
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$, a head of $r = h + 1$
singular values, $r \le t \le q$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, $\delta > 0$,
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, and the event
$E = \{\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert > \delta/t \text{ for every } i\}$,
$$\mathbb{E}\bigl[\mathbf{1}_E\,
\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2\bigr] \le
\sigma_r^2 + 4e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^2}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
The complement of $E$ has probability at most $\delta$
(`NLAlib.measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector` at
$a = \delta/t$). On $E$ the sum $\sum_i (\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i^{-2}$ is at most
$t^3/\delta^2$, and the tail energy is integrated over the whole space, so the independence of
the head and tail coordinates is not used.
[MeyerMuscoMusco2023, Theorem 6], there in probability, as a number of iterations in $O(\cdot)$
form with unspecified constants; here the expectation restricted to the event $E$, with explicit
constants.
Result: rbki-single-vector-gapped-error -/
theorem integral_setOf_specNorm_sub_rbki_sq_le_of_hasLaw_gaussianVector (A : Matrix m n ℝ)
    (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} {Z : Matrix n (Fin t) ℝ}
    (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i : Fin t => singularValues A i ^ 2)
    (hr : h + 1 = r) (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    ∫ ω in {ω | ∀ i, δ / t < |(Zᴴ *ᵥ x ω) i|},
        specNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 2) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  have := hx.isProbabilityMeasure
  have ht : 0 < t := by omega
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  set C := 4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
    Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 2) with hCdef
  have hC : 0 ≤ C := by positivity
  have hiso := isIsotropic_of_hasLaw_gaussianVector hx
  have hN := hiso.integrable_norm_mulVec_sq (A - A * Z * Zᴴ)
  have hrep : Measurable (Matrix.replicateCol Unit : (n → ℝ) → Matrix n Unit ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun _ => measurable_pi_apply i
  have hint := integrable_specNorm_sub_rbki_sq A (hrep.comp_aemeasurable hx.aemeasurable) q
  have hG : Integrable (fun ω => singularValues A r ^ 2 +
      C * ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x ω)‖ ^ 2) μ :=
    (integrable_const _).add (hN.const_mul C)
  have hG0 : ∀ ω, 0 ≤ singularValues A r ^ 2 +
      C * ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x ω)‖ ^ 2 := fun ω =>
    add_nonneg (sq_nonneg _) (mul_nonneg hC (sq_nonneg _))
  have hE : NullMeasurableSet {ω | ∀ i, δ / t < |(Zᴴ *ᵥ x ω) i|} μ := by
    have hS : MeasurableSet {v : n → ℝ | ∀ i, δ / t < |(Zᴴ *ᵥ v) i|} := by
      rw [Set.ofPred_forall]
      refine MeasurableSet.iInter fun i => measurableSet_lt measurable_const ?_
      exact (continuous_abs.comp ((continuous_apply i).comp
        (Continuous.matrix_mulVec continuous_const continuous_id))).measurable
    exact hx.aemeasurable.nullMeasurable hS
  have hpt : ∀ ω, ω ∈ {ω | ∀ i, δ / t < |(Zᴴ *ᵥ x ω) i|} →
      specNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2 ≤
        singularValues A r ^ 2 + C * ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x ω)‖ ^ 2 := by
    intro ω hω
    have hδt : 0 < δ / t := by positivity
    rcases (singularValues_nonneg A (t - 1)).eq_or_lt with h0 | h0
    · have hrank : A.rank ≤ t :=
        ((singularValues_eq_zero_iff A).1 h0.symm).trans (Nat.sub_le t 1)
      have hne : ∀ i, (Zᴴ *ᵥ x ω) i ≠ 0 := fun i => abs_pos.1 (hδt.trans (hω i))
      rw [rbki_replicateCol_eq_self_of_rank_le A (x ω) hZ hAZ hrank hΔ hgap hne hq, sub_self,
        specNorm_zero]
      exact le_trans (by norm_num) (hG0 ω)
    · have hpos : ∀ i < t, 0 < singularValues A i := fun i hi =>
        h0.trans_le (singularValues_antitone A (by omega))
      have h1 := specNorm_sub_rbki_replicateCol_sq_le_of_forall_le_abs A (x ω) hZ hAZ hr hrt hq
        hΔ hpos hgap hδt fun i => (hω i).le
      have h2 : (t : ℝ) / (δ / t) ^ 2 = (t : ℝ) ^ 3 / δ ^ 2 := by
        field_simp
      rw [h2] at h1
      exact h1
  calc ∫ ω in {ω | ∀ i, δ / t < |(Zᴴ *ᵥ x ω) i|},
        specNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2 ∂μ
      ≤ ∫ ω in {ω | ∀ i, δ / t < |(Zᴴ *ᵥ x ω) i|}, (singularValues A r ^ 2 +
          C * ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x ω)‖ ^ 2) ∂μ :=
        setIntegral_mono_on_ae₀ hint.integrableOn hG.integrableOn hE (ae_of_all _ hpt)
    _ ≤ ∫ ω, (singularValues A r ^ 2 +
          C * ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x ω)‖ ^ 2) ∂μ :=
        setIntegral_le_integral hG (ae_of_all _ hG0)
    _ = singularValues A r ^ 2 + C * frobNorm (A - truncatedSVD A t) ^ 2 := by
        rw [integral_add (integrable_const _) (hN.const_mul C), integral_const,
          integral_const_mul, hiso.integral_norm_mulVec_sq, probReal_univ, one_smul,
          frobNorm_sub_mul_mul_conjTranspose_eq_frobNorm_sub_truncatedSVD A hZ hAZ]

/-! ### One Gaussian start vector, gapless -/

/-- The case split in probability: if the truncated block Krylov error at every head
$h + 1 \le r$ exceeds the gapped bound $\sigma_{h+1}^2 + 32e^{-8(q-r)\sqrt{\gamma_h}}\,D\,T\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$ with probability at most
$\delta$, then the error at rank $r$ exceeds the same bound with $(1 + \varepsilon)^2\sigma_r^2$
and $\gamma = \varepsilon/(2 + \varepsilon)$ with probability at most $\delta$. -/
private theorem measureReal_gt_one_add_sq_mul_le_of_gapped [IsProbabilityMeasure μ] {k' : Type*}
    [Fintype k'] (A : Matrix m n ℝ) (Y : Ω → Matrix n k' ℝ) {r q : ℕ} (hq : r ≤ q)
    {δ ε D T : ℝ} (hε : 0 < ε) (hD : 0 ≤ D) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (G : ∀ h, h + 1 ≤ r → μ.real {ω | singularValues A (h + 1) ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (singularGapRatio A h r)) * D * T *
          frobNorm (A - truncatedSVD A r) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Y ω) q) (h + 1)) ^ 2} ≤ δ) :
    μ.real {ω | (1 + ε) ^ 2 * singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) * D * T *
          frobNorm (A - truncatedSVD A r) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Y ω) q) r) ^ 2} ≤ δ := by
  have hq' : (0 : ℝ) ≤ (q : ℝ) - r := sub_nonneg.2 (by exact_mod_cast hq)
  rcases singularValues_zero_le_or_exists_singularGapRatio A r hε with h0 | ⟨h, hhr, hσ, hgap⟩
  · refine (measureReal_mono (s₂ := ∅) fun ω hω => ?_).trans
      (by rw [measureReal_empty]; exact hδ)
    have hω' : (1 + ε) ^ 2 * singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) * D * T *
          frobNorm (A - truncatedSVD A r) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Y ω) q) r) ^ 2 := hω
    have h1 := singularValues_sub_truncatedSVD_rsvd_le_of_le A
      (blockKrylovMatrix (Aᴴ * A) (Y ω) q) (Nat.zero_le r) 0
    rw [truncatedSVD_zero, sub_zero, singularValues_zero_eq_specNorm,
      singularValues_zero_eq_specNorm, ← rbki_def] at h1
    rw [singularValues_zero_eq_specNorm] at h0
    have h2 := pow_le_pow_left₀ (specNorm_nonneg _) (h1.trans h0) 2
    rw [mul_pow] at h2
    have h3 : 0 ≤ 32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) * D * T *
        frobNorm (A - truncatedSVD A r) ^ 2 := by positivity
    linarith
  · refine (measureReal_mono fun ω hω => ?_).trans (G h hhr)
    have hω' : (1 + ε) ^ 2 * singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) * D * T *
          frobNorm (A - truncatedSVD A r) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Y ω) q) r) ^ 2 := hω
    have h1 := singularValues_sub_truncatedSVD_rsvd_le_of_le A
      (blockKrylovMatrix (Aᴴ * A) (Y ω) q) hhr 0
    rw [singularValues_zero_eq_specNorm, singularValues_zero_eq_specNorm, ← rbki_def] at h1
    have h2 := pow_le_pow_left₀ (specNorm_nonneg _) h1 2
    have he : Antitone fun γ : ℝ => 32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt γ) := by
      intro a b hab
      have := Real.sqrt_le_sqrt hab
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by norm_num)
    have h3 : 32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (singularGapRatio A h r)) * (D * T) *
        frobNorm (A - truncatedSVD A r) ^ 2 ≤
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) * (D * T) *
          frobNorm (A - truncatedSVD A r) ^ 2 :=
      mul_frobNorm_sub_truncatedSVD_sq_le A he (mul_nonneg hD hT) hgap
    have h4 : singularValues A (h + 1) ^ 2 ≤ (1 + ε) ^ 2 * singularValues A r ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (singularValues_nonneg _ _) hσ 2
    rw [Set.mem_ofPred_eq]
    linarith

/-- **The gapless tail bound for truncated randomized block Krylov iteration from one start
vector, $(1 + \varepsilon)$ form**: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$
(independent standard normal entries), a target rank $r$, depth $q \ge r$, a gap $\Delta > 0$
with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < r$, $\delta > 0$ and
$\varepsilon > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{A} -
\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\rrbracket_r\|_2^2 >
(1 + \varepsilon)^2\sigma_r^2 +
32e^{-8(q-r)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\Delta^{-2(r-1)}\,\frac{r^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The start vector is the one-column block `Matrix.replicateCol Unit (x ω)`. No gap between
$\sigma_{r-1}$ and $\sigma_r$ is assumed; the gap $\Delta$ among the top $r$ singular values is
the price of the single start vector.
[MeyerMuscoMusco2023, Theorem 1], there as a number of iterations in $O(\cdot)$ form with
unspecified constants, for a factor $1 + \varepsilon$ on the optimal error in the spectral or the
Frobenius norm; here a tail bound in the spectral norm with explicit constants and an additive
Frobenius term.
Result: rbki-single-vector-gapless-error -/
theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianVector
    (A : Matrix m n ℝ) (hx : HasLaw x (gaussianVector n) μ) {r q : ℕ} (hq : r ≤ q)
    {Δ δ ε : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ) (hε : 0 < ε)
    (hgap : ∀ i, i + 1 < r → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | (1 + ε) ^ 2 * singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) *
          Δ⁻¹ ^ (2 * (r - 1)) * ((r : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A r) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Matrix.replicateCol Unit (x ω)) q) r) ^ 2} ≤ δ := by
  have := hx.isProbabilityMeasure
  exact measureReal_gt_one_add_sq_mul_le_of_gapped A (fun ω => Matrix.replicateCol Unit (x ω)) hq
    hε (by positivity) (by positivity) hδ.le fun h hhr =>
    measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianVector A hx rfl hhr hq
      hΔ hδ hgap

/-! ### A Gaussian block of any size -/

omit [Fintype n] [DecidableEq n] in
/-- A column lies in the range: the range of the one-column block of column $j$ of
$\mathbf{X}$ is contained in the range of $\mathbf{X}$. -/
private theorem range_replicateCol_col_le (X : Matrix n l ℝ) (j : l) :
    LinearMap.range (Matrix.replicateCol Unit fun i => X i j).mulVecLin ≤
      LinearMap.range X.mulVecLin := by
  classical
  refine range_le_iff_exists_mul.mpr ⟨Matrix.replicateCol Unit (Pi.single j 1), ?_⟩
  ext i u
  simp [Matrix.mul_apply, Pi.single_apply]

/-- **The gapped tail bound for randomized block Krylov iteration with a block of any size,
spectral norm**: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries) with $\ell \ge 1$ columns, a head of $r = h + 1$ singular
values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 >
\sigma_r^2 + 32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The index type of the columns is assumed nonempty. The block does at least as well as its first
column at the same depth, so the bound does not improve with $\ell$; for $t + 2 \le \ell$ the
bound in expectation
`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix` needs no gap
$\Delta$.
[MeyerMuscoMusco2023, Theorem 6], there for one start vector, as a number of iterations in
$O(\cdot)$ form with unspecified constants; here a tail bound with explicit constants for a block
of any size, which does not use the block size.
Result: rbki-any-block-gapped-error -/
theorem measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix [Nonempty l]
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - rbki A (X ω) q) ^ 2} ≤ δ := by
  have := hX.isProbabilityMeasure
  obtain ⟨j⟩ := ‹Nonempty l›
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector A
      (hasLaw_col_of_hasLaw_gaussianMatrix hX j) hr hrt hq hΔ hδ hgap)
  have h1 := singularValues_sub_rbki_le_of_range_le A (range_replicateCol_col_le (X ω) j) q 0
  rw [singularValues_zero_eq_specNorm, singularValues_zero_eq_specNorm] at h1
  exact lt_of_lt_of_le hω (pow_le_pow_left₀ (specNorm_nonneg _) h1 2)

/-- **The gapped tail bound for randomized block Krylov iteration with a block of any size,
Frobenius norm**: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries) with $\ell \ge 1$ columns, a head of $r = h + 1$ singular
values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_{\mathsf{F}}^2 >
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The index type of the columns is assumed nonempty. The block does at least as well as its first
column at the same depth.
[MeyerMuscoMusco2023, Theorem 6], there for one start vector, as a number of iterations in
$O(\cdot)$ form with unspecified constants; here a tail bound with explicit constants for a block
of any size, which does not use the block size.
Result: rbki-any-block-gapped-error -/
theorem measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix [Nonempty l]
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | frobNorm (A - truncatedSVD A r) ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        frobNorm (A - rbki A (X ω) q) ^ 2} ≤ δ := by
  have := hX.isProbabilityMeasure
  obtain ⟨j⟩ := ‹Nonempty l›
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector A
      (hasLaw_col_of_hasLaw_gaussianMatrix hX j) hr hrt hq hΔ hδ hgap)
  have h1 := (lpGauge 2).matrixNorm_le_of_singularValues_le
    (singularValues_sub_rbki_le_of_range_le A (range_replicateCol_col_le (X ω) j) q)
  rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h1
  exact lt_of_lt_of_le hω (pow_le_pow_left₀ (frobNorm_nonneg _) h1 2)

/-- **The gapped tail bound for truncated randomized block Krylov iteration with a block of any
size, spectral norm**: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries) with $\ell \ge 1$ columns, a head of $r = h + 1$ singular
values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} -
\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2 >
\sigma_r^2 + 32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The index type of the columns is assumed nonempty. The truncated error is not monotone in the
block, so this is not a comparison of outputs: the bound for one column is proved through a
quantity that is monotone in the range of the sketch.
[MeyerMuscoMusco2023, Theorem 6], there for one start vector, as a number of iterations in
$O(\cdot)$ form with unspecified constants; here a tail bound with explicit constants for a block
of any size, which does not use the block size.
Result: rbki-any-block-gapped-error -/
theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianMatrix
    [Nonempty l] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ}
    (hr : h + 1 = r) (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2} ≤ δ := by
  obtain ⟨j⟩ := ‹Nonempty l›
  exact measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_range_le A
    (hasLaw_col_of_hasLaw_gaussianMatrix hX j) (fun ω => range_replicateCol_col_le (X ω) j) hr
    hrt hq hΔ hδ hgap

/-- **The gapless tail bound for truncated randomized block Krylov iteration with a block of any
size, $(1 + \varepsilon)$ form**: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries) with $\ell \ge 1$ columns, a target rank $r$, depth
$q \ge r$, a gap $\Delta > 0$ with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every
$i + 1 < r$, $\delta > 0$ and $\varepsilon > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{A} -
\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2 >
(1 + \varepsilon)^2\sigma_r^2 +
32e^{-8(q-r)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\Delta^{-2(r-1)}\,\frac{r^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The index type of the columns is assumed nonempty. For $r + 2 \le \ell$ the bound in expectation
`NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`
needs no gap $\Delta$.
[MeyerMuscoMusco2023, Theorem 1], there for one start vector, as a number of iterations in
$O(\cdot)$ form with unspecified constants; here a tail bound with explicit constants for a block
of any size under the gap hypothesis of one vector, which does not use the block size, unlike
[MeyerMuscoMusco2023, Theorem 11].
Result: rbki-any-block-gapless-error -/
theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianMatrix
    [Nonempty l] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hq : r ≤ q) {Δ δ ε : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ) (hε : 0 < ε)
    (hgap : ∀ i, i + 1 < r → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | (1 + ε) ^ 2 * singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) *
          Δ⁻¹ ^ (2 * (r - 1)) * ((r : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A r) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2} ≤ δ := by
  have := hX.isProbabilityMeasure
  exact measureReal_gt_one_add_sq_mul_le_of_gapped A X hq hε (by positivity) (by positivity) hδ.le
    fun h hhr => measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianMatrix A
      hX rfl hhr hq hΔ hδ hgap

end NLAlib
