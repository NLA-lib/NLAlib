/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.Norms.SchattenPinching
public import NLAlib.Matrix.Spectral.CompressionSingularValues
public import NLAlib.Matrix.Spectral.SingularValueDecay

/-!
# Low-rank approximation error from singular value deficits

Deterministic error bounds, in Schatten norms, for a low-rank approximation built from an
orthogonal projector $\mathbf{P}$ on the left, in terms of the *deficits*
$\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2$, $i < k$, of the compression
$\mathbf{P}\mathbf{A}$. Two outputs are covered. The *two-sided* output $\mathbf{A}\mathbf{Q}$,
for an orthogonal projector $\mathbf{Q}$ with $\mathbf{P}\mathbf{A}\mathbf{Q} =
\mathbf{P}\mathbf{A}$ (the row space of $\mathbf{P}\mathbf{A}$ lies in the range of
$\mathbf{Q}$), for $1 \le p < \infty$; the *one-sided* output $\mathbf{P}\mathbf{A}$, for
$2 \le p < \infty$ and in the Frobenius norm. Nothing here is about a Krylov space or a random
matrix: the hypotheses are inequalities between singular values.

The *tail-count forms* replace the case analysis of [BakshiClarksonWoodruff2022] by one
inequality: if $\sigma_k \le \kappa\,\sigma_{k+j}$ (the spectrum has not dropped by the factor
$\kappa$ after $j$ more singular values), then $\sigma_k^p$ is at most
$\kappa^p/(j + 1)$ times the optimal error, so deficits of relative size $\gamma$ cost
$k\gamma\kappa^p/(j + 1)$.

## Main results

* `IsStarProjection.schattenNorm_sub_mul_rpow_add_le`,
  `IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum`,
  `IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum_mul`: the two-sided error from the
  deficits, $1 \le p < \infty$.
* `IsStarProjection.matrixNorm_sub_mul_le_matrixNorm_sub_mul`: the two-sided error is at most the
  one-sided error, in every unitarily invariant norm.
* `IsStarProjection.schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul`,
  `IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq_le_of_singularValues_le_mul`,
  `NLAlib.min_schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul`: the tail-count forms for
  $1 \le p \le 2$, for the Frobenius norm, and for the better of two candidates.
* `NLAlib.schattenNorm_sub_truncatedSVD_rpow_eq_add_sum`: the Schatten tail split at a later
  index.
* `IsStarProjection.schattenNorm_sub_mul_le_add_rpow`,
  `IsStarProjection.schattenNorm_sub_mul_le_of_sq_singularValues_sub_le`,
  `IsStarProjection.schattenNorm_sub_mul_le_mul_of_singularValues_le_mul`: the head split and
  the tail-count form for $2 \le p < \infty$, one-sided.
* `IsStarProjection.frobNorm_truncatedSVD_sub_mul_le_sqrt_mul`: head capture from small head
  deficits and a gap.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### The Schatten tail -/

omit [DecidableEq m] [DecidableEq n] in
/-- The Schatten tail splits at a later index: for $0 < p < \infty$ and $L \le k$,
$$\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_L\|_{S_p}^p =
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sum_{L \le i < k} \sigma_i(\mathbf{A})^p\,.$$ -/
theorem schattenNorm_sub_truncatedSVD_rpow_eq_add_sum {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (A : Matrix m n 𝕜) {L k : ℕ} (hLk : L ≤ k) :
    schattenNorm p (A - truncatedSVD A L) ^ p.toReal =
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        ∑ i ∈ Finset.Ico L k, singularValues A i ^ p.toReal := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLk
  have hL : (A - truncatedSVD A L).rank ≤ d + (Fintype.card n + L) := by
    have := (A - truncatedSVD A L).rank_le_card_width
    omega
  have hk : (A - truncatedSVD A (L + d)).rank ≤ Fintype.card n + L := by
    have := (A - truncatedSVD A (L + d)).rank_le_card_width
    omega
  rw [schattenNorm_rpow hp0 hp _ hL, schattenNorm_rpow hp0 hp _ hk, Finset.sum_range_add,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
    simp only [singularValues_sub_truncatedSVD, add_assoc]

/-! ### The two-sided output, $1 \le p < \infty$ -/

omit [DecidableEq m] [DecidableEq n] in
/-- **The two-sided error against the energy of the compression**: for $1 \le p < \infty$ and
orthogonal projectors $\mathbf{P}$, $\mathbf{Q}$ with
$\mathbf{P}\mathbf{A}\mathbf{Q} = \mathbf{P}\mathbf{A}$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{S_p}^p + \|\mathbf{P}\mathbf{A}\|_{S_p}^p \le
\|\mathbf{A}\|_{S_p}^p\,.$$
Under the hypothesis, $(\mathbf{I} - \mathbf{P})\mathbf{A}(\mathbf{I} - \mathbf{Q}) =
\mathbf{A}(\mathbf{I} - \mathbf{Q})$, so this is
`IsStarProjection.schattenNorm_mul_mul_rpow_add_le`.
[BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there with $\mathbf{P} =
\mathbf{W}\mathbf{W}^{\mathsf{T}}$ for a Krylov basis $\mathbf{W}$ and $\mathbf{Q}$ the projector
onto the range of $\mathbf{A}^{\mathsf{T}}\mathbf{W}$, here for any pair of projectors with
$\mathbf{P}\mathbf{A}\mathbf{Q} = \mathbf{P}\mathbf{A}$. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_add_le {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) :
    schattenNorm p (A - A * Q) ^ p.toReal + schattenNorm p (P * A) ^ p.toReal ≤
      schattenNorm p A ^ p.toReal := by
  classical
  have h := hP.schattenNorm_mul_mul_rpow_add_le hp1 hp hQ A
  have e : (1 - P) * A * (1 - Q) = A - A * Q := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPAQ]
    abel
  rw [hPAQ, e] at h
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- **The two-sided error from the deficits in $p$-th powers**: for $1 \le p < \infty$, orthogonal
projectors $\mathbf{P}$, $\mathbf{Q}$ with $\mathbf{P}\mathbf{A}\mathbf{Q} =
\mathbf{P}\mathbf{A}$ and every $k$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{S_p}^p \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sum_{i<k} \bigl(\sigma_i(\mathbf{A})^p - \sigma_i(\mathbf{P}\mathbf{A})^p\bigr)\,.$$
[BakshiClarksonWoodruff2022, Lemma 3.4]; there for a basis with a per-vector guarantee and inside
a probability, here deterministic, with hypotheses on the singular values of
$\mathbf{P}\mathbf{A}$ only. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) (k : ℕ) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤ schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
      ∑ i ∈ Finset.range k,
        (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have h := hP.schattenNorm_sub_mul_rpow_add_le hp1 hp hQ hPAQ
  have hA := schattenNorm_sub_truncatedSVD_rpow_eq_add_sum hp0 hp A (Nat.zero_le k)
  rw [truncatedSVD_zero, sub_zero, ← Finset.range_eq_Ico] at hA
  -- the energy of `PA` is at least that of its first `k` singular values
  have hPA : ∑ i ∈ Finset.range k, singularValues (P * A) i ^ p.toReal ≤
      schattenNorm p (P * A) ^ p.toReal := by
    rw [schattenNorm_rpow hp0 hp _ (N := k + Fintype.card n)
      ((P * A).rank_le_card_width.trans (Nat.le_add_left _ _)), Finset.sum_range_add]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg _ _) _)
  rw [Finset.sum_sub_distrib]
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- **The two-sided error from the deficits in squares**: for $1 \le p < \infty$, orthogonal
projectors $\mathbf{P}$, $\mathbf{Q}$ with $\mathbf{P}\mathbf{A}\mathbf{Q} =
\mathbf{P}\mathbf{A}$ and every $k$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{S_p}^p \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sum_{i<k} \max\Bigl(1, \frac{p}{2}\Bigr)\,\sigma_i(\mathbf{A})^{p-2}
\bigl(\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2\bigr)\,,$$
termwise from `Real.rpow_sub_rpow_le_max_mul` at the exponent $p/2$.
[BakshiClarksonWoodruff2022, Lemma 3.4]; there with the constant $p/2$, which is correct only
for $p \ge 2$; here $\max(1, p/2)$. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum_mul {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) (k : ℕ) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤ schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
      ∑ i ∈ Finset.range k, max 1 (p.toReal / 2) * singularValues A i ^ (p.toReal - 2) *
        (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hp1).ne' hp
  refine (hP.schattenNorm_sub_mul_rpow_le_add_sum hp1 hp hQ hPAQ k).trans
    (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
  exact Real.rpow_sub_rpow_le_max_mul_sq (singularValues_nonneg _ _)
    (hP.singularValues_mul_le A i) hr

omit [DecidableEq m] [DecidableEq n] in
/-- The two-sided error is at most the one-sided error: for a matrix $\mathbf{P}$, an orthogonal
projector $\mathbf{Q}$ with $\mathbf{P}\mathbf{A}\mathbf{Q} = \mathbf{P}\mathbf{A}$ and every
unitarily invariant norm,
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{\Phi} \le \|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\Phi}\,,$$
since $\mathbf{A} - \mathbf{A}\mathbf{Q} =
(\mathbf{A} - \mathbf{P}\mathbf{A})(\mathbf{I} - \mathbf{Q})$. It transfers every bound for the
one-sided output $\mathbf{P}\mathbf{A}$ to the two-sided output $\mathbf{A}\mathbf{Q}$. -/
theorem _root_.IsStarProjection.matrixNorm_sub_mul_le_matrixNorm_sub_mul (Φ : SymmetricGauge)
    {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) :
    Φ.matrixNorm (A - A * Q) ≤ Φ.matrixNorm (A - P * A) := by
  classical
  have h : A - A * Q = (A - P * A) * (1 - Q) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one, hPAQ]
    abel
  rw [h]
  exact (Φ.matrixNorm_mul_le_mul_specNorm _ _).trans
    (mul_le_of_le_one_right (Φ.matrixNorm_nonneg _) hQ.one_sub.specNorm_le_one)

/-! ### Tail-count forms, $1 \le p \le 2$ and Frobenius -/

omit [DecidableEq m] [DecidableEq n] in
/-- **The tail-count form of the two-sided error, $1 \le p \le 2$**: let $\mathbf{P}$,
$\mathbf{Q}$ be orthogonal projectors with $\mathbf{P}\mathbf{A}\mathbf{Q} =
\mathbf{P}\mathbf{A}$, let $\gamma, \kappa \ge 0$ and $\beta_i \ge 0$ for $i < k$, with
$\beta_i = 0$ for all $i < k$ if $\sigma_k(\mathbf{A}) = 0$. If the tail is flat,
$\sigma_k \le \kappa\,\sigma_{k+j}$, and the deficits satisfy
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 - \beta_i \le
\sigma_i(\mathbf{P}\mathbf{A})^2$ for $i < k$, then
$$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\|_{S_p}^p \le
\Bigl(1 + \frac{k\gamma\kappa^p}{j + 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sigma_k(\mathbf{A})^{p-2} \sum_{i<k} \beta_i\,.$$
The relative part $\gamma$ of the deficits is paid for by the tail count
`NLAlib.mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow`; the absolute parts
$\beta_i$ enter through their sum. The condition at $\sigma_k = 0$ is needed because
$\sigma_k^{p-2}$ is $0$ there in Lean for $p < 2$; at $p = 2$ it is not needed.
[BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there the case of a heavy tail, with
unspecified constants, here one inequality with the flatness $\kappa$ and the count $j + 1$ as
parameters. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) {k j : ℕ} {γ κ : ℝ} {β : ℕ → ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (hβ : ∀ i < k, 0 ≤ β i) (hβ0 : singularValues A k = 0 → ∀ i < k, β i = 0)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 - β i ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤
      (1 + k * γ * κ ^ p.toReal / ((j : ℝ) + 1)) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) * ∑ i ∈ Finset.range k, β i := sorry

omit [DecidableEq m] [DecidableEq n] in
/-- **The tail-count form of the Frobenius error, one-sided**: let $\mathbf{P}$ be an orthogonal
projector and $\gamma \ge 0$. If the tail is flat, $\sigma_k \le \kappa\,\sigma_{k+j}$, and
the deficits satisfy
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 - \beta_i \le
\sigma_i(\mathbf{P}\mathbf{A})^2$ for $i < k$, then
$$\|\mathbf{A} - \llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k\gamma\kappa^2}{j + 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 + \sum_{i<k} \beta_i\,.$$
[BakshiClarksonWoodruff2022, proof of Theorem 3.1]; the case $p = 2$ of the heavy-tail case
there, here for the truncated compression $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ with the
flatness $\kappa$ and the count $j + 1$ as parameters. -/
theorem _root_.IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq_le_of_singularValues_le_mul
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) {A : Matrix m n 𝕜} {k j : ℕ} {γ κ : ℝ}
    {β : ℕ → ℝ} (hγ : 0 ≤ γ) (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 - β i ≤
      singularValues (P * A) i ^ 2) :
    frobNorm (A - truncatedSVD (P * A) k) ^ 2 ≤
      (1 + k * γ * κ ^ 2 / ((j : ℝ) + 1)) * frobNorm (A - truncatedSVD A k) ^ 2 +
        ∑ i ∈ Finset.range k, β i := by
  set E := frobNorm (A - truncatedSVD A k) ^ 2
  -- the tail count at `p = 2`: `(j + 1) σ_{k+j}² ≤ E`
  have hcount : ((j : ℝ) + 1) * singularValues A (k + j) ^ 2 ≤ E := by
    have h := mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow (p := 2)
      two_ne_zero ENNReal.ofNat_ne_top A k j
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, schattenNorm_two] using h
  have hk : singularValues A k ^ 2 ≤ κ ^ 2 * singularValues A (k + j) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (singularValues_nonneg A k) htail 2
  have hj : (0 : ℝ) < j + 1 := by positivity
  have hσ : singularValues A k ^ 2 ≤ κ ^ 2 / ((j : ℝ) + 1) * E := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hj]
    nlinarith [sq_nonneg κ]
  have hsum : ∑ i ∈ Finset.range k, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) ≤
      k * (γ * singularValues A k ^ 2) + ∑ i ∈ Finset.range k, β i := by
    have h := Finset.sum_le_sum fun i (hi : i ∈ Finset.range k) =>
      (show singularValues A i ^ 2 - singularValues (P * A) i ^ 2 ≤
          γ * singularValues A k ^ 2 + β i by linarith [hritz i (Finset.mem_range.mp hi)])
    rwa [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  rw [hP.frobNorm_sub_truncatedSVD_mul_sq A k]
  have hkγ : (k : ℝ) * (γ * singularValues A k ^ 2) ≤ k * (γ * (κ ^ 2 / ((j : ℝ) + 1) * E)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσ hγ) (Nat.cast_nonneg k)
  have e : (1 + k * γ * κ ^ 2 / ((j : ℝ) + 1)) * E =
      E + k * (γ * (κ ^ 2 / ((j : ℝ) + 1) * E)) := by ring
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- **The better of two candidates, $1 \le p \le 2$**: let $(\mathbf{P}_1, \mathbf{Q}_1)$ and
$(\mathbf{P}_2, \mathbf{Q}_2)$ be pairs of orthogonal projectors with
$\mathbf{P}_a\mathbf{A}\mathbf{Q}_a = \mathbf{P}_a\mathbf{A}$, let
$\gamma_1, \gamma_2, \kappa \ge 0$ and $\beta^{(1)}_i, \beta^{(2)}_i \ge 0$ for $i < k$, all
zero if $\sigma_k(\mathbf{A}) = 0$. Suppose the first pair has deficits
$\sigma_i(\mathbf{A})^2 - \gamma_1\sigma_k(\mathbf{A})^2 - \beta^{(1)}_i \le
\sigma_i(\mathbf{P}_1\mathbf{A})^2$ for $i < k$, and the second pair has
$\sigma_i(\mathbf{A})^2 - \gamma_2\sigma_k(\mathbf{A})^2 - \beta^{(2)}_i \le
\sigma_i(\mathbf{P}_2\mathbf{A})^2$ for $i < k$ whenever there is a gap,
$\kappa\,\sigma_{k+j} < \sigma_k$. Then
$$\min\bigl(\|\mathbf{A} - \mathbf{A}\mathbf{Q}_1\|_{S_p}^p,
\|\mathbf{A} - \mathbf{A}\mathbf{Q}_2\|_{S_p}^p\bigr) \le
\Bigl(1 + k\max\Bigl(\frac{\gamma_1\kappa^p}{j + 1}, \gamma_2\Bigr)\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sigma_k(\mathbf{A})^{p-2}
\max\Bigl(\sum_{i<k} \beta^{(1)}_i, \sum_{i<k} \beta^{(2)}_i\Bigr)\,.$$
[BakshiClarksonWoodruff2022, Algorithm 3.2]; there the algorithm selects one of two block Krylov
runs from estimated singular values, here a statement about two pairs of projectors produced in
any way, with no selection rule. -/
theorem min_schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P₁ P₂ : Matrix m m 𝕜} {Q₁ Q₂ : Matrix n n 𝕜}
    (hP₁ : IsStarProjection P₁) (hQ₁ : IsStarProjection Q₁) (hP₂ : IsStarProjection P₂)
    (hQ₂ : IsStarProjection Q₂) {A : Matrix m n 𝕜} (h₁ : P₁ * A * Q₁ = P₁ * A)
    (h₂ : P₂ * A * Q₂ = P₂ * A) {k j : ℕ} {γ₁ γ₂ κ : ℝ} {β₁ β₂ : ℕ → ℝ} (hγ₁ : 0 ≤ γ₁)
    (hγ₂ : 0 ≤ γ₂) (hκ : 0 ≤ κ) (hβ₁ : ∀ i < k, 0 ≤ β₁ i) (hβ₂ : ∀ i < k, 0 ≤ β₂ i)
    (hβ0 : singularValues A k = 0 → ∀ i < k, β₁ i = 0 ∧ β₂ i = 0)
    (hritz₁ : ∀ i < k, singularValues A i ^ 2 - γ₁ * singularValues A k ^ 2 - β₁ i ≤
      singularValues (P₁ * A) i ^ 2)
    (hritz₂ : κ * singularValues A (k + j) < singularValues A k →
      ∀ i < k, singularValues A i ^ 2 - γ₂ * singularValues A k ^ 2 - β₂ i ≤
        singularValues (P₂ * A) i ^ 2) :
    min (schattenNorm p (A - A * Q₁) ^ p.toReal) (schattenNorm p (A - A * Q₂) ^ p.toReal) ≤
      (1 + k * max (γ₁ * κ ^ p.toReal / ((j : ℝ) + 1)) γ₂) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) *
          max (∑ i ∈ Finset.range k, β₁ i) (∑ i ∈ Finset.range k, β₂ i) := sorry

/-! ### The one-sided output, $2 \le p < \infty$ -/

omit [DecidableEq m] [DecidableEq n] in
/-- **The head split of the one-sided error, $2 \le p < \infty$**: for an orthogonal projector
$\mathbf{P}$ and $L \le k$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{S_p} \le
\|\llbracket\mathbf{A}\rrbracket_L - \mathbf{P}\llbracket\mathbf{A}\rrbracket_L\|_{S_p} +
\Bigl(\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\sum_{L \le i < k} \bigl(\sigma_i(\mathbf{A})^p - \sigma_i(\mathbf{P}\mathbf{A})^p\bigr)
\Bigr)^{1/p}\,.$$
The head $\llbracket\mathbf{A}\rrbracket_L$ is split off by the triangle inequality, and the
rest is `IsStarProjection.schattenNorm_mul_rpow_add_le` for
$\mathbf{A} - \llbracket\mathbf{A}\rrbracket_L$ with Weyl's inequality for a perturbation of rank
at most $L$. [BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there for the two-sided output
with the pair-of-projectors inequality, here one-sided. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_add_rpow {p : ℝ≥0∞}
    (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P) (A : Matrix m n 𝕜)
    {L k : ℕ} (hLk : L ≤ k) :
    schattenNorm p (A - P * A) ≤
      schattenNorm p (truncatedSVD A L - P * truncatedSVD A L) +
        (schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
          ∑ i ∈ Finset.Ico L k,
            (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal)) ^
          p.toReal⁻¹ := by
  classical
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp2).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLk
  set E := A - truncatedSVD A L
  have hsplit : A - P * A = (truncatedSVD A L - P * truncatedSVD A L) + (E - P * E) := by
    simp only [E, Matrix.mul_sub]
    abel
  rw [hsplit]
  refine (schattenNorm_add_le (le_trans (by norm_num) hp2) _ _).trans (add_le_add le_rfl ?_)
  -- the tail `E` after one projector
  have hPN4 := hP.schattenNorm_mul_rpow_add_le hp2 hp E
  rw [Matrix.sub_mul, Matrix.one_mul] at hPN4
  have hE := schattenNorm_sub_truncatedSVD_rpow_eq_add_sum hp0 hp A hLk
  -- Weyl: `σ_{L+i}(PA) ≤ σ_i(PE)`, since `PA - PE` has rank at most `L`
  have hW (i : ℕ) : singularValues (P * A) (L + i) ≤ singularValues (P * E) i := by
    have hrk : (-(P * truncatedSVD A L)).rank ≤ L := by
      rw [Matrix.rank_neg]
      exact (Matrix.rank_mul_le_right _ _).trans (rank_truncatedSVD_le A L)
    have h := singularValues_le_singularValues_add_of_rank_le (P * A) hrk i
    rwa [← sub_eq_add_neg, ← Matrix.mul_sub, add_comm] at h
  have hPE : (P * E).rank ≤ Fintype.card n + d := by
    have := (P * E).rank_le_card_width
    omega
  have hsum : ∑ i ∈ Finset.Ico L (L + d), singularValues (P * A) i ^ p.toReal ≤
      schattenNorm p (P * E) ^ p.toReal := by
    rw [schattenNorm_rpow hp0 hp _ hPE, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
      add_comm, Finset.sum_range_add]
    refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i _ => ?_)
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg _ _) _)
    exact Real.rpow_le_rpow (singularValues_nonneg _ _) (hW i) hr.le
  have hX : schattenNorm p (E - P * E) ^ p.toReal ≤
      schattenNorm p (A - truncatedSVD A (L + d)) ^ p.toReal +
        ∑ i ∈ Finset.Ico L (L + d),
          (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal) := by
    rw [Finset.sum_sub_distrib]
    linarith
  calc schattenNorm p (E - P * E)
      = (schattenNorm p (E - P * E) ^ p.toReal) ^ p.toReal⁻¹ :=
        (Real.rpow_rpow_inv (schattenNorm_nonneg _ _) hr.ne').symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hX (inv_nonneg.mpr hr.le)

omit [DecidableEq m] [DecidableEq n] in
/-- Head capture from small head deficits: for an orthogonal projector $\mathbf{P}$,
$\delta, c \ge 0$ and $0 < \theta \le 1$, if there is a gap before $L$,
$\sigma_L^2 \le (1 - \theta)\,\sigma_h^2$ when $L = h + 1$, and the head deficits satisfy
$\sigma_i(\mathbf{A})^2 - \delta c^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$ for $i < L$, then
$$\|\llbracket\mathbf{A}\rrbracket_L - \mathbf{P}\llbracket\mathbf{A}\rrbracket_L
\|_{\mathsf{F}} \le \sqrt{\frac{L\delta}{\theta}}\;c\,.$$
`IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le` with the deficits summed. -/
theorem _root_.IsStarProjection.frobNorm_truncatedSVD_sub_mul_le_sqrt_mul {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) {L : ℕ} {δ θ c : ℝ} (hδ : 0 ≤ δ)
    (hc : 0 ≤ c) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : ∀ h, h + 1 = L → singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hhead : ∀ i < L, singularValues A i ^ 2 - δ * c ^ 2 ≤ singularValues (P * A) i ^ 2) :
    frobNorm (truncatedSVD A L - P * truncatedSVD A L) ≤ Real.sqrt (L * δ / θ) * c := by
  rcases Nat.eq_zero_or_eq_succ_pred L with hL | hL
  · subst hL
    rw [truncatedSVD_zero, Matrix.mul_zero, sub_zero, frobNorm_zero]
    positivity
  have h := hP.mul_frobNorm_truncatedSVD_sub_mul_sq_le A hL.symm hθ1 (hgap _ hL.symm)
  have hsum : ∑ i ∈ Finset.range L,
      (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) ≤ L * (δ * c ^ 2) := by
    have h' := Finset.sum_le_sum fun i (hi : i ∈ Finset.range L) =>
      (show singularValues A i ^ 2 - singularValues (P * A) i ^ 2 ≤ δ * c ^ 2 by
        linarith [hhead i (Finset.mem_range.mp hi)])
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h'
  refine (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), div_mul_eq_mul_div, le_div_iff₀ hθ]
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- The middle deficits in $p$-th powers, $p \ge 2$: if
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$ for
$L \le i < k$ and $\sigma_L \le \kappa\,\sigma_k$, then
$\sum_{L \le i < k} (\sigma_i^p - \sigma_i(\mathbf{P}\mathbf{A})^p) \le
(p/2)\,\kappa^{p-2}(k - L)\,\gamma\,\sigma_k^p$, termwise by `Real.rpow_sub_rpow_le_max_mul`. -/
private theorem sum_Ico_rpow_sub_rpow_le {p : ℝ} (hp2 : 2 ≤ p) {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {A : Matrix m n 𝕜} {L k : ℕ} (hLk : L ≤ k) {γ κ : ℝ}
    (hκ : 0 ≤ κ) (hflat : singularValues A L ≤ κ * singularValues A k)
    (hmid : ∀ i, L ≤ i → i < k → singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    ∑ i ∈ Finset.Ico L k, (singularValues A i ^ p - singularValues (P * A) i ^ p) ≤
      p / 2 * κ ^ (p - 2) * ((k : ℝ) - L) * γ * singularValues A k ^ p := by
  have hk0 := singularValues_nonneg A k
  have hσk : singularValues A k ^ (p - 2) * singularValues A k ^ 2 = singularValues A k ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_add' hk0 (by linarith), sub_add_cancel]
  have hterm (i : ℕ) (hi : i ∈ Finset.Ico L k) :
      singularValues A i ^ p - singularValues (P * A) i ^ p ≤
        p / 2 * κ ^ (p - 2) * γ * singularValues A k ^ p := by
    obtain ⟨hLi, hik⟩ := Finset.mem_Ico.mp hi
    have hi0 := singularValues_nonneg A i
    have hPi : singularValues (P * A) i ≤ singularValues A i := hP.singularValues_mul_le A i
    have h := Real.rpow_sub_rpow_le_max_mul_sq (singularValues_nonneg _ _) hPi
      (show 0 < p by linarith)
    rw [max_eq_right (by linarith)] at h
    -- `σ_i^(p-2) ≤ κ^(p-2) σ_k^(p-2)`, since `σ_i ≤ σ_L ≤ κ σ_k`
    have hpow : singularValues A i ^ (p - 2) ≤ κ ^ (p - 2) * singularValues A k ^ (p - 2) := by
      rw [← Real.mul_rpow hκ hk0]
      exact Real.rpow_le_rpow hi0 ((singularValues_antitone A hLi).trans hflat) (by linarith)
    have hd : singularValues A i ^ 2 - singularValues (P * A) i ^ 2 ≤
        γ * singularValues A k ^ 2 := by linarith [hmid i hLi hik]
    calc singularValues A i ^ p - singularValues (P * A) i ^ p
        ≤ p / 2 * singularValues A i ^ (p - 2) *
          (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := h
      _ ≤ p / 2 * (κ ^ (p - 2) * singularValues A k ^ (p - 2)) * (γ * singularValues A k ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (by linarith)) hd
            (sub_nonneg.mpr (pow_le_pow_left₀ (singularValues_nonneg _ _) hPi 2))
            (mul_nonneg (by linarith) (by positivity))
      _ = p / 2 * κ ^ (p - 2) * γ * singularValues A k ^ p := by rw [← hσk]; ring
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hLk]
  ring

omit [DecidableEq m] [DecidableEq n] in
/-- **The head split with deficits, $2 \le p < \infty$**: let $\mathbf{P}$ be an orthogonal
projector, $L \le k$, $\delta \ge 0$, $0 < \theta \le 1$ and $\kappa \ge 1$. Suppose
there is a gap before $L$, $\sigma_L^2 \le (1 - \theta)\,\sigma_h^2$ when $L = h + 1$; the
spectrum is flat from $L$ to $k$, $\sigma_L \le \kappa\,\sigma_k$; the head deficits satisfy
$\sigma_i(\mathbf{A})^2 - \delta\,\sigma_k(\mathbf{A})^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$
for $i < L$; and the others satisfy
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$
for $L \le i < k$. Then
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{S_p} \le
\sqrt{\frac{L\delta}{\theta}}\;\sigma_k(\mathbf{A}) +
\Bigl(\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p +
\frac{p}{2}\,\kappa^{p-2}(k - L)\,\gamma\,\sigma_k(\mathbf{A})^p\Bigr)^{1/p}\,.$$
The first term is the head capture
`IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le`, the Schatten norm bounded by the
Frobenius norm. [BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there the case of large
singular values, with accuracies that are unspecified polynomials in $\varepsilon/d$, here with
explicit $\delta$, $\gamma$, $\theta$, $\kappa$. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_of_sq_singularValues_sub_le
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {A : Matrix m n 𝕜} {L k : ℕ} (hLk : L ≤ k) {δ γ θ κ : ℝ} (hδ : 0 ≤ δ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hκ : 1 ≤ κ)
    (hgap : ∀ h, h + 1 = L → singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hflat : singularValues A L ≤ κ * singularValues A k)
    (hhead : ∀ i < L, singularValues A i ^ 2 - δ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2)
    (hmid : ∀ i, L ≤ i → i < k → singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - P * A) ≤
      Real.sqrt (L * δ / θ) * singularValues A k +
        (schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
          p.toReal / 2 * κ ^ (p.toReal - 2) * ((k : ℝ) - L) * γ *
            singularValues A k ^ p.toReal) ^ p.toReal⁻¹ := by
  have hr2 : 2 ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  refine (hP.schattenNorm_sub_mul_le_add_rpow hp2 hp A hLk).trans (add_le_add ?_ ?_)
  · -- the head: the Schatten norm is at most the Frobenius norm
    refine ((schattenNorm_anti two_ne_zero hp2 _).trans_eq (schattenNorm_two _)).trans ?_
    exact hP.frobNorm_truncatedSVD_sub_mul_le_sqrt_mul A hδ (singularValues_nonneg A k) hθ hθ1
      hgap hhead
  · -- the middle deficits
    have hS : 0 ≤ ∑ i ∈ Finset.Ico L k,
        (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal) :=
      Finset.sum_nonneg fun i _ => sub_nonneg.mpr (Real.rpow_le_rpow (singularValues_nonneg _ _)
        (hP.singularValues_mul_le A i) (by linarith))
    refine Real.rpow_le_rpow (by positivity) (add_le_add le_rfl ?_)
      (inv_nonneg.mpr (by linarith))
    exact sum_Ico_rpow_sub_rpow_le hr2 hP hLk (by linarith) hflat hmid

omit [DecidableEq m] [DecidableEq n] in
/-- The head index of `NLAlib.exists_le_singularValues_le_and_gap` with its gap parameter: for
$p \ge 1$ and $\delta \ge 0$ there are $L \le k$ and $0 < \theta \le 1$ with
$\sigma_L \le (1 + 1/p)\,\sigma_k$, the gap $\sigma_L^2 \le (1 - \theta)\,\sigma_h^2$ when
$L = h + 1$, $(1 + 1/(2p))\,\sigma_k < \sigma_i$ for $i < L$, and
$\sqrt{L\delta/\theta} \le k\sqrt{2(p + 1)\delta}$: $\theta = 1/(2k(p + 1))$ if $L > 0$ and
$\theta = 1$ if $L = 0$. -/
private theorem exists_head_index_sqrt_le (A : Matrix m n 𝕜) (k : ℕ) {p δ : ℝ} (hp : 1 ≤ p)
    (hδ : 0 ≤ δ) :
    ∃ L ≤ k, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      singularValues A L ≤ (1 + 1 / p) * singularValues A k ∧
      (∀ h, h + 1 = L → singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2) ∧
      (∀ i < L, (1 + 1 / (2 * p)) * singularValues A k < singularValues A i) ∧
      Real.sqrt (L * δ / θ) ≤ k * Real.sqrt (2 * (p + 1) * δ) := by
  obtain ⟨L, hLk, hflat, hgap⟩ := exists_le_singularValues_le_and_gap A k hp
  rcases Nat.eq_zero_or_eq_succ_pred L with hL | hL
  · subst hL
    refine ⟨0, hLk, 1, one_pos, le_rfl, hflat, fun h hh => absurd hh (Nat.succ_ne_zero h),
      fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    rw [Nat.cast_zero, zero_mul, zero_div, Real.sqrt_zero]
    positivity
  set h := L.pred
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (by omega)
  have hX : 0 < 2 * (k : ℝ) * (p + 1) := by positivity
  refine ⟨L, hLk, 1 / (2 * k * (p + 1)), by positivity, ?_, hflat,
    fun h' hh => (hgap h' hh).2, fun i hi => ?_, ?_⟩
  · rw [div_le_one hX]; nlinarith
  · exact (hgap h hL.symm).1.trans_le (singularValues_antitone A (by omega))
  · have hLk' : (L : ℝ) ≤ k := Nat.cast_le.mpr hLk
    rw [show (k : ℝ) * Real.sqrt (2 * (p + 1) * δ) = Real.sqrt (k ^ 2 * (2 * (p + 1) * δ)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]]
    refine Real.sqrt_le_sqrt ?_
    rw [div_div_eq_mul_div, div_one]
    have : 0 ≤ ((k : ℝ) - L) * k * (2 * (p + 1) * δ) :=
      mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg k)) (by positivity)
    nlinarith

/-- The middle deficits against the tail count: for $p \ge 2$, $L \le k$, $\gamma, s \ge 0$
and $s \le \kappa^p/(j + 1)\cdot O$,
$$\frac{p}{2}\Bigl(1 + \frac1p\Bigr)^{p-2}(k - L)\,\gamma\,s \le
\frac{e\,p\,k\gamma\kappa^p}{2(j + 1)}\,O\,,$$
with $(1 + 1/p)^{p-2} \le (1 + 1/p)^p \le e$. -/
private theorem mul_rpow_mul_le_exp_mul {p κ γ s O : ℝ} {k L j : ℕ} (hp : 2 ≤ p) (hLk : L ≤ k)
    (hγ : 0 ≤ γ) (hs0 : 0 ≤ s) (hs : s ≤ κ ^ p / ((j : ℝ) + 1) * O) :
    p / 2 * (1 + 1 / p) ^ (p - 2) * ((k : ℝ) - L) * γ * s ≤
      Real.exp 1 * (p / 2) * k * γ * κ ^ p / ((j : ℝ) + 1) * O := by
  have hp0 : 0 < p := by linarith
  have h1 : 1 ≤ 1 + 1 / p := le_add_of_nonneg_right (by positivity)
  have he : (1 + 1 / p) ^ (p - 2) ≤ Real.exp 1 :=
    (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)).trans
      (Real.one_add_one_div_rpow_le_exp_one hp0)
  have hLk' : (L : ℝ) ≤ k := Nat.cast_le.mpr hLk
  calc p / 2 * (1 + 1 / p) ^ (p - 2) * ((k : ℝ) - L) * γ * s
      ≤ p / 2 * Real.exp 1 * k * γ * s := by
        have : 0 ≤ (k : ℝ) - L := by linarith
        gcongr
        linarith
    _ ≤ p / 2 * Real.exp 1 * k * γ * (κ ^ p / ((j : ℝ) + 1) * O) := by gcongr
    _ = _ := by ring

omit [DecidableEq m] [DecidableEq n] in
/-- **The tail-count form of the one-sided error, $2 \le p < \infty$**: let $\mathbf{P}$ be an
orthogonal projector and $\delta, \gamma, \kappa \ge 0$. Suppose the tail is flat,
$\sigma_k \le \kappa\,\sigma_{k+j}$; every $i < k$ has the deficit
$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$;
and every large singular value, $i < k$ with $(1 + 1/(2p))\,\sigma_k < \sigma_i$, has the
smaller deficit
$\sigma_i(\mathbf{A})^2 - \delta\,\sigma_k(\mathbf{A})^2 \le \sigma_i(\mathbf{P}\mathbf{A})^2$.
Then
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{S_p} \le
\Bigl(k\sqrt{2(p + 1)\delta} +
\Bigl(1 + \frac{e\,p\,k\gamma\kappa^p}{2(j + 1)}\Bigr)^{1/p}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}\,.$$
The head index is chosen by `NLAlib.exists_le_singularValues_le_and_gap`; the factor $e$ bounds
$(1 + 1/p)^p$. [BakshiClarksonWoodruff2022, proof of Theorem 3.1]; there with a head index that
need not exist and unspecified accuracies, for the two-sided output; here one-sided, with
explicit constants. -/
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_mul_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {A : Matrix m n 𝕜} {k j : ℕ} {δ γ κ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hhead : ∀ i < k, (1 + 1 / (2 * p.toReal)) * singularValues A k < singularValues A i →
      singularValues A i ^ 2 - δ * singularValues A k ^ 2 ≤ singularValues (P * A) i ^ 2)
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - P * A) ≤
      (k * Real.sqrt (2 * (p.toReal + 1) * δ) +
        (1 + Real.exp 1 * (p.toReal / 2) * k * γ * κ ^ p.toReal / ((j : ℝ) + 1)) ^ p.toReal⁻¹) *
        schattenNorm p (A - truncatedSVD A k) := by
  have hr2 : 2 ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  have hr : 0 < p.toReal := by linarith
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp2).ne'
  set O := schattenNorm p (A - truncatedSVD A k)
  have hO : 0 ≤ O := schattenNorm_nonneg _ _
  have hk0 := singularValues_nonneg A k
  -- the tail count: `σ_k ≤ OPT` and `σ_k^p ≤ κ^p/(j + 1) OPT^p`
  have hσO : singularValues A k ≤ O := by
    have h := mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow hp0 hp A k 0
    rw [Nat.cast_zero, zero_add, one_mul, add_zero] at h
    exact (Real.rpow_le_rpow_iff hk0 hO hr).mp h
  have hσr : singularValues A k ^ p.toReal ≤ κ ^ p.toReal / ((j : ℝ) + 1) * O ^ p.toReal := by
    have h := mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow hp0 hp A k j
    have hj : (0 : ℝ) < j + 1 := by positivity
    calc singularValues A k ^ p.toReal ≤ κ ^ p.toReal * singularValues A (k + j) ^ p.toReal := by
          rw [← Real.mul_rpow hκ (singularValues_nonneg _ _)]
          exact Real.rpow_le_rpow hk0 htail hr.le
      _ ≤ κ ^ p.toReal * (O ^ p.toReal / ((j : ℝ) + 1)) := by
          gcongr
          rw [le_div_iff₀ hj, mul_comm]
          exact h
      _ = _ := by ring
  -- the head index, with the flatness `1 + 1/p` of `NLAlib.exists_le_singularValues_le_and_gap`
  obtain ⟨L, hLk, θ, hθ, hθ1, hflat, hgap, hbig, hsqrt⟩ :=
    exists_head_index_sqrt_le A k (show 1 ≤ p.toReal by linarith) hδ
  have h := hP.schattenNorm_sub_mul_le_of_sq_singularValues_sub_le hp2 hp hLk hδ hθ hθ1
    (le_add_of_nonneg_right (by positivity)) hgap hflat
    (fun i hi => hhead i (hi.trans_le hLk) (hbig i hi)) (fun i _ hik => hritz i hik)
  refine h.trans ?_
  rw [add_mul]
  refine add_le_add (mul_le_mul hsqrt hσO hk0 (by positivity)) ?_
  -- the middle deficits, paid for by the tail count
  have hM := mul_rpow_mul_le_exp_mul hr2 hLk hγ (Real.rpow_nonneg hk0 _) hσr
  set c := Real.exp 1 * (p.toReal / 2) * k * γ * κ ^ p.toReal / ((j : ℝ) + 1)
  have hc : 0 ≤ c := by positivity
  have hLk' : (L : ℝ) ≤ k := Nat.cast_le.mpr hLk
  calc (O ^ p.toReal + p.toReal / 2 * (1 + 1 / p.toReal) ^ (p.toReal - 2) * ((k : ℝ) - L) * γ *
          singularValues A k ^ p.toReal) ^ p.toReal⁻¹
      ≤ ((1 + c) * O ^ p.toReal) ^ p.toReal⁻¹ := by
        refine Real.rpow_le_rpow ?_ (by linarith) (inv_nonneg.mpr hr.le)
        have : 0 ≤ (k : ℝ) - L := by linarith
        positivity
    _ = (1 + c) ^ p.toReal⁻¹ * O := by
        rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hO _), Real.rpow_rpow_inv hO hr.ne']

end NLAlib
