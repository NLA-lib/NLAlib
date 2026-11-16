/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Matrix.Structured.BoundedOrthonormal
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.Probability.SubGaussianVector.Norm
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Matrix.Subspaces.Leverage

/-!
# Flattening by a randomized unitary transform

Let $\mathbf{F}$ be a bounded orthonormal transform with constant $\beta$
(`NLAlib.IsBoundedOrthonormal F β`: unitary, $\lvert n \rvert \, \lvert \mathbf{F}_{i,j} \rvert^2
\le \beta$) and $\mathbf{D} = \operatorname{diag}(\boldsymbol{\xi})$ a diagonal of independent
random signs. For every $\mathbf{U}$ of rank $d$, the leverage scores of $\mathbf{F}\mathbf{D}
\mathbf{U}$ are all at most
$$\frac{\beta\,(d + 2\sqrt{d t} + 2t)}{\lvert n \rvert}$$
outside probability $\lvert n \rvert e^{-t}$: the randomized transform makes every subspace
incoherent (**flattening**). Row $i$ of $\mathbf{F}\mathbf{D}\mathbf{Q}$, for an orthonormal basis
$\mathbf{Q}$ of $\operatorname{range}\mathbf{U}$, is the image of the sign vector under a matrix
$\mathbf{M}_i$ with $\|\mathbf{M}_i\|_{\mathsf{F}}^2 \le \beta d / \lvert n \rvert$ and
$\|\mathbf{M}_i\|_2^2 \le \beta / \lvert n \rvert$, so the Hsu–Kakade–Zhang tail
(`NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le`) bounds it, over any `RCLike` field
with
the real constant. At $t = \log(\lvert n \rvert/\delta)$, outside probability $\delta$ the leverage
scores are at most <!-- value srhtRowBound {\lvert n \rvert} d \delta -->
$$\frac{\beta\,\bigl(d + 2\sqrt{d \log(\lvert n \rvert/\delta)} +
2 \log(\lvert n \rvert/\delta)\bigr)}{\lvert n \rvert}\,,$$
whose numerator is the threshold `NLAlib.srhtRowBound`. The same argument bounds the rows of
$\mathbf{F}\mathbf{D}\mathbf{A}$ for a general $\mathbf{A}$: outside probability
$\lvert n\rvert e^{-t}$ every squared row norm is at most $\beta$ times the flattened row-norm
bound <!-- value srhtRowNormBound \mathbf{A} t -->
$$\|\mathbf{A}\|_{\mathsf{F}}^2 + 2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{t} +
2\|\mathbf{A}\|_2^2 t$$
over $\lvert n\rvert$ (`NLAlib.srhtRowNormBound`), the input of the SRHT's spectral approximate
multiplication.

The second half is generic: a sampler that injects (or embeds) every fixed subspace whose
leverage scores are at most $L / \lvert n \rvert$, composed with an independent random unitary
$\mathbf{T}$ that makes $\mathbf{T}\mathbf{U}$ so incoherent outside probability $\delta_2$,
injects (or embeds) $\operatorname{range}\mathbf{U}$ outside probability $\delta_1 + \delta_2$
(**flatten, then sample**). The subsampled randomized trigonometric transforms of
`NLAlib.Sketching.Structured.SRHT` instantiate it with uniform row sampling; rerandomized
transforms and sparse samplers are other instances.

Degenerate cases. Rank zero: every leverage score is $0$ and the flattening event is empty. Empty
`n`: every event is empty. For nonempty `n`, $\beta \ge 1$. The signs are $\pm 1$ only almost
surely, so $\mathbf{F}\mathbf{D}$ is unitary only almost surely. The transfer takes
$0 \le \delta_1$: with $L < 0$ its sampling hypothesis is vacuous.

## Main definitions

* `NLAlib.srhtRowBound`: the flattening threshold at failure probability $\delta$,
  the value <!-- value srhtRowBound n d \delta -->
  $d + 2\sqrt{d \log(n/\delta)} + 2 \log(n/\delta)$ for dimension $d$ and $n$ rows.
* `NLAlib.srhtRowNormBound`: the flattened row-norm bound of a general matrix,
  the value <!-- value srhtRowNormBound \mathbf{A} t -->
  $$\|\mathbf{A}\|_{\mathsf{F}}^2 + 2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{t} +
  2\|\mathbf{A}\|_2^2 t\,.$$

## Main results

* `NLAlib.HasOrthonormalCols.ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector`:
  $\mathbf{F}\mathbf{D}$ is unitary almost surely.
* `NLAlib.measureReal_exists_leverageScore_mul_diagonal_gt_le_of_hasLaw_rademacherVector`:
  flattening; its $\delta$ form, in namespace `NLAlib`,
  `measureReal_exists_leverageScore_mul_diagonal_gt_srhtRowBound_le_of_hasLaw_rademacherVector`.
* `NLAlib.srhtRowBound_nonneg`, `NLAlib.srhtRowBound_mono`, `NLAlib.srhtRowBound_le`,
  `NLAlib.srhtRowBound_div_two_le`: the API of the threshold.
* `NLAlib.measureReal_exists_norm_mul_diagonal_mul_apply_sq_gt_le_of_hasLaw_rademacherVector`:
  flattening of the rows of a general matrix.
* `NLAlib.hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le`,
  `NLAlib.hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le`: flatten, then sample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal

namespace NLAlib

/-! ### The row bound -/

/-- The **SRHT row bound** <!-- value srhtRowBound n d \delta -->
$d + 2\sqrt{d \log(n/\delta)} + 2 \log(n/\delta)$: flattening with
failure probability $\delta$ makes every leverage score at most $\beta$ times this over $n$
(`measureReal_exists_leverageScore_mul_diagonal_gt_srhtRowBound_le_of_hasLaw_rademacherVector`).
The value the proof reaches, at $t = \log(n/\delta)$ in the Hsu–Kakade–Zhang tail. Tropp 2011a has
$(\sqrt{d} + \sqrt{8 \log(n/\delta)})^2$ ([Tropp2011a, Lemma 3.3], Walsh–Hadamard, failure
probability $\delta$; the $8$ is as in [HalkoMartinssonTropp2011, Theorem 11.1],
$[\sqrt{k} + \sqrt{8 \log(kn)}]^2$), which is
larger (`NLAlib.srhtRowBound_le`). Consumers use the API. Junk values: for $\delta > n$ the
logarithm is negative, the square root is $0$, and the value may be below $d$; the flattening tail
is then trivial. -/
noncomputable irreducible_def srhtRowBound (n d : ℕ) (δ : ℝ) : ℝ :=
  d + 2 * √(d * Real.log (n / δ)) + 2 * Real.log (n / δ)

/-- The SRHT row bound is nonnegative in its nontrivial range $0 < \delta \le n$. -/
theorem srhtRowBound_nonneg {n d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδn : δ ≤ n) :
    0 ≤ srhtRowBound n d δ := by
  rw [srhtRowBound_def]
  have : 0 ≤ Real.log (n / δ) := Real.log_nonneg ((one_le_div hδ).2 hδn)
  positivity

/-- The SRHT row bound is monotone in the dimensions $n \ge 1$ and $d$ and antitone in the
failure probability $\delta > 0$. -/
theorem srhtRowBound_mono {n n' d d' : ℕ} {δ δ' : ℝ} (hn : 0 < n) (hnn' : n ≤ n') (hd : d ≤ d')
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') : srhtRowBound n d δ' ≤ srhtRowBound n' d' δ := by
  rw [srhtRowBound_def, srhtRowBound_def]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hℓ : Real.log (n / δ') ≤ Real.log (n' / δ) :=
    Real.log_le_log (div_pos hn0 (hδ.trans_le hδδ'))
      (div_le_div₀ (Nat.cast_nonneg _) (Nat.cast_le.2 hnn') hδ hδδ')
  have hdd : (d : ℝ) ≤ d' := Nat.cast_le.2 hd
  have hsq : √(d * Real.log (n / δ')) ≤ √(d' * Real.log (n' / δ)) := by
    rcases le_or_gt (Real.log (n / δ')) 0 with h | h
    · rw [Real.sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h)]
      exact Real.sqrt_nonneg _
    · exact Real.sqrt_le_sqrt (mul_le_mul hdd hℓ h.le (Nat.cast_nonneg _))
  linarith

/-- The explicit comparison consumers invert with:
$\mathrm{srhtRowBound}(n, d, \delta) \le (\sqrt{d} + \sqrt{2 \log(n/\delta)})^2$, Tropp's form
with $2$ in place of $8$. No hypothesis: in the junk range $\log(n/\delta) < 0$ the left side is
$d + 2\log(n/\delta) < d$ and the right side is $d$. -/
theorem srhtRowBound_le (n d : ℕ) (δ : ℝ) :
    srhtRowBound n d δ ≤ (√(d : ℝ) + √(2 * Real.log (n / δ))) ^ 2 := by
  rw [srhtRowBound_def]
  have hd := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  rcases le_or_gt (Real.log (n / δ)) 0 with h | h
  · rw [Real.sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h),
      Real.sqrt_eq_zero'.2 (by linarith : 2 * Real.log (n / δ) ≤ 0)]
    nlinarith
  · have h1 : √(d * Real.log (n / δ)) ≤ √(d : ℝ) * √(2 * Real.log (n / δ)) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
      exact Real.sqrt_le_sqrt (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
    have h2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * Real.log (n / δ))
    nlinarith

/-- The row bound at half the failure probability, against the size of its logarithm: for
$n \ge 1$ and $0 < \delta \le 1/2$, <!-- value srhtRowBound n d (\delta/2) -->
$$d + 2\sqrt{d \log(n/(\delta/2))} + 2 \log(n/(\delta/2)) \le
8\bigl(d + \log(n/\delta)\bigr).$$
The step from the SRHT sample sizes, which flatten with probability $\delta/2$, to their
asymptotic forms. -/
theorem srhtRowBound_div_two_le {n : ℕ} (hn : 0 < n) (d : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) : srhtRowBound n d (δ / 2) ≤ 8 * (d + Real.log (n / δ)) := by
  have hN : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
  have h2N : Real.log 2 ≤ Real.log (n / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlN : Real.log (n / (δ / 2)) = Real.log 2 + Real.log (n / δ) := by
    rw [show (n : ℝ) / (δ / 2) = 2 * (n / δ) by ring, Real.log_mul (by norm_num) (by positivity)]
  have h := srhtRowBound_le n d (δ / 2)
  have ha := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  have hb := Real.sq_sqrt (by linarith : 0 ≤ 2 * Real.log (n / (δ / 2)))
  nlinarith [sq_nonneg (√(d : ℝ) - √(2 * Real.log (n / (δ / 2))))]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n r : Type*} [Fintype k] [Fintype n] [Fintype r] [DecidableEq n]
  {F : Matrix n n 𝕜} {ξ : Ω → n → ℝ} {β L a b t δ δ₁ δ₂ : ℝ}

/-! ### Flattening -/

/-- A unitary times a diagonal of random signs is unitary almost surely:
$(\mathbf{F}\mathbf{D})^{\mathsf{H}}\mathbf{F}\mathbf{D} = \mathbf{D}^2 = \mathbf{I}$ on the event
that every sign squares to $1$. -/
theorem HasOrthonormalCols.ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector
    (hF : HasOrthonormalCols F)
    (hξ : HasLaw ξ (rademacherVector n) μ) :
    ∀ᵐ ω ∂μ, HasOrthonormalCols (F * Matrix.diagonal fun i => (ξ ω i : 𝕜)) := by
  filter_upwards [ae_sq_eq_one_of_hasLaw_rademacherVector hξ] with ω hω
  exact hF.hasOrthonormalCols_mul_diagonal hω

/-- Row $i$ of $\mathbf{F}\operatorname{diag}(\boldsymbol{\xi})\mathbf{Q}$ is the image of the
sign vector under
$\mathbf{M}_i = \mathbf{Q}^{\mathsf{T}} \operatorname{diag}(\mathbf{F}_{i,\cdot})$. -/
private theorem mul_diagonal_mul_apply {q : Type*} (Q : Matrix n q 𝕜) (v : n → ℝ)
    (i : n) :
    (F * Matrix.diagonal (fun l => (v l : 𝕜)) * Q) i =
      (Qᵀ * Matrix.diagonal (F i)) *ᵥ fun l => (v l : 𝕜) := by
  funext j
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The row matrix $\mathbf{M}_i$ has $\|\mathbf{M}_i\|_{\mathsf{F}}^2 \le \beta \lvert q \rvert /
\lvert n \rvert$ and $\|\mathbf{M}_i\|_2^2 \le \beta / \lvert n \rvert$. -/
private theorem frobNorm_sq_le_and_specNorm_sq_le (hF : IsBoundedOrthonormal F β) [Nonempty n]
    {q : Type*} [Fintype q] [DecidableEq q] {Q : Matrix n q 𝕜} (hQ : HasOrthonormalCols Q) (i : n) :
    frobNorm (Qᵀ * Matrix.diagonal (F i)) ^ 2 ≤ β * (Fintype.card n : ℝ)⁻¹ * Fintype.card q ∧
      specNorm (Qᵀ * Matrix.diagonal (F i)) ^ 2 ≤ β * (Fintype.card n : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  have hFi : ∀ l, ‖F i l‖ ^ 2 ≤ β * (Fintype.card n : ℝ)⁻¹ := fun l => by
    rw [← div_eq_mul_inv, le_div_iff₀ hn, mul_comm]
    exact hF.card_mul_norm_sq_le i l
  have hK : 0 ≤ β * (Fintype.card n : ℝ)⁻¹ :=
    (sq_nonneg _).trans (hFi (Classical.arbitrary n))
  refine ⟨?_, ?_⟩
  · rw [← frobNorm_transpose, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.transpose_transpose, ← hQ.frobNorm_sq, frobNorm_sq_eq_sum, frobNorm_sq_eq_sum,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.diagonal_mul, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (hFi l) (sq_nonneg _)
  · have h1 : specNorm (Matrix.diagonal (F i)) ≤ √(β * (Fintype.card n : ℝ)⁻¹) :=
      specNorm_diagonal_le (Real.sqrt_nonneg _) fun l => Real.le_sqrt_of_sq_le (hFi l)
    have h2 : specNorm (Qᵀ * Matrix.diagonal (F i)) ≤ √(β * (Fintype.card n : ℝ)⁻¹) := by
      refine (specNorm_mul_le _ _).trans ?_
      rw [specNorm_transpose]
      calc specNorm Q * specNorm (Matrix.diagonal (F i)) ≤ 1 * √(β * (Fintype.card n : ℝ)⁻¹) :=
            mul_le_mul hQ.specNorm_le_one h1 (specNorm_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc specNorm (Qᵀ * Matrix.diagonal (F i)) ^ 2 ≤ √(β * (Fintype.card n : ℝ)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (specNorm_nonneg _) h2 2
      _ = _ := Real.sq_sqrt hK

/-- The tail of one row: the Hsu–Kakade–Zhang tail at $\mathbf{M}_i$, proxy $1$. -/
private theorem measureReal_not_norm_row_sq_le (hF : IsBoundedOrthonormal F β)
    (hξ : HasLaw ξ (rademacherVector n) μ) {q : Type*} [Fintype q] [DecidableEq q]
    {Q : Matrix n q 𝕜} (hQ : HasOrthonormalCols Q) (ht : 0 ≤ t) (i : n) :
    μ.real {ω | ¬ ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * Q) i)‖ ^ 2 ≤
      β * (Fintype.card q + 2 * √(Fintype.card q * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹} ≤
      Real.exp (-t) := by
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure_iff.2 inferInstance
  have : Nonempty n := ⟨i⟩
  obtain ⟨hFr, hSp⟩ := frobNorm_sq_le_and_specNorm_sq_le hF hQ i
  set M := Qᵀ * Matrix.diagonal (F i) with hM_def
  set K := β * (Fintype.card n : ℝ)⁻¹ with hK_def
  set d : ℝ := (Fintype.card q : ℝ) with hd_def
  have hK : 0 ≤ K := (sq_nonneg _).trans hSp
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hthr : β * (d + 2 * √(d * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹ =
      K * (d + 2 * √d * √t + 2 * t) := by
    rw [Real.sqrt_mul hd, hK_def]
    ring
  simp only [mul_diagonal_mul_apply Q, hthr]
  by_cases hM : M = 0
  · have hset : {ω | ¬ ‖WithLp.toLp 2 (M *ᵥ fun l => (ξ ω l : 𝕜))‖ ^ 2 ≤
        K * (d + 2 * √d * √t + 2 * t)} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => hω ?_
      rw [hM, Matrix.zero_mulVec, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero]
      positivity
    rw [hset, measureReal_empty]
    positivity
  have hS : specNorm M ≤ √K := Real.le_sqrt_of_sq_le hSp
  have hFr' : frobNorm M ≤ √K * √d := by
    rw [← Real.sqrt_mul hK]
    exact Real.le_sqrt_of_sq_le hFr
  have hG : frobNorm (Mᴴ * M) ≤ K * √d := by
    refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
    rw [specNorm_conjTranspose]
    calc specNorm M * frobNorm M ≤ √K * (√K * √d) :=
          mul_le_mul hS hFr' (frobNorm_nonneg _) (Real.sqrt_nonneg _)
      _ = K * √d := by rw [← mul_assoc, Real.mul_self_sqrt hK]
  have key := (isSubgaussianVector_of_hasLaw_rademacherVector hξ).measureReal_norm_mulVec_sq_ge_le
    one_ne_zero hM ht (𝕜 := 𝕜)
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) key
  simp only [Set.mem_ofPred_eq, not_le, NNReal.coe_one, one_mul] at hω ⊢
  refine le_trans ?_ hω.le
  have h1 := mul_le_mul_of_nonneg_right hG (Real.sqrt_nonneg t)
  have h2 := mul_le_mul_of_nonneg_right hSp ht
  nlinarith

/-- **Flattening**: a randomized unitary transform makes every subspace incoherent. For a bounded
orthonormal $\mathbf{F}$ with constant $\beta$, independent signs $\boldsymbol{\xi}$,
$\mathbf{D} = \operatorname{diag}(\boldsymbol{\xi})$, any $\mathbf{U}$ with
$d = \operatorname{rank}\mathbf{U}$ and $t \ge 0$, outside probability $\lvert n \rvert e^{-t}$
every leverage score satisfies
$$\ell_i(\mathbf{F}\mathbf{D}\mathbf{U}) \le \frac{\beta\,(d + 2\sqrt{d t} + 2t)}{\lvert n \rvert}
\,.$$
[CamanoEpperlyMeyerTropp2025, Imported Theorem 4.3] (there $O((d + \log(n/\delta))/n)$ for a
unitary Walsh–Hadamard, cosine or Fourier transform with entries $O(n^{-1/2})$; they note the
argument needs only these two features); [Tropp2011a, Lemma 3.3] (real signs, Walsh–Hadamard,
orthonormal $\mathbf{U}$; $(\sqrt{d} + \sqrt{8 \log(n/\delta)})^2 / n$ outside probability
$\delta$). Here any
$\mathbf{F}$ with $n \lvert \mathbf{F}_{i,j} \rvert^2 \le \beta$, any field, any $\mathbf{U}$, the
Hsu–Kakade–Zhang constant.
The proof passes to an orthonormal basis $\mathbf{Q}$ of $\operatorname{range}\mathbf{U}$
(`NLAlib.leverageScore_eq_of_range_eq`); almost surely $\mathbf{F}\mathbf{D}\mathbf{Q}$ is
orthonormal and score $i$ is $\|(\mathbf{F}\mathbf{D}\mathbf{Q})_i\|^2 =
\|\mathbf{M}_i \boldsymbol{\xi}\|^2$ with $\mathbf{M}_i = \mathbf{Q}^{\mathsf{T}}
\operatorname{diag}(\mathbf{F}_{i,\cdot})$,
$\|\mathbf{M}_i\|_{\mathsf{F}}^2 \le \beta d / \lvert n \rvert$ and
$\|\mathbf{M}_i\|_2^2 \le \beta / \lvert n \rvert$; the Hsu–Kakade–Zhang tail at proxy $1$ per
row, then a union over the rows.
Result: srht-flattening -/
theorem measureReal_exists_leverageScore_mul_diagonal_gt_le_of_hasLaw_rademacherVector
    (hF : IsBoundedOrthonormal F β) (hξ : HasLaw ξ (rademacherVector n) μ) (U : Matrix n r 𝕜)
    (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹ <
        leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i} ≤
      Fintype.card n * Real.exp (-t) := by
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure_iff.2 inferInstance
  obtain ⟨Q, hQ, hQU⟩ := exists_hasOrthonormalCols_range_eq (p := Fin U.rank) U
    (Fintype.card_fin _)
  have hae := HasOrthonormalCols.ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector
    hF.hasOrthonormalCols hξ
  have hrow := fun i => measureReal_not_norm_row_sq_le hF hξ hQ ht i
  simp only [Fintype.card_fin] at hrow
  have hsub : {ω | ∃ i, β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹ <
        leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i} ≤ᵐ[μ]
      ⋃ i, {ω | ¬ ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * Q) i)‖ ^ 2 ≤
        β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹} := by
    filter_upwards [hae] with ω hω hex
    obtain ⟨i, hi⟩ := hex
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rw [leverageScore_eq_of_range_eq (range_mul_eq_of_range_eq _ hQU).symm,
      (hω.mul hQ).leverageScore_eq i] at hi
    exact not_le.2 hi
  calc _ ≤ μ.real (⋃ i, {ω | ¬ ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * Q)
          i)‖ ^ 2 ≤ β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹}) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ ∑ i, μ.real {ω | ¬ ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * Q)
          i)‖ ^ 2 ≤ β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : n, Real.exp (-t) := Finset.sum_le_sum fun i _ => hrow i
    _ = Fintype.card n * Real.exp (-t) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Flattening in $\delta$ form: for a bounded orthonormal $\mathbf{F}$ with constant $\beta$,
independent signs and $\delta > 0$, outside probability $\delta$ every leverage score of
$\mathbf{F}\mathbf{D}\mathbf{U}$ is at most <!-- value srhtRowBound {\lvert n \rvert} r \delta -->
$$\frac{\beta\,\bigl(r + 2\sqrt{r \log(\lvert n \rvert/\delta)} +
2 \log(\lvert n \rvert/\delta)\bigr)}{\lvert n \rvert}$$
with $r = \operatorname{rank}\mathbf{U}$; the numerator is `NLAlib.srhtRowBound`.
The flattening tail at $t = \log(n/\delta)$ for $\delta \le n$, where $n e^{-t} = \delta$; for
$\delta > n \ge 1$ the bound exceeds $1$, and empty `n` has an empty event. -/
theorem measureReal_exists_leverageScore_mul_diagonal_gt_srhtRowBound_le_of_hasLaw_rademacherVector
    (hF : IsBoundedOrthonormal F β) (hξ : HasLaw ξ (rademacherVector n) μ) (U : Matrix n r 𝕜)
    (hδ : 0 < δ) :
    μ.real {ω | ∃ i, β * srhtRowBound (Fintype.card n) U.rank δ * (Fintype.card n : ℝ)⁻¹ <
        leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i} ≤ δ := by
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure_iff.2 inferInstance
  rcases isEmpty_or_nonempty n with hn | hn
  · have h : {ω | ∃ i, β * srhtRowBound (Fintype.card n) U.rank δ * (Fintype.card n : ℝ)⁻¹ <
        leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω ⟨i, _⟩ => isEmptyElim i
    rw [h, measureReal_empty]
    exact hδ.le
  have hn0 : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  rcases le_or_gt δ (Fintype.card n) with hδn | hδn
  · have ht : 0 ≤ Real.log (Fintype.card n / δ) := Real.log_nonneg ((one_le_div hδ).2 hδn)
    have h := measureReal_exists_leverageScore_mul_diagonal_gt_le_of_hasLaw_rademacherVector
      hF hξ U ht
    rw [← srhtRowBound_def, Real.exp_neg, Real.exp_log (div_pos hn0 hδ), inv_div,
      mul_div_cancel₀ _ hn0.ne'] at h
    exact h
  · exact measureReal_le_one.trans (le_of_lt (lt_of_le_of_lt (Nat.one_le_cast.2 Fintype.card_pos)
      hδn))

/-! ### Flattening a general matrix -/

/-- The **flattened row-norm bound** <!-- value srhtRowNormBound \mathbf{A} t -->
$$\|\mathbf{A}\|_{\mathsf{F}}^2 + 2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{t} +
2\|\mathbf{A}\|_2^2 t:$$
flattening makes every squared row norm of $\mathbf{F}\mathbf{D}\mathbf{A}$ at most $\beta$ times
this over $\lvert n\rvert$, outside probability $\lvert n\rvert e^{-t}$
(`NLAlib.measureReal_exists_norm_mul_diagonal_mul_apply_sq_gt_le_of_hasLaw_rademacherVector`).
At a matrix with $d$ orthonormal columns it is $d + 2\sqrt{dt} + 2t$, at $t = \log(n/\delta)$
the bracket of `NLAlib.srhtRowBound`, <!-- value srhtRowBound n d \delta -->
$d + 2\sqrt{d \log(n/\delta)} + 2 \log(n/\delta)$. The value the proof reaches, the Hsu–Kakade–Zhang
threshold. Junk: for $t < 0$ the square root is $0$. -/
noncomputable irreducible_def srhtRowNormBound (A : Matrix n r 𝕜) (t : ℝ) : ℝ :=
  frobNorm A ^ 2 + 2 * frobNorm A * specNorm A * √t + 2 * specNorm A ^ 2 * t

omit [DecidableEq n] in
/-- The flattened row-norm bound <!-- value srhtRowNormBound \mathbf{A} t -->
$$\|\mathbf{A}\|_{\mathsf{F}}^2 + 2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{t} +
2\|\mathbf{A}\|_2^2 t$$
is nonnegative for $t \ge 0$. -/
theorem srhtRowNormBound_nonneg (A : Matrix n r 𝕜) (ht : 0 ≤ t) : 0 ≤ srhtRowNormBound A t := by
  rw [srhtRowNormBound_def]
  have := frobNorm_nonneg A
  have := specNorm_nonneg A
  positivity

omit [DecidableEq n] in
/-- The explicit value the documentation displays: the flattened row-norm bound is at
most <!-- value srhtRowNormBound \mathbf{A} t -->
$$\|\mathbf{A}\|_{\mathsf{F}}^2 + 2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{t} +
2\|\mathbf{A}\|_2^2 t$$
(at present an equality). -/
theorem srhtRowNormBound_le (A : Matrix n r 𝕜) (t : ℝ) :
    srhtRowNormBound A t ≤
      frobNorm A ^ 2 + 2 * frobNorm A * specNorm A * √t + 2 * specNorm A ^ 2 * t := by
  rw [srhtRowNormBound_def]

/-- The row matrix $\mathbf{M}_i = \mathbf{A}^{\mathsf{T}}\operatorname{diag}(\mathbf{F}_{i,\cdot})$
of a general $\mathbf{A}$ has $\|\mathbf{M}_i\|_{\mathsf{F}}^2 \le
\beta\|\mathbf{A}\|_{\mathsf{F}}^2/\lvert n\rvert$ and
$\|\mathbf{M}_i\|_2^2 \le \beta\|\mathbf{A}\|_2^2/\lvert n\rvert$. -/
private theorem frobNorm_sq_le_and_specNorm_sq_le_of_matrix (hF : IsBoundedOrthonormal F β)
    [Nonempty n] (A : Matrix n r 𝕜) (i : n) :
    frobNorm (Aᵀ * Matrix.diagonal (F i)) ^ 2 ≤ β * (Fintype.card n : ℝ)⁻¹ * frobNorm A ^ 2 ∧
      specNorm (Aᵀ * Matrix.diagonal (F i)) ^ 2 ≤
        β * (Fintype.card n : ℝ)⁻¹ * specNorm A ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  have hFi : ∀ l, ‖F i l‖ ^ 2 ≤ β * (Fintype.card n : ℝ)⁻¹ := fun l => by
    rw [← div_eq_mul_inv, le_div_iff₀ hn, mul_comm]
    exact hF.card_mul_norm_sq_le i l
  have hK : 0 ≤ β * (Fintype.card n : ℝ)⁻¹ :=
    (sq_nonneg _).trans (hFi (Classical.arbitrary n))
  refine ⟨?_, ?_⟩
  · rw [← frobNorm_transpose, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.transpose_transpose, frobNorm_sq_eq_sum, frobNorm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.diagonal_mul, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (hFi l) (sq_nonneg _)
  · have h1 : specNorm (Matrix.diagonal (F i)) ≤ √(β * (Fintype.card n : ℝ)⁻¹) :=
      specNorm_diagonal_le (Real.sqrt_nonneg _) fun l => Real.le_sqrt_of_sq_le (hFi l)
    have h2 : specNorm (Aᵀ * Matrix.diagonal (F i)) ≤
        specNorm A * √(β * (Fintype.card n : ℝ)⁻¹) := by
      refine (specNorm_mul_le _ _).trans ?_
      rw [specNorm_transpose]
      exact mul_le_mul_of_nonneg_left h1 (specNorm_nonneg _)
    calc specNorm (Aᵀ * Matrix.diagonal (F i)) ^ 2
        ≤ (specNorm A * √(β * (Fintype.card n : ℝ)⁻¹)) ^ 2 :=
          pow_le_pow_left₀ (specNorm_nonneg _) h2 2
      _ = β * (Fintype.card n : ℝ)⁻¹ * specNorm A ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hK, mul_comm]

/-- The tail of one row of $\mathbf{F}\mathbf{D}\mathbf{A}$: the Hsu–Kakade–Zhang tail at
$\mathbf{M}_i$, proxy $1$, with threshold $\beta$ times `srhtRowNormBound A t` over
$\lvert n\rvert$ (<!-- mention srhtRowNormBound -->the flattened row-norm bound). -/
private theorem measureReal_not_norm_row_sq_le_srhtRowNormBound (hF : IsBoundedOrthonormal F β)
    (hξ : HasLaw ξ (rademacherVector n) μ) (A : Matrix n r 𝕜) (ht : 0 ≤ t) (i : n) :
    μ.real {ω | ¬ ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * A) i)‖ ^ 2 ≤
      β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹} ≤ Real.exp (-t) := by
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure_iff.2 inferInstance
  have : Nonempty n := ⟨i⟩
  obtain ⟨hFr, hSp⟩ := frobNorm_sq_le_and_specNorm_sq_le_of_matrix hF A i
  set M := Aᵀ * Matrix.diagonal (F i) with hM_def
  set K := β * (Fintype.card n : ℝ)⁻¹ with hK_def
  have hb : (1 : ℝ) ≤ β := hF.one_le
  have hK : 0 ≤ K := mul_nonneg (by linarith) (by positivity)
  have hR := srhtRowNormBound_nonneg A ht
  have hthr : β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹ = K * srhtRowNormBound A t := by
    rw [hK_def]
    ring
  simp only [mul_diagonal_mul_apply A, hthr]
  by_cases hM : M = 0
  · have hset : {ω | ¬ ‖WithLp.toLp 2 (M *ᵥ fun l => (ξ ω l : 𝕜))‖ ^ 2 ≤
        K * srhtRowNormBound A t} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => hω ?_
      rw [hM, Matrix.zero_mulVec, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero]
      positivity
    rw [hset, measureReal_empty]
    positivity
  have hFr' : frobNorm M ≤ √K * frobNorm A := by
    rw [← Real.sqrt_sq (frobNorm_nonneg A), ← Real.sqrt_mul hK]
    exact Real.le_sqrt_of_sq_le hFr
  have hS : specNorm M ≤ √K * specNorm A := by
    rw [← Real.sqrt_sq (specNorm_nonneg A), ← Real.sqrt_mul hK]
    exact Real.le_sqrt_of_sq_le hSp
  have hG : frobNorm (Mᴴ * M) ≤ K * (specNorm A * frobNorm A) := by
    refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
    rw [specNorm_conjTranspose]
    calc specNorm M * frobNorm M ≤ (√K * specNorm A) * (√K * frobNorm A) :=
          mul_le_mul hS hFr' (frobNorm_nonneg _) (by positivity)
      _ = K * (specNorm A * frobNorm A) := by rw [mul_mul_mul_comm, Real.mul_self_sqrt hK]
  have key := (isSubgaussianVector_of_hasLaw_rademacherVector hξ).measureReal_norm_mulVec_sq_ge_le
    one_ne_zero hM ht (𝕜 := 𝕜)
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) key
  simp only [Set.mem_ofPred_eq, not_le, NNReal.coe_one, one_mul] at hω ⊢
  refine le_trans ?_ hω.le
  rw [srhtRowNormBound_def]
  have h1 := mul_le_mul_of_nonneg_right hG (Real.sqrt_nonneg t)
  have h2 := mul_le_mul_of_nonneg_right hSp ht
  nlinarith

/-- **Flattening of a general matrix**: for a bounded orthonormal $\mathbf{F}$ with constant
$\beta$, a diagonal $\mathbf{D} = \operatorname{diag}(\boldsymbol{\xi})$ of independent random
signs, any $\mathbf{A} \in \Bbbk^{n \times r}$ and $t \ge 0$, outside probability
$\lvert n\rvert e^{-t}$ every row of $\mathbf{F}\mathbf{D}\mathbf{A}$
satisfies <!-- value srhtRowNormBound \mathbf{A} t -->
$$\|(\mathbf{F}\mathbf{D}\mathbf{A})_i\|^2 \le \frac{\beta\bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 +
2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{t} + 2\|\mathbf{A}\|_2^2 t\bigr)}{\lvert n\rvert}
\,,$$
the numerator being $\beta$ times `NLAlib.srhtRowNormBound A t`. Row $i$ is
$\mathbf{M}_i\boldsymbol{\xi}$ with $\|\mathbf{M}_i\|_{\mathsf{F}}^2 \le
\beta\|\mathbf{A}\|_{\mathsf{F}}^2/\lvert n\rvert$ and
$\|\mathbf{M}_i\|_2^2 \le \beta\|\mathbf{A}\|_2^2/\lvert n\rvert$, then the Hsu–Kakade–Zhang tail
and a union over the rows, as in
`NLAlib.measureReal_exists_leverageScore_mul_diagonal_gt_le_of_hasLaw_rademacherVector`, which is
the case of an orthonormal basis. [Tropp2011a, Lemma 3.3] for orthonormal columns. -/
theorem measureReal_exists_norm_mul_diagonal_mul_apply_sq_gt_le_of_hasLaw_rademacherVector
    (hF : IsBoundedOrthonormal F β) (hξ : HasLaw ξ (rademacherVector n) μ) (A : Matrix n r 𝕜)
    (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹ <
      ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * A) i)‖ ^ 2} ≤
      Fintype.card n * Real.exp (-t) := by
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure_iff.2 inferInstance
  rcases isEmpty_or_nonempty n with hn | hn
  · have h : {ω | ∃ i, β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹ <
        ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * A) i)‖ ^ 2} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω ⟨i, _⟩ => isEmptyElim i
    rw [h, measureReal_empty]
    positivity
  have hrow := fun i => measureReal_not_norm_row_sq_le_srhtRowNormBound hF hξ A ht i
  have hsub : {ω | ∃ i, β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹ <
        ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * A) i)‖ ^ 2} ⊆
      ⋃ i, {ω | ¬ ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * A) i)‖ ^ 2 ≤
        β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹} := by
    intro ω ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, not_le.2 hi⟩
  calc _ ≤ μ.real (⋃ i, {ω | ¬ ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * A)
          i)‖ ^ 2 ≤ β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹}) := measureReal_mono hsub
    _ ≤ ∑ i, μ.real {ω | ¬ ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ ω l : 𝕜)) * A)
          i)‖ ^ 2 ≤ β * srhtRowNormBound A t * (Fintype.card n : ℝ)⁻¹} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : n, Real.exp (-t) := Finset.sum_le_sum fun i _ => hrow i
    _ = Fintype.card n * Real.exp (-t) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Flatten, then sample -/

/-- The measurable set of unitaries $\mathbf{B}$ making $\mathbf{B}\mathbf{U}$ incoherent. -/
private theorem measurableSet_good (U : Matrix n r 𝕜) (L : ℝ) :
    MeasurableSet {B : Matrix n n 𝕜 | HasOrthonormalCols B ∧
      ∀ i, leverageScore (B * U) i ≤ L * (Fintype.card n : ℝ)⁻¹} := by
  have h1 : MeasurableSet {B : Matrix n n 𝕜 | HasOrthonormalCols B} :=
    (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
      continuous_const).measurableSet
  have h2 : MeasurableSet {B : Matrix n n 𝕜 |
      ∀ i, leverageScore (B * U) i ≤ L * (Fintype.card n : ℝ)⁻¹} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i => measurableSet_le ?_ measurable_const
    exact RCLike.continuous_re.measurable.comp ((Matrix.measurable_apply i i).comp
      (measurable_rangeProjector.comp (measurable_id.matrix_mul measurable_const)))
  exact h1.inter h2

omit [Fintype k] in
/-- The shared step of the two transfers, for a closed property $R$ of the pair
$(\mathbf{A}, \mathbf{V})$ with $R(\mathbf{A}\mathbf{B}, \mathbf{U}) \iff R(\mathbf{A},
\mathbf{B}\mathbf{U})$ for unitary $\mathbf{B}$. -/
private theorem measureReal_not_mul_le_add [Finite k] [IsProbabilityMeasure μ]
    {R : Matrix k n 𝕜 → Matrix n r 𝕜 → Prop}
    (hR : IsClosed {x : Matrix k n 𝕜 × Matrix n r 𝕜 | R x.1 x.2}) {U : Matrix n r 𝕜}
    (hRB : ∀ (A : Matrix k n 𝕜) (B : Matrix n n 𝕜), HasOrthonormalCols B →
      (R (A * B) U ↔ R A (B * U)))
    {P : Ω → Matrix k n 𝕜} {T : Ω → Matrix n n 𝕜} (hind : IndepFun P T μ)
    (hP : AEMeasurable P μ) (hT : AEMeasurable T μ) (hTU : ∀ᵐ ω ∂μ, HasOrthonormalCols (T ω))
    (hδ₁ : 0 ≤ δ₁)
    (hsample : ∀ V : Matrix n r 𝕜, V.rank ≤ U.rank →
      (∀ i, leverageScore V i ≤ L * (Fintype.card n : ℝ)⁻¹) → μ.real {ω | ¬ R (P ω) V} ≤ δ₁)
    (hflat : μ.real {ω | ∃ i, L * (Fintype.card n : ℝ)⁻¹ < leverageScore (T ω * U) i} ≤ δ₂) :
    μ.real {ω | ¬ R (P ω * T ω) U} ≤ δ₁ + δ₂ := by
  have hE : MeasurableSet {x : Matrix k n 𝕜 × Matrix n n 𝕜 | ¬ R (x.1 * x.2) U} :=
    (hR.preimage ((continuous_fst.matrix_mul continuous_snd).prodMk continuous_const)
      ).isOpen_compl.measurableSet
  refine hind.measureReal_mem_le_add hP hT hE (measurableSet_good U L) hδ₁ ?_ ?_
  · rintro B ⟨hB, hlev⟩
    have h := hsample (B * U) (Matrix.rank_mul_le_right B U) hlev
    refine le_of_eq_of_le ?_ h
    congr 1
    ext ω
    exact not_congr (hRB (P ω) B hB)
  · refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)) hflat
    filter_upwards [hTU] with ω hω hnot
    by_contra h
    exact hnot ⟨hω, fun i => not_lt.1 fun hi => h ⟨i, hi⟩⟩

/-- **Flatten, then sample** (injection). A random sketch $\mathbf{P}$ that is a subspace injection
with constant $a$ and failure probability $\delta_1$ for every fixed subspace of rank at most
$\operatorname{rank}\mathbf{U}$ whose leverage scores are at most $L / \lvert n \rvert$, composed
with an independent random unitary $\mathbf{T}$ that makes $\mathbf{T}\mathbf{U}$ so incoherent
outside probability $\delta_2$, is a subspace injection for $\operatorname{range}\mathbf{U}$ with
constant $a$ outside probability $\delta_1 + \delta_2$. $0 \le \delta_1$ is needed: for $L < 0$
and nonempty `n` the sampling hypothesis is vacuous. [Tropp2011a, §3.1] (the structure of the
SRHT proof: Lemma 3.3 flattens, Lemma 3.4 samples); [CamanoEpperlyMeyerTropp2025, §4.5] (the
same two steps for SparseRTT, where their Theorem 4.4 is the sampling hypothesis). -/
theorem hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le [IsProbabilityMeasure μ]
    {P : Ω → Matrix k n 𝕜} {T : Ω → Matrix n n 𝕜} (hind : IndepFun P T μ)
    (hP : AEMeasurable P μ) (hT : AEMeasurable T μ) (hTU : ∀ᵐ ω ∂μ, HasOrthonormalCols (T ω))
    {U : Matrix n r 𝕜} (hδ₁ : 0 ≤ δ₁)
    (hsample : ∀ V : Matrix n r 𝕜, V.rank ≤ U.rank →
      (∀ i, leverageScore V i ≤ L * (Fintype.card n : ℝ)⁻¹) → HasSubspaceInjection P V a δ₁ μ)
    (hflat : μ.real {ω | ∃ i, L * (Fintype.card n : ℝ)⁻¹ < leverageScore (T ω * U) i} ≤ δ₂) :
    HasSubspaceInjection (fun ω => P ω * T ω) U a (δ₁ + δ₂) μ :=
  measureReal_not_mul_le_add (R := fun A V => IsSubspaceInjection A V a)
    (isClosed_setOf_isSubspaceInjection a) (fun _ _ hB => hB.isSubspaceInjection_mul_iff U)
    hind hP hT hTU hδ₁ hsample hflat

/-- **Flatten, then sample** (embedding). A random sketch $\mathbf{P}$ that is a subspace
embedding with constants $a$, $b$ and failure probability $\delta_1$ for every fixed subspace of
rank at most $\operatorname{rank}\mathbf{U}$ whose leverage scores are at most
$L / \lvert n \rvert$, composed with an independent random unitary $\mathbf{T}$ that makes
$\mathbf{T}\mathbf{U}$ so incoherent outside probability $\delta_2$, is a subspace embedding for
$\operatorname{range}\mathbf{U}$ with constants $a$, $b$ outside probability
$\delta_1 + \delta_2$. $0 \le \delta_1$ is needed, as in
`NLAlib.hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le`. [Tropp2011a, §3.1];
[CamanoEpperlyMeyerTropp2025, §4.5]. -/
theorem hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le [IsProbabilityMeasure μ]
    {P : Ω → Matrix k n 𝕜} {T : Ω → Matrix n n 𝕜} (hind : IndepFun P T μ)
    (hP : AEMeasurable P μ) (hT : AEMeasurable T μ) (hTU : ∀ᵐ ω ∂μ, HasOrthonormalCols (T ω))
    {U : Matrix n r 𝕜} (hδ₁ : 0 ≤ δ₁)
    (hsample : ∀ V : Matrix n r 𝕜, V.rank ≤ U.rank →
      (∀ i, leverageScore V i ≤ L * (Fintype.card n : ℝ)⁻¹) → HasSubspaceEmbedding P V a b δ₁ μ)
    (hflat : μ.real {ω | ∃ i, L * (Fintype.card n : ℝ)⁻¹ < leverageScore (T ω * U) i} ≤ δ₂) :
    HasSubspaceEmbedding (fun ω => P ω * T ω) U a b (δ₁ + δ₂) μ :=
  measureReal_not_mul_le_add (R := fun A V => IsSubspaceEmbedding A V a b)
    (isClosed_setOf_isSubspaceEmbedding a b) (fun _ _ hB => hB.isSubspaceEmbedding_mul_iff U)
    hind hP hT hTU hδ₁ hsample hflat

end NLAlib
