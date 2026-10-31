/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.PosDef
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Spectral.EigenvectorPairing
public import NLAlib.Matrix.Spectral.PowerBounds

/-!
# Discrete Stein equations

The series $\sum_{j\ge0}\mathbf{A}^j\mathbf{Q}(\mathbf{A}^{\mathsf{H}})^j$ solves
$\mathbf{X}-\mathbf{A}\mathbf{X}\mathbf{A}^{\mathsf{H}}=\mathbf{Q}$ when the spectral radius
of $\mathbf{A}$ is less than one. Positive forcing gives positive solutions. A strict positive
definite Stein certificate characterizes stability over any `RCLike` field. Finite sums and
infinite sums use native notation, including for the empty index type.

Adapted from the Stein development of `tchen-research/NLAlib` commit
`77514ce42a0e437d837797a063ac161f41022730`, using the current spectral-radius, norm, positivity,
and complexification interfaces. Smith algorithms are not part of this matrix-equation topic.

## Main results

* `NLAlib.sub_sum_range_pow_mul_mul_conjTranspose`: exact finite-prefix error.
* `NLAlib.summable_pow_mul_mul_conjTranspose`: convergence under spectral stability.
* `NLAlib.existsUnique_sub_mul_mul_conjTranspose_eq`: the unique Stein solution.
* `Matrix.PosDef.tsum_pow_mul_mul_conjTranspose`: positive definite forcing gives a positive sum.
* `NLAlib.SymmetricGauge.matrixNorm_tsum_sub_sum_range_pow_mul_mul_conjTranspose_le`:
  geometric truncation bounds in every unitarily invariant norm.
* `NLAlib.specRadius_lt_one_iff_exists_posDef_sub_mul_mul_conjTranspose`: stability certificates.
-/

@[expose] public section

open Filter Topology
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Finite sums -/

/-- Splitting a finite Stein sum after $M$ terms propagates its remaining $N$ terms by
$\mathbf{A}^M$ and $(\mathbf{A}^{\mathsf{H}})^M$. -/
theorem sum_range_pow_mul_mul_conjTranspose_add (A Q : Matrix n n 𝕜) (M N : ℕ) :
    (∑ j ∈ Finset.range (M + N), A ^ j * Q * (Aᴴ) ^ j) =
      (∑ j ∈ Finset.range M, A ^ j * Q * (Aᴴ) ^ j) +
        A ^ M * (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) * (Aᴴ) ^ M := by
  rw [Finset.sum_range_add]
  congr 1
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_add, Matrix.mul_assoc]
  rw [pow_mul_comm (Aᴴ) j M]

/-- For every solution $\mathbf{X}-\mathbf{A}\mathbf{X}\mathbf{A}^{\mathsf{H}}=\mathbf{Q}$,
the error after the first $N$ Stein terms is $\mathbf{A}^N\mathbf{X}
(\mathbf{A}^{\mathsf{H}})^N$, without a convergence hypothesis. -/
theorem sub_sum_range_pow_mul_mul_conjTranspose (A Q X : Matrix n n 𝕜)
    (hX : X - A * X * Aᴴ = Q) (N : ℕ) :
    X - (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) = A ^ N * X * (Aᴴ) ^ N := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
      Matrix.one_mul, Matrix.mul_one]
  | succ N hN =>
    rw [Finset.sum_range_succ, ← sub_sub, hN, ← hX, Matrix.mul_sub, Matrix.sub_mul]
    rw [pow_succ, pow_succ']
    simp only [Matrix.mul_assoc]
    abel

/-- The residual of the first $N$ Stein terms is the next summand
$\mathbf{A}^N\mathbf{Q}(\mathbf{A}^{\mathsf{H}})^N$. -/
theorem sub_sum_range_add_mul_sum_range_mul_conjTranspose (A Q : Matrix n n 𝕜) (N : ℕ) :
    Q - (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) +
      A * (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ =
        A ^ N * Q * (Aᴴ) ^ N := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ N hN =>
    rw [Finset.sum_range_succ]
    simp only [Matrix.mul_add, Matrix.add_mul]
    have heq : Q - ((∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) +
        A ^ N * Q * (Aᴴ) ^ N) +
        (A * (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ +
          A * (A ^ N * Q * (Aᴴ) ^ N) * Aᴴ) =
        (Q - (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) +
          A * (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ) -
            A ^ N * Q * (Aᴴ) ^ N + A * (A ^ N * Q * (Aᴴ) ^ N) * Aᴴ := by abel
    rw [heq, hN, sub_self, zero_add, pow_succ', pow_succ]
    simp only [Matrix.mul_assoc]

/-- Positive semidefinite forcing makes every finite Stein sum positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.sum_range_pow_mul_mul_conjTranspose {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (A : Matrix n n 𝕜) (N : ℕ) :
    (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  simpa only [Matrix.conjTranspose_pow] using hQ.mul_mul_conjTranspose_same (A ^ j)

/-- Finite Stein sums increase in the Loewner order when the forcing is positive semidefinite.
-/
theorem _root_.Matrix.PosSemidef.monotone_sum_range_pow_mul_mul_conjTranspose
    {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) (A : Matrix n n 𝕜) :
    Monotone (fun N => ∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [Matrix.le_iff, Finset.sum_range_succ, add_sub_cancel_left]
  simpa only [Matrix.conjTranspose_pow] using hQ.mul_mul_conjTranspose_same (A ^ N)

/-! ### Convergence, solution, and positivity -/

/-- **Stein equation, series convergence.** If $\rho(\mathbf{A})<1$, the series
$\sum_{j\ge0}\mathbf{A}^j\mathbf{Q}(\mathbf{A}^{\mathsf{H}})^j$ converges, for arbitrary
forcing $\mathbf{Q}$; the spectral norm of $\mathbf{A}$ need not be below one.
[Boyd2009, slide 13–22] treats real matrices with symmetric forcing.
The present statement allows arbitrary forcing over `RCLike`.
Adapted from `tchen-research/NLAlib` commit `77514ce42a0e437d837797a063ac161f41022730`.
Result: stein-equation -/
theorem summable_pow_mul_mul_conjTranspose (A Q : Matrix n n 𝕜)
    (hA : specRadius A < 1) : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j) := by
  let r := specRadius A + (1 - specRadius A) / 2
  have hr : 0 < r := by dsimp [r]; linarith [specRadius_nonneg A]
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨C, hC, hpow⟩ := exists_forall_specNorm_pow_le_mul_pow A
    (show 0 < (1 - specRadius A) / 2 by linarith)
  have hr2 : r ^ 2 < 1 := by nlinarith
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sq_nonneg r) hr2).mul_left (C ^ 2 * specNorm Q))
  intro j
  rw [← specNorm_eq_norm, ← Matrix.conjTranspose_pow]
  calc
    _ ≤ specNorm (A ^ j * Q) * specNorm (A ^ j)ᴴ := specNorm_mul_le _ _
    _ ≤ (specNorm (A ^ j) * specNorm Q) * specNorm (A ^ j) := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ ≤ (C * r ^ j * specNorm Q) * (C * r ^ j) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hpow j) (specNorm_nonneg _)) (hpow j)
        (specNorm_nonneg _) (by positivity)
    _ = _ := by rw [← pow_mul, mul_comm 2 j, pow_mul]; ring

/-- **Stein equation, explicit solution.** A summable series
$\sum_{j\ge0}\mathbf{A}^j\mathbf{Q}(\mathbf{A}^{\mathsf{H}})^j$ has sum $\mathbf{X}$
satisfying $\mathbf{X}-\mathbf{A}\mathbf{X}\mathbf{A}^{\mathsf{H}}=\mathbf{Q}$.
[Boyd2009, slide 13–22] treats stable real matrices with symmetric forcing. Here summability
suffices, with arbitrary forcing over `RCLike`. Adapted from `tchen-research/NLAlib` commit
`77514ce42a0e437d837797a063ac161f41022730`.
Result: stein-equation -/
theorem sub_mul_mul_conjTranspose_tsum (A Q : Matrix n n 𝕜)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) -
      A * (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ = Q := by
  have hlim := hs.hasSum.tendsto_sum_nat
  have hleft : Tendsto (fun N => Q - (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) +
      A * (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ) atTop
      (𝓝 (Q - (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) +
        A * (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ)) :=
    (tendsto_const_nhds.sub hlim).add ((tendsto_const_nhds.mul hlim).mul_const Aᴴ)
  have hright : Tendsto (fun N => Q - (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) +
      A * (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ) atTop (𝓝 0) := by
    simpa only [sub_sum_range_add_mul_sum_range_mul_conjTranspose] using hs.tendsto_atTop_zero
  have heq := tendsto_nhds_unique hleft hright
  apply eq_of_sub_eq_zero
  calc
    _ = -(Q - (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) +
        A * (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ) := by abel
    _ = 0 := by rw [heq, neg_zero]

/-- If $\rho(\mathbf{A})<1$, every solution of
$\mathbf{X}-\mathbf{A}\mathbf{X}\mathbf{A}^{\mathsf{H}}=\mathbf{Q}$ equals the Stein series.
-/
theorem eq_tsum_pow_mul_mul_conjTranspose (A Q X : Matrix n n 𝕜)
    (hA : specRadius A < 1) (hX : X - A * X * Aᴴ = Q) :
    X = ∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j := by
  have hlim := (summable_pow_mul_mul_conjTranspose A Q hA).hasSum.tendsto_sum_nat
  have hp := (tendsto_pow_zero_iff_specRadius_lt_one A).mpr hA
  have hstar := (tendsto_pow_zero_iff_specRadius_lt_one Aᴴ).mpr
    (by simpa only [specRadius_conjTranspose] using hA)
  have hzero := (hp.mul_const X).mul hstar
  simp only [Matrix.zero_mul, Matrix.mul_zero] at hzero
  have hid : (fun N => A ^ N * X * (Aᴴ) ^ N) =
      fun N => X - (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) := by
    funext N
    exact (sub_sum_range_pow_mul_mul_conjTranspose A Q X hX N).symm
  rw [hid] at hzero
  exact sub_eq_zero.mp (tendsto_nhds_unique (tendsto_const_nhds.sub hlim) hzero)

/-- **Stein equation, unique solvability.** For $\rho(\mathbf{A})<1$ and every
forcing $\mathbf{Q}$, there is exactly one $\mathbf{X}$ satisfying
$\mathbf{X}-\mathbf{A}\mathbf{X}\mathbf{A}^{\mathsf{H}}=\mathbf{Q}$.
[Boyd2009, slide 13–22] treats real matrices with symmetric forcing.
The present statement allows arbitrary forcing over `RCLike`.
Adapted from `tchen-research/NLAlib` commit `77514ce42a0e437d837797a063ac161f41022730`.
Result: stein-equation -/
theorem existsUnique_sub_mul_mul_conjTranspose_eq (A Q : Matrix n n 𝕜)
    (hA : specRadius A < 1) : ∃! X : Matrix n n 𝕜, X - A * X * Aᴴ = Q := by
  refine ⟨∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j,
    sub_mul_mul_conjTranspose_tsum A Q (summable_pow_mul_mul_conjTranspose A Q hA), ?_⟩
  exact fun X hX => eq_tsum_pow_mul_mul_conjTranspose A Q X hA hX

/-- A convergent Stein series has positive semidefinite sum for positive semidefinite forcing.
-/
theorem _root_.Matrix.PosSemidef.tsum_pow_mul_mul_conjTranspose {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (A : Matrix n n 𝕜)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j).PosSemidef := by
  refine Matrix.PosSemidef.of_hasSum (fun j => ?_) hs.hasSum
  simpa only [Matrix.conjTranspose_pow] using hQ.mul_mul_conjTranspose_same (A ^ j)

/-- A convergent Stein series has positive definite sum for positive definite forcing. -/
theorem _root_.Matrix.PosDef.tsum_pow_mul_mul_conjTranspose {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) (A : Matrix n n 𝕜)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j).PosDef := by
  have hG := hQ.posSemidef.tsum_pow_mul_mul_conjTranspose A hs
  rw [eq_add_of_sub_eq (sub_mul_mul_conjTranspose_tsum A Q hs)]
  exact hQ.add_posSemidef (hG.mul_mul_conjTranspose_same A)

/-! ### Bounds in every unitarily invariant norm -/

private theorem matrixNorm_pow_mul_mul_conjTranspose_le (Φ : SymmetricGauge)
    {A Q : Matrix n n 𝕜} {q : ℝ} (hA : specNorm A ≤ q) (j : ℕ) :
    Φ.matrixNorm (A ^ j * Q * (Aᴴ) ^ j) ≤ q ^ (2 * j) * Φ.matrixNorm Q := by
  have hq : 0 ≤ q := (specNorm_nonneg A).trans hA
  have hp : specNorm (A ^ j) ≤ q ^ j :=
    (specNorm_pow_le A j).trans (pow_le_pow_left₀ (specNorm_nonneg A) hA j)
  rw [← Matrix.conjTranspose_pow]
  calc
    _ ≤ Φ.matrixNorm (A ^ j * Q) * specNorm (A ^ j)ᴴ :=
      Φ.matrixNorm_mul_le_mul_specNorm _ _
    _ ≤ (q ^ j * Φ.matrixNorm Q) * q ^ j := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul
        ((Φ.matrixNorm_mul_le_specNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right hp (Φ.matrixNorm_nonneg Q))) hp
        (specNorm_nonneg _) (mul_nonneg (pow_nonneg hq _) (Φ.matrixNorm_nonneg Q))
    _ = _ := by rw [pow_mul]; ring

/-- **Stein series truncation, norm bound.** If $\|\mathbf{A}\|_2\le q<1$, then every unitarily
invariant
norm satisfies
$$\left\|\sum_{j\ge0}\mathbf{A}^j\mathbf{Q}(\mathbf{A}^{\mathsf{H}})^j\right\|_{\Phi}
\le \frac{\|\mathbf{Q}\|_{\Phi}}{1-q^2}\,.$$
No printed source. Generalizes the spectral and Frobenius estimates of `tchen-research/NLAlib`
commit `77514ce42a0e437d837797a063ac161f41022730`.
Result: stein-series-truncation -/
theorem SymmetricGauge.matrixNorm_tsum_pow_mul_mul_conjTranspose_le
    (Φ : SymmetricGauge) {A Q : Matrix n n 𝕜} {q : ℝ}
    (hA : specNorm A ≤ q) (hq : q < 1) :
    Φ.matrixNorm (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) ≤ Φ.matrixNorm Q / (1 - q ^ 2) := by
  have hq0 := (specNorm_nonneg A).trans hA
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  have hs := summable_pow_mul_mul_conjTranspose A Q
    (((specRadius_le_specNorm A).trans hA).trans_lt hq)
  let G := ∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j
  have heq : G = Q + A * G * Aᴴ := eq_add_of_sub_eq
    (sub_mul_mul_conjTranspose_tsum A Q hs)
  have hb : Φ.matrixNorm (A * G * Aᴴ) ≤ q ^ 2 * Φ.matrixNorm G := by
    simpa only [pow_one, Nat.mul_one] using
      matrixNorm_pow_mul_mul_conjTranspose_le Φ (Q := G) hA 1
  have ht : Φ.matrixNorm G ≤ Φ.matrixNorm Q + q ^ 2 * Φ.matrixNorm G := by
    calc
      _ = Φ.matrixNorm (Q + A * G * Aᴴ) := congrArg Φ.matrixNorm heq
      _ ≤ Φ.matrixNorm Q + Φ.matrixNorm (A * G * Aᴴ) := Φ.matrixNorm_add_le _ _
      _ ≤ _ := by linarith
  apply (le_div_iff₀ hd).mpr
  change Φ.matrixNorm G * (1 - q ^ 2) ≤ Φ.matrixNorm Q
  nlinarith

/-- **Stein series truncation, geometric error.** If $\|\mathbf{A}\|_2\le q<1$, the first
$N$ terms approximate the full sum in every unitarily invariant norm:
$$\left\|\sum_{j\ge0}\mathbf{A}^j\mathbf{Q}(\mathbf{A}^{\mathsf{H}})^j-
\sum_{j=0}^{N-1}\mathbf{A}^j\mathbf{Q}(\mathbf{A}^{\mathsf{H}})^j\right\|_{\Phi}
\le \frac{q^{2N}\|\mathbf{Q}\|_{\Phi}}{1-q^2}\,.$$
No printed source. Generalizes the spectral and Frobenius estimates of `tchen-research/NLAlib`
commit `77514ce42a0e437d837797a063ac161f41022730`.
Result: stein-series-truncation -/
theorem SymmetricGauge.matrixNorm_tsum_sub_sum_range_pow_mul_mul_conjTranspose_le
    (Φ : SymmetricGauge) {A Q : Matrix n n 𝕜} {q : ℝ}
    (hA : specNorm A ≤ q) (hq : q < 1) (N : ℕ) :
    Φ.matrixNorm ((∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) -
      (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j)) ≤
        q ^ (2 * N) * Φ.matrixNorm Q / (1 - q ^ 2) := by
  have hq0 := (specNorm_nonneg A).trans hA
  have hs := summable_pow_mul_mul_conjTranspose A Q
    (((specRadius_le_specNorm A).trans hA).trans_lt hq)
  rw [sub_sum_range_pow_mul_mul_conjTranspose A Q _
    (sub_mul_mul_conjTranspose_tsum A Q hs) N]
  calc
    _ ≤ q ^ (2 * N) * Φ.matrixNorm (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) :=
      matrixNorm_pow_mul_mul_conjTranspose_le Φ hA N
    _ ≤ q ^ (2 * N) * (Φ.matrixNorm Q / (1 - q ^ 2)) :=
      mul_le_mul_of_nonneg_left (Φ.matrixNorm_tsum_pow_mul_mul_conjTranspose_le hA hq)
        (pow_nonneg hq0 _)
    _ = _ := by ring

/-! ### Stability certificates -/

private theorem norm_lt_one_of_posDef_sub_mul_mul_conjTranspose (A X : Matrix n n ℂ)
    (hX : X.PosDef) (hR : (X - A * X * Aᴴ).PosDef) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ A) : ‖μ‖ < 1 := by
  obtain ⟨y, hy, hyA⟩ := exists_vecMul_eq_smul_of_mem_spectrum hμ
  have hx : star y ≠ 0 := by simpa only [star_ne_zero] using hy
  have hAx : Aᴴ *ᵥ star y = star μ • star y := by
    rw [← Matrix.star_vecMul, hyA, star_smul]
  have hquad : quadForm (A * X * Aᴴ) (star y) =
      ((‖μ‖ ^ 2 : ℝ) : ℂ) * quadForm X (star y) := by
    have hc := quadForm_conjTranspose_mul_mul X Aᴴ (star y)
    rw [Matrix.conjTranspose_conjTranspose, hAx, quadForm_smul_right] at hc
    have hstar : star (star μ) * star μ = (‖μ‖ : ℂ) ^ 2 := by
      rw [star_star]
      exact RCLike.mul_conj μ
    simpa only [hstar, Complex.ofReal_pow] using hc
  have hXp := hX.re_quadForm_pos hx
  have hRp := hR.re_quadForm_pos hx
  rw [quadForm_sub_left, hquad] at hRp
  change 0 < (quadForm X (star y) -
    ((‖μ‖ ^ 2 : ℝ) : ℂ) * quadForm X (star y)).re at hRp
  change 0 < (quadForm X (star y)).re at hXp
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hRp
  have hcoef : 0 < 1 - ‖μ‖ ^ 2 := by
    apply (mul_pos_iff_of_pos_right hXp).mp
    nlinarith
  nlinarith [norm_nonneg μ]

/-- **Discrete Lyapunov stability criterion.** A matrix over any `RCLike` field has spectral
radius less than one exactly when there is a positive definite $\mathbf{X}$ for which
$\mathbf{X}-\mathbf{A}\mathbf{X}\mathbf{A}^{\mathsf{H}}$ is positive definite. This includes
the empty index type, where positive definiteness is vacuous and the spectral radius is zero.
[Boyd2009, slides 13–21 through 13–23] gives the real case; extended here to `RCLike`.
Generalizes and consolidates the real and complex versions of `tchen-research/NLAlib` commit
`77514ce42a0e437d837797a063ac161f41022730`.
Result: stein-stability-certificate -/
theorem specRadius_lt_one_iff_exists_posDef_sub_mul_mul_conjTranspose
    (A : Matrix n n 𝕜) :
    specRadius A < 1 ↔ ∃ X : Matrix n n 𝕜, X.PosDef ∧ (X - A * X * Aᴴ).PosDef := by
  constructor
  · intro hA
    have hs := summable_pow_mul_mul_conjTranspose A 1 hA
    refine ⟨∑' j : ℕ, A ^ j * 1 * (Aᴴ) ^ j,
      Matrix.PosDef.one.tsum_pow_mul_mul_conjTranspose A hs, ?_⟩
    rw [sub_mul_mul_conjTranspose_tsum A 1 hs]
    exact Matrix.PosDef.one
  · rintro ⟨X, hX, hR⟩
    cases isEmpty_or_nonempty n with
    | inl hn => rw [specRadius_of_isEmpty]; exact zero_lt_one
    | inr hn =>
      obtain ⟨μ, hμ, hρ⟩ := exists_mem_spectrum_norm_eq_specRadius A
      rw [← hρ]
      apply norm_lt_one_of_posDef_sub_mul_mul_conjTranspose (complexify A) (complexify X)
        (posDef_complexify_iff.mpr hX) _ hμ
      simpa only [complexify_sub, complexify_mul, complexify_conjTranspose] using
        posDef_complexify_iff.mpr hR

end NLAlib
