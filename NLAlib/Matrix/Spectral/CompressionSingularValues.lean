/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.TruncationWindow
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Singular values of a compression

Singular values and Frobenius errors of a compression $\mathbf{P}\mathbf{A}$ of a matrix by an
orthogonal projector $\mathbf{P}$. The quantities
$\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2 \ge 0$ are called the *deficits* of
$\mathbf{P}$: they are bounded by how much of the best rank-$(i+1)$ approximation $\mathbf{P}$
misses, they decrease when the range of $\mathbf{P}$ grows, their sum over $i < k$ is exactly the
excess of the Frobenius error of $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ over the optimal
one, and a small sum of the first $L$ deficits together with a gap after $\sigma_{L-1}$ forces
the range of $\mathbf{P}$ to capture $\llbracket\mathbf{A}\rrbracket_L$.

## Main results

* `IsStarProjection.sq_singularValues_sub_sq_specNorm_le`: $\sigma_i(\mathbf{P}\mathbf{A})^2 \ge
  \sigma_i(\mathbf{A})^2 - \|(\mathbf{I} - \mathbf{P})\llbracket\mathbf{A}\rrbracket_{i+1}\|_2^2$.
* `NLAlib.singularValues_rangeProjector_mul_le_of_range_le`: a larger range gives larger singular
  values of the compression.
* `IsStarProjection.frobNorm_sub_mul_sq_eq_add_sum`,
  `IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq`: the Frobenius error as the optimal error
  plus the sum of the deficits.
* `IsStarProjection.mul_rangeProjector_truncatedSVD_mul`,
  `IsStarProjection.rangeProjector_truncatedSVD_mul_mul`: the truncated compression
  $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ is $\mathbf{\Pi}\mathbf{A}$ for a projector
  $\mathbf{\Pi} \le \mathbf{P}$.
* `NLAlib.HasOrthonormalCols.mul_frobNorm_truncatedSVD_sub_mul_sq_le`,
  `IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le`: an energy deficit and a gap give
  head capture.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n s : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq s]

omit [DecidableEq n] in
/-- Singular values of a compression from below, for any matrix: for an orthogonal projector
$\mathbf{P}$, a matrix $\mathbf{B}$ and every index $i$ (from $0$),
$$\sigma_i(\mathbf{B})^2 - \|(\mathbf{I} - \mathbf{P})\mathbf{B}\|_2^2 \le
\sigma_i(\mathbf{P}\mathbf{B})^2\,.$$
On the leading right singular subspace of $\mathbf{B}$ (dimension $i + 1$) Pythagoras gives
$\|\mathbf{P}\mathbf{B}\mathbf{x}\|^2 \ge (\sigma_i^2 -
\|(\mathbf{I} - \mathbf{P})\mathbf{B}\|_2^2)\|\mathbf{x}\|^2$, and the min–max
characterization `NLAlib.le_singularValues_of_forall_mem` applies. -/
theorem _root_.IsStarProjection.sq_singularValues_sub_sq_specNorm_one_sub_mul_le
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) (B : Matrix m n 𝕜) (i : ℕ) :
    singularValues B i ^ 2 - specNorm ((1 - P) * B) ^ 2 ≤ singularValues (P * B) i ^ 2 := by
  by_cases hi : i < Fintype.card n
  · obtain ⟨S, hS, hSB⟩ := exists_submodule_singularValues_mul_norm_le B hi
    rcases le_or_gt (singularValues B i ^ 2 - specNorm ((1 - P) * B) ^ 2) 0 with hd | hd
    · exact hd.trans (sq_nonneg _)
    have key : Real.sqrt (singularValues B i ^ 2 - specNorm ((1 - P) * B) ^ 2) ≤
        singularValues (P * B) i := by
      refine le_singularValues_of_forall_mem (P * B) S hS.ge fun x hx => ?_
      refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp ?_
      have h1 := pow_le_pow_left₀ (mul_nonneg (singularValues_nonneg B i) (norm_nonneg _))
        (hSB x hx) 2
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_mulVec_le ((1 - P) * B) x) 2
      rw [← Matrix.mulVec_mulVec] at h2 ⊢
      rw [mul_pow, Real.sq_sqrt hd.le]
      rw [mul_pow] at h1 h2
      nlinarith [hP.norm_toLp_sq_eq_add (B *ᵥ x)]
    calc singularValues B i ^ 2 - specNorm ((1 - P) * B) ^ 2
        = Real.sqrt (singularValues B i ^ 2 - specNorm ((1 - P) * B) ^ 2) ^ 2 :=
          (Real.sq_sqrt hd.le).symm
      _ ≤ singularValues (P * B) i ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) key 2
  · rw [singularValues_of_card_cols_le B (not_lt.mp hi)]
    nlinarith [sq_nonneg (specNorm ((1 - P) * B)), sq_nonneg (singularValues (P * B) i)]

omit [DecidableEq n] in
/-- **Singular values of a compression from below**: for an orthogonal projector $\mathbf{P}$
($m \times m$), an $m \times n$ matrix $\mathbf{A}$ and every index $i$ (from $0$),
$$\sigma_i(\mathbf{A})^2 -
\|(\mathbf{I} - \mathbf{P})\llbracket\mathbf{A}\rrbracket_{i+1}\|_2^2 \le
\sigma_i(\mathbf{P}\mathbf{A})^2\,.$$
On the row space of $\llbracket\mathbf{A}\rrbracket_{i+1}$, of dimension $i + 1$ when
$\sigma_i > 0$, the compression loses at most the second term (Pythagoras), and the min–max
characterization `NLAlib.le_singularValues_of_forall_mem` applies.
[MuscoMusco2015, Theorem 12]; used there in the proof of the per-vector guarantee, for the
projector of a Krylov space. -/
theorem _root_.IsStarProjection.sq_singularValues_sub_sq_specNorm_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (i : ℕ) :
    singularValues A i ^ 2 - specNorm ((1 - P) * truncatedSVD A (i + 1)) ^ 2 ≤
      singularValues (P * A) i ^ 2 := by
  have h := hP.sq_singularValues_sub_sq_specNorm_one_sub_mul_le (truncatedSVD A (i + 1)) i
  rw [singularValues_truncatedSVD, if_pos (Nat.lt_succ_self i)] at h
  have hPB : singularValues (P * truncatedSVD A (i + 1)) i ≤ singularValues (P * A) i := by
    rw [← mul_rangeProjector_conjTranspose_truncatedSVD A (i + 1), ← Matrix.mul_assoc]
    exact (singularValues_mul_le_mul_specNorm _ _ i).trans (mul_le_of_le_one_right
      (singularValues_nonneg _ _) (isStarProjection_rangeProjector _).specNorm_le_one)
  exact h.trans (pow_le_pow_left₀ (singularValues_nonneg _ _) hPB 2)

omit [DecidableEq m] in
omit [DecidableEq n] [DecidableEq s] in
/-- Monotonicity of the singular values of a compression in the range: if the range of
$\mathbf{Y}'$ is contained in the range of $\mathbf{Y}$, then for every $\mathbf{A}$ and $i$,
$$\sigma_i(\mathbf{P}_{\mathbf{Y}'}\mathbf{A}) \le \sigma_i(\mathbf{P}_{\mathbf{Y}}\mathbf{A})\,,$$
since $\mathbf{P}_{\mathbf{Y}'} = \mathbf{P}_{\mathbf{Y}'}\mathbf{P}_{\mathbf{Y}}$. The twin for
the error $\mathbf{A} - \mathbf{P}_{\mathbf{Y}}\mathbf{A}$ of the randomized SVD is
`NLAlib.singularValues_one_sub_rangeProjector_mul_le_of_range_le`. -/
theorem singularValues_rangeProjector_mul_le_of_range_le {Y : Matrix m l 𝕜} {Y' : Matrix m s 𝕜}
    (h : LinearMap.range Y'.mulVecLin ≤ LinearMap.range Y.mulVecLin) (A : Matrix m n 𝕜) (i : ℕ) :
    singularValues (rangeProjector Y' * A) i ≤ singularValues (rangeProjector Y * A) i := by
  rw [← rangeProjector_mul_rangeProjector_of_range_le' h, Matrix.mul_assoc]
  exact (isStarProjection_rangeProjector Y').singularValues_mul_le _ i

omit [DecidableEq m] [DecidableEq n] in
/-- **The Frobenius error of a compression of rank at most $k$**: for an orthogonal projector
$\mathbf{P}$ with $\operatorname{rank}\mathbf{P} \le k$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 =
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
\sum_{i<k} \bigl(\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2\bigr)\,,$$
the optimal error plus the deficits of $\mathbf{P}$. It holds for every such projector, whether
or not its range is spanned by singular vectors of a compression.
[MuscoMusco2015, Definition 8]; the sum of the deficits is the error function
$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 -
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ defined there for a frame with
$k$ orthonormal columns, here written through the singular values of $\mathbf{P}\mathbf{A}$. -/
theorem _root_.IsStarProjection.frobNorm_sub_mul_sq_eq_add_sum {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) {k : ℕ} (hk : P.rank ≤ k) :
    frobNorm (A - P * A) ^ 2 = frobNorm (A - truncatedSVD A k) ^ 2 +
      ∑ i ∈ Finset.range k, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := by
  classical
  have h1 := hP.frobNorm_sq_eq_add A
  rw [Matrix.sub_mul, Matrix.one_mul] at h1
  have h2 := frobNorm_sq_eq_truncatedSVD_add A k
  rw [frobNorm_truncatedSVD_sq] at h2
  rw [Finset.sum_sub_distrib, ← frobNorm_sq_eq_sum_range_singularValues_sq (P * A)
    ((Matrix.rank_mul_le_left P A).trans hk)]
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- The column space of the truncated compression lies in the range of the projector: for an
orthogonal projector $\mathbf{P}$ and every $k$, the projector $\mathbf{\Pi}$ onto the column
space of $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ satisfies
$\mathbf{P}\mathbf{\Pi} = \mathbf{\Pi}$. -/
theorem _root_.IsStarProjection.mul_rangeProjector_truncatedSVD_mul {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (k : ℕ) :
    P * rangeProjector (truncatedSVD (P * A) k) = rangeProjector (truncatedSVD (P * A) k) := by
  classical
  have hYP : LinearMap.range (truncatedSVD (P * A) k).mulVecLin ≤
      LinearMap.range P.mulVecLin :=
    (range_truncatedSVD_le (P * A) k).trans (range_le_iff_exists_mul.mpr ⟨A, rfl⟩)
  simpa only [hP.rangeProjector_eq] using rangeProjector_mul_rangeProjector_of_range_le hYP

omit [DecidableEq m] [DecidableEq n] in
/-- The truncated compression is a projection of $\mathbf{A}$ itself: for an orthogonal
projector $\mathbf{P}$ and every $k$, the projector $\mathbf{\Pi}$ onto the column space of
$\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ satisfies
$\mathbf{\Pi}\mathbf{A} = \llbracket\mathbf{P}\mathbf{A}\rrbracket_k$, with
$\mathbf{\Pi} \le \mathbf{P}$ by `IsStarProjection.mul_rangeProjector_truncatedSVD_mul`. -/
theorem _root_.IsStarProjection.rangeProjector_truncatedSVD_mul_mul {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (k : ℕ) :
    rangeProjector (truncatedSVD (P * A) k) * A = truncatedSVD (P * A) k := by
  classical
  have hRP : rangeProjector (truncatedSVD (P * A) k) * P =
      rangeProjector (truncatedSVD (P * A) k) := by
    have h := congrArg Matrix.conjTranspose (hP.mul_rangeProjector_truncatedSVD_mul A k)
    rwa [Matrix.conjTranspose_mul, (isStarProjection_rangeProjector _).conjTranspose_eq,
      hP.conjTranspose_eq] at h
  rw [← hRP, Matrix.mul_assoc, rangeProjector_truncatedSVD_mul]

omit [DecidableEq m] [DecidableEq n] in
/-- **The Frobenius error of a truncated compression**: for an orthogonal projector $\mathbf{P}$
(of any rank) and every $k$,
$$\|\mathbf{A} - \llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 =
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
\sum_{i<k} \bigl(\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2\bigr)\,.$$
The truncation $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$ is $\mathbf{\Pi}\mathbf{A}$ for the
projector $\mathbf{\Pi}$ onto its column space, which lies in the range of $\mathbf{P}$ and has
rank at most $k$. [MuscoMusco2015, Definition 8]; the error function defined there, at the frame
of the column space of $\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$. -/
theorem _root_.IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (P * A) k) ^ 2 = frobNorm (A - truncatedSVD A k) ^ 2 +
      ∑ i ∈ Finset.range k, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := by
  classical
  set Y := truncatedSVD (P * A) k
  have hRA : rangeProjector Y * A = Y := hP.rangeProjector_truncatedSVD_mul_mul A k
  have h := (isStarProjection_rangeProjector Y).frobNorm_sub_mul_sq_eq_add_sum A
    ((rank_rangeProjector Y).trans_le (rank_truncatedSVD_le _ k))
  rw [hRA] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [singularValues_truncatedSVD, if_pos (Finset.mem_range.mp hi)]

omit [DecidableEq m] [DecidableEq n] in
/-- The energy of a block splits between the head and the tail: for every $k$ and
$\mathbf{W}$,
$$\|\mathbf{A}^{\mathsf{H}}\mathbf{W}\|_{\mathsf{F}}^2 =
\|\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}\mathbf{W}\|_{\mathsf{F}}^2 +
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)^{\mathsf{H}}\mathbf{W}\|_{\mathsf{F}}^2\,,$$
since $\llbracket\mathbf{A}\rrbracket_k(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)^{\mathsf{H}}
= \mathbf{0}$. -/
theorem frobNorm_conjTranspose_mul_sq_eq_add (A : Matrix m n 𝕜) (k : ℕ) (W : Matrix m l 𝕜) :
    frobNorm (Aᴴ * W) ^ 2 = frobNorm ((truncatedSVD A k)ᴴ * W) ^ 2 +
      frobNorm ((A - truncatedSVD A k)ᴴ * W) ^ 2 := by
  classical
  have hQ := isStarProjection_rangeProjector (truncatedSVD A k)ᴴ
  have hAQ := mul_rangeProjector_conjTranspose_truncatedSVD A k
  have hE : A - truncatedSVD A k = A * (1 - rangeProjector (truncatedSVD A k)ᴴ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hAQ]
  have hB1 : truncatedSVD A k * (1 - rangeProjector (truncatedSVD A k)ᴴ) = 0 := by
    calc truncatedSVD A k * (1 - rangeProjector (truncatedSVD A k)ᴴ)
        = A * (rangeProjector (truncatedSVD A k)ᴴ *
            (1 - rangeProjector (truncatedSVD A k)ᴴ)) := by rw [← Matrix.mul_assoc, hAQ]
      _ = 0 := by rw [hQ.mul_one_sub_self, Matrix.mul_zero]
  have hBE : truncatedSVD A k * (A - truncatedSVD A k)ᴴ = 0 := by
    rw [hE, Matrix.conjTranspose_mul, hQ.one_sub.conjTranspose_eq, ← Matrix.mul_assoc, hB1,
      Matrix.zero_mul]
  have hsplit : Aᴴ * W = (truncatedSVD A k)ᴴ * W + (A - truncatedSVD A k)ᴴ * W := by
    rw [← Matrix.add_mul, Matrix.conjTranspose_sub, add_sub_cancel]
  rw [hsplit]
  refine frobNorm_add_sq_of_frobInner_eq_zero ?_
  rw [frobInner_mul_left, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hBE,
    Matrix.zero_mul, frobInner_zero_right]

omit [DecidableEq n] in
/-- The tail energy of a block: for every $k$ and $\mathbf{W}$,
$$\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)^{\mathsf{H}}\mathbf{W}\|_{\mathsf{F}} \le
\sigma_k(\mathbf{A})\,
\|(\mathbf{I} - \mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k})\mathbf{W}\|_{\mathsf{F}}\,:$$
only the part of $\mathbf{W}$ outside the column space of $\llbracket\mathbf{A}\rrbracket_k$
sees the tail. -/
theorem frobNorm_conjTranspose_sub_truncatedSVD_mul_le (A : Matrix m n 𝕜) (k : ℕ)
    (W : Matrix m l 𝕜) :
    frobNorm ((A - truncatedSVD A k)ᴴ * W) ≤
      singularValues A k * frobNorm ((1 - rangeProjector (truncatedSVD A k)) * W) := by
  have hR := isStarProjection_rangeProjector (truncatedSVD A k)
  have hRE : rangeProjector (truncatedSVD A k) * (A - truncatedSVD A k) = 0 := by
    rw [Matrix.mul_sub, rangeProjector_truncatedSVD_mul, rangeProjector_mul_self, sub_self]
  have e : (A - truncatedSVD A k)ᴴ * W =
      (A - truncatedSVD A k)ᴴ * ((1 - rangeProjector (truncatedSVD A k)) * W) := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← hR.conjTranspose_eq,
      ← Matrix.conjTranspose_mul, hRE, Matrix.conjTranspose_zero, sub_zero]
  rw [e]
  refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
  rw [specNorm_conjTranspose, specNorm_sub_truncatedSVD]

omit [DecidableEq m] [DecidableEq n] in
/-- **An energy deficit and a gap give head capture, frame form**: let $\mathbf{W}$ have at most
$L = h + 1$ orthonormal columns, let $\theta \le 1$ be a relative gap,
$\sigma_L(\mathbf{A})^2 \le (1 - \theta)\,\sigma_h(\mathbf{A})^2$, and let the energy of
$\mathbf{W}$ be within $\eta$ of the largest possible,
$\sum_{i<L} \sigma_i(\mathbf{A})^2 - \eta \le \|\mathbf{A}^{\mathsf{H}}\mathbf{W}\|_{\mathsf{F}}^2$.
Then the range of $\mathbf{W}$ captures the best rank-$L$ approximation,
$$\theta\,\|\llbracket\mathbf{A}\rrbracket_L -
\mathbf{W}\mathbf{W}^{\mathsf{H}}\llbracket\mathbf{A}\rrbracket_L\|_{\mathsf{F}}^2 \le \eta\,.$$
For $\theta \le 0$ the statement is trivial; without $\theta \le 1$ it is false.
[BakshiClarksonWoodruff2022, Lemma 3.5]; there for exactly $L$ columns with a per-vector
hypothesis and an unspecified polynomial accuracy, here for at most $L$ columns, with the summed
energy deficit and the gap explicit. -/
theorem HasOrthonormalCols.mul_frobNorm_truncatedSVD_sub_mul_sq_le {W : Matrix m s 𝕜}
    (hW : HasOrthonormalCols W) (A : Matrix m n 𝕜) {h L : ℕ} (hL : h + 1 = L)
    (hcard : Fintype.card s ≤ L) {θ η : ℝ} (hθ : θ ≤ 1)
    (hgap : singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hη : ∑ i ∈ Finset.range L, singularValues A i ^ 2 - η ≤ frobNorm (Aᴴ * W) ^ 2) :
    θ * frobNorm (truncatedSVD A L - W * Wᴴ * truncatedSVD A L) ^ 2 ≤ η := by
  classical
  subst hL
  have hR := isStarProjection_rangeProjector (truncatedSVD A (h + 1))
  have hP := hW.isStarProjection_mul_conjTranspose
  -- the energy of `W` splits between the head and the tail
  have h1 := frobNorm_conjTranspose_mul_sq_eq_add A (h + 1) W
  -- the tail energy is at most `σ_L²` times the part of `W` outside the head range
  have h2 := frobNorm_conjTranspose_sub_truncatedSVD_mul_le A (h + 1) W
  have h3 : frobNorm ((1 - rangeProjector (truncatedSVD A (h + 1))) * W) ^ 2 =
      Fintype.card s - frobNorm (rangeProjector (truncatedSVD A (h + 1)) * W) ^ 2 := by
    have hWn : frobNorm W ^ 2 = Fintype.card s := by
      rw [← Matrix.mul_one W, hW.frobNorm_mul_left, frobNorm_one_sq]
    linarith [hR.frobNorm_sq_eq_add W]
  -- the head energy missed by `W`
  have h4 : frobNorm (truncatedSVD A (h + 1)) ^ 2 = frobNorm ((truncatedSVD A (h + 1))ᴴ * W) ^ 2 +
      frobNorm (truncatedSVD A (h + 1) - W * Wᴴ * truncatedSVD A (h + 1)) ^ 2 := by
    have e := hP.frobNorm_sq_eq_add (truncatedSVD A (h + 1))
    rwa [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hW.frobNorm_mul_left,
      ← frobNorm_conjTranspose (Wᴴ * _), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at e
  -- it is at least `σ_h²` times the head range missed by `W`
  have h5 : singularValues A h ^ 2 *
      frobNorm ((1 - W * Wᴴ) * rangeProjector (truncatedSVD A (h + 1))) ^ 2 ≤
        frobNorm ((1 - W * Wᴴ) * truncatedSVD A (h + 1)) ^ 2 := by
    have e := sq_mul_frobNorm_mul_sub_rangeProjector_sq_le A (1 - W * Wᴴ) (Nat.zero_le (h + 1))
      (singularValues_nonneg A h) fun i _ hi => singularValues_antitone A (Nat.lt_succ_iff.mp hi)
    simpa only [truncatedSVD_zero, rangeProjector_zero, sub_zero] using e
  have h6 : frobNorm ((1 - W * Wᴴ) * rangeProjector (truncatedSVD A (h + 1))) ^ 2 =
      (truncatedSVD A (h + 1)).rank -
        frobNorm (rangeProjector (truncatedSVD A (h + 1)) * W) ^ 2 := by
    have e := hP.frobNorm_sq_eq_add (rangeProjector (truncatedSVD A (h + 1)))
    have hPR : frobNorm (W * Wᴴ * rangeProjector (truncatedSVD A (h + 1))) =
        frobNorm (rangeProjector (truncatedSVD A (h + 1)) * W) := by
      rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hR.conjTranspose_eq, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
        hW.frobNorm_mul_conjTranspose_right]
    rw [frobNorm_rangeProjector_sq, hPR] at e
    linarith
  rw [h6, Matrix.sub_mul, Matrix.one_mul] at h5
  rw [← frobNorm_truncatedSVD_sq] at hη
  have hY := pow_le_pow_left₀ (frobNorm_nonneg _) h2 2
  rw [mul_pow, h3] at hY
  have hD := sq_nonneg (frobNorm (truncatedSVD A (h + 1) - W * Wᴴ * truncatedSVD A (h + 1)))
  rcases (singularValues_nonneg A (h + 1)).eq_or_lt with h0 | hpos
  · rw [← h0] at hY
    nlinarith
  · have hr : ((truncatedSVD A (h + 1)).rank : ℝ) = h + 1 := by
      rw [rank_truncatedSVD, min_eq_left ((singularValues_pos_iff A).mp hpos).le]
      push_cast
      ring
    have hc : (Fintype.card s : ℝ) ≤ h + 1 := by exact_mod_cast hcard
    have hx := sq_nonneg (frobNorm ((1 - rangeProjector (truncatedSVD A (h + 1))) * W))
    rw [h3] at hx
    rw [hr] at h5
    have hθ0 : 0 ≤ 1 - θ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hgap hx, mul_le_mul_of_nonneg_left h5 hθ0,
      mul_le_mul_of_nonneg_left (sub_le_sub_right hc
        (frobNorm (rangeProjector (truncatedSVD A (h + 1)) * W) ^ 2))
        (mul_nonneg hθ0 (sq_nonneg (singularValues A h)))]

omit [DecidableEq m] [DecidableEq n] in
/-- **Small deficits and a gap give head capture**: for an orthogonal projector $\mathbf{P}$,
$L = h + 1$ and a relative gap $\theta \le 1$ with
$\sigma_L(\mathbf{A})^2 \le (1 - \theta)\,\sigma_h(\mathbf{A})^2$,
$$\theta\,\|\llbracket\mathbf{A}\rrbracket_L -
\mathbf{P}\llbracket\mathbf{A}\rrbracket_L\|_{\mathsf{F}}^2 \le
\sum_{i<L} \bigl(\sigma_i(\mathbf{A})^2 - \sigma_i(\mathbf{P}\mathbf{A})^2\bigr)\,.$$
The frame form `NLAlib.HasOrthonormalCols.mul_frobNorm_truncatedSVD_sub_mul_sq_le` at a frame of
the column space of $\llbracket\mathbf{P}\mathbf{A}\rrbracket_L$.
[BakshiClarksonWoodruff2022, Corollary 3.7]; there for a basis of the range of
$\mathbf{A}^{\mathsf{T}}\mathbf{W}$ and an unspecified polynomial accuracy, here one-sided, for
any projector, with the sum of the deficits on the right. -/
theorem _root_.IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) {h L : ℕ} (hL : h + 1 = L) {θ : ℝ}
    (hθ : θ ≤ 1) (hgap : singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2) :
    θ * frobNorm (truncatedSVD A L - P * truncatedSVD A L) ^ 2 ≤
      ∑ i ∈ Finset.range L, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := by
  classical
  have hPR := hP.mul_rangeProjector_truncatedSVD_mul A L
  have hRA := hP.rangeProjector_truncatedSVD_mul_mul A L
  set Y := truncatedSVD (P * A) L
  set X := truncatedSVD A L
  obtain ⟨W, hW, hWr⟩ :=
    exists_hasOrthonormalCols_range_eq (p := Fin Y.rank) Y (Fintype.card_fin _)
  have hWW : W * Wᴴ = rangeProjector Y := by
    rw [← hW.rangeProjector_eq, rangeProjector_inj.mpr hWr]
  have hdef : 0 ≤ ∑ i ∈ Finset.range L,
      (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) :=
    Finset.sum_nonneg fun i _ => sub_nonneg.mpr
      (pow_le_pow_left₀ (singularValues_nonneg _ _) (hP.singularValues_mul_le A i) 2)
  -- the energy of the frame is that of `⟦PA⟧_L`
  have hη : ∑ i ∈ Finset.range L, singularValues A i ^ 2 - ∑ i ∈ Finset.range L,
      (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) ≤ frobNorm (Aᴴ * W) ^ 2 := by
    have e : frobNorm (Aᴴ * W) = frobNorm Y := by
      rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        ← hW.frobNorm_mul_left, ← Matrix.mul_assoc, hWW, hRA]
    rw [e, frobNorm_truncatedSVD_sq, Finset.sum_sub_distrib, sub_sub_cancel]
  have h := hW.mul_frobNorm_truncatedSVD_sub_mul_sq_le A hL
    (by rw [Fintype.card_fin]; exact rank_truncatedSVD_le _ _) hθ hgap hη
  rw [hWW] at h
  rcases lt_or_ge θ 0 with hθ0 | hθ0
  · nlinarith [sq_nonneg (frobNorm (X - P * X))]
  -- `P` captures at least what `Π ≤ P` captures
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hθ0) h
  have e : X - P * X = (1 - P) * (X - rangeProjector Y * X) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, ← Matrix.mul_assoc, hPR]
    abel
  rw [e]
  exact pow_le_pow_left₀ (frobNorm_nonneg _) (hP.one_sub.frobNorm_mul_le _) 2

end NLAlib
