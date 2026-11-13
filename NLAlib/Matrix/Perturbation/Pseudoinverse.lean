/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Subspaces.ProjectorPair

/-!
# Perturbation of the pseudoinverse

The pseudoinverse is not continuous: the rank can jump. Wedin's decomposition of
$\mathbf{B}^{+} - \mathbf{A}^{+}$ into three terms gives bounds in terms of $\|\mathbf{A}^{+}\|_2$
and $\|\mathbf{B}^{+}\|_2$, with the constant $(1 + \sqrt{5})/2$ in the spectral norm and $\sqrt{2}$
in the equal-rank Frobenius bound. When the ranks agree and the perturbation is small,
the bound controls $\|\mathbf{B}^{+}\|_2$ in terms of $\|\mathbf{A}^{+}\|_2$.

## Main results

* `NLAlib.pinv_sub_pinv`: Wedin's decomposition.
* `NLAlib.SymmetricGauge.matrixNorm_pinv_sub_pinv_le`: the bound in every unitarily invariant
  norm.
* `NLAlib.specNorm_pinv_sub_pinv_le_goldenRatio_mul_max`: the spectral norm constant.
* `NLAlib.SymmetricGauge.matrixNorm_pinv_sub_pinv_le_three_mul_of_rank_eq`,
  `NLAlib.specNorm_pinv_sub_pinv_le_goldenRatio_mul_of_rank_eq`,
  `NLAlib.frobNorm_pinv_sub_pinv_le_sqrt_two_mul_of_rank_eq`: bounds for equal ranks.
* `NLAlib.specNorm_pinv_le_div_of_rank_eq`: control of $\|\mathbf{B}^{+}\|_2$ for equal ranks.
* `NLAlib.specNorm_rangeProjector_sub_rangeProjector_le`: perturbation of the range projector.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Wedin's decomposition -/

/-- $\mathbf{B}^{+}(\mathbf{B}^{+})^{\mathsf{H}}\mathbf{B}^{\mathsf{H}} = \mathbf{B}^{+}$. -/
private theorem pinv_mul_conjTranspose_pinv_mul_conjTranspose (B : Matrix m n 𝕜) :
    pinv B * (pinv B)ᴴ * Bᴴ = pinv B := by
  rw [Matrix.mul_assoc, ← Matrix.conjTranspose_mul, (isPinv_pinv B).isHermitian_left.eq,
    ← Matrix.mul_assoc, pinv_mul_mul_pinv]

/-- $\mathbf{A}^{\mathsf{H}}(\mathbf{A}^{+})^{\mathsf{H}}\mathbf{A}^{+} = \mathbf{A}^{+}$. -/
private theorem conjTranspose_mul_conjTranspose_pinv_mul_pinv (A : Matrix m n 𝕜) :
    Aᴴ * (pinv A)ᴴ * pinv A = pinv A := by
  rw [← Matrix.conjTranspose_mul, (isPinv_pinv A).isHermitian_right.eq, pinv_mul_mul_pinv]

/-- $\mathbf{A}^{+}\mathbf{P}_{\mathbf{A}} = \mathbf{A}^{+}$. -/
private theorem pinv_mul_rangeProjector (A : Matrix m n 𝕜) :
    pinv A * rangeProjector A = pinv A := by
  rw [← mul_pinv, ← Matrix.mul_assoc, pinv_mul_mul_pinv]

/-- $\mathbf{P}_{\mathbf{A}^{\mathsf{H}}}\mathbf{A}^{+} = \mathbf{A}^{+}$. -/
private theorem rangeProjector_conjTranspose_mul_pinv (A : Matrix m n 𝕜) :
    rangeProjector Aᴴ * pinv A = pinv A := by
  rw [← pinv_mul, pinv_mul_mul_pinv]

/-- $\mathbf{A}^{+}(\mathbf{I} - \mathbf{P}_{\mathbf{A}}) = \mathbf{0}$. -/
private theorem pinv_mul_one_sub_rangeProjector [DecidableEq m] (A : Matrix m n 𝕜) :
    pinv A * (1 - rangeProjector A) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, pinv_mul_rangeProjector, sub_self]

/-- $(\mathbf{I} - \mathbf{P}_{\mathbf{A}^{\mathsf{H}}})\mathbf{A}^{+} = \mathbf{0}$. -/
private theorem one_sub_rangeProjector_conjTranspose_mul_pinv [DecidableEq n] (A : Matrix m n 𝕜) :
    (1 - rangeProjector Aᴴ) * pinv A = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_conjTranspose_mul_pinv, sub_self]

/-- The second term of Wedin's decomposition is
$\mathbf{B}^{+}(\mathbf{I} - \mathbf{P}_{\mathbf{A}})$. -/
private theorem pinv_mul_conjTranspose_mul_one_sub_rangeProjector [DecidableEq m]
    (A B : Matrix m n 𝕜) :
    pinv B * (pinv B)ᴴ * (B - A)ᴴ * (1 - rangeProjector A) =
      pinv B * (1 - rangeProjector A) := by
  rw [Matrix.conjTranspose_sub, Matrix.mul_sub (pinv B * (pinv B)ᴴ), Matrix.sub_mul,
    pinv_mul_conjTranspose_pinv_mul_conjTranspose, Matrix.mul_assoc _ Aᴴ,
    conjTranspose_mul_one_sub_rangeProjector, Matrix.mul_zero, sub_zero]

/-- The third term of Wedin's decomposition is
$-(\mathbf{I} - \mathbf{P}_{\mathbf{B}^{\mathsf{H}}})\mathbf{A}^{+}$. -/
private theorem one_sub_rangeProjector_mul_conjTranspose_mul_pinv [DecidableEq n]
    (A B : Matrix m n 𝕜) :
    (1 - rangeProjector Bᴴ) * (B - A)ᴴ * (pinv A)ᴴ * pinv A =
      -((1 - rangeProjector Bᴴ) * pinv A) := by
  rw [Matrix.conjTranspose_sub, Matrix.mul_sub, one_sub_rangeProjector_mul_self, zero_sub,
    Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ,
    conjTranspose_mul_conjTranspose_pinv_mul_pinv]

/-- **Wedin's decomposition** of the difference of two pseudoinverses:
$$\begin{aligned}
  \mathbf{B}^{+} - \mathbf{A}^{+} &= -\mathbf{B}^{+}(\mathbf{B} - \mathbf{A})\mathbf{A}^{+} +
    \mathbf{B}^{+}(\mathbf{B}^{+})^{\mathsf{H}}(\mathbf{B} - \mathbf{A})^{\mathsf{H}}
    (\mathbf{I} - \mathbf{A}\mathbf{A}^{+}) \\
  &\quad + (\mathbf{I} - \mathbf{B}^{+}\mathbf{B})(\mathbf{B} - \mathbf{A})^{\mathsf{H}}
    (\mathbf{A}^{+})^{\mathsf{H}}\mathbf{A}^{+}.
\end{aligned}$$
[Wedin1973, Theorem 4.1]; [StewartSun1990, Theorem III.3.10].
Result: pseudoinverse-perturbation -/
theorem pinv_sub_pinv [DecidableEq m] [DecidableEq n] (A B : Matrix m n 𝕜) :
    pinv B - pinv A =
      -(pinv B * (B - A) * pinv A) + pinv B * (pinv B)ᴴ * (B - A)ᴴ * (1 - A * pinv A) +
        (1 - pinv B * B) * (B - A)ᴴ * (pinv A)ᴴ * pinv A := by
  rw [mul_pinv, pinv_mul, pinv_mul_conjTranspose_mul_one_sub_rangeProjector,
    one_sub_rangeProjector_mul_conjTranspose_mul_pinv, ← mul_pinv A, ← pinv_mul B]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  abel

/-! ### The four blocks of the difference

Relative to the projectors $\mathbf{P}_{\mathbf{A}}$ on the right and
$\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ on the left, $\mathbf{B}^{+} - \mathbf{A}^{+}$ has three
nonzero blocks, which are the three terms of Wedin's decomposition. -/

private theorem rangeProjector_mul_pinv_sub_pinv_mul_rangeProjector (A B : Matrix m n 𝕜) :
    rangeProjector Bᴴ * (pinv B - pinv A) * rangeProjector A = -(pinv B * (B - A) * pinv A) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, rangeProjector_conjTranspose_mul_pinv,
    Matrix.mul_assoc _ (pinv A), pinv_mul_rangeProjector, ← mul_pinv A, ← pinv_mul B]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

private theorem rangeProjector_mul_pinv_sub_pinv_mul_one_sub [DecidableEq m] (A B : Matrix m n 𝕜) :
    rangeProjector Bᴴ * (pinv B - pinv A) * (1 - rangeProjector A) =
      pinv B * (1 - rangeProjector A) := by
  rw [Matrix.mul_sub (rangeProjector Bᴴ), Matrix.sub_mul, rangeProjector_conjTranspose_mul_pinv,
    Matrix.mul_assoc _ (pinv A), pinv_mul_one_sub_rangeProjector, Matrix.mul_zero, sub_zero]

private theorem one_sub_mul_pinv_sub_pinv_mul_rangeProjector [DecidableEq n] (A B : Matrix m n 𝕜) :
    (1 - rangeProjector Bᴴ) * (pinv B - pinv A) * rangeProjector A =
      -((1 - rangeProjector Bᴴ) * pinv A) := by
  rw [Matrix.mul_sub, one_sub_rangeProjector_conjTranspose_mul_pinv, zero_sub, Matrix.neg_mul,
    Matrix.mul_assoc, pinv_mul_rangeProjector]

private theorem one_sub_mul_pinv_sub_pinv_mul_one_sub [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n 𝕜) :
    (1 - rangeProjector Bᴴ) * (pinv B - pinv A) * (1 - rangeProjector A) = 0 := by
  rw [Matrix.mul_sub (1 - rangeProjector Bᴴ) (pinv B),
    one_sub_rangeProjector_conjTranspose_mul_pinv, zero_sub, Matrix.neg_mul, Matrix.mul_assoc,
    pinv_mul_one_sub_rangeProjector, Matrix.mul_zero, neg_zero]

/-- A product of three factors, the outer two measured in the spectral norm. -/
private theorem matrixNorm_mul_mul_le (Φ : SymmetricGauge) {l p : Type*} [Fintype l] [Fintype p]
    (X : Matrix l m 𝕜) (Y : Matrix m n 𝕜) (Z : Matrix n p 𝕜) :
    Φ.matrixNorm (X * Y * Z) ≤ specNorm X * Φ.matrixNorm Y * specNorm Z :=
  (Φ.matrixNorm_mul_le_mul_specNorm _ _).trans
    (mul_le_mul_of_nonneg_right (Φ.matrixNorm_mul_le_specNorm_mul _ _) (specNorm_nonneg _))

/-- The diagonal block: $\|\mathbf{B}^{+}(\mathbf{B} - \mathbf{A})\mathbf{A}^{+}\|_{\Phi}
\le \|\mathbf{B}^{+}\|_2 \|\mathbf{A}^{+}\|_2 \|\mathbf{B} - \mathbf{A}\|_{\Phi}$. -/
private theorem matrixNorm_pinv_mul_sub_mul_pinv_le (Φ : SymmetricGauge) (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (pinv B * (B - A) * pinv A) ≤
      specNorm (pinv B) * specNorm (pinv A) * Φ.matrixNorm (B - A) := by
  refine (matrixNorm_mul_mul_le Φ _ _ _).trans_eq ?_
  ring

/-- The block $\mathbf{B}^{+}(\mathbf{I} - \mathbf{P}_{\mathbf{A}})$:
$\|\mathbf{B}^{+}(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\|_{\Phi}
\le \|\mathbf{B}^{+}\|_2^2 \|\mathbf{B} - \mathbf{A}\|_{\Phi}$. -/
private theorem matrixNorm_pinv_mul_one_sub_rangeProjector_le [DecidableEq m] (Φ : SymmetricGauge)
    (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (pinv B * (1 - rangeProjector A)) ≤
      specNorm (pinv B) ^ 2 * Φ.matrixNorm (B - A) := by
  rw [← pinv_mul_conjTranspose_mul_one_sub_rangeProjector, ← specNorm_mul_conjTranspose_self,
    ← Φ.matrixNorm_conjTranspose (B - A)]
  refine (matrixNorm_mul_mul_le Φ _ _ _).trans ?_
  exact mul_le_of_le_one_right (mul_nonneg (specNorm_nonneg _) (Φ.matrixNorm_nonneg _))
    (isStarProjection_one_sub_rangeProjector A).specNorm_le_one

/-- The block $(\mathbf{I} - \mathbf{P}_{\mathbf{B}^{\mathsf{H}}})\mathbf{A}^{+}$:
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}^{\mathsf{H}}})\mathbf{A}^{+}\|_{\Phi}
\le \|\mathbf{A}^{+}\|_2^2 \|\mathbf{B} - \mathbf{A}\|_{\Phi}$. -/
private theorem matrixNorm_one_sub_rangeProjector_mul_pinv_le [DecidableEq n] (Φ : SymmetricGauge)
    (A B : Matrix m n 𝕜) :
    Φ.matrixNorm ((1 - rangeProjector Bᴴ) * pinv A) ≤
      specNorm (pinv A) ^ 2 * Φ.matrixNorm (B - A) := by
  rw [← Φ.matrixNorm_neg, ← one_sub_rangeProjector_mul_conjTranspose_mul_pinv,
    ← specNorm_conjTranspose_mul_self, ← Φ.matrixNorm_conjTranspose (B - A),
    Matrix.mul_assoc _ (pinv A)ᴴ]
  refine (matrixNorm_mul_mul_le Φ _ _ _).trans ?_
  rw [mul_comm (specNorm _ * _)]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (Φ.matrixNorm_nonneg _)
    (isStarProjection_one_sub_rangeProjector Bᴴ).specNorm_le_one) (specNorm_nonneg _)

/-- $\mathbf{B}^{+} - \mathbf{A}^{+}$ as the sum of its three nonzero blocks. -/
private theorem pinv_sub_pinv_eq_add_add [DecidableEq m] [DecidableEq n] (A B : Matrix m n 𝕜) :
    pinv B - pinv A = -(pinv B * (B - A) * pinv A) + pinv B * (1 - rangeProjector A) +
      -((1 - rangeProjector Bᴴ) * pinv A) := by
  rw [← pinv_mul_conjTranspose_mul_one_sub_rangeProjector,
    ← one_sub_rangeProjector_mul_conjTranspose_mul_pinv, ← mul_pinv, ← pinv_mul]
  exact pinv_sub_pinv A B

/-- **Perturbation of the pseudoinverse in every unitarily invariant norm** $\|\cdot\|_{\Phi}$:
$$\|\mathbf{B}^{+} - \mathbf{A}^{+}\|_{\Phi}
  \le \bigl(\|\mathbf{B}^{+}\|_2 \|\mathbf{A}^{+}\|_2 + \|\mathbf{B}^{+}\|_2^2 +
  \|\mathbf{A}^{+}\|_2^2\bigr) \|\mathbf{B} - \mathbf{A}\|_{\Phi}.$$
[Wedin1973]; [StewartSun1990, Theorem III.3.8].
Result: pseudoinverse-perturbation -/
theorem SymmetricGauge.matrixNorm_pinv_sub_pinv_le (Φ : SymmetricGauge) (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (pinv B - pinv A) ≤
      (specNorm (pinv B) * specNorm (pinv A) + specNorm (pinv B) ^ 2 + specNorm (pinv A) ^ 2) *
        Φ.matrixNorm (B - A) := by
  classical
  have h1 := matrixNorm_pinv_mul_sub_mul_pinv_le Φ A B
  have h2 := matrixNorm_pinv_mul_one_sub_rangeProjector_le Φ A B
  have h3 := matrixNorm_one_sub_rangeProjector_mul_pinv_le Φ A B
  rw [pinv_sub_pinv_eq_add_add A B, add_mul, add_mul]
  refine (Φ.matrixNorm_add_le _ _).trans (add_le_add ((Φ.matrixNorm_add_le _ _).trans
    (add_le_add ?_ h2)) ?_)
  · rwa [Φ.matrixNorm_neg]
  · rwa [Φ.matrixNorm_neg]

/-- $\|\mathbf{B}^{+} - \mathbf{A}^{+}\|_{\Phi} \le 3 \max(\|\mathbf{A}^{+}\|_2^2,
\|\mathbf{B}^{+}\|_2^2) \, \|\mathbf{B} - \mathbf{A}\|_{\Phi}$ in every unitarily invariant norm
$\|\cdot\|_{\Phi}$. -/
theorem SymmetricGauge.matrixNorm_pinv_sub_pinv_le_three_mul_max (Φ : SymmetricGauge)
    (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (pinv B - pinv A) ≤
      3 * max (specNorm (pinv A) ^ 2) (specNorm (pinv B) ^ 2) * Φ.matrixNorm (B - A) := by
  refine (Φ.matrixNorm_pinv_sub_pinv_le A B).trans
    (mul_le_mul_of_nonneg_right ?_ (Φ.matrixNorm_nonneg _))
  have ha := le_max_left (specNorm (pinv A) ^ 2) (specNorm (pinv B) ^ 2)
  have hb := le_max_right (specNorm (pinv A) ^ 2) (specNorm (pinv B) ^ 2)
  nlinarith [sq_nonneg (specNorm (pinv B) - specNorm (pinv A))]

/-- **Wedin's bound in the spectral norm**, with the golden ratio:
$$\|\mathbf{B}^{+} - \mathbf{A}^{+}\|_2
  \le \frac{1 + \sqrt{5}}{2} \max\bigl(\|\mathbf{A}^{+}\|_2^2, \|\mathbf{B}^{+}\|_2^2\bigr)
  \|\mathbf{B} - \mathbf{A}\|_2.$$
[Wedin1973, Theorem 4.1]; [StewartSun1990, Theorem III.3.8].
Result: pseudoinverse-perturbation -/
theorem specNorm_pinv_sub_pinv_le_goldenRatio_mul_max (A B : Matrix m n 𝕜) :
    specNorm (pinv B - pinv A) ≤
      Real.goldenRatio * max (specNorm (pinv A) ^ 2) (specNorm (pinv B) ^ 2) *
        specNorm (B - A) := by
  classical
  have ha := le_max_left (specNorm (pinv A) ^ 2) (specNorm (pinv B) ^ 2)
  have hb := le_max_right (specNorm (pinv A) ^ 2) (specNorm (pinv B) ^ 2)
  have he := specNorm_nonneg (B - A)
  have h1 := matrixNorm_pinv_mul_sub_mul_pinv_le (lpGauge ⊤) A B
  have h2 := matrixNorm_pinv_mul_one_sub_rangeProjector_le (lpGauge ⊤) A B
  have h3 := matrixNorm_one_sub_rangeProjector_mul_pinv_le (lpGauge ⊤) A B
  rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm] at h1 h2 h3
  rw [mul_assoc]
  refine specNorm_le_goldenRatio_mul_of_one_sub_mul_mul_one_sub_eq_zero
    (isStarProjection_rangeProjector A) (isStarProjection_rangeProjector Bᴴ)
    (one_sub_mul_pinv_sub_pinv_mul_one_sub A B) ?_ ?_ ?_
  · rw [rangeProjector_mul_pinv_sub_pinv_mul_rangeProjector, specNorm_neg]
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ he)
    nlinarith [sq_nonneg (specNorm (pinv B) - specNorm (pinv A))]
  · rw [rangeProjector_mul_pinv_sub_pinv_mul_one_sub]
    exact h2.trans (mul_le_mul_of_nonneg_right hb he)
  · rw [one_sub_mul_pinv_sub_pinv_mul_rangeProjector, specNorm_neg]
    exact h3.trans (mul_le_mul_of_nonneg_right ha he)

/-! ### The range projector -/

/-- The part of the range of $\mathbf{A}$ outside the range of $\mathbf{B}$ is controlled by
$\mathbf{B} - \mathbf{A}$, in every unitarily invariant norm:
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{P}_{\mathbf{A}}\|_{\Phi}
\le \|\mathbf{A}^{+}\|_2
\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})(\mathbf{A} - \mathbf{B})\|_{\Phi}$. -/
theorem SymmetricGauge.matrixNorm_one_sub_rangeProjector_mul_rangeProjector_le [DecidableEq m]
    (Φ : SymmetricGauge) (A B : Matrix m n 𝕜) :
    Φ.matrixNorm ((1 - rangeProjector B) * rangeProjector A) ≤
      specNorm (pinv A) * Φ.matrixNorm ((1 - rangeProjector B) * (A - B)) := by
  have h : (1 - rangeProjector B) * rangeProjector A =
      (1 - rangeProjector B) * (A - B) * pinv A := by
    rw [Matrix.mul_sub, one_sub_rangeProjector_mul_self, sub_zero, Matrix.mul_assoc, mul_pinv]
  rw [h, mul_comm]
  exact Φ.matrixNorm_mul_le_mul_specNorm _ _

/-- **Perturbation of the range projector.** For matrices of equal rank,
$\|\mathbf{P}_{\mathbf{A}} - \mathbf{P}_{\mathbf{B}}\|_2
\le \min(\|\mathbf{A}^{+}\|_2, \|\mathbf{B}^{+}\|_2) \, \|\mathbf{B} - \mathbf{A}\|_2$.
[StewartSun1990, §III.3]; [Wedin1973]. -/
theorem specNorm_rangeProjector_sub_rangeProjector_le {A B : Matrix m n 𝕜} (h : A.rank = B.rank) :
    specNorm (rangeProjector A - rangeProjector B) ≤
      min (specNorm (pinv A)) (specNorm (pinv B)) * specNorm (B - A) := by
  classical
  have key : ∀ {A B : Matrix m n 𝕜}, A.rank = B.rank →
      specNorm (rangeProjector A - rangeProjector B) ≤ specNorm (pinv A) * specNorm (B - A) := by
    intro A B h
    have hr : (rangeProjector A).rank = (rangeProjector B).rank := by
      rw [rank_rangeProjector, rank_rangeProjector, h]
    have h1 := SymmetricGauge.matrixNorm_one_sub_rangeProjector_mul_rangeProjector_le
      (lpGauge ⊤) A B
    rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm] at h1
    rw [(isStarProjection_rangeProjector A).specNorm_sub_eq_of_rank_eq
      (isStarProjection_rangeProjector B) hr, specNorm_sub_comm B A]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (specNorm_one_sub_rangeProjector_mul_le B (A - B)) (specNorm_nonneg _))
  rw [min_mul_of_nonneg _ _ (specNorm_nonneg _)]
  refine le_min (key h) ?_
  rw [specNorm_sub_comm, specNorm_sub_comm B A]
  exact key h.symm

/-! ### Equal ranks -/

/-- For equal ranks, $\|\mathbf{B}^{+}(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\|_{\Phi}
\le \|\mathbf{A}^{+}\|_2 \|\mathbf{B}^{+}\|_2
\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})(\mathbf{B} - \mathbf{A})\|_{\Phi}$. -/
private theorem matrixNorm_pinv_mul_one_sub_rangeProjector_le_of_rank_eq [DecidableEq m]
    (Φ : SymmetricGauge) {A B : Matrix m n 𝕜} (h : A.rank = B.rank) :
    Φ.matrixNorm (pinv B * (1 - rangeProjector A)) ≤
      specNorm (pinv A) * specNorm (pinv B) *
        Φ.matrixNorm ((1 - rangeProjector B) * (B - A)) := by
  have hPA := isStarProjection_rangeProjector A
  have hPB := isStarProjection_rangeProjector B
  have hr : (rangeProjector B).rank = (rangeProjector A).rank := by
    rw [rank_rangeProjector, rank_rangeProjector, h]
  have h1 : pinv B * (1 - rangeProjector A) =
      pinv B * ((1 - rangeProjector A) * rangeProjector B)ᴴ := by
    rw [Matrix.conjTranspose_mul, hPB.conjTranspose_eq, hPA.one_sub.conjTranspose_eq,
      ← Matrix.mul_assoc, pinv_mul_rangeProjector]
  have h2 : (1 - rangeProjector B) * (B - A) = -((1 - rangeProjector B) * (A - B)) := by
    rw [← Matrix.mul_neg, neg_sub]
  rw [h1, h2, Φ.matrixNorm_neg, mul_comm (specNorm (pinv A)), mul_assoc]
  refine (Φ.matrixNorm_mul_le_specNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_left ?_ (specNorm_nonneg _))
  rw [Φ.matrixNorm_conjTranspose, hPB.matrixNorm_one_sub_mul_eq_of_rank_eq Φ hPA hr]
  exact Φ.matrixNorm_one_sub_rangeProjector_mul_rangeProjector_le A B

open scoped ComplexOrder in
/-- For equal ranks, $\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}^{\mathsf{H}}})\mathbf{A}^{+}\|_{\Phi}
\le \|\mathbf{A}^{+}\|_2 \|\mathbf{B}^{+}\|_2
\|(\mathbf{B} - \mathbf{A})(\mathbf{I} - \mathbf{P}_{\mathbf{A}^{\mathsf{H}}})\|_{\Phi}$. -/
private theorem matrixNorm_one_sub_rangeProjector_mul_pinv_le_of_rank_eq [DecidableEq n]
    (Φ : SymmetricGauge) {A B : Matrix m n 𝕜} (h : A.rank = B.rank) :
    Φ.matrixNorm ((1 - rangeProjector Bᴴ) * pinv A) ≤
      specNorm (pinv A) * specNorm (pinv B) *
        Φ.matrixNorm ((B - A) * (1 - rangeProjector Aᴴ)) := by
  have h1 := matrixNorm_pinv_mul_one_sub_rangeProjector_le_of_rank_eq Φ (A := Bᴴ) (B := Aᴴ)
    (by rw [Matrix.rank_conjTranspose, Matrix.rank_conjTranspose, h])
  have h2 : pinv Aᴴ * (1 - rangeProjector Bᴴ) = ((1 - rangeProjector Bᴴ) * pinv A)ᴴ := by
    rw [Matrix.conjTranspose_mul, pinv_conjTranspose,
      (isStarProjection_one_sub_rangeProjector Bᴴ).conjTranspose_eq]
  have h3 : (1 - rangeProjector Aᴴ) * (Aᴴ - Bᴴ) = -((B - A) * (1 - rangeProjector Aᴴ))ᴴ := by
    rw [Matrix.conjTranspose_mul, (isStarProjection_one_sub_rangeProjector Aᴴ).conjTranspose_eq,
      Matrix.conjTranspose_sub, ← Matrix.mul_neg, neg_sub]
  rw [h2, h3, Φ.matrixNorm_neg, Φ.matrixNorm_conjTranspose, Φ.matrixNorm_conjTranspose,
    pinv_conjTranspose, pinv_conjTranspose, specNorm_conjTranspose, specNorm_conjTranspose,
    mul_comm (specNorm (pinv B))] at h1
  exact h1

/-- **Perturbation of the pseudoinverse for equal ranks**, every unitarily invariant norm:
$\|\mathbf{B}^{+} - \mathbf{A}^{+}\|_{\Phi} \le 3 \|\mathbf{A}^{+}\|_2 \|\mathbf{B}^{+}\|_2
\|\mathbf{B} - \mathbf{A}\|_{\Phi}$ when
$\operatorname{rank} \mathbf{A} = \operatorname{rank} \mathbf{B}$. The constant improves to
$(1 + \sqrt{5})/2$ in the spectral norm and to $\sqrt{2}$ in the Frobenius norm. [Wedin1973];
[StewartSun1990, Theorem III.3.9].
Result: pseudoinverse-perturbation -/
theorem SymmetricGauge.matrixNorm_pinv_sub_pinv_le_three_mul_of_rank_eq (Φ : SymmetricGauge)
    {A B : Matrix m n 𝕜} (h : A.rank = B.rank) :
    Φ.matrixNorm (pinv B - pinv A) ≤
      3 * specNorm (pinv A) * specNorm (pinv B) * Φ.matrixNorm (B - A) := by
  classical
  have hab : 0 ≤ specNorm (pinv A) * specNorm (pinv B) :=
    mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have h1 := matrixNorm_pinv_mul_sub_mul_pinv_le Φ A B
  have h2 := (matrixNorm_pinv_mul_one_sub_rangeProjector_le_of_rank_eq Φ h).trans
    (mul_le_mul_of_nonneg_left (Φ.matrixNorm_mul_le_of_isStarProjection
      (isStarProjection_one_sub_rangeProjector B) (B - A)) hab)
  have h3 := (matrixNorm_one_sub_rangeProjector_mul_pinv_le_of_rank_eq Φ h).trans
    (mul_le_mul_of_nonneg_left ((Φ.matrixNorm_mul_le_mul_specNorm (B - A) _).trans
      (mul_le_of_le_one_right (Φ.matrixNorm_nonneg _)
        (isStarProjection_one_sub_rangeProjector Aᴴ).specNorm_le_one)) hab)
  have h4 := (Φ.matrixNorm_add_le (-(pinv B * (B - A) * pinv A) + pinv B * (1 - rangeProjector A))
    (-((1 - rangeProjector Bᴴ) * pinv A))).trans (add_le_add_left (Φ.matrixNorm_add_le _ _) _)
  rw [Φ.matrixNorm_neg, Φ.matrixNorm_neg, ← pinv_sub_pinv_eq_add_add] at h4
  linarith

/-- For matrices of equal rank, $\|\mathbf{B}^{+} - \mathbf{A}^{+}\|_2
\le ((1 + \sqrt{5})/2) \|\mathbf{A}^{+}\|_2 \|\mathbf{B}^{+}\|_2 \|\mathbf{B} - \mathbf{A}\|_2$.
[Wedin1973]; [StewartSun1990, Theorem III.3.9]. -/
theorem specNorm_pinv_sub_pinv_le_goldenRatio_mul_of_rank_eq {A B : Matrix m n 𝕜}
    (h : A.rank = B.rank) :
    specNorm (pinv B - pinv A) ≤
      Real.goldenRatio * specNorm (pinv A) * specNorm (pinv B) * specNorm (B - A) := by
  classical
  have hab : 0 ≤ specNorm (pinv A) * specNorm (pinv B) :=
    mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have h1 := matrixNorm_pinv_mul_sub_mul_pinv_le (lpGauge ⊤) A B
  have h2 := matrixNorm_pinv_mul_one_sub_rangeProjector_le_of_rank_eq (lpGauge ⊤) h
  have h3 := matrixNorm_one_sub_rangeProjector_mul_pinv_le_of_rank_eq (lpGauge ⊤) h
  rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm] at h1 h2 h3
  rw [mul_assoc, mul_assoc, ← mul_assoc (specNorm (pinv A))]
  refine specNorm_le_goldenRatio_mul_of_one_sub_mul_mul_one_sub_eq_zero
    (isStarProjection_rangeProjector A) (isStarProjection_rangeProjector Bᴴ)
    (one_sub_mul_pinv_sub_pinv_mul_one_sub A B) ?_ ?_ ?_
  · rw [rangeProjector_mul_pinv_sub_pinv_mul_rangeProjector, specNorm_neg,
      mul_comm (specNorm (pinv A))]
    exact h1
  · rw [rangeProjector_mul_pinv_sub_pinv_mul_one_sub]
    exact h2.trans (mul_le_mul_of_nonneg_left
      (specNorm_one_sub_rangeProjector_mul_le B (B - A)) hab)
  · rw [one_sub_mul_pinv_sub_pinv_mul_rangeProjector, specNorm_neg]
    exact h3.trans (mul_le_mul_of_nonneg_left
      ((isStarProjection_one_sub_rangeProjector Aᴴ).specNorm_mul_right_le (B - A)) hab)

/-- The three compressions of a matrix by two orthogonal projectors that appear in the blocks of
$\mathbf{B}^{+} - \mathbf{A}^{+}$ have squared Frobenius norms summing to at most twice that of the
matrix. -/
private theorem frobNorm_sq_add_add_le_two_mul [DecidableEq m] [DecidableEq n]
    {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (E : Matrix m n 𝕜) :
    frobNorm (P * E * Q) ^ 2 + frobNorm ((1 - P) * E) ^ 2 + frobNorm (E * (1 - Q)) ^ 2 ≤
      2 * frobNorm E ^ 2 := by
  have h1 := hP.frobNorm_sq_eq_add E
  have h2 := pow_le_pow_left₀ (frobNorm_nonneg _) (hQ.frobNorm_mul_right_le (P * E)) 2
  have h3 := pow_le_pow_left₀ (frobNorm_nonneg _) (hQ.one_sub.frobNorm_mul_right_le E) 2
  linarith

/-- For matrices of equal rank, $\|\mathbf{B}^{+} - \mathbf{A}^{+}\|_{\mathsf{F}}
\le \sqrt{2} \, \|\mathbf{A}^{+}\|_2 \|\mathbf{B}^{+}\|_2 \|\mathbf{B} - \mathbf{A}\|_{\mathsf{F}}$.
[Wedin1973]; [StewartSun1990, Theorem III.3.9]. -/
theorem frobNorm_pinv_sub_pinv_le_sqrt_two_mul_of_rank_eq {A B : Matrix m n 𝕜}
    (h : A.rank = B.rank) :
    frobNorm (pinv B - pinv A) ≤ √2 * specNorm (pinv A) * specNorm (pinv B) * frobNorm (B - A) := by
  classical
  have hP := isStarProjection_rangeProjector A
  have hQ := isStarProjection_rangeProjector Bᴴ
  have hab : 0 ≤ specNorm (pinv A) * specNorm (pinv B) :=
    mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have h1 : frobNorm (pinv B * (B - A) * pinv A) ≤ specNorm (pinv A) * specNorm (pinv B) *
      frobNorm (rangeProjector B * (B - A) * rangeProjector Aᴴ) := by
    have e : pinv B * (rangeProjector B * (B - A) * rangeProjector Aᴴ) * pinv A =
        pinv B * (B - A) * pinv A := by
      rw [Matrix.mul_assoc (rangeProjector B), ← Matrix.mul_assoc (pinv B),
        pinv_mul_rangeProjector, Matrix.mul_assoc (pinv B), Matrix.mul_assoc (B - A),
        rangeProjector_conjTranspose_mul_pinv, ← Matrix.mul_assoc]
    have h0 := matrixNorm_mul_mul_le (lpGauge 2) (pinv B)
      (rangeProjector B * (B - A) * rangeProjector Aᴴ) (pinv A)
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm, e] at h0
    exact h0.trans_eq (by ring)
  have h2 := matrixNorm_pinv_mul_one_sub_rangeProjector_le_of_rank_eq (lpGauge 2) h
  have h3 := matrixNorm_one_sub_rangeProjector_mul_pinv_le_of_rank_eq (lpGauge 2) h
  rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h2 h3
  have hsum := frobNorm_sq_add_add_le_two_mul (isStarProjection_rangeProjector B)
    (isStarProjection_rangeProjector Aᴴ) (B - A)
  have hZ : frobNorm (pinv B - pinv A) ^ 2 = frobNorm (pinv B * (B - A) * pinv A) ^ 2 +
      frobNorm (pinv B * (1 - rangeProjector A)) ^ 2 +
        frobNorm ((1 - rangeProjector Bᴴ) * pinv A) ^ 2 := by
    rw [hQ.frobNorm_sq_eq_add (pinv B - pinv A),
      hP.frobNorm_sq_eq_add_mul_right (rangeProjector Bᴴ * (pinv B - pinv A)),
      hP.frobNorm_sq_eq_add_mul_right ((1 - rangeProjector Bᴴ) * (pinv B - pinv A)),
      rangeProjector_mul_pinv_sub_pinv_mul_rangeProjector,
      rangeProjector_mul_pinv_sub_pinv_mul_one_sub, one_sub_mul_pinv_sub_pinv_mul_rangeProjector,
      one_sub_mul_pinv_sub_pinv_mul_one_sub, frobNorm_neg, frobNorm_neg, frobNorm_zero]
    ring
  have h1' := pow_le_pow_left₀ (frobNorm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (frobNorm_nonneg _) h2 2
  have h3' := pow_le_pow_left₀ (frobNorm_nonneg _) h3 2
  refine (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [hZ, mul_assoc √2, mul_assoc √2, mul_pow, Real.sq_sqrt zero_le_two, mul_pow]
  rw [mul_pow] at h1' h2' h3'
  nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg (specNorm (pinv A) * specNorm (pinv B)))]

/-- **Control of the perturbed pseudoinverse.** For matrices of equal rank with
$\|\mathbf{A}^{+}\|_2 \|\mathbf{B} - \mathbf{A}\|_2 < 1$,
$$\|\mathbf{B}^{+}\|_2
  \le \frac{\|\mathbf{A}^{+}\|_2}{1 - \|\mathbf{A}^{+}\|_2 \|\mathbf{B} - \mathbf{A}\|_2}.$$
[Wedin1973]; [StewartSun1990, Theorem III.3.8]. -/
theorem specNorm_pinv_le_div_of_rank_eq {A B : Matrix m n 𝕜} (h : A.rank = B.rank)
    (hsmall : specNorm (pinv A) * specNorm (B - A) < 1) :
    specNorm (pinv B) ≤ specNorm (pinv A) / (1 - specNorm (pinv A) * specNorm (B - A)) := by
  rcases Nat.eq_zero_or_pos A.rank with h0 | h0
  · obtain rfl : B = 0 := Matrix.rank_eq_zero.mp (h ▸ h0)
    rw [pinv_zero, specNorm_zero]
    exact div_nonneg (specNorm_nonneg _) (sub_nonneg.mpr hsmall.le)
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = A.rank := ⟨A.rank - 1, Nat.sub_add_cancel h0⟩
    have hsa : 0 < singularValues A k := (singularValues_pos_iff A).mpr (by omega)
    have hsb : 0 < singularValues B k := (singularValues_pos_iff B).mpr (by omega)
    have hw := (abs_sub_le_iff.mp (abs_singularValues_sub_le_specNorm A B k)).1
    rw [specNorm_sub_comm] at hw
    rw [specNorm_pinv A hk, inv_mul_lt_iff₀ hsa, mul_one] at hsmall
    rw [specNorm_pinv A hk, specNorm_pinv B (hk.trans h)]
    have e : (singularValues A k)⁻¹ / (1 - (singularValues A k)⁻¹ * specNorm (B - A)) =
        (singularValues A k - specNorm (B - A))⁻¹ := by
      have h1 : singularValues A k - specNorm (B - A) ≠ 0 := by linarith
      field_simp
    rw [e]
    exact inv_anti₀ (by linarith) (by linarith)

/-- A small perturbation of a matrix of full column rank has full column rank: if $\mathbf{A}$ has
full column rank and $\|\mathbf{A}^{+}\|_2 \|\mathbf{E}\|_2 < 1$, then $\mathbf{A} + \mathbf{E}$ has
full column rank. -/
theorem injective_mulVec_add_of_specNorm_pinv_mul_lt_one {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (hE : specNorm (pinv A) * specNorm E < 1) :
    Function.Injective (A + E).mulVec := by
  refine (injective_iff_map_eq_zero (A + E).mulVecLin).mpr fun x hx => ?_
  rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, add_eq_zero_iff_eq_neg] at hx
  have h1 := norm_le_specNorm_pinv_mul_norm_mulVec hA x
  rw [hx, WithLp.toLp_neg, norm_neg] at h1
  have h2 := mul_le_mul_of_nonneg_left (norm_toLp_mulVec_le E x) (specNorm_nonneg (pinv A))
  rw [← mul_assoc] at h2
  by_contra hne
  have hpos : 0 < ‖WithLp.toLp 2 x‖ := by
    rw [norm_pos_iff]
    exact fun h => hne (congrArg WithLp.ofLp h)
  nlinarith

/-- For $\mathbf{A}$ of full column rank and $\|\mathbf{A}^{+}\|_2 \|\mathbf{E}\|_2 < 1$,
$\|(\mathbf{A} + \mathbf{E})^{+}\|_2 \le \|\mathbf{A}^{+}\|_2 / (1 - \|\mathbf{A}^{+}\|_2
\|\mathbf{E}\|_2)$. -/
theorem specNorm_pinv_add_le_of_injective {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (hE : specNorm (pinv A) * specNorm E < 1) :
    specNorm (pinv (A + E)) ≤ specNorm (pinv A) / (1 - specNorm (pinv A) * specNorm E) := by
  have hB := injective_mulVec_add_of_specNorm_pinv_mul_lt_one hA hE
  have hr : A.rank = (A + E).rank :=
    (mulVec_injective_iff_rank_eq.mp hA).trans (mulVec_injective_iff_rank_eq.mp hB).symm
  have h := specNorm_pinv_le_div_of_rank_eq hr (by rwa [add_sub_cancel_left])
  rwa [add_sub_cancel_left] at h

end NLAlib
