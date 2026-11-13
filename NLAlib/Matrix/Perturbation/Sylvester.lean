/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Separation bounds for the Sylvester operator

For matrices $\mathbf{L}$ and $\mathbf{M}$ whose spectra are separated, the Sylvester operator
$\mathbf{X} \mapsto \mathbf{L}\mathbf{X} - \mathbf{X}\mathbf{M}$ is bounded below:
$\delta \|\mathbf{X}\|_{\Phi} \le \|\mathbf{L}\mathbf{X} - \mathbf{X}\mathbf{M}\|_{\Phi}$.
These bounds are the
engine of the $\sin \Theta$ theorems.

Two regimes are covered. When one spectrum lies in a disc and the other outside a larger concentric
disc (in particular: Hermitian $\mathbf{M}$ with spectrum in an interval and Hermitian $\mathbf{L}$
with spectrum outside a wider interval) the bound holds in every unitarily invariant norm. For
Hermitian matrices with arbitrarily interleaved spectra at distance $\delta$ it holds in the
Frobenius norm.

## Main results

* `NLAlib.SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul`: disc separation, any
  unitarily invariant norm.
* `NLAlib.SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_eigenvalue`: interval
  separation for Hermitian matrices.
* `Matrix.IsHermitian.mul_frobNorm_le_frobNorm_mul_sub_mul`: arbitrary separation, Frobenius norm.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Disc separation, every unitarily invariant norm -/

/-- **Sylvester separation bound, disc form.** If $\|\mathbf{M}\|_2 \le r$ and $\mathbf{L}$ is
bounded below by $r + \delta$, in the form $(r + \delta)^2 \mathbf{I}
\preceq \mathbf{L}^{\mathsf{H}}\mathbf{L}$, then $\delta \|\mathbf{X}\|_{\Phi}
\le \|\mathbf{L}\mathbf{X} - \mathbf{X}\mathbf{M}\|_{\Phi}$ in every unitarily invariant norm
$\|\cdot\|_{\Phi}$. Apply it to $\mathbf{L} - c\mathbf{I}$ and $\mathbf{M} - c\mathbf{I}$ for a disc
centred at $c$.
[Bhatia1997, Theorem VII.2.8]. -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul [DecidableEq m]
    (Φ : SymmetricGauge) {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} {r δ : ℝ} (hM : specNorm M ≤ r)
    (hL : ((r + δ) ^ 2) • (1 : Matrix m m 𝕜) ≤ Lᴴ * L) (X : Matrix m n 𝕜) :
    δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  have hr : 0 ≤ r := (specNorm_nonneg M).trans hM
  rcases le_or_gt (r + δ) 0 with h | h
  · have hδ : δ ≤ 0 := by linarith
    exact (mul_nonpos_of_nonpos_of_nonneg hδ (Φ.matrixNorm_nonneg X)).trans
      (Φ.matrixNorm_nonneg _)
  · have h₁ := Φ.mul_matrixNorm_le_of_sq_smul_one_le h.le hL X
    have h₂ : Φ.matrixNorm (L * X) ≤ Φ.matrixNorm (L * X - X * M) + Φ.matrixNorm X * r := by
      calc Φ.matrixNorm (L * X) = Φ.matrixNorm (L * X - X * M + X * M) := by rw [sub_add_cancel]
        _ ≤ Φ.matrixNorm (L * X - X * M) + Φ.matrixNorm (X * M) := Φ.matrixNorm_add_le _ _
        _ ≤ Φ.matrixNorm (L * X - X * M) + Φ.matrixNorm X * r := by
          gcongr
          exact (Φ.matrixNorm_mul_le_mul_specNorm X M).trans
            (mul_le_mul_of_nonneg_left hM (Φ.matrixNorm_nonneg X))
    linarith

/-! ### Interval separation for Hermitian matrices -/

/-- A Hermitian matrix with spectrum in $[a, b]$, that is
$a\mathbf{I} \preceq \mathbf{M} \preceq b\mathbf{I}$, is within $(b - a)/2$ of the midpoint:
$\|\mathbf{M} - c\mathbf{I}\|_2 \le (b - a)/2$ for $c = (a + b)/2$. The hypothesis $a \le b$ is
automatic unless the matrix has size zero. -/
theorem specNorm_sub_smul_one_le_of_le [DecidableEq n] {M : Matrix n n 𝕜} {a b : ℝ}
    (hab : a ≤ b) (h₁ : a • (1 : Matrix n n 𝕜) ≤ M) (h₂ : M ≤ b • (1 : Matrix n n 𝕜)) :
    specNorm (M - ((a + b) / 2) • (1 : Matrix n n 𝕜)) ≤ (b - a) / 2 := by
  have hH : (M - ((a + b) / 2) • (1 : Matrix n n 𝕜)).IsHermitian :=
    (isHermitian_of_le_smul_one h₂).sub (isHermitian_real_smul_one _)
  refine hH.specNorm_le_of_le_smul_one (by linarith) ?_ ?_
  · rw [neg_le_sub_iff_le_add, ← sub_le_iff_le_add, ← sub_smul]
    convert h₁ using 2
    ring
  · rw [sub_le_iff_le_add, ← add_smul]
    convert h₂ using 2
    ring

/-- A Hermitian matrix whose eigenvalues are at distance at least $s \ge 0$ from $c$ is bounded
below by $s$ after the shift: $s^2 \mathbf{I}
\preceq (\mathbf{L} - c\mathbf{I})^{\mathsf{H}}(\mathbf{L} - c\mathbf{I})$. -/
theorem _root_.Matrix.IsHermitian.sq_smul_one_le_sub_smul_one_conjTranspose_mul_self
    [DecidableEq m] {L : Matrix m m 𝕜} (hL : L.IsHermitian) {s c : ℝ} (hs : 0 ≤ s)
    (h : ∀ i, i < Fintype.card m → s ≤ |eigenvalue L i - c|) :
    (s ^ 2) • (1 : Matrix m m 𝕜) ≤
      (L - c • (1 : Matrix m m 𝕜))ᴴ * (L - c • (1 : Matrix m m 𝕜)) := by
  obtain ⟨U, hU, hLU⟩ := hL.exists_eq_mul_diagonal_mul_conjTranspose
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  rw [smul_one_le_conjTranspose_mul_self_iff]
  intro x
  have hx : x = U *ᵥ (Uᴴ *ᵥ x) := by rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hLx : (L - c • (1 : Matrix m m 𝕜)) *ᵥ x =
      U *ᵥ fun i => ((eigenvalue L i - c : ℝ) : 𝕜) * (Uᴴ *ᵥ x) i := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    nth_rewrite 1 [hLU]
    nth_rewrite 2 [hx]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul,
      ← Matrix.mulVec_sub]
    congr 1
    ext i
    rw [Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply, RCLike.real_smul_eq_coe_mul,
      RCLike.ofReal_sub, sub_mul]
  rw [hLx, hU.norm_toLp_mulVec]
  nth_rewrite 1 [hx]
  rw [hU.norm_toLp_mulVec, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← sq_abs (eigenvalue L i - c)]
  exact pow_le_pow_left₀ hs (h i i.2) 2

/-- **Sylvester separation bound, interval form.** For Hermitian $\mathbf{L}$ and $\mathbf{M}$, if
the spectrum of $\mathbf{M}$ lies in $[a, b]$ (that is,
$a\mathbf{I} \preceq \mathbf{M} \preceq b\mathbf{I}$) and every eigenvalue of $\mathbf{L}$ lies
outside $(a - \delta, b + \delta)$, then $\delta \|\mathbf{X}\|_{\Phi}
\le \|\mathbf{L}\mathbf{X} - \mathbf{X}\mathbf{M}\|_{\Phi}$ in every unitarily invariant norm
$\|\cdot\|_{\Phi}$.
[Bhatia1997, Theorem VII.2.8 and §VII.3]; [DavisKahan1970].
Result: sylvester-separation -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_eigenvalue [DecidableEq n]
    (Φ : SymmetricGauge) {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} (hL : L.IsHermitian) {a b δ : ℝ}
    (hM₁ : a • (1 : Matrix n n 𝕜) ≤ M) (hM₂ : M ≤ b • (1 : Matrix n n 𝕜))
    (hLsep : ∀ i, i < Fintype.card m → eigenvalue L i ≤ a - δ ∨ b + δ ≤ eigenvalue L i)
    (X : Matrix m n 𝕜) : δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  classical
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ (Φ.matrixNorm_nonneg X)).trans
      (Φ.matrixNorm_nonneg _)
  rcases isEmpty_or_nonempty n with hn | ⟨⟨j⟩⟩
  · rw [Subsingleton.elim X 0, SymmetricGauge.matrixNorm_zero, mul_zero]
    exact Φ.matrixNorm_nonneg _
  have hab : a ≤ b := by
    have h := re_quadForm_le_re_quadForm_of_le (hM₁.trans hM₂) (Pi.single j 1)
    rw [re_quadForm_real_smul_one, re_quadForm_real_smul_one, PiLp.toLp_single,
      PiLp.norm_single, norm_one, one_pow, mul_one, mul_one] at h
    exact h
  have h₁ := specNorm_sub_smul_one_le_of_le hab hM₁ hM₂
  have h₂ := hL.sq_smul_one_le_sub_smul_one_conjTranspose_mul_self (s := (b - a) / 2 + δ)
    (c := (a + b) / 2) (by linarith) fun i hi => by
      rw [le_abs]
      rcases hLsep i hi with h | h
      · right
        linarith
      · left
        linarith
  have h₃ := Φ.mul_matrixNorm_le_matrixNorm_mul_sub_mul h₁ h₂ X
  have heq : (L - ((a + b) / 2) • (1 : Matrix m m 𝕜)) * X -
      X * (M - ((a + b) / 2) • (1 : Matrix n n 𝕜)) = L * X - X * M := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, sub_sub_sub_cancel_right]
  rwa [heq] at h₃

/-- **Sylvester separation bound, one-sided form.** If
$\mathbf{L} \preceq (\alpha - \delta)\mathbf{I}$ and $\alpha\mathbf{I} \preceq \mathbf{M}$, then
$\delta \|\mathbf{X}\|_{\Phi} \le \|\mathbf{L}\mathbf{X} - \mathbf{X}\mathbf{M}\|_{\Phi}$ in every
unitarily invariant norm $\|\cdot\|_{\Phi}$.
[Bhatia1997, §VII.2, Theorem VII.2.3]. -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_le [DecidableEq m]
    [DecidableEq n] (Φ : SymmetricGauge) {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} {α δ : ℝ}
    (hL : L ≤ (α - δ) • (1 : Matrix m m 𝕜)) (hM : α • (1 : Matrix n n 𝕜) ≤ M)
    (X : Matrix m n 𝕜) : δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  have hLh : L.IsHermitian := isHermitian_of_le_smul_one hL
  refine Φ.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_eigenvalue hLh hM
    (isHermitian_of_smul_one_le hM).le_specNorm_smul_one (fun i hi => Or.inl ?_) X
  have h := eigenvalue_le_eigenvalue_of_le hL hLh i
  rwa [eigenvalue_real_smul_one _ hi] at h

/-- The one-sided form with $\mathbf{L}$ above $\mathbf{M}$: if
$(\alpha + \delta)\mathbf{I} \preceq \mathbf{L}$ and $\mathbf{M} \preceq \alpha\mathbf{I}$, then
$\delta \|\mathbf{X}\|_{\Phi} \le \|\mathbf{L}\mathbf{X} - \mathbf{X}\mathbf{M}\|_{\Phi}$. -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_ge [DecidableEq m]
    [DecidableEq n] (Φ : SymmetricGauge) {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} {α δ : ℝ}
    (hL : (α + δ) • (1 : Matrix m m 𝕜) ≤ L) (hM : M ≤ α • (1 : Matrix n n 𝕜))
    (X : Matrix m n 𝕜) : δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  have hMh : M.IsHermitian := isHermitian_of_le_smul_one hM
  have hM₁ : (-specNorm M) • (1 : Matrix n n 𝕜) ≤ M := by
    rw [neg_smul]
    exact hMh.neg_specNorm_smul_one_le
  refine Φ.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_eigenvalue (isHermitian_of_smul_one_le hL)
    hM₁ hM (fun i hi => Or.inr ?_) X
  have h := eigenvalue_le_eigenvalue_of_le hL (isHermitian_real_smul_one _) i
  rwa [eigenvalue_real_smul_one _ hi] at h

/-! ### Arbitrary separation, Frobenius norm -/

/-- Simultaneous diagonalisation of the Sylvester operator of two Hermitian matrices: in eigenvector
bases of $\mathbf{L}$ and $\mathbf{M}$ it multiplies the entry $(i, j)$ by
$\lambda_i(\mathbf{L}) - \lambda_j(\mathbf{M})$. -/
private theorem exists_conjTranspose_mul_mul_sub_mul_mul_apply {L : Matrix m m 𝕜}
    {M : Matrix n n 𝕜} (hL : L.IsHermitian) (hM : M.IsHermitian) (X : Matrix m n 𝕜) :
    ∃ (U : Matrix m (Fin (Fintype.card m)) 𝕜) (V : Matrix n (Fin (Fintype.card n)) 𝕜),
      HasOrthonormalCols U ∧ HasOrthonormalCols V ∧ ∀ i j,
        (Uᴴ * (L * X - X * M) * V) i j =
          ((eigenvalue L i - eigenvalue M j : ℝ) : 𝕜) * (Uᴴ * X * V) i j := by
  classical
  obtain ⟨U, hU, hLU⟩ := hL.exists_mul_eq_mul_diagonal
  obtain ⟨V, hV, hMV⟩ := hM.exists_mul_eq_mul_diagonal
  refine ⟨U, V, hU, hV, fun i j => ?_⟩
  have hUL : Uᴴ * L =
      (Matrix.diagonal fun i : Fin (Fintype.card m) => ((eigenvalue L i : ℝ) : 𝕜)) * Uᴴ := by
    have h := congrArg Matrix.conjTranspose hLU
    rw [Matrix.conjTranspose_mul, hL.eq, Matrix.conjTranspose_mul,
      Matrix.diagonal_conjTranspose] at h
    rw [h]
    congr 2
    ext k
    exact RCLike.conj_ofReal _
  have h : Uᴴ * (L * X - X * M) * V =
      (Matrix.diagonal fun i : Fin (Fintype.card m) => ((eigenvalue L i : ℝ) : 𝕜)) *
        (Uᴴ * X * V) -
      Uᴴ * X * V * Matrix.diagonal fun j : Fin (Fintype.card n) => ((eigenvalue M j : ℝ) : 𝕜) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc Uᴴ L X, hUL]
    simp only [Matrix.mul_assoc, hMV]
  rw [h, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, RCLike.ofReal_sub, sub_mul,
    mul_comm ((Uᴴ * X * V) i j)]

/-- **Sylvester separation bound in the Frobenius norm.** For Hermitian $\mathbf{L}$ and
$\mathbf{M}$ whose eigenvalues are pairwise at distance at least $\delta$,
$\lvert \lambda_i(\mathbf{L}) - \lambda_j(\mathbf{M}) \rvert \ge \delta$ for all $i, j$, we have
$\delta \|\mathbf{X}\|_{\mathsf{F}} \le
\|\mathbf{L}\mathbf{X} - \mathbf{X}\mathbf{M}\|_{\mathsf{F}}$. No interval structure is needed.
[Bhatia1997, §VII.2]; [StewartSun1990, §V.3].
Result: sylvester-separation -/
theorem _root_.Matrix.IsHermitian.mul_frobNorm_le_frobNorm_mul_sub_mul {L : Matrix m m 𝕜}
    {M : Matrix n n 𝕜}
    (hL : L.IsHermitian) (hM : M.IsHermitian) {δ : ℝ}
    (hsep : ∀ i, i < Fintype.card m → ∀ j, j < Fintype.card n →
      δ ≤ |eigenvalue L i - eigenvalue M j|)
    (X : Matrix m n 𝕜) : δ * frobNorm X ≤ frobNorm (L * X - X * M) := by
  classical
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ (frobNorm_nonneg X)).trans (frobNorm_nonneg _)
  obtain ⟨U, V, hU, hV, h⟩ := exists_conjTranspose_mul_mul_sub_mul_mul_apply hL hM X
  have hUc : HasOrthonormalCols Uᴴ := hU.conjTranspose_of_card_eq (Fintype.card_fin _).symm
  have hnorm (Y : Matrix m n 𝕜) : frobNorm (Uᴴ * Y * V) = frobNorm Y := by
    rw [hV.frobNorm_mul_right_of_card_eq (Fintype.card_fin _).symm, hUc.frobNorm_mul_left]
  rw [← hnorm X, ← hnorm (L * X - X * M),
    ← sq_le_sq₀ (mul_nonneg hδ.le (frobNorm_nonneg _)) (frobNorm_nonneg _), mul_pow,
    frobNorm_sq_eq_sum, frobNorm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [h i j, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← sq_abs (eigenvalue L i - eigenvalue M j)]
  exact pow_le_pow_left₀ hδ.le (hsep i i.2 j j.2) 2

/-- A Sylvester equation with separated Hermitian coefficients has only the trivial homogeneous
solution: if $\mathbf{L}\mathbf{X} = \mathbf{X}\mathbf{M}$ and the spectra are disjoint, then
$\mathbf{X} = \mathbf{0}$. -/
theorem _root_.Matrix.IsHermitian.eq_zero_of_mul_eq_mul_of_eigenvalue_ne {L : Matrix m m 𝕜}
    {M : Matrix n n 𝕜}
    (hL : L.IsHermitian) (hM : M.IsHermitian)
    (hsep : ∀ i, i < Fintype.card m → ∀ j, j < Fintype.card n → eigenvalue L i ≠ eigenvalue M j)
    {X : Matrix m n 𝕜} (h : L * X = X * M) : X = 0 := by
  classical
  obtain ⟨U, V, hU, hV, hUV⟩ := exists_conjTranspose_mul_mul_sub_mul_mul_apply hL hM X
  have hZ : Uᴴ * X * V = 0 := by
    ext i j
    have hij := hUV i j
    rw [h, sub_self, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply] at hij
    rcases mul_eq_zero.mp hij.symm with h0 | h0
    · exact absurd (sub_eq_zero.mp (RCLike.ofReal_eq_zero.mp h0)) (hsep i i.2 j j.2)
    · exact h0
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  have hVV : V * Vᴴ = 1 := hV.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  calc X = U * Uᴴ * X * (V * Vᴴ) := by rw [hUU, hVV, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * X * V) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]

end NLAlib
