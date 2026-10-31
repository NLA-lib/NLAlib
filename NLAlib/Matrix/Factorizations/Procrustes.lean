/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.PolarFrames

/-!
# Procrustes problems

The orthogonal Procrustes problem asks for the unitary $\mathbf{U}$ that brings
$\mathbf{U}\mathbf{B}$ closest to $\mathbf{A}$ in the Frobenius norm. It is solved by an isometric
polar factor of $\mathbf{A}\mathbf{B}^{\mathsf{H}}$, and the least value is
$\|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{B}\|_{\mathsf{F}}^2 -
2 \|\mathbf{A}\mathbf{B}^{\mathsf{H}}\|_*$. With a unitary factor on each side the least value is
the squared distance between the non-increasing sequences of singular values.

For a matrix with at least as many rows as columns, the nearest real multiple of a matrix
with orthonormal columns is an isometric polar extension scaled by the average singular value.
The least squared error is
$$\|\mathbf{A}\|_{\mathsf{F}}^2 - \frac{\|\mathbf{A}\|_*^2}{\lvert n \rvert}\,.$$
This includes negative competing scales, rank-deficient matrices and empty column types, with
division by zero interpreted as zero.

## Main results

* `NLAlib.HasOrthonormalCols.frobInner_eq_nuclearNorm_of_mul_sqrt_eq`,
  `NLAlib.frobInner_polarFactor`: a polar factor attains the nuclear dual pairing.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_sq_of_mul_sqrt_eq`: the objective at a polar factor of
  $\mathbf{A}\mathbf{B}^{\mathsf{H}}$.
* `NLAlib.isLeast_frobNorm_sub_mul_sq`: the orthogonal Procrustes problem.
* `NLAlib.isLeast_frobNorm_sub_mul_mul_sq`: the two-sided Procrustes problem.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_smul_sq_of_mul_sqrt_eq`: the objective at any real
  multiple of an isometric polar extension.
* `NLAlib.HasOrthonormalCols.frobNorm_sq_sub_nuclearNorm_sq_div_le`: the lower bound for every
  scaled isometry.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_div_smul_sq_of_mul_sqrt_eq`: the objective at the
  average-singular-value scale.
* `NLAlib.isLeast_frobNorm_sub_smul_sq`: the nearest scaled isometry in Frobenius norm.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

omit [DecidableEq m] in
/-- **An isometric polar factor attains the nuclear dual pairing.** If
$\mathbf{M} = \mathbf{U}(\mathbf{M}^{\mathsf{H}}\mathbf{M})^{1/2}$ with $\mathbf{U}$ of orthonormal
columns, then $\langle \mathbf{M}, \mathbf{U} \rangle_{\mathsf{F}} = \|\mathbf{M}\|_*$. This is the
case of equality in `NLAlib.abs_frobInner_le_nuclearNorm_mul_specNorm`. Rectangular, any rank.
[HornJohnson2013, §7.4.4].
-/
theorem HasOrthonormalCols.frobInner_eq_nuclearNorm_of_mul_sqrt_eq [DecidableEq n]
    {M U : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (h : U * CFC.sqrt (Mᴴ * M) = M) :
    frobInner M U = nuclearNorm M := by
  rw [nuclearNorm_eq_re_trace_sqrt, frobInner_eq_re_trace_mul_conjTranspose]
  obtain ⟨S, hS⟩ : ∃ S, S = CFC.sqrt (Mᴴ * M) := ⟨_, rfl⟩
  rw [← hS] at h ⊢
  rw [← h, Matrix.trace_mul_comm, hU.conjTranspose_mul_cancel_left]

omit [DecidableEq m] in
/-- **The polar factor attains the nuclear dual pairing**:
$\langle \mathbf{M}, \mathbf{U} \rangle_{\mathsf{F}} = \|\mathbf{M}\|_*$ for the polar factor
$\mathbf{U}$ of $\mathbf{M}$, for every shape and rank; the polar factor is then a partial
isometry and need not have orthonormal columns. [HornJohnson2013, §7.4.4]. -/
theorem frobInner_polarFactor [DecidableEq n] (M : Matrix m n 𝕜) :
    frobInner M (polarFactor M) = nuclearNorm M := by
  rw [nuclearNorm_eq_re_trace_sqrt, frobInner_eq_re_trace, polarFactor, ← Matrix.mul_assoc]
  obtain ⟨S, hS⟩ : ∃ S, S = CFC.sqrt (Mᴴ * M) := ⟨_, rfl⟩
  have hSS : S * S = Mᴴ * M := by
    rw [hS]
    exact CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  rw [← hS, ← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm, mul_pinv_mul_self]

/-- The Procrustes objective through the inner product of $\mathbf{A}\mathbf{B}^{\mathsf{H}}$
with the unitary factor: for unitary $\mathbf{U}$,
$\|\mathbf{A} - \mathbf{U}\mathbf{B}\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2 +
\|\mathbf{B}\|_{\mathsf{F}}^2 -
2 \langle \mathbf{A}\mathbf{B}^{\mathsf{H}}, \mathbf{U} \rangle_{\mathsf{F}}$. -/
private theorem frobNorm_sub_mul_sq_eq (A B : Matrix m n 𝕜) {U : Matrix m m 𝕜}
    (hU : HasOrthonormalCols U) :
    frobNorm (A - U * B) ^ 2 =
      frobNorm A ^ 2 + frobNorm B ^ 2 - 2 * frobInner (A * Bᴴ) U := by
  rw [frobNorm_sub_sq, hU.frobNorm_mul_left, frobInner_eq_re_trace_mul_conjTranspose A,
    frobInner_eq_re_trace_mul_conjTranspose (A * Bᴴ), Matrix.conjTranspose_mul,
    ← Matrix.mul_assoc]
  ring

/-- The Procrustes objective at a polar factor of $\mathbf{A}\mathbf{B}^{\mathsf{H}}$: for
unitary $\mathbf{U}$ with
$\mathbf{U}\bigl((\mathbf{A}\mathbf{B}^{\mathsf{H}})^{\mathsf{H}}
\mathbf{A}\mathbf{B}^{\mathsf{H}}\bigr)^{1/2} = \mathbf{A}\mathbf{B}^{\mathsf{H}}$,
$$\|\mathbf{A} - \mathbf{U}\mathbf{B}\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2 +
  \|\mathbf{B}\|_{\mathsf{F}}^2 - 2 \|\mathbf{A}\mathbf{B}^{\mathsf{H}}\|_*\,.$$ -/
theorem HasOrthonormalCols.frobNorm_sub_mul_sq_of_mul_sqrt_eq {A B : Matrix m n 𝕜}
    {U : Matrix m m 𝕜}
    (hU : HasOrthonormalCols U)
    (h : U * CFC.sqrt ((A * Bᴴ)ᴴ * (A * Bᴴ)) = A * Bᴴ) :
    frobNorm (A - U * B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 - 2 * nuclearNorm (A * Bᴴ) := by
  rw [frobNorm_sub_mul_sq_eq A B hU, hU.frobInner_eq_nuclearNorm_of_mul_sqrt_eq h]

/-- **The orthogonal Procrustes problem.** The least value of
$\|\mathbf{A} - \mathbf{U}\mathbf{B}\|_{\mathsf{F}}^2$ over unitary $\mathbf{U}$ is
$$\|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{B}\|_{\mathsf{F}}^2 -
  2 \|\mathbf{A}\mathbf{B}^{\mathsf{H}}\|_*\,,$$
attained at a polar factor of $\mathbf{A}\mathbf{B}^{\mathsf{H}}$.
[GolubVanLoan2013, §6.4.1]; [HornJohnson2013, §7.4.5].
Result: procrustes -/
theorem isLeast_frobNorm_sub_mul_sq (A B : Matrix m n 𝕜) :
    IsLeast ((fun U : Matrix m m 𝕜 => frobNorm (A - U * B) ^ 2) '' {U | HasOrthonormalCols U})
      (frobNorm A ^ 2 + frobNorm B ^ 2 - 2 * nuclearNorm (A * Bᴴ)) := by
  constructor
  · obtain ⟨U, hU, h⟩ := exists_hasOrthonormalCols_mul_sqrt_eq (A * Bᴴ) le_rfl
    exact ⟨U, hU, HasOrthonormalCols.frobNorm_sub_mul_sq_of_mul_sqrt_eq hU h⟩
  · rintro _ ⟨U, hU, rfl⟩
    have hU' : HasOrthonormalCols U := hU
    have h1 : frobInner (A * Bᴴ) U ≤ nuclearNorm (A * Bᴴ) :=
      (le_abs_self _).trans ((abs_frobInner_le_nuclearNorm_mul_specNorm _ _).trans
        (mul_le_of_le_one_right (nuclearNorm_nonneg _) hU'.specNorm_le_one))
    simp only
    rw [frobNorm_sub_mul_sq_eq A B hU']
    linarith

/-- **The two-sided Procrustes problem.** The least value of
$\|\mathbf{A} - \mathbf{U}\mathbf{B}\mathbf{W}\|_{\mathsf{F}}^2$ over unitary $\mathbf{U}$,
$\mathbf{W}$ is
$$\sum_{i < \min(\lvert m \rvert, \lvert n \rvert)}
  \bigl(\sigma_i(\mathbf{A}) - \sigma_i(\mathbf{B})\bigr)^2\,,$$
singular values non-increasing and indexed from $0$. [HornJohnson2013, §7.4.1 context]. -/
theorem isLeast_frobNorm_sub_mul_mul_sq [DecidableEq n] (A B : Matrix m n 𝕜) :
    IsLeast
      ((fun P : Matrix m m 𝕜 × Matrix n n 𝕜 => frobNorm (A - P.1 * B * P.2) ^ 2) ''
        {P | HasOrthonormalCols P.1 ∧ HasOrthonormalCols P.2})
      (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        (singularValues A i - singularValues B i) ^ 2) := by
  obtain ⟨k, hk⟩ : ∃ k, k = min (Fintype.card m) (Fintype.card n) := ⟨_, rfl⟩
  rw [← hk]
  constructor
  · -- Align the singular vectors of `B` with those of `A`.
    have hkm : k ≤ Fintype.card m := hk.trans_le (min_le_left _ _)
    have hkn : k ≤ Fintype.card n := hk.trans_le (min_le_right _ _)
    obtain ⟨UA, VA, hA⟩ := exists_isSVD A
      (hk.symm ▸ le_min A.rank_le_card_height A.rank_le_card_width) hkm hkn
    obtain ⟨UB, VB, hB⟩ := exists_isSVD B
      (hk.symm ▸ le_min B.rank_le_card_height B.rank_le_card_width) hkm hkn
    obtain ⟨P, hP, hPU⟩ :=
      hB.hasOrthonormalCols_left.exists_mul_eq hA.hasOrthonormalCols_left
    obtain ⟨R, hR, hRV⟩ :=
      hB.hasOrthonormalCols_right.exists_mul_eq hA.hasOrthonormalCols_right
    refine ⟨(P, Rᴴ), ⟨hP, hR.conjTranspose⟩, ?_⟩
    have h1 : P * B * Rᴴ =
        UA * Matrix.diagonal (fun i : Fin k => ((singularValues B i : ℝ) : 𝕜)) * VAᴴ :=
      calc P * B * Rᴴ
        _ = P * (UB * Matrix.diagonal (fun i : Fin k => ((singularValues B i : ℝ) : 𝕜)) * VBᴴ) *
            Rᴴ := by rw [← hB.eq]
        _ = P * UB * Matrix.diagonal (fun i : Fin k => ((singularValues B i : ℝ) : 𝕜)) *
            (R * VB)ᴴ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hPU, hRV]
    have h2 : A - P * B * Rᴴ = UA * Matrix.diagonal (fun i : Fin k =>
        ((singularValues A i : ℝ) : 𝕜) - ((singularValues B i : ℝ) : 𝕜)) * VAᴴ := by
      rw [h1, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, ← hA.eq]
    simp only
    rw [h2, Matrix.mul_assoc, hA.hasOrthonormalCols_left.frobNorm_mul_left,
      hA.hasOrthonormalCols_right.frobNorm_mul_conjTranspose_right, frobNorm_diagonal_sq,
      ← Fin.sum_univ_eq_sum_range (fun i => (singularValues A i - singularValues B i) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal, sq_abs]
  · rintro _ ⟨⟨P, W⟩, ⟨hP, hW⟩, rfl⟩
    have hP' : HasOrthonormalCols P := hP
    have hW' : HasOrthonormalCols W := hW
    have hsv : singularValues (P * B * W) = singularValues B := by
      rw [Matrix.mul_assoc, hP'.singularValues_mul_left]
      have h := hW'.conjTranspose.singularValues_mul_conjTranspose_right B
      rwa [Matrix.conjTranspose_conjTranspose] at h
    have h := sum_singularValues_sub_sq_le_frobNorm_sub_sq A (P * B * W) (Finset.range k)
    rwa [hsv] at h

/-! ### The nearest scaled isometry -/

omit [DecidableEq m] in
/-- The squared Frobenius distance to a real multiple of an isometric polar extension is a
scalar quadratic. For $\mathbf{A},\mathbf{U} \in \Bbbk^{m \times n}$, with $\mathbf{U}$ of
orthonormal columns and
$\mathbf{U}(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{1/2} = \mathbf{A}$, every $c \in \mathbb{R}$
satisfies
$$\|\mathbf{A} - c\mathbf{U}\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2 -
  2c\|\mathbf{A}\|_* + \lvert n \rvert c^2\,.$$
No full-rank or nonempty-dimension hypothesis is needed. This evaluates the objective before
optimizing the scale.
Generalizes `NLAlib.frobSq_sub_smul_polar_eq` from the original NLAlib formal library,
`NLAlib.Matrix.Factorizations.ScaledOrthogonal`, commit
`77514ce42a0e437d837797a063ac161f41022730`, from square real to rectangular `RCLike` matrices. -/
theorem HasOrthonormalCols.frobNorm_sub_smul_sq_of_mul_sqrt_eq [DecidableEq n]
    {A U : Matrix m n 𝕜} (hU : HasOrthonormalCols U)
    (hA : U * CFC.sqrt (Aᴴ * A) = A) (c : ℝ) :
    frobNorm (A - c • U) ^ 2 =
      frobNorm A ^ 2 - 2 * c * nuclearNorm A + (Fintype.card n : ℝ) * c ^ 2 := by
  rw [frobNorm_sub_sq, frobInner_smul_right,
    hU.frobInner_eq_nuclearNorm_of_mul_sqrt_eq hA, frobNorm_real_smul,
    mul_pow, sq_abs, hU.frobNorm_sq]
  ring

omit [DecidableEq m] in
/-- Every real multiple of a matrix with orthonormal columns has squared Frobenius error at
least the nuclear-norm optimum. For $\mathbf{A},\mathbf{U} \in \Bbbk^{m \times n}$ with
$\mathbf{U}$ of orthonormal columns and every $c \in \mathbb{R}$,
$$\|\mathbf{A}\|_{\mathsf{F}}^2 - \frac{\|\mathbf{A}\|_*^2}{\lvert n \rvert}
  \le \|\mathbf{A} - c\mathbf{U}\|_{\mathsf{F}}^2\,.$$
This certifies a lower bound for any competing scaled isometry, including negative scales.
Empty columns are included, with division by zero interpreted as zero.
Generalizes `NLAlib.frobSq_sub_nuclearNorm_sq_div_card_le_sub_smul` from the original NLAlib
formal library, `NLAlib.Matrix.Factorizations.ScaledOrthogonal`, commit
`77514ce42a0e437d837797a063ac161f41022730`, from positive-dimensional square real matrices to
rectangular `RCLike` matrices of any dimension. -/
theorem HasOrthonormalCols.frobNorm_sq_sub_nuclearNorm_sq_div_le [DecidableEq n]
    {U : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (A : Matrix m n 𝕜) (c : ℝ) :
    frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ) ≤
      frobNorm (A - c • U) ^ 2 := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · have hA : A = 0 := Subsingleton.elim _ _
    have hU0 : U = 0 := Subsingleton.elim _ _
    simp [hA, hU0]
  · have hd : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
    have hp : |frobInner A U| ≤ nuclearNorm A :=
      (abs_frobInner_le_nuclearNorm_mul_specNorm A U).trans
        (mul_le_of_le_one_right (nuclearNorm_nonneg A) hU.specNorm_le_one)
    have hp2 : frobInner A U ^ 2 ≤ nuclearNorm A ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hp 2
    have hdiv : nuclearNorm A ^ 2 / (Fintype.card n : ℝ) * (Fintype.card n : ℝ) =
        nuclearNorm A ^ 2 := div_mul_cancel₀ _ hd.ne'
    rw [frobNorm_sub_sq, frobInner_smul_right, frobNorm_real_smul,
      mul_pow, sq_abs, hU.frobNorm_sq]
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith [sq_nonneg ((Fintype.card n : ℝ) * c - frobInner A U)]

omit [DecidableEq m] in
/-- Scaling an isometric polar extension by the average singular value attains the optimal
squared Frobenius error. For $\mathbf{A},\mathbf{U} \in \Bbbk^{m \times n}$, with $\mathbf{U}$
of orthonormal columns and
$\mathbf{U}(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{1/2} = \mathbf{A}$,
$$\left\|\mathbf{A} - \frac{\|\mathbf{A}\|_*}{\lvert n \rvert}\mathbf{U}
  \right\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2 -
  \frac{\|\mathbf{A}\|_*^2}{\lvert n \rvert}\,.$$
This certifies optimality of a supplied factor, even when $\mathbf{A}$ is rank deficient.
For empty columns the scale and both sides are zero by total division.
Generalizes `NLAlib.frobSq_sub_avg_smul_polar_eq` from the original NLAlib formal library,
`NLAlib.Matrix.Factorizations.ScaledOrthogonal`, commit
`77514ce42a0e437d837797a063ac161f41022730`, from positive-dimensional square real matrices to
rectangular `RCLike` matrices of any dimension. -/
theorem HasOrthonormalCols.frobNorm_sub_div_smul_sq_of_mul_sqrt_eq [DecidableEq n]
    {A U : Matrix m n 𝕜} (hU : HasOrthonormalCols U)
    (hA : U * CFC.sqrt (Aᴴ * A) = A) :
    frobNorm (A - (nuclearNorm A / (Fintype.card n : ℝ)) • U) ^ 2 =
      frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ) := by
  rw [hU.frobNorm_sub_smul_sq_of_mul_sqrt_eq hA]
  rcases eq_or_ne (Fintype.card n : ℝ) 0 with hd | hd
  · simp [hd]
  · field_simp
    ring

omit [DecidableEq m] in
/-- **The nearest scaled isometry in Frobenius norm.** For
$\mathbf{A} \in \Bbbk^{m \times n}$ with $\lvert n \rvert \le \lvert m \rvert$, the least
value of $\|\mathbf{A} - c\mathbf{U}\|_{\mathsf{F}}^2$ over all $c \in \mathbb{R}$ and all
$\mathbf{U} \in \Bbbk^{m \times n}$ with orthonormal columns is
$$\|\mathbf{A}\|_{\mathsf{F}}^2 - \frac{\|\mathbf{A}\|_*^2}{\lvert n \rvert}\,.$$
It is attained by an isometric polar extension scaled by the average singular value. This
includes negative competing scales and rank-deficient matrices. For empty columns the minimum
is zero, with division by zero interpreted as zero. No uniqueness is asserted.
[HornJohnson2013, §7.4.4], the square case; here generalized to rectangular matrices over any
`RCLike` field and arbitrary finite index types, including empty columns.
Generalizes `NLAlib.isLeast_frobSq_sub_scaled_orthogonal` and
`NLAlib.isLeast_frobSq_sub_scaled_orthogonal_of_isEmpty` from the original NLAlib formal library,
`NLAlib.Matrix.Factorizations.ScaledOrthogonal`, commit
`77514ce42a0e437d837797a063ac161f41022730`, from square real to rectangular `RCLike` matrices,
combining the nonempty and empty cases.
Result: procrustes-scaled -/
theorem isLeast_frobNorm_sub_smul_sq [DecidableEq n] (A : Matrix m n 𝕜)
    (hcard : Fintype.card n ≤ Fintype.card m) :
    IsLeast {z : ℝ | ∃ (c : ℝ) (U : Matrix m n 𝕜),
      HasOrthonormalCols U ∧ frobNorm (A - c • U) ^ 2 = z}
      (frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ)) := by
  obtain ⟨U, hU, hA⟩ := exists_hasOrthonormalCols_mul_sqrt_eq A hcard
  refine ⟨⟨_, U, hU, hU.frobNorm_sub_div_smul_sq_of_mul_sqrt_eq hA⟩, ?_⟩
  rintro z ⟨c, V, hV, rfl⟩
  exact hV.frobNorm_sq_sub_nuclearNorm_sq_div_le A c

end NLAlib
