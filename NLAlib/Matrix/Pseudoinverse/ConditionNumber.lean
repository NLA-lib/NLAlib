/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Spectral.LowRank
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.Positivity.Core

/-!
# Spectral conditioning and the distance to singularity

`NLAlib.pseudoConditionNumber A` is $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$, defined for a matrix
of any shape through the Moore–Penrose pseudoinverse: the ratio of the largest singular value of
$\mathbf{A}$ to its smallest *nonzero* one, and $0$ for the zero matrix. It is real-valued.

It is not the classical condition number on singular or rank-deficient matrices, which is
$\sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$, infinite as soon as
$\sigma_{\min}(\mathbf{A}) = 0$: a nonzero singular orthogonal projector, such as
$\operatorname{diag}(1, 0)$, has pseudo-condition number $1$. For a matrix of full column rank
the two agree,
$\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2 = \sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$
(`NLAlib.pseudoConditionNumber_of_injective`), and for an invertible matrix it is the classical
$\kappa(\mathbf{A}) = \|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2$
(`NLAlib.pseudoConditionNumber_of_isUnit`). For square matrices
`NLAlib.spectralConditionNumber` takes values in the extended nonnegative reals:
it agrees with the finite quantity on units and takes the value infinity on singular inputs.

The distance from a matrix to the nearest rank-deficient one, in spectral norm, is its smallest
singular value.

The names `conditionNumber` and `conditionNumber_*` are deprecated aliases (2026-10-14).

## Main definitions

* `NLAlib.pseudoConditionNumber`: $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$, that is
  `specNorm A * specNorm (pinv A)`.
* `NLAlib.frobPseudoConditionNumber`: $\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$, that is
  `frobNorm A * specNorm (pinv A)`, the rate constant of randomized Kaczmarz.

## Main results

* `NLAlib.pseudoConditionNumber_mul_le`: submultiplicativity on invertible matrices.

* `NLAlib.spectralConditionNumber_eq_top_iff`: singularity is equivalent to infinite
  spectral condition number.

* `NLAlib.pseudoConditionNumber_eq_singularValues_div`: the ratio of the extreme nonzero singular
  values.
* `NLAlib.pseudoConditionNumber_of_injective`: the classical
  $\sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$ at full column rank.
* `NLAlib.one_le_pseudoConditionNumber`: at least one for a nonzero matrix.
* `NLAlib.pseudoConditionNumber_of_isUnit`: the classical formula
  $\|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2$.
* `NLAlib.singularValues_last_le_specNorm_of_not_injective_add`,
  `NLAlib.isLeast_specNorm_not_injective_add`: the distance to rank deficiency.
* `NLAlib.one_le_frobPseudoConditionNumber`, `NLAlib.rank_le_frobPseudoConditionNumber_sq`,
  `NLAlib.frobPseudoConditionNumber_sq_le_rank_mul_pseudoConditionNumber_sq`: the squared
  Frobenius pseudo-condition number lies between the rank and the rank times the squared
  pseudo-condition number.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- The **pseudo-condition number** $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$, that is
`specNorm A * specNorm (pinv A)`, of a matrix of any shape: the ratio of its largest singular
value to its smallest nonzero singular value, computed through the pseudoinverse, and $0$ for the
zero matrix.

It is not the classical condition number $\sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$ on
singular or rank-deficient matrices, where the classical one is infinite: it ignores the zero
singular values, so a nonzero singular orthogonal projector ($\operatorname{diag}(1, 0)$, or any
$\mathbf{P}$ with `IsStarProjection P`, $\mathbf{P} \ne \mathbf{0}$, $\mathbf{P} \ne \mathbf{I}$)
has pseudo-condition number $1$. For a matrix of full column rank it agrees with the classical
one, $\sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$ (`pseudoConditionNumber_of_injective`),
and for an invertible matrix it is the classical
$\kappa(\mathbf{A}) = \|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2$ (`pseudoConditionNumber_of_isUnit`);
theorems about the classical condition number assume invertibility or full column rank.
[GolubVanLoan2013, §2.6.2 and §5.3.7]. -/
noncomputable def pseudoConditionNumber (A : Matrix m n 𝕜) : ℝ :=
  specNorm A * specNorm (pinv A)

/-- `pseudoConditionNumber A` unfolds to $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$. -/
theorem pseudoConditionNumber_def (A : Matrix m n 𝕜) :
    pseudoConditionNumber A = specNorm A * specNorm (pinv A) :=
  rfl

/-- The pseudo-condition number is nonnegative. -/
theorem pseudoConditionNumber_nonneg (A : Matrix m n 𝕜) : 0 ≤ pseudoConditionNumber A := by
  exact mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)

/-- The pseudo-condition number of the zero matrix is zero. -/
@[simp]
theorem pseudoConditionNumber_zero : pseudoConditionNumber (0 : Matrix m n 𝕜) = 0 := by
  rw [pseudoConditionNumber, specNorm_zero, zero_mul]

/-- The pseudo-condition number of a nonzero matrix is at least one:
$1 \le \|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$ for $\mathbf{A} \ne \mathbf{0}$. -/
theorem one_le_pseudoConditionNumber {A : Matrix m n 𝕜} (hA : A ≠ 0) :
    1 ≤ pseudoConditionNumber A := by
  have hpos : 0 < specNorm A :=
    lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp hA))
  have hbound : 1 * specNorm A ≤ pseudoConditionNumber A * specNorm A := by
    calc 1 * specNorm A = specNorm (A * pinv A * A) := by rw [one_mul, mul_pinv_mul_self]
      _ ≤ specNorm (A * pinv A) * specNorm A := specNorm_mul_le _ _
      _ ≤ specNorm A * specNorm (pinv A) * specNorm A :=
        mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
  exact le_of_mul_le_mul_right hbound hpos

/-- The pseudo-condition number as a ratio of singular values: for
$k + 1 = \operatorname{rank} \mathbf{A}$,
$\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2 = \sigma_0(\mathbf{A}) / \sigma_k(\mathbf{A})$. -/
theorem pseudoConditionNumber_eq_singularValues_div (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = A.rank) :
    pseudoConditionNumber A = singularValues A 0 / singularValues A k := by
  rw [pseudoConditionNumber, specNorm_pinv A hk, singularValues_zero_eq_specNorm, div_eq_mul_inv]

/-- Agreement with the classical condition number at full column rank: if $\mathbf{A}$ has
full column rank, its pseudo-condition number is the classical
$\kappa(\mathbf{A}) = \sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$, written
$\|\mathbf{A}\|_2 / \sigma_k(\mathbf{A})$ with $k + 1 = \lvert n \rvert$. -/
theorem pseudoConditionNumber_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec)
    {k : ℕ} (hk : k + 1 = Fintype.card n) :
    pseudoConditionNumber A = specNorm A / singularValues A k := by
  rw [pseudoConditionNumber, specNorm_pinv_of_injective hA hk, div_eq_mul_inv]

/-- For an invertible matrix the pseudo-condition number is the classical condition number
$\kappa(\mathbf{A}) = \|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2$. -/
theorem pseudoConditionNumber_of_isUnit [DecidableEq n] {A : Matrix n n 𝕜} (hA : IsUnit A) :
    pseudoConditionNumber A = specNorm A * specNorm A⁻¹ := by
  rw [pseudoConditionNumber, pinv_of_isUnit hA]

/-- The classical spectral condition number of a square matrix. It agrees with
`pseudoConditionNumber` on invertible matrices and takes the value infinity on singular
matrices. The empty matrix is invertible and has condition number zero with the operator-norm
convention. [GolubVanLoan2013, §2.6.2]. -/
noncomputable def spectralConditionNumber [DecidableEq n] (A : Matrix n n 𝕜) : ℝ≥0∞ := by
  classical
  exact if IsUnit A then ENNReal.ofReal (pseudoConditionNumber A) else ⊤

/-- At an invertible square matrix the finite pseudo-condition number gives the classical
spectral condition number. [GolubVanLoan2013, §2.6.2]. -/
theorem spectralConditionNumber_of_isUnit [DecidableEq n] {A : Matrix n n 𝕜} (hA : IsUnit A) :
    spectralConditionNumber A = ENNReal.ofReal (pseudoConditionNumber A) := by
  classical
  simp only [spectralConditionNumber, if_pos hA]

/-- **Singularity and the spectral condition number.** A real or complex square matrix has
infinite spectral condition number exactly when it is singular. [GolubVanLoan2013, §2.6.2].
Result: condition-number-def -/
@[simp]
theorem spectralConditionNumber_eq_top_iff [DecidableEq n] (A : Matrix n n 𝕜) :
    spectralConditionNumber A = ⊤ ↔ ¬ IsUnit A := by
  classical
  by_cases hA : IsUnit A <;> simp [spectralConditionNumber, hA]

/-- The condition number is submultiplicative on invertible matrices:
$\kappa(\mathbf{A}\mathbf{B}) \le \kappa(\mathbf{A})\kappa(\mathbf{B})$ for invertible
$\mathbf{A}$ and $\mathbf{B}$. [GolubVanLoan2013, §2.6.2]. -/
theorem pseudoConditionNumber_mul_le [DecidableEq n] {A B : Matrix n n 𝕜} (hA : IsUnit A)
    (hB : IsUnit B) :
    pseudoConditionNumber (A * B) ≤ pseudoConditionNumber A * pseudoConditionNumber B := by
  rw [pseudoConditionNumber_of_isUnit (hA.mul hB), pseudoConditionNumber_of_isUnit hA,
    pseudoConditionNumber_of_isUnit hB, Matrix.mul_inv_rev]
  calc specNorm (A * B) * specNorm (B⁻¹ * A⁻¹)
      ≤ specNorm A * specNorm B * (specNorm B⁻¹ * specNorm A⁻¹) :=
        mul_le_mul (specNorm_mul_le _ _) (specNorm_mul_le _ _) (specNorm_nonneg _)
          (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
    _ = specNorm A * specNorm A⁻¹ * (specNorm B * specNorm B⁻¹) := by ring

/-- For a positive definite matrix the pseudo-condition number is the ratio of the extreme
eigenvalues: $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2 = \lambda_0(\mathbf{A}) / \lambda_k(\mathbf{A})$
for $k + 1 = \lvert n \rvert$, eigenvalues non-increasing and indexed from $0$. -/
theorem _root_.Matrix.PosDef.pseudoConditionNumber_eq {A : Matrix n n 𝕜} (hA : A.PosDef) {k : ℕ}
    (hk : k + 1 = Fintype.card n) : pseudoConditionNumber A = eigenvalue A 0 / eigenvalue A k := by
  classical
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hA.isUnit
  rw [pseudoConditionNumber_of_injective hinj hk, ← singularValues_zero_eq_specNorm,
    hA.posSemidef.singularValues_eq_eigenvalue]

/-- The pseudo-condition number is invariant under the conjugate transpose:
$\mathbf{A}^{\mathsf{H}}$ and $\mathbf{A}$ have the same pseudo-condition number. -/
@[simp]
theorem pseudoConditionNumber_conjTranspose (A : Matrix m n 𝕜) :
    pseudoConditionNumber Aᴴ = pseudoConditionNumber A := by
  rw [pseudoConditionNumber, pinv_conjTranspose, specNorm_conjTranspose, specNorm_conjTranspose,
    pseudoConditionNumber]

/-- The pseudo-condition number of the pseudoinverse $\mathbf{A}^{+}$ is that of $\mathbf{A}$. -/
@[simp]
theorem pseudoConditionNumber_pinv (A : Matrix m n 𝕜) :
    pseudoConditionNumber (pinv A) = pseudoConditionNumber A := by
  rw [pseudoConditionNumber, pinv_pinv, mul_comm, pseudoConditionNumber]

/-- The pseudo-condition number is invariant under nonzero scaling: $c\mathbf{A}$ and
$\mathbf{A}$ have the same pseudo-condition number for $c \ne 0$. -/
theorem pseudoConditionNumber_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix m n 𝕜) :
    pseudoConditionNumber (c • A) = pseudoConditionNumber A := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [pseudoConditionNumber, pinv_smul, specNorm_smul, specNorm_smul, norm_inv,
    pseudoConditionNumber]
  field_simp

/-- The pseudo-condition number of the Gram matrix $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ is the
square of the pseudo-condition number of $\mathbf{A}$. -/
theorem pseudoConditionNumber_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    pseudoConditionNumber (Aᴴ * A) = pseudoConditionNumber A ^ 2 := by
  rw [pseudoConditionNumber, specNorm_conjTranspose_mul_self, ← specNorm_pinv_sq,
    pseudoConditionNumber, mul_pow]

/-- Left multiplication by a matrix with orthonormal columns preserves the pseudo-condition number.
-/
theorem HasOrthonormalCols.pseudoConditionNumber_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    pseudoConditionNumber (Q * A) = pseudoConditionNumber A := by
  rw [pseudoConditionNumber, hQ.pinv_mul_left, hQ.specNorm_mul_left,
    hQ.specNorm_mul_conjTranspose_right, pseudoConditionNumber]

/-- A matrix with orthonormal columns, and at least one column, has pseudo-condition number one. -/
theorem HasOrthonormalCols.pseudoConditionNumber_eq_one [DecidableEq n] [Nonempty n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : pseudoConditionNumber Q = 1 := by
  rw [pseudoConditionNumber, hQ.pinv_eq, specNorm_conjTranspose, hQ.specNorm_eq_one, mul_one]

/-- Two-sided Gram bounds control the pseudo-condition number: if
$a\mathbf{I} \preceq \mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq b\mathbf{I}$ with $0 < a$ and
$0 \le b$, then $(\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2)^2 \le b / a$. With
$\mathbf{A} = \mathbf{S}\mathbf{U}$ this is the conditioning of a sketched orthonormal basis. -/
theorem pseudoConditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one [DecidableEq n]
    {A : Matrix m n 𝕜} {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A) (h₂ : Aᴴ * A ≤ b • (1 : Matrix n n 𝕜)) :
    pseudoConditionNumber A ^ 2 ≤ b / a := by
  rw [pseudoConditionNumber, mul_pow, div_eq_mul_inv]
  exact mul_le_mul ((specNorm_sq_le_iff_conjTranspose_mul_self_le hb).mpr h₂)
    (specNorm_pinv_sq_le_inv_of_smul_one_le ha h₁) (sq_nonneg _) hb

/-! ### Distance to rank deficiency -/

/-- **The smallest singular value is a lower bound for rank-deficient perturbations.** If
$\mathbf{A} + \mathbf{E}$ does not have full column rank, then
$\sigma_k(\mathbf{A}) \le \|\mathbf{E}\|_2$ for $k + 1 = \lvert n \rvert$: $\sigma_k(\mathbf{A})$ is
$\sigma_{\min}(\mathbf{A})$, the last of the $\lvert n \rvert$ singular values.
[GolubVanLoan2013, Theorem 2.5.3 and §2.6.2]. -/
theorem singularValues_last_le_specNorm_of_not_injective_add (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) {E : Matrix m n 𝕜}
    (hE : ¬ Function.Injective (A + E).mulVec) : singularValues A k ≤ specNorm E := by
  have h0 : singularValues (A + E) k = 0 :=
    le_antisymm (not_lt.mp ((singularValues_last_pos_iff_injective (A + E) hk).not.mpr hE))
      (singularValues_nonneg _ _)
  have h := abs_singularValues_sub_le_specNorm A (A + E) k
  rw [h0, sub_zero, sub_add_cancel_left, specNorm_neg] at h
  exact (le_abs_self _).trans h

/-- **The distance to rank deficiency is the smallest singular value.** Among perturbations
$\mathbf{E}$ for which $\mathbf{A} + \mathbf{E}$ loses full column rank, the smallest spectral norm
is $\sigma_k(\mathbf{A})$ with $k + 1 = \lvert n \rvert$, that is $\sigma_{\min}(\mathbf{A})$; it is
attained.
[GolubVanLoan2013, §2.6.2].
Result: distance-to-singularity -/
theorem isLeast_specNorm_not_injective_add (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    IsLeast (specNorm '' {E : Matrix m n 𝕜 | ¬ Function.Injective (A + E).mulVec})
      (singularValues A k) := by
  refine ⟨⟨truncatedSVD A k - A, ?_, ?_⟩, ?_⟩
  · rw [Set.mem_ofPred_eq, add_sub_cancel, mulVec_injective_iff_rank_eq]
    have := rank_truncatedSVD_le A k
    omega
  · rw [specNorm_sub_comm, specNorm_sub_truncatedSVD]
  · rintro _ ⟨E, hE, rfl⟩
    exact singularValues_last_le_specNorm_of_not_injective_add A hk hE

/-- **The distance from an invertible matrix to the singular matrices** is
$1 / \|\mathbf{A}^{-1}\|_2$: it is the least $\|\mathbf{E}\|_2$ over $\mathbf{E}$ with
$\mathbf{A} + \mathbf{E}$ singular, on a nonempty index type.
[GolubVanLoan2013, §2.6.2].
Result: distance-to-singularity -/
theorem isLeast_specNorm_not_isUnit_add [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : IsUnit A) :
    IsLeast (specNorm '' {E : Matrix n n 𝕜 | ¬ IsUnit (A + E)}) (specNorm A⁻¹)⁻¹ := by
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n :=
    ⟨Fintype.card n - 1, Nat.sub_add_cancel Fintype.card_pos⟩
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hA
  have hset : {E : Matrix n n 𝕜 | ¬ IsUnit (A + E)} =
      {E | ¬ Function.Injective (A + E).mulVec} := by
    ext E
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Matrix.mulVec_injective_iff_isUnit]
  rw [hset, ← pinv_of_isUnit hA, specNorm_pinv_of_injective hinj hk, inv_inv]
  exact isLeast_specNorm_not_injective_add A hk

/-- The relative distance from an invertible matrix to the singular matrices is the inverse of
the pseudo-condition number, which for an invertible matrix is the classical condition number:
the least $\|\mathbf{E}\|_2 / \|\mathbf{A}\|_2$ over $\mathbf{E}$ with $\mathbf{A} + \mathbf{E}$
singular is $\kappa(\mathbf{A})^{-1} = (\|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2)^{-1}$. -/
theorem isLeast_specNorm_div_not_isUnit_add [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : IsUnit A) :
    IsLeast ((fun E : Matrix n n 𝕜 => specNorm E / specNorm A) '' {E | ¬ IsUnit (A + E)})
      (pseudoConditionNumber A)⁻¹ := by
  have heq : (pseudoConditionNumber A)⁻¹ = (specNorm A⁻¹)⁻¹ / specNorm A := by
    rw [pseudoConditionNumber_of_isUnit hA, mul_inv, div_eq_mul_inv, mul_comm]
  obtain ⟨⟨E, hE, hEn⟩, hmin⟩ := isLeast_specNorm_not_isUnit_add hA
  rw [heq]
  refine ⟨⟨E, hE, ?_⟩, ?_⟩
  · rw [← hEn]
  · rintro _ ⟨F, hF, rfl⟩
    exact div_le_div_of_nonneg_right (hmin ⟨F, hF, rfl⟩) (specNorm_nonneg A)

/-- **Reciprocal condition number and distance to singularity.** For every nonzero square
matrix $\mathbf{A}$,
$$
\min_{\mathbf{A}+\mathbf{E}\ \mathrm{singular}}
  \frac{\|\mathbf{E}\|_2}{\|\mathbf{A}\|_2} = \kappa_2(\mathbf{A})^{-1}.
$$
For singular $\mathbf{A}$ the zero perturbation attains the minimum, with $1/\infty=0$.
[GolubVanLoan2013, §2.6.2].
Result: distance-to-singularity -/
theorem isLeast_specNorm_div_not_isUnit_add_of_ne_zero [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A ≠ 0) :
    IsLeast ((fun E : Matrix n n 𝕜 => specNorm E / specNorm A) '' {E | ¬ IsUnit (A + E)})
      ((spectralConditionNumber A)⁻¹).toReal := by
  classical
  by_cases hu : IsUnit A
  · have : Nonempty n := by
      by_contra! he
      exact hA (Subsingleton.elim _ _)
    rw [spectralConditionNumber_of_isUnit hu, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (pseudoConditionNumber_nonneg A)]
    exact isLeast_specNorm_div_not_isUnit_add hu
  · rw [(spectralConditionNumber_eq_top_iff A).2 hu, ENNReal.inv_top, ENNReal.toReal_zero]
    refine ⟨⟨0, by simpa using hu, by simp⟩, ?_⟩
    rintro _ ⟨E, _, rfl⟩
    exact div_nonneg (specNorm_nonneg _) (specNorm_nonneg _)

/-! ### The Frobenius pseudo-condition number -/

/-- The **Frobenius pseudo-condition number** $\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$,
that is `frobNorm A * specNorm (pinv A)`, of a matrix of any shape and rank: the Frobenius norm
divided by the smallest *nonzero* singular value
(`NLAlib.frobPseudoConditionNumber_eq_frobNorm_div_singularValues`), and $0$ for the zero matrix.
Its square is the inverse rate of randomized Kaczmarz. It lies between the pseudo-condition number
and $\sqrt{\operatorname{rank}\mathbf{A}}$ times it, and its square is at least the rank.
[StrohmerVershynin2009, Theorem 2], there $\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{-1}\|_2$ for a
left inverse (full column rank), Demmel's scaled condition number; [ZouziasFreris2013, (2)], there
with the pseudoinverse. -/
noncomputable def frobPseudoConditionNumber (A : Matrix m n 𝕜) : ℝ :=
  frobNorm A * specNorm (pinv A)

/-- `frobPseudoConditionNumber A` unfolds to $\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$. -/
theorem frobPseudoConditionNumber_def (A : Matrix m n 𝕜) :
    frobPseudoConditionNumber A = frobNorm A * specNorm (pinv A) :=
  rfl

/-- The Frobenius pseudo-condition number is nonnegative:
$0 \le \|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$. -/
theorem frobPseudoConditionNumber_nonneg (A : Matrix m n 𝕜) : 0 ≤ frobPseudoConditionNumber A :=
  mul_nonneg (frobNorm_nonneg _) (specNorm_nonneg _)

/-- The Frobenius pseudo-condition number of the zero matrix is zero. -/
@[simp]
theorem frobPseudoConditionNumber_zero : frobPseudoConditionNumber (0 : Matrix m n 𝕜) = 0 := by
  rw [frobPseudoConditionNumber, frobNorm_zero, zero_mul]

/-- The Frobenius pseudo-condition number is invariant under the conjugate transpose:
$\|\mathbf{A}^{\mathsf{H}}\|_{\mathsf{F}}\|(\mathbf{A}^{\mathsf{H}})^{+}\|_2 =
\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$. -/
@[simp]
theorem frobPseudoConditionNumber_conjTranspose (A : Matrix m n 𝕜) :
    frobPseudoConditionNumber Aᴴ = frobPseudoConditionNumber A := by
  rw [frobPseudoConditionNumber, frobNorm_conjTranspose, pinv_conjTranspose,
    specNorm_conjTranspose, frobPseudoConditionNumber]

/-- The Frobenius pseudo-condition number as a ratio: for
$k + 1 = \operatorname{rank}\mathbf{A}$,
$$\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2 =
\frac{\|\mathbf{A}\|_{\mathsf{F}}}{\sigma_k(\mathbf{A})}\,,$$
the Frobenius norm over the smallest nonzero singular value. -/
theorem frobPseudoConditionNumber_eq_frobNorm_div_singularValues (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = A.rank) :
    frobPseudoConditionNumber A = frobNorm A / singularValues A k := by
  rw [frobPseudoConditionNumber, specNorm_pinv A hk, div_eq_mul_inv]

/-- The pseudo-condition number is at most the Frobenius one:
$\|\mathbf{A}\|_2\|\mathbf{A}^{+}\|_2 \le \|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$.
[StrohmerVershynin2009, (3)], there for an invertible matrix. -/
theorem pseudoConditionNumber_le_frobPseudoConditionNumber (A : Matrix m n 𝕜) :
    pseudoConditionNumber A ≤ frobPseudoConditionNumber A :=
  mul_le_mul_of_nonneg_right (specNorm_le_frobNorm A) (specNorm_nonneg _)

/-- The Frobenius pseudo-condition number of a nonzero matrix is at least one:
$1 \le \|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$ for $\mathbf{A} \ne \mathbf{0}$, so the
Kaczmarz rate $1 - (\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^{-2}$ lies in $[0, 1)$. -/
theorem one_le_frobPseudoConditionNumber {A : Matrix m n 𝕜} (hA : A ≠ 0) :
    1 ≤ frobPseudoConditionNumber A :=
  (one_le_pseudoConditionNumber hA).trans (pseudoConditionNumber_le_frobPseudoConditionNumber A)

/-- **The square of the Frobenius pseudo-condition number is at least the rank**:
$\operatorname{rank}\mathbf{A} \le (\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^2$, since each
of the $\operatorname{rank}\mathbf{A}$ nonzero singular values is at least the smallest one.
[StrohmerVershynin2009, (3)], there $n \le \kappa(\mathbf{A})^2$ at full column rank. -/
theorem rank_le_frobPseudoConditionNumber_sq (A : Matrix m n 𝕜) :
    (A.rank : ℝ) ≤ frobPseudoConditionNumber A ^ 2 := by
  obtain h0 | ⟨k, hk⟩ : A.rank = 0 ∨ ∃ k, k + 1 = A.rank := by
    rcases Nat.eq_zero_or_pos A.rank with h | h
    · exact Or.inl h
    · exact Or.inr ⟨A.rank - 1, by omega⟩
  · rw [h0, Nat.cast_zero]
    positivity
  have hσ : 0 < singularValues A k := (singularValues_pos_iff A).2 (by omega)
  have hsum : (A.rank : ℝ) * singularValues A k ^ 2 ≤ frobNorm A ^ 2 := by
    rw [frobNorm_sq_eq_sum_range_singularValues_sq A le_rfl]
    calc (A.rank : ℝ) * singularValues A k ^ 2
        = ∑ _i ∈ Finset.range A.rank, singularValues A k ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range A.rank, singularValues A i ^ 2 :=
          Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (singularValues_nonneg A k)
            (singularValues_antitone A (by rw [Finset.mem_range] at hi; omega)) 2
  rw [frobPseudoConditionNumber, specNorm_pinv A hk, mul_pow, inv_pow, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  exact hsum

/-- **The Frobenius pseudo-condition number is at most $\sqrt{\operatorname{rank}\mathbf{A}}$
times the pseudo-condition number**, squared:
$(\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^2 \le
\operatorname{rank}\mathbf{A}\,(\|\mathbf{A}\|_2\|\mathbf{A}^{+}\|_2)^2$.
[StrohmerVershynin2009, (3)], there for an invertible matrix. -/
theorem frobPseudoConditionNumber_sq_le_rank_mul_pseudoConditionNumber_sq (A : Matrix m n 𝕜) :
    frobPseudoConditionNumber A ^ 2 ≤ A.rank * pseudoConditionNumber A ^ 2 := by
  have h := mul_le_mul_of_nonneg_right (frobNorm_sq_le_rank_mul_specNorm_sq A)
    (sq_nonneg (specNorm (pinv A)))
  calc frobPseudoConditionNumber A ^ 2 = frobNorm A ^ 2 * specNorm (pinv A) ^ 2 := by
        rw [frobPseudoConditionNumber, mul_pow]
    _ ≤ A.rank * specNorm A ^ 2 * specNorm (pinv A) ^ 2 := h
    _ = A.rank * pseudoConditionNumber A ^ 2 := by
        rw [pseudoConditionNumber, mul_pow, mul_assoc]

/-! ### Deprecated aliases -/

@[deprecated pseudoConditionNumber (since := "2026-10-14")]
noncomputable alias conditionNumber :=
  pseudoConditionNumber

@[deprecated pseudoConditionNumber_def (since := "2026-10-14")]
alias conditionNumber_def :=
  pseudoConditionNumber_def

@[deprecated pseudoConditionNumber_nonneg (since := "2026-10-14")]
alias conditionNumber_nonneg :=
  pseudoConditionNumber_nonneg

@[deprecated pseudoConditionNumber_zero (since := "2026-10-14")]
alias conditionNumber_zero :=
  pseudoConditionNumber_zero

@[deprecated one_le_pseudoConditionNumber (since := "2026-10-14")]
alias one_le_conditionNumber :=
  one_le_pseudoConditionNumber

@[deprecated pseudoConditionNumber_eq_singularValues_div (since := "2026-10-14")]
alias conditionNumber_eq_singularValues_div :=
  pseudoConditionNumber_eq_singularValues_div

@[deprecated pseudoConditionNumber_of_injective (since := "2026-10-14")]
alias conditionNumber_of_injective :=
  pseudoConditionNumber_of_injective

@[deprecated pseudoConditionNumber_of_isUnit (since := "2026-10-14")]
alias conditionNumber_of_isUnit :=
  pseudoConditionNumber_of_isUnit

@[deprecated _root_.Matrix.PosDef.pseudoConditionNumber_eq (since := "2026-10-14")]
alias _root_.Matrix.PosDef.conditionNumber_eq :=
  _root_.Matrix.PosDef.pseudoConditionNumber_eq

@[deprecated pseudoConditionNumber_conjTranspose (since := "2026-10-14")]
alias conditionNumber_conjTranspose :=
  pseudoConditionNumber_conjTranspose

@[deprecated pseudoConditionNumber_pinv (since := "2026-10-14")]
alias conditionNumber_pinv :=
  pseudoConditionNumber_pinv

@[deprecated pseudoConditionNumber_smul (since := "2026-10-14")]
alias conditionNumber_smul :=
  pseudoConditionNumber_smul

@[deprecated pseudoConditionNumber_conjTranspose_mul_self (since := "2026-10-14")]
alias conditionNumber_conjTranspose_mul_self :=
  pseudoConditionNumber_conjTranspose_mul_self

@[deprecated HasOrthonormalCols.pseudoConditionNumber_mul_left (since := "2026-10-14")]
alias HasOrthonormalCols.conditionNumber_mul_left :=
  HasOrthonormalCols.pseudoConditionNumber_mul_left

@[deprecated HasOrthonormalCols.pseudoConditionNumber_eq_one (since := "2026-10-14")]
alias HasOrthonormalCols.conditionNumber_eq_one :=
  HasOrthonormalCols.pseudoConditionNumber_eq_one

@[deprecated pseudoConditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one (since := "2026-10-14")]
alias conditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one :=
  pseudoConditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.pseudoConditionNumber A` is nonnegative. -/
@[positivity NLAlib.pseudoConditionNumber _]
meta def evalPseudoConditionNumber : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    -- match the head after `whnfR` instead of reading arguments with `appArg!`, so that an atom
    -- that is a let-bound variable (from `set`) is rejected, never a panic
    match (← whnfR e).getAppFnArgs with
    | (``NLAlib.pseudoConditionNumber, #[_, _, _, _, _, _, A]) =>
      pure (.nonnegative (← mkAppM ``NLAlib.pseudoConditionNumber_nonneg #[A]))
    | _ => failure

/-! Regression: a `set` atom whose value is a pseudo-condition number, the case that used to
panic in `NLAlib.Matrix.QRIteration.Dichotomy`. -/
example {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] (V : Matrix m n 𝕜) :
    True := by
  set κ := NLAlib.pseudoConditionNumber V
  have : 0 ≤ κ := by positivity
  trivial

example {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] (V : Matrix m n 𝕜)
    (h : 1 ≤ NLAlib.pseudoConditionNumber V) : True := by
  set κ := NLAlib.pseudoConditionNumber V
  have : 0 < 2 * κ ^ 4 := by positivity
  trivial

end Mathlib.Meta.Positivity
