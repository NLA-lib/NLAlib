/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Positivity.Core

/-!
# The Frobenius norm and inner product

`NLAlib.frobNorm A` is the Frobenius norm `√(∑ i j, ‖A i j‖ ^ 2)` and `NLAlib.frobInner A B` is
the real Frobenius inner product `re (tr (Aᴴ B))`. They are named functions because Mathlib's
matrix norms are scoped instances; `NLAlib.frobNorm_eq_norm` is the bridge.

The squared Frobenius norm has no name of its own: it is always written `frobNorm A ^ 2`.
Statements that are naturally quadratic (Pythagoras, sums over entries or columns) are stated in
that form; `positivity` knows `frobNorm`, so `gcongr` passes between a bound and its square.

## Main definitions

* `NLAlib.frobInner`: the real Frobenius inner product.
* `NLAlib.frobNorm`: the Frobenius norm.

## Main results

* `NLAlib.frobNorm_sq_eq_sum`, `NLAlib.frobNorm_sq_eq_re_trace`: the squared norm as an entry sum
  and as a trace.
* `NLAlib.frobNorm_sq_eq_sum_sq`, `NLAlib.frobInner_eq_sum_mul`: the entry sums over `ℝ`.
* `NLAlib.frobNorm_add_sq`, `NLAlib.frobNorm_add_sq_of_frobInner_eq_zero`: the polar identity and
  Pythagoras.
* `NLAlib.abs_frobInner_le`: Cauchy–Schwarz.
* `NLAlib.frobInner_mul_left`, `NLAlib.frobInner_mul_right`: adjoints move across the pairing.
* `NLAlib.frobNorm_eq_norm`: the bridge to Mathlib's Frobenius norm.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### The Frobenius inner product -/

/-- The real **Frobenius inner product** `re (tr (Aᴴ B)) = ∑ i j, re (conj (A i j) * B i j)`. It
is real-valued and real-bilinear; the `𝕜`-valued pairing is Mathlib's `(Aᴴ * B).trace`. -/
def frobInner (A B : Matrix m n 𝕜) : ℝ :=
  RCLike.re (Aᴴ * B).trace

/-- `frobInner A B` unfolds to `re (Aᴴ * B).trace`. This is the only bridge between the two
pairings. -/
theorem frobInner_eq_re_trace (A B : Matrix m n 𝕜) : frobInner A B = RCLike.re (Aᴴ * B).trace :=
  rfl

/-- The Frobenius inner product as a sum over entries. Port of `NLAlib.frobInner_eq_sum_re`. -/
theorem frobInner_eq_sum (A B : Matrix m n 𝕜) :
    frobInner A B = ∑ i, ∑ j, RCLike.re (star (A i j) * B i j) := by
  simp only [frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    map_sum]
  exact Finset.sum_comm

/-- Over `ℝ` the Frobenius inner product is the sum of the products of the entries. This is
`NLAlib.frobInner_eq_sum` with the conjugation and the real part removed, the form to rewrite
with under an integral or a sum. Port of `NLAlib.frobInner_eq_sum_mul`. -/
theorem frobInner_eq_sum_mul (A B : Matrix m n ℝ) : frobInner A B = ∑ i, ∑ j, A i j * B i j := by
  simp only [frobInner_eq_sum, star_trivial, RCLike.re_to_real]

/-- The Frobenius inner product as the real part of the trace of `A * Bᴴ`, by cyclicity of the
trace: `re (tr (Aᴴ B)) = re (tr (A Bᴴ))`. The two traces are complex conjugates of each other, so
only the real parts agree. Port of `NLAlib.frobInner_eq_re_trace_mul_conjTranspose`. -/
theorem frobInner_eq_re_trace_mul_conjTranspose (A B : Matrix m n 𝕜) :
    frobInner A B = RCLike.re (A * Bᴴ).trace := by
  rw [frobInner, Matrix.trace_mul_comm A, ← RCLike.conj_re (Bᴴ * A).trace, ← RCLike.star_def,
    ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- The Frobenius inner product is symmetric. Port of `NLAlib.frobInner_comm`. -/
theorem frobInner_comm (A B : Matrix m n 𝕜) : frobInner A B = frobInner B A := by
  rw [frobInner_eq_sum, frobInner_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← RCLike.conj_re (star (B i j) * A i j), ← RCLike.star_def, star_mul, star_star]

/-- The Frobenius inner product is additive in its first argument. -/
theorem frobInner_add_left (A B C : Matrix m n 𝕜) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  simp only [frobInner, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add, map_add]

/-- The Frobenius inner product is additive in its second argument. -/
theorem frobInner_add_right (A B C : Matrix m n 𝕜) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  simp only [frobInner, Matrix.mul_add, Matrix.trace_add, map_add]

/-- The Frobenius inner product commutes with subtraction in its first argument. -/
theorem frobInner_sub_left (A B C : Matrix m n 𝕜) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  simp only [frobInner, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, map_sub]

/-- The Frobenius inner product commutes with subtraction in its second argument. -/
theorem frobInner_sub_right (A B C : Matrix m n 𝕜) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  simp only [frobInner, Matrix.mul_sub, Matrix.trace_sub, map_sub]

/-- The Frobenius inner product commutes with negation of its first argument. -/
@[simp]
theorem frobInner_neg_left (A B : Matrix m n 𝕜) : frobInner (-A) B = -frobInner A B := by
  simp only [frobInner, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.trace_neg, map_neg]

/-- The Frobenius inner product commutes with negation of its second argument. -/
@[simp]
theorem frobInner_neg_right (A B : Matrix m n 𝕜) : frobInner A (-B) = -frobInner A B := by
  simp only [frobInner, Matrix.mul_neg, Matrix.trace_neg, map_neg]

/-- The Frobenius inner product is real-homogeneous in its first argument. -/
theorem frobInner_smul_left (c : ℝ) (A B : Matrix m n 𝕜) :
    frobInner (c • A) B = c * frobInner A B := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), frobInner, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, RCLike.star_def, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, frobInner]

/-- The Frobenius inner product is real-homogeneous in its second argument. -/
theorem frobInner_smul_right (c : ℝ) (A B : Matrix m n 𝕜) :
    frobInner A (c • B) = c * frobInner A B := by
  rw [frobInner_comm, frobInner_smul_left, frobInner_comm]

/-- The Frobenius inner product with zero on the left is zero. -/
@[simp]
theorem frobInner_zero_left (B : Matrix m n 𝕜) : frobInner 0 B = 0 := by
  simp [frobInner]

/-- The Frobenius inner product with zero on the right is zero. -/
@[simp]
theorem frobInner_zero_right (A : Matrix m n 𝕜) : frobInner A 0 = 0 := by
  simp [frobInner]

/-- The Frobenius inner product commutes with finite sums in its first argument. -/
theorem frobInner_sum_left {ι : Type*} (s : Finset ι) (A : ι → Matrix m n 𝕜) (B : Matrix m n 𝕜) :
    frobInner (∑ i ∈ s, A i) B = ∑ i ∈ s, frobInner (A i) B := by
  simp only [frobInner, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.trace_sum, map_sum]

/-- The Frobenius inner product commutes with finite sums in its second argument. -/
theorem frobInner_sum_right {ι : Type*} (s : Finset ι) (A : Matrix m n 𝕜) (B : ι → Matrix m n 𝕜) :
    frobInner A (∑ i ∈ s, B i) = ∑ i ∈ s, frobInner A (B i) := by
  simp only [frobInner, Matrix.mul_sum, Matrix.trace_sum, map_sum]

/-- The Frobenius inner product is invariant under taking conjugate transposes of both
arguments. Port of `NLAlib.frobInner_conjTranspose`. -/
@[simp]
theorem frobInner_conjTranspose (A B : Matrix m n 𝕜) : frobInner Aᴴ Bᴴ = frobInner A B := by
  rw [frobInner, frobInner, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm,
    ← RCLike.conj_re (Bᴴ * A).trace, ← RCLike.star_def, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- A left factor moves across the Frobenius inner product as its conjugate transpose:
`⟨C A, B⟩ = ⟨A, Cᴴ B⟩`. Port of `NLAlib.frobInner_mul_mul`. -/
theorem frobInner_mul_left (C : Matrix l m 𝕜) (A : Matrix m n 𝕜) (B : Matrix l n 𝕜) :
    frobInner (C * A) B = frobInner A (Cᴴ * B) := by
  rw [frobInner, frobInner, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A right factor moves across the Frobenius inner product as its conjugate transpose:
`⟨A C, B⟩ = ⟨A, B Cᴴ⟩`. -/
theorem frobInner_mul_right (A : Matrix m n 𝕜) (C : Matrix n p 𝕜) (B : Matrix m p 𝕜) :
    frobInner (A * C) B = frobInner A (B * Cᴴ) := by
  rw [frobInner, frobInner, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc]

/-! ### The Frobenius norm -/

/-- The **Frobenius norm** `√(∑ i j, ‖A i j‖ ^ 2)`. Its square is written `frobNorm A ^ 2`.
[GolubVanLoan2013, §2.3.1]. -/
noncomputable def frobNorm (A : Matrix m n 𝕜) : ℝ :=
  √(∑ i, ∑ j, ‖A i j‖ ^ 2)

/-- The Frobenius norm is nonnegative. -/
theorem frobNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ frobNorm A := by
  exact Real.sqrt_nonneg _

/-- The squared Frobenius norm is the sum of the squared moduli of the entries.
Port of `NLAlib.frobSq_eq_sum_norm_sq`. -/
theorem frobNorm_sq_eq_sum (A : Matrix m n 𝕜) : frobNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- The Frobenius norm is the Euclidean norm of the entries read as a vector indexed by
`m × n`. -/
theorem frobNorm_eq_norm_toLp_uncurry (A : Matrix m n 𝕜) :
    frobNorm A = ‖WithLp.toLp 2 (Function.uncurry A)‖ := by
  rw [← Real.sqrt_sq (frobNorm_nonneg A), frobNorm_sq_eq_sum, EuclideanSpace.norm_eq,
    Fintype.sum_prod_type]
  rfl

/-- Over `ℝ` the squared Frobenius norm is the sum of the squared entries. This is
`NLAlib.frobNorm_sq_eq_sum` with the absolute values removed, the form to rewrite with under an
integral or a sum. Port of `NLAlib.frobSq_eq_sum_sq`. -/
theorem frobNorm_sq_eq_sum_sq (A : Matrix m n ℝ) : frobNorm A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  simp only [frobNorm_sq_eq_sum, Real.norm_eq_abs, sq_abs]

/-- The Frobenius inner product of a matrix with itself is its squared Frobenius norm. -/
@[simp]
theorem frobInner_self (A : Matrix m n 𝕜) : frobInner A A = frobNorm A ^ 2 := by
  rw [frobNorm_sq_eq_sum, frobInner_eq_sum]
  simp only [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The squared Frobenius norm is the real part of the trace of the Gram matrix.
Port of `NLAlib.frobSq_eq_re_trace_conjTranspose_mul_self`. -/
theorem frobNorm_sq_eq_re_trace (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = RCLike.re (Aᴴ * A).trace := by
  rw [← frobInner_self, frobInner]

/-- The squared Frobenius norm is the sum of the squared Euclidean norms of the columns.
Port of `NLAlib.frobSq_eq_sum_frobSq_col`. -/
theorem frobNorm_sq_eq_sum_col (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = ∑ j, ‖WithLp.toLp 2 (A.col j)‖ ^ 2 := by
  simp only [frobNorm_sq_eq_sum, EuclideanSpace.norm_sq_eq, Matrix.col_apply]
  exact Finset.sum_comm

/-- The squared Frobenius norm is the sum of the squared Euclidean norms of the rows. -/
theorem frobNorm_sq_eq_sum_row (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = ∑ i, ‖WithLp.toLp 2 (A.row i)‖ ^ 2 := by
  simp only [frobNorm_sq_eq_sum, EuclideanSpace.norm_sq_eq, Matrix.row_apply]

open scoped Matrix.Norms.Frobenius in
/-- **Bridge to Mathlib.** `frobNorm A` is the norm of `A` in the `Matrix.Norms.Frobenius`
scope. Port of `NLAlib.frobNorm_eq_norm`. -/
theorem frobNorm_eq_norm (A : Matrix m n 𝕜) : frobNorm A = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, frobNorm, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]

/-- The Frobenius norm of the zero matrix is zero. -/
@[simp]
theorem frobNorm_zero : frobNorm (0 : Matrix m n 𝕜) = 0 := by
  simp [frobNorm]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm vanishes only at the zero matrix. -/
@[simp]
theorem frobNorm_eq_zero_iff {A : Matrix m n 𝕜} : frobNorm A = 0 ↔ A = 0 := by
  rw [frobNorm_eq_norm, norm_eq_zero]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm is invariant under negation. -/
@[simp]
theorem frobNorm_neg (A : Matrix m n 𝕜) : frobNorm (-A) = frobNorm A := by
  rw [frobNorm_eq_norm, frobNorm_eq_norm, norm_neg]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm of a difference is symmetric. -/
theorem frobNorm_sub_comm (A B : Matrix m n 𝕜) : frobNorm (A - B) = frobNorm (B - A) := by
  rw [frobNorm_eq_norm, frobNorm_eq_norm, norm_sub_rev]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm is absolutely homogeneous. -/
theorem frobNorm_smul (c : 𝕜) (A : Matrix m n 𝕜) : frobNorm (c • A) = ‖c‖ * frobNorm A := by
  rw [frobNorm_eq_norm, frobNorm_eq_norm, norm_smul]

/-- The Frobenius norm is absolutely homogeneous for the real scalar action on a `𝕜`-matrix. -/
theorem frobNorm_real_smul (a : ℝ) (A : Matrix m n 𝕜) : frobNorm (a • A) = |a| * frobNorm A := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), frobNorm_smul, RCLike.norm_ofReal]

/-- **Cauchy–Schwarz** for the Frobenius inner product.
Port of `NLAlib.abs_frobInner_le_frobNorm_mul_frobNorm`. -/
theorem abs_frobInner_le (A B : Matrix m n 𝕜) : |frobInner A B| ≤ frobNorm A * frobNorm B := by
  have hA : frobNorm A = √(∑ x : m × n, ‖A x.1 x.2‖ ^ 2) :=
    congrArg Real.sqrt (Fintype.sum_prod_type' fun i j => ‖A i j‖ ^ 2).symm
  have hB : frobNorm B = √(∑ x : m × n, ‖B x.1 x.2‖ ^ 2) :=
    congrArg Real.sqrt (Fintype.sum_prod_type' fun i j => ‖B i j‖ ^ 2).symm
  have hAB : frobInner A B = ∑ x : m × n, RCLike.re (star (A x.1 x.2) * B x.1 x.2) :=
    (frobInner_eq_sum A B).trans
      (Fintype.sum_prod_type' fun i j => RCLike.re (star (A i j) * B i j)).symm
  rw [hA, hB, hAB]
  calc |∑ x : m × n, RCLike.re (star (A x.1 x.2) * B x.1 x.2)|
      ≤ ∑ x : m × n, ‖A x.1 x.2‖ * ‖B x.1 x.2‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        refine (RCLike.abs_re_le_norm _).trans_eq ?_
        rw [norm_mul, norm_star]
    _ ≤ √(∑ x : m × n, ‖A x.1 x.2‖ ^ 2) * √(∑ x : m × n, ‖B x.1 x.2‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- Cauchy–Schwarz without the absolute value. -/
theorem frobInner_le (A B : Matrix m n 𝕜) : frobInner A B ≤ frobNorm A * frobNorm B := by
  exact (le_abs_self _).trans (abs_frobInner_le A B)

open scoped Matrix.Norms.Frobenius in
/-- The triangle inequality for the Frobenius norm. -/
theorem frobNorm_add_le (A B : Matrix m n 𝕜) : frobNorm (A + B) ≤ frobNorm A + frobNorm B := by
  simp only [frobNorm_eq_norm]
  exact norm_add_le A B

open scoped Matrix.Norms.Frobenius in
/-- The triangle inequality for a difference. -/
theorem frobNorm_sub_le (A B : Matrix m n 𝕜) : frobNorm (A - B) ≤ frobNorm A + frobNorm B := by
  simp only [frobNorm_eq_norm]
  exact norm_sub_le A B

open scoped Matrix.Norms.Frobenius in
/-- The reverse triangle inequality for the Frobenius norm. -/
theorem abs_frobNorm_sub_frobNorm_le (A B : Matrix m n 𝕜) :
    |frobNorm A - frobNorm B| ≤ frobNorm (A - B) := by
  simp only [frobNorm_eq_norm]
  exact abs_norm_sub_norm_le A B

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm of a finite sum is at most the sum of the Frobenius norms. -/
theorem frobNorm_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix m n 𝕜) :
    frobNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, frobNorm (A i) := by
  simp only [frobNorm_eq_norm]
  exact norm_sum_le s A

/-- The polar identity: `‖A + B‖² = ‖A‖² + 2 ⟨A, B⟩ + ‖B‖²`. Port of `NLAlib.frobSq_add`. -/
theorem frobNorm_add_sq (A B : Matrix m n 𝕜) :
    frobNorm (A + B) ^ 2 = frobNorm A ^ 2 + 2 * frobInner A B + frobNorm B ^ 2 := by
  rw [← frobInner_self, ← frobInner_self, ← frobInner_self, frobInner_add_left,
    frobInner_add_right, frobInner_add_right, frobInner_comm B A]
  ring

/-- The polar identity for a difference. Port of `NLAlib.frobSq_sub`. -/
theorem frobNorm_sub_sq (A B : Matrix m n 𝕜) :
    frobNorm (A - B) ^ 2 = frobNorm A ^ 2 - 2 * frobInner A B + frobNorm B ^ 2 := by
  rw [← frobInner_self, ← frobInner_self, ← frobInner_self, frobInner_sub_left,
    frobInner_sub_right, frobInner_sub_right, frobInner_comm B A]
  ring

/-- **Pythagoras** in the Frobenius norm.
Port of `NLAlib.frobSq_add_of_frobInner_eq_zero`. -/
theorem frobNorm_add_sq_of_frobInner_eq_zero {A B : Matrix m n 𝕜} (h : frobInner A B = 0) :
    frobNorm (A + B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  rw [frobNorm_add_sq, h, mul_zero, add_zero]

/-- Pythagoras for a difference. Port of `NLAlib.frobSq_sub_of_frobInner_eq_zero`. -/
theorem frobNorm_sub_sq_of_frobInner_eq_zero {A B : Matrix m n 𝕜} (h : frobInner A B = 0) :
    frobNorm (A - B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  rw [frobNorm_sub_sq, h, mul_zero, sub_zero]

/-! ### Transposes, reindexing and special matrices -/

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm is invariant under the conjugate transpose. -/
@[simp]
theorem frobNorm_conjTranspose (A : Matrix m n 𝕜) : frobNorm Aᴴ = frobNorm A := by
  rw [frobNorm_eq_norm, frobNorm_eq_norm, Matrix.frobenius_norm_conjTranspose]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm is invariant under the transpose. -/
@[simp]
theorem frobNorm_transpose (A : Matrix m n 𝕜) : frobNorm Aᵀ = frobNorm A := by
  rw [frobNorm_eq_norm, frobNorm_eq_norm, Matrix.frobenius_norm_transpose]

/-- The Frobenius norm is invariant under relabelling rows and columns by bijections.
Port of `NLAlib.frobNorm_reindex`. -/
@[simp]
theorem frobNorm_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    frobNorm (A.submatrix e₁ e₂) = frobNorm A := by
  rw [frobNorm, frobNorm]
  simp only [Matrix.submatrix_apply]
  exact congrArg Real.sqrt ((e₁.sum_comp fun i => ∑ j, ‖A i (e₂ j)‖ ^ 2).trans
    (Finset.sum_congr rfl fun i _ => e₂.sum_comp fun j => ‖A i j‖ ^ 2))

/-- The squared Frobenius norm of a diagonal matrix. Port of `NLAlib.frobSq_diagonal`. -/
theorem frobNorm_diagonal_sq [DecidableEq n] (d : n → 𝕜) :
    frobNorm (Matrix.diagonal d) ^ 2 = ∑ i, ‖d i‖ ^ 2 := by
  rw [frobNorm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)])
    (fun h => (h (Finset.mem_univ i)).elim), Matrix.diagonal_apply_eq]

/-- The squared Frobenius norm of the identity is the dimension.
Port of `NLAlib.frobNorm_one_sq`. -/
theorem frobNorm_one_sq [DecidableEq n] :
    frobNorm (1 : Matrix n n 𝕜) ^ 2 = Fintype.card n := by
  rw [← Matrix.diagonal_one, frobNorm_diagonal_sq]
  simp

/-- The Frobenius norm of a rank-one matrix `u vᵀ` is the product of the Euclidean norms. -/
theorem frobNorm_vecMulVec (u : m → 𝕜) (v : n → 𝕜) :
    frobNorm (Matrix.vecMulVec u v) = ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _), frobNorm, Finset.sum_mul_sum]
  simp only [Matrix.vecMulVec_apply, norm_mul, mul_pow]

/-- Every entry is bounded by the Frobenius norm. -/
theorem norm_apply_le_frobNorm (A : Matrix m n 𝕜) (i : m) (j : n) : ‖A i j‖ ≤ frobNorm A := by
  refine Real.le_sqrt_of_sq_le ?_
  exact (Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i))

/-- The Frobenius norm is compatible with the Euclidean vector norm.
Port of `NLAlib.sum_norm_sq_mulVec_le_frobSq`. -/
theorem norm_toLp_mulVec_le_frobNorm_mul (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ frobNorm A * ‖WithLp.toLp 2 x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (frobNorm_nonneg A) (norm_nonneg _))).1 ?_
  rw [mul_pow, frobNorm_sq_eq_sum, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
  calc ‖(A *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The Frobenius norm is continuous for the entrywise topology on matrices. -/
theorem continuous_frobNorm : Continuous (frobNorm : Matrix m n 𝕜 → ℝ) := by
  change Continuous fun A : Matrix m n 𝕜 => √(∑ i, ∑ j, ‖A i j‖ ^ 2)
  fun_prop

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.frobNorm A` is nonnegative. -/
@[positivity NLAlib.frobNorm _]
meta def evalFrobNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.frobNorm_nonneg #[e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
