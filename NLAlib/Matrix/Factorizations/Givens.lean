/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR

/-!
# Givens rotations

The Givens rotation `NLAlib.givens i j c s` acts on the coordinates `i` and `j` by the matrix
`[[c, s], [-s̄, c̄]]` and fixes the others. It is unitary when `|c|² + |s|² = 1`, and for every
vector there is a rotation that clears coordinate `j` into coordinate `i`.

## Main definitions

* `NLAlib.givens`: the rotation in the coordinate plane `(i, j)`.

## Main results

* `NLAlib.hasOrthonormalCols_givens`: unitarity.
* `NLAlib.givens_mulVec_apply_left`, `…_right`, `…_of_ne`: the action on a vector.
* `NLAlib.exists_givens_mulVec_apply_eq_zero`: clearing an entry.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype n] [DecidableEq n]

/-- The **Givens rotation** in the coordinate plane `(i, j)`: the identity outside rows and
columns `i`, `j`, and `[[c, s], [-s̄, c̄]]` on them.
[GolubVanLoan2013, §5.1.8]. Port of `NLAlib.givens`, there over `ℝ`. -/
def givens (i j : n) (c s : 𝕜) : Matrix n n 𝕜 :=
  1 + (c - 1) • Matrix.single i i 1 + (star c - 1) • Matrix.single j j 1 +
    s • Matrix.single i j 1 - star s • Matrix.single j i 1

/-- The action of a rotation on a vector, in vector form. -/
private theorem givens_mulVec (i j : n) (c s : 𝕜) (x : n → 𝕜) :
    givens i j c s *ᵥ x = x + ((c - 1) * x i + s * x j) • Pi.single i 1 +
      ((star c - 1) * x j - star s * x i) • Pi.single j 1 := by
  simp only [givens, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul, smul_smul]
  module

/-- The normalisation `|c|² + |s|² = 1`, in the field. -/
private theorem star_mul_self_add {c s : 𝕜} (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) :
    star c * c + star s * s = 1 := by
  rw [RCLike.star_def, RCLike.conj_mul, RCLike.conj_mul, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_add, hcs, RCLike.ofReal_one]

/-- Coordinate `i` of a rotated vector. Port of `NLAlib.givens_mulVec_apply_left`. -/
theorem givens_mulVec_apply_left {i j : n} (hij : i ≠ j) (c s : 𝕜) (x : n → 𝕜) :
    (givens i j c s *ᵥ x) i = c * x i + s * x j := by
  rw [givens_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, smul_eq_mul]
  ring

/-- Coordinate `j` of a rotated vector. Port of `NLAlib.givens_mulVec_apply_right`. -/
theorem givens_mulVec_apply_right {i j : n} (hij : i ≠ j) (c s : 𝕜) (x : n → 𝕜) :
    (givens i j c s *ᵥ x) j = -star s * x i + star c * x j := by
  rw [givens_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm,
    smul_eq_mul]
  ring

/-- The other coordinates of a rotated vector are unchanged.
Port of `NLAlib.givens_mulVec_apply_of_ne`. -/
theorem givens_mulVec_apply_of_ne {i j a : n} (hai : a ≠ i) (haj : a ≠ j) (c s : 𝕜)
    (x : n → 𝕜) : (givens i j c s *ᵥ x) a = x a := by
  rw [givens_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj,
    smul_eq_mul, mul_zero, add_zero]

/-- Left multiplication by a rotation changes only rows `i` and `j`. -/
theorem givens_mul_apply_of_ne {i j a : n} (hai : a ≠ i) (haj : a ≠ j) (c s : 𝕜)
    (A : Matrix n m 𝕜) (b : m) : (givens i j c s * A) a b = A a b := by
  simp only [givens, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.single_mul_apply_of_ne _ _ _ _ _ hai, Matrix.single_mul_apply_of_ne _ _ _ _ _ haj,
    smul_zero, add_zero, sub_zero]

/-- Right multiplication by a rotation changes only columns `i` and `j`. -/
theorem mul_givens_apply_of_ne {i j b : n} (hbi : b ≠ i) (hbj : b ≠ j) (c s : 𝕜)
    (A : Matrix m n 𝕜) (a : m) : (A * givens i j c s) a b = A a b := by
  simp only [givens, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_single_apply_of_ne _ _ _ _ _ hbi, Matrix.mul_single_apply_of_ne _ _ _ _ _ hbj,
    smul_zero, add_zero, sub_zero]

/-- Row `i` of a matrix multiplied on the left by a rotation in the plane `(i, j)`. -/
theorem givens_mul_apply_left {i j : n} (hij : i ≠ j) (c s : 𝕜) (A : Matrix n m 𝕜) (b : m) :
    (givens i j c s * A) i b = c * A i b + s * A j b := by
  exact givens_mulVec_apply_left hij c s fun a => A a b

/-- Row `j` of a matrix multiplied on the left by a rotation in the plane `(i, j)`. -/
theorem givens_mul_apply_right {i j : n} (hij : i ≠ j) (c s : 𝕜) (A : Matrix n m 𝕜) (b : m) :
    (givens i j c s * A) j b = -star s * A i b + star c * A j b := by
  exact givens_mulVec_apply_right hij c s fun a => A a b

/-- Column `i` of a matrix multiplied on the right by a rotation in the plane `(i, j)`. -/
theorem mul_givens_apply_left {i j : n} (hij : i ≠ j) (c s : 𝕜) (A : Matrix m n 𝕜) (a : m) :
    (A * givens i j c s) a i = A a i * c - A a j * star s := by
  simp only [givens, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_single_apply_same,
    Matrix.mul_single_apply_of_ne _ _ _ _ _ hij, smul_eq_mul, mul_one]
  ring

/-- Column `j` of a matrix multiplied on the right by a rotation in the plane `(i, j)`. -/
theorem mul_givens_apply_right {i j : n} (hij : i ≠ j) (c s : 𝕜) (A : Matrix m n 𝕜) (a : m) :
    (A * givens i j c s) a j = A a i * s + A a j * star c := by
  simp only [givens, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_single_apply_same,
    Matrix.mul_single_apply_of_ne _ _ _ _ _ hij.symm, smul_eq_mul, mul_one]
  ring

omit [Fintype n] in
/-- The conjugate transpose of a rotation is the inverse rotation.
Port of `NLAlib.transpose_givens`. -/
theorem conjTranspose_givens (i j : n) (c s : 𝕜) :
    (givens i j c s)ᴴ = givens i j (star c) (-s) := by
  simp only [givens, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.conjTranspose_single, star_sub,
    star_one, star_star, star_neg]
  module

/-- **A Givens rotation is unitary** when `|c|² + |s|² = 1`.
Port of `NLAlib.hasOrthonormalCols_givens`. -/
theorem hasOrthonormalCols_givens {i j : n} (hij : i ≠ j) {c s : 𝕜}
    (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) : HasOrthonormalCols (givens i j c s) := by
  have h := star_mul_self_add hcs
  rw [HasOrthonormalCols, conjTranspose_givens, Matrix.ext_iff_mulVec]
  intro x
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  ext a
  by_cases hai : a = i
  · rw [hai, givens_mulVec_apply_left hij, givens_mulVec_apply_left hij,
      givens_mulVec_apply_right hij]
    linear_combination x i * h
  by_cases haj : a = j
  · rw [haj, givens_mulVec_apply_right hij, givens_mulVec_apply_left hij,
      givens_mulVec_apply_right hij, star_neg, star_star]
    linear_combination x j * h
  · rw [givens_mulVec_apply_of_ne hai haj, givens_mulVec_apply_of_ne hai haj]

/-- A unitary Givens rotation times its conjugate transpose is the identity.
Port of `NLAlib.givens_mul_transpose_self`. -/
theorem givens_mul_conjTranspose_self {i j : n} (hij : i ≠ j) {c s : 𝕜}
    (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) : givens i j c s * (givens i j c s)ᴴ = 1 := by
  exact (hasOrthonormalCols_givens hij hcs).mul_conjTranspose_self

/-- The determinant of a unitary Givens rotation is one. -/
theorem det_givens {i j : n} (hij : i ≠ j) {c s : 𝕜} (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) :
    (givens i j c s).det = 1 := by
  have h := star_mul_self_add hcs
  let ei : n → 𝕜 := Pi.single i 1
  let ej : n → 𝕜 := Pi.single j 1
  let U : Matrix n (Fin 2) 𝕜 := Matrix.of fun a k => (![ei a, ej a] : Fin 2 → 𝕜) k
  let V : Matrix (Fin 2) n 𝕜 := Matrix.of fun k b =>
    (![(c - 1) * ei b + s * ej b, -star s * ei b + (star c - 1) * ej b] : Fin 2 → 𝕜) k
  have hG : givens i j c s = 1 + U * V := by
    ext a b
    simp only [givens, Matrix.single_eq_single_vecMulVec_single, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Fin.sum_univ_two, U, V, ei, ej, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_eq_mul]
    ring
  have hVU : V * U = !![c - 1, s; -star s, star c - 1] := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [U, V, ei, ej, Matrix.mul_apply, Pi.single_apply, hij, hij.symm]
  rw [hG, Matrix.det_one_add_mul_comm, hVU, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.one_apply_ne,
    ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true]
  linear_combination h

/-- **Clearing an entry.** For every vector `x` and `i ≠ j` there is a unitary Givens rotation
that sends coordinate `j` to zero and coordinate `i` to `√(|x i|² + |x j|²)`.
Port of `NLAlib.givensRotation_transpose_mulVec_apply_right` and `…_left`, there over `ℝ`. -/
theorem exists_givens_mulVec_apply_eq_zero {i j : n} (hij : i ≠ j) (x : n → 𝕜) :
    ∃ c s : 𝕜, ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1 ∧ (givens i j c s *ᵥ x) j = 0 ∧
      (givens i j c s *ᵥ x) i = ((√(‖x i‖ ^ 2 + ‖x j‖ ^ 2) : ℝ) : 𝕜) := by
  set r : ℝ := √(‖x i‖ ^ 2 + ‖x j‖ ^ 2) with hr
  have hr2 : r ^ 2 = ‖x i‖ ^ 2 + ‖x j‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hxi : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
  have hxj : star (x j) * x j = ((‖x j‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
  by_cases h0 : r = 0
  · have hi : x i = 0 := by
      have : ‖x i‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x i‖, sq_nonneg ‖x j‖]
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    have hj : x j = 0 := by
      have : ‖x j‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x i‖, sq_nonneg ‖x j‖]
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    refine ⟨1, 0, by simp, ?_, ?_⟩
    · rw [givens_mulVec_apply_right hij, hi, hj]
      simp
    · rw [givens_mulVec_apply_left hij, hi, hj, h0]
      simp
  · have hr0 : (r : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr h0
    have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    refine ⟨star (x i) / (r : 𝕜), star (x j) / (r : 𝕜), ?_, ?_, ?_⟩
    · rw [norm_div, norm_div, norm_star, norm_star, RCLike.norm_ofReal, abs_of_pos hrpos,
        div_pow, div_pow, ← add_div, ← hr2, div_self (pow_ne_zero 2 h0)]
    · rw [givens_mulVec_apply_right hij, star_div₀, star_div₀, star_star, star_star,
        RCLike.star_def, RCLike.conj_ofReal]
      field_simp
      ring
    · rw [givens_mulVec_apply_left hij, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, hxi,
        hxj, ← RCLike.ofReal_add, ← hr2, RCLike.ofReal_pow, pow_two, mul_div_assoc,
        div_self hr0, mul_one]

end NLAlib
