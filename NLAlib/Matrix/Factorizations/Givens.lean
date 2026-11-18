/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR

/-!
# Givens rotations

The Givens rotation `NLAlib.givens i j c s` acts on the coordinates $i$ and $j$ by the matrix
$\begin{bmatrix} c & s \\ -\bar{s} & \bar{c} \end{bmatrix}$ and fixes the others. It is unitary
when $\lvert c \rvert^2 + \lvert s \rvert^2 = 1$, and for every vector there is a rotation that
clears coordinate $j$ into coordinate $i$: `NLAlib.givensOf`, with the coefficients
`NLAlib.givensCoeffs`.

Givens QR of an upper Hessenberg matrix is a total recursion indexed by the step, as Householder
QR in `NLAlib/Matrix/Factorizations/Householder.lean`: step $k$ rotates rows $k$ and $k + 1$ to
clear the subdiagonal entry of column $k$. It never breaks down (a zero pair gives the identity).

## Main definitions

* `NLAlib.givens`: the rotation in the coordinate plane $(i, j)$.
* `NLAlib.givensCoeffs`, `NLAlib.givensOf`: the clearing rotation of a vector.
* `NLAlib.givensHessenbergStep`, `NLAlib.givensHessenbergState`, `NLAlib.givensHessenbergQ`,
  `NLAlib.givensHessenbergR`: Givens QR, step by step.

## Main results

* `NLAlib.givens_apply`: the entries.
* `NLAlib.hasOrthonormalCols_givens`: unitarity.
* `NLAlib.det_givens_eq_mul_star_add_mul_star`, `NLAlib.det_givens`: the determinant.
* `NLAlib.givens_mulVec_apply_left`, `…_right`, `…_of_ne`: the action on a vector.
* `NLAlib.exists_givens_mulVec_apply_eq_zero`: clearing an entry.
* `NLAlib.norm_givensCoeffs_fst_sq_add`, `NLAlib.givensOf_mulVec_apply_right`,
  `NLAlib.givensOf_mulVec_apply_left`: the clearing rotation is unitary and clears.
* `NLAlib.hasOrthonormalCols_givensHessenbergState_fst`,
  `NLAlib.givensHessenbergState_fst_mul_snd`: every step of Givens QR factors the matrix with a
  unitary first factor.
* `NLAlib.givensHessenbergState_apply_of_lt`, `NLAlib.givensHessenbergState_apply_eq_zero_of_le`,
  `NLAlib.givensHessenbergState_snd_apply_eq_zero_of_col`: later steps leave the leading rows
  alone, and trailing zero rows and zero columns stay zero (the freeze of Givens QR past a
  breakdown).
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype n] [DecidableEq n]

/-- The **Givens rotation** in the coordinate plane $(i, j)$: the identity outside rows and
columns $i$, $j$, and $\begin{bmatrix} c & s \\ -\bar{s} & \bar{c} \end{bmatrix}$ on them.
[GolubVanLoan2013, §5.1.8]. -/
def givens (i j : n) (c s : 𝕜) : Matrix n n 𝕜 :=
  1 + (c - 1) • Matrix.single i i 1 + (star c - 1) • Matrix.single j j 1 +
    s • Matrix.single i j 1 - star s • Matrix.single j i 1

omit [Fintype n] in
/-- **The entries of a Givens rotation** in the plane $(i, j)$, $i \ne j$: $c$, $s$ in row $i$
and $-\bar{s}$, $\bar{c}$ in row $j$ at the columns $i$, $j$, and the identity elsewhere.
[GolubVanLoan2013, §5.1.8]. -/
theorem givens_apply {i j : n} (hij : i ≠ j) (c s : 𝕜) (a b : n) :
    givens i j c s a b =
      if a = i then (if b = i then c else if b = j then s else 0)
      else if a = j then (if b = i then -star s else if b = j then star c else 0)
      else if a = b then 1 else 0 := by
  simp only [givens, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, @eq_comm _ i a,
    @eq_comm _ j a, @eq_comm _ i b, @eq_comm _ j b]
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
    by_cases hbj : b = j <;>
    first
    | exact absurd (hai.symm.trans haj) hij
    | exact absurd (hbi.symm.trans hbj) hij
    | simp [hai, haj, hbi, hbj, hij, hij.symm, @eq_comm _ i b, @eq_comm _ j b]

/-- The action of a rotation on a vector, in vector form. -/
private theorem givens_mulVec (i j : n) (c s : 𝕜) (x : n → 𝕜) :
    givens i j c s *ᵥ x = x + ((c - 1) * x i + s * x j) • Pi.single i 1 +
      ((star c - 1) * x j - star s * x i) • Pi.single j 1 := by
  simp only [givens, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul, smul_smul]
  module

/-- The normalisation $\lvert c \rvert^2 + \lvert s \rvert^2 = 1$, in the field:
$\bar{c} c + \bar{s} s = 1$. -/
private theorem star_mul_self_add {c s : 𝕜} (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) :
    star c * c + star s * s = 1 := by
  rw [RCLike.star_def, RCLike.conj_mul, RCLike.conj_mul, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_add, hcs, RCLike.ofReal_one]

/-- Coordinate $i$ of a rotated vector: $c \mathbf{x}_i + s \mathbf{x}_j$. -/
theorem givens_mulVec_apply_left {i j : n} (hij : i ≠ j) (c s : 𝕜) (x : n → 𝕜) :
    (givens i j c s *ᵥ x) i = c * x i + s * x j := by
  rw [givens_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, smul_eq_mul]
  ring

/-- Coordinate $j$ of a rotated vector: $-\bar{s} \mathbf{x}_i + \bar{c} \mathbf{x}_j$. -/
theorem givens_mulVec_apply_right {i j : n} (hij : i ≠ j) (c s : 𝕜) (x : n → 𝕜) :
    (givens i j c s *ᵥ x) j = -star s * x i + star c * x j := by
  rw [givens_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm,
    smul_eq_mul]
  ring

/-- The other coordinates of a rotated vector are unchanged. -/
theorem givens_mulVec_apply_of_ne {i j a : n} (hai : a ≠ i) (haj : a ≠ j) (c s : 𝕜)
    (x : n → 𝕜) : (givens i j c s *ᵥ x) a = x a := by
  rw [givens_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj,
    smul_eq_mul, mul_zero, add_zero]

/-- Left multiplication by a rotation changes only rows $i$ and $j$. -/
theorem givens_mul_apply_of_ne {i j a : n} (hai : a ≠ i) (haj : a ≠ j) (c s : 𝕜)
    (A : Matrix n m 𝕜) (b : m) : (givens i j c s * A) a b = A a b := by
  simp only [givens, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.single_mul_apply_of_ne _ _ _ _ _ hai, Matrix.single_mul_apply_of_ne _ _ _ _ _ haj,
    smul_zero, add_zero, sub_zero]

/-- Right multiplication by a rotation changes only columns $i$ and $j$. -/
theorem mul_givens_apply_of_ne {i j b : n} (hbi : b ≠ i) (hbj : b ≠ j) (c s : 𝕜)
    (A : Matrix m n 𝕜) (a : m) : (A * givens i j c s) a b = A a b := by
  simp only [givens, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_single_apply_of_ne _ _ _ _ _ hbi, Matrix.mul_single_apply_of_ne _ _ _ _ _ hbj,
    smul_zero, add_zero, sub_zero]

/-- Row $i$ of a matrix multiplied on the left by a rotation in the plane $(i, j)$:
$c \mathbf{A}_{i,b} + s \mathbf{A}_{j,b}$. -/
theorem givens_mul_apply_left {i j : n} (hij : i ≠ j) (c s : 𝕜) (A : Matrix n m 𝕜) (b : m) :
    (givens i j c s * A) i b = c * A i b + s * A j b := by
  exact givens_mulVec_apply_left hij c s fun a => A a b

/-- Row $j$ of a matrix multiplied on the left by a rotation in the plane $(i, j)$:
$-\bar{s} \mathbf{A}_{i,b} + \bar{c} \mathbf{A}_{j,b}$. -/
theorem givens_mul_apply_right {i j : n} (hij : i ≠ j) (c s : 𝕜) (A : Matrix n m 𝕜) (b : m) :
    (givens i j c s * A) j b = -star s * A i b + star c * A j b := by
  exact givens_mulVec_apply_right hij c s fun a => A a b

/-- Column $i$ of a matrix multiplied on the right by a rotation in the plane $(i, j)$:
$\mathbf{A}_{a,i} c - \mathbf{A}_{a,j} \bar{s}$. -/
theorem mul_givens_apply_left {i j : n} (hij : i ≠ j) (c s : 𝕜) (A : Matrix m n 𝕜) (a : m) :
    (A * givens i j c s) a i = A a i * c - A a j * star s := by
  simp only [givens, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_single_apply_same,
    Matrix.mul_single_apply_of_ne _ _ _ _ _ hij, smul_eq_mul, mul_one]
  ring

/-- Column $j$ of a matrix multiplied on the right by a rotation in the plane $(i, j)$:
$\mathbf{A}_{a,i} s + \mathbf{A}_{a,j} \bar{c}$. -/
theorem mul_givens_apply_right {i j : n} (hij : i ≠ j) (c s : 𝕜) (A : Matrix m n 𝕜) (a : m) :
    (A * givens i j c s) a j = A a i * s + A a j * star c := by
  simp only [givens, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_single_apply_same,
    Matrix.mul_single_apply_of_ne _ _ _ _ _ hij.symm, smul_eq_mul, mul_one]
  ring

omit [Fintype n] in
/-- The conjugate transpose of a rotation is the rotation with parameters $\bar{c}$, $-s$; for
$\lvert c \rvert^2 + \lvert s \rvert^2 = 1$ it is the inverse rotation. -/
theorem conjTranspose_givens (i j : n) (c s : 𝕜) :
    (givens i j c s)ᴴ = givens i j (star c) (-s) := by
  simp only [givens, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.conjTranspose_single, star_sub,
    star_one, star_star, star_neg]
  module

/-- A Givens rotation is unitary when $\lvert c \rvert^2 + \lvert s \rvert^2 = 1$ and
$i \ne j$. -/
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

/-- A unitary Givens rotation times its conjugate transpose is the identity. -/
theorem givens_mul_conjTranspose_self {i j : n} (hij : i ≠ j) {c s : 𝕜}
    (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) : givens i j c s * (givens i j c s)ᴴ = 1 := by
  exact (hasOrthonormalCols_givens hij hcs).mul_conjTranspose_self

/-- The determinant of a Givens rotation is $c \bar{c} + s \bar{s}$, for any $c$, $s$ and
$i \ne j$. -/
theorem det_givens_eq_mul_star_add_mul_star {i j : n} (hij : i ≠ j) (c s : 𝕜) :
    (givens i j c s).det = c * star c + s * star s := by
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
  ring

/-- The determinant of a unitary Givens rotation is one. -/
theorem det_givens {i j : n} (hij : i ≠ j) {c s : 𝕜} (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) :
    (givens i j c s).det = 1 := by
  rw [det_givens_eq_mul_star_add_mul_star hij, mul_comm c, mul_comm s]
  exact star_mul_self_add hcs

/-- Clearing an entry: for every vector $\mathbf{x}$ and $i \ne j$ there is a unitary Givens
rotation ($\lvert c \rvert^2 + \lvert s \rvert^2 = 1$) that sends coordinate $j$ to zero and
coordinate $i$ to $\sqrt{\lvert \mathbf{x}_i \rvert^2 + \lvert \mathbf{x}_j \rvert^2}$. -/
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

/-! ### The clearing rotation -/

/-- The **Givens coefficients** of a pair $(u, v)$: with $r = \sqrt{\lvert u \rvert^2 +
\lvert v \rvert^2}$, $(c, s) = (\bar{u}/r, \bar{v}/r)$, and $(1, 0)$ when $r = 0$. Then
$cu + sv = r$ and $-\bar{s}u + \bar{c}v = 0$. [GolubVanLoan2013, Algorithm 5.1.3]. -/
noncomputable def givensCoeffs (u v : 𝕜) : 𝕜 × 𝕜 :=
  if Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) = 0 then (1, 0)
  else (star u / (Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) : 𝕜), star v / (Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) : 𝕜))

/-- A pair with $\sqrt{\lvert u \rvert^2 + \lvert v \rvert^2} = 0$ is zero. -/
private theorem eq_zero_and_eq_zero_of_sqrt_eq_zero {u v : 𝕜}
    (h : Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) = 0) : u = 0 ∧ v = 0 := by
  rw [Real.sqrt_eq_zero (by positivity)] at h
  have hu : ‖u‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖v‖]
  have hv : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖v‖]
  exact ⟨norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hu),
    norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hv)⟩

/-- The Givens coefficients are unitary: $\lvert c \rvert^2 + \lvert s \rvert^2 = 1$. -/
theorem norm_givensCoeffs_fst_sq_add (u v : 𝕜) :
    ‖(givensCoeffs u v).1‖ ^ 2 + ‖(givensCoeffs u v).2‖ ^ 2 = 1 := by
  unfold givensCoeffs
  set r : ℝ := Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) with hr
  have hr2 : r ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := Real.sq_sqrt (by positivity)
  split_ifs with h0
  · simp
  · have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    rw [norm_div, norm_div, norm_star, norm_star, RCLike.norm_ofReal, abs_of_pos hrpos,
      div_pow, div_pow, ← add_div, ← hr2, div_self (pow_ne_zero 2 h0)]

/-- The rotated first entry: $cu + sv = \sqrt{\lvert u \rvert^2 + \lvert v \rvert^2}$. -/
theorem givensCoeffs_fst_mul_add (u v : 𝕜) :
    (givensCoeffs u v).1 * u + (givensCoeffs u v).2 * v =
      ((Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) : ℝ) : 𝕜) := by
  have h00 := @eq_zero_and_eq_zero_of_sqrt_eq_zero _ _ u v
  unfold givensCoeffs
  set r : ℝ := Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) with hr
  have hr2 : r ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := Real.sq_sqrt (by positivity)
  split_ifs with h0
  · obtain ⟨hu, hv⟩ := h00 h0
    rw [hu, hv, h0]
    simp
  · have hr0 : (r : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr h0
    have hu : star u * u = ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
      rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
    have hv : star v * v = ((‖v‖ ^ 2 : ℝ) : 𝕜) := by
      rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, hu, hv, ← RCLike.ofReal_add, ← hr2,
      RCLike.ofReal_pow, pow_two, mul_div_assoc, div_self hr0, mul_one]

/-- The rotated second entry vanishes: $-\bar{s}u + \bar{c}v = 0$. -/
theorem neg_star_givensCoeffs_snd_mul_add (u v : 𝕜) :
    -star (givensCoeffs u v).2 * u + star (givensCoeffs u v).1 * v = 0 := by
  have h00 := @eq_zero_and_eq_zero_of_sqrt_eq_zero _ _ u v
  unfold givensCoeffs
  set r : ℝ := Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) with hr
  split_ifs with h0
  · obtain ⟨-, hv⟩ := h00 h0
    simp [hv]
  · rw [star_div₀, star_div₀, star_star, star_star, RCLike.star_def, RCLike.conj_ofReal]
    ring

/-- A pair with second entry zero has zero Givens sine: $(c, s) = (\bar{u}/\lvert u \rvert, 0)$, or
$(1, 0)$ for $u = 0$. -/
theorem givensCoeffs_snd_zero (u : 𝕜) : (givensCoeffs u 0).2 = 0 := by
  unfold givensCoeffs
  split_ifs <;> simp

/-- The **clearing rotation** of $\mathbf{x}$ in the plane $(i, j)$: the Givens rotation with
the coefficients of $(\mathbf{x}_i, \mathbf{x}_j)$, which sends $\mathbf{x}_j$ to $0$ and
$\mathbf{x}_i$ to $\sqrt{\lvert\mathbf{x}_i\rvert^2 + \lvert\mathbf{x}_j\rvert^2}$.
[GolubVanLoan2013, §5.1.8]. -/
noncomputable def givensOf (x : n → 𝕜) (i j : n) : Matrix n n 𝕜 :=
  givens i j (givensCoeffs (x i) (x j)).1 (givensCoeffs (x i) (x j)).2

/-- The clearing rotation is unitary. -/
theorem hasOrthonormalCols_givensOf {i j : n} (hij : i ≠ j) (x : n → 𝕜) :
    HasOrthonormalCols (givensOf x i j) := by
  exact hasOrthonormalCols_givens hij (norm_givensCoeffs_fst_sq_add _ _)

/-- The clearing rotation clears coordinate $j$. -/
theorem givensOf_mulVec_apply_right {i j : n} (hij : i ≠ j) (x : n → 𝕜) :
    (givensOf x i j *ᵥ x) j = 0 := by
  rw [givensOf, givens_mulVec_apply_right hij]
  exact neg_star_givensCoeffs_snd_mul_add _ _

/-- The clearing rotation puts the norm of the pair into coordinate $i$. -/
theorem givensOf_mulVec_apply_left {i j : n} (hij : i ≠ j) (x : n → 𝕜) :
    (givensOf x i j *ᵥ x) i = ((Real.sqrt (‖x i‖ ^ 2 + ‖x j‖ ^ 2) : ℝ) : 𝕜) := by
  rw [givensOf, givens_mulVec_apply_left hij]
  exact givensCoeffs_fst_mul_add _ _

/-! ### Givens QR of an upper Hessenberg matrix -/

section QR

variable {m p : ℕ}

/-- The rotation of step $k$ of Givens QR: in the plane $(k, k + 1)$, clearing entry
$(k + 1, k)$ of $\mathbf{W}$; the identity beyond the size of the matrix. -/
noncomputable def givensHessenbergStep (W : Matrix (Fin m) (Fin p) 𝕜) (k : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  if h : k + 1 < m ∧ k < p then givensOf (W.col ⟨k, h.2⟩) ⟨k, by omega⟩ ⟨k + 1, h.1⟩ else 1

/-- The state of Givens QR after $k$ steps: the accumulated unitary factor
$\mathbf{G}_0^{\mathsf{H}} \cdots \mathbf{G}_{k-1}^{\mathsf{H}}$ and the partially triangularised
matrix $\mathbf{G}_{k-1} \cdots \mathbf{G}_0\mathbf{H}$. [GolubVanLoan2013, Algorithm 5.2.4]. -/
noncomputable def givensHessenbergState (H : Matrix (Fin m) (Fin p) 𝕜) :
    ℕ → Matrix (Fin m) (Fin m) 𝕜 × Matrix (Fin m) (Fin p) 𝕜
  | 0 => (1, H)
  | k + 1 =>
      ((givensHessenbergState H k).1 * (givensHessenbergStep (givensHessenbergState H k).2 k)ᴴ,
        givensHessenbergStep (givensHessenbergState H k).2 k * (givensHessenbergState H k).2)

/-- The unitary factor of Givens QR after all $p$ steps. -/
noncomputable def givensHessenbergQ (H : Matrix (Fin m) (Fin p) 𝕜) : Matrix (Fin m) (Fin m) 𝕜 :=
  (givensHessenbergState H p).1

/-- The upper trapezoidal factor of Givens QR after all $p$ steps. -/
noncomputable def givensHessenbergR (H : Matrix (Fin m) (Fin p) 𝕜) : Matrix (Fin m) (Fin p) 𝕜 :=
  (givensHessenbergState H p).2

/-- The rotation of a step inside the matrix, written out: the Givens rotation in the plane
$(k, k + 1)$ with the coefficients of $(\mathbf{W}_{k,k}, \mathbf{W}_{k+1,k})$. -/
theorem givensHessenbergStep_of_lt (W : Matrix (Fin m) (Fin p) 𝕜) {k : ℕ} (hk : k < m)
    (hm : k + 1 < m) (hp : k < p) :
    givensHessenbergStep W k = givens ⟨k, hk⟩ ⟨k + 1, hm⟩
      (givensCoeffs (W ⟨k, hk⟩ ⟨k, hp⟩) (W ⟨k + 1, hm⟩ ⟨k, hp⟩)).1
      (givensCoeffs (W ⟨k, hk⟩ ⟨k, hp⟩) (W ⟨k + 1, hm⟩ ⟨k, hp⟩)).2 := by
  rw [givensHessenbergStep, dif_pos ⟨hm, hp⟩]
  rfl

/-- The rotation of every step is unitary. -/
theorem hasOrthonormalCols_givensHessenbergStep (W : Matrix (Fin m) (Fin p) 𝕜) (k : ℕ) :
    HasOrthonormalCols (givensHessenbergStep W k) := by
  unfold givensHessenbergStep
  split_ifs with h
  · exact hasOrthonormalCols_givensOf (Fin.ne_of_val_ne (Nat.succ_ne_self k).symm) _
  · exact hasOrthonormalCols_one

/-- Step $k$ changes only rows $k$ and $k + 1$. -/
theorem givensHessenbergStep_mul_apply_of_ne {l : Type*} (W : Matrix (Fin m) (Fin p) 𝕜)
    {k : ℕ} (M : Matrix (Fin m) l 𝕜) {a : Fin m} (ha : (a : ℕ) ≠ k) (ha' : (a : ℕ) ≠ k + 1)
    (b : l) : (givensHessenbergStep W k * M) a b = M a b := by
  unfold givensHessenbergStep
  split_ifs
  · exact givens_mul_apply_of_ne (Fin.ne_of_val_ne ha) (Fin.ne_of_val_ne ha') _ _ M b
  · rw [Matrix.one_mul]

/-- Step $k$ fixes a column that vanishes in rows $k$ and $k + 1$. -/
theorem givensHessenbergStep_mul_apply_of_apply_eq_zero {l : Type*}
    (W : Matrix (Fin m) (Fin p) 𝕜) {k : ℕ} (M : Matrix (Fin m) l 𝕜) {b : l}
    (hb : ∀ a : Fin m, ((a : ℕ) = k ∨ (a : ℕ) = k + 1) → M a b = 0) (a : Fin m) :
    (givensHessenbergStep W k * M) a b = M a b := by
  by_cases ha : (a : ℕ) = k ∨ (a : ℕ) = k + 1
  · by_cases h : k + 1 < m ∧ k < p
    · have h0 : M ⟨k, by omega⟩ b = 0 := hb _ (Or.inl rfl)
      have h1 : M ⟨k + 1, h.1⟩ b = 0 := hb _ (Or.inr rfl)
      have hne : (⟨k, by omega⟩ : Fin m) ≠ ⟨k + 1, h.1⟩ :=
        Fin.ne_of_val_ne (Nat.succ_ne_self k).symm
      rw [givensHessenbergStep_of_lt W (by omega) h.1 h.2, hb a ha]
      rcases ha with ha | ha
      · rw [show a = ⟨k, by omega⟩ from Fin.ext ha,
          givens_mul_apply_left hne, h0, h1, mul_zero, mul_zero,
          add_zero]
      · rw [show a = ⟨k + 1, h.1⟩ from Fin.ext ha,
          givens_mul_apply_right hne, h0, h1, mul_zero, mul_zero,
          add_zero]
    · rw [givensHessenbergStep, dif_neg h, Matrix.one_mul]
  · push Not at ha
    exact givensHessenbergStep_mul_apply_of_ne W M ha.1 ha.2 b

/-- The accumulated factor is unitary, at every step. -/
theorem hasOrthonormalCols_givensHessenbergState_fst (H : Matrix (Fin m) (Fin p) 𝕜) (k : ℕ) :
    HasOrthonormalCols (givensHessenbergState H k).1 := by
  induction k with
  | zero => exact hasOrthonormalCols_one
  | succ k ih => exact ih.mul (hasOrthonormalCols_givensHessenbergStep _ k).conjTranspose

/-- The state factors the matrix at every step:
$(\mathbf{G}_0^{\mathsf{H}} \cdots \mathbf{G}_{k-1}^{\mathsf{H}})(\mathbf{G}_{k-1} \cdots
\mathbf{G}_0\mathbf{H}) = \mathbf{H}$. -/
theorem givensHessenbergState_fst_mul_snd (H : Matrix (Fin m) (Fin p) 𝕜) (k : ℕ) :
    (givensHessenbergState H k).1 * (givensHessenbergState H k).2 = H := by
  induction k with
  | zero => exact Matrix.one_mul H
  | succ k ih =>
    rw [givensHessenbergState, Matrix.mul_assoc,
      ← Matrix.mul_assoc (givensHessenbergStep (givensHessenbergState H k).2 k)ᴴ,
      (hasOrthonormalCols_givensHessenbergStep _ k).conjTranspose_mul_self, Matrix.one_mul, ih]

/-- One more step of Givens QR on the triangularised part. -/
theorem givensHessenbergState_succ_snd (H : Matrix (Fin m) (Fin p) 𝕜) (k : ℕ) :
    (givensHessenbergState H (k + 1)).2 =
      givensHessenbergStep (givensHessenbergState H k).2 k * (givensHessenbergState H k).2 :=
  rfl

/-- One more step of Givens QR on a rotated vector: the conjugate transpose of the accumulated
factor is multiplied on the left by the new rotation. -/
theorem conjTranspose_givensHessenbergState_succ_fst_mulVec (H : Matrix (Fin m) (Fin p) 𝕜)
    (k : ℕ) (v : Fin m → 𝕜) :
    (givensHessenbergState H (k + 1)).1ᴴ *ᵥ v =
      givensHessenbergStep (givensHessenbergState H k).2 k *ᵥ
        ((givensHessenbergState H k).1ᴴ *ᵥ v) := by
  rw [show (givensHessenbergState H (k + 1)).1 = (givensHessenbergState H k).1 *
      (givensHessenbergStep (givensHessenbergState H k).2 k)ᴴ from rfl,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mulVec_mulVec]

/-- Step $k$ changes only coordinates $k$ and $k + 1$ of a vector. -/
theorem givensHessenbergStep_mulVec_apply_of_ne (W : Matrix (Fin m) (Fin p) 𝕜) {k : ℕ}
    (v : Fin m → 𝕜) {a : Fin m} (ha : (a : ℕ) ≠ k) (ha' : (a : ℕ) ≠ k + 1) :
    (givensHessenbergStep W k *ᵥ v) a = v a :=
  givensHessenbergStep_mul_apply_of_ne W (Matrix.of fun i (_ : Unit) => v i) ha ha' ()

/-- One step keeps the coordinates of a column from $r$ on zero, provided the entry it clears is
zero when its plane is $(r - 1, r)$. -/
private theorem givensHessenbergStep_mul_apply_eq_zero_of_le {l : Type*}
    (W : Matrix (Fin m) (Fin p) 𝕜) {k r : ℕ}
    (hW : ∀ (h : k + 1 < m) (h' : k < p), k + 1 = r → W ⟨k + 1, h⟩ ⟨k, h'⟩ = 0)
    (X : Matrix (Fin m) l 𝕜) (b : l) (hX : ∀ a : Fin m, r ≤ (a : ℕ) → X a b = 0) (a : Fin m)
    (ha : r ≤ (a : ℕ)) : (givensHessenbergStep W k * X) a b = 0 := by
  by_cases hak : (a : ℕ) = k ∨ (a : ℕ) = k + 1
  · by_cases h : k + 1 < m ∧ k < p
    · rw [givensHessenbergStep_of_lt W (by omega) h.1 h.2]
      have hne : (⟨k, by omega⟩ : Fin m) ≠ ⟨k + 1, h.1⟩ :=
        Fin.ne_of_val_ne (Nat.succ_ne_self k).symm
      rcases hak with hak | hak
      · rw [show a = ⟨k, by omega⟩ from Fin.ext hak, givens_mul_apply_left hne,
          hX _ (by simp only; omega), hX _ (by simp only; omega), mul_zero, mul_zero, add_zero]
      · rw [show a = ⟨k + 1, h.1⟩ from Fin.ext hak, givens_mul_apply_right hne,
          hX ⟨k + 1, h.1⟩ (by simp only; omega)]
        rcases eq_or_lt_of_le (show r ≤ k + 1 by omega) with hr | hr
        · rw [hW h.1 h.2 hr.symm, givensCoeffs_snd_zero]
          simp
        · rw [hX _ (by simp only; omega)]
          simp
    · rw [givensHessenbergStep, dif_neg h, Matrix.one_mul]
      exact hX a ha
  · push Not at hak
    rw [givensHessenbergStep_mul_apply_of_ne W X hak.1 hak.2]
    exact hX a ha

/-- Givens QR keeps trailing zero rows: if the rows of $\mathbf{H}$ from $r$ on vanish, so do
the rows from $r$ on of every state of its Givens QR, and so do the coordinates from $r$ on of every
rotated vector $\mathbf{v}$ whose coordinates from $r$ on vanish. The rotation of step $r - 1$
clears a zero entry, so its sine is zero. -/
theorem givensHessenbergState_apply_eq_zero_of_le {H : Matrix (Fin m) (Fin p) 𝕜} {r : ℕ}
    (hH : ∀ (a : Fin m) (b : Fin p), r ≤ (a : ℕ) → H a b = 0) {v : Fin m → 𝕜}
    (hv : ∀ a : Fin m, r ≤ (a : ℕ) → v a = 0) (k : ℕ) :
    (∀ (a : Fin m) (b : Fin p), r ≤ (a : ℕ) → (givensHessenbergState H k).2 a b = 0) ∧
      ∀ a : Fin m, r ≤ (a : ℕ) → ((givensHessenbergState H k).1ᴴ *ᵥ v) a = 0 := by
  induction k with
  | zero =>
    refine ⟨hH, fun a ha => ?_⟩
    simp only [givensHessenbergState, Matrix.conjTranspose_one, Matrix.one_mulVec]
    exact hv a ha
  | succ k ih =>
    have hW : ∀ (h : k + 1 < m) (h' : k < p), k + 1 = r →
        (givensHessenbergState H k).2 ⟨k + 1, h⟩ ⟨k, h'⟩ = 0 :=
      fun h h' hr => ih.1 _ _ (by simp only; omega)
    refine ⟨fun a b ha => ?_, fun a ha => ?_⟩
    · rw [givensHessenbergState_succ_snd]
      exact givensHessenbergStep_mul_apply_eq_zero_of_le _ hW _ b (fun a ha => ih.1 a b ha) a ha
    · rw [conjTranspose_givensHessenbergState_succ_fst_mulVec]
      exact givensHessenbergStep_mul_apply_eq_zero_of_le _ hW
        (Matrix.of fun i (_ : Unit) => ((givensHessenbergState H k).1ᴴ *ᵥ v) i) ()
        (fun a ha => ih.2 a ha) a ha

/-- Givens QR keeps zero columns: a column of $\mathbf{H}$ that vanishes vanishes in every
state of its Givens QR. -/
theorem givensHessenbergState_snd_apply_eq_zero_of_col {H : Matrix (Fin m) (Fin p) 𝕜}
    {b : Fin p} (hH : ∀ a : Fin m, H a b = 0) (k : ℕ) (a : Fin m) :
    (givensHessenbergState H k).2 a b = 0 := by
  induction k generalizing a with
  | zero => exact hH a
  | succ k ih =>
    rw [givensHessenbergState_succ_snd,
      givensHessenbergStep_mul_apply_of_apply_eq_zero _ _ (fun a _ => ih a)]
    exact ih a

/-- Later steps leave the leading rows alone: for $k \le j$, rows $a < k$ of the state after
$j$ steps are those after $k$ steps, and so are the coordinates $a < k$ of a rotated vector, since
step $l$ acts on rows $l$ and $l + 1$ only. -/
theorem givensHessenbergState_apply_of_lt (H : Matrix (Fin m) (Fin p) 𝕜) (v : Fin m → 𝕜)
    {k j : ℕ} (hkj : k ≤ j) {a : Fin m} (ha : (a : ℕ) < k) :
    (∀ b : Fin p, (givensHessenbergState H j).2 a b = (givensHessenbergState H k).2 a b) ∧
      ((givensHessenbergState H j).1ᴴ *ᵥ v) a = ((givensHessenbergState H k).1ᴴ *ᵥ v) a := by
  induction j, hkj using Nat.le_induction with
  | base => exact ⟨fun b => rfl, rfl⟩
  | succ j hkj ih =>
    refine ⟨fun b => ?_, ?_⟩
    · rw [givensHessenbergState_succ_snd,
        givensHessenbergStep_mul_apply_of_ne _ _ (by omega) (by omega)]
      exact ih.1 b
    · rw [conjTranspose_givensHessenbergState_succ_fst_mulVec,
        givensHessenbergStep_mulVec_apply_of_ne _ _ (by omega) (by omega)]
      exact ih.2

end QR

/-! ### The exact unitary of a log of rotations -/

/-- The exact Givens rotation of a log entry $(r, p, q)$: rows and columns $r, r + 1$ with the
coefficients `NLAlib.givensCoeffs p q`; the identity when $r + 1 \ge n$. The padding entry
$(0, 0, 0)$ is the identity (`givensCoeffs 0 0` rotates by nothing). -/
noncomputable def givensAt (n : ℕ) (e : ℕ × ℂ × ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  if h : e.1 + 1 < n then
    givens (⟨e.1, by omega⟩ : Fin n) ⟨e.1 + 1, h⟩ (givensCoeffs e.2.1 e.2.2).1
      (givensCoeffs e.2.1 e.2.2).2
  else 1

/-- **The exact unitary of a log of rotations**, $\mathbf{V} = \mathbf{G}_1^{\mathsf H}
\mathbf{G}_2^{\mathsf H}\cdots$, so that applying the entries in order, $\mathbf{Z} \mapsto
\mathbf{G}\mathbf{Z}\mathbf{G}^{\mathsf H}$, is $\mathbf{Z} \mapsto \mathbf{V}^{\mathsf H}
\mathbf{Z}\mathbf{V}$. -/
noncomputable def givensLog (n : ℕ) (L : List (ℕ × ℂ × ℂ)) : Matrix (Fin n) (Fin n) ℂ :=
  (L.map fun e => (givensAt n e)ᴴ).prod

/-- The empty log is the identity. -/
@[simp] theorem givensLog_nil (n : ℕ) : givensLog n [] = 1 := rfl

/-- The unitary of a log has orthonormal columns. -/
theorem hasOrthonormalCols_givensLog (n : ℕ) (L : List (ℕ × ℂ × ℂ)) :
    HasOrthonormalCols (givensLog n L) := by
  induction L with
  | nil => exact hasOrthonormalCols_one
  | cons e L ih =>
    rw [givensLog, List.map_cons, List.prod_cons]
    refine HasOrthonormalCols.mul (HasOrthonormalCols.conjTranspose ?_) ih
    unfold givensAt
    split_ifs with h
    · exact hasOrthonormalCols_givens (by simp [Fin.ext_iff])
        (norm_givensCoeffs_fst_sq_add _ _)
    · exact hasOrthonormalCols_one

/-- Logs compose: the unitary of a concatenation is the product. -/
theorem givensLog_append (n : ℕ) (L L' : List (ℕ × ℂ × ℂ)) :
    givensLog n (L ++ L') = givensLog n L * givensLog n L' := by
  simp [givensLog, List.map_append, List.prod_append]

end NLAlib
