/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import NLAlib.Matrix.Norms.Compare

/-!
# Circulant matrices and the discrete Fourier transform

A circulant matrix is Mathlib's `Matrix.circulant v`. The powers of an `n`-th root of unity form
an eigenvector, with eigenvalue a value of the discrete Fourier transform of `v`; over `ℂ` the
unitary Fourier matrix diagonalises every circulant matrix. A matrix is circulant exactly when it
commutes with the cyclic shift.

## Main definitions

* `NLAlib.fourierMatrix`: the unitary `n × n` discrete Fourier transform matrix.

## Main results

* `NLAlib.circulant_mulVec_pow`: eigenvectors of a circulant matrix, over any field.
* `NLAlib.hasOrthonormalCols_fourierMatrix`.
* `NLAlib.circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose`: Fourier diagonalisation.
* `NLAlib.specNorm_circulant_le_iff`: the spectral norm is the largest Fourier coefficient.
* `NLAlib.mul_circulant_single_comm_iff`: characterisation by commutation with the shift.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **Eigenvectors of a circulant matrix.** For an `n`-th root of unity `ζ` in a field, the
vector of powers of `ζ` is an eigenvector of `circulant v` with eigenvalue `∑ l, v l * ζ⁻ˡ`.
[HornJohnson2013, §0.9.6]. -/
theorem circulant_mulVec_pow {K : Type*} [Field K] (v : Fin n → K) {ζ : K} (hζ : ζ ^ n = 1) :
    (Matrix.circulant v *ᵥ fun j : Fin n => ζ ^ (j : ℕ)) =
      (∑ l : Fin n, v l * ζ⁻¹ ^ (l : ℕ)) • fun j : Fin n => ζ ^ (j : ℕ) := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow n.succ_ne_zero] at hζ
    exact zero_ne_one hζ
  funext i
  have key : ∀ l : Fin (n + 1), ζ ^ ((i - l : Fin (n + 1)) : ℕ) = ζ ^ (i : ℕ) * ζ⁻¹ ^ (l : ℕ) := by
    intro l
    rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hζ0), ← pow_add, pow_eq_pow_mod _ hζ,
      ← Fin.val_add, sub_add_cancel]
  rw [Matrix.mulVec, dotProduct, ← (Equiv.subLeft i).sum_comp]
  simp only [Matrix.circulant_apply, Equiv.subLeft_apply, sub_sub_cancel, key, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Right multiplication by the cyclic shift moves the columns. -/
private theorem mul_circulant_single_apply {R : Type*} [Semiring R] [NeZero n]
    (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (A * Matrix.circulant (Pi.single 1 1) : Matrix (Fin n) (Fin n) R) i j = A i (j + 1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (j + 1)]
  · rw [Matrix.circulant_apply, add_sub_cancel_left, Pi.single_eq_same, mul_one]
  · intro k _ hk
    rw [Matrix.circulant_apply, Pi.single_eq_of_ne, mul_zero]
    exact fun h => hk (by rw [← h, add_sub_cancel])
  · exact fun h => absurd (Finset.mem_univ _) h

/-- Left multiplication by the cyclic shift moves the rows. -/
private theorem circulant_single_mul_apply {R : Type*} [Semiring R] [NeZero n]
    (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Matrix.circulant (Pi.single 1 1) * A : Matrix (Fin n) (Fin n) R) i j = A (i - 1) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - 1)]
  · rw [Matrix.circulant_apply, sub_sub_cancel, Pi.single_eq_same, one_mul]
  · intro k _ hk
    rw [Matrix.circulant_apply, Pi.single_eq_of_ne, zero_mul]
    exact fun h => hk (by rw [← h, sub_sub_cancel])
  · exact fun h => absurd (Finset.mem_univ _) h

/-- A matrix that commutes with the cyclic shift is the circulant matrix of its first column.
Port of `NLAlib.eq_circulant_of_commute_cyclicShift`. -/
theorem eq_circulant_of_mul_circulant_single_comm {R : Type*} [Semiring R] [NeZero n]
    {A : Matrix (Fin n) (Fin n) R}
    (h : A * Matrix.circulant (Pi.single 1 1) = Matrix.circulant (Pi.single 1 1) * A) :
    A = Matrix.circulant fun i => A i 0 := by
  have hstep : ∀ i j, A i (j + 1) = A (i - 1) j := fun i j => by
    have h' := congrFun (congrFun h i) j
    rwa [mul_circulant_single_apply, circulant_single_mul_apply] at h'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have hall : ∀ j i : Fin (k + 1), A i j = A (i - j) 0 := fun j =>
    Fin.induction (motive := fun j => ∀ i, A i j = A (i - j) 0) (fun i => by rw [sub_zero])
      (fun j ih i => by rw [← Fin.coeSucc_eq_succ, hstep, ih, sub_sub, add_comm]) j
  ext i j
  rw [Matrix.circulant_apply, hall]

/-- **A matrix commutes with the cyclic shift exactly when it is circulant.**
Port of `NLAlib.commute_cyclicShift_iff_exists_circulant`, there over `ℝ`. -/
theorem mul_circulant_single_comm_iff {R : Type*} [Semiring R] [NeZero n]
    (A : Matrix (Fin n) (Fin n) R) :
    A * Matrix.circulant (Pi.single 1 1) = Matrix.circulant (Pi.single 1 1) * A ↔
      ∃ v, A = Matrix.circulant v := by
  refine ⟨fun h => ⟨_, eq_circulant_of_mul_circulant_single_comm h⟩, ?_⟩
  rintro ⟨v, rfl⟩
  ext i j
  rw [mul_circulant_single_apply, circulant_single_mul_apply, Matrix.circulant_apply,
    Matrix.circulant_apply, sub_sub, add_comm 1 j]

/-! ### The Fourier matrix -/

/-- The **Fourier matrix**: the unitary matrix of the discrete Fourier transform on `Fin n`, with
entries `exp (2π i j k / n) / √n`. -/
noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / n) / (√(n : ℝ) : ℂ)

/-- Entries of the Fourier matrix have modulus `1 / √n`. -/
theorem norm_fourierMatrix_apply (j k : Fin n) : ‖fourierMatrix n j k‖ = (√(n : ℝ))⁻¹ := by
  have h : (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / n : ℂ) =
      ((2 * Real.pi * (j : ℕ) * (k : ℕ) / n : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourierMatrix, Matrix.of_apply, norm_div, h, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), one_div]

/-- The Fourier matrix is symmetric. -/
theorem transpose_fourierMatrix (n : ℕ) : (fourierMatrix n)ᵀ = fourierMatrix n := by
  ext j k
  rw [Matrix.transpose_apply, fourierMatrix, Matrix.of_apply, Matrix.of_apply, mul_right_comm]

/-- The entries of the Fourier matrix are powers of a primitive root of unity. -/
private theorem fourierMatrix_apply (j k : Fin n) :
    fourierMatrix n j k =
      Complex.exp (2 * Real.pi * Complex.I / n) ^ ((j : ℕ) * (k : ℕ)) / (√(n : ℝ) : ℂ) := by
  rw [fourierMatrix, Matrix.of_apply, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The conjugates of the entries of the Fourier matrix. -/
private theorem star_fourierMatrix_apply (j k : Fin n) :
    star (fourierMatrix n j k) =
      (Complex.exp (2 * Real.pi * Complex.I / n) ^ ((j : ℕ) * (k : ℕ)))⁻¹ / (√(n : ℝ) : ℂ) := by
  have hn : n ≠ 0 := (Fin.pos j).ne'
  have hnorm : ‖Complex.exp (2 * Real.pi * Complex.I / n) ^ ((j : ℕ) * (k : ℕ))‖ = 1 := by
    rw [norm_pow, (Complex.isPrimitiveRoot_exp n hn).norm'_eq_one hn, one_pow]
  rw [fourierMatrix_apply, star_div₀, Complex.star_def, Complex.conj_ofReal]
  congr 1
  refine eq_inv_of_mul_eq_one_left ?_
  rw [Complex.conj_mul', hnorm, Complex.ofReal_one, one_pow]

/-- The sum of the powers of a ratio of two `n`-th roots of unity vanishes unless they agree. -/
private theorem sum_inv_mul_pow (k l : Fin n) :
    ∑ j : Fin n, ((Complex.exp (2 * Real.pi * Complex.I / n) ^ (k : ℕ))⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I / n) ^ (l : ℕ)) ^ (j : ℕ) =
        if k = l then (n : ℂ) else 0 := by
  have hn : n ≠ 0 := (Fin.pos k).ne'
  have hω := Complex.isPrimitiveRoot_exp n hn
  rw [Fin.sum_univ_eq_sum_range fun j =>
    ((Complex.exp (2 * Real.pi * Complex.I / n) ^ (k : ℕ))⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I / n) ^ (l : ℕ)) ^ j]
  split_ifs with hkl
  · rw [hkl, inv_mul_cancel₀ (pow_ne_zero _ (hω.ne_zero hn))]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hne : (Complex.exp (2 * Real.pi * Complex.I / n) ^ (k : ℕ))⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I / n) ^ (l : ℕ) - 1 ≠ 0 := by
      rw [sub_ne_zero, Ne, inv_mul_eq_one₀ (pow_ne_zero _ (hω.ne_zero hn))]
      exact fun h => hkl (Fin.ext (hω.pow_inj k.isLt l.isLt h))
    refine (mul_eq_zero.mp ?_).resolve_right hne
    rw [geom_sum_mul, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (k : ℕ), mul_comm (l : ℕ),
      pow_mul, pow_mul, hω.pow_eq_one, one_pow, one_pow, inv_one, one_mul, sub_self]

/-- **The Fourier matrix is unitary.** -/
theorem hasOrthonormalCols_fourierMatrix (n : ℕ) : HasOrthonormalCols (fourierMatrix n) := by
  rw [hasOrthonormalCols_iff]
  ext k l
  have hn : (√(n : ℝ) : ℂ) * (√(n : ℝ) : ℂ) = n := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt n.cast_nonneg, Complex.ofReal_natCast]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos k).ne'
  have hterm : ∀ j : Fin n, star (fourierMatrix n j k) * fourierMatrix n j l =
      ((Complex.exp (2 * Real.pi * Complex.I / n) ^ (k : ℕ))⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I / n) ^ (l : ℕ)) ^ (j : ℕ) / n := by
    intro j
    rw [star_fourierMatrix_apply, fourierMatrix_apply, div_mul_div_comm, hn, mul_pow, inv_pow,
      ← pow_mul, ← pow_mul, mul_comm (k : ℕ), mul_comm (l : ℕ)]
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hterm]
  rw [← Finset.sum_div, sum_inv_mul_pow, Matrix.one_apply]
  split_ifs
  · exact div_self hn0
  · exact zero_div _

/-- The scaled unitary transform as a sum of powers of roots of unity. -/
private theorem sqrt_mul_conjTranspose_fourierMatrix_mulVec_apply_eq_sum (v : Fin n → ℂ)
    (k : Fin n) : (√(n : ℝ) : ℂ) * ((fourierMatrix n)ᴴ *ᵥ v) k =
      ∑ l : Fin n, v l * (Complex.exp (2 * Real.pi * Complex.I / n) ^ (k : ℕ))⁻¹ ^ (l : ℕ) := by
  have hn0 : (√(n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Fin.pos k)))
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, star_fourierMatrix_apply, inv_pow, ← pow_mul,
    mul_comm (k : ℕ), ← mul_assoc, mul_div_cancel₀ _ hn0, mul_comm]

/-- The unitary discrete Fourier transform of a vector, scaled by `√n`, is the discrete Fourier
transform: `√n (Fᴴ v)_k = ∑ l, v l * exp (-2π i k l / n)`. -/
theorem sqrt_mul_conjTranspose_fourierMatrix_mulVec_apply (v : Fin n → ℂ) (k : Fin n) :
    (√(n : ℝ) : ℂ) * ((fourierMatrix n)ᴴ *ᵥ v) k =
      ∑ l : Fin n, v l * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℕ) * (l : ℕ) / n)) := by
  rw [sqrt_mul_conjTranspose_fourierMatrix_mulVec_apply_eq_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inv_pow, ← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  congr 2
  push_cast
  ring

/-- **Fourier diagonalisation of a circulant matrix.** `circulant v = F diag(v̂) Fᴴ` with `F` the
Fourier matrix and `v̂ = √n Fᴴ v` the discrete Fourier transform of `v`.
[HornJohnson2013, §2.2.P10]; [GolubVanLoan2013, §4.8.2].
Result: circulant-diagonalization -/
theorem circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose (v : Fin n → ℂ) :
    Matrix.circulant v =
      fourierMatrix n * Matrix.diagonal ((√(n : ℝ) : ℂ) • ((fourierMatrix n)ᴴ *ᵥ v)) *
        (fourierMatrix n)ᴴ := by
  have hCF : Matrix.circulant v * fourierMatrix n =
      fourierMatrix n * Matrix.diagonal ((√(n : ℝ) : ℂ) • ((fourierMatrix n)ᴴ *ᵥ v)) := by
    ext i k
    have hn : n ≠ 0 := (Fin.pos k).ne'
    have hζ : (Complex.exp (2 * Real.pi * Complex.I / n) ^ (k : ℕ)) ^ n = 1 := by
      rw [pow_right_comm, (Complex.isPrimitiveRoot_exp n hn).pow_eq_one, one_pow]
    have hcol : (fun j => fourierMatrix n j k) = (√(n : ℝ) : ℂ)⁻¹ • fun j : Fin n =>
        (Complex.exp (2 * Real.pi * Complex.I / n) ^ (k : ℕ)) ^ (j : ℕ) := by
      funext j
      rw [fourierMatrix_apply, mul_comm (j : ℕ), pow_mul, Pi.smul_apply, smul_eq_mul,
        div_eq_inv_mul]
    have hmul : (Matrix.circulant v * fourierMatrix n) i k =
        (Matrix.circulant v *ᵥ fun j => fourierMatrix n j k) i := rfl
    rw [hmul, hcol, Matrix.mulVec_smul, circulant_mulVec_pow v hζ, Matrix.mul_diagonal,
      Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      sqrt_mul_conjTranspose_fourierMatrix_mulVec_apply_eq_sum, fourierMatrix_apply,
      mul_comm (i : ℕ), pow_mul]
    ring
  rw [← hCF, Matrix.mul_assoc, (hasOrthonormalCols_fourierMatrix n).mul_conjTranspose_self,
    Matrix.mul_one]

/-- A circulant matrix is normal. -/
theorem isStarNormal_circulant (v : Fin n → ℂ) : IsStarNormal (Matrix.circulant v) := by
  refine ⟨?_⟩
  rw [Matrix.star_eq_conjTranspose, Matrix.Fin.conjTranspose_circulant]
  exact Matrix.Fin.circulant_mul_comm _ _

/-- **The spectral norm of a circulant matrix** is the largest modulus of a Fourier coefficient
of its first column. -/
theorem specNorm_circulant_le_iff (v : Fin n → ℂ) {c : ℝ} (hc : 0 ≤ c) :
    specNorm (Matrix.circulant v) ≤ c ↔
      ∀ k : Fin n, √(n : ℝ) * ‖((fourierMatrix n)ᴴ *ᵥ v) k‖ ≤ c := by
  rw [circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose,
    (hasOrthonormalCols_fourierMatrix n).specNorm_mul_conjTranspose_right,
    (hasOrthonormalCols_fourierMatrix n).specNorm_mul_left, specNorm_diagonal,
    pi_norm_le_iff_of_nonneg hc]
  simp only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The determinant of a circulant matrix is the product of the Fourier coefficients of its
first column. -/
theorem det_circulant (v : Fin n → ℂ) :
    (Matrix.circulant v).det = ∏ k : Fin n, (√(n : ℝ) : ℂ) * ((fourierMatrix n)ᴴ *ᵥ v) k := by
  rw [circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul,
    (hasOrthonormalCols_fourierMatrix n).mul_conjTranspose_self, Matrix.det_one, one_mul]
  rfl

end NLAlib
