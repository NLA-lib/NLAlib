/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Matrix.Basic.Orthonormal

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
  sorry

/-- **A matrix commutes with the cyclic shift exactly when it is circulant.**
Port of `NLAlib.commute_cyclicShift_iff_exists_circulant`, there over `ℝ`. -/
theorem mul_circulant_single_comm_iff {R : Type*} [Semiring R] [NeZero n]
    (A : Matrix (Fin n) (Fin n) R) :
    A * Matrix.circulant (Pi.single 1 1) = Matrix.circulant (Pi.single 1 1) * A ↔
      ∃ v, A = Matrix.circulant v := by
  sorry

/-- A matrix that commutes with the cyclic shift is the circulant matrix of its first column.
Port of `NLAlib.eq_circulant_of_commute_cyclicShift`. -/
theorem eq_circulant_of_mul_circulant_single_comm {R : Type*} [Semiring R] [NeZero n]
    {A : Matrix (Fin n) (Fin n) R}
    (h : A * Matrix.circulant (Pi.single 1 1) = Matrix.circulant (Pi.single 1 1) * A) :
    A = Matrix.circulant fun i => A i 0 := by
  sorry

/-! ### The Fourier matrix -/

/-- The **Fourier matrix**: the unitary matrix of the discrete Fourier transform on `Fin n`, with
entries `exp (2π i j k / n) / √n`. -/
noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / n) / (√(n : ℝ) : ℂ)

/-- Entries of the Fourier matrix have modulus `1 / √n`. -/
theorem norm_fourierMatrix_apply (j k : Fin n) : ‖fourierMatrix n j k‖ = (√(n : ℝ))⁻¹ := by
  sorry

/-- The Fourier matrix is symmetric. -/
theorem transpose_fourierMatrix (n : ℕ) : (fourierMatrix n)ᵀ = fourierMatrix n := by
  sorry

/-- **The Fourier matrix is unitary.** -/
theorem hasOrthonormalCols_fourierMatrix (n : ℕ) : HasOrthonormalCols (fourierMatrix n) := by
  sorry

/-- **Fourier diagonalisation of a circulant matrix.** `circulant v = F diag(v̂) Fᴴ` with `F` the
Fourier matrix and `v̂ k = ∑ l, v l * exp (-2π i k l / n)` the discrete Fourier transform.
[HornJohnson2013, §2.2.P10]; [GolubVanLoan2013, §4.8.2]. -/
theorem circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose (v : Fin n → ℂ) :
    Matrix.circulant v =
      fourierMatrix n *
        Matrix.diagonal (fun k : Fin n =>
          ∑ l : Fin n, v l * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℕ) * (l : ℕ) / n))) *
        (fourierMatrix n)ᴴ := by
  sorry

/-- A circulant matrix is normal. -/
theorem isStarNormal_circulant (v : Fin n → ℂ) : IsStarNormal (Matrix.circulant v) := by
  sorry

/-- **The spectral norm of a circulant matrix** is the largest modulus of a Fourier coefficient
of its first column. -/
theorem specNorm_circulant_le_iff (v : Fin n → ℂ) {c : ℝ} (hc : 0 ≤ c) :
    specNorm (Matrix.circulant v) ≤ c ↔
      ∀ k : Fin n,
        ‖∑ l : Fin n, v l * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℕ) * (l : ℕ) / n))‖ ≤
          c := by
  sorry

/-- The determinant of a circulant matrix is the product of the Fourier coefficients of its
first column. -/
theorem det_circulant (v : Fin n → ℂ) :
    (Matrix.circulant v).det =
      ∏ k : Fin n,
        ∑ l : Fin n, v l * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℕ) * (l : ℕ) / n)) := by
  sorry

end NLAlib
