/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR

/-!
# Householder reflectors and Householder QR

The Householder reflector of a vector `v` is `1 - (2 / ‖v‖²) v vᴴ`: Hermitian, unitary, an
involution, with `v ↦ -v` and the orthogonal complement of `v` fixed. For every vector `x` and
coordinate `i₀` there is a reflector sending `x` to a multiple of the coordinate vector `e_{i₀}`;
`NLAlib.householderVector` is the numerically stable choice of `v`.

Householder QR applies such reflectors to clear the columns of a matrix below the diagonal. It is
defined for matrices indexed by `Fin m` and `Fin n` and never breaks down.

## Main definitions

* `NLAlib.householder`: the reflector of a vector (the identity for the zero vector).
* `NLAlib.householderVector`: the vector whose reflector sends `x` to a multiple of `e_{i₀}`.
* `NLAlib.householderQ`, `NLAlib.householderR`: the factors computed by Householder QR.

## Main results

* `NLAlib.isHermitian_householder`, `NLAlib.householder_mul_self`,
  `NLAlib.hasOrthonormalCols_householder`, `NLAlib.det_householder`.
* `NLAlib.householder_mulVec_householderVector`: the reflector clears a vector.
* `NLAlib.householderQ_mul_householderR`, `NLAlib.hasOrthonormalCols_householderQ`,
  `NLAlib.isUpperTrapezoidal_householderR`: Householder QR computes the full factorization.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

/-! ### Reflectors -/

/-- The **Householder reflector** of `v`: `1 - (2 / ‖v‖²) v vᴴ`. For `v = 0` it is the identity.
[GolubVanLoan2013, §5.1.2]; [TrefethenBau1997, Lecture 10].
Port of `NLAlib.householder`, there over `ℝ`. -/
noncomputable def householder (v : m → 𝕜) : Matrix m m 𝕜 :=
  1 - ((2 / ‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) • Matrix.vecMulVec v (star v)

/-- The reflector of the zero vector is the identity. Port of `NLAlib.householder_zero`. -/
@[simp]
theorem householder_zero : householder (0 : m → 𝕜) = 1 := by
  sorry

/-- The action of a reflector: `H x = x - (2 vᴴx / ‖v‖²) v`.
Port of `NLAlib.householder_mulVec`. -/
theorem householder_mulVec (v x : m → 𝕜) :
    householder v *ᵥ x = x - ((2 / ‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) • (star v ⬝ᵥ x) • v := by
  sorry

/-- A reflector is Hermitian. Port of `NLAlib.householder_transpose`. -/
theorem isHermitian_householder (v : m → 𝕜) : (householder v).IsHermitian := by
  sorry

/-- A reflector is an involution. Port of `NLAlib.householder_mul_self`. -/
@[simp]
theorem householder_mul_self (v : m → 𝕜) : householder v * householder v = 1 := by
  sorry

/-- A reflector is unitary. Port of `NLAlib.hasOrthonormalCols_householder`. -/
theorem hasOrthonormalCols_householder (v : m → 𝕜) : HasOrthonormalCols (householder v) := by
  sorry

/-- A reflector negates its vector. Port of `NLAlib.householder_mulVec_self`. -/
theorem householder_mulVec_self (v : m → 𝕜) : householder v *ᵥ v = -v := by
  sorry

/-- A reflector fixes the vectors orthogonal to its vector.
Port of `NLAlib.householder_mulVec_of_dotProduct_eq_zero`. -/
theorem householder_mulVec_of_dotProduct_eq_zero {v w : m → 𝕜} (h : star v ⬝ᵥ w = 0) :
    householder v *ᵥ w = w := by
  sorry

/-- The reflector depends only on the direction of its vector. -/
theorem householder_smul {c : 𝕜} (hc : c ≠ 0) (v : m → 𝕜) :
    householder (c • v) = householder v := by
  sorry

/-- The determinant of a reflector of a nonzero vector is `-1`. -/
theorem det_householder {v : m → 𝕜} (hv : v ≠ 0) : (householder v).det = -1 := by
  sorry

/-! ### Clearing a vector -/

/-- The **Householder vector** of `x` at the coordinate `i₀`: `x + phase(x i₀) ‖x‖ e_{i₀}`, with
`phase z = z / ‖z‖` and `phase 0 = 1`. The sign avoids cancellation.
[GolubVanLoan2013, §5.1.3]. Port of `NLAlib.householderVector`, there over `ℝ`. -/
noncomputable def householderVector (x : m → 𝕜) (i₀ : m) : m → 𝕜 :=
  x + ((if x i₀ = 0 then 1 else x i₀ / (‖x i₀‖ : 𝕜)) * (‖WithLp.toLp 2 x‖ : 𝕜)) • Pi.single i₀ 1

/-- **The Householder reflector clears a vector**: `H x = x - v`, a multiple of `e_{i₀}`.
Port of `NLAlib.householder_mulVec_householderVector`. -/
theorem householder_mulVec_householderVector (x : m → 𝕜) (i₀ : m) :
    householder (householderVector x i₀) *ᵥ x = x - householderVector x i₀ := by
  sorry

/-- The cleared vector vanishes away from the chosen coordinate. -/
theorem householder_mulVec_householderVector_apply_of_ne (x : m → 𝕜) {i₀ i : m} (hi : i ≠ i₀) :
    (householder (householderVector x i₀) *ᵥ x) i = 0 := by
  sorry

/-- The cleared vector has the norm of `x` in the chosen coordinate. -/
theorem norm_householder_mulVec_householderVector_apply (x : m → 𝕜) (i₀ : m) :
    ‖(householder (householderVector x i₀) *ᵥ x) i₀‖ = ‖WithLp.toLp 2 x‖ := by
  sorry

/-! ### Householder QR -/

section QR

variable {m n : ℕ}

/-- The reflector of step `k` of Householder QR: it clears column `k` of `W` below the diagonal
and fixes the first `k` coordinates. Beyond the size of the matrix it is the identity. -/
noncomputable def householderStep (W : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  if h : k < m ∧ k < n then
    householder (householderVector (fun i => if k ≤ (i : ℕ) then W i ⟨k, h.2⟩ else 0) ⟨k, h.1⟩)
  else 1

/-- The state of Householder QR after `k` steps: the accumulated unitary factor and the partially
triangularised matrix. -/
noncomputable def householderState (A : Matrix (Fin m) (Fin n) 𝕜) :
    ℕ → Matrix (Fin m) (Fin m) 𝕜 × Matrix (Fin m) (Fin n) 𝕜
  | 0 => (1, A)
  | k + 1 =>
      ((householderState A k).1 * householderStep (householderState A k).2 k,
        householderStep (householderState A k).2 k * (householderState A k).2)

/-- The unitary factor of Householder QR. Port of `NLAlib.householderQ`, there over `ℝ`. -/
noncomputable def householderQ (A : Matrix (Fin m) (Fin n) 𝕜) : Matrix (Fin m) (Fin m) 𝕜 :=
  (householderState A n).1

/-- The upper trapezoidal factor of Householder QR. Port of `NLAlib.householderR`. -/
noncomputable def householderR (A : Matrix (Fin m) (Fin n) 𝕜) : Matrix (Fin m) (Fin n) 𝕜 :=
  (householderState A n).2

/-- The unitary factor of Householder QR is unitary.
Port of `NLAlib.hasOrthonormalCols_householderQ`. -/
theorem hasOrthonormalCols_householderQ (A : Matrix (Fin m) (Fin n) 𝕜) :
    HasOrthonormalCols (householderQ A) := by
  sorry

/-- Householder QR factors the matrix. Port of `NLAlib.householderQ_mul_householderR`. -/
theorem householderQ_mul_householderR (A : Matrix (Fin m) (Fin n) 𝕜) :
    householderQ A * householderR A = A := by
  sorry

/-- **The second factor of Householder QR is upper trapezoidal.**
[TrefethenBau1997, Lecture 10]. Port of `NLAlib.isUpperTrapezoidal_householderR`. -/
theorem isUpperTrapezoidal_householderR (A : Matrix (Fin m) (Fin n) 𝕜) :
    IsUpperTrapezoidal (householderR A) := by
  sorry

/-- Householder QR gives the thin QR factorization of a tall matrix.
Port of `NLAlib.isQR_householderQR`. -/
theorem isQR_householder (A : Matrix (Fin m) (Fin n) 𝕜) (h : n ≤ m) :
    IsQR A ((householderQ A).submatrix id (Fin.castLE h))
      ((householderR A).submatrix (Fin.castLE h) id) := by
  sorry

end QR

end NLAlib
