/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Data.ZMod.Basic
public import NLAlib.Matrix.Basic.Orthonormal

/-!
# Walsh–Hadamard matrices

The Walsh–Hadamard matrix of order `2 ^ b` is indexed by bit strings `Fin b → ZMod 2`, with entry
`(-1) ^ ⟨x, y⟩` at `(x, y)`. It is symmetric with entries `±1` and `H * H = 2 ^ b • 1`, so it is
a Hadamard matrix in the sense of Mathlib's `Matrix.IsHadamard`, and `2 ^ (-b / 2) • H` is a
symmetric orthogonal matrix all of whose entries have the same modulus. This flatness is what
subsampled randomized Hadamard transforms use.

## Main definitions

* `NLAlib.walshHadamard`: the Walsh–Hadamard matrix over a ring.

## Main results

* `NLAlib.walshHadamard_mul_self`: `H * H = 2 ^ b • 1`.
* `NLAlib.isHadamard_walshHadamard`.
* `NLAlib.hasOrthonormalCols_smul_walshHadamard`: the normalised matrix is orthogonal.
* `NLAlib.sum_walshHadamard_apply`: character sums.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {R : Type*} [Ring R] {b : ℕ}

/-- The **Walsh–Hadamard matrix** of order `2 ^ b`, indexed by bit strings: the entry at `(x, y)`
is `1` if `x` and `y` share an even number of ones and `-1` otherwise.
Port of `NLAlib.walshMatrix`, there normalised and over `ℝ`. -/
def walshHadamard (R : Type*) [Ring R] (b : ℕ) :
    Matrix (Fin b → ZMod 2) (Fin b → ZMod 2) R :=
  Matrix.of fun x y => if ∑ i, x i * y i = 0 then 1 else -1

/-- Entries of the Walsh–Hadamard matrix square to one. Port of `NLAlib.walshCharacter_sq`. -/
theorem walshHadamard_apply_mul_self (x y : Fin b → ZMod 2) :
    walshHadamard R b x y * walshHadamard R b x y = 1 := by
  sorry

/-- The Walsh–Hadamard matrix is symmetric. Port of `NLAlib.walshMatrix_transpose`. -/
theorem transpose_walshHadamard (b : ℕ) : (walshHadamard R b)ᵀ = walshHadamard R b := by
  sorry

/-- The entries are characters: `H (x + z) y = H x y * H z y`.
Port of `NLAlib.walshCharacter_add_left`. -/
theorem walshHadamard_add_apply (x z y : Fin b → ZMod 2) :
    walshHadamard R b (x + z) y = walshHadamard R b x y * walshHadamard R b z y := by
  sorry

/-- **Character sums**: a row of the Walsh–Hadamard matrix sums to `2 ^ b` for the zero string
and to `0` otherwise. Port of `NLAlib.sum_walshCharacter`. -/
theorem sum_walshHadamard_apply (x : Fin b → ZMod 2) :
    ∑ y, walshHadamard R b x y = if x = 0 then (2 : R) ^ b else 0 := by
  sorry

/-- **`H * H = 2 ^ b • 1`.** Port of `NLAlib.walshMatrix_mul_self`. -/
theorem walshHadamard_mul_self (b : ℕ) :
    walshHadamard R b * walshHadamard R b = (2 : R) ^ b • (1 : Matrix _ _ R) := by
  sorry

/-- The Walsh–Hadamard matrix is a Hadamard matrix. -/
theorem isHadamard_walshHadamard [StarRing R] (b : ℕ) : (walshHadamard R b).IsHadamard := by
  sorry

/-- **The normalised Walsh–Hadamard matrix is orthogonal.**
Port of `NLAlib.walshMatrix_transpose_mul_self`. -/
theorem hasOrthonormalCols_smul_walshHadamard {𝕜 : Type*} [RCLike 𝕜] (b : ℕ) :
    HasOrthonormalCols (((√((2 : ℝ) ^ b))⁻¹ : ℝ) • walshHadamard 𝕜 b) := by
  sorry

/-- The entries of the normalised Walsh–Hadamard matrix all have modulus `2 ^ (-b / 2)`.
Port of `NLAlib.walshMatrix_apply_sq`. -/
theorem norm_smul_walshHadamard_apply {𝕜 : Type*} [RCLike 𝕜] (x y : Fin b → ZMod 2) :
    ‖(((√((2 : ℝ) ^ b))⁻¹ : ℝ) • walshHadamard 𝕜 b) x y‖ ^ 2 = ((2 : ℝ) ^ b)⁻¹ := by
  sorry

end NLAlib
