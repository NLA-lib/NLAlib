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

* `NLAlib.walshHadamard_apply`, `NLAlib.transpose_walshHadamard`,
  `NLAlib.conjTranspose_walshHadamard`: entries and symmetry.
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

/-- The sign `(-1) ^ s` of a bit `s`, written with `if`, is multiplicative. -/
private theorem ite_add_eq_zero (s t : ZMod 2) :
    (if s + t = 0 then (1 : R) else -1) =
      (if s = 0 then 1 else -1) * (if t = 0 then 1 else -1) := by
  have h : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases h s with rfl | rfl <;> rcases h t with rfl | rfl <;>
    simp [show (1 : ZMod 2) + 1 = 0 from by decide]

/-- Entries of the Walsh–Hadamard matrix, unfolded. -/
theorem walshHadamard_apply (x y : Fin b → ZMod 2) :
    walshHadamard R b x y = if ∑ i, x i * y i = 0 then 1 else -1 :=
  rfl

/-- The entries are symmetric in the two bit strings. -/
private theorem walshHadamard_comm (x y : Fin b → ZMod 2) :
    walshHadamard R b x y = walshHadamard R b y x := by
  simp only [walshHadamard_apply, mul_comm]

/-- Entries of the Walsh–Hadamard matrix square to one. Port of `NLAlib.walshCharacter_sq`. -/
theorem walshHadamard_apply_mul_self (x y : Fin b → ZMod 2) :
    walshHadamard R b x y * walshHadamard R b x y = 1 := by
  rw [walshHadamard_apply]
  split_ifs
  · rw [mul_one]
  · rw [neg_mul_neg, mul_one]

/-- The Walsh–Hadamard matrix is symmetric. Port of `NLAlib.walshMatrix_transpose`. -/
theorem transpose_walshHadamard (b : ℕ) : (walshHadamard R b)ᵀ = walshHadamard R b := by
  ext x y
  rw [Matrix.transpose_apply, walshHadamard_comm]

/-- The entries are characters: `H (x + z) y = H x y * H z y`.
Port of `NLAlib.walshCharacter_add_left`. -/
theorem walshHadamard_add_apply (x z y : Fin b → ZMod 2) :
    walshHadamard R b (x + z) y = walshHadamard R b x y * walshHadamard R b z y := by
  simp only [walshHadamard_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  exact ite_add_eq_zero _ _

/-- **Character sums**: a row of the Walsh–Hadamard matrix sums to `2 ^ b` for the zero string
and to `0` otherwise. Port of `NLAlib.sum_walshCharacter`. -/
theorem sum_walshHadamard_apply (x : Fin b → ZMod 2) :
    ∑ y, walshHadamard R b x y = if x = 0 then (2 : R) ^ b else 0 := by
  split_ifs with hx
  · subst hx
    simp [walshHadamard_apply, ZMod.card]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hi1 : x i = 1 := (by decide : ∀ s : ZMod 2, s ≠ 0 → s = 1) _ hi
    have hflip : walshHadamard R b (Pi.single i 1) x = -1 := by
      rw [walshHadamard_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp [hi1]
    refine Finset.sum_ninvolution (fun y => y + Pi.single i 1) (fun y => ?_) (fun y _ h => ?_)
      (fun _ => Finset.mem_univ _) (fun y => ?_)
    · rw [walshHadamard_comm x (y + Pi.single i 1), walshHadamard_add_apply,
        walshHadamard_comm y x, hflip, mul_neg, mul_one, add_neg_cancel]
    · have h' := congrFun (add_eq_left.mp h) i
      simp at h'
    · ext j
      simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **`H * H = 2 ^ b • 1`.** Port of `NLAlib.walshMatrix_mul_self`. -/
theorem walshHadamard_mul_self (b : ℕ) :
    walshHadamard R b * walshHadamard R b = (2 : R) ^ b • (1 : Matrix _ _ R) := by
  ext x z
  have hxz : x + z = 0 ↔ x = z := by
    rw [funext_iff, funext_iff]
    exact forall_congr' fun i => CharTwo.add_eq_zero
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ← if_congr hxz rfl rfl, ← sum_walshHadamard_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [walshHadamard_add_apply, walshHadamard_comm z y]

/-- The Walsh–Hadamard matrix is its own conjugate transpose. -/
theorem conjTranspose_walshHadamard [StarRing R] (b : ℕ) :
    (walshHadamard R b)ᴴ = walshHadamard R b := by
  ext x y
  rw [Matrix.conjTranspose_apply, walshHadamard_comm, walshHadamard_apply]
  split_ifs
  · rw [star_one]
  · rw [star_neg, star_one]

/-- The Walsh–Hadamard matrix is a Hadamard matrix. -/
theorem isHadamard_walshHadamard [StarRing R] (b : ℕ) : (walshHadamard R b).IsHadamard := by
  have hH := conjTranspose_walshHadamard (R := R) b
  have hcard : (Fintype.card (Fin b → ZMod 2) : R) = 2 ^ b := by
    simp [ZMod.card]
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · have hstar : star (walshHadamard R b x y) = walshHadamard R b x y := by
      rw [← Matrix.conjTranspose_apply, hH, walshHadamard_comm]
    rw [Unitary.mem_iff, hstar]
    exact ⟨walshHadamard_apply_mul_self x y, walshHadamard_apply_mul_self x y⟩
  · rw [hH, hcard, walshHadamard_mul_self]
  · rw [hH, hcard, walshHadamard_mul_self]

/-- **The normalised Walsh–Hadamard matrix is orthogonal.**
Port of `NLAlib.walshMatrix_transpose_mul_self`. -/
theorem hasOrthonormalCols_smul_walshHadamard {𝕜 : Type*} [RCLike 𝕜] (b : ℕ) :
    HasOrthonormalCols (((√((2 : ℝ) ^ b))⁻¹ : ℝ) • walshHadamard 𝕜 b) := by
  have hc : ((√((2 : ℝ) ^ b))⁻¹ * (√((2 : ℝ) ^ b))⁻¹) * (2 : ℝ) ^ b = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  rw [HasOrthonormalCols, Matrix.conjTranspose_smul, star_trivial, conjTranspose_walshHadamard,
    Matrix.smul_mul, Matrix.mul_smul, walshHadamard_mul_self, smul_smul,
    show ((2 : 𝕜) ^ b) = (((2 : ℝ) ^ b : ℝ) : 𝕜) by push_cast; rfl,
    ← RCLike.real_smul_eq_coe_smul, smul_smul, hc, one_smul]

/-- The entries of the normalised Walsh–Hadamard matrix all have modulus `2 ^ (-b / 2)`.
Port of `NLAlib.walshMatrix_apply_sq`. -/
theorem norm_smul_walshHadamard_apply {𝕜 : Type*} [RCLike 𝕜] (x y : Fin b → ZMod 2) :
    ‖(((√((2 : ℝ) ^ b))⁻¹ : ℝ) • walshHadamard 𝕜 b) x y‖ ^ 2 = ((2 : ℝ) ^ b)⁻¹ := by
  have h1 : ‖walshHadamard 𝕜 b x y‖ = 1 := by
    rw [walshHadamard_apply]
    split_ifs
    · rw [norm_one]
    · rw [norm_neg, norm_one]
  rw [Matrix.smul_apply, norm_smul, h1, mul_one, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (by positivity)]

end NLAlib
