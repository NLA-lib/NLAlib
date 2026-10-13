/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import NLAlib.Matrix.Spectral.Simultaneous

/-!
# Diagonalisable matrices, eigenvector pairings and the Sylvester equation

A square matrix over a field is diagonalisable when it has a basis of eigenvectors,
`NLAlib.IsDiagonalizable A`. This file gives the equivalent forms, the standard sufficient
conditions, simultaneous diagonalisation of commuting families, the biorthogonality of left and
right eigenvectors with its characterisation of simple eigenvalues, and the solvability of the
Sylvester equation `A X - X B = C` when `A` and `B` have no common eigenvalue.

## Main definitions

* `NLAlib.IsDiagonalizable`: `A * V = V * diagonal d` for an invertible `V`.

## Main results

* `NLAlib.isDiagonalizable_iff_exists_eq_mul_diagonal_mul_inv`.
* `NLAlib.isDiagonalizable_of_injective_of_forall_mem_spectrum`: distinct eigenvalues.
* `NLAlib.isDiagonalizable_iff_isSemisimple`.
* `NLAlib.exists_forall_mul_eq_mul_diagonal_of_pairwise_commute`: commuting families.
* `NLAlib.dotProduct_eq_zero_of_vecMul_eq_smul_of_mulVec_eq_smul`: biorthogonality.
* `NLAlib.existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly`: the Sylvester equation.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {K : Type*} [Field K] {ι m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Diagonalisability -/

/-- A square matrix is **diagonalisable** if `A * V = V * diagonal d` for an invertible `V`: the
columns of `V` are a basis of eigenvectors. [HornJohnson2013, Definition 1.3.6].
Port of `NLAlib.IsDiagonalizable`. -/
def IsDiagonalizable (A : Matrix n n K) : Prop :=
  ∃ (V : Matrix n n K) (d : n → K), IsUnit V.det ∧ A * V = V * Matrix.diagonal d

/-- Diagonalisability as a similarity `A = V D V⁻¹`.
Port of `NLAlib.isDiagonalizable_iff_exists_similarity`. -/
theorem isDiagonalizable_iff_exists_eq_mul_diagonal_mul_inv {A : Matrix n n K} :
    IsDiagonalizable A ↔
      ∃ (V : Matrix n n K) (d : n → K), IsUnit V.det ∧ A = V * Matrix.diagonal d * V⁻¹ := by
  sorry

/-- Diagonalisability as a linearly independent family of eigenvectors.
Port of `NLAlib.isDiagonalizable_iff_exists_independent_eigenvectors`. -/
theorem isDiagonalizable_iff_exists_linearIndependent {A : Matrix n n K} :
    IsDiagonalizable A ↔
      ∃ (v : n → n → K) (d : n → K), LinearIndependent K v ∧ ∀ j, A *ᵥ v j = d j • v j := by
  sorry

/-- The diagonal of a diagonalisation lists the eigenvalues. -/
theorem charpoly_eq_prod_of_mul_eq_mul_diagonal {A V : Matrix n n K} {d : n → K}
    (hV : IsUnit V.det) (h : A * V = V * Matrix.diagonal d) :
    A.charpoly = ∏ i, (X - C (d i)) := by
  sorry

/-- **A matrix with distinct eigenvalues is diagonalisable.**
[HornJohnson2013, Theorem 1.3.9]. Port of `NLAlib.isDiagonalizable_of_distinct_eigenvalues`. -/
theorem isDiagonalizable_of_injective_of_forall_mem_spectrum {A : Matrix n n K} {d : n → K}
    (hd : Function.Injective d) (h : ∀ j, d j ∈ spectrum K A) : IsDiagonalizable A := by
  sorry

/-- A matrix is diagonalisable exactly when its eigenspaces span.
Port of `NLAlib.isDiagonalizable_iff_iSup_eigenspace_eq_top`. -/
theorem isDiagonalizable_iff_iSup_eigenspace_eq_top {A : Matrix n n K} :
    IsDiagonalizable A ↔ ⨆ μ, Module.End.eigenspace (Matrix.toLin' A) μ = ⊤ := by
  sorry

/-- Over an algebraically closed field, diagonalisable means semisimple.
Port of `NLAlib.isDiagonalizable_iff_isSemisimple`. -/
theorem isDiagonalizable_iff_isSemisimple [IsAlgClosed K] {A : Matrix n n K} :
    IsDiagonalizable A ↔ Module.End.IsSemisimple (Matrix.toLin' A) := by
  sorry

/-- A block diagonal matrix is diagonalisable exactly when its blocks are.
Port of `NLAlib.isDiagonalizable_fromBlocks_zero_zero_iff`. -/
theorem isDiagonalizable_fromBlocks_diagonal_iff {A : Matrix m m K} {B : Matrix n n K} :
    IsDiagonalizable (Matrix.fromBlocks A 0 0 B) ↔ IsDiagonalizable A ∧ IsDiagonalizable B := by
  sorry

/-- A Hermitian matrix is diagonalisable. Port of `NLAlib.isDiagonalizable_of_isHermitian`. -/
theorem _root_.Matrix.IsHermitian.isDiagonalizable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : IsDiagonalizable A := by
  sorry

/-- A normal complex matrix is diagonalisable. -/
theorem _root_.IsStarNormal.isDiagonalizable {A : Matrix n n ℂ} (hA : IsStarNormal A) :
    IsDiagonalizable A := by
  sorry

/-- **A commuting family of diagonalisable matrices is simultaneously diagonalisable.**
[HornJohnson2013, Theorem 1.3.21].
Port of `NLAlib.exists_simultaneous_diagonalization_of_commute`. -/
theorem exists_forall_mul_eq_mul_diagonal_of_pairwise_commute {A : ι → Matrix n n K}
    (hA : ∀ i, IsDiagonalizable (A i)) (h : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ V : Matrix n n K, IsUnit V.det ∧ ∀ i, ∃ d : n → K, A i * V = V * Matrix.diagonal d := by
  sorry

/-- Simultaneously diagonalisable matrices commute.
Port of `NLAlib.commute_of_simultaneous_diagonalization`. -/
theorem commute_of_mul_eq_mul_diagonal {A B V : Matrix n n K} {a b : n → K} (hV : IsUnit V.det)
    (hA : A * V = V * Matrix.diagonal a) (hB : B * V = V * Matrix.diagonal b) : Commute A B := by
  sorry

/-! ### Left and right eigenvectors -/

/-- Every eigenvalue has a right eigenvector.
Port of `NLAlib.exists_mulVec_eq_smul_of_mem_spectrum`. -/
theorem exists_mulVec_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ x : n → K, x ≠ 0 ∧ A *ᵥ x = μ • x := by
  sorry

/-- Every eigenvalue has a left eigenvector.
Port of `NLAlib.exists_vecMul_eq_smul_of_mem_spectrum`. -/
theorem exists_vecMul_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ y : n → K, y ≠ 0 ∧ y ᵥ* A = μ • y := by
  sorry

/-- **Biorthogonality**: left and right eigenvectors for different eigenvalues are orthogonal.
[HornJohnson2013, Theorem 1.4.7].
Port of `NLAlib.dotProduct_eq_zero_of_left_right_eigenvalues_ne`. -/
theorem dotProduct_eq_zero_of_vecMul_eq_smul_of_mulVec_eq_smul {A : Matrix n n K} {x y : n → K}
    {α μ : K} (hx : A *ᵥ x = α • x) (hy : y ᵥ* A = μ • y) (h : α ≠ μ) : y ⬝ᵥ x = 0 := by
  sorry

/-- **A geometrically simple eigenvalue is algebraically simple exactly when its left and right
eigenvectors are not orthogonal.** [HornJohnson2013, Theorem 1.4.12].
Port of `NLAlib.rootMultiplicity_eq_one_iff_pairing_ne_zero_of_finrank_eigenspace_eq_one`. -/
theorem rootMultiplicity_charpoly_eq_one_iff_dotProduct_ne_zero [IsAlgClosed K]
    {A : Matrix n n K} {x y : n → K} {μ : K} (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x)
    (hyA : y ᵥ* A = μ • y)
    (h : Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) = 1) :
    A.charpoly.rootMultiplicity μ = 1 ↔ y ⬝ᵥ x ≠ 0 := by
  sorry

/-- **The adjugate at a geometrically simple eigenvalue** is a nonzero multiple of `x yᵀ`, with
`x` a right and `y` a left eigenvector. [HornJohnson2013, §1.4.11].
Port of `NLAlib.exists_adjugate_shift_eq_smul_vecMulVec_of_finrank_eigenspace_eq_one`. -/
theorem exists_adjugate_eq_smul_vecMulVec {M : Matrix n n K} {x y : n → K} (hx : x ≠ 0)
    (hy : y ≠ 0) (hMx : M *ᵥ x = 0) (hyM : y ᵥ* M = 0)
    (h : Module.finrank K (LinearMap.ker M.mulVecLin) = 1) :
    ∃ c : K, c ≠ 0 ∧ M.adjugate = c • Matrix.vecMulVec x y := by
  sorry

/-! ### The Sylvester equation -/

/-- If the characteristic polynomials of `A` and `B` are coprime, only `X = 0` intertwines them.
Port of `NLAlib.eq_zero_of_mul_eq_mul_of_isCoprime_charpoly`. -/
theorem eq_zero_of_mul_eq_mul_of_isCoprime_charpoly {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) {X : Matrix m n K} (hX : A * X = X * B) : X = 0 := by
  sorry

/-- **The Sylvester equation `A X - X B = C` has a unique solution** when the characteristic
polynomials of `A` and `B` are coprime. [HornJohnson2013, Theorem 2.4.4.1].
Port of `NLAlib.existsUnique_sylvester_of_isCoprime_charpoly`.
Result: sylvester-equation -/
theorem existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly (A : Matrix m m K) (B : Matrix n n K)
    (h : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C := by
  sorry

/-- Over an algebraically closed field the characteristic polynomials are coprime exactly when
the spectra are disjoint. Port of `NLAlib.isCoprime_charpoly_iff_disjoint_spectrum`. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum [IsAlgClosed K] (A : Matrix m m K)
    (B : Matrix n n K) :
    IsCoprime A.charpoly B.charpoly ↔ Disjoint (spectrum K A) (spectrum K B) := by
  sorry

/-- **A block upper triangular matrix whose diagonal blocks have coprime characteristic
polynomials is similar to its block diagonal part.** [HornJohnson2013, Theorem 2.4.6.1 context]. -/
theorem exists_fromBlocks_mul_eq_mul_fromBlocks (A : Matrix m m K) (B : Matrix n n K)
    (h : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃ X : Matrix m n K,
      Matrix.fromBlocks A C 0 B * Matrix.fromBlocks 1 X 0 1 =
        Matrix.fromBlocks 1 X 0 1 * Matrix.fromBlocks A 0 0 B := by
  sorry

end NLAlib
