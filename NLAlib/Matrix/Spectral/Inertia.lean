/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Matrix.Factorizations.GaussState

/-!
# Inertia of Hermitian matrices

The inertia of a Hermitian matrix is the triple of the numbers of its positive, negative and zero
eigenvalues. `NLAlib.inertiaPos A` and `NLAlib.inertiaNeg A` count the positive and negative
`eigenvalue A i`. Sylvester's law says congruence preserves them. Haynsworth's formula computes the
inertia of a block matrix from a Schur complement, Ostrowski's theorem quantifies how far congruence
moves each eigenvalue, and the signs of the pivots of elimination on `A - x • 1` count the
eigenvalues below `x`, which is what the bisection method uses.

## Main definitions

* `NLAlib.inertiaPos`, `NLAlib.inertiaNeg`.

## Main results

* `Matrix.IsHermitian.inertiaPos_conjTranspose_mul_mul`,
  `Matrix.IsHermitian.inertiaNeg_conjTranspose_mul_mul`: Sylvester's law of inertia.
* `Matrix.IsHermitian.inertiaPos_fromBlocks`, `Matrix.IsHermitian.inertiaNeg_fromBlocks`: Haynsworth
  additivity.
* `Matrix.IsHermitian.exists_eigenvalue_conjTranspose_mul_mul_eq_mul`: Ostrowski's theorem.
* `Matrix.IsHermitian.inertiaNeg_sub_smul_one_eq_card_gaussState_re_neg`: counting eigenvalues by
  pivots.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- The **positive index of inertia**: the number of positive eigenvalues.
[HornJohnson2013, Definition 4.5.6]. Port of `NLAlib.inertiaPos`, there over `ℝ` through the
signature of the quadratic form. For a matrix that is not Hermitian the value is `0`, since
`eigenvalue` is then zero. -/
noncomputable def inertiaPos (A : Matrix n n 𝕜) : ℕ :=
  ((Finset.range (Fintype.card n)).filter fun i => 0 < eigenvalue A i).card

/-- The **negative index of inertia**: the number of negative eigenvalues; `0` for a matrix that
is not Hermitian. Port of `NLAlib.inertiaNeg`. -/
noncomputable def inertiaNeg (A : Matrix n n 𝕜) : ℕ :=
  ((Finset.range (Fintype.card n)).filter fun i => eigenvalue A i < 0).card

/-- The positive and negative indices of a Hermitian matrix add up to its rank.
Port of `NLAlib.inertiaPos_add_inertiaNeg_eq_rank`. -/
theorem _root_.Matrix.IsHermitian.inertiaPos_add_inertiaNeg {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : inertiaPos A + inertiaNeg A = A.rank := by
  sorry

/-- The positive index of a real diagonal matrix. Port of `NLAlib.inertiaPos_diagonal`. -/
theorem inertiaPos_diagonal (d : n → ℝ) :
    inertiaPos (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      (Finset.univ.filter fun i => 0 < d i).card := by
  sorry

/-- The negative index of a real diagonal matrix. Port of `NLAlib.inertiaNeg_diagonal`. -/
theorem inertiaNeg_diagonal (d : n → ℝ) :
    inertiaNeg (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      (Finset.univ.filter fun i => d i < 0).card := by
  sorry

/-- The negative index of `A` is the positive index of `-A`. -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_eq_inertiaPos_neg
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    inertiaNeg A = inertiaPos (-A) := by
  sorry

/-- A Hermitian matrix is positive definite exactly when its positive index is its size. -/
theorem _root_.Matrix.IsHermitian.posDef_iff_inertiaPos_eq_card {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosDef ↔ inertiaPos A = Fintype.card n := by
  sorry

/-- A Hermitian matrix is positive semidefinite exactly when its negative index vanishes. -/
theorem _root_.Matrix.IsHermitian.posSemidef_iff_inertiaNeg_eq_zero {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosSemidef ↔ inertiaNeg A = 0 := by
  sorry

/-- **The positive index is the largest dimension of a subspace on which the form is positive
definite.** [HornJohnson2013, Theorem 4.5.8 context]. -/
theorem _root_.Matrix.IsHermitian.le_inertiaPos_iff_exists_posDef
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ} :
    k ≤ inertiaPos A ↔
      ∃ V : Matrix n (Fin k) 𝕜, HasOrthonormalCols V ∧ (Vᴴ * A * V).PosDef := by
  sorry

/-! ### Sylvester's law -/

/-- **Sylvester's law of inertia**, positive index: congruence by an invertible matrix preserves
the number of positive eigenvalues. [HornJohnson2013, Theorem 4.5.8].
Port of `NLAlib.inertiaPos_transpose_mul_mul`, there over `ℝ`.
Result: sylvester-inertia -/
theorem _root_.Matrix.IsHermitian.inertiaPos_conjTranspose_mul_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {S : Matrix n n 𝕜} (hS : IsUnit S.det) : inertiaPos (Sᴴ * A * S) = inertiaPos A := by
  sorry

/-- **Sylvester's law of inertia**, negative index.
Port of `NLAlib.inertiaNeg_transpose_mul_mul`, there over `ℝ`.
Result: sylvester-inertia -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_conjTranspose_mul_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {S : Matrix n n 𝕜} (hS : IsUnit S.det) : inertiaNeg (Sᴴ * A * S) = inertiaNeg A := by
  sorry

/-- A congruence by any matrix does not increase the positive index.
Port of `NLAlib.card_eigenvalues₀_pos_congruence_le`. -/
theorem _root_.Matrix.IsHermitian.inertiaPos_conjTranspose_mul_mul_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (S : Matrix n m 𝕜) : inertiaPos (Sᴴ * A * S) ≤ inertiaPos A := by
  sorry

/-- A congruence by any matrix does not increase the negative index.
Port of `NLAlib.card_eigenvalues₀_neg_congruence_le`. -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_conjTranspose_mul_mul_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (S : Matrix n m 𝕜) : inertiaNeg (Sᴴ * A * S) ≤ inertiaNeg A := by
  sorry

/-- **Ostrowski's theorem.** Congruence by `S` multiplies each eigenvalue by a factor between
the squares of the smallest and largest singular values of `S`.
[HornJohnson2013, Theorem 4.5.9]. Port of `NLAlib.exists_eigenvalues₀_congruence_scale`.
Result: ostrowski -/
theorem _root_.Matrix.IsHermitian.exists_eigenvalue_conjTranspose_mul_mul_eq_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (S : Matrix n n 𝕜) {k j : ℕ} (hk : k < Fintype.card n) (hj : j + 1 = Fintype.card n) :
    ∃ θ : ℝ, singularValues S j ^ 2 ≤ θ ∧ θ ≤ specNorm S ^ 2 ∧
      eigenvalue (Sᴴ * A * S) k = θ * eigenvalue A k := by
  sorry

/-! ### Inertia and interlacing -/

/-- **Adding a Hermitian matrix with `p` positive eigenvalues moves each eigenvalue up by at most
`p` places**: `λ_{i+p}(A + B) ≤ λ_i(A)` with `p = inertiaPos B`, for `i + p` below the size.
[HornJohnson2013, Corollary 4.3.5].
Port of `NLAlib.eigenvalues₀_add_le_of_card_pos`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_add_le_of_inertiaPos
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {i : ℕ} (hi : i + inertiaPos B < Fintype.card n) :
    eigenvalue (A + B) (i + inertiaPos B) ≤ eigenvalue A i := by
  sorry

/-- Adding a Hermitian matrix with `q` negative eigenvalues moves each eigenvalue down by at most
`q` places: `λ_{i+q}(A) ≤ λ_i(A + B)` with `q = inertiaNeg B`, for `i + q` below the size.
Port of `NLAlib.eigenvalues₀_le_add_of_card_neg`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_eigenvalue_add_of_inertiaNeg
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {i : ℕ} (hi : i + inertiaNeg B < Fintype.card n) :
    eigenvalue A (i + inertiaNeg B) ≤ eigenvalue (A + B) i := by
  sorry

/-- **A strict Courant–Fischer bound from below**: if the form of `A` exceeds `c` on a subspace
of dimension `k + 1`, then `c < λ_k(A)`.
Port of `NLAlib.lt_eigenvalues₀_of_forall_mem`. -/
theorem _root_.Matrix.IsHermitian.lt_eigenvalue_of_posDef_conjTranspose_mul_mul_sub
    {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} {V : Matrix n (Fin (k + 1)) 𝕜} (hV : HasOrthonormalCols V)
    {c : ℝ} (h : (Vᴴ * A * V - c • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜)).PosDef) :
    c < eigenvalue A k := by
  sorry

/-! ### Blocks -/

/-- The positive index of a block diagonal matrix is the sum of those of the blocks.
Port of `NLAlib.inertiaPos_fromBlocks_zero`. -/
theorem _root_.Matrix.IsHermitian.inertiaPos_fromBlocks_diagonal
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    inertiaPos (Matrix.fromBlocks A 0 0 C) = inertiaPos A + inertiaPos C := by
  sorry

/-- The negative index of a block diagonal matrix is the sum of those of the blocks.
Port of `NLAlib.inertiaNeg_fromBlocks_zero`. -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_fromBlocks_diagonal
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    inertiaNeg (Matrix.fromBlocks A 0 0 C) = inertiaNeg A + inertiaNeg C := by
  sorry

/-- **Haynsworth inertia additivity**, positive index: for an invertible Hermitian block `A`,
the inertia of the block matrix is that of `A` plus that of the Schur complement.
[HornJohnson2013, §4.5].
Port of `NLAlib.inertiaPos_fromBlocks_eq_add_schur`, there over `ℝ`.
Result: haynsworth -/
theorem _root_.Matrix.IsHermitian.inertiaPos_fromBlocks
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hAu : IsUnit A.det) (hC : C.IsHermitian) (B : Matrix m n 𝕜) :
    inertiaPos (Matrix.fromBlocks A B Bᴴ C) = inertiaPos A + inertiaPos (C - Bᴴ * A⁻¹ * B) := by
  sorry

/-- **Haynsworth inertia additivity**, negative index.
Port of `NLAlib.inertiaNeg_fromBlocks_eq_add_schur`.
Result: haynsworth -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_fromBlocks
    {A : Matrix m m 𝕜} {C : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hAu : IsUnit A.det) (hC : C.IsHermitian) (B : Matrix m n 𝕜) :
    inertiaNeg (Matrix.fromBlocks A B Bᴴ C) = inertiaNeg A + inertiaNeg (C - Bᴴ * A⁻¹ * B) := by
  sorry

/-- **The inertia of a saddle-point matrix.** For `A` positive definite, the matrix
`[[A, B], [Bᴴ, 0]]` has as many positive eigenvalues as `A` has rows.
[GolubVanLoan2013, §4.4 context]. -/
theorem _root_.Matrix.PosDef.inertiaPos_fromBlocks_zero {A : Matrix m m 𝕜} (hA : A.PosDef)
    (B : Matrix m n 𝕜) :
    inertiaPos (Matrix.fromBlocks A B Bᴴ 0) = Fintype.card m := by
  sorry

/-- The inertia of a saddle-point matrix: for `A` positive definite, `[[A, B], [Bᴴ, 0]]` has
`rank B` negative eigenvalues. -/
theorem _root_.Matrix.PosDef.inertiaNeg_fromBlocks_zero {A : Matrix m m 𝕜} (hA : A.PosDef)
    (B : Matrix m n 𝕜) : inertiaNeg (Matrix.fromBlocks A B Bᴴ 0) = B.rank := by
  sorry

/-! ### Counting eigenvalues -/

/-- The negative index of `A - x • 1` counts the eigenvalues of `A` below `x`.
Port of `NLAlib.inertiaNeg_sub_smul_one_eq_card`. -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_sub_smul_one
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : ℝ) :
    inertiaNeg (A - x • (1 : Matrix n n 𝕜)) =
      ((Finset.range (Fintype.card n)).filter fun i => eigenvalue A i < x).card := by
  sorry

/-- The positive index of `A - x • 1` counts the eigenvalues of `A` above `x`.
Port of `NLAlib.inertiaPos_sub_smul_one_eq_card`. -/
theorem _root_.Matrix.IsHermitian.inertiaPos_sub_smul_one
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : ℝ) :
    inertiaPos (A - x • (1 : Matrix n n 𝕜)) =
      ((Finset.range (Fintype.card n)).filter fun i => x < eigenvalue A i).card := by
  sorry

/-- **Counting eigenvalues by a triangular factorization.** If `A - x • 1 = L D Lᴴ` with `L`
invertible and `D` real diagonal, the number of eigenvalues of `A` below `x` is the number of
negative entries of `D`. [GolubVanLoan2013, §8.4.2].
Port of `NLAlib.card_eigenvalues_lt_eq_card_neg_of_eq_mul_diagonal_mul`. -/
theorem _root_.Matrix.IsHermitian.card_eigenvalue_lt_eq_card_neg_of_sub_smul_one_eq
    {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : ℝ} {L : Matrix n n 𝕜} (hL : IsUnit L.det) {d : n → ℝ}
    (h : A - x • (1 : Matrix n n 𝕜) = L * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Lᴴ) :
    ((Finset.range (Fintype.card n)).filter fun i => eigenvalue A i < x).card =
      (Finset.univ.filter fun i => d i < 0).card := by
  sorry

/-- **Counting eigenvalues by pivots** (the Sturm count). If elimination on `A - x • 1` meets no
zero pivot, the number of eigenvalues of `A` below `x`, which is `inertiaNeg (A - x • 1)`, is
the number of negative pivots (the pivots of a Hermitian matrix are real).
[GolubVanLoan2013, Theorem 8.4.1]; [Parlett1998, §3.3].
Port of `NLAlib.card_eigenvalues_lt_eq_card_sign_changes`, which the prototype leaves unproved.
Result: sturm-count -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_sub_smul_one_eq_card_gaussState_re_neg {k : ℕ}
    {A : Matrix (Fin k) (Fin k) 𝕜} (hA : A.IsHermitian) (x : ℝ)
    (hp : ∀ i : Fin k, gaussState (A - x • (1 : Matrix (Fin k) (Fin k) 𝕜)) i i i ≠ 0) :
    inertiaNeg (A - x • (1 : Matrix (Fin k) (Fin k) 𝕜)) =
      (Finset.univ.filter fun i : Fin k =>
        RCLike.re (gaussState (A - x • (1 : Matrix (Fin k) (Fin k) 𝕜)) i i i) < 0).card := by
  sorry

end NLAlib
