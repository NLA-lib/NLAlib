/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# The Sylvester equation

The Sylvester equation `A X - X B = C`, for square `A` and `B` of possibly different sizes over a
field, has exactly one solution `X` when the characteristic polynomials of `A` and `B` are
coprime; over an algebraically closed field this says that `A` and `B` have no common eigenvalue.
A block upper triangular matrix whose diagonal blocks satisfy this condition is therefore similar
to its block diagonal part.

## Main results

* `NLAlib.eq_zero_of_mul_eq_mul_of_isCoprime_charpoly`: only `X = 0` intertwines `A` and `B`.
* `NLAlib.existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly`: the Sylvester equation.
* `NLAlib.isCoprime_charpoly_iff_disjoint_spectrum`: coprimality as disjoint spectra.
* `NLAlib.exists_fromBlocks_mul_eq_mul_fromBlocks`: block diagonalisation.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- An intertwining relation `A Y = Y B` passes to polynomials in `A` and `B`. -/
private theorem aeval_mul_eq_mul_aeval {A : Matrix m m K} {B : Matrix n n K} {Y : Matrix m n K}
    (hY : A * Y = Y * B) (p : K[X]) : aeval A p * Y = Y * aeval B p := by
  have hpow : ∀ k : ℕ, A ^ k * Y = Y * B ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
    | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, hY, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
      Matrix.smul_mul, Matrix.mul_smul, hpow]

/-- If the characteristic polynomials of `A` and `B` are coprime, only `X = 0` intertwines them.
Port of `NLAlib.eq_zero_of_mul_eq_mul_of_isCoprime_charpoly`. -/
theorem eq_zero_of_mul_eq_mul_of_isCoprime_charpoly {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) {X : Matrix m n K} (hX : A * X = X * B) : X = 0 := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (aeval A) huv
  rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, zero_add, map_one] at h1
  have h2 := aeval_mul_eq_mul_aeval hX B.charpoly
  rw [Matrix.aeval_self_charpoly, Matrix.mul_zero] at h2
  rw [← Matrix.one_mul X, ← h1, Matrix.mul_assoc, h2, Matrix.mul_zero]

/-- **The Sylvester equation `A X - X B = C` has a unique solution** when the characteristic
polynomials of `A` and `B` are coprime. [HornJohnson2013, Theorem 2.4.4.1].
Port of `NLAlib.existsUnique_sylvester_of_isCoprime_charpoly`.
Result: sylvester-equation -/
theorem existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly (A : Matrix m m K) (B : Matrix n n K)
    (h : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C := by
  let T : Matrix m n K →ₗ[K] Matrix m n K :=
    { toFun Y := A * Y - Y * B
      map_add' Y Z := by rw [Matrix.mul_add, Matrix.add_mul, add_sub_add_comm]
      map_smul' c Y := by rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    exact eq_zero_of_mul_eq_mul_of_isCoprime_charpoly h (sub_eq_zero.mp hY)
  obtain ⟨Y, hY⟩ := LinearMap.injective_iff_surjective.mp hinj C
  exact ⟨Y, hY, fun Z hZ => hinj (hZ.trans hY.symm)⟩

/-- Over an algebraically closed field the characteristic polynomials are coprime exactly when
the spectra are disjoint. Port of `NLAlib.isCoprime_charpoly_iff_disjoint_spectrum`. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum [IsAlgClosed K] (A : Matrix m m K)
    (B : Matrix n n K) :
    IsCoprime A.charpoly B.charpoly ↔ Disjoint (spectrum K A) (spectrum K B) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K A.charpoly B.charpoly,
    Set.disjoint_left]
  refine forall_congr' fun a => ?_
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    IsRoot.def, IsRoot.def, coe_aeval_eq_eval]
  tauto

/-- **A block upper triangular matrix whose diagonal blocks have coprime characteristic
polynomials is similar to its block diagonal part.** [HornJohnson2013, Theorem 2.4.6.1 context]. -/
theorem exists_fromBlocks_mul_eq_mul_fromBlocks (A : Matrix m m K) (B : Matrix n n K)
    (h : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃ X : Matrix m n K,
      Matrix.fromBlocks A C 0 B * Matrix.fromBlocks 1 X 0 1 =
        Matrix.fromBlocks 1 X 0 1 * Matrix.fromBlocks A 0 0 B := by
  obtain ⟨Y, hY, -⟩ := existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly A B h (-C)
  refine ⟨Y, ?_⟩
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    Matrix.one_mul]
  rw [show A * Y + C = Y * B from by rw [sub_eq_iff_eq_add.mp hY]; abel]

end NLAlib
