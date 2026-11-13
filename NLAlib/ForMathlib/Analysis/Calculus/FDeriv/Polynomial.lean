/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Fréchet derivative of polynomial evaluation

A scalar polynomial is evaluated in a possibly noncommutative normed algebra. Its derivative
inserts a direction at each position in each monomial. Upstream candidate for Mathlib's polynomial
calculus and used in Hermitian and rational matrix differentiation.

## Main results

* `Polynomial.hasFDerivAt_aevalFDeriv`: polynomial evaluation has the finite insertion derivative.
-/

@[expose] public section

open scoped RightActions
namespace Polynomial
variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The derivative of polynomial evaluation in an arbitrary normed algebra,
as a finite sum of continuous linear insertion maps. -/
noncomputable def aevalFDeriv (p : 𝕜[X]) (x : A) : A →L[𝕜] A :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k •
    ∑ j ∈ Finset.range k,
      x ^ (k.pred - j) •> ContinuousLinearMap.id 𝕜 A <• x ^ j

/-- Evaluation of the polynomial derivative is the sum of products with
one occurrence of the direction at every insertion position. -/
theorem aevalFDeriv_apply (p : 𝕜[X]) (x h : A) :
    aevalFDeriv p x h = ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k • ∑ j ∈ Finset.range k, x ^ (k.pred - j) * h * x ^ j := by
  simp [aevalFDeriv, mul_assoc]

/-- Polynomial evaluation has the insertion-sum Fréchet derivative even
when the target algebra is noncommutative. -/
theorem hasFDerivAt_aevalFDeriv (p : 𝕜[X]) (x : A) :
    HasFDerivAt (fun y : A => aeval y p) (aevalFDeriv p x) x := by
  have heq : (fun y : A => aeval y p) =
      fun y => ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • y ^ k := by
    funext y
    rw [aeval_eq_sum_range]
  rw [heq]
  exact HasFDerivAt.fun_sum (fun k _ => (hasFDerivAt_pow' k).const_smul (p.coeff k))

/-- Constants have zero polynomial evaluation derivative. -/
@[simp] theorem aevalFDeriv_C (c : 𝕜) (x : A) :
    aevalFDeriv (C c) x = 0 := by
  apply (hasFDerivAt_aevalFDeriv (C c) x).unique
  convert! (hasFDerivAt_const (𝕜 := 𝕜) (algebraMap 𝕜 A c) x) using 1
  simp only [aeval_C]

/-- The derivative of the variable polynomial is the identity map. -/
@[simp] theorem aevalFDeriv_X (x : A) :
    aevalFDeriv (X : 𝕜[X]) x = ContinuousLinearMap.id 𝕜 A := by
  apply (hasFDerivAt_aevalFDeriv (X : 𝕜[X]) x).unique
  convert! (hasFDerivAt_id (𝕜 := 𝕜) x) using 1
  funext y
  exact aeval_X y

/-- The insertion derivative is additive in the polynomial. -/
@[simp] theorem aevalFDeriv_add (p q : 𝕜[X]) (x : A) :
    aevalFDeriv (p + q) x = aevalFDeriv p x + aevalFDeriv q x := by
  apply (hasFDerivAt_aevalFDeriv (p + q) x).unique
  convert! (hasFDerivAt_aevalFDeriv p x).add (hasFDerivAt_aevalFDeriv q x) using 1
  funext y
  exact map_add (aeval y) p q

/-- The polynomial derivative obeys the noncommutative product rule. -/
theorem aevalFDeriv_mul (p q : 𝕜[X]) (x : A) :
    aevalFDeriv (p * q) x =
      aeval x p •> aevalFDeriv q x + aevalFDeriv p x <• aeval x q := by
  apply (hasFDerivAt_aevalFDeriv (p * q) x).unique
  convert! (hasFDerivAt_aevalFDeriv p x).mul' (hasFDerivAt_aevalFDeriv q x) using 1
  funext y
  exact map_mul (aeval y) p q

/-- Algebra homomorphisms transport each insertion in a polynomial
derivative, without requiring continuity of the homomorphism. -/
theorem map_aevalFDeriv_apply {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]
    (f : A →ₐ[𝕜] B) (p : 𝕜[X]) (x h : A) :
    f (p.aevalFDeriv x h) = p.aevalFDeriv (f x) (f h) := by
  simp only [aevalFDeriv_apply, map_sum, map_smul, map_mul, map_pow]

end Polynomial
