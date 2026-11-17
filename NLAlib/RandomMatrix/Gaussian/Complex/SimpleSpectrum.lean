/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.RandomMatrix.Gaussian.Rank
public import NLAlib.Matrix.Spectral.Diagonalizable
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Separable

/-!
# Simple spectrum of complex Gaussian perturbations

A deterministic square matrix plus a nonzero multiple of a matrix with independent standard
complex Gaussian entries has a separable characteristic polynomial almost surely. The resultant
of the characteristic polynomial and its derivative is a nonzero polynomial in the entries.

## Main results

* `NLAlib.ae_charpoly_separable_of_hasLaw_complexGaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem eval_resultant_charpoly (P : Matrix n n (MvPolynomial (n × n) ℂ)) (x : n × n → ℂ) :
    MvPolynomial.eval x (P.charpoly.resultant P.charpoly.derivative
      (Fintype.card n) (Fintype.card n - 1)) =
      (P.map (MvPolynomial.eval x)).charpoly.resultant
        (P.map (MvPolynomial.eval x)).charpoly.derivative := by
  have hdeg : (P.charpoly.derivative.map (MvPolynomial.eval x)).natDegree =
      Fintype.card n - 1 := by
    rw [← Polynomial.derivative_map, Polynomial.natDegree_derivative,
      (Matrix.charpoly_monic P).natDegree_map, Matrix.charpoly_natDegree_eq_dim]
  rw [Matrix.charpoly_map, Polynomial.derivative_map, hdeg,
    (Matrix.charpoly_monic P).natDegree_map, Matrix.charpoly_natDegree_eq_dim,
    Polynomial.resultant_map_map]

private theorem exists_eval_eq_resultant_charpoly (M : Matrix n n ℂ) {c : ℂ} (hc : c ≠ 0) :
    ∃ q : MvPolynomial (n × n) ℂ, q ≠ 0 ∧ ∀ x : n × n → ℂ,
      MvPolynomial.eval x q =
        (M + c • Matrix.of x.curry).charpoly.resultant
          (M + c • Matrix.of x.curry).charpoly.derivative := by
  let P : Matrix n n (MvPolynomial (n × n) ℂ) :=
    fun i j => MvPolynomial.C (M i j) + MvPolynomial.C c * MvPolynomial.X (i,j)
  let q := P.charpoly.resultant P.charpoly.derivative
    (Fintype.card n) (Fintype.card n - 1)
  have heval (x : n × n → ℂ) : P.map (MvPolynomial.eval x) = M + c • Matrix.of x.curry := by
    ext i j
    change MvPolynomial.eval x (MvPolynomial.C (M i j) +
      MvPolynomial.C c * MvPolynomial.X (i,j)) = M i j + c * x (i,j)
    simp
  have he (x : n × n → ℂ) : MvPolynomial.eval x q =
      (M + c • Matrix.of x.curry).charpoly.resultant
        (M + c • Matrix.of x.curry).charpoly.derivative := by
    change MvPolynomial.eval x (P.charpoly.resultant P.charpoly.derivative
      (Fintype.card n) (Fintype.card n - 1)) = _
    rw [eval_resultant_charpoly, heval]
  refine ⟨q, ?_, he⟩
  let d : n → ℂ := fun i => ((Fintype.equivFin n i).val : ℂ)
  have hd : Function.Injective d := by
    intro i j hij
    apply (Fintype.equivFin n).injective
    apply Fin.ext
    change ((Fintype.equivFin n i).val : ℂ) = ((Fintype.equivFin n j).val : ℂ) at hij
    exact_mod_cast hij
  let x : n × n → ℂ := fun ij => c⁻¹ * (Matrix.diagonal d ij.1 ij.2 - M ij.1 ij.2)
  have hx : M + c • Matrix.of x.curry = Matrix.diagonal d := by
    ext i j
    change M i j + c * (c⁻¹ * (Matrix.diagonal d i j - M i j)) = Matrix.diagonal d i j
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, add_sub_cancel]
  have hsep : (Matrix.diagonal d).charpoly.Separable := by
    rw [Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr hd
  intro hq
  have hz := he x
  rw [hq, map_zero, hx] at hz
  exact (Polynomial.resultant_ne_zero _ _ hsep).symm hz

/-- A deterministic matrix plus a nonzero multiple of a matrix with independent standard complex
Gaussian entries has simple spectrum almost surely, expressed as separability of its
characteristic polynomial. This includes the empty matrix. No printed source. -/
theorem ae_charpoly_separable_of_hasLaw_complexGaussianMatrix
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {c : ℂ} (hc : c ≠ 0) :
    ∀ᵐ ω ∂μ, (M + c • G ω).charpoly.Separable := by
  obtain ⟨q, hq, he⟩ := exists_eval_eq_resultant_charpoly M hc
  have hflat : HasLaw (fun ω (ij : n × n) => G ω ij.1 ij.2)
      (Measure.pi fun _ : n × n => complexGaussian) μ :=
    (measurePreserving_curry_pi (ν := fun (_ : n) (_ : n) => complexGaussian)).symm.comp_hasLaw hG
  have hp : Measurable (fun x : n × n → ℂ => MvPolynomial.eval x q ≠ 0) := by
    exact measurableSet_setOfPred.1
      (((MvPolynomial.continuous_eval q).measurable (measurableSet_singleton 0)).compl)
  have hae := (hflat.ae_iff hp).2 (ae_eval_ne_zero_of_ne_zero hq)
  filter_upwards [hae] with ω hω
  have hne : (M + c • G ω).charpoly.resultant
      (M + c • G ω).charpoly.derivative ≠ 0 := by
    have hx : Matrix.of (Function.curry fun ij : n × n => G ω ij.1 ij.2) = G ω := by
      ext i j
      rfl
    rw [he] at hω
    rw [hx] at hω
    exact hω
  exact (Polynomial.separable_def _).2
    ((Polynomial.isUnit_resultant_iff_isCoprime (Matrix.charpoly_monic _)).1
      (isUnit_iff_ne_zero.mpr hne))

end NLAlib
