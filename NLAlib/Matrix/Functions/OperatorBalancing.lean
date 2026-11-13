/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Functions.OperatorCapacity
public import NLAlib.Matrix.Inequalities.DeterminantObjective
public import NLAlib.ForMathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
# Rank and capacity certificates for nearly balanced maps

Approximate balance of the two Kraus marginals controls rank and capacity. The results cover
both unital and adjoint-normalized maps.

## Main results

* `NLAlib.rank_le_rank_krausMap_of_unital`.
* `NLAlib.pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_unital`.
-/
@[expose] public section

open scoped BigOperators ComplexOrder

open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every normalized positive definite test matrix bounds operator capacity
from above, for a positive real-linear map. -/
theorem operatorCapacity_le_det_apply
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    {X : Matrix n n ℂ} (hX : X.PosDef) (hdet : X.det = 1) :
    operatorCapacity T ≤ (T X).det.re := by
  exact csInf_le (operatorCapacity_attainable_bddBelow T hT) ⟨X, hX, hdet, rfl⟩

/-- The identity matrix supplies an upper bound on operator capacity. -/
theorem operatorCapacity_le_det_apply_one
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef) :
    operatorCapacity T ≤ (T 1).det.re :=
  operatorCapacity_le_det_apply T hT Matrix.PosDef.one Matrix.det_one

/-- A positive map whose image of the identity has normalized trace and whose
capacity is at least `exp (-eps)` has squared Frobenius imbalance at most
`6 * eps`, provided $\varepsilon\le 1/6$. -/
theorem frobNorm_sub_one_sq_le_of_exp_neg_le_operatorCapacity
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (htr : (T 1).trace.re = (Fintype.card n : ℝ))
    {eps : ℝ} (heps : eps ≤ 1 / 6)
    (hcap : Real.exp (-eps) ≤ operatorCapacity T) :
    (frobNorm (T 1 - 1) ^ 2) ≤ 6 * eps := by
  have hdet : Real.exp (-eps) ≤ (T 1).det.re :=
    hcap.trans (operatorCapacity_le_det_apply_one T hT)
  have hdetpos : 0 < (T 1).det.re := (Real.exp_pos _).trans_le hdet
  have hne : (T 1).det ≠ 0 := by
    intro h
    simp [h] at hdetpos
  have hpos : (T 1).PosDef :=
    (hT 1 Matrix.PosSemidef.one).posDef_iff_det_ne_zero.mpr hne
  exact hpos.frobNorm_sub_one_sq_le_six_mul_of_exp_neg_le_det eps htr heps hdet

/-- Adjoint normalization of a finite Kraus family implies trace preservation
of its actual Kraus map. -/
theorem trace_krausMap_eq_of_adjoint_unital
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap (fun i => (A i)ᴴ) 1 = 1) (X : Matrix n n ℂ) :
    (krausMap A X).trace = X.trace := by
  have hsum : ∑ i, (A i)ᴴ * A i = 1 := by
    simpa only [krausMap_apply, Matrix.mul_one, Matrix.conjTranspose_conjTranspose]
      using hA
  calc
    (krausMap A X).trace = ∑ i, (A i * X * (A i)ᴴ).trace := by
      rw [krausMap_apply, Matrix.trace_sum]
    _ = ∑ i, ((A i)ᴴ * A i * X).trace :=
      Finset.sum_congr rfl fun i _ => Matrix.trace_mul_cycle _ _ _
    _ = ((∑ i, (A i)ᴴ * A i) * X).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [hsum, Matrix.one_mul]

/-- **Capacity-to-balance converse.** For a trace-preserving Kraus family with
$e^{-\delta}\le\operatorname{cap}(T)$ and $\delta\le1/6$, its two marginals satisfy
$$\|T(I)-I\|_{\mathsf{F}}^2+\|T^{\mathsf{H}}(I)-I\|_{\mathsf{F}}^2\le6\delta.$$
[GargGurvitsOliveiraWigderson2015, Lemma 3.6].
Result: operator-capacity-near-balanced-certificate -/
theorem frobNorm_sub_one_sq_add_le_of_adjoint_unital_of_exp_neg_le_operatorCapacity
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap (fun i => (A i)ᴴ) 1 = 1)
    {eps : ℝ} (heps : eps ≤ 1 / 6)
    (hcap : Real.exp (-eps) ≤ operatorCapacity (krausMap A)) :
    (frobNorm (krausMap A 1 - 1) ^ 2) +
      (frobNorm (krausMap (fun i => (A i)ᴴ) 1 - 1) ^ 2) ≤ 6 * eps := by
  rw [hA, sub_self, frobNorm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]
  apply frobNorm_sub_one_sq_le_of_exp_neg_le_operatorCapacity
    (krausMap A) (krausMap_posSemidef A) _ heps hcap
  rw [trace_krausMap_eq_of_adjoint_unital A hA 1]
  simp

/-- A positive map whose image of the identity has trace equal to the matrix
dimension has capacity at most one. The proof uses the identity trial point
and the PSD arithmetic-geometric mean inequality.
Source: Garg--Gurvits--Oliveira--Wigderson (2015), Proposition 2.8. -/
theorem operatorCapacity_le_one_of_trace_apply_one
    (hN : 0 < Fintype.card n)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (htr : (T 1).trace.re = (Fintype.card n : ℝ)) :
    operatorCapacity T ≤ 1 := by
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    operatorCapacity T ≤ (T 1).det.re := operatorCapacity_le_det_apply_one T hT
    _ ≤ ((T 1).trace.re / (Fintype.card n : ℝ)) ^ Fintype.card n :=
      (hT 1 Matrix.PosSemidef.one).re_det_le_pow_re_trace_div_card hN
    _ = 1 := by rw [htr, div_self hcard, one_pow]

/-- **Upper capacity bound for a unital Kraus family.**
The operator capacity is at most one. [GargGurvitsOliveiraWigderson2015, Proposition 2.8].
Result: operator-capacity-near-balanced-certificate -/
theorem operatorCapacity_krausMap_le_one_of_unital
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap A 1 = 1) :
    operatorCapacity (krausMap A) ≤ 1 := by
  simpa only [hA, Matrix.det_one, Complex.one_re] using
    operatorCapacity_le_det_apply_one (krausMap A) (krausMap_posSemidef A)

/-- **Upper capacity bound for a trace-preserving Kraus family.**
The operator capacity is at most one. [GargGurvitsOliveiraWigderson2015, Proposition 2.8].
Result: operator-capacity-near-balanced-certificate -/
theorem operatorCapacity_krausMap_le_one_of_adjoint_unital
    (hN : 0 < Fintype.card n)
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap (fun a => (A a)ᴴ) 1 = 1) :
    operatorCapacity (krausMap A) ≤ 1 := by
  apply operatorCapacity_le_one_of_trace_apply_one hN
    (krausMap A) (krausMap_posSemidef A)
  rw [trace_krausMap_eq_of_adjoint_unital A hA 1]
  simp

end NLAlib

open Matrix

open scoped BigOperators ComplexOrder MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In the empty matrix dimension, every real-linear map has operator capacity
`1`. No positivity assumption is needed. -/
theorem operatorCapacity_eq_one_of_isEmpty [IsEmpty n]
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    operatorCapacity T = 1 := by
  unfold operatorCapacity
  have hset :
      {d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re} =
        {1} := by
    ext d
    constructor
    · rintro ⟨X, hXpos, hXdet, hd⟩
      rw [hd]
      rw [Matrix.det_isEmpty]
      rfl
    · intro hd
      refine ⟨1, Matrix.PosDef.one, Matrix.det_one, ?_⟩
      rw [Matrix.det_isEmpty, hd]
      rfl
  rw [hset]
  exact csInf_singleton 1

omit [DecidableEq n] in
/-- Exact trace duality between a finite Kraus family and its
conjugate-transposed family. The test matrices need not be Hermitian. -/
theorem trace_mul_krausMap_eq_trace_mul_krausMap_conjTranspose
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (X Y : Matrix n n ℂ) :
    (Y * krausMap A X).trace = (X * krausMap (fun i => (A i).conjTranspose) Y).trace := by
  rw [krausMap_apply, krausMap_apply]
  rw [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  calc
    (Y * (A i * X * (A i).conjTranspose)).trace
        = ((Y * A i) * X * (A i).conjTranspose).trace := by
          simp [Matrix.mul_assoc]
    _ = ((A i).conjTranspose * Y * A i * X).trace := by
          simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (Y * A i) X
            (A i).conjTranspose
    _ = (X * (A i).conjTranspose * Y * A i).trace := by
          simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm
            ((A i).conjTranspose * Y * A i) X
    _ = (X * ((A i).conjTranspose * Y * ((A i).conjTranspose).conjTranspose)).trace := by
          simp [Matrix.mul_assoc, Matrix.conjTranspose_conjTranspose]

private theorem operatorCapacity_le_of_trace_eq
    (hN : 0 < Fintype.card n)
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (hS : ∀ X, X.PosSemidef → (S X).PosSemidef)
    (htrace : ∀ X Y, (Y * T X).trace = (X * S Y).trace) :
    operatorCapacity T ≤ operatorCapacity S := by
  apply le_csInf (operatorCapacity_attainable_nonempty S)
  rintro d ⟨Y, hY, hYdet, rfl⟩
  apply ((hS Y hY.posSemidef).isGLB_determinantTraceObjectiveSet hN).2
  rintro v ⟨X, hX, hXdet, rfl⟩
  calc
    operatorCapacity T ≤ (T X).det.re :=
      csInf_le (operatorCapacity_attainable_bddBelow T hT) ⟨X, hX, hXdet, rfl⟩
    _ ≤ (RCLike.re (Y * T X).trace / (Fintype.card n : ℝ)) ^ Fintype.card n :=
      (hT X hX.posSemidef).re_det_le_objective_of_det_one hN hY hYdet
    _ = (RCLike.re (X * S Y).trace / (Fintype.card n : ℝ)) ^ Fintype.card n := by
      rw [htrace X Y]

/-- Generic operator-capacity equality: if the real-linear maps `T` and `S`
preserve positive semidefiniteness and satisfy the trace identity
`trace (Y * T X) = trace (X * S Y)` for all `X`, `Y`, then
`operatorCapacity T = operatorCapacity S`.

The proof is a pure lower-bound argument: for a normalized positive definite `Y`
and PSD `M`, `re M.det` is the greatest lower bound of the determinant-trace
objective set of `M` (`Matrix.PosSemidef.isGLB_determinantTraceObjectiveSet`),
and the trace identity converts the objective of `S Y` at `X` into the objective
of `T X` at `Y`.  The empty dimension is handled separately by
`operatorCapacity_eq_one_of_isEmpty`. -/
theorem operatorCapacity_eq_of_trace_eq
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (hS : ∀ X, X.PosSemidef → (S X).PosSemidef)
    (htrace : ∀ X Y, (Y * T X).trace = (X * S Y).trace) :
    operatorCapacity T = operatorCapacity S := by
  classical
  by_cases hN : 0 < Fintype.card n
  · exact le_antisymm
      (operatorCapacity_le_of_trace_eq hN T S hT hS htrace)
      (operatorCapacity_le_of_trace_eq hN S T hS hT fun X Y => (htrace Y X).symm)
  · have hcard0 : Fintype.card n = 0 := Nat.eq_zero_of_not_pos hN
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hcard0
    rw [operatorCapacity_eq_one_of_isEmpty T, operatorCapacity_eq_one_of_isEmpty S]

/-- Operator capacity is invariant under taking the adjoint of a finite Kraus
family: `operatorCapacity (krausMap A) = operatorCapacity (krausMap A†)`.
This covers all finite dimensions, including the empty one, and singular or
zero-capacity maps. -/
theorem operatorCapacity_krausMap_conjTranspose
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ) :
    operatorCapacity (krausMap A) = operatorCapacity (krausMap (fun i => (A i).conjTranspose)) := by
  exact operatorCapacity_eq_of_trace_eq (krausMap A) (krausMap (fun i => (A i).conjTranspose))
    (krausMap_posSemidef A) (krausMap_posSemidef (fun i => (A i).conjTranspose))
    (fun X Y => trace_mul_krausMap_eq_trace_mul_krausMap_conjTranspose A X Y)

end NLAlib

open Matrix

open scoped BigOperators ComplexOrder MatrixOrder

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

omit [DecidableEq n] in
/-- Simultaneous left and right multiplication of a Kraus family realizes
the corresponding congruence scaling of its Kraus map. -/
theorem krausMap_mul_mul_apply (A : ι → Matrix n n ℂ) (B C X : Matrix n n ℂ) :
    krausMap (fun a => B * A a * C) X =
      B * krausMap A (C * X * Cᴴ) * Bᴴ := by
  simp only [krausMap_apply, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Matrix.mul_assoc]

/-- The nonnegative transition matrix associated with the entries of a finite
Kraus family. In eigenvector coordinates it sends input eigenvalues to output
eigenvalues. -/
private noncomputable def krausTransition (A : ι → Matrix n n ℂ) : Matrix n n ℝ :=
  fun i j => ∑ a, Complex.normSq (A a i j)

omit [Fintype n] [DecidableEq n] in
/-- Every entry of a Kraus transition matrix is nonnegative. -/
private theorem krausTransition_nonneg (A : ι → Matrix n n ℂ) (i j : n) :
    0 ≤ krausTransition A i j :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- On a real diagonal input, the real diagonal of a Kraus image is the
transition matrix applied to that input diagonal. -/
private theorem re_diag_krausMap_diagonal (A : ι → Matrix n n ℂ) (x : n → ℝ) (i : n) :
    (krausMap A (Matrix.diagonal fun j => (x j : ℂ)) i i).re =
      (krausTransition A *ᵥ x) i := by
  simp only [krausMap_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Matrix.conjTranspose_apply, Complex.re_sum,
    krausTransition, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_right_comm, Complex.star_def, Complex.mul_conj]
  simp

/-- Row sums of the Kraus transition matrix are the real diagonal of the
image of the identity. -/
private theorem sum_row_krausTransition (A : ι → Matrix n n ℂ) (i : n) :
    (∑ j, krausTransition A i j) = (krausMap A 1 i i).re := by
  simpa only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.mulVec, dotProduct, mul_one]
    using (re_diag_krausMap_diagonal A (fun _ => 1) i).symm

/-- Column sums of the Kraus transition matrix are the real diagonal of the
adjoint image of the identity. -/
private theorem sum_col_krausTransition (A : ι → Matrix n n ℂ) (j : n) :
    (∑ i, krausTransition A i j) =
      (krausMap (fun a => (A a)ᴴ) 1 j j).re := by
  rw [← sum_row_krausTransition]
  simp only [krausTransition, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.normSq_conj]

omit [DecidableEq n] in
private theorem sum_sq_re_diag_le_frobNormSq (M : Matrix n n ℂ) :
    (∑ i, (M i i).re ^ 2) ≤ (frobNorm M ^ 2) := by
  rw [frobNorm_sq_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    (M i i).re ^ 2 ≤ ‖M i i‖ ^ 2 := by
      simpa only [← pow_two, Complex.normSq_eq_norm_sq] using Complex.re_sq_le_normSq (M i i)
    _ ≤ ∑ j, ‖M i j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖M i j‖) (Finset.mem_univ i)

/-- Discarding off-diagonal entries bounds the squared row-sum error of a
Kraus transition matrix by the Frobenius defect of the map at the identity. -/
private theorem sum_sq_sum_row_krausTransition_sub_one_le (A : ι → Matrix n n ℂ) :
    (∑ i, (∑ j, krausTransition A i j - 1) ^ 2) ≤ (frobNorm (krausMap A 1 - 1) ^ 2) := by
  convert sum_sq_re_diag_le_frobNormSq (krausMap A 1 - 1) using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_row_krausTransition]
  simp

private theorem frobNorm_sub_one_of_unitary_conjugate {X Y Q : Matrix n n ℂ}
    (hY : Y = Qᴴ * X * Q) (hc : Qᴴ * Q = 1) (hr : Q * Qᴴ = 1) :
    frobNorm (Y - 1) = frobNorm (X - 1) := by
  have hQ : HasOrthonormalCols Q := hc
  have hQ' : HasOrthonormalCols Qᴴ := by
    change (Qᴴ)ᴴ * Qᴴ = 1
    simpa only [Matrix.conjTranspose_conjTranspose] using hr
  have hsub : Y - 1 = Qᴴ * (X - 1) * Q := by
    rw [hY]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hc]
  rw [hsub, Matrix.mul_assoc, hQ'.frobNorm_mul_left, hQ.frobNorm_mul_right]

/-- In input and output eigenvector coordinates, a Kraus family induces a
nonnegative matrix taking input eigenvalues to output eigenvalues. Both
marginal errors are bounded by the corresponding Frobenius normalization
defects. Exact normalization gives the corresponding exact marginal sums.
This is the spectral reduction in Garg--Gurvits--Oliveira--Wigderson (2015),
Lemma 3.4. -/
private theorem exists_krausTransition_eigenvalues_with_marginals
    (A : ι → Matrix n n ℂ)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    ∃ W : Matrix n n ℝ,
      (∀ i j, 0 ≤ W i j) ∧
      (krausMap (fun a => (A a)ᴴ) 1 = 1 → ∀ j, ∑ i, W i j = 1) ∧
      (krausMap A 1 = 1 → ∀ i, ∑ j, W i j = 1) ∧
      (∑ i, (∑ j, W i j - 1) ^ 2) ≤ (frobNorm (krausMap A 1 - 1) ^ 2) ∧
      (∑ j, (∑ i, W i j - 1) ^ 2) ≤
        (frobNorm (krausMap (fun a => (A a)ᴴ) 1 - 1) ^ 2) ∧
      W *ᵥ hX.isHermitian.eigenvalues =
        (krausMap_posSemidef A X hX).isHermitian.eigenvalues := by
  let hY := krausMap_posSemidef A X hX
  let u := hX.isHermitian.eigenvectorUnitary
  let v := hY.isHermitian.eigenvectorUnitary
  let U : Matrix n n ℂ := u
  let V : Matrix n n ℂ := v
  let B : ι → Matrix n n ℂ := fun a => Vᴴ * A a * U
  have hUU : U * Uᴴ = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self u
  have hU'U : Uᴴ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self u
  have hVV : V * Vᴴ = 1 := by
    simpa only [V, Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self v
  have hV'V : Vᴴ * V = 1 := by
    simpa only [V, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self v
  have hB_one : krausMap B 1 = Vᴴ * krausMap A 1 * V := by
    dsimp [B]
    rw [krausMap_mul_mul_apply]
    simp only [Matrix.mul_one, hUU, Matrix.conjTranspose_conjTranspose]
  have hB_adj : krausMap (fun a => (B a)ᴴ) 1 =
      Uᴴ * krausMap (fun a => (A a)ᴴ) 1 * U := by
    have hfamily : (fun a => (B a)ᴴ) = (fun a => Uᴴ * (A a)ᴴ * V) := by
      funext a
      simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [hfamily, krausMap_mul_mul_apply, Matrix.mul_one, hVV,
      Matrix.conjTranspose_conjTranspose]
  have hXspec : X = U * Matrix.diagonal (fun j => (hX.isHermitian.eigenvalues j : ℂ)) * Uᴴ := by
    convert hX.isHermitian.spectral_theorem using 1
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, U, u]
  have hYspec : Vᴴ * krausMap A X * V =
      Matrix.diagonal (fun i => (hY.isHermitian.eigenvalues i : ℂ)) := by
    convert hY.isHermitian.conjStarAlgAut_star_eigenvectorUnitary using 1 <;>
    simp [Matrix.star_eq_conjTranspose,
      Function.comp_def, V, v]
  have hBeig : krausMap B (Matrix.diagonal fun j => (hX.isHermitian.eigenvalues j : ℂ)) =
      Matrix.diagonal (fun i => (hY.isHermitian.eigenvalues i : ℂ)) := by
    rw [show krausMap B (Matrix.diagonal fun j => (hX.isHermitian.eigenvalues j : ℂ)) =
      Vᴴ * krausMap A
        (U * Matrix.diagonal (fun j => (hX.isHermitian.eigenvalues j : ℂ)) * Uᴴ) * V by
          simpa only [B, Matrix.conjTranspose_conjTranspose] using
            krausMap_mul_mul_apply A Vᴴ U
              (Matrix.diagonal fun j => (hX.isHermitian.eigenvalues j : ℂ))]
    rw [← hXspec, hYspec]
  refine ⟨krausTransition B, krausTransition_nonneg B, ?_, ?_, ?_, ?_, ?_⟩
  · intro hA j
    rw [sum_col_krausTransition, hB_adj, hA, Matrix.mul_one, hU'U]
    simp
  · intro hA i
    rw [sum_row_krausTransition, hB_one, hA, Matrix.mul_one, hV'V]
    simp
  · simpa only [frobNorm_sub_one_of_unitary_conjugate hB_one hV'V hVV] using
      sum_sq_sum_row_krausTransition_sub_one_le B
  · have hrow := sum_sq_sum_row_krausTransition_sub_one_le (fun a => (B a)ᴴ)
    have hcols : (∑ j, (∑ i, krausTransition B i j - 1) ^ 2) ≤
        (frobNorm (krausMap (fun a => (B a)ᴴ) 1 - 1) ^ 2) := by
      simpa only [krausTransition, Matrix.conjTranspose_apply, Complex.star_def,
        Complex.normSq_conj] using hrow
    simpa only [frobNorm_sub_one_of_unitary_conjugate hB_adj hU'U hUU] using hcols
  · funext i
    rw [← re_diag_krausMap_diagonal, hBeig]
    simp

/-- A trace-preserving Kraus family has a nonnegative column-stochastic
spectral transition, with squared row error bounded by its Frobenius defect. -/
private theorem exists_krausTransition_eigenvalues
    (A : ι → Matrix n n ℂ) (hA : krausMap (fun a => (A a)ᴴ) 1 = 1)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    ∃ W : Matrix n n ℝ, (∀ i j, 0 ≤ W i j) ∧
      (∀ j, ∑ i, W i j = 1) ∧
      (∑ i, (∑ j, W i j - 1) ^ 2) ≤ (frobNorm (krausMap A 1 - 1) ^ 2) ∧
      W *ᵥ hX.isHermitian.eigenvalues =
        (krausMap_posSemidef A X hX).isHermitian.eigenvalues := by
  obtain ⟨W, hW, hc, _, hr, _, heig⟩ :=
    exists_krausTransition_eigenvalues_with_marginals A hX
  exact ⟨W, hW, hc hA, hr, heig⟩

/-- A unital Kraus family has a nonnegative row-stochastic spectral
transition, with squared column error bounded by its adjoint Frobenius defect. -/
private theorem exists_krausTransition_eigenvalues_of_unital
    (A : ι → Matrix n n ℂ) (hA : krausMap A 1 = 1)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    ∃ W : Matrix n n ℝ, (∀ i j, 0 ≤ W i j) ∧
      (∀ i, ∑ j, W i j = 1) ∧
      (∑ j, (∑ i, W i j - 1) ^ 2) ≤
        (frobNorm (krausMap (fun a => (A a)ᴴ) 1 - 1) ^ 2) ∧
      W *ᵥ hX.isHermitian.eigenvalues =
        (krausMap_posSemidef A X hX).isHermitian.eigenvalues := by
  obtain ⟨W, hW, _, hr, _, hc, heig⟩ :=
    exists_krausTransition_eigenvalues_with_marginals A hX
  exact ⟨W, hW, hr hA, hc, heig⟩

end NLAlib

open Matrix

open scoped BigOperators ComplexOrder MatrixOrder


namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

omit [DecidableEq n] in
private theorem card_mul_lt_one_of_le_div_card_add_one {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1)) :
    (Fintype.card n : ℝ) * ε < 1 := by
  have hn0 : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hbound := (le_div_iff₀
    (show (0 : ℝ) < (Fintype.card n : ℝ) + 1 by positivity)).mp hεsmall
  rcases eq_or_lt_of_le hε0 with hzero | hpos
  · simp [← hzero]
  · nlinarith

/-- **Rank nondecrease under approximate balance.** If the trace-preserving Kraus family has
$\|T(I)-I\|_{\mathsf{F}}^2\le\varepsilon\le1/(n+1)$, then every positive semidefinite input
satisfies
$\operatorname{rank}(\mathbf{X})\le\operatorname{rank}(T(\mathbf{X}))$.
[GargGurvitsOliveiraWigderson2015, Theorem 2.12].
Result: operator-capacity-near-balanced-certificate -/
theorem rank_le_rank_krausMap_of_adjoint_unital
    (A : ι → Matrix n n ℂ) (hA : krausMap (fun a => (A a)ᴴ) 1 = 1)
    {ε : ℝ} (hε : (frobNorm (krausMap A 1 - 1) ^ 2) ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1))
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    X.rank ≤ (krausMap A X).rank := by
  obtain ⟨W, hW, hcol, hrow, heig⟩ := exists_krausTransition_eigenvalues A hA hX
  have hε0 := (sq_nonneg (frobNorm (krausMap A 1 - 1))).trans hε
  have hdef : (Fintype.card n : ℝ) *
      ∑ i, ((∑ j, W i j) - 1) ^ 2 < 1 :=
    (mul_le_mul_of_nonneg_left (hrow.trans hε) (Nat.cast_nonneg _)).trans_lt
      (card_mul_lt_one_of_le_div_card_add_one hε0 hεsmall)
  obtain ⟨σ, hσ⟩ := Matrix.exists_perm_pos_of_card_mul_sum_sq_row_sub_lt_one W hW hcol hdef
  have hcard := Matrix.card_nonzero_le_card_nonzero_mulVec_of_perm_pos
    W hW σ hσ hX.isHermitian.eigenvalues hX.eigenvalues_nonneg
  rw [heig] at hcard
  rw [hX.isHermitian.rank_eq_card_non_zero_eigs,
    (krausMap_posSemidef A X hX).isHermitian.rank_eq_card_non_zero_eigs]
  exact hcard

/-- **Rank nondecrease under approximate balance.** If the unital Kraus family has
$\|T^{\mathsf{H}}(I)-I\|_{\mathsf{F}}^2\le\varepsilon\le1/(n+1)$, then every positive semidefinite
input satisfies
$\operatorname{rank}(\mathbf{X})\le\operatorname{rank}(T(\mathbf{X}))$.
[GargGurvitsOliveiraWigderson2015, Theorem 2.12].
Result: operator-capacity-near-balanced-certificate -/
theorem rank_le_rank_krausMap_of_unital
    (A : ι → Matrix n n ℂ) (hA : krausMap A 1 = 1)
    {ε : ℝ} (hε : (frobNorm (krausMap (fun a => (A a)ᴴ) 1 - 1) ^ 2) ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1))
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    X.rank ≤ (krausMap A X).rank := by
  obtain ⟨W, hW, hrow, hcol, heig⟩ := exists_krausTransition_eigenvalues_of_unital A hA hX
  have hε0 := (sq_nonneg (frobNorm (krausMap (fun a => (A a)ᴴ) 1 - 1))).trans hε
  have hdef : (Fintype.card n : ℝ) *
      ∑ j, ((∑ i, W i j) - 1) ^ 2 < 1 :=
    (mul_le_mul_of_nonneg_left (hcol.trans hε) (Nat.cast_nonneg _)).trans_lt
      (card_mul_lt_one_of_le_div_card_add_one hε0 hεsmall)
  obtain ⟨σ, hσ⟩ := Matrix.exists_perm_pos_of_card_mul_sum_sq_column_sub_lt_one W hW hrow hdef
  have hcard := Matrix.card_nonzero_le_card_nonzero_mulVec_of_perm_pos
    W hW σ hσ hX.isHermitian.eigenvalues hX.eigenvalues_nonneg
  rw [heig] at hcard
  rw [hX.isHermitian.rank_eq_card_non_zero_eigs,
    (krausMap_posSemidef A X hX).isHermitian.rank_eq_card_non_zero_eigs]
  exact hcard

end NLAlib

open Matrix

open scoped BigOperators ComplexOrder MatrixOrder

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

private theorem re_det_eq_prod_eigenvalues {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M.det.re = ∏ i, hM.eigenvalues i := by
  rw [hM.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  rfl

/-- **Lower capacity bound from approximate balance.** For a trace-preserving Kraus family
with $\|T(I)-I\|_{\mathsf{F}}^2\le\varepsilon\le1/(n+1)$,
$$(1-\sqrt{n\varepsilon})^n\le\operatorname{cap}(T).$$
[GargGurvitsOliveiraWigderson2015, Lemma 3.4].
Result: operator-capacity-near-balanced-certificate -/
theorem pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_adjoint_unital
    (A : ι → Matrix n n ℂ)
    (hA : krausMap (fun a => (A a)ᴴ) 1 = 1)
    {ε : ℝ} (hε : (frobNorm (krausMap A 1 - 1) ^ 2) ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1)) :
    (1 - Real.sqrt ((Fintype.card n : ℝ) * ε)) ^ Fintype.card n ≤
      operatorCapacity (krausMap A) := by
  apply le_csInf (operatorCapacity_attainable_nonempty (krausMap A))
  rintro d ⟨X, hX, hXdet, rfl⟩
  obtain ⟨W, hW, hcol, hrow, heig⟩ := exists_krausTransition_eigenvalues A hA hX.posSemidef
  have hprod : ∏ i, hX.isHermitian.eigenvalues i = 1 := by
    rw [← re_det_eq_prod_eigenvalues hX.isHermitian, hXdet]
    rfl
  have hbound := Matrix.mul_prod_le_prod_mulVec_of_col_sum_one
    W hW hcol (hrow.trans hε) hεsmall hX.isHermitian.eigenvalues
      (fun i => hX.eigenvalues_pos i)
  rw [hprod, mul_one, heig] at hbound
  simpa only [re_det_eq_prod_eigenvalues
    (krausMap_posSemidef A X hX.posSemidef).isHermitian] using hbound

/-- **Lower capacity bound from approximate balance.** For a unital Kraus family
with $\|T^{\mathsf{H}}(I)-I\|_{\mathsf{F}}^2\le\varepsilon\le1/(n+1)$,
$$(1-\sqrt{n\varepsilon})^n\le\operatorname{cap}(T).$$
[GargGurvitsOliveiraWigderson2015, Lemma 3.4].
Result: operator-capacity-near-balanced-certificate -/
theorem pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_unital
    (A : ι → Matrix n n ℂ) (hA : krausMap A 1 = 1)
    {ε : ℝ} (hε : (frobNorm (krausMap (fun a => (A a)ᴴ) 1 - 1) ^ 2) ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1)) :
    (1 - Real.sqrt ((Fintype.card n : ℝ) * ε)) ^ Fintype.card n ≤
      operatorCapacity (krausMap A) := by
  rw [operatorCapacity_krausMap_conjTranspose A]
  apply pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_adjoint_unital
    (fun a => (A a)ᴴ) ?_ hε hεsmall
  simpa only [Matrix.conjTranspose_conjTranspose] using hA

end NLAlib

open Matrix

open scoped BigOperators ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Capacity-to-balance converse.** For a unital Kraus family with
$e^{-\delta}\le\operatorname{cap}(T)$ and $\delta\le1/6$, its two marginals satisfy
$$\|T(I)-I\|_{\mathsf{F}}^2+\|T^{\mathsf{H}}(I)-I\|_{\mathsf{F}}^2\le6\delta.$$
[GargGurvitsOliveiraWigderson2015, Lemma 3.6].
Result: operator-capacity-near-balanced-certificate -/
theorem frobNorm_sub_one_sq_add_le_of_unital_of_exp_neg_le_operatorCapacity
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap A 1 = 1)
    {eps : ℝ} (heps : eps ≤ 1 / 6)
    (hcap : Real.exp (-eps) ≤ operatorCapacity (krausMap A)) :
    (frobNorm (krausMap A 1 - 1) ^ 2) +
      (frobNorm (krausMap (fun i => (A i).conjTranspose) 1 - 1) ^ 2) ≤ 6 * eps := by
  have hA' : krausMap (fun i => ((A i).conjTranspose).conjTranspose) 1 = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hA
  have hcap' : Real.exp (-eps) ≤
      operatorCapacity (krausMap (fun i => (A i).conjTranspose)) := by
    rw [← operatorCapacity_krausMap_conjTranspose A]
    exact hcap
  have h := frobNorm_sub_one_sq_add_le_of_adjoint_unital_of_exp_neg_le_operatorCapacity
    (fun i => (A i).conjTranspose) hA' heps hcap'
  simpa only [Matrix.conjTranspose_conjTranspose, add_comm] using h

end NLAlib
