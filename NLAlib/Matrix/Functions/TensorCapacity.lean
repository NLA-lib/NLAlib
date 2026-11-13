/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Topology.Order.IsLUB
public import NLAlib.Matrix.Functions.OperatorBalancing
public import NLAlib.Matrix.Functions.Perspective

/-!
# Capacity of tensor products

The tensor product of two Kraus tuples has capacity given by the dimension-weighted product of
the two capacities.

## Main results

* `NLAlib.operatorCapacity_krausMap_kronecker`.
-/
@[expose] public section

open Matrix

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- A positive-capacity Kraus map sends every normalized positive definite
test matrix to a positive definite matrix. Its determinant is bounded below
by the positive capacity. -/
theorem posDef_krausMap_of_operatorCapacity_pos
    (A : ι → Matrix n n ℂ) (hcap : 0 < operatorCapacity (krausMap A))
    {X : Matrix n n ℂ} (hX : X.PosDef) (hdet : X.det = 1) :
    (krausMap A X).PosDef := by
  have hpos : 0 < (krausMap A X).det.re :=
    hcap.trans_le (operatorCapacity_le_det_apply (krausMap A) (krausMap_posSemidef A) hX hdet)
  apply (krausMap_posSemidef A X hX.posSemidef).posDef_iff_det_ne_zero.mpr
  intro hzero
  simp only [hzero, Complex.zero_re, lt_self_iff_false] at hpos

/-- Normalizing a positive-capacity Kraus family at an actual determinant-one
positive definite test matrix gives an invertible unital scaling. The product
of its squared determinant factors is exactly the reciprocal objective value.
Source: GGOW, arXiv:1511.03730v4, Lemma 3.9, normalization formula. -/
theorem exists_isUnit_unital_scaling_of_operatorCapacity_pos
    (A : ι → Matrix n n ℂ) (hcap : 0 < operatorCapacity (krausMap A))
    {X : Matrix n n ℂ} (hX : X.PosDef) (hdet : X.det = 1) :
    ∃ L R : Matrix n n ℂ, IsUnit L ∧ IsUnit R ∧
      krausMap (fun a => L * A a * R) 1 = 1 ∧
      Complex.normSq L.det * Complex.normSq R.det = ((krausMap A X).det.re)⁻¹ := by
  let Y := krausMap A X
  have hY : Y.PosDef := posDef_krausMap_of_operatorCapacity_pos A hcap hX hdet
  let R := CFC.sqrt X
  let L := (CFC.sqrt Y)⁻¹
  have hR : IsUnit R := hX.isUnit_sqrt
  have hL : IsUnit L := Matrix.isUnit_nonsing_inv_iff.mpr hY.isUnit_sqrt
  have hRH : R.IsHermitian := (CFC.sqrt_nonneg X).isSelfAdjoint
  have hLH : L.IsHermitian := Matrix.IsHermitian.inv (CFC.sqrt_nonneg Y).isSelfAdjoint
  have hRX : R * 1 * Rᴴ = X := by
    rw [Matrix.mul_one, hRH.eq]
    exact CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg
  have hLY : L * Y * Lᴴ = 1 := by
    rw [hLH.eq, ← CFC.sqrt_mul_sqrt_self Y hY.posSemidef.nonneg, ← Matrix.mul_assoc]
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit_sqrt
    change (CFC.sqrt Y)⁻¹ * CFC.sqrt Y * CFC.sqrt Y * (CFC.sqrt Y)⁻¹ = 1
    rw [Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_nonsing_inv _ hd]
  have hRdet : (Complex.normSq R.det : ℂ) = X.det := by
    have h := congrArg Matrix.det hRX
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, mul_one,
      Matrix.det_conjTranspose] at h
    rw [Complex.normSq_eq_conj_mul_self]
    simpa only [Complex.star_def, mul_comm] using h
  have hRdet1 : Complex.normSq R.det = 1 := by
    have h := congrArg Complex.re hRdet
    simpa only [hdet, Complex.ofReal_re, Complex.one_re] using h
  have hLdet : (Complex.normSq L.det : ℂ) * Y.det = 1 := by
    have h := congrArg Matrix.det hLY
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]
    simpa only [Complex.star_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hLdetre : Complex.normSq L.det * Y.det.re = 1 := by
    have h := congrArg Complex.re hLdet
    simpa only [Complex.re_ofReal_mul, Complex.one_re] using h
  refine ⟨L, R, hL, hR, ?_, ?_⟩
  · rw [krausMap_mul_mul_apply, hRX]
    exact hLY
  · rw [hRdet1, mul_one]
    exact eq_inv_of_mul_eq_one_left hLdetre

end NLAlib

open Matrix Filter

open scoped BigOperators ComplexOrder MatrixOrder Kronecker Topology

namespace NLAlib

variable {n m ι κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype ι] [Fintype κ]

/-- Every positive map has a sequence of normalized positive definite test
matrices whose determinant objectives tend to its capacity. -/
theorem exists_seq_det_tendsto_operatorCapacity
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef) :
    ∃ X : ℕ → Matrix n n ℂ,
      (∀ k, (X k).PosDef) ∧ (∀ k, (X k).det = 1) ∧
      Tendsto (fun k => (T (X k)).det.re) atTop (𝓝 (operatorCapacity T)) := by
  obtain ⟨d, _, hlim, hmem⟩ := exists_seq_tendsto_sInf
    (operatorCapacity_attainable_nonempty T) (operatorCapacity_attainable_bddBelow T hT)
  choose X hX hdet hd using hmem
  refine ⟨X, hX, hdet, ?_⟩
  have hfun : (fun k => (T (X k)).det.re) = d := funext fun k => (hd k).symm
  rw [hfun]
  exact hlim

omit [DecidableEq n] [DecidableEq m] in
/-- The tensor Kraus family acts componentwise on a pure tensor matrix. -/
theorem krausMap_kronecker_apply (A : ι → Matrix n n ℂ) (B : κ → Matrix m m ℂ)
    (X : Matrix n n ℂ) (Y : Matrix m m ℂ) :
    krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2) (X ⊗ₖ Y) =
      krausMap A X ⊗ₖ krausMap B Y := by
  simp only [krausMap_apply, Fintype.sum_prod_type, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul_sum]

private theorem re_det_kronecker {X : Matrix n n ℂ} {Y : Matrix m m ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (X ⊗ₖ Y).det.re = X.det.re ^ Fintype.card m * Y.det.re ^ Fintype.card n := by
  have hXi : X.det.im = 0 := (Complex.nonneg_iff.mp hX.det_nonneg).2.symm
  have hYi : Y.det.im = 0 := (Complex.nonneg_iff.mp hY.det_nonneg).2.symm
  have hXreal : X.det = (X.det.re : ℂ) := by apply Complex.ext <;> simp [hXi]
  have hYreal : Y.det = (Y.det.re : ℂ) := by apply Complex.ext <;> simp [hYi]
  rw [Matrix.det_kronecker, hXreal, hYreal, ← Complex.ofReal_pow,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp

/-- Tensor capacity is at most the product of the corresponding capacity
powers. Normalized pure tensor test matrices and independent approximating
sequences prove the bound even when either capacity is zero.
Source: Garg--Gurvits--Oliveira--Wigderson (2015), Lemma 3.12.
-/
theorem operatorCapacity_krausMap_kronecker_le
    (A : ι → Matrix n n ℂ) (B : κ → Matrix m m ℂ) :
    operatorCapacity (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2)) ≤
      operatorCapacity (krausMap A) ^ Fintype.card m *
        operatorCapacity (krausMap B) ^ Fintype.card n := by
  obtain ⟨X, hX, hXdet, hXlim⟩ :=
    exists_seq_det_tendsto_operatorCapacity (krausMap A) (krausMap_posSemidef A)
  obtain ⟨Y, hY, hYdet, hYlim⟩ :=
    exists_seq_det_tendsto_operatorCapacity (krausMap B) (krausMap_posSemidef B)
  apply ge_of_tendsto ((hXlim.pow (Fintype.card m)).mul (hYlim.pow (Fintype.card n)))
  apply Filter.Eventually.of_forall
  intro k
  have hdet : (X k ⊗ₖ Y k).det = 1 := by
    rw [Matrix.det_kronecker, hXdet, hYdet]
    simp
  have hbound := operatorCapacity_le_det_apply
    (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2))
    (krausMap_posSemidef _) ((hX k).kronecker (hY k)) hdet
  rw [krausMap_kronecker_apply,
    re_det_kronecker (krausMap_posSemidef A _ (hX k).posSemidef)
      (krausMap_posSemidef B _ (hY k).posSemidef)] at hbound
  exact hbound

omit [DecidableEq n] [DecidableEq m] in
private theorem frobNormSq_kronecker_complex (X : Matrix n n ℂ) (Y : Matrix m m ℂ) :
    (frobNorm (X ⊗ₖ Y) ^ 2) = (frobNorm X ^ 2) * (frobNorm Y ^ 2) := by
  simp only [frobNorm_sq_eq_sum, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    norm_mul, mul_pow]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem frobNormSq_one_complex : (frobNorm (1 : Matrix n n ℂ) ^ 2) = Fintype.card n := by
  exact frobNorm_one_sq

private theorem frobNormSq_sub_one_eq_sub_card {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (htr : X.trace = (Fintype.card n : ℂ)) :
    (frobNorm (X - 1) ^ 2) = (frobNorm X ^ 2) - Fintype.card n := by
  have hinner : frobInner X 1 = (Fintype.card n : ℝ) := by
    rw [frobInner_eq_re_trace, hX.eq, Matrix.mul_one, htr]
    simp
  rw [frobNorm_sub_sq, hinner, frobNormSq_one_complex]
  ring

/-- The image of the identity under a tensor Kraus family is the tensor
product of the two individual images of the identity. -/
theorem krausMap_kronecker_one (A : ι → Matrix n n ℂ) (B : κ → Matrix m m ℂ) :
    krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2) 1 =
      krausMap A 1 ⊗ₖ krausMap B 1 := by
  simpa only [Matrix.one_kronecker_one] using krausMap_kronecker_apply A B 1 1

/-- Unitality is preserved by tensoring finite Kraus families. -/
theorem krausMap_kronecker_one_eq_one
    (A : ι → Matrix n n ℂ) (B : κ → Matrix m m ℂ)
    (hA : krausMap A 1 = 1) (hB : krausMap B 1 = 1) :
    krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2) 1 = 1 := by
  rw [krausMap_kronecker_one, hA, hB, Matrix.one_kronecker_one]

/-- The exact adjoint normalization defect of a tensor of two unital Kraus
families. The mixed terms vanish because both individual errors have trace
zero. This quantitative identity is used in the tensor-capacity lower bound. -/
theorem frobNorm_krausMap_kronecker_sub_one_sq
    (A : ι → Matrix n n ℂ) (B : κ → Matrix m m ℂ)
    (hA : krausMap A 1 = 1) (hB : krausMap B 1 = 1) :
    (frobNorm (krausMap (fun p : ι × κ => (A p.1 ⊗ₖ B p.2)ᴴ) 1 - 1) ^ 2) =
      (Fintype.card m : ℝ) * (frobNorm (krausMap (fun a => (A a)ᴴ) 1 - 1) ^ 2) +
      (Fintype.card n : ℝ) * (frobNorm (krausMap (fun b => (B b)ᴴ) 1 - 1) ^ 2) +
      (frobNorm (krausMap (fun a => (A a)ᴴ) 1 - 1) ^ 2) *
        (frobNorm (krausMap (fun b => (B b)ᴴ) 1 - 1) ^ 2) := by
  let X : Matrix n n ℂ := krausMap (fun a => (A a)ᴴ) 1
  let Y : Matrix m m ℂ := krausMap (fun b => (B b)ᴴ) 1
  have hX : X.PosSemidef := krausMap_posSemidef _ _ Matrix.PosSemidef.one
  have hY : Y.PosSemidef := krausMap_posSemidef _ _ Matrix.PosSemidef.one
  have hXtr : X.trace = (Fintype.card n : ℂ) := by
    have hAn : krausMap (fun a => ((A a)ᴴ)ᴴ) 1 = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hA
    simpa only [X, Matrix.trace_one] using
      trace_krausMap_eq_of_adjoint_unital (fun a => (A a)ᴴ) hAn 1
  have hYtr : Y.trace = (Fintype.card m : ℂ) := by
    have hBn : krausMap (fun b => ((B b)ᴴ)ᴴ) 1 = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hB
    simpa only [Y, Matrix.trace_one] using
      trace_krausMap_eq_of_adjoint_unital (fun b => (B b)ᴴ) hBn 1
  have hXYtr : (X ⊗ₖ Y).trace = (Fintype.card (n × m) : ℂ) := by
    rw [Matrix.trace_kronecker, hXtr, hYtr, Fintype.card_prod, Nat.cast_mul]
  have hmap : krausMap (fun p : ι × κ => (A p.1 ⊗ₖ B p.2)ᴴ) 1 = X ⊗ₖ Y := by
    simpa only [Matrix.conjTranspose_kronecker, X, Y] using
      krausMap_kronecker_one (fun a => (A a)ᴴ) (fun b => (B b)ᴴ)
  rw [hmap, frobNormSq_sub_one_eq_sub_card (hX.kronecker hY).isHermitian hXYtr,
    frobNormSq_kronecker_complex,
    frobNormSq_sub_one_eq_sub_card hX.isHermitian hXtr,
    frobNormSq_sub_one_eq_sub_card hY.isHermitian hYtr,
    Fintype.card_prod, Nat.cast_mul]
  ring

/-- Invertible scaling of each Kraus factor gives the corresponding tensor
scaling of capacity, with each scalar factor raised to the opposite matrix
dimension. This identity includes zero capacities. -/
theorem operatorCapacity_scaled_krausMap_kronecker
    (hN : 0 < Fintype.card n) (hM : 0 < Fintype.card m)
    (A : ι → Matrix n n ℂ) (B : κ → Matrix m m ℂ)
    (L R : Matrix n n ℂ) (P Q : Matrix m m ℂ)
    (hL : IsUnit L) (hR : IsUnit R) (hP : IsUnit P) (hQ : IsUnit Q) :
    operatorCapacity (krausMap
      (fun p : ι × κ => (L * A p.1 * R) ⊗ₖ (P * B p.2 * Q))) =
      (Complex.normSq L.det * Complex.normSq R.det) ^ Fintype.card m *
      (Complex.normSq P.det * Complex.normSq Q.det) ^ Fintype.card n *
      operatorCapacity (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2)) := by
  have hdim : 0 < Fintype.card (n × m) := by
    rw [Fintype.card_prod]
    exact Nat.mul_pos hN hM
  have hfamily :
      (fun p : ι × κ => (L * A p.1 * R) ⊗ₖ (P * B p.2 * Q)) =
      (fun p : ι × κ => (L ⊗ₖ P) * (A p.1 ⊗ₖ B p.2) * (R ⊗ₖ Q)) := by
    funext p
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  have hscale := operatorCapacity_congruence_scaling hdim
    (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2))
    (krausMap (fun p : ι × κ => (L * A p.1 * R) ⊗ₖ (P * B p.2 * Q)))
    (krausMap_posSemidef _) (L ⊗ₖ P) (R ⊗ₖ Q) (hL.kronecker hP)
    (hR.kronecker hQ) (fun X => by rw [hfamily, krausMap_mul_mul_apply])
  rw [hscale]
  simp only [Matrix.det_kronecker, map_mul, map_pow, mul_pow]
  ring

/-- Positive-capacity Kraus maps admit a sequence of invertible unital
scalings with adjoint Frobenius defect tending to zero. The determinant
scaling factors tend to the reciprocal original capacity. The construction
normalizes actual near-minimizing test matrices; it assumes no attaining
minimizer and uses no convergence theorem for an operator-scaling algorithm. -/
theorem exists_seq_unital_krausMap_scaling
    (hN : 0 < Fintype.card n) (A : ι → Matrix n n ℂ)
    (hcap : 0 < operatorCapacity (krausMap A)) :
    ∃ L R : ℕ → Matrix n n ℂ,
      (∀ k, IsUnit (L k)) ∧ (∀ k, IsUnit (R k)) ∧
      (∀ k, krausMap (fun a => L k * A a * R k) 1 = 1) ∧
      Tendsto (fun k => Complex.normSq (L k).det * Complex.normSq (R k).det)
        atTop (𝓝 ((operatorCapacity (krausMap A))⁻¹)) ∧
      Tendsto (fun k => (frobNorm (krausMap (fun a => (L k * A a * R k)ᴴ) 1 - 1) ^ 2))
        atTop (𝓝 0) := by
  obtain ⟨X, hX, hXdet, hXlim⟩ :=
    exists_seq_det_tendsto_operatorCapacity (krausMap A) (krausMap_posSemidef A)
  choose L R hL hR hS hfactor using fun k =>
    exists_isUnit_unital_scaling_of_operatorCapacity_pos A hcap (hX k) (hXdet k)
  let S : ℕ → ι → Matrix n n ℂ := fun k a => L k * A a * R k
  let f : ℕ → ℝ := fun k => Complex.normSq (L k).det * Complex.normSq (R k).det
  have hflim : Tendsto f atTop (𝓝 ((operatorCapacity (krausMap A))⁻¹)) := by
    convert hXlim.inv₀ hcap.ne' using 1
    funext k
    exact hfactor k
  have hScap (k : ℕ) : operatorCapacity (krausMap (S k)) =
      f k * operatorCapacity (krausMap A) := by
    exact operatorCapacity_congruence_scaling hN (krausMap A) (krausMap (S k))
      (krausMap_posSemidef A) (L k) (R k) (hL k) (hR k)
      (fun Y => krausMap_mul_mul_apply A (L k) (R k) Y)
  have hqpos (k : ℕ) : 0 < f k * operatorCapacity (krausMap A) := by
    have hdpos : 0 < (krausMap A (X k)).det.re :=
      hcap.trans_le (operatorCapacity_le_det_apply (krausMap A)
        (krausMap_posSemidef A) (hX k) (hXdet k))
    exact mul_pos (by rw [show f k = _ from hfactor k]; exact inv_pos.mpr hdpos) hcap
  have hqlim : Tendsto (fun k => f k * operatorCapacity (krausMap A)) atTop (𝓝 1) := by
    simpa only [inv_mul_cancel₀ hcap.ne'] using hflim.mul_const (operatorCapacity (krausMap A))
  have hδlim : Tendsto (fun k => -Real.log (f k * operatorCapacity (krausMap A)))
      atTop (𝓝 0) := by
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hqlim
    simpa only [Real.log_one, neg_zero, Function.comp_def] using hlog.neg
  have hδsmall : ∀ᶠ k : ℕ in atTop,
      -Real.log (f k * operatorCapacity (krausMap A)) ≤ 1 / 6 := by
    exact (hδlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))).mono
      (fun k hk => hk.le)
  refine ⟨L, R, hL, hR, hS, hflim, ?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall fun k => sq_nonneg _) ?_
    (show Tendsto (fun k => 6 * (-Real.log (f k * operatorCapacity (krausMap A))))
      atTop (𝓝 0) by simpa only [mul_zero] using hδlim.const_mul 6)
  filter_upwards [hδsmall] with k hk
  have hS1 : krausMap (S k) 1 = 1 := hS k
  have hbound := frobNorm_sub_one_sq_add_le_of_unital_of_exp_neg_le_operatorCapacity
    (S k) hS1 hk (show Real.exp (-(-Real.log (f k * operatorCapacity (krausMap A)))) ≤
      operatorCapacity (krausMap (S k)) by
        rw [neg_neg, Real.exp_log (hqpos k), hScap])
  simpa only [hS1, sub_self, frobNorm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] using hbound

/-- The lower tensor-capacity bound when both factor capacities are positive.
Actual near-minimizers give unital scalings with defects tending to zero;
the quantitative lower certificate then tends to one. -/
theorem le_operatorCapacity_krausMap_kronecker_of_pos
    (hN : 0 < Fintype.card n) (hM : 0 < Fintype.card m)
    (A : ι → Matrix n n ℂ) (B : κ → Matrix m m ℂ)
    (hcapA : 0 < operatorCapacity (krausMap A))
    (hcapB : 0 < operatorCapacity (krausMap B)) :
    operatorCapacity (krausMap A) ^ Fintype.card m *
        operatorCapacity (krausMap B) ^ Fintype.card n ≤
      operatorCapacity (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2)) := by
  obtain ⟨L, R, hL, hR, hS, hflim, ha⟩ := exists_seq_unital_krausMap_scaling hN A hcapA
  obtain ⟨P, Q, hP, hQ, hT, hglim, hb⟩ := exists_seq_unital_krausMap_scaling hM B hcapB
  let S : ℕ → ι → Matrix n n ℂ := fun k a => L k * A a * R k
  let T : ℕ → κ → Matrix m m ℂ := fun k b => P k * B b * Q k
  let e : ℕ → ℝ := fun k => (frobNorm (krausMap (fun p : ι × κ => (S k p.1 ⊗ₖ T k p.2)ᴴ) 1 - 1) ^ 2)
  have heq : e = fun k =>
      (Fintype.card m : ℝ) * (frobNorm (krausMap (fun a => (S k a)ᴴ) 1 - 1) ^ 2) +
      (Fintype.card n : ℝ) * (frobNorm (krausMap (fun b => (T k b)ᴴ) 1 - 1) ^ 2) +
      (frobNorm (krausMap (fun a => (S k a)ᴴ) 1 - 1) ^ 2) *
        (frobNorm (krausMap (fun b => (T k b)ᴴ) 1 - 1) ^ 2) := by
    funext k
    exact frobNorm_krausMap_kronecker_sub_one_sq (S k) (T k) (hS k) (hT k)
  have helim : Tendsto e atTop (𝓝 0) := by
    rw [heq]
    simpa only [mul_zero, zero_add] using
      ((ha.const_mul (Fintype.card m : ℝ)).add
        (hb.const_mul (Fintype.card n : ℝ))).add (ha.mul hb)
  have hesmall : ∀ᶠ k : ℕ in atTop,
      e k ≤ 1 / ((Fintype.card (n × m) : ℝ) + 1) := by
    exact (helim.eventually (gt_mem_nhds (by positivity :
      (0 : ℝ) < 1 / ((Fintype.card (n × m) : ℝ) + 1)))).mono fun k hk => hk.le
  have hrootlim : Tendsto
      (fun k => (1 - Real.sqrt ((Fintype.card (n × m) : ℝ) * e k)) ^
        Fintype.card (n × m)) atTop (𝓝 1) := by
    have hroot := (Real.continuous_sqrt.tendsto 0).comp
      (show Tendsto (fun k => (Fintype.card (n × m) : ℝ) * e k) atTop (𝓝 0) by
        simpa only [mul_zero] using helim.const_mul (Fintype.card (n × m) : ℝ))
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [Function.comp_def, Real.sqrt_zero, sub_zero, one_pow] using
      (hone.sub hroot).pow (Fintype.card (n × m))
  have hprodlim := ((hflim.pow (Fintype.card m)).mul (hglim.pow (Fintype.card n))).mul_const
    (operatorCapacity (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2)))
  have hlim := le_of_tendsto_of_tendsto hrootlim hprodlim
    (show ∀ᶠ k : ℕ in atTop,
      (1 - Real.sqrt ((Fintype.card (n × m) : ℝ) * e k)) ^ Fintype.card (n × m) ≤
        (Complex.normSq (L k).det * Complex.normSq (R k).det) ^ Fintype.card m *
        (Complex.normSq (P k).det * Complex.normSq (Q k).det) ^ Fintype.card n *
        operatorCapacity (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2)) by
      filter_upwards [hesmall] with k hk
      have hunital := krausMap_kronecker_one_eq_one (S k) (T k) (hS k) (hT k)
      have hlow := pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_unital
        (fun p : ι × κ => S k p.1 ⊗ₖ T k p.2) hunital (le_refl (e k)) hk
      rw [operatorCapacity_scaled_krausMap_kronecker hN hM A B
        (L k) (R k) (P k) (Q k) (hL k) (hR k) (hP k) (hQ k)] at hlow
      exact hlow)
  have hpos : 0 < operatorCapacity (krausMap A) ^ Fintype.card m *
      operatorCapacity (krausMap B) ^ Fintype.card n :=
    mul_pos (pow_pos hcapA _) (pow_pos hcapB _)
  have hdiv : 1 ≤
      operatorCapacity (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2)) /
      (operatorCapacity (krausMap A) ^ Fintype.card m *
        operatorCapacity (krausMap B) ^ Fintype.card n) := by
    simpa only [div_eq_mul_inv, mul_inv, inv_pow, mul_comm] using hlim
  simpa only [one_mul] using (le_div_iff₀ hpos).mp hdiv

/-- **Tensor multiplicativity of operator capacity.** For finite Kraus families on complex
matrices of positive orders $n,m$, including families of zero capacity,
$$\operatorname{cap}(T\otimes S)=\operatorname{cap}(T)^m\operatorname{cap}(S)^n.$$
[GargGurvitsOliveiraWigderson2015, Theorem 3.11].
Result: operator-capacity-scaling-identities -/
theorem operatorCapacity_krausMap_kronecker
    (hN : 0 < Fintype.card n) (hM : 0 < Fintype.card m)
    (A : ι → Matrix n n ℂ) (B : κ → Matrix m m ℂ) :
    operatorCapacity (krausMap (fun p : ι × κ => A p.1 ⊗ₖ B p.2)) =
      operatorCapacity (krausMap A) ^ Fintype.card m *
        operatorCapacity (krausMap B) ^ Fintype.card n := by
  refine le_antisymm (operatorCapacity_krausMap_kronecker_le A B) ?_
  have hA0 := operatorCapacity_krausMap_nonneg A
  have hB0 := operatorCapacity_krausMap_nonneg B
  by_cases hAz : operatorCapacity (krausMap A) = 0
  · simpa only [hAz, zero_pow (Nat.ne_of_gt hM), zero_mul] using
      operatorCapacity_krausMap_nonneg (fun p : ι × κ => A p.1 ⊗ₖ B p.2)
  by_cases hBz : operatorCapacity (krausMap B) = 0
  · simpa only [hBz, zero_pow (Nat.ne_of_gt hN), mul_zero] using
      operatorCapacity_krausMap_nonneg (fun p : ι × κ => A p.1 ⊗ₖ B p.2)
  exact le_operatorCapacity_krausMap_kronecker_of_pos hN hM A B
    (lt_of_le_of_ne hA0 (Ne.symm hAz)) (lt_of_le_of_ne hB0 (Ne.symm hBz))

end NLAlib
