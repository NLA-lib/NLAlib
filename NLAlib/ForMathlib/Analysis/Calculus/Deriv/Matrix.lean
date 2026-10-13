/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix

/-!
# Derivatives of matrix-valued functions of one variable

Derivatives of the product, the powers, the determinant (Jacobi's formula), the inverse and the
trace of powers of a differentiable one-parameter family of matrices. Hypotheses and matrix-valued
conclusions are entrywise, `∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t`, so the statements
do not depend on a choice of matrix norm. Upstream candidates for a file
`Mathlib.Analysis.Calculus.Deriv.Matrix`.

## Main results

* `Matrix.hasDerivAt_iff_forall_apply`: the entrywise form of a derivative.
* `Matrix.hasDerivAt_mul_apply`, `Matrix.hasDerivAt_pow_succ_apply`: products and powers.
* `Matrix.hasDerivAt_det`: Jacobi's formula `(det A)' = tr (adj A · A')`.
* `Matrix.hasDerivAt_log_det`: `(log det A)' = tr (A⁻¹ A')`.
* `Matrix.hasDerivAt_inv_apply`: `(A⁻¹)' = -A⁻¹ A' A⁻¹`.
* `Matrix.hasDerivAt_trace_pow_succ`: `(tr Aᵏ⁺¹)' = (k + 1) tr (A' Aᵏ)`.
-/

@[expose] public section

namespace Matrix

variable {𝔽 : Type*} [NontriviallyNormedField 𝔽] {R : Type*} [NormedCommRing R]
  [NormedAlgebra 𝔽 R] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

omit [Fintype m] [Fintype n] in
/-- A matrix family is differentiable exactly when its entries are. `HasDerivAt` depends only on
the topology of the matrices, here Mathlib's global product topology, which every norm on
matrices induces; no matrix norm enters the statement. -/
theorem hasDerivAt_iff_forall_apply [Finite n] {A : 𝔽 → Matrix m n R} {A' : Matrix m n R}
    {t : 𝔽} : HasDerivAt A A' t ↔ ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t := by
  cases nonempty_fintype n
  exact hasDerivAt_pi.trans (forall_congr' fun i => hasDerivAt_pi)

omit [Fintype l] [Fintype n] in
/-- The derivative of a product of two matrix families, entrywise. -/
theorem hasDerivAt_mul_apply {A : 𝔽 → Matrix l m R} {B : 𝔽 → Matrix m n R} {A' : Matrix l m R}
    {B' : Matrix m n R} {t : 𝔽} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i : l) (j : n) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hA i k).mul (hB k j)
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact h

/-- The derivative of the trace of a matrix family. -/
theorem hasDerivAt_trace {A : 𝔽 → Matrix n n R} {A' : Matrix n n R} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt (fun s => (A s).trace) A'.trace t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hA i i

variable [DecidableEq n]

/-- The derivative of a power of a matrix family, entrywise:
`(Aᵏ⁺¹)' = ∑_{i + j = k} Aⁱ A' Aʲ`. -/
theorem hasDerivAt_pow_succ_apply {A : 𝔽 → Matrix n n R} {A' : Matrix n n R} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (k : ℕ) (i j : n) :
    HasDerivAt (fun s => (A s ^ (k + 1)) i j)
      ((∑ p ∈ Finset.antidiagonal k, A t ^ p.1 * A' * A t ^ p.2) i j) t := by
  induction k generalizing i j with
  | zero =>
    simpa only [zero_add, pow_one, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using hA i j
  | succ k ih =>
    have h := hasDerivAt_mul_apply (A := fun s => A s ^ (k + 1)) (B := A) (fun i j => ih i j) hA i j
    have hsum : ∑ p ∈ Finset.antidiagonal (k + 1), A t ^ p.1 * A' * A t ^ p.2 =
        (∑ p ∈ Finset.antidiagonal k, A t ^ p.1 * A' * A t ^ p.2) * A t + A t ^ (k + 1) * A' := by
      rw [Finset.Nat.sum_antidiagonal_succ', Finset.sum_mul, pow_zero, Matrix.mul_one, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [pow_succ, ← Matrix.mul_assoc]
    rw [hsum]
    simpa only [pow_succ _ (k + 1)] using h

/-- **The derivative of the trace of a power**: `(tr Aᵏ⁺¹)' = (k + 1) tr (A' Aᵏ)`.
Port of `NLAlib.hasDerivAt_matrix_trace_pow`, there over `ℝ` in the operator norm. -/
theorem hasDerivAt_trace_pow_succ {A : 𝔽 → Matrix n n R} {A' : Matrix n n R} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (k : ℕ) :
    HasDerivAt (fun s => (A s ^ (k + 1)).trace) ((k + 1) * (A' * A t ^ k).trace) t := by
  have h := hasDerivAt_trace fun i j => hasDerivAt_pow_succ_apply hA k i j
  have hval : (∑ p ∈ Finset.antidiagonal k, A t ^ p.1 * A' * A t ^ p.2).trace =
      (k + 1) * (A' * A t ^ k).trace := by
    rw [Matrix.trace_sum, Finset.sum_congr rfl (g := fun _ => (A' * A t ^ k).trace),
      Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    intro p hp
    rw [Matrix.trace_mul_cycle, ← pow_add, Matrix.trace_mul_comm, Nat.add_comm p.2 p.1,
      Finset.mem_antidiagonal.mp hp]
  rw [← hval]
  exact h

/-- The sum over rows of the determinants with one row replaced is the trace against the
adjugate. Port of `NLAlib.sum_det_updateRow_eq_trace_adjugate_mul`, there over `ℝ`. -/
theorem sum_det_updateRow {S : Type*} [CommRing S] (A H : Matrix n n S) :
    ∑ i, (A.updateRow i (H i)).det = (A.adjugate * H).trace := by
  simp_rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply]
  exact Finset.sum_comm

/-- **Jacobi's formula**: `(det A)' = tr (adj A · A')`.
Port of `NLAlib.hasDerivAt_det`, there over `ℝ` in the entrywise norm. -/
theorem hasDerivAt_det {A : 𝔽 → Matrix n n R} {A' : Matrix n n R} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt (fun s => (A s).det) ((A t).adjugate * A').trace t := by
  let D : ContinuousMultilinearMap 𝔽 (fun _ : n => n → R) R :=
    { (Matrix.detRowAlternating (R := R) (n := n)).toMultilinearMap.restrictScalars 𝔽 with
      cont := (continuous_id (X := Matrix n n R)).matrix_det }
  let B : 𝔽 → n → n → R := fun s i j => A s i j
  let B' : n → n → R := fun i j => A' i j
  have hB : HasDerivAt B B' t := hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hA i j
  have h := (D.hasFDerivAt (B t)).comp_hasDerivAt t hB
  have hval : D.linearDeriv (B t) B' = ((A t).adjugate * A').trace := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    exact sum_det_updateRow (A t) A'
  rw [← hval]
  exact h

/-- **The derivative of the inverse**, entrywise: `(A⁻¹)' = -A⁻¹ A' A⁻¹` where `A t` is
invertible. Port of `NLAlib.hasDerivAt_matrix_inv`, there over `ℝ` in the operator norm. -/
theorem hasDerivAt_inv_apply {A : 𝔽 → Matrix n n 𝔽} {A' : Matrix n n 𝔽} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (ht : IsUnit (A t).det) (i j : n) :
    HasDerivAt (fun s => (A s)⁻¹ i j) ((-((A t)⁻¹ * A' * (A t)⁻¹)) i j) t := by
  have hdet := hasDerivAt_det hA
  have hne : (A t).det ≠ 0 := ht.ne_zero
  have hdiff : ∀ i j, DifferentiableAt 𝔽 (fun s => (A s)⁻¹ i j) t := by
    intro i j
    have hadj : HasDerivAt (fun s => (A s).adjugate i j)
        ((((A t).updateRow j (Pi.single i 1)).adjugate * A'.updateRow j 0).trace) t := by
      simp only [Matrix.adjugate_apply (A _) i j]
      refine hasDerivAt_det (A := fun s => (A s).updateRow j (Pi.single i 1))
        (A' := A'.updateRow j 0) fun i' j' => ?_
      by_cases h : i' = j
      · simp only [Matrix.updateRow_apply, if_pos h, Pi.zero_apply]
        exact hasDerivAt_const t _
      · simp only [Matrix.updateRow_apply, if_neg h]
        exact hA i' j'
    have hmul := (hdet.inv hne).mul hadj
    simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact hmul.differentiableAt
  obtain ⟨B', hB⟩ : ∃ B' : Matrix n n 𝔽, ∀ i j, HasDerivAt (fun s => (A s)⁻¹ i j) (B' i j) t :=
    ⟨Matrix.of fun i j => deriv (fun s => (A s)⁻¹ i j) t, fun i j => (hdiff i j).hasDerivAt⟩
  have hev : ∀ᶠ s in nhds t, IsUnit (A s).det := by
    filter_upwards [hdet.continuousAt.eventually_ne hne] with s hs
    exact isUnit_iff_ne_zero.mpr hs
  have hzero : A' * (A t)⁻¹ + A t * B' = 0 := by
    ext i j
    have h1 := hasDerivAt_mul_apply hA hB i j
    have h2 : HasDerivAt (fun s => (A s * (A s)⁻¹) i j) 0 t := by
      refine (hasDerivAt_const t ((1 : Matrix n n 𝔽) i j)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with s hs
      rw [Matrix.mul_nonsing_inv _ hs]
    exact h1.unique h2
  have hB' : B' = -((A t)⁻¹ * A' * (A t)⁻¹) := by
    have h := congrArg ((A t)⁻¹ * ·) hzero
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul,
      Matrix.mul_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  rw [← hB']
  exact hB i j

/-- **The derivative of the logarithm of the determinant**: `(log det A)' = tr (A⁻¹ A')` where
`A t` is invertible. Port of `NLAlib.hasDerivAt_log_det`. -/
theorem hasDerivAt_log_det {A : ℝ → Matrix n n ℝ} {A' : Matrix n n ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (ht : (A t).det ≠ 0) :
    HasDerivAt (fun s => Real.log (A s).det) ((A t)⁻¹ * A').trace t := by
  have h := (hasDerivAt_det hA).log ht
  have hTrace : ((A t)⁻¹ * A').trace = ((A t).adjugate * A').trace / (A t).det := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      div_eq_inv_mul]
  rwa [← hTrace] at h

end Matrix
