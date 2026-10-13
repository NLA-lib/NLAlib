/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# The exponential and the logarithm of a Hermitian matrix

The matrix exponential is Mathlib's `NormedSpace.exp A`; for a Hermitian matrix it is
`cfc Real.exp A`. The logarithm of a positive definite matrix is `cfc Real.log A`. This file
gives the bridge, the order facts (`1 + A ≤ exp A`, comparison of `exp` with polynomials on the
spectrum), and the properties of the trace exponential `re (exp A).trace` used by the matrix
Laplace transform method: its expression through the eigenvalues, its bounds by the largest
eigenvalue, and its behaviour under shifts and unitary conjugation.

## Main results

* `Matrix.IsHermitian.exp_eq_cfc`: the bridge.
* `Matrix.IsHermitian.posDef_exp`, `Matrix.IsHermitian.cfc_log_exp`, `Matrix.PosDef.exp_cfc_log`.
* `Matrix.IsHermitian.one_add_le_exp`.
* `Matrix.IsHermitian.re_trace_exp`: `tr exp A = ∑ exp λ_i`.
* `Matrix.IsHermitian.exp_eigenvalue_zero_le_re_trace_exp`: `exp(λ_max) ≤ tr exp A`.
* `Matrix.IsHermitian.re_trace_exp_le_card_mul_exp`: `tr exp A ≤ n exp(λ_max)`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### The bridge -/

/-- The exponential of a real number, seen in `𝕜`. -/
private theorem exp_ofReal (x : ℝ) : exp ((x : ℝ) : 𝕜) = ((Real.exp x : ℝ) : 𝕜) := by
  have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := 𝕜) x
  rw [RCLike.algebraMap_eq_ofReal] at h
  rw [← h, Real.exp_eq_exp_ℝ]

/-- The exponential of a real diagonal matrix. -/
private theorem exp_diagonal_ofReal (d : n → ℝ) :
    exp (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      Matrix.diagonal fun i => ((Real.exp (d i) : ℝ) : 𝕜) := by
  rw [Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp]
  exact exp_ofReal (d i)

/-- The exponential commutes with unitary conjugation.
Port of `NLAlib.matrixExp_unitary_conj`, there over `ℂ`. -/
theorem exp_mul_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r] {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n) (A : Matrix r r 𝕜) :
    exp (U * A * Uᴴ) = U * exp A * Uᴴ := by
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq hr.symm
  let f : Matrix r r 𝕜 →+* Matrix n n 𝕜 :=
    { toFun := fun M => U * M * Uᴴ
      map_one' := by rw [Matrix.mul_one, hUU]
      map_mul' := fun M N => by simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
      map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.add_mul] }
  have hf : Continuous f :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h : f (exp A) = exp (f A) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.map_exp f hf A
  exact h.symm

/-- The exponential of a unitary diagonalisation: `exp (U D Uᴴ) = U exp(D) Uᴴ`, for `U` with
orthonormal columns and as many columns as rows. -/
theorem exp_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n)
    (d : r → ℝ) :
    exp (U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) =
      U * Matrix.diagonal (fun i => ((Real.exp (d i) : ℝ) : 𝕜)) * Uᴴ := by
  rw [exp_mul_mul_conjTranspose hU hr, exp_diagonal_ofReal]

/-- **The exponential of a Hermitian matrix through the functional calculus.**
Port of `NLAlib.matrixExp_smul_eq_cfc`, at `s = 1`. -/
theorem _root_.Matrix.IsHermitian.exp_eq_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    exp A = cfc Real.exp A := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  rw [cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAU Real.exp]
  conv_lhs => rw [hAU]
  exact exp_mul_diagonal_mul_conjTranspose hU hr _

/-- A scalar shift factors out of the exponential: `exp (A + t • 1) = e^t • exp A`. -/
theorem exp_add_real_smul_one (A : Matrix n n 𝕜) (t : ℝ) :
    exp (A + t • (1 : Matrix n n 𝕜)) = Real.exp t • exp A := by
  have hc : Commute A (t • (1 : Matrix n n 𝕜)) := (Commute.one_right A).smul_right t
  have ht : exp (t • (1 : Matrix n n 𝕜)) = Real.exp t • (1 : Matrix n n 𝕜) := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜),
      Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal]
    exact exp_diagonal_ofReal fun _ => t
  rw [Matrix.exp_add_of_commute A _ hc, ht, Matrix.mul_smul, Matrix.mul_one]

/-- The exponential of a block diagonal matrix. -/
theorem exp_fromBlocks_diagonal (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    exp (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (exp A) 0 0 (exp B) := by
  let f : Matrix m m 𝕜 × Matrix n n 𝕜 →+* Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
    { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.fromBlocks_multiply, Matrix.mul_zero,
          Matrix.zero_mul, add_zero, zero_add]
      map_zero' := Matrix.fromBlocks_zero
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.fromBlocks_add, add_zero] }
  have hf : Continuous f :=
    Continuous.matrix_fromBlocks continuous_fst continuous_const continuous_const continuous_snd
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp f hf (A, B)
  open scoped Matrix.Norms.Operator in
  have h1 : exp (A, B) = (exp A, exp B) := Prod.ext (Prod.fst_exp _) (Prod.snd_exp _)
  exact h.symm.trans (congrArg f h1)

/-! ### Positivity and the logarithm -/

/-- **The exponential of a Hermitian matrix is positive definite.**
Port of `NLAlib.posDef_matrixExp_and_matrixLog_matrixExp`, first half. -/
theorem _root_.Matrix.IsHermitian.posDef_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (exp A).PosDef := by
  rw [hA.exp.posDef_iff_eigenvalue_pos]
  intro k hk
  rw [hA.exp_eq_cfc, hA.eigenvalue_cfc_of_monotoneOn (Real.exp_monotone.monotoneOn Set.univ)
    (Set.subset_univ _) hk]
  exact Real.exp_pos _

/-- The logarithm inverts the exponential on Hermitian matrices.
Port of `NLAlib.posDef_matrixExp_and_matrixLog_matrixExp`, second half. -/
theorem _root_.Matrix.IsHermitian.cfc_log_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    cfc Real.log (exp A) = A := by
  have hsa : IsSelfAdjoint A := hA
  rw [hA.exp_eq_cfc, ← cfc_comp' Real.log Real.exp A
    ((A.finite_real_spectrum.image _).continuousOn _) (A.finite_real_spectrum.continuousOn _) hsa]
  conv_rhs => rw [← cfc_id' ℝ A hsa]
  exact cfc_congr fun x _ => Real.log_exp x

/-- The exponential inverts the logarithm on positive definite matrices. -/
theorem _root_.Matrix.PosDef.exp_cfc_log {A : Matrix n n 𝕜} (hA : A.PosDef) :
    exp (cfc Real.log A) = A := by
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hL : (cfc Real.log A).IsHermitian := cfc_predicate Real.log A
  rw [hL.exp_eq_cfc, ← cfc_comp' Real.exp Real.log A
    ((A.finite_real_spectrum.image _).continuousOn _) (A.finite_real_spectrum.continuousOn _) hsa]
  conv_rhs => rw [← cfc_id' ℝ A hsa]
  exact cfc_congr fun x hx => Real.exp_log (hA.spectrum_subset_Ioi hx)

/-- Eigenvalues of the exponential: `λ_k(exp A) = exp(λ_k(A))`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : ℕ} (hk : k < Fintype.card n) : eigenvalue (exp A) k = Real.exp (eigenvalue A k) := by
  rw [hA.exp_eq_cfc]
  exact hA.eigenvalue_cfc_of_monotoneOn (Real.exp_monotone.monotoneOn Set.univ)
    (Set.subset_univ _) hk

/-! ### Order -/

/-- **`1 + A ≤ exp A`** for Hermitian `A`.
[Tropp2015, §2.1]. Port of `NLAlib.one_add_le_matrixExp_of_isHermitian`. -/
theorem _root_.Matrix.IsHermitian.one_add_le_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    1 + A ≤ exp A := by
  have hsa : IsSelfAdjoint A := hA
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  have h1 : cfc (fun x : ℝ => 1 + x) A = 1 + A := by
    rw [cfc_const_add 1 (fun x => x) A (hcont _) hsa, cfc_id' ℝ A hsa, map_one]
  rw [hA.exp_eq_cfc, ← h1]
  exact cfc_mono (fun x _ => by linarith [Real.add_one_le_exp x]) (hcont _) (hcont _)

/-- **The transfer rule for the exponential.** If `exp (θ x) ≤ 1 + θ x + c x²` for every `x` in
`[a, b]` and `a • 1 ≤ A ≤ b • 1`, then `exp (θ • A) ≤ 1 + θ • A + c • A ^ 2`.
[Tropp2015, §2.1 and §6.6].
Port of `NLAlib.matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le`. -/
theorem exp_smul_le_one_add_smul_add_smul_sq {A : Matrix n n 𝕜} {a b θ c : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜))
    (h : ∀ x ∈ Set.Icc a b, Real.exp (θ * x) ≤ 1 + θ * x + c * x ^ 2) :
    exp (θ • A) ≤ 1 + θ • A + c • A ^ 2 := by
  have hA := isHermitian_of_le_smul_one h₂
  have hsa : IsSelfAdjoint A := hA
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  have hθA : θ • A = cfc (fun x : ℝ => θ * x) A := by
    rw [cfc_const_mul θ (fun x => x) A (hcont _), cfc_id' ℝ A hsa]
  have hH : (θ • A).IsHermitian := by
    rw [hθA]
    exact cfc_predicate _ A
  have hL : exp (θ • A) = cfc (fun x : ℝ => Real.exp (θ * x)) A := by
    rw [hH.exp_eq_cfc, hθA, ← cfc_comp' Real.exp (fun x => θ * x) A
      ((A.finite_real_spectrum.image _).continuousOn _) (hcont _) hsa]
  have hR : 1 + θ • A + c • A ^ 2 = cfc (fun x : ℝ => 1 + θ * x + c * x ^ 2) A := by
    rw [cfc_add A (fun x : ℝ => 1 + θ * x) (fun x : ℝ => c * x ^ 2) (hcont _) (hcont _),
      cfc_const_add 1 (fun x : ℝ => θ * x) A (hcont _) hsa,
      cfc_const_mul c (fun x : ℝ => x ^ 2) A (hcont _),
      cfc_pow (fun x : ℝ => x) 2 A (hcont _) hsa, cfc_id' ℝ A hsa, ← hθA, map_one]
  rw [hL, hR]
  exact cfc_le_cfc_of_forall_mem_Icc h₁ h₂ h

/-- **`log (1 + A) ≤ A`** for positive semidefinite `A`. This bounds matrix cumulant generating
functions in the Bernstein and Bennett inequalities. [Tropp2015, §6.6]. -/
theorem _root_.Matrix.PosSemidef.cfc_log_one_add_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    cfc Real.log (1 + A) ≤ A := by
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  have h1 : 1 + A = cfc (fun x : ℝ => 1 + x) A := by
    rw [cfc_const_add 1 (fun x => x) A (hcont _) hsa, cfc_id' ℝ A hsa, map_one]
  rw [h1, ← cfc_comp' Real.log (fun x : ℝ => 1 + x) A
    ((A.finite_real_spectrum.image _).continuousOn _) (hcont _) hsa]
  conv_rhs => rw [← cfc_id' ℝ A hsa]
  refine cfc_mono (fun x hx => ?_) (hcont _) (hcont _)
  have hx0 : (0 : ℝ) ≤ x := hA.spectrum_subset_Ici hx
  linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)]

/-! ### The trace exponential -/

/-- **The trace of the exponential** of a Hermitian matrix is the sum of the exponentials of its
eigenvalues. Port of `NLAlib.traceExp_smul_eq_sum`. -/
theorem _root_.Matrix.IsHermitian.re_trace_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (exp A).trace = ∑ i ∈ Finset.range (Fintype.card n), Real.exp (eigenvalue A i) := by
  rw [hA.exp_eq_cfc]
  exact hA.re_trace_cfc Real.exp

/-- The trace exponential of a Hermitian matrix of positive size is positive.
Port of `NLAlib.traceExp_pos_of_isHermitian`. -/
theorem _root_.Matrix.IsHermitian.re_trace_exp_pos [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : 0 < RCLike.re (exp A).trace := by
  rw [hA.re_trace_exp]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _)
    (Finset.nonempty_range_iff.mpr Fintype.card_ne_zero)

/-- **The largest eigenvalue is controlled by the trace exponential**: `exp(λ_0(A)) ≤ tr exp A`.
This is the first step of the matrix Laplace transform method.
[Tropp2015, Proposition 3.2.1].
Port of `NLAlib.exp_mul_lambdaMax_lambdaMin_le_traceExp_smul`. -/
theorem _root_.Matrix.IsHermitian.exp_eigenvalue_zero_le_re_trace_exp [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Real.exp (eigenvalue A 0) ≤ RCLike.re (exp A).trace := by
  rw [hA.exp_eq_cfc]
  exact hA.apply_eigenvalue_zero_le_re_trace_cfc fun x _ => (Real.exp_pos x).le

/-- The trace exponential is at most the dimension times the exponential of the largest
eigenvalue. Port of `NLAlib.traceExp_smul_le_mul_exp_mul_norm`, there with the norm. -/
theorem _root_.Matrix.IsHermitian.re_trace_exp_le_card_mul_exp {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    RCLike.re (exp A).trace ≤ Fintype.card n * Real.exp (eigenvalue A 0) := by
  rw [hA.re_trace_exp]
  have h := Finset.sum_le_card_nsmul (Finset.range (Fintype.card n))
    (fun i => Real.exp (eigenvalue A i)) (Real.exp (eigenvalue A 0)) fun i hi =>
      Real.exp_le_exp.mpr (hA.eigenvalue_le_eigenvalue (Nat.zero_le i) (Finset.mem_range.mp hi))
  rwa [Finset.card_range, nsmul_eq_mul] at h

/-- The trace exponential is invariant under unitary conjugation.
Port of `NLAlib.traceExp_unitary_conj`. -/
theorem re_trace_exp_mul_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n)
    (A : Matrix r r 𝕜) : RCLike.re (exp (U * A * Uᴴ)).trace = RCLike.re (exp A).trace := by
  rw [exp_mul_mul_conjTranspose hU hr, Matrix.trace_mul_cycle, hU.conjTranspose_mul_self,
    Matrix.one_mul]

/-- A scalar shift factors out of the trace exponential.
Port of `NLAlib.traceExp_add_smul_one_eq_exp_mul`. -/
theorem re_trace_exp_add_real_smul_one (A : Matrix n n 𝕜) (t : ℝ) :
    RCLike.re (exp (A + t • (1 : Matrix n n 𝕜))).trace = Real.exp t * RCLike.re (exp A).trace := by
  rw [exp_add_real_smul_one, Matrix.trace_smul, RCLike.smul_re]

/-- The trace exponential of a block diagonal matrix is the sum of the two.
Port of the block case used in `NLAlib.intrinsicDimension_fromBlocks`. -/
theorem re_trace_exp_fromBlocks_diagonal (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    RCLike.re (exp (Matrix.fromBlocks A 0 0 B)).trace =
      RCLike.re (exp A).trace + RCLike.re (exp B).trace := by
  rw [exp_fromBlocks_diagonal, ← map_add]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂]

/-- The trace exponential is continuous. Port of `NLAlib.continuous_traceExp`. -/
theorem continuous_re_trace_exp :
    Continuous fun A : Matrix n n 𝕜 => RCLike.re (exp A).trace := by
  have h : Continuous (exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  exact RCLike.continuous_re.comp h.matrix_trace

end NLAlib
