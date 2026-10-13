/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import NLAlib.Matrix.Functions.OperatorConvex
public import NLAlib.Matrix.Functions.Perspective
public import NLAlib.Matrix.Functions.TraceFunctions

/-!
# Lieb's concavity theorem

For a fixed Hermitian `H`, the function `A ↦ tr exp (H + log A)` is concave on positive definite
matrices. This is the theorem behind Tropp's master inequality for sums of independent random
matrices. The proof follows Tropp: the relative entropy
`D(A; H) = tr (A (log A - log H) - (A - H))` is nonnegative (Klein) and jointly convex (through
the operator convexity of the matrix perspective), and `tr exp (H + log A)` is a partial maximum
of an affine function minus a relative entropy.

## Main definitions

* `NLAlib.relativeEntropy`: the matrix relative entropy `tr (A (log A - log H) - (A - H))`.

## Main results

* `NLAlib.relativeEntropy_nonneg`: nonnegativity.
* `NLAlib.convexOn_relativeEntropy`: joint convexity.
* `NLAlib.isGreatest_re_trace_mul_cfc_log_sub`, `NLAlib.isGreatest_re_trace_exp_add_cfc_log`: the
  variational formulas for `tr M` and `tr exp (H + log A)`.
* `NLAlib.concaveOn_re_trace_exp_add_cfc_log`: Lieb's theorem.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **matrix relative entropy** of two positive definite matrices,
`D(A; H) = tr (A (log A - log H) - (A - H))`: the Bregman divergence of `A ↦ tr (A log A - A)`.
[Tropp2015, Definition 8.3.1]. Port of `NLAlib.relativeEntropy`. -/
noncomputable def relativeEntropy (A H : Matrix n n 𝕜) : ℝ :=
  RCLike.re (A * (cfc Real.log A - cfc Real.log H) - (A - H)).trace

/-- The relative entropy of a matrix with itself vanishes. -/
@[simp]
theorem relativeEntropy_self (A : Matrix n n 𝕜) : relativeEntropy A A = 0 := by
  rw [relativeEntropy, sub_self, sub_self, Matrix.mul_zero, sub_zero, Matrix.trace_zero, map_zero]

/-- `A log A` as a function of `A`. -/
private theorem cfc_mul_log {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    cfc (fun x : ℝ => x * Real.log x) A = A * cfc Real.log A := by
  rw [cfc_mul (fun x : ℝ => x) Real.log A (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _), cfc_id' ℝ A hA.isSelfAdjoint]

/-- The relative entropy as a combination of four traces. -/
private theorem relativeEntropy_eq (A H : Matrix n n 𝕜) :
    relativeEntropy A H = RCLike.re (A * cfc Real.log A).trace -
      RCLike.re (A * cfc Real.log H).trace - RCLike.re A.trace + RCLike.re H.trace := by
  rw [relativeEntropy, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    map_sub, map_sub, map_sub]
  ring

/-- **The matrix relative entropy is nonnegative** (Klein's inequality).
[Tropp2015, Proposition 8.3.5]. Port of `NLAlib.relativeEntropy_nonneg`, there over `ℂ`.
Result: relative-entropy -/
theorem relativeEntropy_nonneg {A H : Matrix n n 𝕜} (hA : A.PosDef) (hH : H.PosDef) :
    0 ≤ relativeEntropy A H := by
  have hconv : ConvexOn ℝ (Set.Ioi 0) fun x : ℝ => x * Real.log x - x :=
    (Real.convexOn_mul_log.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).sub
      (concaveOn_id (convex_Ioi 0))
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun x : ℝ => x * Real.log x - x) (Real.log x) (Set.Ioi 0) x :=
    fun x hx => by
      have h := (Real.hasDerivAt_mul_log (ne_of_gt hx)).sub (hasDerivAt_id' x)
      rw [add_sub_cancel_right] at h
      exact h.hasDerivWithinAt
  have hcfc : ∀ X : Matrix n n 𝕜, X.IsHermitian →
      cfc (fun x : ℝ => x * Real.log x - x) X = X * cfc Real.log X - X := fun X hX => by
    rw [cfc_sub (fun x : ℝ => x * Real.log x) (fun x : ℝ => x) X
      (X.finite_real_spectrum.continuousOn _) (X.finite_real_spectrum.continuousOn _),
      cfc_mul_log hX, cfc_id' ℝ X hX.isSelfAdjoint]
  have h := re_trace_mul_cfc_le_re_trace_cfc_sub hconv hderiv hA.isHermitian hH.isHermitian
    hA.spectrum_subset_Ioi hH.spectrum_subset_Ioi
  rw [hcfc A hA.isHermitian, hcfc H hH.isHermitian, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_sub, map_sub, map_sub, map_sub] at h
  rw [relativeEntropy_eq]
  linarith

/-! ### Joint convexity

`D(A; H) = ⟨vec 1, ψ(A ⊗ 1, 1 ⊗ Hᵀ) vec 1⟩ - tr (A - H)` for the perspective `ψ` of `-log`: the
Kronecker factors commute, are linear in `A` and `H`, and the perspective is jointly operator
convex. -/

omit [Fintype n] [DecidableEq n] in
/-- Convex combinations of positive definite matrices are positive definite. -/
private theorem posDef_smul_add_smul {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : (a • A + b • B).PosDef := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    rwa [hab, zero_smul, zero_add, one_smul]
  · exact (hA.smul ha').add_posSemidef (hB.posSemidef.smul hb)

/-- The quadratic form of a matrix on `n × n` at the vectorised identity. -/
private noncomputable def kroneckerContraction (M : Matrix (n × n) (n × n) 𝕜) : ℝ :=
  RCLike.re (quadForm M fun p => if p.1 = p.2 then 1 else 0)

/-- The contraction of `X ⊗ Yᵀ` is `tr (X Y)`. -/
private theorem kroneckerContraction_kronecker_transpose (X Y : Matrix n n 𝕜) :
    kroneckerContraction (X ⊗ₖ Yᵀ) = RCLike.re (X * Y).trace := by
  rw [kroneckerContraction, quadForm_eq_sum]
  congr 1
  simp only [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.transpose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, apply_ite, star_one, star_zero, ite_mul,
    one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

private theorem kroneckerContraction_sub (M N : Matrix (n × n) (n × n) 𝕜) :
    kroneckerContraction (M - N) = kroneckerContraction M - kroneckerContraction N := by
  rw [kroneckerContraction, quadForm_sub_left, map_sub]
  rfl

private theorem kroneckerContraction_smul_add_smul (a b : ℝ) (M N : Matrix (n × n) (n × n) 𝕜) :
    kroneckerContraction (a • M + b • N) =
      a * kroneckerContraction M + b * kroneckerContraction N := by
  rw [kroneckerContraction, quadForm_add_left, RCLike.real_smul_eq_coe_smul (K := 𝕜) a,
    RCLike.real_smul_eq_coe_smul (K := 𝕜) b, quadForm_smul_left, quadForm_smul_left, map_add,
    RCLike.re_ofReal_mul, RCLike.re_ofReal_mul]
  rfl

private theorem kroneckerContraction_mono {M N : Matrix (n × n) (n × n) 𝕜} (h : M ≤ N) :
    kroneckerContraction M ≤ kroneckerContraction N :=
  re_quadForm_le_re_quadForm_of_le h _

omit [Fintype n] [DecidableEq n] in
/-- The Kronecker product of two diagonalised matrices. -/
private theorem kronecker_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    (U V : Matrix n r 𝕜) (x y : r → ℝ) :
    (U * Matrix.diagonal (fun i => ((x i : ℝ) : 𝕜)) * Uᴴ) ⊗ₖ
        (V * Matrix.diagonal (fun i => ((y i : ℝ) : 𝕜)) * Vᴴ) =
      (U ⊗ₖ V) * Matrix.diagonal (fun p : r × r => ((x p.1 * y p.2 : ℝ) : 𝕜)) * (U ⊗ₖ V)ᴴ := by
  rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
    Matrix.diagonal_kronecker_diagonal]
  simp only [RCLike.ofReal_mul]

omit [Fintype n] [DecidableEq n] in
/-- The transpose of a diagonalised matrix is diagonalised by the conjugate frame. -/
private theorem transpose_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    (V : Matrix n r 𝕜) (d : r → 𝕜) :
    (V * Matrix.diagonal d * Vᴴ)ᵀ = Vᵀᴴ * Matrix.diagonal d * (Vᵀᴴ)ᴴ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rfl

/-- The perspective of `-log` at the commuting pair `A ⊗ 1`, `1 ⊗ Hᵀ`. -/
private theorem matrixPerspective_neg_log_kronecker {A H : Matrix n n 𝕜} (hA : A.PosDef)
    (hH : H.PosDef) :
    matrixPerspective (fun x : ℝ => -Real.log x) (A ⊗ₖ (1 : Matrix n n 𝕜))
        ((1 : Matrix n n 𝕜) ⊗ₖ Hᵀ) =
      (A * cfc Real.log A) ⊗ₖ (1 : Matrix n n 𝕜) - A ⊗ₖ (cfc Real.log H)ᵀ := by
  obtain ⟨U, hU, hAU⟩ := hA.isHermitian.exists_eq_mul_diagonal_mul_conjTranspose
  obtain ⟨V, hV, hHV⟩ := hH.isHermitian.exists_eq_mul_diagonal_mul_conjTranspose
  have hc : Fintype.card (Fin (Fintype.card n)) = Fintype.card n := Fintype.card_fin _
  have ha : ∀ i : Fin (Fintype.card n), 0 < eigenvalue A i := fun i =>
    hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA i i.2
  have hh : ∀ i : Fin (Fintype.card n), 0 < eigenvalue H i := fun i =>
    hH.isHermitian.posDef_iff_eigenvalue_pos.mp hH i i.2
  have hV' : HasOrthonormalCols Vᵀᴴ := by
    have h := congrArg Matrix.transpose (hV.mul_conjTranspose_self_of_card_eq hc.symm)
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h
    rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mul_eq_one_comm_of_card_eq _ _ 𝕜 hc.symm).mp h
  have hone : ∀ W : Matrix n (Fin (Fintype.card n)) 𝕜, HasOrthonormalCols W →
      (1 : Matrix n n 𝕜) = W * Matrix.diagonal (fun _ => ((1 : ℝ) : 𝕜)) * Wᴴ := fun W hW => by
    rw [RCLike.ofReal_one, Matrix.diagonal_one, Matrix.mul_one,
      hW.mul_conjTranspose_self_of_card_eq hc.symm]
  have hHt : Hᵀ = Vᵀᴴ * Matrix.diagonal (fun i : Fin (Fintype.card n) =>
      ((eigenvalue H i : ℝ) : 𝕜)) * (Vᵀᴴ)ᴴ :=
    (congrArg Matrix.transpose hHV).trans (transpose_mul_diagonal_mul_conjTranspose V _)
  have hW : HasOrthonormalCols (U ⊗ₖ Vᵀᴴ) := by
    rw [HasOrthonormalCols, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hU.conjTranspose_mul_self, hV'.conjTranspose_mul_self, Matrix.one_kronecker_one]
  have hrW : Fintype.card (Fin (Fintype.card n) × Fin (Fintype.card n)) =
      Fintype.card (n × n) := by
    rw [Fintype.card_prod, Fintype.card_prod, hc]
  have hL : A ⊗ₖ (1 : Matrix n n 𝕜) = (U ⊗ₖ Vᵀᴴ) * Matrix.diagonal
      (fun p : Fin (Fintype.card n) × Fin (Fintype.card n) =>
        ((eigenvalue A p.1 * 1 : ℝ) : 𝕜)) * (U ⊗ₖ Vᵀᴴ)ᴴ := by
    rw [← kronecker_mul_diagonal_mul_conjTranspose U Vᵀᴴ (fun i => eigenvalue A i) fun _ => 1,
      ← hone _ hV', ← hAU]
  have hR : (1 : Matrix n n 𝕜) ⊗ₖ Hᵀ = (U ⊗ₖ Vᵀᴴ) * Matrix.diagonal
      (fun p : Fin (Fintype.card n) × Fin (Fintype.card n) =>
        ((1 * eigenvalue H p.2 : ℝ) : 𝕜)) * (U ⊗ₖ Vᵀᴴ)ᴴ := by
    rw [← kronecker_mul_diagonal_mul_conjTranspose U Vᵀᴴ (fun _ => 1) fun i => eigenvalue H i,
      ← hone _ hU, ← hHt]
  have h1 : (A * cfc Real.log A) ⊗ₖ (1 : Matrix n n 𝕜) = (U ⊗ₖ Vᵀᴴ) * Matrix.diagonal
      (fun p : Fin (Fintype.card n) × Fin (Fintype.card n) =>
        ((eigenvalue A p.1 * Real.log (eigenvalue A p.1) * 1 : ℝ) : 𝕜)) * (U ⊗ₖ Vᵀᴴ)ᴴ := by
    rw [← kronecker_mul_diagonal_mul_conjTranspose U Vᵀᴴ
      (fun i => eigenvalue A i * Real.log (eigenvalue A i)) fun _ => 1, ← hone _ hV',
      ← cfc_mul_log hA.isHermitian, cfc_eq_mul_diagonal_mul_conjTranspose hU hc hAU]
  have h2 : A ⊗ₖ (cfc Real.log H)ᵀ = (U ⊗ₖ Vᵀᴴ) * Matrix.diagonal
      (fun p : Fin (Fintype.card n) × Fin (Fintype.card n) =>
        ((eigenvalue A p.1 * Real.log (eigenvalue H p.2) : ℝ) : 𝕜)) * (U ⊗ₖ Vᵀᴴ)ᴴ := by
    rw [← kronecker_mul_diagonal_mul_conjTranspose U Vᵀᴴ (fun i => eigenvalue A i)
      fun i => Real.log (eigenvalue H i), ← hAU, ← transpose_mul_diagonal_mul_conjTranspose,
      ← cfc_eq_mul_diagonal_mul_conjTranspose hV hc hHV]
  rw [hL, hR, h1, h2, matrixPerspective_mul_diagonal_mul_conjTranspose hW hrW _
    (fun p => by rw [mul_one]; exact ha p.1), ← Matrix.sub_mul, ← Matrix.mul_sub,
    Matrix.diagonal_sub]
  congr 3
  funext p
  rw [← RCLike.ofReal_sub, mul_one, one_mul, mul_one,
    Real.log_div (hh p.2).ne' (ha p.1).ne']
  congr 1
  ring

/-- The relative entropy through the perspective of `-log` at `A ⊗ 1` and `1 ⊗ Hᵀ`.
[Tropp2015, (8.8.1)]. -/
private theorem relativeEntropy_eq_kroneckerContraction {A H : Matrix n n 𝕜} (hA : A.PosDef)
    (hH : H.PosDef) :
    relativeEntropy A H = kroneckerContraction (matrixPerspective (fun x : ℝ => -Real.log x)
      (A ⊗ₖ (1 : Matrix n n 𝕜)) ((1 : Matrix n n 𝕜) ⊗ₖ Hᵀ)) - RCLike.re (A - H).trace := by
  have h := kroneckerContraction_kronecker_transpose (A * cfc Real.log A) 1
  rw [Matrix.transpose_one, Matrix.mul_one] at h
  rw [matrixPerspective_neg_log_kronecker hA hH, kroneckerContraction_sub, h,
    kroneckerContraction_kronecker_transpose, relativeEntropy_eq, Matrix.trace_sub, map_sub]
  ring

/-- **The matrix relative entropy is jointly convex** (Lindblad).
[Tropp2015, §8.3 and §8.8]; [Lindblad1974].
Port of `NLAlib.convexOn_relativeEntropy`, there over `ℂ` on `Fin d`.
Result: relative-entropy -/
theorem convexOn_relativeEntropy :
    ConvexOn ℝ {P : Matrix n n 𝕜 × Matrix n n 𝕜 | P.1.PosDef ∧ P.2.PosDef}
      fun P => relativeEntropy P.1 P.2 := by
  refine ⟨fun P hP Q hQ a b ha hb hab => ⟨posDef_smul_add_smul hP.1 hQ.1 ha hb hab,
    posDef_smul_add_smul hP.2 hQ.2 ha hb hab⟩, fun P hP Q hQ a b ha hb hab => ?_⟩
  have hL : ∀ X : Matrix n n 𝕜, X.PosDef → (X ⊗ₖ (1 : Matrix n n 𝕜)).PosDef := fun X hX =>
    hX.kronecker Matrix.PosDef.one
  have hR : ∀ X : Matrix n n 𝕜, X.PosDef → ((1 : Matrix n n 𝕜) ⊗ₖ Xᵀ).PosDef := fun X hX =>
    Matrix.PosDef.one.kronecker hX.transpose
  have h := kroneckerContraction_mono
    (operatorConvexOn_neg_log.matrixPerspective_smul_add_smul_le (hL _ hP.1) (hL _ hQ.1)
      (hR _ hP.2) (hR _ hQ.2) ha hb hab)
  rw [kroneckerContraction_smul_add_smul, ← Matrix.smul_kronecker, ← Matrix.smul_kronecker,
    ← Matrix.add_kronecker, ← Matrix.kronecker_smul, ← Matrix.kronecker_smul,
    ← Matrix.kronecker_add, ← Matrix.transpose_smul, ← Matrix.transpose_smul,
    ← Matrix.transpose_add] at h
  have ht : RCLike.re (a • P.1 + b • Q.1 - (a • P.2 + b • Q.2)).trace =
      a * RCLike.re (P.1 - P.2).trace + b * RCLike.re (Q.1 - Q.2).trace := by
    simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, map_sub, map_add,
      RCLike.smul_re]
    ring
  change relativeEntropy (a • P.1 + b • Q.1) (a • P.2 + b • Q.2) ≤
    a * relativeEntropy P.1 P.2 + b * relativeEntropy Q.1 Q.2
  rw [relativeEntropy_eq_kroneckerContraction (posDef_smul_add_smul hP.1 hQ.1 ha hb hab)
    (posDef_smul_add_smul hP.2 hQ.2 ha hb hab), relativeEntropy_eq_kroneckerContraction hP.1 hP.2,
    relativeEntropy_eq_kroneckerContraction hQ.1 hQ.2, ht]
  linarith

/-! ### The variational formulas and Lieb's theorem -/

/-- **A variational formula for the trace.** For positive definite `M`,
`tr M = max_T tr (T log M - T log T + T)` over positive definite `T`.
[Tropp2015, §8.3]. Port of `NLAlib.isGreatest_variational_trace`. -/
theorem isGreatest_re_trace_mul_cfc_log_sub {M : Matrix n n 𝕜} (hM : M.PosDef) :
    IsGreatest
      ((fun T : Matrix n n 𝕜 =>
        RCLike.re (T * cfc Real.log M - T * cfc Real.log T + T).trace) '' {T | T.PosDef})
      (RCLike.re M.trace) := by
  refine ⟨⟨M, hM, ?_⟩, ?_⟩
  · change RCLike.re (M * cfc Real.log M - M * cfc Real.log M + M).trace = RCLike.re M.trace
    rw [sub_self, zero_add]
  · rintro _ ⟨T, hT, rfl⟩
    have h := relativeEntropy_nonneg hT hM
    rw [relativeEntropy_eq] at h
    change RCLike.re (T * cfc Real.log M - T * cfc Real.log T + T).trace ≤ RCLike.re M.trace
    rw [Matrix.trace_add, Matrix.trace_sub, map_add, map_sub]
    linarith

/-- **The variational formula behind Lieb's theorem**: for Hermitian `H`,
`tr exp (H + log A) = max_T [tr (T H) + tr A - D(T; A)]` over positive definite `T`. The formula
needs no hypothesis on `A`; it is used for positive definite `A`.
[Tropp2015, §8.3].
Port of `NLAlib.isGreatest_variational_traceExp`, there over `ℂ` on `Fin d`. -/
theorem isGreatest_re_trace_exp_add_cfc_log {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (A : Matrix n n 𝕜) :
    IsGreatest
      ((fun T : Matrix n n 𝕜 =>
        RCLike.re (T * H).trace + RCLike.re A.trace - relativeEntropy T A) '' {T | T.PosDef})
      (RCLike.re (exp (H + cfc Real.log A)).trace) := by
  have hX : (H + cfc Real.log A).IsHermitian :=
    hH.add (cfc_predicate Real.log A : IsSelfAdjoint _)
  have hVar := isGreatest_re_trace_mul_cfc_log_sub hX.posDef_exp
  rw [hX.cfc_log_exp] at hVar
  have score : (fun T : Matrix n n 𝕜 =>
      RCLike.re (T * (H + cfc Real.log A) - T * cfc Real.log T + T).trace) =
        fun T => RCLike.re (T * H).trace + RCLike.re A.trace - relativeEntropy T A :=
    funext fun T => by
      rw [relativeEntropy_eq, Matrix.mul_add, Matrix.trace_add, Matrix.trace_sub,
        Matrix.trace_add, map_add, map_sub, map_add]
      ring
  rwa [score] at hVar

/-- **Lieb's concavity theorem.** For a fixed Hermitian `H`, `A ↦ tr exp (H + log A)` is concave
on the positive definite matrices.
[Lieb1973]; [Tropp2015, Theorem 8.1.1].
Port of `NLAlib.lieb_concavity`, there over `ℂ`.
Result: lieb-concavity -/
theorem concaveOn_re_trace_exp_add_cfc_log {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      fun A => RCLike.re (exp (H + cfc Real.log A)).trace := by
  have hc : Convex ℝ {A : Matrix n n 𝕜 | A.PosDef} := fun A hA B hB a b ha hb hab =>
    posDef_smul_add_smul hA hB ha hb hab
  refine ⟨hc, fun A hA B hB a b ha hb hab => ?_⟩
  obtain ⟨T, hT, hTA⟩ := (isGreatest_re_trace_exp_add_cfc_log hH A).1
  obtain ⟨S, hS, hSB⟩ := (isGreatest_re_trace_exp_add_cfc_log hH B).1
  have hent : relativeEntropy (a • T + b • S) (a • A + b • B) ≤
      a * relativeEntropy T A + b * relativeEntropy S B :=
    convexOn_relativeEntropy.2 (show (T, A) ∈ _ from ⟨hT, hA⟩) (show (S, B) ∈ _ from ⟨hS, hB⟩)
      ha hb hab
  have hmax : RCLike.re ((a • T + b • S) * H).trace + RCLike.re (a • A + b • B).trace -
      relativeEntropy (a • T + b • S) (a • A + b • B) ≤
        RCLike.re (exp (H + cfc Real.log (a • A + b • B))).trace :=
    (isGreatest_re_trace_exp_add_cfc_log hH (a • A + b • B)).2
      ⟨a • T + b • S, hc hT hS ha hb hab, rfl⟩
  have htr : ∀ C D : Matrix n n 𝕜, RCLike.re (a • C + b • D).trace =
      a * RCLike.re C.trace + b * RCLike.re D.trace := fun C D => by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, map_add, RCLike.smul_re,
      RCLike.smul_re]
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, htr, htr] at hmax
  change a * RCLike.re (exp (H + cfc Real.log A)).trace +
    b * RCLike.re (exp (H + cfc Real.log B)).trace ≤
      RCLike.re (exp (H + cfc Real.log (a • A + b • B))).trace
  rw [← hTA, ← hSB]
  linarith

end NLAlib
