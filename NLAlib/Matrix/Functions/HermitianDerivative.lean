/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Polynomial
public import NLAlib.Matrix.Spectral.Weyl
public import NLAlib.Matrix.Spectral.SimpleSpectrum
public import NLAlib.Polynomial.Interpolation.Hermite
public import NLAlib.ForMathlib.Analysis.CStarAlgebra.Matrix
public import NLAlib.ForMathlib.Analysis.Calculus.FDeriv.Polynomial
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.Tactic.NoncommRing

/-!
# Derivatives of Hermitian matrix functions

Divided differences in a unitary eigenbasis describe the real Fréchet derivative within the
Hermitian matrices. Repeated nodes use the derivative of the scalar function.

## Main results

* `Matrix.IsHermitian.hasFDerivWithinAt_cfc`: the derivative along Hermitian matrices.
* `NLAlib.hasFDerivAt_cfc_subtype`: the derivative on the self-adjoint submodule.
-/

@[expose] public section

open Matrix Polynomial Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology RightActions
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

private noncomputable local instance : NormedAlgebra ℝ (Matrix n n 𝕜) :=
  Matrix.l2OpNormedAlgebraReal

/-- The confluent Löwner matrix on a finite family of real nodes. Mathlib's `dslope` gives
the derivative on repeated nodes and the secant slope on distinct nodes. [Tropp2022, §14]. -/
noncomputable def loewnerMatrix {ι : Type*} (f : ℝ → ℝ) (ev : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => dslope f (ev i) (ev j)

private theorem dslope_poly_add (p q : ℝ[X]) (x y : ℝ) :
    dslope (p + q).eval x y = dslope p.eval x y + dslope q.eval x y := by
  by_cases h : y = x
  · subst y
    rw [dslope_same, dslope_same, dslope_same, ((p + q).hasDerivAt x).deriv,
      (p.hasDerivAt x).deriv, (q.hasDerivAt x).deriv, derivative_add, eval_add]
  · simp only [dslope_of_ne _ h, slope, vsub_eq_sub, smul_eq_mul, Polynomial.eval_add]
    ring

private theorem dslope_poly_mul_X (p : ℝ[X]) (x y : ℝ) :
    dslope (p * X).eval x y = p.eval x + dslope p.eval x y * y := by
  by_cases h : y = x
  · subst y
    rw [dslope_same, dslope_same, (Polynomial.hasDerivAt (p * X : ℝ[X]) x).deriv,
      (p.hasDerivAt x).deriv]
    simp only [derivative_mul, derivative_X, eval_add, eval_mul, eval_X, mul_one, add_comm]
  · simp only [dslope_of_ne _ h, slope, vsub_eq_sub, smul_eq_mul, Polynomial.eval_mul,
      Polynomial.eval_X]
    field_simp [sub_ne_zero.mpr h]
    ring

private theorem dslope_poly_C (c x y : ℝ) : dslope (C c).eval x y = 0 := by
  by_cases h : y = x
  · subst y
    simp only [dslope_same, Polynomial.deriv, derivative_C, eval_zero]
  · simp [dslope_of_ne _ h, slope]

private theorem aevalFDeriv_diagonal_apply (p : ℝ[X]) (ev : n → ℝ) (H : Matrix n n 𝕜) :
    p.aevalFDeriv (diagonal (fun i => (ev i : 𝕜))) H =
      Matrix.of (fun i j => ((dslope p.eval (ev i) (ev j) : ℝ) : 𝕜) * H i j) := by
  induction p using Polynomial.induction_on with
  | C a =>
    ext i j
    simp only [Polynomial.aevalFDeriv_C, _root_.zero_apply, Matrix.zero_apply, Matrix.of_apply,
      dslope_poly_C, RCLike.ofReal_zero, zero_mul]
  | add p q hp hq =>
    rw [Polynomial.aevalFDeriv_add, _root_.add_apply, hp, hq]
    ext i j
    simp only [Matrix.add_apply, Matrix.of_apply, dslope_poly_add, RCLike.ofReal_add, add_mul]
  | monomial k a ih =>
    let p : ℝ[X] := C a * X ^ k
    have hpoly : C a * X ^ (k + 1) = p * X := by dsimp [p]; rw [pow_succ]; ring
    rw [hpoly, Polynomial.aevalFDeriv_mul, Polynomial.aevalFDeriv_X, Polynomial.aeval_X]
    change aeval (diagonal (fun i => (ev i : 𝕜))) p * H +
      p.aevalFDeriv (diagonal (fun i => (ev i : 𝕜))) H * diagonal (fun i => (ev i : 𝕜)) = _
    rw [ih, aeval_diagonal]
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply,
      dslope_poly_mul_X, RCLike.ofReal_add, RCLike.ofReal_mul]
    ring

/-- The real linear divided-difference operator in a supplied unitary
eigenbasis. It is defined on the ambient matrix space; its derivative
meaning is along the real subspace of Hermitian matrices. -/
noncomputable def loewnerDerivative (f : ℝ → ℝ) (ev : n → ℝ) (U : unitary (Matrix n n 𝕜)) :
    Matrix n n 𝕜 →L[ℝ] Matrix n n 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun H := (U : Matrix n n 𝕜) *
        ((loewnerMatrix f ev).map (RCLike.ofReal (K := 𝕜)) ⊙
          ((U : Matrix n n 𝕜)ᴴ * H * U)) * (U : Matrix n n 𝕜)ᴴ
      map_add' H K := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.hadamard_add]
      map_smul' c H := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.hadamard_smul, RingHom.id_apply] }

/-- Evaluation of the real linear Hadamard derivative operator. -/
theorem loewnerDerivative_apply (f : ℝ → ℝ) (ev : n → ℝ)
    (U : unitary (Matrix n n 𝕜)) (H : Matrix n n 𝕜) :
    loewnerDerivative f ev U H = (U : Matrix n n 𝕜) *
      ((loewnerMatrix f ev).map (RCLike.ofReal (K := 𝕜)) ⊙
        ((U : Matrix n n 𝕜)ᴴ * H * U)) * (U : Matrix n n 𝕜)ᴴ := rfl

/-- Polynomial derivatives equal their divided-difference operators in
every unitary eigenbasis, including repeated nodes. -/
private theorem aevalFDeriv_eq_loewnerDerivative (p : ℝ[X]) (ev : n → ℝ)
    (U : unitary (Matrix n n 𝕜)) {A : Matrix n n 𝕜}
    (hA : A = (U : Matrix n n 𝕜) * diagonal (fun i => (ev i : 𝕜)) *
      (U : Matrix n n 𝕜)ᴴ) : p.aevalFDeriv A = loewnerDerivative p.eval ev U := by
  let E := Unitary.conjStarAlgAut ℝ (Matrix n n 𝕜) U
  have hU : (U : Matrix n n 𝕜) * (U : Matrix n n 𝕜)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  apply ContinuousLinearMap.ext
  intro H
  let K := (U : Matrix n n 𝕜)ᴴ * H * U
  have hK : E K = H := by
    change (U : Matrix n n 𝕜) * ((U : Matrix n n 𝕜)ᴴ * H * U) *
      (U : Matrix n n 𝕜)ᴴ = H
    calc
      _ = ((U : Matrix n n 𝕜) * (U : Matrix n n 𝕜)ᴴ) * H *
        ((U : Matrix n n 𝕜) * (U : Matrix n n 𝕜)ᴴ) := by noncomm_ring
      _ = H := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  have hEA : E (diagonal (fun i => (ev i : 𝕜))) = A := hA.symm
  calc
    _ = E (p.aevalFDeriv (diagonal (fun i => (ev i : 𝕜))) K) := by
      have hm : E (p.aevalFDeriv (diagonal (fun i => (ev i : 𝕜))) K) =
          p.aevalFDeriv (E (diagonal (fun i => (ev i : 𝕜)))) (E K) :=
        Polynomial.map_aevalFDeriv_apply E.toAlgEquiv.toAlgHom p _ K
      rw [hEA, hK] at hm
      exact hm.symm
    _ = E (Matrix.of (fun i j =>
        (((dslope p.eval (ev i) (ev j)) : ℝ) : 𝕜) * K i j)) := by
      rw [aevalFDeriv_diagonal_apply]
    _ = _ := by
      rw [loewnerDerivative_apply]
      change (U : Matrix n n 𝕜) * _ * (U : Matrix n n 𝕜)ᴴ = _
      congr 2

/-- Matching scalar values and derivatives at the nodes gives the same
divided-difference operator, including confluent entries. -/
private theorem loewnerDerivative_eq_of_values_deriv (p : ℝ[X]) (f : ℝ → ℝ) (ev : n → ℝ)
    (U : unitary (Matrix n n 𝕜)) (hv : ∀ i, p.eval (ev i) = f (ev i))
    (hd : ∀ i, p.derivative.eval (ev i) = deriv f (ev i)) :
    loewnerDerivative p.eval ev U = loewnerDerivative f ev U := by
  have heq : loewnerMatrix p.eval ev = loewnerMatrix f ev := by
    ext i j
    change dslope p.eval (ev i) (ev j) = dslope f (ev i) (ev j)
    by_cases hij : ev i = ev j
    · rw [hij, dslope_same, dslope_same, (p.hasDerivAt (ev j)).deriv, hd]
    · rw [dslope_of_ne _ (Ne.symm hij), dslope_of_ne _ (Ne.symm hij)]
      simp only [slope, vsub_eq_sub, hv]
  ext H
  simp only [loewnerDerivative_apply, heq]


private theorem hasFDerivWithinAt_cfc_zero
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {g : ℝ → ℝ}
    (hg : ∀ i, g (hA.eigenvalues i) = 0)
    (hg' : ∀ i, HasDerivAt g 0 (hA.eigenvalues i)) :
    HasFDerivWithinAt (fun B : Matrix n n 𝕜 => cfc g B)
      (0 : Matrix n n 𝕜 →L[ℝ] Matrix n n 𝕜) {B | B.IsHermitian} A := by
  have hgA : cfc g A = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    apply norm_cfc_le le_rfl
    intro x hx
    obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
    simp only [hg i, norm_zero, le_refl]
  apply HasFDerivWithinAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hnear (i : n) : ∀ᶠ B : Matrix n n 𝕜 in 𝓝 A,
      ∀ x : ℝ, ‖x - hA.eigenvalues i‖ ≤ ‖B - A‖ →
        ‖g x‖ ≤ ε * ‖x - hA.eigenvalues i‖ := by
    have hs := (hg' i).isLittleO.bound hε
    simp only [hg i, smul_zero, sub_zero] at hs
    obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hs
    have hn : ∀ᶠ B : Matrix n n 𝕜 in 𝓝 A, ‖B - A‖ < δ := by
      have hc : ContinuousAt (fun B : Matrix n n 𝕜 => ‖B - A‖) A := by fun_prop
      have ht := hc.tendsto.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hδ))
      exact ht
    filter_upwards [hn] with B hB
    intro x hx
    exact hbound (by simpa only [dist_eq_norm] using hx.trans_lt hB)
  have hnearall : ∀ᶠ B : Matrix n n 𝕜 in 𝓝 A,
      ∀ i x, ‖x - hA.eigenvalues i‖ ≤ ‖B - A‖ →
        ‖g x‖ ≤ ε * ‖x - hA.eigenvalues i‖ := Filter.eventually_all.mpr hnear
  filter_upwards [hnearall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with B hB hherm
  simp only [hgA, sub_zero, _root_.zero_apply]
  apply norm_cfc_le (mul_nonneg hε.le (norm_nonneg _))
  intro x hx
  have hBH : B.IsHermitian := hherm
  obtain ⟨k, hk, rfl⟩ := hBH.spectrum_eq_image_eigenvalue ▸ hx
  obtain ⟨i, hi⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hA.eigenvalue_mem_spectrum hk
  have he := hBH.abs_eigenvalue_sub_le hA k
  rw [← hi] at he
  exact (hB i _ (by simpa only [Real.norm_eq_abs, specNorm_eq_norm] using he)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs, specNorm_eq_norm] using he) hε.le)

private theorem exists_aevalFDeriv_cfc
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, DifferentiableAt ℝ f (hA.eigenvalues i)) :
    ∃ p : ℝ[X], (∀ i, p.eval (hA.eigenvalues i) = f (hA.eigenvalues i)) ∧
      (∀ i, p.derivative.eval (hA.eigenvalues i) = deriv f (hA.eigenvalues i)) ∧
      HasFDerivWithinAt (fun B : Matrix n n 𝕜 => cfc f B)
        (p.aevalFDeriv A) {B | B.IsHermitian} A := by
  classical
  let s := Finset.univ.image hA.eigenvalues
  let m := s.val + s.val
  obtain ⟨p, _, hp⟩ := exists_degree_lt_forall_iterate_derivative_eval_eq m
    (fun x k => if k = 0 then f x else deriv f x)
  have hmem (i : n) : hA.eigenvalues i ∈ s :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hcnt (i : n) : 1 < m.count (hA.eigenvalues i) := by
    have h : 0 < s.val.count (hA.eigenvalues i) := Multiset.count_pos.mpr (hmem i)
    simp only [m, Multiset.count_add]
    omega
  have hm (i : n) : hA.eigenvalues i ∈ m := Multiset.count_pos.mp (by have := hcnt i; omega)
  have hv (i : n) : p.eval (hA.eigenvalues i) = f (hA.eigenvalues i) := by
    simpa using hp _ (hm i) 0 (by have := hcnt i; omega)
  have hd (i : n) : p.derivative.eval (hA.eigenvalues i) = deriv f (hA.eigenvalues i) := by
    simpa using hp _ (hm i) 1 (hcnt i)
  refine ⟨p, hv, hd, ?_⟩
  let g : ℝ → ℝ := fun x => f x - p.eval x
  have hg (i : n) : g (hA.eigenvalues i) = 0 := by dsimp [g]; rw [hv, sub_self]
  have hg' (i : n) : HasDerivAt g 0 (hA.eigenvalues i) := by
    have h := (hf i).hasDerivAt.sub (p.hasDerivAt (hA.eigenvalues i))
    convert! h using 1
    exact (sub_self _).symm.trans (congrArg (fun z => deriv f (hA.eigenvalues i) - z) (hd i).symm)
  have h := (hasFDerivWithinAt_cfc_zero hA hg hg').add
    (p.hasFDerivAt_aevalFDeriv A).hasFDerivWithinAt
  simp only [zero_add] at h
  have heq (B : Matrix n n 𝕜) (hB : B.IsHermitian) :
      cfc f B = cfc g B + aeval B p := by
    have hsub : cfc g B = cfc f B - cfc p.eval B :=
      cfc_sub f p.eval B (B.finite_real_spectrum.continuousOn f)
        (B.finite_real_spectrum.continuousOn p.eval)
    have hp : cfc p.eval B = aeval B p := cfc_polynomial p B hB
    calc
      _ = (cfc f B - cfc p.eval B) + cfc p.eval B := by abel
      _ = _ := by rw [← hsub, hp]
  exact h.congr (fun B hB => heq B hB) (heq A hA)


/-- The CFC has its divided-difference derivative along the Hermitian
subspace. Differentiability at just the finite spectrum is sufficient. -/
theorem _root_.Matrix.IsHermitian.hasFDerivWithinAt_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : ∀ i, DifferentiableAt ℝ f (hA.eigenvalues i))
    (ev : n → ℝ) (U : unitary (Matrix n n 𝕜))
    (hdiag : A = (U : Matrix n n 𝕜) * diagonal (fun i => (ev i : 𝕜)) *
      (U : Matrix n n 𝕜)ᴴ) :
    HasFDerivWithinAt (fun B : Matrix n n 𝕜 => cfc f B)
      (loewnerDerivative f ev U) {B | B.IsHermitian} A := by
  obtain ⟨p, hv, hd, hp⟩ := exists_aevalFDeriv_cfc hA hf
  have hnodes (i : n) : ∃ j, hA.eigenvalues j = ev i := by
    have hi := mem_spectrum_of_eq_mul_diagonal_mul_conjTranspose ev U hdiag i
    rwa [hA.spectrum_real_eq_range_eigenvalues] at hi
  have hv' (i : n) : p.eval (ev i) = f (ev i) := by
    obtain ⟨j, hj⟩ := hnodes i
    rw [← hj]
    exact hv j
  have hd' (i : n) : p.derivative.eval (ev i) = deriv f (ev i) := by
    obtain ⟨j, hj⟩ := hnodes i
    rw [← hj]
    exact hd j
  rw [aevalFDeriv_eq_loewnerDerivative p ev U hdiag,
    loewnerDerivative_eq_of_values_deriv p f ev U hv' hd'] at hp
  exact hp

/-- **Daleckii–Krein derivative.** The real Fréchet derivative on the Hermitian
matrix space is the conjugated divided-difference Hadamard operator.
Differentiability at each eigenvalue is enough, hence in particular the
continuously differentiable hypothesis on any open spectral interval is sufficient.
The supplied unitary basis need not order or separate repeated eigenvalues.
[Tropp2022, Theorem 14.13].
Result: matrix-function-frechet-divided-difference -/
theorem hasFDerivAt_cfc_subtype
    (A : selfAdjoint.submodule ℝ (Matrix n n 𝕜)) {f : ℝ → ℝ}
    (hf : ∀ x ∈ spectrum ℝ (A : Matrix n n 𝕜), DifferentiableAt ℝ f x)
    (ev : n → ℝ) (U : unitary (Matrix n n 𝕜))
    (hdiag : (A : Matrix n n 𝕜) = (U : Matrix n n 𝕜) * diagonal (fun i => (ev i : 𝕜)) *
      (U : Matrix n n 𝕜)ᴴ) :
    HasFDerivAt (fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) => cfc f (B : Matrix n n 𝕜))
      ((loewnerDerivative f ev U).comp (selfAdjoint.submodule ℝ (Matrix n n 𝕜)).subtypeL) A := by
  have hA : (A : Matrix n n 𝕜).IsHermitian := A.property
  have h := hA.hasFDerivWithinAt_cfc
    (fun i => hf _ (hA.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)) ev U hdiag
  exact h.comp_hasFDerivAt A (selfAdjoint.submodule ℝ (Matrix n n 𝕜)).subtypeL.hasFDerivAt
    (Filter.Eventually.of_forall fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) => B.property)


end NLAlib
