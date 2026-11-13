/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Asymptotics.Lemmas
public import NLAlib.Matrix.Spectral.EigenvalueListing

/-!
# Analytic branches of simple matrix eigenvalues

A one-dimensional Schur complement selects an analytic eigenvalue of a diagonal pencil
through an isolated diagonal entry and gives its derivative there.

## Main results

* `NLAlib.exists_analytic_eigenvalue_branch_diagonal_expansion`.
-/

@[expose] public section

section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [DecidableEq n] {K : Type*} [Zero K]

/-- Any perturbation matrix decomposes into its leading scalar, row, column and trailing block in
the isolated-coordinate split. [HornJohnson2013, Theorem 6.3.12]. -/
private theorem submatrix_eq_fromBlocks_scalar_row_col (F : Matrix n n K) (i : n) :
    F.submatrix (Equiv.sumCompl (fun j => j = i)) (Equiv.sumCompl (fun j => j = i)) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : {j : n // j = i} => F i i))
        (Matrix.replicateRow {j : n // j = i} (fun j : {j : n // j ≠ i} => F i j.val))
        (Matrix.replicateCol {j : n // j = i} (fun j : {j : n // j ≠ i} => F j.val i))
        (F.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  classical
  let : Unique {j : n // j = i} := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change F a.val b.val = Matrix.diagonal (fun _ : {j : n // j = i} => F i i) a b
      rw [a.property, b.property]
      simp only [Matrix.diagonal_apply, Subsingleton.elim a b, ite_true]
    | inr b =>
      change F a.val b.val = F i b.val
      rw [a.property]
  | inr a =>
    cases b with
    | inl b =>
      change F a.val b.val = F a.val i
      rw [b.property]
    | inr b => rfl

end NLAlib

end

section

open Filter

open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The scalar row/resolvent/column coupling as a continuous linear map on matrices.
[HornJohnson2013, Theorem 6.3.12]. -/
private noncomputable def schurResolventCoupling (b c : n → ℂ) : Matrix n n ℂ →L[ℂ] ℂ :=
  ({ toFun M := b ⬝ᵥ (M *ᵥ c)
     map_add' M N := by rw [Matrix.add_mulVec, dotProduct_add]
     map_smul' a M := by rw [Matrix.smul_mulVec, dotProduct_smul]; rfl } :
      Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

/-- The scalar Schur-complement eigenvalue equation, with `s` measuring the eigenvalue shift and
`t` the perturbation parameter. [HornJohnson2013, Theorem 6.3.12]. -/
private noncomputable def simpleEigenvalueSchurFunction (μ a : ℂ) (B F : Matrix n n ℂ) (b c : n → ℂ)
    (p : ℂ × ℂ) : ℂ :=
  p.2 - p.1 * a - p.1 ^ 2 * schurResolventCoupling b c
    (Ring.inverse ((μ + p.2) • 1 - B - p.1 • F))

open scoped Matrix.Norms.L2Operator in
/-- The scalar Schur equation has the expected strict derivative at the origin whenever the
remaining block excludes the original eigenvalue. [HornJohnson2013, Theorem 6.3.12]. -/
private theorem hasStrictFDerivAt_simpleEigenvalueSchurFunction (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    HasStrictFDerivAt (simpleEigenvalueSchurFunction μ a B F b c)
      (ContinuousLinearMap.snd ℂ ℂ ℂ - a • ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := by
  let K₀ : Matrix n n ℂ := μ • 1 - B
  let L : (ℂ × ℂ) →L[ℂ] Matrix n n ℂ :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight 1 -
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight F
  have hK₀ : IsUnit K₀ := by
    simpa only [K₀, Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hμ
  have hKfun : (fun p : ℂ × ℂ => (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) =
      (fun p => K₀ + L p) := by
    funext p
    change (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F =
      (μ • 1 - B) + (p.2 • 1 - p.1 • F)
    rw [add_smul]
    abel
  have hK : HasStrictFDerivAt (fun p : ℂ × ℂ => K₀ + L p) L 0 :=
    HasStrictFDerivAt.const_add K₀ L.hasStrictFDerivAt
  have hInv : HasStrictFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) ↑hK₀.unit⁻¹ ↑hK₀.unit⁻¹) K₀ := by
    simpa only [hK₀.unit_spec] using hasStrictFDerivAt_ringInverse (𝕜 := ℂ) hK₀.unit
  have hInv' : HasStrictFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) ↑hK₀.unit⁻¹ ↑hK₀.unit⁻¹)
        (K₀ + L (0 : ℂ × ℂ)) := by
    simpa only [map_zero, add_zero] using hInv
  have hQ := (schurResolventCoupling b c).hasStrictFDerivAt.comp 0 (hInv'.comp 0 hK)
  have hfst : HasStrictFDerivAt (fun p : ℂ × ℂ => p.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun p : ℂ × ℂ => p.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := hasStrictFDerivAt_snd
  have hsq : HasStrictFDerivAt (fun p : ℂ × ℂ => p.1 ^ 2)
      (0 : (ℂ × ℂ) →L[ℂ] ℂ) 0 := by
    convert! hfst.mul hfst using 1 <;> first
    | rfl
    | (apply ContinuousLinearMap.ext; intro p
       change (0 : ℂ) = (0 : ℂ) * p.1 + (0 : ℂ) * p.1
       simp)
    | (funext p; simp [pow_two])
  have hquad := hsq.mul hQ
  have hbase' : HasStrictFDerivAt (fun p : ℂ × ℂ => p.2 - p.1 * a)
      (ContinuousLinearMap.snd ℂ ℂ ℂ - a • ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := by
    exact hsnd.sub (hfst.mul_const a)
  have h := hbase'.sub hquad
  have hKval (p : ℂ × ℂ) := congrFun hKfun p
  convert! h using 1 <;> first
  | rfl
  | (apply ContinuousLinearMap.ext; intro p
     simp only [ContinuousLinearMap.comp_apply, smul_apply, add_apply, sub_apply]
     change p.2 - a * p.1 = (p.2 - a * p.1) -
       ((0 : ℂ) ^ 2 * _ + _ * (0 : ℂ))
     simp)
  | (funext p; simp [simpleEigenvalueSchurFunction, hKval, pow_two])

end NLAlib

end

section

open scoped Matrix

namespace NLAlib

/-- The scalar Schur function is the determinant factor in the separated scalar/block eigenvalue
pencil. Arbitrary finite trailing indices, including empty blocks, are allowed. Horn–Johnson 2013,
Theorem 6.3.12; supports `simple-eigenvalue-perturbation`. [HornJohnson2013, Theorem 6.3.12]. -/
private theorem det_scalar_block_eigenvalue_pencil_eq_schur
    {l n : Type*} [Unique l] [Fintype n] [DecidableEq n]
    (μ a t s : ℂ) (B F : Matrix n n ℂ) (b c : n → ℂ)
    (hK : IsUnit ((μ + s) • (1 : Matrix n n ℂ) - B - t • F)) :
    (((μ + s) • (1 : Matrix (l ⊕ n) (l ⊕ n) ℂ) -
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
        t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
          (Matrix.replicateRow l b) (Matrix.replicateCol l c) F))).det =
      ((μ + s) • (1 : Matrix n n ℂ) - B - t • F).det *
        simpleEigenvalueSchurFunction μ a B F b c (t, s) := by
  let K := (μ + s) • (1 : Matrix n n ℂ) - B - t • F
  let := hK.nonempty_invertible.some
  have hBlocks : ((μ + s) • (1 : Matrix (l ⊕ n) (l ⊕ n) ℂ) -
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
        t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
          (Matrix.replicateRow l b) (Matrix.replicateCol l c) F)) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : l => s - t * a))
        (-(t • Matrix.replicateRow l b)) (-(t • Matrix.replicateCol l c)) K := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply, K] <;>
      split_ifs <;> ring
  rw [hBlocks, Matrix.det_fromBlocks₂₂]
  congr 1
  rw [Matrix.det_unique, Matrix.invOf_eq_nonsing_inv, Matrix.nonsing_inv_eq_ringInverse]
  simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.smul_mul, Matrix.mul_smul, smul_neg, neg_neg, smul_smul,
    Matrix.smul_apply, smul_eq_mul]
  change s - t * a - (t * t) *
    ((Matrix.replicateRow l b * Ring.inverse K * Matrix.replicateCol l c) default default) =
      s - t * a - t ^ 2 * (b ⬝ᵥ (Ring.inverse K *ᵥ c))
  have hCouple : ((Matrix.replicateRow l b * Ring.inverse K *
      Matrix.replicateCol l c) default default) = b ⬝ᵥ (Ring.inverse K *ᵥ c) := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply,
      dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hCouple, pow_two]

open scoped Matrix.Norms.L2Operator in
/-- Under invertibility of the trailing pencil block, a spectral point of the perturbed
scalar/block matrix is exactly a zero of the scalar Schur function. One common arbitrary finite
trailing type is used throughout. Horn–Johnson 2013, Theorem 6.3.12; supports
`simple-eigenvalue-perturbation`. [HornJohnson2013, Theorem 6.3.12]. -/
private theorem mem_spectrum_scalar_block_iff_schur_eq_zero
    {l n : Type*} [Unique l] [Fintype n] [DecidableEq n]
    (μ a t s : ℂ) (B F : Matrix n n ℂ) (b c : n → ℂ)
    (hK : IsUnit ((μ + s) • (1 : Matrix n n ℂ) - B - t • F)) :
    μ + s ∈ spectrum ℂ
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
        t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
          (Matrix.replicateRow l b) (Matrix.replicateCol l c) F) ↔
      simpleEigenvalueSchurFunction μ a B F b c (t, s) = 0 := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    det_scalar_block_eigenvalue_pencil_eq_schur μ a t s B F b c hK]
  have hDet := (Matrix.isUnit_iff_isUnit_det _).mp hK
  exact mul_eq_zero_iff_left hDet.ne_zero

end NLAlib

end

section

open Filter

open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The trailing resolvent remains invertible near a separated scalar eigenvalue.
[HornJohnson2013, Theorem 6.3.12]. -/
private theorem eventually_isUnit_shifted_pencil (μ : ℂ) (B F : Matrix n n ℂ)
    (hμ : μ ∉ spectrum ℂ B) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 0, IsUnit ((μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) := by
  have hunit : IsUnit (μ • (1 : Matrix n n ℂ) - B) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hμ
  have hcont : Continuous (fun p : ℂ × ℂ =>
      (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) := by fun_prop
  exact (hcont.continuousAt (x := 0)).preimage_mem_nhds (by simpa using Units.isOpen.mem_nhds hunit)

end NLAlib

end

section

open Filter

open scoped Matrix Topology ContDiff

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The scalar Schur equation is analytic near the origin when the trailing block excludes the
leading eigenvalue. The matrix inverse in the definition is the Banach-algebra inverse on a
neighborhood of the base point. [HornJohnson2013, Theorem 6.3.12]. -/
private theorem analyticAt_simpleEigenvalueSchurFunction (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    AnalyticAt ℂ (simpleEigenvalueSchurFunction μ a B F b c) 0 := by
  have hunit : IsUnit (μ • (1 : Matrix n n ℂ) - B) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hμ
  have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) 0 :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) 0 :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
  have hK : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) 0 :=
    (((analyticAt_const.add hsnd).smul analyticAt_const).sub
      analyticAt_const).sub (hfst.smul analyticAt_const)
  have hi : AnalyticAt ℂ Ring.inverse
      ((μ + (0 : ℂ × ℂ).2) • (1 : Matrix n n ℂ) - B - (0 : ℂ × ℂ).1 • F) := by
    simpa only [Prod.fst_zero, Prod.snd_zero, add_zero, zero_smul, sub_zero,
      hunit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hunit.unit)
  exact (hsnd.sub (hfst.mul analyticAt_const)).sub
    ((hfst.pow 2).mul (((schurResolventCoupling b c).analyticAt _).comp
      (hi.comp (f := fun p : ℂ × ℂ => (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) hK)))

open scoped Matrix.Norms.L2Operator in
/-- The separated scalar Schur equation admits an analytic local shift branch with derivative
equal to the leading perturbation entry. This proves holomorphy on a neighborhood, as needed for
exterior spectral branches in Stahl (2013), Theorem 2. [HornJohnson2013, Theorem 6.3.12]. -/
private theorem exists_analytic_simpleEigenvalueSchurFunction_branch (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    ∃ ψ : ℂ → ℂ, ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧ HasDerivAt ψ a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), simpleEigenvalueSchurFunction μ a B F b c (t, ψ t) = 0) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        simpleEigenvalueSchurFunction μ a B F b c p = 0 ↔ ψ p.1 = p.2) := by
  let f := simpleEigenvalueSchurFunction μ a B F b c
  let D : (ℂ × ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.snd ℂ ℂ ℂ - a • ContinuousLinearMap.fst ℂ ℂ ℂ
  have hf : HasStrictFDerivAt f D 0 :=
    hasStrictFDerivAt_simpleEigenvalueSchurFunction μ a B F b c hμ
  have hreg : ContDiffAt ℂ ω f 0 :=
    (analyticAt_simpleEigenvalueSchurFunction μ a B F b c hμ).contDiffAt
  have hD₂ : D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ = ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro z
    change z - a * 0 = z
    ring
  have hif : (fderiv ℂ f 0 ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [hf.hasFDerivAt.fderiv, hD₂]
    exact ⟨ContinuousLinearEquiv.refl ℂ ℂ, rfl⟩
  let ψ := hreg.implicitFunction (by simp : (ω : ℕ∞ω) ≠ 0) hif
  have hψ₀ : ψ 0 = 0 := hreg.implicitFunction_apply_self (by simp) hif
  have hψanalytic : AnalyticAt ℂ ψ 0 :=
    (hreg.contDiffAt_implicitFunction (by simp) hif).analyticAt
  have hderiv : -(fderiv ℂ f 0 ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).inverse ∘L
      (fderiv ℂ f 0 ∘L ContinuousLinearMap.inl ℂ ℂ ℂ) =
        a • ContinuousLinearMap.id ℂ ℂ := by
    rw [hf.hasFDerivAt.fderiv, hD₂, ContinuousLinearMap.inverse_id]
    apply ContinuousLinearMap.ext
    intro z
    change -(0 - a * z) = a * z
    ring
  have hψderiv : HasDerivAt ψ a 0 := by
    have h := (hreg.hasStrictFDerivAt_implicitFunction (by simp) hif).hasFDerivAt.hasDerivAt
    rw [hderiv] at h
    simpa using h
  have hf₀ : f 0 = 0 := by simp [f, simpleEigenvalueSchurFunction]
  refine ⟨ψ, hψ₀, hψanalytic, hψderiv, ?_, ?_⟩
  · simpa only [hf₀, Prod.fst_zero] using
      hreg.eventually_apply_implicitFunction (by simp) hif
  · simpa only [hf₀] using hreg.eventually_apply_eq_iff_implicitFunction (by simp) hif

open scoped Matrix.Norms.L2Operator in
/-- A separated scalar block has an analytic eigenvalue branch. The derivative at the base point
is its leading perturbation entry. [HornJohnson2013, Theorem 6.3.12]. -/
theorem exists_analytic_eigenvalue_branch_of_scalar_block
    {l : Type*} [Unique l] (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    ∃ φ : ℂ → ℂ, φ 0 = μ ∧ AnalyticAt ℂ φ 0 ∧ HasDerivAt φ a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ
        (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
          t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
            (Matrix.replicateRow l b) (Matrix.replicateCol l c) F)) := by
  obtain ⟨ψ, hψ₀, hψanalytic, hψderiv, hψeq, _⟩ :=
    exists_analytic_simpleEigenvalueSchurFunction_branch μ a B F b c hμ
  let φ : ℂ → ℂ := fun t => μ + ψ t
  have hgraph : Tendsto (fun t : ℂ => (t, ψ t)) (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    change Tendsto (fun t : ℂ => (t, ψ t)) (𝓝 0) (𝓝 ((0 : ℂ), 0))
    simpa only [hψ₀, id_eq] using
      (continuousAt_id.prodMk hψderiv.continuousAt).tendsto
  refine ⟨φ, by simp [φ, hψ₀], analyticAt_const.add hψanalytic,
    hψderiv.const_add μ, ?_⟩
  filter_upwards [hψeq,
    hgraph.eventually (eventually_isUnit_shifted_pencil μ B F hμ)] with t ht hKt
  exact (mem_spectrum_scalar_block_iff_schur_eq_zero μ a t (ψ t) B F b c hKt).mpr ht

open scoped Matrix.Norms.L2Operator in
/-- Each distinct diagonal entry of a diagonal pencil extends to an analytic eigenvalue branch,
with derivative the corresponding diagonal entry of the perturbation. [Stahl2013, Theorem 2]. -/
private theorem exists_analytic_eigenvalue_branch_of_diagonal
    (d : n → ℂ) (hd : Function.Injective d) (A : Matrix n n ℂ) (i : n) :
    ∃ φ : ℂ → ℂ, φ 0 = d i ∧ AnalyticAt ℂ φ 0 ∧ HasDerivAt φ (A i i) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ (Matrix.diagonal d + t • A)) := by
  classical
  let L := {j : n // j = i}
  let R := {j : n // j ≠ i}
  let : Unique L := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  let e : L ⊕ R ≃ n := Equiv.sumCompl (fun j => j = i)
  let B : Matrix R R ℂ := Matrix.diagonal (fun j => d j.val)
  let F : Matrix R R ℂ := A.submatrix Subtype.val Subtype.val
  let b : R → ℂ := fun j => A i j.val
  let c : R → ℂ := fun j => A j.val i
  have hsep : d i ∉ spectrum ℂ B := by
    rw [spectrum_diagonal]
    rintro ⟨j, hj⟩
    exact j.property (hd hj)
  have hM : (Matrix.diagonal d).submatrix e e =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : L => d i)) 0 0 B := by
    have hB : (Matrix.diagonal d).submatrix (fun j : R => j.val) (fun j : R => j.val) = B := by
      ext j k
      simp only [B, Matrix.submatrix_apply, Matrix.diagonal_apply]
      exact if_congr (Subtype.val_injective.eq_iff) rfl rfl
    have h := submatrix_eq_fromBlocks_of_isolated_coordinate (Matrix.diagonal d) i (d i)
      (fun j => by by_cases hj : j = i <;> simp [hj])
      (fun j => by by_cases hj : j = i <;> simp [hj, Ne.symm])
    convert! h using 1
    congr 1
    exact hB.symm
  have hA : A.submatrix e e =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : L => A i i))
        (Matrix.replicateRow L b) (Matrix.replicateCol L c) F :=
    submatrix_eq_fromBlocks_scalar_row_col A i
  obtain ⟨φ, hφ₀, hφanalytic, hφderiv, hφspec⟩ :=
    exists_analytic_eigenvalue_branch_of_scalar_block (l := L) (d i) (A i i) B F b c hsep
  refine ⟨φ, hφ₀, hφanalytic, hφderiv, ?_⟩
  filter_upwards [hφspec] with t ht
  have ht' : φ t ∈ spectrum ℂ ((Matrix.diagonal d + t • A).submatrix e e) := by
    change φ t ∈ spectrum ℂ ((Matrix.diagonal d).submatrix e e + t • A.submatrix e e)
    rw [hM, hA]
    convert! ht using 1
    congr 10 <;> exact Subsingleton.elim _ _
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at ht' ⊢
  have hc := Matrix.charpoly_reindex e.symm (Matrix.diagonal d + t • A)
  exact hc ▸ ht'

open scoped Matrix.Norms.L2Operator in
/-- The analytic diagonal-pencil branch has its first two Taylor terms with an analytic quadratic
remainder. Unlike a derivative statement alone, this gives the `O(z⁻¹)` remainder after reciprocal
substitution at infinity. [Stahl2013, Theorem 2]. -/
theorem exists_analytic_eigenvalue_branch_diagonal_expansion
    (d : n → ℂ) (hd : Function.Injective d) (A : Matrix n n ℂ) (i : n) :
    ∃ φ g : ℂ → ℂ, φ 0 = d i ∧ AnalyticAt ℂ φ 0 ∧ AnalyticAt ℂ g 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ (Matrix.diagonal d + t • A)) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t = d i + t * A i i + t ^ 2 * g t) := by
  obtain ⟨φ, hφ₀, hφanalytic, hφderiv, hφspec⟩ :=
    exists_analytic_eigenvalue_branch_of_diagonal d hd A i
  obtain ⟨g, hga, hg⟩ := hφanalytic.exists_eventuallyEq_sum_add_pow_mul 2
  refine ⟨φ, g, hφ₀, hφanalytic, hga, hφspec, ?_⟩
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    hφ₀, hφderiv.deriv, smul_eq_mul] using hg

end NLAlib

end
