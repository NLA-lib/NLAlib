/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import NLAlib.ForMathlib.Analysis.CStarAlgebra.Matrix
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.PosDef
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Probability.Isotropic

/-!
# Integrals of matrix-valued functions

The expectation of a random matrix `X : Ω → Matrix m n 𝕜` is Mathlib's Bochner integral
`∫ ω, X ω ∂μ`, which needs a normed-space structure on matrices. NLAlib uses one scope for it,
library-wide: `open scoped Matrix.Norms.L2Operator` (`docs/design/Mathlib-deviations.md`
entry 13), with the real normed-space instance of
`NLAlib/ForMathlib/Analysis/CStarAlgebra/Matrix.lean`. The value of the integral does not depend
on the norm, and the statements here mention none: integrability and the integral are entrywise,
and the integral commutes with the conjugate transpose, reindexing, submatrices, the trace,
products with fixed matrices and quadratic forms. An almost surely Hermitian (positive
semidefinite) random matrix has a Hermitian (positive semidefinite) mean, with no integrability
hypothesis, because a non-integrable function integrates to `0`. Loewner monotonicity is Mathlib's
`MeasureTheory.integral_mono_ae`, through `Matrix.instOrderClosedTopology`
(`NLAlib/ForMathlib/LinearAlgebra/Matrix/PosDef.lean`).

## Main results

* `Matrix.integrable_iff`, `Matrix.memLp_iff`, `Matrix.integral_apply`: entrywise.
* `Matrix.integral_conjTranspose`, `Matrix.integral_reindex`, `Matrix.integral_submatrix`,
  `Matrix.integral_trace`, `Matrix.integral_const_mul`, `Matrix.integral_mul_const`,
  `Matrix.integral_quadForm`.
* `Matrix.isHermitian_integral`, `Matrix.posSemidef_integral`, `Matrix.posDef_integral`.
* `Matrix.IsHermitian.integrable_cfc`, `Matrix.IsHermitian.cfc_integral`: a random function of a
  fixed Hermitian matrix, with no continuity hypothesis.
* `NLAlib.IsIsotropic.integral_vecMulVec`: `E [X Xᴴ] = 1`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {l m n k : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype k] [DecidableEq n]

section Entrywise

variable {X : Ω → Matrix m n 𝕜}

/-- Matrices as functions of two indices, a real continuous linear equivalence. -/
private noncomputable def toPi : Matrix m n 𝕜 ≃L[ℝ] (m → n → 𝕜) :=
  (Matrix.ofLinearEquiv ℝ).symm.toContinuousLinearEquiv

/-- A random matrix is integrable exactly when its entries are. -/
theorem _root_.Matrix.integrable_iff :
    Integrable X μ ↔ ∀ i j, Integrable (fun ω => X ω i j) μ := by
  rw [← toPi.integrable_comp_iff]
  simp only [integrable_pi_iff]
  rfl

/-- A random matrix is in `Lᵖ` exactly when its entries are. -/
theorem _root_.Matrix.memLp_iff {p : ℝ≥0∞} :
    MemLp X p μ ↔ ∀ i j, MemLp (fun ω => X ω i j) p μ := by
  have h : MemLp X p μ ↔ MemLp (fun ω => toPi (X ω)) p μ :=
    ⟨fun h => (toPi (m := m) (n := n) (𝕜 := 𝕜)).toContinuousLinearMap.comp_memLp' h, fun h => by
      simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] using
        (toPi (m := m) (n := n) (𝕜 := 𝕜)).symm.toContinuousLinearMap.comp_memLp' h⟩
  rw [h]
  simp only [memLp_pi_iff]
  rfl

/-- The entries of the mean of a random matrix are the means of its entries. Integrability of
the entries is needed: if one entry is not integrable, the integral is `0` while the other
entries may have nonzero means. -/
theorem _root_.Matrix.integral_apply (hX : ∀ i j, Integrable (fun ω => X ω i j) μ) (i : m)
    (j : n) : (∫ ω, X ω ∂μ) i j = ∫ ω, X ω i j ∂μ := by
  exact ((Matrix.entryLinearMap ℝ 𝕜 i j).toContinuousLinearMap.integral_comp_comm
    (Matrix.integrable_iff.mpr hX)).symm

end Entrywise

section Linear

variable {X : Ω → Matrix m n 𝕜}

/-- The conjugate transpose as a real linear equivalence. -/
private def conjTransposeLinearEquivReal : Matrix m n 𝕜 ≃ₗ[ℝ] Matrix n m 𝕜 where
  toFun := Matrix.conjTranspose
  invFun := Matrix.conjTranspose
  map_add' := Matrix.conjTranspose_add
  map_smul' r A := by simp only [Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply]
  left_inv := Matrix.conjTranspose_conjTranspose
  right_inv := Matrix.conjTranspose_conjTranspose

variable [DecidableEq m] in
/-- The conjugate transpose commutes with the integral; no integrability is needed, since the
conjugate transpose is a real-linear isometric equivalence. -/
theorem _root_.Matrix.integral_conjTranspose (X : Ω → Matrix m n 𝕜) :
    ∫ ω, (X ω)ᴴ ∂μ = (∫ ω, X ω ∂μ)ᴴ := by
  exact (conjTransposeLinearEquivReal (m := m) (n := n) (𝕜 := 𝕜)).toContinuousLinearEquiv
    |>.integral_comp_comm X

/-- Reindexing commutes with the integral; no integrability is needed. -/
theorem _root_.Matrix.integral_reindex {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (e : m ≃ m') (f : n ≃ n') (X : Ω → Matrix m n 𝕜) :
    ∫ ω, Matrix.reindex e f (X ω) ∂μ = Matrix.reindex e f (∫ ω, X ω ∂μ) := by
  exact (Matrix.reindexLinearEquiv ℝ 𝕜 e f).toContinuousLinearEquiv.integral_comp_comm X

variable [DecidableEq k] in
/-- A submatrix of the mean is the mean of the submatrix. -/
theorem _root_.Matrix.integral_submatrix (hX : Integrable X μ) (r : l → m) (c : k → n) :
    ∫ ω, (X ω).submatrix r c ∂μ = (∫ ω, X ω ∂μ).submatrix r c := by
  let L : Matrix m n 𝕜 →ₗ[ℝ] Matrix l k 𝕜 :=
    { toFun := fun A => A.submatrix r c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.toContinuousLinearMap.integral_comp_comm hX

/-- The trace commutes with the integral. -/
theorem _root_.Matrix.integral_trace {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ) :
    ∫ ω, (X ω).trace ∂μ = (∫ ω, X ω ∂μ).trace := by
  exact (Matrix.traceLinearMap n ℝ 𝕜).toContinuousLinearMap.integral_comp_comm hX

/-- A fixed left factor comes out of the integral. Integrability is needed: `A * X` may be
integrable when `X` is not. -/
theorem _root_.Matrix.integral_const_mul (A : Matrix l m 𝕜) (hX : Integrable X μ) :
    ∫ ω, A * X ω ∂μ = A * ∫ ω, X ω ∂μ := by
  let L : Matrix m n 𝕜 →ₗ[ℝ] Matrix l n 𝕜 :=
    { toFun := fun B => A * B
      map_add' := Matrix.mul_add A
      map_smul' := fun r B => Matrix.mul_smul A r B }
  exact L.toContinuousLinearMap.integral_comp_comm hX

variable [DecidableEq k] in
/-- A fixed right factor comes out of the integral. -/
theorem _root_.Matrix.integral_mul_const (hX : Integrable X μ) (B : Matrix n k 𝕜) :
    ∫ ω, X ω * B ∂μ = (∫ ω, X ω ∂μ) * B := by
  let L : Matrix m n 𝕜 →ₗ[ℝ] Matrix m k 𝕜 :=
    { toFun := fun A => A * B
      map_add' := fun A A' => Matrix.add_mul A A' B
      map_smul' := fun r A => Matrix.smul_mul r A B }
  exact L.toContinuousLinearMap.integral_comp_comm hX

/-- The quadratic form at a fixed vector, as a real linear map of the matrix. -/
private def quadFormLinearMap (z : n → 𝕜) : Matrix n n 𝕜 →ₗ[ℝ] 𝕜 where
  toFun A := quadForm A z
  map_add' A A' := quadForm_add_left A A' z
  map_smul' r A := by
    simp only [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left,
      smul_eq_mul]

/-- The quadratic form of the mean is the mean of the quadratic form. -/
theorem _root_.Matrix.integral_quadForm {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ)
    (z : n → 𝕜) : ∫ ω, quadForm (X ω) z ∂μ = quadForm (∫ ω, X ω ∂μ) z := by
  exact (quadFormLinearMap z).toContinuousLinearMap.integral_comp_comm hX

end Linear

section Order

variable {X : Ω → Matrix n n 𝕜}

/-- An almost surely Hermitian random matrix has a Hermitian mean. No integrability is needed:
a non-integrable function integrates to `0`. -/
theorem _root_.Matrix.isHermitian_integral (h : ∀ᵐ ω ∂μ, (X ω).IsHermitian) :
    (∫ ω, X ω ∂μ).IsHermitian := by
  rw [Matrix.IsHermitian, ← Matrix.integral_conjTranspose]
  exact integral_congr_ae (h.mono fun _ hω => hω.eq)

/-- An almost surely positive semidefinite random matrix has a positive semidefinite mean. No
integrability is needed. -/
theorem _root_.Matrix.posSemidef_integral (h : ∀ᵐ ω ∂μ, (X ω).PosSemidef) :
    (∫ ω, X ω ∂μ).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae (h.mono fun _ hω => hω.nonneg))

/-- An integrable, almost surely positive definite random matrix has a positive definite mean,
for a nonzero measure. -/
theorem _root_.Matrix.posDef_integral [NeZero μ] (hX : Integrable X μ)
    (h : ∀ᵐ ω ∂μ, (X ω).PosDef) : (∫ ω, X ω ∂μ).PosDef := by
  refine posDef_iff_quadForm_pos.mpr
    ⟨Matrix.isHermitian_integral (h.mono fun _ hω => hω.isHermitian), fun z hz => ?_⟩
  have hq : ∀ᵐ ω ∂μ, 0 < quadForm (X ω) z := h.mono fun _ hω => hω.quadForm_pos hz
  have hre : ∀ᵐ ω ∂μ, 0 < RCLike.re (quadForm (X ω) z) :=
    h.mono fun _ hω => hω.re_quadForm_pos hz
  have hint : Integrable (fun ω => quadForm (X ω) z) μ :=
    (quadFormLinearMap z).toContinuousLinearMap.integrable_comp hX
  rw [← Matrix.integral_quadForm hX, RCLike.pos_iff]
  refine ⟨?_, ?_⟩
  · rw [← integral_re hint]
    refine (integral_pos_iff_support_of_nonneg_ae (hre.mono fun _ h => h.le) hint.re).mpr ?_
    have hs : Function.support (fun ω => RCLike.re (quadForm (X ω) z)) =ᵐ[μ] Set.univ := by
      filter_upwards [hre] with ω hω
      exact propext (iff_true_intro hω.ne')
    rw [measure_congr hs]
    exact Measure.measure_univ_pos.mpr (NeZero.ne μ)
  · rw [← integral_im hint, integral_eq_zero_of_ae (hq.mono fun _ hω => ?_)]
    exact (RCLike.pos_iff.mp hω).2

end Order

/-! ### Functions of a fixed Hermitian matrix -/

/-- Both halves of `Matrix.IsHermitian.integrable_cfc` and `Matrix.IsHermitian.cfc_integral`,
through a unitary diagonalisation of `B`. -/
private theorem integrable_and_integral_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {f : Ω → ℝ → ℝ} (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    Integrable (fun ω => cfc (f ω) B) μ ∧
      ∫ ω, cfc (f ω) B ∂μ = cfc (fun x => ∫ ω, f ω x ∂μ) B := by
  obtain ⟨U, hU, hBU⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  let L : (Fin (Fintype.card n) → ℝ) →ₗ[ℝ] Matrix n n 𝕜 :=
    { toFun := fun v => U * Matrix.diagonal (fun i => ((v i : ℝ) : 𝕜)) * Uᴴ
      map_add' := fun v w => by
        simp only [Pi.add_apply, RCLike.ofReal_add, ← Matrix.diagonal_add, Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := fun a v => by
        have hd : (fun i => (((a • v) i : ℝ) : 𝕜)) = (a : 𝕜) • fun i => ((v i : ℝ) : 𝕜) := by
          funext i
          simp only [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul]
        rw [RingHom.id_apply, hd, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul,
          ← RCLike.real_smul_eq_coe_smul] }
  let Lc := LinearMap.toContinuousLinearMap L
  have hcfc : ∀ g : ℝ → ℝ, cfc g B = Lc (fun i => g (eigenvalue B i)) := fun g =>
    cfc_eq_mul_diagonal_mul_conjTranspose hU hr hBU g
  have hv : Integrable (fun ω => fun i : Fin (Fintype.card n) => f ω (eigenvalue B i)) μ :=
    integrable_pi_iff.2 fun i => hf _
  simp only [hcfc]
  refine ⟨Lc.integrable_comp hv, ?_⟩
  rw [Lc.integral_comp_comm hv]
  congr 1
  funext i
  exact eval_integral (fun i => hf _) i

/-- **A random function of a fixed Hermitian matrix is integrable** when its values are: if
`ω ↦ f ω x` is integrable for every `x`, so is `ω ↦ cfc (f ω) B`. Unlike Mathlib's
`integrable_cfc`, no continuity in `ω` or `x` is needed: the spectrum of a matrix is finite. -/
theorem _root_.Matrix.IsHermitian.integrable_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {f : Ω → ℝ → ℝ} (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    Integrable (fun ω => cfc (f ω) B) μ :=
  (integrable_and_integral_cfc hB hf).1

/-- **The functional calculus of a fixed Hermitian matrix commutes with the integral**: if
`ω ↦ f ω x` is integrable for every `x`, then `cfc (∫ f ω) B = ∫ cfc (f ω) B`. Unlike Mathlib's
`cfc_integral`, no continuity in `ω` or `x` is needed: the spectrum of a matrix is finite. -/
theorem _root_.Matrix.IsHermitian.cfc_integral {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {f : Ω → ℝ → ℝ} (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    cfc (fun x => ∫ ω, f ω x ∂μ) B = ∫ ω, cfc (f ω) B ∂μ :=
  (integrable_and_integral_cfc hB hf).2.symm

/-- The second-moment matrix of an isotropic vector is the identity: `E [X Xᴴ] = 1`. -/
theorem IsIsotropic.integral_vecMulVec {X : Ω → n → 𝕜} (hX : IsIsotropic X μ) :
    ∫ ω, Matrix.vecMulVec (X ω) (star (X ω)) ∂μ = 1 := by
  ext i j
  refine (Matrix.integral_apply (X := fun ω => Matrix.vecMulVec (X ω) (star (X ω)))
    (fun i j => hX.integrable_mul_star i j) i j).trans ?_
  exact (hX.integral_mul_star i j).trans Matrix.one_apply.symm

end NLAlib
