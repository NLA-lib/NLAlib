/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Matrix.PosDef
public import NLAlib.Matrix.Norms.Frobenius

/-!
# The real Frobenius space of Hermitian matrices

The underlying real vector space is the self-adjoint submodule. Its Euclidean norm is the
Frobenius norm, so operator-norm statements on this space control Frobenius perturbations.

## Main results

* `NLAlib.norm_eq_frobNorm`: agreement with the matrix Frobenius norm.
-/

@[expose] public section

namespace NLAlib

variable (𝕜 n : Type*) [RCLike 𝕜] [Fintype n]

/-- The native Hermitian real vector space, equipped below with its Frobenius Hilbert norm
rather than its spectral matrix norm. -/
noncomputable def hermitianFrobenius : Type _ := ↥(selfAdjoint.submodule ℝ (Matrix n n 𝕜))
noncomputable instance : AddCommGroup (hermitianFrobenius 𝕜 n) :=
  inferInstanceAs (AddCommGroup (selfAdjoint.submodule ℝ (Matrix n n 𝕜)))
noncomputable instance : Module ℝ (hermitianFrobenius 𝕜 n) :=
  inferInstanceAs (Module ℝ (selfAdjoint.submodule ℝ (Matrix n n 𝕜)))

/-- The identity linear equivalence to the native self-adjoint submodule. -/
noncomputable def hermitianFrobeniusEquiv : hermitianFrobenius 𝕜 n ≃ₗ[ℝ]
    selfAdjoint.submodule ℝ (Matrix n n 𝕜) := LinearEquiv.refl ℝ _

/-- The Hermitian matrix represented by a Frobenius Hilbert vector. -/
noncomputable def hermitianFrobeniusMatrix (x : hermitianFrobenius 𝕜 n) : Matrix n n 𝕜 :=
  (hermitianFrobeniusEquiv 𝕜 n x).val

variable {𝕜 n}

/-- Matrix realization is real-linear. -/
noncomputable def hermitianFrobeniusMatrixLinear : hermitianFrobenius 𝕜 n →ₗ[ℝ] Matrix n n 𝕜 :=
  (selfAdjoint.submodule ℝ (Matrix n n 𝕜)).subtype.comp
    (hermitianFrobeniusEquiv 𝕜 n).toLinearMap

/-- Frobenius inner-product data on the native self-adjoint submodule. -/
@[instance_reducible]
noncomputable def hermitianFrobeniusCore : InnerProductSpace.Core ℝ (hermitianFrobenius 𝕜 n) where
  inner x y := frobInner (hermitianFrobeniusMatrix 𝕜 n x) (hermitianFrobeniusMatrix 𝕜 n y)
  conj_inner_symm x y := frobInner_comm _ _
  re_inner_nonneg x := by
    change 0 ≤ frobInner (hermitianFrobeniusMatrix 𝕜 n x) _
    rw [frobInner_self]; exact sq_nonneg _
  add_left x y z := frobInner_add_left _ _ _
  smul_left x y r := frobInner_smul_left r _ _
  definite x hx := by
    apply (hermitianFrobeniusEquiv 𝕜 n).injective
    apply Subtype.ext
    rw [frobInner_self, sq_eq_zero_iff] at hx
    exact frobNorm_eq_zero_iff.mp hx
noncomputable instance : NormedAddCommGroup (hermitianFrobenius 𝕜 n) :=
  hermitianFrobeniusCore.toNormedAddCommGroup
noncomputable instance : InnerProductSpace ℝ (hermitianFrobenius 𝕜 n) :=
  InnerProductSpace.ofCore hermitianFrobeniusCore.toCore

/-- The Hilbert inner product is exactly the library's real Frobenius pairing. -/
theorem inner_eq_frobInner (x y : hermitianFrobenius 𝕜 n) :
    inner ℝ x y = frobInner (hermitianFrobeniusMatrix 𝕜 n x)
      (hermitianFrobeniusMatrix 𝕜 n y) := rfl

/-- The Hilbert norm is exactly the named Frobenius matrix norm. -/
theorem norm_eq_frobNorm (x : hermitianFrobenius 𝕜 n) :
    ‖x‖ = frobNorm (hermitianFrobeniusMatrix 𝕜 n x) := by
  change √(frobInner (hermitianFrobeniusMatrix 𝕜 n x) _) = _
  rw [frobInner_self, Real.sqrt_sq (frobNorm_nonneg _)]

omit [Fintype n] in
noncomputable instance [Finite n] : FiniteDimensional ℝ (hermitianFrobenius 𝕜 n) := by
  let := Fintype.ofFinite n
  exact FiniteDimensional.of_injective hermitianFrobeniusMatrixLinear
    (fun _ _ h => (hermitianFrobeniusEquiv 𝕜 n).injective (Subtype.ext h))

noncomputable instance : CompleteSpace (hermitianFrobenius 𝕜 n) := FiniteDimensional.complete ℝ _

omit [Fintype n] in
/-- Every realized vector is a Hermitian matrix. -/
theorem isHermitian_hermitianFrobeniusMatrix (x : hermitianFrobenius 𝕜 n) :
    (hermitianFrobeniusMatrix 𝕜 n x).IsHermitian :=
  (hermitianFrobeniusEquiv 𝕜 n x).property

/-- A Hermitian matrix as a vector in the Frobenius Hilbert realization. -/
noncomputable def toHermitianFrobenius {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    hermitianFrobenius 𝕜 n := (hermitianFrobeniusEquiv 𝕜 n).symm ⟨H, hH⟩

omit [Fintype n] in
noncomputable instance [DecidableEq n] : One (hermitianFrobenius 𝕜 n) :=
  ⟨toHermitianFrobenius (Matrix.isHermitian_one : (1 : Matrix n n 𝕜).IsHermitian)⟩

omit [Fintype n] in
/-- Matrix realization of the canonical Hermitian inclusion. -/
@[simp] theorem _root_.Matrix.IsHermitian.hermitianFrobeniusMatrix_toHermitianFrobenius
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    hermitianFrobeniusMatrix 𝕜 n (toHermitianFrobenius hH) = H := rfl

omit [Fintype n] in
noncomputable instance [Finite n] [Nonempty n] : Nontrivial (hermitianFrobenius 𝕜 n) := by
  classical
  let := Fintype.ofFinite n
  refine ⟨⟨0, toHermitianFrobenius (Matrix.isHermitian_one : (1 : Matrix n n 𝕜).IsHermitian), ?_⟩⟩
  intro h
  have hm := congrArg (hermitianFrobeniusMatrix 𝕜 n) h
  exact zero_ne_one hm

end NLAlib
