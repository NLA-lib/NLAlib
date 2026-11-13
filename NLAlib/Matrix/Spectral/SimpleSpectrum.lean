/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Finite lists of distinct spectral values

A complete list of distinct eigenvalues identifies the spectrum and supplies an eigenbasis.
The scalar field need not be algebraically closed, and the empty matrix is allowed.

## Main results

* `NLAlib.exists_mulVec_eq_smul_of_injective`.
* `NLAlib.spectrum_eq_range_of_injective_mem_spectrum`.
-/

@[expose] public section
open Matrix Module.End
namespace NLAlib
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A full list of pairwise distinct spectral values gives a basis of eigenvectors. -/
theorem exists_mulVec_eq_smul_of_injective
    (M : Matrix n n K) (ev : n → K) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum K M) :
    ∃ b : Module.Basis n K (n → K), ∀ i, M *ᵥ b i = ev i • b i := by
  classical
  have heig : ∀ i, Module.End.HasEigenvalue M.toLin' (ev i) := by
    intro i
    apply Module.End.HasEigenvalue.of_mem_spectrum
    simpa using hmem i
  choose v hv using fun i => (heig i).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent' M.toLin' ev hev v hv
  let b := basisOfLinearIndependentOfCardEqFinrank' v hli
    (Module.finrank_fintype_fun_eq_card K).symm
  refine ⟨b, ?_⟩
  intro i
  change M.toLin' (b i) = ev i • b i
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using
    (hv i).apply_eq_smul

/-- A full list of pairwise distinct spectral values exhausts the spectrum. -/
theorem spectrum_eq_range_of_injective_mem_spectrum
    (M : Matrix n n K) (ev : n → K) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum K M) : spectrum K M = Set.range ev := by
  obtain ⟨b, hb⟩ := exists_mulVec_eq_smul_of_injective M ev hev hmem
  have hD : LinearMap.toMatrix b b M.toLin' = Matrix.diagonal ev := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [← Matrix.spectrum_toLin' M, ← LinearMap.spectrum_toMatrix M.toLin' b,
    hD, spectrum_diagonal]

/-- Every real diagonal node in a unitary diagonalization is a real
spectral value of the original matrix. -/
theorem mem_spectrum_of_eq_mul_diagonal_mul_conjTranspose {𝕜 : Type*} [RCLike 𝕜]
    (ev : n → ℝ)
    (U : unitary (Matrix n n 𝕜)) {A : Matrix n n 𝕜}
    (hA : A = (U : Matrix n n 𝕜) * diagonal (fun i => (ev i : 𝕜)) *
      (U : Matrix n n 𝕜)ᴴ) (i : n) : ev i ∈ spectrum ℝ A := by
  have hc : (ev i : 𝕜) ∈ spectrum 𝕜 A := by
    rw [hA]
    change (ev i : 𝕜) ∈ spectrum 𝕜
      ((Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) U) (diagonal (fun j => (ev j : 𝕜))))
    rw [AlgEquiv.spectrum_eq, spectrum_diagonal]
    exact ⟨i, rfl⟩
  exact (spectrum.algebraMap_mem_iff 𝕜).mp hc

end NLAlib
