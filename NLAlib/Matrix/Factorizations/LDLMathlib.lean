/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.LDL
public import NLAlib.Matrix.Factorizations.LDL

/-!
# Bridge to Mathlib's LDL decomposition

Mathlib constructs LDL factors of a positive definite matrix through Gram–Schmidt. Its inverse
lower factor has unit diagonal, so its lower factor is unit lower triangular. Together with
Mathlib's diagonal conjugation identity, these factors satisfy the same `IsLDL` predicate as
Hermitian elimination. On ordered finite numerical indices uniqueness identifies both factors
with the canonical elimination lower factor and pivot diagonal. The predicate also admits
indefinite matrices, beyond Mathlib's positive-definite construction.

## Main results

* `Matrix.PosDef.isUnitLowerTriangular_lowerInv`: Mathlib's inverse lower factor has unit diagonal.
* `Matrix.PosDef.isUnitLowerTriangular_lower`: Mathlib's lower factor has unit diagonal.
* `Matrix.PosDef.isLDL_lower_diagEntries`: Mathlib's factors satisfy the general LDL predicate.
* `Matrix.PosDef.lower_eq_luLower`: canonical lower factors agree on positive definite inputs.
* `Matrix.PosDef.diagEntries_eq_gaussState_apply_self`: canonical pivot diagonals agree.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [LinearOrder n]
    [WellFoundedLT n] [LocallyFiniteOrderBot n] [Fintype n]

private theorem _root_.Matrix.PosDef.lowerInv_apply_self
    {A : Matrix n n 𝕜} (hA : A.PosDef) (i : n) :
    LDL.lowerInv hA i i = 1 := by
  let := Aᵀ.toNormedAddCommGroup hA.transpose
  let := Aᵀ.toInnerProductSpace hA.transpose.posSemidef
  have hs : ∀ j ∈ Finset.Iio i,
      InnerProductSpace.gramSchmidt 𝕜 (Pi.basisFun 𝕜 n) j i = 0 := by
    intro j hj
    exact LDL.lowerInv_triangular hA (Finset.mem_Iio.mp hj)
  have hg := congrFun (InnerProductSpace.gramSchmidt_def'' 𝕜 (Pi.basisFun 𝕜 n) i) i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hg
  rw [Finset.sum_eq_zero (fun j hj => by rw [hs j hj, mul_zero]), add_zero] at hg
  simpa only [LDL.lowerInv, Pi.basisFun_apply, Pi.single_eq_same] using hg.symm

/-- The inverse lower factor in Mathlib's positive-definite LDL construction is unit lower
triangular. Its diagonal entries follow by evaluating the Gram–Schmidt identity on the same
basis coordinate; earlier triangular rows contribute zero at that coordinate. -/
theorem _root_.Matrix.PosDef.isUnitLowerTriangular_lowerInv {A : Matrix n n 𝕜} (hA : A.PosDef) :
    IsUnitLowerTriangular (LDL.lowerInv hA) :=
  ⟨fun _ _ hij => LDL.lowerInv_triangular hA hij, hA.lowerInv_apply_self⟩

/-- Mathlib's positive-definite LDL lower factor is unit lower triangular, as the inverse of
its unit lower triangular Gram–Schmidt factor. -/
theorem _root_.Matrix.PosDef.isUnitLowerTriangular_lower {A : Matrix n n 𝕜} (hA : A.PosDef) :
    IsUnitLowerTriangular (LDL.lower hA) :=
  hA.isUnitLowerTriangular_lowerInv.inv

/-- Mathlib's positive-definite LDL construction supplies the general Hermitian LDL predicate,
with its actual lower factor and diagonal entries. This bridge holds for real and complex
scalars and the ordered finite index types supported by Mathlib's construction. -/
theorem _root_.Matrix.PosDef.isLDL_lower_diagEntries {A : Matrix n n 𝕜} (hA : A.PosDef) :
    IsLDL A (LDL.lower hA) (LDL.diagEntries hA) := by
  refine ⟨hA.isUnitLowerTriangular_lower, ?_, (LDL.lower_conj_diag hA).symm⟩
  have hd : (LDL.diag hA).IsHermitian := by
    rw [LDL.diag_eq_lowerInv_conj hA]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA.isHermitian
  exact Matrix.isHermitian_diagonal_iff.mp hd

variable {N : ℕ}

/-- On positive definite inputs, Mathlib's lower factor equals the canonical elimination
lower factor. Both obey the same LDL predicate and the nonsingular factorization is unique. -/
theorem _root_.Matrix.PosDef.lower_eq_luLower {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef) :
    LDL.lower hA = luLower A := by
  have hc := hA.isHermitian.isLDL_luLower
    (fun i => ne_of_gt (hA.gaussState_apply_self_pos i))
  exact (IsLDL.unique ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
    hA.isLDL_lower_diagEntries hc).1

/-- On positive definite inputs, Mathlib's diagonal entries are exactly the total elimination
pivots. The equality concerns the actual canonical factors, without an existential choice. -/
theorem _root_.Matrix.PosDef.diagEntries_eq_gaussState_apply_self
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef) :
    LDL.diagEntries hA = fun i : Fin N => gaussState A i i i := by
  have hc := hA.isHermitian.isLDL_luLower
    (fun i => ne_of_gt (hA.gaussState_apply_self_pos i))
  exact (IsLDL.unique ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
    hA.isLDL_lower_diagEntries hc).2

end NLAlib
