/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Complexification
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Matrix monotonicity on a scalar set

Order preservation is required in every finite dimension. Complexification and reindexing
give the same order comparison in real or complex coordinates of arbitrary finite type.

## Main results

* `NLAlib.OperatorMonotoneOn.cfc_le_cfc`: order preservation for arbitrary finite index types.
* `NLAlib.operatorMonotoneOn_rpow`, `NLAlib.operatorMonotoneOn_sqrt`: the Löwner–Heinz powers.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

/-- A function is matrix monotone on a scalar set if its Hermitian functional calculus preserves
the Loewner order there, in every finite complex dimension. [Bhatia1997, §V.1]. -/
def OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ), A.IsHermitian → B.IsHermitian →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s → A ≤ B → cfc f A ≤ cfc f B

/-- Matrix monotonicity on a set implies scalar monotonicity on that set,
by considering one-dimensional matrices. [Bhatia1997, §V.1]. -/
theorem OperatorMonotoneOn.monotoneOn {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorMonotoneOn s f) : MonotoneOn f s := by
  intro x hx y hy hxy
  let ι := algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℂ)
  have hι (z : ℝ) : (ι z).IsHermitian := (IsSelfAdjoint.all z).algebraMap _
  have hs (z : ℝ) (hz : z ∈ s) : spectrum ℝ (ι z) ⊆ s := by
    rw [spectrum.scalar_eq]
    exact Set.singleton_subset_iff.mpr hz
  have h := hf 1 (ι x) (ι y) (hι x) (hι y) (hs x hx) (hs y hy) (algebraMap_le_algebraMap.mpr hxy)
  rw [cfc_algebraMap, cfc_algebraMap] at h
  exact algebraMap_le_algebraMap.mp h

/-- Matrix monotonicity applies over real or complex scalars on any finite index type.
[Bhatia1997, §V.1]. -/
theorem OperatorMonotoneOn.cfc_le_cfc {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {s : Set ℝ} {f : ℝ → ℝ} (hf : OperatorMonotoneOn s f) {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAs : spectrum ℝ A ⊆ s)
    (hBs : spectrum ℝ B ⊆ s) (hAB : A ≤ B) : cfc f A ≤ cfc f B := by
  let e := (Fintype.equivFin n).symm
  let R (M : Matrix n n 𝕜) := (complexify M).submatrix e e
  have hr (M : Matrix n n 𝕜) (hM : M.IsHermitian) : (R M).IsHermitian :=
    (isHermitian_complexify_iff.mpr hM).submatrix e
  have hs (M : Matrix n n 𝕜) : spectrum ℝ (R M) = spectrum ℝ M := by
    rw [← spectrum_complexify M]
    exact AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℂ e.symm) (complexify M)
  have ho (M N : Matrix n n 𝕜) : R M ≤ R N ↔ M ≤ N := by
    rw [Matrix.le_iff, Matrix.le_iff]
    change ((complexify N - complexify M).submatrix e e).PosSemidef ↔ _
    rw [Matrix.posSemidef_submatrix_equiv, ← complexify_sub, posSemidef_complexify_iff]
  have hc (M : Matrix n n 𝕜) (hM : M.IsHermitian) : cfc f (R M) = R (cfc f M) := by
    change cfc f ((complexify M).submatrix e e) = (complexify (cfc f M)).submatrix e e
    rw [Matrix.IsHermitian.cfc_submatrix_equiv (isHermitian_complexify_iff.mpr hM) f e,
      hM.complexify_cfc]
  have h := hf _ _ _ (hr A hA) (hr B hB) (by rwa [hs]) (by rwa [hs]) ((ho A B).mpr hAB)
  rwa [hc A hA, hc B hB, ho] at h

open scoped Matrix.Norms.L2Operator in
/-- Powers with exponent in the closed unit interval are operator monotone on the nonnegative
half-line. At exponent zero the scalar function is constant one, including at zero.
[Bhatia1997, Theorem V.1.9]. -/
theorem operatorMonotoneOn_rpow {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    OperatorMonotoneOn (Set.Ici 0) (fun x : ℝ => x ^ r) := by
  intro d A B hA _ hAs _ hAB
  have ha : 0 ≤ A := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A hA.isSelfAdjoint).2
    fun _ hx => hAs hx
  rw [← CFC.rpow_eq_cfc_real ha, ← CFC.rpow_eq_cfc_real (ha.trans hAB)]
  exact CFC.rpow_le_rpow hr hAB

/-- The nonnegative square root is operator monotone on the closed positive half-line.
[Bhatia1997, Proposition V.1.8]. -/
theorem operatorMonotoneOn_sqrt : OperatorMonotoneOn (Set.Ici 0) Real.sqrt := by
  rw [show Real.sqrt = (fun x : ℝ => x ^ (1 / 2 : ℝ)) from funext Real.sqrt_eq_rpow]
  exact operatorMonotoneOn_rpow ⟨by norm_num, by norm_num⟩

end NLAlib
