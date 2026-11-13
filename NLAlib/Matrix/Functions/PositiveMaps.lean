/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import NLAlib.ForMathlib.Data.Matrix.Block
public import NLAlib.Matrix.Factorizations.PolarFrames
public import NLAlib.Matrix.Functions.OperatorConvex
public import NLAlib.Matrix.Inequalities.Block
public import NLAlib.Matrix.Spectral.Normal

/-!
# Positive matrix maps

A positive map sends a finite spectral resolution of the identity to positive weights. For a
unital map these sum to the identity, so the operator Jensen inequality applies on each
Hermitian input. [Tropp2022, §12].

## Main results

* `NLAlib.OperatorConvexOn.cfc_map_le`: Jensen's inequality for positive unital matrix maps.
* `NLAlib.sq_map_le_map_sq`, `NLAlib.inv_map_le_map_inv`: the square and inverse inequalities.
* `NLAlib.isGreatest_image_specNorm_map`: norm attainment at the identity on the whole unit ball.
-/

@[expose] public section

open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private abbrev spectralAtom (U : Matrix n n 𝕜) (i : n) : Matrix n n 𝕜 :=
  vecMulVec (U.col i) (star (U.col i))

private theorem sum_spectralAtom {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) :
    ∑ i, spectralAtom U i = 1 := by
  simpa [hU.mul_conjTranspose_self_of_card_eq rfl] using
    (mul_diagonal_mul_conjTranspose_eq_sum_vecMulVec U (fun _ => 1)).symm

private theorem cfc_eq_sum_spectralAtom {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = ∑ i, ((f (hA.eigenvalues i) : ℝ) : 𝕜) •
      spectralAtom (hA.eigenvectorUnitary : Matrix n n 𝕜) i := by
  have hdiag : A = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜)) *
        (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
    have h := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  exact hA.hasOrthonormalCols_eigenvectorUnitary.cfc_eq_sum_smul_vecMulVec rfl hdiag f

private theorem map_cfc_eq_sum_sqrt (Φ : Matrix n n 𝕜 →ₚ[𝕜] Matrix m m 𝕜)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    let K := fun i => CFC.sqrt (Φ (spectralAtom (hA.eigenvectorUnitary : Matrix n n 𝕜) i))
    Φ (cfc f A) = ∑ i, (K i)ᴴ * algebraMap ℝ (Matrix m m 𝕜) (f (hA.eigenvalues i)) * K i := by
  intro K
  rw [cfc_eq_sum_spectralAtom hA, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  let u := (hA.eigenvectorUnitary : Matrix n n 𝕜).col i
  have hp := Φ.map_nonneg (Matrix.posSemidef_vecMulVec_self_star u).nonneg
  have hh : (K i).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  rw [map_smul, Algebra.algebraMap_eq_smul_one, hh.eq, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  rw [show K i * K i = _ from CFC.sqrt_mul_sqrt_self _ hp]

/-- For a positive unital linear map and an operator convex function on the spectrum of a
Hermitian input, applying the function after the map is bounded above by applying the map after
the function. [Bhatia1997, Theorem V.2.2]; [Tropp2022, §12]. -/
theorem OperatorConvexOn.cfc_map_le {s : Set ℝ} {f : ℝ → ℝ} (hf : OperatorConvexOn s f)
    (Φ : Matrix n n 𝕜 →ₚ[𝕜] Matrix m m 𝕜) (hΦ : Φ 1 = 1) {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hs : spectrum ℝ A ⊆ s) : cfc f (Φ A) ≤ Φ (cfc f A) := by
  let K := fun i => CFC.sqrt (Φ (spectralAtom (hA.eigenvectorUnitary : Matrix n n 𝕜) i))
  have hK : ∑ i, (K i)ᴴ * K i = 1 := by
    calc
      _ = ∑ i, Φ (spectralAtom (hA.eigenvectorUnitary : Matrix n n 𝕜) i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        let u := (hA.eigenvectorUnitary : Matrix n n 𝕜).col i
        have hp := Φ.map_nonneg (Matrix.posSemidef_vecMulVec_self_star u).nonneg
        rw [(show (K i).IsHermitian from (CFC.sqrt_nonneg _).isSelfAdjoint).eq]
        exact CFC.sqrt_mul_sqrt_self _ hp
      _ = 1 := by rw [← map_sum, sum_spectralAtom hA.hasOrthonormalCols_eigenvectorUnitary, hΦ]
  cases isEmpty_or_nonempty m with
  | inl he => exact le_of_eq (Subsingleton.elim _ _)
  | inr hm =>
    let D (i : n) := algebraMap ℝ (Matrix m m 𝕜) (hA.eigenvalues i)
    have hD (i : n) : (D i).IsHermitian := (IsSelfAdjoint.all _).algebraMap _
    have hDs (i : n) : spectrum ℝ (D i) ⊆ s := by
      intro t ht
      change t ∈ spectrum ℝ (algebraMap ℝ (Matrix m m 𝕜) _) at ht
      rw [spectrum.scalar_eq, Set.mem_singleton_iff] at ht
      exact hs (ht ▸ hA.eigenvalues_mem_spectrum_real i)
    have h := hf.cfc_sum_conjTranspose_mul_mul_le hD hDs hK
    have hm := map_cfc_eq_sum_sqrt Φ hA id
    dsimp only [id_eq] at hm
    rw [cfc_id ℝ A hA.isSelfAdjoint] at hm
    rw [map_cfc_eq_sum_sqrt Φ hA f, hm]
    simpa only [D, cfc_algebraMap] using h

/-- **Kadison's inequality.** For a positive unital linear matrix map and Hermitian input,
the square of the image is bounded above by the image of the square.
[Tropp2022, Theorem 12.17].
Result: positive-map-kadison -/
theorem sq_map_le_map_sq (Φ : Matrix n n 𝕜 →ₚ[𝕜] Matrix m m 𝕜) (hΦ : Φ 1 = 1)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : (Φ A) ^ 2 ≤ Φ (A ^ 2) := by
  have hs : (Φ A).IsHermitian := by
    rw [← cfc_id' ℝ A hA.isSelfAdjoint, cfc_eq_sum_spectralAtom hA, map_sum]
    apply isSelfAdjoint_sum
    intro i _
    rw [map_smul]
    have hp := Φ.map_nonneg
      (Matrix.posSemidef_vecMulVec_self_star ((hA.eigenvectorUnitary : Matrix n n 𝕜).col i)).nonneg
    apply hp.posSemidef.isHermitian.smul
    exact (show IsSelfAdjoint ((hA.eigenvalues i : ℝ) : 𝕜) from RCLike.conj_ofReal _)
  have h := operatorConvexOn_sq.cfc_map_le Φ hΦ hA (Set.subset_univ _)
  rwa [cfc_pow_id (Φ A) 2 hs.isSelfAdjoint, cfc_pow_id A 2 hA.isSelfAdjoint] at h

omit [Fintype n] [Fintype m] in
/-- A positive unital map preserves strict positivity of a finite matrix. [Tropp2022, §12]. -/
theorem _root_.Matrix.PosDef.posDef_map [Finite n] {A : Matrix n n 𝕜} (hA : A.PosDef)
    (Φ : Matrix n n 𝕜 →ₚ[𝕜] Matrix m m 𝕜) (hΦ : Φ 1 = 1) : (Φ A).PosDef := by
  let := Fintype.ofFinite n
  cases isEmpty_or_nonempty n with
  | inl hn =>
    rw [show A = 1 from Subsingleton.elim _ _, hΦ]
    exact Matrix.PosDef.one
  | inr hn =>
    obtain ⟨c, hc, hcA⟩ :=
      (CFC.exists_pos_algebraMap_le_iff hA.isHermitian.isSelfAdjoint).mpr
        (fun x hx => hA.isStrictlyPositive.spectrum_pos hx)
    have hgap := Φ.monotone hcA
    change Φ (algebraMap ℝ (Matrix n n 𝕜) c) ≤ Φ A at hgap
    rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smul, hΦ,
      ← RCLike.real_smul_eq_coe_smul] at hgap
    have hp := (Matrix.PosDef.one.smul hc).add_posSemidef (Matrix.le_iff.mp hgap)
    simpa only [add_sub_cancel] using hp

/-- **Inverse Jensen inequality.** A positive unital linear matrix map evaluated at a positive
definite matrix has inverse bounded above by the map of the inverse. [Tropp2022, Theorem 12.19].
Result: positive-map-inverse-jensen -/
theorem inv_map_le_map_inv (Φ : Matrix n n 𝕜 →ₚ[𝕜] Matrix m m 𝕜) (hΦ : Φ 1 = 1)
    {A : Matrix n n 𝕜} (hA : A.PosDef) : (Φ A)⁻¹ ≤ Φ A⁻¹ := by
  have hP := hA.posDef_map Φ hΦ
  have h := operatorConvexOn_inv.cfc_map_le Φ hΦ hA.isHermitian
    (fun _ hx => hA.isStrictlyPositive.spectrum_pos hx)
  simpa only [cfc_ringInverse_id (R := ℝ) A hA.isUnit hA.isHermitian.isSelfAdjoint,
    cfc_ringInverse_id (R := ℝ) (Φ A) hP.isUnit hP.isHermitian.isSelfAdjoint,
    ← Matrix.nonsing_inv_eq_ringInverse] using h

/-! ### The norm of a positive complex-linear map -/

omit [Fintype m] [DecidableEq m] in
private theorem posSemidef_fromBlocks_phase [Finite m] {B : Matrix m m ℂ} (hB : B.PosSemidef)
    {z : ℂ} (hz : z * star z = 1) : (fromBlocks B (z • B) (star z • B) B).PosSemidef := by
  classical
  let := Fintype.ofFinite m
  have h := hB.mul_mul_conjTranspose_same
    (fromRows (z • (1 : Matrix m m ℂ)) (1 : Matrix m m ℂ))
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols] at h
  simpa only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, mul_comm (star z) z,
    hz, one_smul] using h

omit [DecidableEq m] in
private theorem specNorm_map_le_of_hasOrthonormalCols
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) {A : Matrix n n ℂ}
    (hA : HasOrthonormalCols A) : specNorm (Φ A) ≤ specNorm (Φ 1) := by
  classical
  have hnormal : IsStarNormal A :=
    isStarNormal_of_mem_unitary (hasOrthonormalCols_iff_mem_unitaryGroup.mp hA)
  obtain ⟨V, d, hV, hdiag⟩ := isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose.mp hnormal
  have hD : Vᴴ * A * V = diagonal d := by
    rw [hdiag, Matrix.mul_assoc V (diagonal d), hV.conjTranspose_mul_cancel_left,
      Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one]
  have hDV : HasOrthonormalCols (diagonal d) := hD ▸ (hV.conjTranspose.mul hA).mul hV
  have hz (i : n) : d i * star (d i) = 1 := by
    have h := congrFun (congrFun (hDV.mul_conjTranspose_self_of_card_eq rfl) i) i
    simpa using h
  let B := fun i => Φ (spectralAtom V i)
  have hB (i : n) : (B i).PosSemidef :=
    (Φ.map_nonneg (Matrix.posSemidef_vecMulVec_self_star (V.col i)).nonneg).posSemidef
  have hsum : ∑ i, B i = Φ 1 := by
    dsimp [B]
    rw [← map_sum, sum_spectralAtom hV]
  have hfirst : ∑ i, d i • B i = Φ A := by
    rw [hdiag, mul_diagonal_mul_conjTranspose_eq_sum_vecMulVec, map_sum]
    simp only [map_smul]
    rfl
  have hsecond : ∑ i, star (d i) • B i = (Φ A)ᴴ := by
    rw [← hfirst, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.conjTranspose_smul, (hB i).isHermitian.eq]
  have hp := Matrix.posSemidef_sum Finset.univ fun i _ => posSemidef_fromBlocks_phase (hB i) (hz i)
  rw [Matrix.sum_fromBlocks, hsum, hfirst, hsecond] at hp
  exact hp.specNorm_le_specNorm_of_fromBlocks

omit [DecidableEq m] in
/-- **Russo–Dye norm attainment.** A positive complex-linear map attains its largest spectral
norm on the closed spectral-norm unit ball at the identity matrix. Neither unitality nor strict
positivity of the image of the identity is required. [Tropp2022, Theorem 12.22].
Result: positive-map-norm-at-identity -/
theorem isGreatest_image_specNorm_map (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) :
    IsGreatest ((fun A => specNorm (Φ A)) '' {A | specNorm A ≤ 1}) (specNorm (Φ 1)) := by
  refine ⟨⟨1, specNorm_one_le, rfl⟩, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨U, V, hU, hV, h⟩ := exists_eq_smul_add_of_specNorm_le_one A hA
  change specNorm (Φ A) ≤ _
  rw [h, map_smul, map_add, specNorm_smul]
  have h₂ : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [h₂]
  have hUV := (specNorm_add_le (Φ U) (Φ V)).trans
    (add_le_add (specNorm_map_le_of_hasOrthonormalCols Φ hU)
      (specNorm_map_le_of_hasOrthonormalCols Φ hV))
  linarith

end NLAlib
