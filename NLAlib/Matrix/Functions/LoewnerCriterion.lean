/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.HermitianDerivative
public import NLAlib.Matrix.Functions.MatrixMonotone
public import NLAlib.Matrix.Functions.Complexification
public import NLAlib.Matrix.Basic.QuadForm
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Löwner matrices and operator monotonicity

An open convex spectral domain and differentiability suffice to test monotonicity by
positivity of all confluent Löwner matrices, in any finite dimension.

## Main results

* `NLAlib.operatorMonotoneOn_iff_posSemidef_loewnerMatrix`: the Löwner criterion.
-/

@[expose] public section

open Matrix Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive Löwner matrix makes the Hadamard derivative positive. -/
private theorem posSemidef_loewnerDerivative {f : ℝ → ℝ} {ev : n → ℝ}
    (hL : (loewnerMatrix f ev).PosSemidef) (U : unitary (Matrix n n ℂ))
    {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    (loewnerDerivative f ev U H).PosSemidef := by
  have hLc : ((loewnerMatrix f ev).map Complex.ofReal).PosSemidef :=
    (posSemidef_complexify_iff (A := loewnerMatrix f ev)).mpr hL
  have hp := hLc.hadamard (hH.conjTranspose_mul_mul_same (U : Matrix n n ℂ))
  exact hp.mul_mul_conjTranspose_same _

/-- On an open spectral domain, operator monotonicity forces the actual
divided-difference derivative to preserve the positive cone. -/
private theorem OperatorMonotoneOn.posSemidef_loewnerDerivative {I : Set ℝ} {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn I f) (hI : IsOpen I) (hf : DifferentiableOn ℝ f I)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hAI : spectrum ℝ A ⊆ I)
    (ev : n → ℝ) (U : unitary (Matrix n n ℂ))
    (hdiag : A = (U : Matrix n n ℂ) * diagonal (fun i => (ev i : ℂ)) *
      (U : Matrix n n ℂ).conjTranspose)
    {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    (loewnerDerivative f ev U H).PosSemidef := by
  have hfd := hA.hasFDerivWithinAt_cfc
    (fun i => (hf _ (hAI (hA.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩))).differentiableAt
      (hI.mem_nhds (hAI (hA.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)))) ev U hdiag
  have hpath : HasDerivAt (fun t : ℝ => A + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add A
  have hd : HasDerivAt (fun t : ℝ => cfc f (A + t • H))
      (loewnerDerivative f ev U H) 0 := by
    apply hfd.comp_hasDerivAt_of_eq 0 hpath
    · exact Filter.Eventually.of_forall fun t => hA.add (hH.isHermitian.smul (IsSelfAdjoint.all t))
    · simp
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, spectrum ℝ (A + t • H) ⊆ I :=
    hpath.continuousAt.preimage_mem_nhds
      ((upperHemicontinuous_spectrum ℝ _).forall_isOpen _ I hI (by simpa using hAI))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (t⁻¹ • (cfc f (A + t • H) - cfc f A)).PosSemidef := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    have hm' := hm.cfc_le_cfc hA (hA.add (hH.isHermitian.smul (IsSelfAdjoint.all t))) hAI ht
      (by rw [Matrix.le_iff, add_sub_cancel_left]; exact hH.smul (le_of_lt ht0))
    exact (Matrix.le_iff.mp hm').smul (inv_nonneg.mpr (le_of_lt ht0))
  have hclosed : IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
    simpa only [Set.Ici, Matrix.nonneg_iff_posSemidef] using
      (isClosed_Ici : IsClosed (Set.Ici (0 : Matrix n n ℂ)))
  apply hclosed.mem_of_tendsto _ hpos
  simpa only [zero_add, zero_smul, add_zero] using hd.tendsto_slope_zero_right


open Set

private theorem spectrum_subset_of_order_interval {I : Set ℝ} (hI : Convex ℝ I)
    {A B C : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I)
    (hAC : A ≤ C) (hCB : C ≤ B) : spectrum ℝ C ⊆ I := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := hC.spectrum_eq_image_eigenvalue ▸ hx
  exact hI.ordConnected.out (hAI (hA.eigenvalue_mem_spectrum hk))
    (hBI (hB.eigenvalue_mem_spectrum hk))
    ⟨eigenvalue_le_eigenvalue_of_le hAC hA k, eigenvalue_le_eigenvalue_of_le hCB hC k⟩


/-- Evaluation of a fixed real quadratic form is a continuous real linear
functional of its matrix argument. -/
private noncomputable def reQuadFormCLM (x : n → ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun A := (quadForm A x).re
      map_add' A B := by simp [quadForm, Matrix.add_mulVec, dotProduct_add]
      map_smul' c A := by
        simp [quadForm, Matrix.smul_mulVec, dotProduct_smul] }

omit [Fintype n] [DecidableEq n] in
/-- Matrix monotonicity forces every finite Löwner matrix to be positive,
including lists with repeated nodes. [Tropp2022, Theorem 14.5]. -/
theorem OperatorMonotoneOn.posSemidef_loewnerMatrix [Finite n] {I : Set ℝ} {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn I f) (hI : IsOpen I) (hf : DifferentiableOn ℝ f I)
    (ev : n → ℝ) (hev : ∀ i, ev i ∈ I) : (loewnerMatrix f ev).PosSemidef := by
  classical
  let _ := Fintype.ofFinite n
  let A := diagonal (fun i => (ev i : ℂ))
  have hA : A.IsHermitian := by
    change (diagonal (fun i => (ev i : ℂ))).IsHermitian
    exact isHermitian_diagonal_iff.mpr (fun i => by change star (ev i : ℂ) = _; simp)
  have hAI : spectrum ℝ A ⊆ I := by
    intro x hx
    have hx' : (x : ℂ) ∈ spectrum ℂ A := (spectrum.algebraMap_mem_iff ℂ).mpr hx
    rw [spectrum_diagonal] at hx'
    obtain ⟨i, hi⟩ := hx'
    exact Complex.ofReal_injective hi ▸ hev i
  let J : Matrix n n ℂ := Matrix.of fun _ _ => 1
  have hJ : J.PosSemidef := by
    simpa [J, vecMulVec] using posSemidef_vecMulVec_self_star (fun _ : n => (1 : ℂ))
  have h := hm.posSemidef_loewnerDerivative hI hf hA hAI ev 1
    (by simp [A]) hJ
  have hc : ((loewnerMatrix f ev).map Complex.ofReal).PosSemidef := by
    change ((1 : Matrix n n ℂ) * ((loewnerMatrix f ev).map Complex.ofReal ⊙
      ((1 : Matrix n n ℂ)ᴴ * J * 1)) * (1 : Matrix n n ℂ)ᴴ).PosSemidef at h
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
    have hj : (loewnerMatrix f ev).map Complex.ofReal ⊙ J =
        (loewnerMatrix f ev).map Complex.ofReal := by ext i j; simp [J]
    rwa [hj] at h
  exact (posSemidef_complexify_iff (A := loewnerMatrix f ev)).mp hc

/-- Positive Löwner matrices imply monotonicity on every ordered matrix
segment in an open convex scalar domain. -/
private theorem cfc_le_of_posSemidef_loewnerMatrices {I : Set ℝ} {f : ℝ → ℝ}
    (hI : IsOpen I) (hcI : Convex ℝ I) (hf : DifferentiableOn ℝ f I)
    (hL : ∀ ev : n → ℝ, (∀ i, ev i ∈ I) → (loewnerMatrix f ev).PosSemidef)
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) (hAB : A ≤ B) :
    cfc f A ≤ cfc f B := by
  cases isEmpty_or_nonempty n with
  | inl he => exact (show cfc f A = cfc f B from Subsingleton.elim _ _).le
  | inr hn =>
    let D := B - A
    have hD : D.PosSemidef := Matrix.le_iff.mp hAB
    let C (t : ℝ) := A + t • D
    have hC (t : ℝ) : (C t).IsHermitian := hA.add (hD.isHermitian.smul (IsSelfAdjoint.all t))
    have hCI (t : ℝ) (ht : t ∈ Icc 0 1) : spectrum ℝ (C t) ⊆ I := by
      apply spectrum_subset_of_order_interval hcI hA hB (hC t) hAI hBI
      · rw [Matrix.le_iff, show C t - A = t • D by dsimp [C]; abel]
        exact hD.smul ht.1
      · rw [Matrix.le_iff, show B - C t = (1-t) • D by dsimp [C, D]; module]
        exact hD.smul (sub_nonneg.mpr ht.2)
    let L (t : ℝ) := loewnerDerivative f (hC t).eigenvalues (hC t).eigenvectorUnitary
    have hd (t : ℝ) (ht : t ∈ Icc 0 1) :
        HasDerivAt (fun s => cfc f (C s)) (L t D) t := by
      have hi (i : n) : (hC t).eigenvalues i ∈ I :=
        hCI t ht ((hC t).spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)
      have hfd := (hC t).hasFDerivWithinAt_cfc
        (fun i => (hf _ (hi i)).differentiableAt (hI.mem_nhds (hi i)))
        (hC t).eigenvalues (hC t).eigenvectorUnitary (hC t).spectral_theorem
      exact hfd.comp_hasDerivAt t
        (by simpa [C] using (((hasDerivAt_id t).smul_const D).const_add A))
        (Eventually.of_forall fun s => hC s)
    have hp (t : ℝ) (ht : t ∈ Icc 0 1) : (L t D).PosSemidef :=
      posSemidef_loewnerDerivative (hL _ fun i =>
        hCI t ht ((hC t).spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)) _ hD
    have hfA : (cfc f A).IsHermitian := cfc_predicate _ _
    have hfB : (cfc f B).IsHermitian := cfc_predicate _ _
    apply (hfA.le_iff_re_quadForm_le hfB).mpr
    intro x
    have hq (t : ℝ) (ht : t ∈ Icc 0 1) :=
      (reQuadFormCLM x).hasFDerivAt.comp_hasDerivAt t (hd t ht)
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      (fun t ht => (hq t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hq t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hq t (interior_subset ht)).deriv]
        exact (hp t (interior_subset ht)).re_quadForm_nonneg x)
    have hv := hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_le_one
    change (quadForm (cfc f (C 0)) x).re ≤ (quadForm (cfc f (C 1)) x).re at hv
    simpa [C, D] using hv

/-- **Löwner criterion.** On an open convex real set a differentiable function is
operator monotone in every finite size precisely when all its Löwner matrices are positive.
Repeated nodes and unbounded intervals are permitted. [Tropp2022, §14].
Result: matrix-monotone-loewner-criterion -/
theorem operatorMonotoneOn_iff_posSemidef_loewnerMatrix {I : Set ℝ} {f : ℝ → ℝ}
    (hI : IsOpen I) (hcI : Convex ℝ I) (hf : DifferentiableOn ℝ f I) :
    OperatorMonotoneOn I f ↔ ∀ (d : ℕ) (ev : Fin d → ℝ),
      (∀ i, ev i ∈ I) → (loewnerMatrix f ev).PosSemidef := by
  constructor
  · intro hm d ev hev
    exact hm.posSemidef_loewnerMatrix hI hf ev hev
  · intro hL d A B hA hB hAI hBI hAB
    exact cfc_le_of_posSemidef_loewnerMatrices hI hcI hf (hL d) hA hB hAI hBI hAB

end NLAlib
