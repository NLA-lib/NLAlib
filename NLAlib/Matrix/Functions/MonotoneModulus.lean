/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.MatrixMonotone
public import NLAlib.Matrix.Factorizations.Givens
public import NLAlib.Matrix.Norms.Loewner
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The modulus of continuity of a matrix monotone function

On the positive semidefinite cone the operator-norm displacement of a matrix monotone
function is bounded by its scalar value at the displacement of the inputs.

## Main results

* `NLAlib.OperatorMonotoneOn.concaveOn`: scalar concavity on the closed positive half-line.
* `NLAlib.OperatorMonotoneOn.specNorm_cfc_sub_le`: the modulus for real and complex matrices.
* `Matrix.PosSemidef.specNorm_rpow_sub_rpow_le`: the perturbation bound for fractional powers.
-/

@[expose] public section

open Matrix Filter Set
open scoped Matrix MatrixOrder ComplexOrder Topology

namespace NLAlib

private theorem posSemidef_diagonal_sub_of_pos (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : D.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    (diagonal ![D 0 0 + ε, D 1 1 + (D 0 1) ^ 2 / ε] - D).PosSemidef := by
  let v : Fin 2 → ℝ := ![1, -(D 0 1) / ε]
  have hv := (posSemidef_vecMulVec_self_star v).smul hε.le
  have he : diagonal ![D 0 0 + ε, D 1 1 + (D 0 1) ^ 2 / ε] - D =
      ε • vecMulVec v (star v) := by
    have hd : D 1 0 = D 0 1 := by simpa using hD.apply 0 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, v, vecMulVec, hd]
    all_goals field_simp
  rwa [← he] at hv

private theorem givens_diagonal_apply {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : ℝ) :
    let R := givens (0 : Fin 2) 1 (√a) (√b)
    (R * diagonal ![x,y] * Rᴴ) 0 0 = a*x + b*y := by
  intro R
  simp [R, Matrix.mul_apply, Fin.sum_univ_two,
    givens_apply (by norm_num : (0 : Fin 2) ≠ 1)]
  nlinarith [congrArg (fun t => x * t) (Real.sq_sqrt ha),
    congrArg (fun t => y * t) (Real.sq_sqrt hb)]

/-- A continuous function matrix monotone on the closed positive half-line is scalar concave
on the same set. [Bhatia1997, §V.2]. -/
theorem OperatorMonotoneOn.concaveOn {f : ℝ → ℝ} (hm : OperatorMonotoneOn (Ici 0) f)
    (hf : ContinuousOn f (Ici 0)) : ConcaveOn ℝ (Ici 0) f := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  let R := givens (0 : Fin 2) 1 (√a) (√b)
  have hR : HasOrthonormalCols R := hasOrthonormalCols_givens (by norm_num) (by
    simpa only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb] using hab)
  let D := R * diagonal ![x,y] * Rᴴ
  have hdiag : (diagonal ![x,y] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
    posSemidef_diagonal_iff.mpr fun i => by fin_cases i <;> assumption
  have hD : D.PosSemidef := hdiag.mul_mul_conjTranspose_same R
  have hDf : (cfc f D) 0 0 = a * f x + b * f y := by
    rw [hR.cfc_eq_mul_diagonal_mul_conjTranspose (d := ![x,y]) rfl (by rfl) f]
    have he : (fun i : Fin 2 => f (![x,y] i)) = ![f x,f y] := by
      funext i; fin_cases i <;> rfl
    simpa only [RCLike.ofReal_real_eq_id, id_eq, he] using givens_diagonal_apply ha hb (f x) (f y)
  have hbound (ε : ℝ) (hε : 0 < ε) : a * f x + b * f y ≤ f (a*x + b*y + ε) := by
    let d : Fin 2 → ℝ := ![D 0 0 + ε, D 1 1 + (D 0 1) ^ 2 / ε]
    have hle : D ≤ diagonal d :=
      Matrix.le_iff.mpr (posSemidef_diagonal_sub_of_pos D hD.isHermitian hε)
    have hE := (hD.nonneg.trans hle).posSemidef
    have h := hm.cfc_le_cfc hD.isHermitian hE.isHermitian
      (fun _ h => spectrum_nonneg_of_nonneg hD.nonneg h)
      (fun _ h => spectrum_nonneg_of_nonneg hE.nonneg h) hle
    have h' := (Matrix.le_iff.mp h).diag_nonneg (i := (0 : Fin 2))
    rw [Matrix.sub_apply, hDf, show cfc f (diagonal d) = diagonal (fun i => f (d i)) from
      cfc_diagonal (𝕜 := ℝ) f d] at h'
    have h00 : D 0 0 = a*x + b*y := givens_diagonal_apply ha hb x y
    simpa [d, h00, sub_nonneg] using h'
  have hz : 0 ≤ a*x + b*y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have ht : Tendsto (fun ε : ℝ => a*x + b*y + ε) (𝓝[>] 0) (𝓝[Ici 0] (a*x + b*y)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds.add
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact add_nonneg hz (le_of_lt hε)
  exact ge_of_tendsto ((hf _ hz).tendsto.comp ht)
    (Eventually.mono self_mem_nhdsWithin fun ε hε => hbound ε hε)

private theorem apply_add_le {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f) (hf0 : 0 ≤ f 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : f (x+y) ≤ f x + f y := by
  by_cases hsum : x+y=0
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    simpa [hx0, hy0] using hf0
  have hs : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hsum)
  have hab : x/(x+y) + y/(x+y) = 1 := by rw [← add_div, div_self hsum]
  have h₁ := hf.2 hs.le (show (0 : ℝ) ∈ Ici 0 by norm_num)
    (div_nonneg hx hs.le) (div_nonneg hy hs.le) hab
  have h₂ := hf.2 hs.le (show (0 : ℝ) ∈ Ici 0 by norm_num)
    (div_nonneg hy hs.le) (div_nonneg hx hs.le) ((add_comm _ _).trans hab)
  simp only [smul_eq_mul, mul_zero, add_zero, div_mul_cancel₀ _ hsum] at h₁ h₂
  have hh := add_le_add h₁ h₂
  nlinarith [show (x/(x+y) + y/(x+y)) * f (x+y) = f (x+y) by rw [hab, one_mul],
    show (x/(x+y) + y/(x+y)) * f 0 = f 0 by rw [hab, one_mul]]

private theorem cfc_add_smul_one {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (t : ℝ) {B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    cfc f (B + t • 1) = cfc (fun x => f (x+t)) B := by
  have hi : cfc (fun x : ℝ => x+t) B = B + t • 1 := by
    rw [cfc_add_const t (fun x : ℝ => x) B (B.finite_real_spectrum.continuousOn _) hB.isSelfAdjoint,
      cfc_id' ℝ B hB.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  rw [← hi]
  exact (cfc_comp f (fun x : ℝ => x+t) B hB.isSelfAdjoint
    ((B.finite_real_spectrum.image _).continuousOn _) (B.finite_real_spectrum.continuousOn _)).symm

/-- **Operator-monotone modulus of continuity.** For a continuous matrix monotone function
on the nonnegative half-line with $f(0)\ge 0$ and positive semidefinite matrices, the spectral-norm
difference of the function values satisfies
$$\|f(\mathbf{A})-f(\mathbf{B})\|_2 \le f(\|\mathbf{A}-\mathbf{B}\|_2).$$
[Bhatia1997, Theorem X.1.1], allowing a nonnegative boundary value.
Result: operator-monotone-modulus-continuity -/
theorem OperatorMonotoneOn.specNorm_cfc_sub_le {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {f : ℝ → ℝ} (hm : OperatorMonotoneOn (Ici 0) f)
    (hf : ContinuousOn f (Ici 0)) (h₀ : 0 ≤ f 0)
    {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    specNorm (cfc f A - cfc f B) ≤ f (specNorm (A - B)) := by
  have hup (A B : Matrix n n 𝕜) (hA : A.PosSemidef) (hB : B.PosSemidef) :
      cfc f A ≤ cfc f B + f (specNorm (A-B)) • 1 := by
    let t := specNorm (A-B)
    have ht : 0 ≤ t := specNorm_nonneg _
    have hBt : (B + t • 1).PosSemidef := hB.add (smul_nonneg ht zero_le_one).posSemidef
    have hcmp : A ≤ B + t • 1 := sub_le_iff_le_add'.mp
      ((hA.isHermitian.sub hB.isHermitian).le_smul_one_of_specNorm_le le_rfl)
    have h := hm.cfc_le_cfc hA.isHermitian hBt.isHermitian
      (fun _ hx => spectrum_nonneg_of_nonneg hA.nonneg hx)
      (fun _ hx => spectrum_nonneg_of_nonneg hBt.nonneg hx) hcmp
    rw [cfc_add_smul_one f t hB.isHermitian] at h
    refine h.trans ((cfc_mono (a := B)
      (fun x hx => apply_add_le (hm.concaveOn hf) h₀
        (spectrum_nonneg_of_nonneg hB.nonneg hx) ht)
      (B.finite_real_spectrum.continuousOn _) (B.finite_real_spectrum.continuousOn _)).trans_eq ?_)
    rw [cfc_add_const (f t) f B (B.finite_real_spectrum.continuousOn _)
      hB.isHermitian.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
  have hH : (cfc f A - cfc f B).IsHermitian :=
    (show (cfc f A).IsHermitian from cfc_predicate _ _).sub (cfc_predicate _ _)
  have ht := specNorm_nonneg (A - B)
  have hn := h₀.trans (hm.monotoneOn (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr ht) ht)
  apply (hH.specNorm_le_iff hn).mpr
  refine ⟨?_, sub_le_iff_le_add'.mpr (hup A B hA hB)⟩
  have h := hup B A hB hA
  rw [specNorm_sub_comm B A] at h
  exact neg_le_sub_iff_le_add.mpr h

/-- For positive semidefinite matrices and $0\le r\le 1$, fractional powers satisfy
$$\|\mathbf{A}^r-\mathbf{B}^r\|_2\le\|\mathbf{A}-\mathbf{B}\|_2^r.$$
At $r=0$ the left side is zero and the right side is one.
[Bhatia1997, Theorem X.1.1], specialized to the Löwner–Heinz powers. -/
theorem _root_.Matrix.PosSemidef.specNorm_rpow_sub_rpow_le {𝕜 n : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    specNorm (A ^ r - B ^ r) ≤ specNorm (A - B) ^ r := by
  rw [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hB.nonneg]
  exact (operatorMonotoneOn_rpow hr).specNorm_cfc_sub_le
    (Real.continuous_rpow_const hr.1).continuousOn (Real.rpow_nonneg le_rfl _) hA hB

end NLAlib
