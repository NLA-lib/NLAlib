/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import NLAlib.Matrix.Functions.GoldenThompson
public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Defect

/-!
# Variational bounds for the determinant

Normalized trace objectives express the determinant of a PSD matrix and give a bound on its
distance from the identity.

## Main results

* `Matrix.PosSemidef.isGLB_determinantTraceObjectiveSet`.
-/
@[expose] public section

open Matrix Filter

open scoped MatrixOrder ComplexOrder Topology

namespace NLAlib

variable {n K : Type*} [Fintype n] [DecidableEq n] [RCLike K]

/-- PSD AM-GM inequality over `RCLike` fields: the determinant (a real number)
of a positive semidefinite matrix is at most the `card n`-th power of its
normalized trace. -/
theorem _root_.Matrix.PosSemidef.re_det_le_pow_re_trace_div_card
    {M : Matrix n n K} (hN : 0 < Fintype.card n) (hM : M.PosSemidef) :
    RCLike.re M.det ≤ (RCLike.re M.trace / (Fintype.card n : ℝ)) ^ Fintype.card n := by
  classical
  let eig : n → ℝ := hM.isHermitian.eigenvalues
  let p : ℝ := ∏ i, eig i
  let s : ℝ := ∑ i, eig i
  have heig_nonneg : ∀ i, 0 ≤ eig i := fun i => hM.eigenvalues_nonneg i
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    exact Finset.prod_nonneg fun i _ => heig_nonneg i
  have hcard_ne : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have htr : RCLike.re M.trace = s := by
    dsimp [s, eig]
    rw [hM.isHermitian.trace_eq_sum_eigenvalues]
    exact (congrArg RCLike.re
      (RCLike.ofReal_sum (Finset.univ : Finset n) eig)).symm.trans
      (RCLike.ofReal_re (∑ i, eig i))
  have hdet : M.det = (p : K) := by
    dsimp [p, eig]
    rw [hM.isHermitian.det_eq_prod_eigenvalues]
    exact (RCLike.ofReal_prod (Finset.univ : Finset n) eig).symm
  have ham := Real.geom_mean_le_arith_mean (s := (Finset.univ : Finset n))
      (w := fun _ : n => (1 : ℝ)) (z := eig)
      (by intro i hi; norm_num)
      (by simpa using (show 0 < (Fintype.card n : ℝ) by exact_mod_cast hN))
      (fun i hi => heig_nonneg i)
  have hmain : p ^ ((Fintype.card n : ℝ)⁻¹) ≤ s / (Fintype.card n : ℝ) := by
    simpa [p, s] using ham
  have hpownat :
      (p ^ ((Fintype.card n : ℝ)⁻¹)) ^ Fintype.card n ≤
        (s / (Fintype.card n : ℝ)) ^ Fintype.card n :=
    pow_le_pow_left₀ (Real.rpow_nonneg hp_nonneg _) hmain (Fintype.card n)
  have hpowid :
      (p ^ ((Fintype.card n : ℝ)⁻¹)) ^ Fintype.card n = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_nonneg, inv_mul_cancel₀ hcard_ne,
      Real.rpow_one]
  calc
    RCLike.re M.det = RCLike.re (∏ i, (eig i : K)) := by
          rw [hdet]
          dsimp [p]
          exact congrArg RCLike.re
            (RCLike.ofReal_prod (Finset.univ : Finset n) eig)
    _ = p := by
          dsimp [p]
          exact (congrArg RCLike.re
            (RCLike.ofReal_prod (Finset.univ : Finset n) eig)).symm.trans
            (RCLike.ofReal_re (∏ i, eig i))
    _ ≤ (s / (Fintype.card n : ℝ)) ^ Fintype.card n := by
          rw [← hpowid]
          exact hpownat
    _ ≤ (RCLike.re M.trace / (Fintype.card n : ℝ)) ^ Fintype.card n := by
          rw [htr]

/-- The variational set for the determinant of `M`: values of the normalized
trace power at positive definite matrices with determinant one. -/
noncomputable def determinantTraceObjectiveSet (M : Matrix n n K) : Set ℝ :=
  {v : ℝ | ∃ Y : Matrix n n K, Y.PosDef ∧ Y.det = 1 ∧
    v = (RCLike.re (Y * M).trace / (Fintype.card n : ℝ)) ^ Fintype.card n}

/-- AM-GM lower bound in variational form: any positive definite `Y` with
`det Y = 1` gives an upper bound for `re M.det`. -/
theorem _root_.Matrix.PosSemidef.re_det_le_objective_of_det_one
    {M : Matrix n n K} (hN : 0 < Fintype.card n) (hM : M.PosSemidef)
    {Y : Matrix n n K} (hY : Y.PosDef) (hYdet : Y.det = 1) :
    RCLike.re M.det ≤
      (RCLike.re (Y * M).trace / (Fintype.card n : ℝ)) ^ Fintype.card n := by
  classical
  let S : Matrix n n K := CFC.sqrt Y
  have hS_herm : S.IsHermitian := (CFC.sqrt_nonneg Y).posSemidef.isHermitian
  have hSM : (S * M * S).PosSemidef := by
    simpa [hS_herm.eq] using hM.conjTranspose_mul_mul_same S
  have hdetS : S.det = 1 := by
    rw [hY.posSemidef.det_sqrt, hYdet]
    simp
  have hdetSMS : (S * M * S).det = M.det := by
    calc
      (S * M * S).det = S.det * M.det * S.det := by
        rw [Matrix.det_mul, Matrix.det_mul]
      _ = M.det := by
        rw [hdetS]
        simp
  have htrSMS : (S * M * S).trace = (Y * M).trace := by
    calc
      (S * M * S).trace = (S * S * M).trace := by
        rw [Matrix.trace_mul_cycle]
      _ = (Y * M).trace := by
        rw [CFC.sqrt_mul_sqrt_self Y hY.posSemidef.nonneg]
  rw [← hdetSMS, ← htrSMS]
  exact hSM.re_det_le_pow_re_trace_div_card hN

/-- In positive dimension, the determinant is a lower bound for every
determinant-trace objective of a PSD matrix. -/
theorem _root_.Matrix.PosSemidef.re_det_mem_lowerBounds_determinantTraceObjectiveSet
    {M : Matrix n n K} (hN : 0 < Fintype.card n) (hM : M.PosSemidef) :
    RCLike.re M.det ∈ lowerBounds (determinantTraceObjectiveSet M) := by
  rintro _ ⟨Y, hY, hYdet, rfl⟩
  exact hM.re_det_le_objective_of_det_one hN hY hYdet

/-- For positive definite `M`, the determinant-trace lower bound is attained at
the positive definite matrix `Y = (re M.det) ^ (1 / card n) • M⁻¹`. -/
theorem _root_.Matrix.PosDef.exists_det_one_objective_eq_re_det
    {M : Matrix n n K} (hN : 0 < Fintype.card n) (hM : M.PosDef) :
    ∃ Y : Matrix n n K, Y.PosDef ∧ Y.det = 1 ∧
      RCLike.re M.det =
        (RCLike.re (Y * M).trace / (Fintype.card n : ℝ)) ^ Fintype.card n := by
  classical
  let c : ℝ := (Fintype.card n : ℝ)
  let d : ℝ := RCLike.re M.det ^ (1 / c)
  let Y : Matrix n n K := d • M⁻¹
  have hre_pos : 0 < RCLike.re M.det := (RCLike.pos_iff.mp hM.det_pos).1
  have him_zero : RCLike.im M.det = 0 := (RCLike.pos_iff.mp hM.det_pos).2
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast Nat.ne_of_gt hN
  have hd_pos : 0 < d := by
    dsimp [d]
    exact Real.rpow_pos_of_pos hre_pos _
  have hd_pow : d ^ Fintype.card n = RCLike.re M.det := by
    dsimp [d]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hre_pos.le, one_div_mul_cancel hc_ne,
      Real.rpow_one]
  have hdet_real : M.det = algebraMap ℝ K (RCLike.re M.det) := by
    refine (RCLike.ext_iff.mpr ?_).symm
    constructor
    · simp
    · simp [him_zero]
  refine ⟨Y, ?_, ?_, ?_⟩
  · exact hM.inv.smul hd_pos
  · dsimp [Y]
    rw [Matrix.det_smul_of_tower, hd_pow, Algebra.smul_def, ← hdet_real]
    rw [mul_comm, Matrix.det_nonsing_inv_mul_det (A := M)]
    exact isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  · have hMinvM : M⁻¹ * M = 1 :=
      Matrix.nonsing_inv_mul (A := M) (isUnit_iff_ne_zero.mpr hM.det_pos.ne')
    have hYM : Y * M = d • (1 : Matrix n n K) := by
      calc
        Y * M = (d • M⁻¹) * M := rfl
        _ = d • (M⁻¹ * M) := by rw [Matrix.smul_mul]
        _ = d • (1 : Matrix n n K) := by rw [hMinvM]
    have htr_re : RCLike.re (Y * M).trace = d * c := by
      rw [hYM]
      rw [Matrix.trace_smul, Matrix.trace_one]
      rw [RCLike.smul_re]
      simp [c]
    have hObj : (RCLike.re (Y * M).trace / c) ^ Fintype.card n =
        RCLike.re M.det := by
      rw [htr_re]
      calc
        (d * c / c) ^ Fintype.card n = d ^ Fintype.card n := by
          rw [mul_div_assoc, div_self hc_ne, mul_one]
        _ = RCLike.re M.det := hd_pow
    exact hObj.symm

/-- In positive dimension, the determinant of a PSD matrix is the greatest
lower bound of its determinant-trace objective set. Singular matrices are
handled by positive scalar regularization; attainment is not assumed. -/
theorem _root_.Matrix.PosSemidef.isGLB_determinantTraceObjectiveSet
    {M : Matrix n n K} (hN : 0 < Fintype.card n) (hM : M.PosSemidef) :
    IsGLB (determinantTraceObjectiveSet M) (RCLike.re M.det) := by
  refine ⟨hM.re_det_mem_lowerBounds_determinantTraceObjectiveSet hN, ?_⟩
  intro b hb
  have hbound (δ : ℝ) (hδ : 0 < δ) :
      b ≤ RCLike.re (M + δ • (1 : Matrix n n K)).det := by
    have hreg : (M + δ • (1 : Matrix n n K)).PosDef :=
      Matrix.PosDef.posSemidef_add hM (Matrix.PosDef.one.smul hδ)
    obtain ⟨Y, hY, hYdet, hobj⟩ :=
      hreg.exists_det_one_objective_eq_re_det hN
    have htr_nonneg : 0 ≤ RCLike.re (Y * M).trace :=
      hY.posSemidef.re_trace_mul_nonneg hM
    have horder : M ≤ M + δ • (1 : Matrix n n K) :=
      le_add_of_nonneg_right (smul_nonneg hδ.le zero_le_one)
    have htr_le : RCLike.re (Y * M).trace ≤
        RCLike.re (Y * (M + δ • (1 : Matrix n n K))).trace :=
      by
        have h := hY.posSemidef.re_trace_mul_nonneg (Matrix.le_iff.mp horder)
        simpa only [Matrix.mul_sub, Matrix.trace_sub, map_sub, sub_nonneg] using h
    have hbY : b ≤
        (RCLike.re (Y * M).trace / (Fintype.card n : ℝ)) ^ Fintype.card n :=
      hb ⟨Y, hY, hYdet, rfl⟩
    exact hbY.trans ((pow_le_pow_left₀
      (div_nonneg htr_nonneg (Nat.cast_nonneg _))
      (div_le_div_of_nonneg_right htr_le (Nat.cast_nonneg _))
      (Fintype.card n)).trans_eq hobj.symm)
  have hcont : Continuous
      (fun δ : ℝ => RCLike.re (M + δ • (1 : Matrix n n K)).det) :=
    RCLike.continuous_re.comp
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hlim : Tendsto
      (fun δ : ℝ => RCLike.re (M + δ • (1 : Matrix n n K)).det)
      (𝓝[>] 0) (𝓝 (RCLike.re M.det)) := by
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  exact ge_of_tendsto hlim
    (Eventually.mono self_mem_nhdsWithin fun δ hδ => hbound δ hδ)

end NLAlib

open scoped BigOperators ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite matrix with trace equal to its dimension and determinant
at least `exp (-eps)`, for $\varepsilon\le 1/6$, has squared Frobenius distance from
the identity at most `6 * eps`. The trace and determinant are real; their real
parts express the statement uniformly over `ℝ` and `ℂ`. -/
theorem _root_.Matrix.PosDef.frobNorm_sub_one_sq_le_six_mul_of_exp_neg_le_det
    {A : Matrix n n 𝕜} (hA : A.PosDef) (eps : ℝ)
    (htr : RCLike.re A.trace = (Fintype.card n : ℝ))
    (heps : eps ≤ 1 / 6) (hdet : Real.exp (-eps) ≤ RCLike.re A.det) :
    (frobNorm (A - 1) ^ 2) ≤ 6 * eps := by
  let eig : n → ℝ := hA.isHermitian.eigenvalues
  have heig_pos : ∀ i, 0 < eig i := hA.eigenvalues_pos
  have htr_sum : ∑ i, eig i = (Fintype.card n : ℝ) := by
    have hre : RCLike.re A.trace = ∑ i, eig i := by
      rw [hA.isHermitian.trace_eq_sum_eigenvalues]
      simp [eig]
    rwa [hre] at htr
  have hdet_prod : RCLike.re A.det = ∏ i, eig i := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
      RCLike.ofReal_re]
  have hscalar := Real.sum_sq_sub_one_le_six_mul_of_exp_neg_le_prod
    eig eps heig_pos htr_sum heps (hdet_prod ▸ hdet)
  have hsum : (∑ i, (eig i - 1) ^ 2) =
      (∑ i, eig i ^ 2) - 2 * (∑ i, eig i) + (Fintype.card n : ℝ) := by
    calc
      (∑ i, (eig i - 1) ^ 2) = ∑ i, (eig i ^ 2 - 2 * eig i + 1) :=
        Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, eig i ^ 2) - 2 * (∑ i, eig i) + (Fintype.card n : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp
  have hA2 : (frobNorm A ^ 2) = ∑ i, eig i ^ 2 := by
    rw [frobNorm_sq_eq_re_trace, hA.isHermitian.eq, ← pow_two]
    conv_lhs => rw [hA.isHermitian.spectral_theorem, ← map_pow]
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
    simp [eig]
  have htr1 : frobInner A (1 : Matrix n n 𝕜) = (Fintype.card n : ℝ) := by
    rw [frobInner_eq_re_trace, Matrix.mul_one, hA.isHermitian.eq]
    exact htr
  have h1 : (frobNorm (1 : Matrix n n 𝕜) ^ 2) = (Fintype.card n : ℝ) := by
    exact frobNorm_one_sq
  calc
    (frobNorm (A - 1) ^ 2) = (∑ i, eig i ^ 2) -
        2 * (Fintype.card n : ℝ) + (Fintype.card n : ℝ) := by
      rw [frobNorm_sub_sq, hA2, htr1, h1]
    _ = ∑ i, (eig i - 1) ^ 2 := by rw [hsum, htr_sum]
    _ ≤ 6 * eps := hscalar

end NLAlib
