/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Spec
public import NLAlib.Krylov.Lanczos.Reorth.SweepBounds
public import NLAlib.Matrix.FinitePrecision.ClassicalGramSchmidt

/-!
# Orthogonality of the actual sequential-update classical passes

The program forms all dot coefficients before its sequential AXPY updates. Its actual local
witnesses give the three norm bounds required by the existing pure two-pass algebra. The
single-pass envelope here is deliberately derived from that AXPY chain, rather than borrowed
from the different matrix-update implementation. Summed coefficients are exact ghost data.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.PassOut.norm_bounds`: three actual single-pass error bounds.
* `NLAlib.Krylov.Lanczos.Reorth.TwoPassOut.isOrthErr`: the existing orthogonalization interface
  for actual two-pass output, with explicit numerical budgets and no execution premise.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops
open scoped Matrix

/-- A computed classical coefficient is bounded by its dot allowance and the actual column
norm. No orthonormality assumption is required. [Higham2002, §3.1]. -/
theorem PassOut.abs_coefficient_le {K : Type} [Inhabited K] {dec : K → ℝ}
    {ed ea : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hd : 0 ≤ ed) (j : Fin k) :
    |dec (vec hs j)| ≤ (1 + ed) *
      ‖WithLp.toLp 2 ((basisMatrix dec n qs k).col j)‖ * ‖WithLp.toLp 2 (decv dec n ws)‖ := by
  have he := h.abs_sub_dotProduct_le hd j.isLt
  have hdprod := EuclideanSpace.abs_dotProduct_le_norm
    ((basisMatrix dec n qs k).col j) (decv dec n ws)
  have htri := abs_add_le
    (dec (vec hs j) - (basisMatrix dec n qs k).col j ⬝ᵥ decv dec n ws)
    ((basisMatrix dec n qs k).col j ⬝ᵥ decv dec n ws)
  rw [sub_add_cancel] at htri
  change |dec (vec hs j) - (basisMatrix dec n qs k).col j ⬝ᵥ decv dec n ws| ≤
    ed * ‖WithLp.toLp 2 ((basisMatrix dec n qs k).col j)‖ *
      ‖WithLp.toLp 2 (decv dec n ws)‖ at he
  nlinarith

/-- Aggregate the actual dot errors in one classical pass. A near-orthonormal input basis
bounds each column by `1+eta`; the dimension factor is a conservative sum bound. -/
theorem PassOut.norm_coefficient_error_le {K : Type} [Inhabited K] {dec : K → ℝ}
    {ed ea η : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hd : 0 ≤ ed) (hη : 0 ≤ η)
    (hV : specNorm ((basisMatrix dec n qs k)ᵀ * basisMatrix dec n qs k - 1) ≤ η) :
    ‖WithLp.toLp 2 ((fun j : Fin k => dec (vec hs j)) -
      (basisMatrix dec n qs k)ᵀ *ᵥ decv dec n ws)‖ ≤
      (k + 1) * ed * (1 + η) * ‖WithLp.toLp 2 (decv dec n ws)‖ := by
  have hspec : specNorm (basisMatrix dec n qs k) ≤ 1 + η :=
    (specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV).trans
      (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)
  let a := ed * (1 + η) * ‖WithLp.toLp 2 (decv dec n ws)‖
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have he : ∀ j : Fin k, |((fun j : Fin k => dec (vec hs j)) -
      (basisMatrix dec n qs k)ᵀ *ᵥ decv dec n ws) j| ≤ a := by
    intro j
    have hc := (norm_toLp_col_le_specNorm (basisMatrix dec n qs k) j).trans hspec
    exact (h.abs_sub_dotProduct_le hd j.isLt).trans (by
      change ed * ‖WithLp.toLp 2 ((basisMatrix dec n qs k).col j)‖ *
        ‖WithLp.toLp 2 (decv dec n ws)‖ ≤ a
      dsimp only [a]
      gcongr)
  have hsq : ‖WithLp.toLp 2 ((fun j : Fin k => dec (vec hs j)) -
      (basisMatrix dec n qs k)ᵀ *ᵥ decv dec n ws)‖ ^ 2 ≤ (k : ℝ) * a ^ 2 := by
    rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq]
    calc
      _ ≤ ∑ _j : Fin k, a ^ 2 := Finset.sum_le_sum fun j _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he j) 2
      _ = (k : ℝ) * a ^ 2 := by simp
  have hk : (k : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (k : ℝ)]
  have hmul := mul_le_mul_of_nonneg_right hk (sq_nonneg a)
  have hn := norm_nonneg (WithLp.toLp 2 ((fun j : Fin k => dec (vec hs j)) -
    (basisMatrix dec n qs k)ᵀ *ᵥ decv dec n ws))
  have hka : 0 ≤ ((k : ℝ) + 1) * a := by positivity
  have hrhs : (k + 1) * ed * (1 + η) * ‖WithLp.toLp 2 (decv dec n ws)‖ =
      ((k : ℝ) + 1) * a := by dsimp only [a]; ring
  rw [hrhs]
  nlinarith

/-- The actual coefficient-weighted column norms have a size-only envelope under a nearly
orthonormal input basis. This bounds the sequential update error without assuming the basis
is exactly orthogonal or replacing the AXPY chain by a matrix update. -/
theorem PassOut.sum_norm_projection_le {K : Type} [Inhabited K] {dec : K → ℝ}
    {ed ea η : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hd : 0 ≤ ed) (hη : 0 ≤ η)
    (hV : specNorm ((basisMatrix dec n qs k)ᵀ * basisMatrix dec n qs k - 1) ≤ η) :
    ∑ j ∈ Finset.range k, |dec (vec hs j)| *
      ‖WithLp.toLp 2 (fun i : Fin n => dec (vec qs (j * n + i)))‖ ≤
      k * (1 + ed) * (1 + η) ^ 2 * ‖WithLp.toLp 2 (decv dec n ws)‖ := by
  let Q := basisMatrix dec n qs k
  have hspec : specNorm Q ≤ 1 + η :=
    (specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV).trans
      (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)
  have hcol (j : Fin k) : ‖WithLp.toLp 2 (Q.col j)‖ ≤ 1 + η :=
    (norm_toLp_col_le_specNorm Q j).trans hspec
  have hj (j : Fin k) : |dec (vec hs j)| * ‖WithLp.toLp 2 (Q.col j)‖ ≤
      (1 + ed) * (1 + η) ^ 2 * ‖WithLp.toLp 2 (decv dec n ws)‖ := by
    calc
      _ ≤ ((1 + ed) * (1 + η) * ‖WithLp.toLp 2 (decv dec n ws)‖) * (1 + η) :=
        mul_le_mul ((h.abs_coefficient_le hd j).trans (by gcongr; exact hcol j))
          (hcol j) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [← Fin.sum_univ_eq_sum_range]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hj j)
  have hcol_eq (j : Fin k) : Q.col j =
      (fun i : Fin n => dec (vec qs (j * n + i))) := rfl
  simp only [hcol_eq] at hs
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_assoc] using hs

/-- The actual sequential-AXPY pass supplies coefficient, representation and ideal-projection
error bounds. The explicit allowance includes accumulated update error and coefficient error;
its constants do not come from the distinct matrix-update implementation. -/
theorem PassOut.norm_bounds {K : Type} [Inhabited K] {dec : K → ℝ}
    {ed ea η c : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hd : 0 ≤ ed) (ha : 0 ≤ ea) (hη : 0 ≤ η)
    (hbudget : (k + 1) * ed * (1 + η) ^ 2 +
      ((1 + ea) ^ k - 1) * (1 + k * (1 + ed) * (1 + η) ^ 2) ≤ c)
    (hV : specNorm ((basisMatrix dec n qs k)ᵀ * basisMatrix dec n qs k - 1) ≤ η) :
    ‖WithLp.toLp 2 ((fun j : Fin k => dec (vec hs j)) -
      (basisMatrix dec n qs k)ᵀ *ᵥ decv dec n ws)‖ ≤ c * ‖WithLp.toLp 2 (decv dec n ws)‖ ∧
    ‖WithLp.toLp 2 (decv dec n ws - basisMatrix dec n qs k *ᵥ
      (fun j : Fin k => dec (vec hs j)) - decv dec n ws')‖ ≤
      c * ‖WithLp.toLp 2 (decv dec n ws)‖ ∧
    ‖WithLp.toLp 2 (decv dec n ws' - (decv dec n ws - basisMatrix dec n qs k *ᵥ
      ((basisMatrix dec n qs k)ᵀ *ᵥ decv dec n ws)))‖ ≤
      c * ‖WithLp.toLp 2 (decv dec n ws)‖ := by
  let Q := basisMatrix dec n qs k
  let w := decv dec n ws
  let H : Fin k → ℝ := fun j => dec (vec hs j)
  let g := (1 + ea) ^ k - 1
  let D := (k + 1) * ed * (1 + η) ^ 2
  let U := g * (1 + k * (1 + ed) * (1 + η) ^ 2)
  have hg : 0 ≤ g := sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hb : D + U ≤ c := hbudget
  have hspec : specNorm Q ≤ 1 + η :=
    (specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV).trans
      (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)
  have hsum := h.sum_norm_projection_le hd hη hV
  have hcoef := h.norm_coefficient_error_le hd hη hV
  have hcoefD : ‖WithLp.toLp 2 (H - Qᵀ *ᵥ w)‖ ≤ D * ‖WithLp.toLp 2 w‖ :=
    hcoef.trans (by dsimp only [D]; gcongr; nlinarith)
  have hres : ‖WithLp.toLp 2 (decv dec n ws' - (w - Q *ᵥ H))‖ ≤
      U * ‖WithLp.toLp 2 w‖ := by
    have hp := h.norm_sub_sub_sum_le ha
    have heq : (∑ j ∈ Finset.range k, dec (vec hs j) •
        (fun i : Fin n => dec (vec qs (j * n + i)))) = Q *ᵥ H := by
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Q, H, basisMatrix,
        Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [heq] at hp
    refine hp.trans ?_
    calc
      _ ≤ g * (‖WithLp.toLp 2 w‖ +
          k * (1 + ed) * (1 + η) ^ 2 * ‖WithLp.toLp 2 w‖) := by
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hg
      _ = U * ‖WithLp.toLp 2 w‖ := by dsimp only [U]; ring
  have hf : ‖WithLp.toLp 2 (decv dec n ws' - (w - Q *ᵥ (Qᵀ *ᵥ w)))‖ ≤
      (D + U) * ‖WithLp.toLp 2 w‖ := by
    have heq : decv dec n ws' - (w - Q *ᵥ (Qᵀ *ᵥ w)) =
        (decv dec n ws' - (w - Q *ᵥ H)) - Q *ᵥ (H - Qᵀ *ᵥ w) := by
      rw [Matrix.mulVec_sub]
      abel
    rw [heq, WithLp.toLp_sub]
    refine (norm_sub_le _ _).trans ?_
    have hprod := (norm_toLp_mulVec_le Q (H - Qᵀ *ᵥ w)).trans
      (mul_le_mul hspec hcoef (norm_nonneg _) (by linarith))
    have hprodD : ‖WithLp.toLp 2 (Q *ᵥ (H - Qᵀ *ᵥ w))‖ ≤ D * ‖WithLp.toLp 2 w‖ := by
      refine hprod.trans_eq ?_
      dsimp only [D]
      ring
    nlinarith
  have hDc : D ≤ c := (le_add_of_nonneg_right hU).trans hb
  have hUc : U ≤ c := (le_add_of_nonneg_left hD).trans hb
  refine ⟨hcoefD.trans (mul_le_mul_of_nonneg_right hDc (norm_nonneg _)), ?_,
    hf.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))⟩
  have heq : w - Q *ᵥ H - decv dec n ws' = -(decv dec n ws' - (w - Q *ᵥ H)) := by abel
  rw [heq, WithLp.toLp_neg, norm_neg]
  exact hres.trans (mul_le_mul_of_nonneg_right hUc (norm_nonneg _))

/-- The actual two classical passes meet the existing orthogonalization guarantee with
first-order output terms and a quadratic input term. The single-pass allowance is derived
from the dot and sequential-AXPY budgets. Ghost coefficients are added exactly; the program
need not retain their words. No success, nonbreakdown or global orthogonality is assumed.
[GiraudLangouRozloznikVandenEshof2005, Theorem 2]. -/
theorem TwoPassOut.isOrthErr {K : Type} [Inhabited K] {dec : K → ℝ}
    {ed ea η c : ℝ} {n k : ℕ} {qs ws ws' : List K}
    (h : TwoPassOut dec ed ea n k qs ws ws') (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100) (hc : c ≤ 1 / 100)
    (hbudget : (k + 1) * ed * (1 + η) ^ 2 +
      ((1 + ea) ^ k - 1) * (1 + k * (1 + ed) * (1 + η) ^ 2) ≤ c) :
    ∃ mid h₁ h₂ : List K, PassOut dec ed ea n k qs ws mid h₁ ∧
      PassOut dec ed ea n k qs mid ws' h₂ ∧
      IsOrthErr η (2 * c) (3 * c) (2 * (η + c) ^ 2)
        (basisMatrix dec n qs k) (decv dec n ws)
        (fun j : Fin k => dec (vec h₁ j) + dec (vec h₂ j)) (decv dec n ws') := by
  obtain ⟨mid, h₁, h₂, hp₁, hp₂⟩ := h
  have hγ : 0 ≤ (1 + ea) ^ k - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hc0 : 0 ≤ c := (by positivity : 0 ≤ (k + 1 : ℝ) * ed * (1 + η) ^ 2 +
    ((1 + ea) ^ k - 1) * (1 + k * (1 + ed) * (1 + η) ^ 2)).trans hbudget
  refine ⟨mid, h₁, h₂, hp₁, hp₂, isOrthErr_of_two_passes hη hc (u := 0) le_rfl
    (by simpa using hc0) (fun hV => hp₁.norm_bounds hd ha hη₀ hbudget hV)
    (fun hV => hp₂.norm_bounds hd ha hη₀ hbudget hV) ?_⟩
  intro j
  simp only [sub_self, abs_zero, zero_mul, le_refl]

end NLAlib.Krylov.Lanczos.Reorth
