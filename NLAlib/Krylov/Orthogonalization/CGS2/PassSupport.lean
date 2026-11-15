/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedOrthogonality
public import NLAlib.Matrix.Perturbation.BasisExtension

/-!
# A rounded classical pass against a basis with zero columns

The three error bounds of one rounded classical Gram–Schmidt pass,
`NLAlib.Krylov.Lanczos.Reorth.PassOut.norm_bounds`, use the near-orthonormality of the stored
basis only through the bound $\lVert\mathbf{V}\rVert_2 \le 1 + \eta$. This file states them
under that bound, and derives the bound from the Gram defect on the support, so that the stored
basis may have zero columns. Design: `docs/design/LowRank-BlockLanczos.md` §3.5.

## Main results

* `NLAlib.CGS2.specNorm_le_one_add_of_specNorm_gramDefect_le`: a basis whose Gram defect on the
  support is at most $\eta$ has spectral norm at most $1 + \eta$.
* `NLAlib.CGS2.passOut_norm_coefficient_error_le`, `NLAlib.CGS2.passOut_sum_norm_projection_le`,
  `NLAlib.CGS2.passOut_norm_bounds`: the bounds of one pass under a bound of the spectral norm.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.CGS2

open Ops Krylov.Lanczos Krylov.Lanczos.Reorth

variable {K : Type} [Inhabited K]

omit [Inhabited K] in
/-- A real matrix $\mathbf{V}$ whose Gram defect on the support has spectral norm at most
$\eta \ge 0$ has $\lVert\mathbf{V}\rVert_2 \le 1 + \eta$: its nonzero columns
$\mathbf{V}_e$ satisfy $\lVert\mathbf{V}_e^{\mathsf{T}}\mathbf{V}_e - \mathbf{I}\rVert_2
\le \eta$, and the zero columns do not change $\lVert\mathbf{V}^{\mathsf{T}}\mathbf{x}\rVert$. -/
theorem specNorm_le_one_add_of_specNorm_gramDefect_le {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {V : Matrix (Fin n) ι ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hV : specNorm (gramDefect V) ≤ η) : specNorm V ≤ 1 + η := by
  classical
  let e : Fin (Fintype.card {i // V.col i ≠ 0}) → ι :=
    fun j => ((Fintype.equivFin {i // V.col i ≠ 0}).symm j : ι)
  have he : Function.Injective e :=
    Subtype.val_injective.comp (Fintype.equivFin _).symm.injective
  have hne : ∀ j, V.col (e j) ≠ 0 := fun j => ((Fintype.equivFin {i // V.col i ≠ 0}).symm j).2
  have hz : ∀ i, i ∉ Set.range e → V.col i = 0 := by
    intro i hi
    by_contra h
    exact hi ⟨Fintype.equivFin {i // V.col i ≠ 0} ⟨i, h⟩, by simp [e]⟩
  have hVe : specNorm (V.submatrix id e) ≤ 1 + η :=
    (specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le
      ((specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect V he hne).trans hV)).trans
      (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)
  rw [← specNorm_transpose]
  refine (specNorm_le_iff (by linarith)).2 fun x => ?_
  have hsum : ∑ j, ‖((V.submatrix id e)ᵀ *ᵥ x) j‖ ^ 2 = ∑ i, ‖(Vᵀ *ᵥ x) i‖ ^ 2 := by
    refine Fintype.sum_of_injective e he _ _ (fun i hi => ?_) fun j => rfl
    have h0 : (Vᵀ *ᵥ x) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      exact Finset.sum_eq_zero fun r _ => by
        rw [show V r i = 0 from congrFun (hz i hi) r, zero_mul]
    rw [h0, norm_zero, zero_pow two_ne_zero]
  have hnorm : ‖WithLp.toLp 2 (Vᵀ *ᵥ x)‖ = ‖WithLp.toLp 2 ((V.submatrix id e)ᵀ *ᵥ x)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact congrArg Real.sqrt hsum.symm
  rw [hnorm]
  exact (norm_toLp_mulVec_le _ x).trans
    (mul_le_mul_of_nonneg_right (by rw [specNorm_transpose]; exact hVe) (norm_nonneg _))

/-- The dot errors of one classical pass, for a stored basis $\mathbf{V}$ of $k$ columns with
$\lVert\mathbf{V}\rVert_2 \le 1 + \eta$: the computed coefficients $\mathbf{h}$ satisfy
$\lVert\mathbf{h} - \mathbf{V}^{\mathsf{T}}\mathbf{w}\rVert \le
(k+1)e_d(1+\eta)\lVert\mathbf{w}\rVert$.
The form of `NLAlib.Krylov.Lanczos.Reorth.PassOut.norm_coefficient_error_le` without
orthonormality. -/
theorem passOut_norm_coefficient_error_le {dec : K → ℝ}
    {ed ea η : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hd : 0 ≤ ed) (hη : 0 ≤ η)
    (hspec : specNorm (basisMatrix dec n qs k) ≤ 1 + η) :
    ‖WithLp.toLp 2 ((fun j : Fin k => dec (vec hs j)) -
      (basisMatrix dec n qs k)ᵀ *ᵥ decv dec n ws)‖ ≤
      (k + 1) * ed * (1 + η) * ‖WithLp.toLp 2 (decv dec n ws)‖ := by
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

/-- The coefficient-weighted column norms of one classical pass, for a stored basis
$\mathbf{V}$ of $k$ columns with $\lVert\mathbf{V}\rVert_2 \le 1 + \eta$:
$\sum_j \lvert h_j\rvert\lVert\mathbf{v}_j\rVert \le k(1+e_d)(1+\eta)^2\lVert\mathbf{w}\rVert$.
The form of `NLAlib.Krylov.Lanczos.Reorth.PassOut.sum_norm_projection_le` without
orthonormality. -/
theorem passOut_sum_norm_projection_le {dec : K → ℝ}
    {ed ea η : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hd : 0 ≤ ed) (hη : 0 ≤ η)
    (hspec : specNorm (basisMatrix dec n qs k) ≤ 1 + η) :
    ∑ j ∈ Finset.range k, |dec (vec hs j)| *
      ‖WithLp.toLp 2 (fun i : Fin n => dec (vec qs (j * n + i)))‖ ≤
      k * (1 + ed) * (1 + η) ^ 2 * ‖WithLp.toLp 2 (decv dec n ws)‖ := by
  let Q := basisMatrix dec n qs k
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

/-- The three bounds of one rounded classical pass under a bound of the spectral norm. For
a stored basis $\mathbf{V}$ of $k$ columns with $\lVert\mathbf{V}\rVert_2 \le 1 + \eta$,
dot errors $e_d \ge 0$, update errors $e_a \ge 0$ and
$(k+1)e_d(1+\eta)^2 + ((1+e_a)^k - 1)(1 + k(1+e_d)(1+\eta)^2) \le c$, the coefficients
$\mathbf{h}$ and the output $\mathbf{w}'$ of the pass on $\mathbf{w}$ satisfy
$\lVert\mathbf{h} - \mathbf{V}^{\mathsf{T}}\mathbf{w}\rVert \le c\lVert\mathbf{w}\rVert$,
$\lVert\mathbf{w} - \mathbf{V}\mathbf{h} - \mathbf{w}'\rVert \le c\lVert\mathbf{w}\rVert$ and
$\lVert\mathbf{w}' - (\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w})\rVert \le
c\lVert\mathbf{w}\rVert$. The form of `NLAlib.Krylov.Lanczos.Reorth.PassOut.norm_bounds` without
orthonormality: the stored columns may be zero. -/
theorem passOut_norm_bounds {dec : K → ℝ}
    {ed ea η c : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hd : 0 ≤ ed) (ha : 0 ≤ ea) (hη : 0 ≤ η)
    (hbudget : (k + 1) * ed * (1 + η) ^ 2 +
      ((1 + ea) ^ k - 1) * (1 + k * (1 + ed) * (1 + η) ^ 2) ≤ c)
    (hspec : specNorm (basisMatrix dec n qs k) ≤ 1 + η) :
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
  have hsum := passOut_sum_norm_projection_le h hd hη hspec
  have hcoef := passOut_norm_coefficient_error_le h hd hη hspec
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

end NLAlib.CGS2
