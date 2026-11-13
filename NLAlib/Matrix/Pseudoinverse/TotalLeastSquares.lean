/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Norms.Block
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Order.OrderClosed

/-!
# Total least squares

The augmented data matrix has domain indexed by `n ⊕ Unit`, so the last coordinate
distinguishes finite solutions from limiting directions. All Frobenius correction costs
refer to the original perturbed equations. Adapted from the total least squares proofs
in the original NLAlib, commit `77514ce42a0e437d837797a063ac161f41022730`.

## Main results

* `NLAlib.isGLB_totalLeastSquaresCosts`: the infimum including unattained problems.
* `NLAlib.isTotalLeastSquaresSolution_iff_exists`: all optimal finite solutions.
* `NLAlib.isTotalLeastSquaresSolution_iff_eq_of_lt_singularValues`: unique shifted normal solution.
-/

@[expose] public section

open Matrix Filter Topology
open scoped MatrixOrder ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- Attainable squared Frobenius costs for total least squares with augmented data
$\mathbf{C}=[\mathbf{A}\ \mathbf{b}]$. A correction is feasible when its corrected
system has a finite solution. [GolubVanLoan2013, §6.3]. -/
def totalLeastSquaresCosts (C : Matrix m (n ⊕ Unit) 𝕜) : Set ℝ :=
  {a | ∃ (x : n → 𝕜) (D : Matrix m (n ⊕ Unit) 𝕜),
    (C + D) *ᵥ Sum.elim x (fun _ => -1) = 0 ∧ frobNorm D ^ 2 = a}

/-- A finite solution of total least squares admits a consistent data correction whose
squared Frobenius norm is minimal among all consistent corrections.
[GolubVanLoan2013, §6.3]. -/
def IsTotalLeastSquaresSolution (A : Matrix m n 𝕜) (b : m → 𝕜) (x : n → 𝕜) : Prop :=
  ∃ D : Matrix m (n ⊕ Unit) 𝕜,
    (fromCols A (replicateCol Unit b) + D) *ᵥ Sum.elim x (fun _ => -1) = 0 ∧
      IsLeast (totalLeastSquaresCosts (fromCols A (replicateCol Unit b))) (frobNorm D ^ 2)

/-- For an assembled augmented matrix $\mathbf{C}=[\mathbf{A}\ \mathbf{b}]$,
an optimal correction of $\mathbf{C}$ gives a solution for its two column blocks.
[GolubVanLoan2013, §6.3]. -/
theorem isTotalLeastSquaresSolution_toCols₁_iff (C : Matrix m (n ⊕ Unit) 𝕜) (x : n → 𝕜) :
    IsTotalLeastSquaresSolution C.toCols₁ (C.col (.inr ())) x ↔
      ∃ D : Matrix m (n ⊕ Unit) 𝕜, (C + D) *ᵥ Sum.elim x (fun _ => -1) = 0 ∧
        IsLeast (totalLeastSquaresCosts C) (frobNorm D ^ 2) := by
  have h : fromCols C.toCols₁ (replicateCol Unit (C.col (.inr ()))) = C := by
    ext i j
    cases j with
    | inl j => rfl
    | inr j => cases j; rfl
  simp only [IsTotalLeastSquaresSolution, h]

omit [Fintype m] in
/-- Consistency of the augmented perturbation $[\mathbf{E}\ \mathbf{f}]$ is the
equation $(\mathbf{A}+\mathbf{E})\mathbf{x}=\mathbf{b}+\mathbf{f}$. -/
theorem fromCols_add_mulVec_eq_zero_iff (A E : Matrix m n 𝕜) (b f : m → 𝕜) (x : n → 𝕜) :
    (fromCols A (replicateCol Unit b) + fromCols E (replicateCol Unit f)) *ᵥ
      Sum.elim x (fun _ => -1) = 0 ↔ (A + E) *ᵥ x = b + f := by
  have h (w : m → 𝕜) : replicateCol Unit w *ᵥ (fun _ => (-1 : 𝕜)) = -w := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  simp only [Matrix.add_mulVec, fromCols_mulVec_sumElim, h]
  constructor <;> intro he <;> linear_combination he

private abbrev direction (x : n → 𝕜) : n ⊕ Unit → 𝕜 := Sum.elim x (fun _ => -1)
private abbrev affine (v : n ⊕ Unit → 𝕜) : n → 𝕜 := fun i => -v (.inl i) / v (.inr ())
private noncomputable abbrev value (C : Matrix m (n ⊕ Unit) 𝕜) :=
  eigenvalue (Cᴴ * C) (Fintype.card n)

omit [Fintype n] in
private theorem direction_ne_zero (x : n → 𝕜) : direction x ≠ 0 := fun h =>
  (by simp : (-1 : 𝕜) ≠ 0) (congrFun h (.inr ()))

omit [Fintype n] in
private theorem direction_affine {v : n ⊕ Unit → 𝕜} (hl : v (.inr ()) ≠ 0) :
    direction (affine v) = -(v (.inr ()))⁻¹ • v := by
  ext i
  cases i with
  | inl i => simp [direction, affine, div_eq_mul_inv, mul_comm]
  | inr i => cases i; simp [direction, hl]

private noncomputable abbrev normalized {ι : Type*} [Fintype ι] (v : ι → 𝕜) : ι → 𝕜 :=
  (NormedSpace.normalize (WithLp.toLp 2 v)).ofLp

private theorem normalized_eq {ι : Type*} [Fintype ι] (v : ι → 𝕜) :
    normalized v = ((‖WithLp.toLp 2 v‖ : 𝕜)⁻¹) • v := by
  ext i
  simp [normalized, NormedSpace.normalize, RCLike.real_smul_eq_coe_mul]

private theorem norm_normalized {ι : Type*} [Fintype ι] {v : ι → 𝕜} (hv : v ≠ 0) :
    ‖WithLp.toLp 2 (normalized v)‖ = 1 :=
  NormedSpace.norm_normalize ((WithLp.toLp_eq_zero 2).not.mpr hv)

private theorem normalized_apply_ne_zero {ι : Type*} [Fintype ι] {v : ι → 𝕜}
    {i : ι} (hi : v i ≠ 0) : normalized v i ≠ 0 := by
  have h : ‖WithLp.toLp 2 v‖ ≠ 0 := norm_ne_zero_iff.mpr
    ((WithLp.toLp_eq_zero 2).not.mpr fun hh => hi (congrFun hh i))
  rw [normalized_eq]
  exact mul_ne_zero (inv_ne_zero (RCLike.ofReal_ne_zero.mpr h)) hi

private theorem affine_normalized_direction (x : n → 𝕜) :
    affine (normalized (direction x)) = x := by
  have h : ‖WithLp.toLp 2 (direction x)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr (direction_ne_zero x))
  ext i
  rw [normalized_eq]
  change -(((‖WithLp.toLp 2 (direction x)‖ : 𝕜)⁻¹) * x i) /
    (((‖WithLp.toLp 2 (direction x)‖ : 𝕜)⁻¹) * (-1)) = x i
  field_simp [RCLike.ofReal_ne_zero.mpr h]

private theorem gram_min_le (C : Matrix m (n ⊕ Unit) 𝕜) {v : n ⊕ Unit → 𝕜}
    (hv : ‖WithLp.toLp 2 v‖ = 1) : value C ≤ ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 := by
  have hj : Fintype.card n + 1 = Fintype.card (n ⊕ Unit) := by simp
  simpa only [hv, one_pow, mul_one, quadForm_conjTranspose_mul_self, RCLike.ofReal_re] using
    (Matrix.isHermitian_conjTranspose_mul_self C).eigenvalue_last_mul_le_re_quadForm hj v

private theorem gram_min_eq_iff (C : Matrix m (n ⊕ Unit) 𝕜) {v : n ⊕ Unit → 𝕜}
    (hv : ‖WithLp.toLp 2 v‖ = 1) :
    ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 = value C ↔ (Cᴴ * C) *ᵥ v = value C • v := by
  classical
  have hj : Fintype.card n + 1 = Fintype.card (n ⊕ Unit) := by simp
  let H := Cᴴ * C - value C • 1
  have hp : H.PosSemidef :=
    (Matrix.isHermitian_conjTranspose_mul_self C).eigenvalue_last_smul_one_le hj
  have he : RCLike.re (quadForm H v) = ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 - value C := by
    rw [show H = _ from rfl, quadForm_sub_left, map_sub, quadForm_conjTranspose_mul_self,
      RCLike.ofReal_re, re_quadForm_real_smul_one, hv, one_pow, mul_one]
  have hz : quadForm H v = 0 ↔ RCLike.re (quadForm H v) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h => by rw [← hp.isHermitian.coe_re_quadForm, h]; simp⟩
  rw [← sub_eq_zero, ← he, ← hz, quadForm, hp.dotProduct_mulVec_zero_iff]
  simp only [H, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

private theorem exists_minimizer (C : Matrix m (n ⊕ Unit) 𝕜) :
    ∃ v : n ⊕ Unit → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧ (Cᴴ * C) *ᵥ v = value C • v :=
  (Matrix.isHermitian_conjTranspose_mul_self C).exists_norm_eq_one_and_mulVec_eq (by simp)

private abbrev correction {ι : Type*} [Fintype ι] (C : Matrix m ι 𝕜) (v : ι → 𝕜) :=
  -Matrix.vecMulVec (C *ᵥ v) (star v)

omit [Fintype m] in
private theorem correction_mulVec {ι : Type*} [Fintype ι] (C : Matrix m ι 𝕜)
    {v : ι → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1) : correction C v *ᵥ v = -(C *ᵥ v) := by
  have hdot : star v ⬝ᵥ v = (1 : 𝕜) := by
    rw [EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, hv]
    norm_num
  rw [correction, Matrix.neg_mulVec, Matrix.vecMulVec_mulVec, hdot, MulOpposite.op_one, one_smul]

private theorem frobNorm_correction {ι : Type*} [Fintype ι] (C : Matrix m ι 𝕜)
    {v : ι → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1) :
    frobNorm (correction C v) = ‖WithLp.toLp 2 (C *ᵥ v)‖ := by
  have hs : ‖WithLp.toLp 2 (star v)‖ = ‖WithLp.toLp 2 v‖ := by
    simp [EuclideanSpace.norm_eq]
  rw [correction, frobNorm_neg, frobNorm_vecMulVec, hs, hv, mul_one]

omit [Fintype m] in
/-- Subtracting the rank-at-most-one outer product along a unit direction whose last coordinate
is nonzero makes the corrected system consistent at the associated finite solution. -/
theorem sub_vecMulVec_mulVec_eq_zero (C : Matrix m (n ⊕ Unit) 𝕜) {v : n ⊕ Unit → 𝕜}
    (hv : ‖WithLp.toLp 2 v‖ = 1) (hl : v (.inr ()) ≠ 0) :
    (C - vecMulVec (C *ᵥ v) (star v)) *ᵥ
      Sum.elim (fun i => -v (.inl i) / v (.inr ())) (fun _ => -1) = 0 := by
  rw [sub_eq_add_neg]
  change (C + correction C v) *ᵥ direction (affine v) = 0
  rw [direction_affine hl, Matrix.mulVec_smul, Matrix.add_mulVec, correction_mulVec C hv,
    add_neg_cancel, smul_zero]

private theorem cost_le (C D : Matrix m (n ⊕ Unit) 𝕜) {x : n → 𝕜}
    (hx : (C + D) *ᵥ direction x = 0) :
    ‖WithLp.toLp 2 (C *ᵥ normalized (direction x))‖ ^ 2 ≤ frobNorm D ^ 2 := by
  let v := normalized (direction x)
  have hv : ‖WithLp.toLp 2 v‖ = 1 := norm_normalized (direction_ne_zero x)
  have he : (C + D) *ᵥ v = 0 := by
    dsimp only [v]
    rw [normalized_eq, Matrix.mulVec_smul, hx, smul_zero]
  have hd : D *ᵥ v = -(C *ᵥ v) := by rw [Matrix.add_mulVec] at he; linear_combination he
  have h := norm_toLp_mulVec_le_frobNorm_mul D v
  rw [hd, WithLp.toLp_neg, norm_neg, hv, mul_one] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem continuousAt_normalized {ι : Type*} [Fintype ι] {v : ι → 𝕜} (hv : v ≠ 0) :
    ContinuousAt (normalized : (ι → 𝕜) → (ι → 𝕜)) v := by
  have hn : ‖WithLp.toLp 2 v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hv)
  simp_rw [funext normalized_eq]
  apply continuousAt_pi.mpr
  intro i
  change ContinuousAt (fun w : ι → 𝕜 => (‖WithLp.toLp 2 w‖ : 𝕜)⁻¹ * w i) v
  apply ContinuousAt.mul _ (continuous_apply i).continuousAt
  have hc : ContinuousAt (fun w : ι → 𝕜 => (‖WithLp.toLp 2 w‖ : 𝕜)) v := by fun_prop
  exact hc.inv₀ (RCLike.ofReal_ne_zero.mpr hn)

/-- **Total least squares infimum.** For augmented data $\mathbf{C}$, the infimum of the
squared Frobenius norms of feasible corrections is the least eigenvalue of its full domain
Gram matrix. This allows nonattainment and repeated minimum eigenvalues.
[GolubVanLoan2013, §6.3]. The statement also covers wide and empty-row data.
Result: total-least-squares-svd -/
theorem isGLB_totalLeastSquaresCosts (C : Matrix m (n ⊕ Unit) 𝕜) :
    IsGLB (totalLeastSquaresCosts C) (eigenvalue (Cᴴ * C) (Fintype.card n)) := by
  classical
  constructor
  · rintro a ⟨x, D, hD, rfl⟩
    exact (gram_min_le C (norm_normalized (direction_ne_zero x))).trans (cost_le C D hD)
  · intro a ha
    obtain ⟨v, hv, he⟩ := exists_minimizer C
    have hvalue := (gram_min_eq_iff C hv).mpr he
    by_cases hl : v (.inr ()) ≠ 0
    · have hc : frobNorm (correction C v) ^ 2 ∈ totalLeastSquaresCosts C :=
        ⟨affine v, correction C v, by
          simpa only [sub_eq_add_neg] using sub_vecMulVec_mulVec_eq_zero C hv hl, rfl⟩
      simpa only [frobNorm_correction C hv, hvalue] using ha hc
    · have hz := not_ne_iff.mp hl
      let w : ℝ → (n ⊕ Unit → 𝕜) := fun t => v + (t : 𝕜) • Pi.single (.inr ()) 1
      have hwlast (t : ℝ) : w t (.inr ()) = (t : 𝕜) := by
        simp [w, hz, RCLike.real_smul_eq_coe_mul]
      have hv0 : v ≠ 0 := fun h => by simp [h] at hv
      have hw : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 v) := by
        have hc : ContinuousAt w 0 := by dsimp only [w]; fun_prop
        simpa [w] using! hc.tendsto.mono_left inf_le_left
      have hn : Tendsto (fun t => normalized (w t)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
        have hh := (continuousAt_normalized hv0).tendsto.comp hw
        simpa only [normalized_eq, hv, RCLike.ofReal_one, inv_one, one_smul,
          Function.comp_def] using! hh
      have hc : Continuous (fun u : n ⊕ Unit → 𝕜 => ‖WithLp.toLp 2 (C *ᵥ u)‖ ^ 2) := by
        fun_prop
      have hlim := hc.continuousAt.tendsto.comp hn
      rw [Function.comp_def, hvalue] at hlim
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hlast : w t (.inr ()) ≠ 0 := (hwlast t) ▸ RCLike.ofReal_ne_zero.mpr (ne_of_gt ht)
      have hnlast := normalized_apply_ne_zero hlast
      have hwt : w t ≠ 0 := fun hh => hlast (congrFun hh (.inr ()))
      have hunit := norm_normalized hwt
      have hcost : frobNorm (correction C (normalized (w t))) ^ 2 ∈ totalLeastSquaresCosts C :=
        ⟨affine (normalized (w t)), correction C _, by
            simpa only [sub_eq_add_neg] using sub_vecMulVec_mulVec_eq_zero C hunit hnlast, rfl⟩
      simpa only [frobNorm_correction C hunit] using ha hcost

/-- **Total least squares correction.** A unit least Gram eigenvector with nonzero last
coordinate gives an optimal data correction of rank at most one,
$$\mathbf{D}=-(\mathbf{C}\mathbf{v})\mathbf{v}^{\mathsf{H}}.$$
[GolubVanLoan2013, §6.3].
Result: total-least-squares-svd -/
theorem isLeast_totalLeastSquaresCosts_of_mulVec_eq (C : Matrix m (n ⊕ Unit) 𝕜)
    {v : n ⊕ Unit → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1) (hl : v (.inr ()) ≠ 0)
    (he : (Cᴴ * C) *ᵥ v = eigenvalue (Cᴴ * C) (Fintype.card n) • v) :
    IsLeast (totalLeastSquaresCosts C) (frobNorm (-vecMulVec (C *ᵥ v) (star v)) ^ 2) := by
  have hx := sub_vecMulVec_mulVec_eq_zero C hv hl
  rw [sub_eq_add_neg] at hx
  refine ⟨⟨affine v, correction C v, hx, rfl⟩, ?_⟩
  change frobNorm (correction C v) ^ 2 ∈ lowerBounds (totalLeastSquaresCosts C)
  rw [frobNorm_correction C hv, (gram_min_eq_iff C hv).mpr he]
  exact (isGLB_totalLeastSquaresCosts C).1

/-- **Total least squares solution directions.** For an augmented matrix $\mathbf{C}$,
every optimal finite solution is the negative ratio of the leading coordinates to the
last coordinate of a unit least Gram eigenvector with nonzero last coordinate:
$$x_i=-\frac{v_i}{v_{\mathrm{last}}}.$$
Every such direction gives an optimal solution. [GolubVanLoan2013, §6.3].
Result: total-least-squares-svd -/
theorem isTotalLeastSquaresSolution_iff_exists (C : Matrix m (n ⊕ Unit) 𝕜) (x : n → 𝕜) :
    IsTotalLeastSquaresSolution C.toCols₁ (C.col (.inr ())) x ↔
      ∃ v : n ⊕ Unit → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧ v (.inr ()) ≠ 0 ∧
        (Cᴴ * C) *ᵥ v = eigenvalue (Cᴴ * C) (Fintype.card n) • v ∧
        x = fun i => -v (.inl i) / v (.inr ()) := by
  rw [isTotalLeastSquaresSolution_toCols₁_iff]
  constructor
  · rintro ⟨D, hd, hmin⟩
    let v := normalized (direction x)
    have hv : ‖WithLp.toLp 2 v‖ = 1 := norm_normalized (direction_ne_zero x)
    have hl : v (.inr ()) ≠ 0 :=
      normalized_apply_ne_zero (v := direction x) (i := .inr ()) (by simp [direction])
    have he : ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 = value C :=
      le_antisymm ((cost_le C D hd).trans_eq (hmin.isGLB.unique (isGLB_totalLeastSquaresCosts C)))
        (gram_min_le C hv)
    exact ⟨v, hv, hl, (gram_min_eq_iff C hv).mp he, (affine_normalized_direction x).symm⟩
  · rintro ⟨v, hv, hl, he, rfl⟩
    have hx := sub_vecMulVec_mulVec_eq_zero C hv hl
    rw [sub_eq_add_neg] at hx
    exact ⟨correction C v, hx, isLeast_totalLeastSquaresCosts_of_mulVec_eq C hv hl he⟩

/-- For a prescribed unit direction, the unique correction of smallest Frobenius norm that
annihilates its image is the negative outer product of that image and the direction. -/
theorem frobNorm_eq_iff_of_add_mulVec_eq_zero {ι : Type*} [Fintype ι] (C D : Matrix m ι 𝕜)
    {v : ι → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1) (hD : (C + D) *ᵥ v = 0) :
    frobNorm D = ‖WithLp.toLp 2 (C *ᵥ v)‖ ↔ D = -vecMulVec (C *ᵥ v) (star v) := by
  have hd : D *ᵥ v = -(C *ᵥ v) := by rw [Matrix.add_mulVec] at hD; linear_combination hD
  have hz : (D - correction C v) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, correction_mulVec C hv, hd, sub_self]
  have horth : (D - correction C v) * (correction C v)ᴴ = 0 := by
    rw [show (correction C v)ᴴ = -vecMulVec v (star (C *ᵥ v)) by
      simp [correction, conjTranspose_vecMulVec], Matrix.mul_neg, mul_vecMulVec, hz]
    ext i j
    simp [vecMulVec]
  have hsq := frobNorm_add_sq_of_mul_conjTranspose_eq_zero horth
  rw [sub_add_cancel, frobNorm_correction C hv] at hsq
  refine ⟨fun he => ?_, fun he => he ▸ frobNorm_correction C hv⟩
  exact sub_eq_zero.mp (frobNorm_eq_zero_iff.mp (by rw [he] at hsq; nlinarith))

private abbrev augmented (A : Matrix m n 𝕜) (b : m → 𝕜) := fromCols A (replicateCol Unit b)

omit [Fintype m] in
private theorem augmented_mulVec (A : Matrix m n 𝕜) (b : m → 𝕜) (v : n ⊕ Unit → 𝕜) :
    augmented A b *ᵥ v = A *ᵥ (v ∘ Sum.inl) + v (.inr ()) • b := by
  rw [augmented, Matrix.fromCols_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]

private theorem augmented_gram_first_block [DecidableEq n] (A : Matrix m n 𝕜)
    (b : m → 𝕜) {μ : ℝ} {v : n ⊕ Unit → 𝕜}
    (he : ((augmented A b)ᴴ * augmented A b) *ᵥ v = μ • v) :
    (Aᴴ * A - μ • 1) *ᵥ (v ∘ Sum.inl) = -(v (.inr ()) • (Aᴴ *ᵥ b)) := by
  have hh : Aᴴ *ᵥ (augmented A b *ᵥ v) = μ • (v ∘ Sum.inl) := by
    rw [← Matrix.mulVec_mulVec] at he
    ext i
    exact congrFun he (Sum.inl i)
  rw [augmented_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at hh
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  linear_combination hh

private theorem affine_eq_inv_mulVec [DecidableEq n] (A : Matrix m n 𝕜) (b : m → 𝕜)
    {μ : ℝ} (hP : IsUnit (Aᴴ * A - μ • 1)) {v : n ⊕ Unit → 𝕜} (hv : v ≠ 0)
    (he : ((augmented A b)ᴴ * augmented A b) *ᵥ v = μ • v) :
    v (.inr ()) ≠ 0 ∧ affine v = (Aᴴ * A - μ • 1)⁻¹ *ᵥ (Aᴴ *ᵥ b) := by
  let P := Aᴴ * A - μ • 1
  have hh := congrArg (fun w => P⁻¹ *ᵥ w) (augmented_gram_first_block A b he)
  change P⁻¹ *ᵥ (P *ᵥ (v ∘ Sum.inl)) = P⁻¹ *ᵥ (-(v (.inr ()) • (Aᴴ *ᵥ b))) at hh
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det _).mp hP),
    Matrix.one_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul] at hh
  have hl : v (.inr ()) ≠ 0 := by
    intro hz
    rw [hz, zero_smul, neg_zero] at hh
    apply hv
    funext i
    cases i with
    | inl i => exact congrFun hh i
    | inr i => cases i; exact hz
  refine ⟨hl, ?_⟩
  ext i
  have hi := congrFun hh i
  change -v (Sum.inl i) / v (Sum.inr ()) = (P⁻¹ *ᵥ (Aᴴ *ᵥ b)) i
  change v (Sum.inl i) = -(v (Sum.inr ()) * (P⁻¹ *ᵥ (Aᴴ *ᵥ b)) i) at hi
  rw [hi]
  field_simp

private theorem posDef_sub_smul_one_of_lt_eigenvalue_last [DecidableEq n] {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) {μ : ℝ}
    (hμ : μ < eigenvalue H k) : (H - μ • 1).PosDef := by
  have hHerm := hH.sub (isHermitian_real_smul_one μ)
  apply hHerm.posDef_iff_eigenvalue_pos.mpr
  intro j hj
  rw [sub_eq_add_neg, ← neg_smul, hH.eigenvalue_add_smul_one _ hj]
  have h := hH.eigenvalue_le_eigenvalue (show j ≤ k by omega) (show k < Fintype.card n by omega)
  linarith

/-- **Generic total least squares solution.** Let $\mu$ be the smallest eigenvalue of the
Gram matrix of $[\mathbf{A}\ \mathbf{b}]$. If $\mu$ is strictly smaller than the least eigenvalue
of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$, the unique solution is $(\mathbf{A}^{\mathsf{H}}\mathbf{A}-
\mu\mathbf{I})^{-1}\mathbf{A}^{\mathsf{H}}\mathbf{b}$. [GolubVanLoan2013, §6.3].
Result: total-least-squares-svd -/
theorem isTotalLeastSquaresSolution_iff_eq_of_lt_singularValues [DecidableEq n]
    (A : Matrix m n 𝕜) (b : m → 𝕜) (x : n → 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (hgap : singularValues (fromCols A (replicateCol Unit b)) (Fintype.card n) <
      singularValues A k) :
    IsTotalLeastSquaresSolution A b x ↔ x =
      (Aᴴ * A - singularValues (fromCols A (replicateCol Unit b)) (Fintype.card n) ^ 2 • 1)⁻¹ *ᵥ
        (Aᴴ *ᵥ b) := by
  let C := augmented A b
  have hsq := (sq_lt_sq₀ (singularValues_nonneg C _) (singularValues_nonneg A k)).mpr hgap
  rw [singularValues_sq, singularValues_sq] at hsq
  change IsTotalLeastSquaresSolution C.toCols₁ (C.col (.inr ())) x ↔
    x = (Aᴴ * A - singularValues C (Fintype.card n) ^ 2 • 1)⁻¹ *ᵥ (Aᴴ *ᵥ b)
  rw [singularValues_sq]
  have hP := (posDef_sub_smul_one_of_lt_eigenvalue_last
    (Matrix.isHermitian_conjTranspose_mul_self A) hk hsq).isUnit
  rw [isTotalLeastSquaresSolution_iff_exists]
  constructor
  · rintro ⟨v, hv, _, he, rfl⟩
    exact (affine_eq_inv_mulVec A b hP (fun h => by simp [h] at hv) he).2
  · intro hx
    obtain ⟨v, hv, he⟩ := exists_minimizer C
    obtain ⟨hl, hn⟩ := affine_eq_inv_mulVec A b hP (fun h => by simp [h] at hv) he
    exact ⟨v, hv, hl, he, hx.trans hn.symm⟩

end NLAlib
