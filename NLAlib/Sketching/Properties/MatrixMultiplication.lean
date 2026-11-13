/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import NLAlib.Sketching.Properties.JohnsonLindenstrauss
public import NLAlib.Sketching.Properties.Oblivious

/-!
# Approximate matrix multiplication from the JL moment property

A real sketch $\mathbf{S}$ with the JL moment property, exponent $p \ge 2$, approximates every
product $\mathbf{A}^{\mathsf{H}}\mathbf{B}$:
$$\mathbb{E}\|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}^p
\le (\varepsilon \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}})^p \delta\,.$$
At $\mathbf{A} = \mathbf{B} = \mathbf{U}$ with orthonormal columns this is a Gram-error bound, so
the sketch is a random subspace embedding for every fixed subspace with distortion $\varepsilon$
times the dimension, hence an oblivious subspace embedding.

Over $\mathbb{R}$ only, with constant $1$: Woodruff's statement has $3 \varepsilon$, and $1$ is
optimal (the deterministic sketch with
$\mathbf{S}^{\mathsf{H}}\mathbf{S} = (1 + \varepsilon)\mathbf{I}$, at $\mathbf{A} = \mathbf{B}$ a
unit vector, attains it). Over $\mathbb{C}$ the hypothesis gives only $\sqrt{2}\,\varepsilon$, and
this is sharp: for
$\mathbf{E} = \mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}
= c (\xi_1 \boldsymbol{\sigma}_x + \xi_2 \boldsymbol{\sigma}_y)$ with Rademacher $\xi_1, \xi_2$,
Pauli matrices $\boldsymbol{\sigma}_x$, $\boldsymbol{\sigma}_y$ and $c \le 1/\sqrt{2}$, one has
$\mathbb{E}(\mathbf{x}^{\mathsf{H}}\mathbf{E}\mathbf{x})^2 \le c^2 \|\mathbf{x}\|^4$ for every
$\mathbf{x}$ but $\mathbb{E}\lvert\mathbf{e}_1^{\mathsf{H}}\mathbf{E}\mathbf{e}_2\rvert^2 = 2 c^2$.
A form over $\Bbbk$ with $\sqrt{2}\,\varepsilon$ is added when a complex consumer appears.

## Main results

* `NLAlib.HasJLMoment.integral_frobNorm_conjTranspose_mul_sub_rpow_le`: approximate matrix
  multiplication in $L^p$.
* `NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le`: its tail.
* `NLAlib.HasJLMoment.hasSubspaceEmbedding`, `NLAlib.HasJLMoment.isObliviousSubspaceEmbedding`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

section ApproximateMultiplication

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n q r : Type*} [Fintype k] [Fintype n] [Fintype q] [Fintype r]

/-- A random sketch approximately preserves the product $\mathbf{A}^{\mathsf{H}}\mathbf{B}$
with distortion $\varepsilon$ and failure budget $\delta$ if its Frobenius error exceeds
$\varepsilon\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{B}\|_{\mathsf{F}}$ with probability at most
$\delta$. The strict failure event is empty if either factor is zero; no measurability of that
event is required. This is the product-specific tail form of approximate matrix multiplication.
[Woodruff2014, Theorem 13]; there for real matrices and with distortion $3\varepsilon$. -/
def HasApproximateMatrixMultiplication (S : Ω → Matrix k n 𝕜) (A : Matrix n q 𝕜)
    (B : Matrix n r 𝕜) (ε δ : ℝ) (μ : Measure Ω) : Prop :=
  μ.real {ω | ε * frobNorm A * frobNorm B <
    frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤ δ

/-- A non-strict AMM tail for nonzero factors implies the strict-tail property for arbitrary
factors, with a nonnegative failure budget. Zero factors need no separate law assumption. -/
theorem hasApproximateMatrixMultiplication_of_measureReal_ge_le [IsFiniteMeasure μ]
    {S : Ω → Matrix k n 𝕜} {A : Matrix n q 𝕜} {B : Matrix n r 𝕜} {ε δ : ℝ}
    (hδ : 0 ≤ δ) (h : A ≠ 0 → B ≠ 0 →
      μ.real {ω | ε * frobNorm A * frobNorm B ≤
        frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤ δ) :
    HasApproximateMatrixMultiplication S A B ε δ μ := by
  unfold HasApproximateMatrixMultiplication
  rcases eq_or_ne A 0 with rfl | hA
  · simpa only [Matrix.conjTranspose_zero, Matrix.zero_mul, sub_self, frobNorm_zero,
      mul_zero, zero_mul, lt_self_iff_false, Set.ofPred_false, measureReal_empty] using hδ
  rcases eq_or_ne B 0 with rfl | hB
  · simpa only [Matrix.mul_zero, sub_self, frobNorm_zero, mul_zero, lt_self_iff_false,
      Set.ofPred_false, measureReal_empty] using hδ
  exact (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => hω.le)).trans (h hA hB)

end ApproximateMultiplication

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n q r : Type*} [Fintype k]
  [Fintype n] [Fintype q] [Fintype r] {S : Ω → Matrix k n ℝ} {ε δ p : ℝ}

/-! ### Proof-local helpers -/

/-- The bilinear form
$(\mathbf{M}\mathbf{x})^{\mathsf{T}}\mathbf{M}\mathbf{y} - \mathbf{x}^{\mathsf{T}}\mathbf{y}$ of
the Gram error $\mathbf{M}^{\mathsf{T}}\mathbf{M} - \mathbf{I}$. -/
private def gramErr (M : Matrix k n ℝ) (x y : n → ℝ) : ℝ := (M *ᵥ x) ⬝ᵥ (M *ᵥ y) - x ⬝ᵥ y

/-- **Polarization** of the Gram error. -/
private theorem gramErr_eq (M : Matrix k n ℝ) (x y : n → ℝ) :
    gramErr M x y = ((‖WithLp.toLp 2 (M *ᵥ (x + y))‖ ^ 2 - ‖WithLp.toLp 2 (x + y)‖ ^ 2) -
      (‖WithLp.toLp 2 (M *ᵥ (x - y))‖ ^ 2 - ‖WithLp.toLp 2 (x - y)‖ ^ 2)) / 4 := by
  simp only [gramErr, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, Matrix.mulVec_add,
    Matrix.mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    dotProduct_comm (M *ᵥ y), dotProduct_comm y]
  ring

private theorem continuous_gramErr (x y : n → ℝ) :
    Continuous fun M : Matrix k n ℝ => gramErr M x y := by
  unfold gramErr
  fun_prop

/-- The moment bound for the Gram error at two vectors of the same norm. -/
private theorem integral_abs_gramErr_rpow_le_of_norm_eq (h : HasJLMoment S ε δ p μ)
    (hp : 1 ≤ p) (hS : AEMeasurable S μ) {x y : n → ℝ} (hx : x ≠ 0)
    (hxy : ‖WithLp.toLp 2 x‖ = ‖WithLp.toLp 2 y‖) :
    Integrable (fun ω => |gramErr (S ω) x y| ^ p) μ ∧
      ∫ ω, |gramErr (S ω) x y| ^ p ∂μ ≤ ε ^ p * δ * (‖WithLp.toLp 2 x‖ ^ 2) ^ p := by
  have hp0 : 0 < p := by linarith
  set c := ‖WithLp.toLp 2 x‖ ^ 2 with hc
  have hc0 : 0 < c := pow_pos (norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])) 2
  let v : Fin 2 → n → ℝ := ![x + y, x - y]
  let Y : Fin 2 → Ω → ℝ := fun i ω =>
    |‖WithLp.toLp 2 (S ω *ᵥ v i)‖ ^ 2 - ‖WithLp.toLp 2 (v i)‖ ^ 2| / 4
  let w : Fin 2 → ℝ := fun i => ‖WithLp.toLp 2 (v i)‖ ^ 2 / (4 * c)
  have hpar : ‖WithLp.toLp 2 (x + y)‖ ^ 2 + ‖WithLp.toLp 2 (x - y)‖ ^ 2 = 4 * c := by
    have hy : y ⬝ᵥ y = c := by rw [hc, hxy, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    have hx2 : x ⬝ᵥ x = c := by rw [hc, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
      dotProduct_comm y x, hy, hx2]
    ring
  have hY : ∀ ω, |gramErr (S ω) x y| ^ p ≤ (∑ i, Y i ω) ^ p := fun ω => by
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hp0.le
    rw [gramErr_eq, Fin.sum_univ_two]
    simp only [Y, v, Matrix.cons_val_zero, Matrix.cons_val_one, abs_div, abs_of_pos
      (show (0 : ℝ) < 4 by norm_num)]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
  have hYm : AEStronglyMeasurable (fun ω => (∑ i, Y i ω) ^ p) μ := by
    have hF : Continuous fun M : Matrix k n ℝ => ∑ i, |‖WithLp.toLp 2 (M *ᵥ v i)‖ ^ 2 -
        ‖WithLp.toLp 2 (v i)‖ ^ 2| / 4 := by fun_prop
    exact ((hF.measurable.comp_aemeasurable hS).pow_const p).aestronglyMeasurable
  have hY0 : ∀ i ω, 0 ≤ Y i ω := fun i ω => by positivity
  have hYint : ∀ i, Integrable (fun ω => Y i ω ^ p) μ := fun i => by
    simp only [Y, Real.div_rpow (abs_nonneg _) (show (0 : ℝ) ≤ 4 by norm_num)]
    exact (h.integrable_abs_norm_mulVec_sq_sub_rpow hp0 (v i)).div_const _
  have hint := integrable_rpow_sum hY0 hp hYm hYint
  have hle := integral_rpow_sum_le (Y := Y) (w := w) (K := ε ^ p * δ * c ^ p)
    hY0 hp hYm (fun i => by positivity)
    (by
      rw [Fin.sum_univ_two, ← add_div]
      simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hpar, div_self (by positivity)])
    (fun i hi ω => by
      have hv : v i = 0 := by
        have := (div_eq_zero_iff.1 hi).resolve_right (by positivity)
        rwa [sq_eq_zero_iff, norm_eq_zero, WithLp.toLp_eq_zero] at this
      simp only [Y, hv, Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, sub_self, abs_zero,
        zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
    hYint
    (fun i => by
      simp only [Y, Real.div_rpow (abs_nonneg _) (show (0 : ℝ) ≤ 4 by norm_num)]
      rw [integral_div]
      have hb := h.integral_abs_norm_mulVec_sq_sub_rpow_le hp0 (v i)
      have e : w i ^ p * (ε ^ p * δ * c ^ p) =
          ε ^ p * δ * ‖WithLp.toLp 2 (v i)‖ ^ (2 * p) / 4 ^ p := by
        simp only [w]
        rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hc0.le,
          Real.rpow_mul (norm_nonneg _), Real.rpow_two]
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right hb (by positivity))
  refine ⟨hint.mono' ((((continuous_gramErr x y).abs.measurable.comp_aemeasurable hS).pow_const
    p).aestronglyMeasurable) (ae_of_all _ fun ω => ?_), (integral_mono_of_nonneg
    (ae_of_all _ fun ω => by positivity) hint (ae_of_all _ hY)).trans hle⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hY ω

/-- The moment bound for the Gram error at any two vectors:
$\mathbb{E}\lvert(\mathbf{S}\mathbf{x})^{\mathsf{T}}\mathbf{S}\mathbf{y} -
\mathbf{x}^{\mathsf{T}}\mathbf{y}\rvert^p
\le \varepsilon^p \delta (\|\mathbf{x}\| \|\mathbf{y}\|)^p$. -/
private theorem integral_abs_gramErr_rpow_le (h : HasJLMoment S ε δ p μ) (hp : 1 ≤ p)
    (hS : AEMeasurable S μ) (x y : n → ℝ) :
    Integrable (fun ω => |gramErr (S ω) x y| ^ p) μ ∧ ∫ ω, |gramErr (S ω) x y| ^ p ∂μ ≤
      ε ^ p * δ * (‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖) ^ p := by
  have hp0 : 0 < p := by linarith
  by_cases hxy : x = 0 ∨ y = 0
  · have h0 (ω : Ω) : |gramErr (S ω) x y| ^ p = 0 := by
      rcases hxy with rfl | rfl <;>
        simp only [gramErr, Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct, sub_self,
          abs_zero, Real.zero_rpow hp0.ne']
    simp only [h0, integral_zero]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rcases hxy with rfl | rfl <;>
      simp only [WithLp.toLp_zero, norm_zero, zero_mul, mul_zero, Real.zero_rpow hp0.ne', le_refl]
  obtain ⟨hx, hy⟩ := not_or.1 hxy
  have hnx : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  have hny : 0 < ‖WithLp.toLp 2 y‖ := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  set t := √(‖WithLp.toLp 2 y‖ / ‖WithLp.toLp 2 x‖) with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 (div_pos hny hnx)
  have ht2 : t ^ 2 = ‖WithLp.toLp 2 y‖ / ‖WithLp.toLp 2 x‖ := Real.sq_sqrt (div_pos hny hnx).le
  have hg (M : Matrix k n ℝ) : gramErr M (t • x) (t⁻¹ • y) = gramErr M x y := by
    simp only [gramErr, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp
  have hnx' : ‖WithLp.toLp 2 (t • x)‖ = t * ‖WithLp.toLp 2 x‖ := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  have hny' : ‖WithLp.toLp 2 (t⁻¹ • y)‖ = t⁻¹ * ‖WithLp.toLp 2 y‖ := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0)]
  have heq : ‖WithLp.toLp 2 (t • x)‖ = ‖WithLp.toLp 2 (t⁻¹ • y)‖ := by
    rw [hnx', hny']
    field_simp
    rw [ht2]
    field_simp
  have hsq : ‖WithLp.toLp 2 (t • x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
    rw [hnx', mul_pow, ht2]
    field_simp
  have hA := integral_abs_gramErr_rpow_le_of_norm_eq h hp hS
    (smul_ne_zero ht0.ne' hx) heq
  simp only [hg, hsq] at hA
  exact hA

/-- $(x^2)^{p/2} = x^p$ for $x \ge 0$. -/
private theorem sq_rpow_half {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (p / 2) = x ^ p := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx]
  congr 1
  ring

omit [Fintype q] [Fintype r] in
/-- The entries of the approximate-multiplication error are Gram errors of columns. -/
private theorem conjTranspose_mul_sub_apply (M : Matrix k n ℝ) (A : Matrix n q ℝ)
    (B : Matrix n r ℝ) (i : q) (j : r) :
    (Aᴴ * Mᴴ * M * B - Aᴴ * B) i j = gramErr M (A.col i) (B.col j) := by
  rw [show Aᴴ * Mᴴ * M * B = (M * A)ᴴ * (M * B) by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    gramErr, dotProduct]
  rfl

/-- Approximate matrix multiplication in $L^p$ for nonzero $\mathbf{A}$, $\mathbf{B}$. -/
private theorem integral_frobNorm_rpow_le_of_ne_zero (h : HasJLMoment S ε δ p μ) (hp : 2 ≤ p)
    (hS : AEMeasurable S μ) {A : Matrix n q ℝ} {B : Matrix n r ℝ} (hA : A ≠ 0) (hB : B ≠ 0) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ p) μ ∧
      ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ p ∂μ ≤
        ε ^ p * δ * (frobNorm A * frobNorm B) ^ p := by
  have hp1 : 1 ≤ p := by linarith
  have hp2 : 1 ≤ p / 2 := by linarith
  have hFA : 0 < frobNorm A :=
    lt_of_le_of_ne (frobNorm_nonneg _) (Ne.symm (mt frobNorm_eq_zero_iff.1 hA))
  have hFB : 0 < frobNorm B :=
    lt_of_le_of_ne (frobNorm_nonneg _) (Ne.symm (mt frobNorm_eq_zero_iff.1 hB))
  set F := frobNorm A * frobNorm B with hF
  have hF0 : 0 < F := mul_pos hFA hFB
  let u : q × r → ℝ := fun ij => ‖WithLp.toLp 2 (A.col ij.1)‖ * ‖WithLp.toLp 2 (B.col ij.2)‖
  let Y : q × r → Ω → ℝ := fun ij ω => gramErr (S ω) (A.col ij.1) (B.col ij.2) ^ 2
  let w : q × r → ℝ := fun ij => (u ij / F) ^ 2
  have hfun (ω : Ω) : frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ p =
      (∑ ij, Y ij ω) ^ (p / 2) := by
    rw [← sq_rpow_half (frobNorm_nonneg _), frobNorm_sq_eq_sum_sq, ← Fintype.sum_prod_type']
    simp only [Y, conjTranspose_mul_sub_apply]
  have hYr (ij : q × r) (ω : Ω) :
      Y ij ω ^ (p / 2) = |gramErr (S ω) (A.col ij.1) (B.col ij.2)| ^ p := by
    simp only [Y]
    rw [← sq_abs, sq_rpow_half (abs_nonneg _)]
  have hwr (ij : q × r) : w ij ^ (p / 2) = u ij ^ p / F ^ p := by
    simp only [w]
    rw [sq_rpow_half (div_nonneg (by positivity) hF0.le),
      Real.div_rpow (by positivity) hF0.le]
  have hm : AEStronglyMeasurable (fun ω => (∑ ij, Y ij ω) ^ (p / 2)) μ := by
    have hc : Continuous fun M : Matrix k n ℝ =>
        ∑ ij : q × r, gramErr M (A.col ij.1) (B.col ij.2) ^ 2 :=
      continuous_finsetSum _ fun ij _ => (continuous_gramErr _ _).pow 2
    exact ((hc.measurable.comp_aemeasurable hS).pow_const _).aestronglyMeasurable
  simp only [hfun]
  have hY0 : ∀ ij ω, 0 ≤ Y ij ω := fun ij ω => sq_nonneg _
  have hYint : ∀ ij, Integrable (fun ω => Y ij ω ^ (p / 2)) μ := fun ij => by
    simp only [hYr]
    exact (integral_abs_gramErr_rpow_le h hp1 hS _ _).1
  refine ⟨integrable_rpow_sum hY0 hp2 hm hYint, integral_rpow_sum_le (Y := Y) (w := w) hY0 hp2 hm
    (fun ij => sq_nonneg _) ?_ (fun ij hij ω => ?_) hYint (fun ij => ?_)⟩
  · simp only [w, u, div_pow, mul_pow]
    rw [← Finset.sum_div, Fintype.sum_prod_type]
    simp only
    rw [← Finset.sum_mul_sum,
      ← frobNorm_sq_eq_sum_col, ← frobNorm_sq_eq_sum_col, ← mul_pow, ← hF,
      div_self (pow_ne_zero 2 hF0.ne')]
  · have hu : u ij = 0 := by
      have := (div_eq_zero_iff.1 (pow_eq_zero_iff two_ne_zero |>.1 hij)).resolve_right hF0.ne'
      exact this
    rcases mul_eq_zero.1 hu with h0 | h0 <;>
      · rw [norm_eq_zero, WithLp.toLp_eq_zero] at h0
        simp only [Y, h0, gramErr, Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct,
          sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  · simp only [hYr, hwr]
    refine (integral_abs_gramErr_rpow_le h hp1 hS _ _).2.trans_eq ?_
    simp only [u]
    have hFp : 0 < F ^ p := Real.rpow_pos_of_pos hF0 p
    field_simp

/-- The approximate-multiplication error vanishes when $\mathbf{A} = \mathbf{0}$ or
$\mathbf{B} = \mathbf{0}$. -/
private theorem frobNorm_conjTranspose_mul_sub_rpow_eq_zero (hp : 0 < p) (M : Matrix k n ℝ)
    {A : Matrix n q ℝ} {B : Matrix n r ℝ} (hAB : A = 0 ∨ B = 0) :
    frobNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B) ^ p = 0 := by
  rcases hAB with rfl | rfl <;>
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, sub_self,
      frobNorm_zero, Real.zero_rpow hp.ne']

/-- The $p$-th power of the approximate-matrix-multiplication error is integrable. -/
theorem HasJLMoment.integrable_frobNorm_conjTranspose_mul_sub_rpow (h : HasJLMoment S ε δ p μ)
    (hp : 2 ≤ p) (hS : AEMeasurable S μ) (A : Matrix n q ℝ) (B : Matrix n r ℝ) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ p) μ := by
  by_cases hAB : A = 0 ∨ B = 0
  · simp only [frobNorm_conjTranspose_mul_sub_rpow_eq_zero (by linarith) _ hAB]
    exact integrable_zero _ _ _
  · obtain ⟨hA, hB⟩ := not_or.1 hAB
    exact (integral_frobNorm_rpow_le_of_ne_zero h hp hS hA hB).1

/-- **Approximate matrix multiplication from the JL moment property**: for a real sketch with
the $(\varepsilon, \delta, p)$ JL moment property, $\varepsilon \ge 0$, $p \ge 2$,
$$\mathbb{E}\|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}^p
\le (\varepsilon \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}})^p \delta\,.$$
[Woodruff2014, Theorem 13]; Woodruff has $3 \varepsilon$; the constant $1$ here is optimal
($\mathbf{S}^{\mathsf{H}}\mathbf{S} = (1 + \varepsilon)\mathbf{I}$ attains it). Over $\mathbb{R}$
only: over $\mathbb{C}$ the hypothesis gives only $\sqrt{2}\,\varepsilon$, sharply, as
$\mathbf{E} = \mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}
= c (\xi_1 \boldsymbol{\sigma}_x + \xi_2 \boldsymbol{\sigma}_y)$ shows (Rademacher $\xi_1, \xi_2$,
Pauli $\boldsymbol{\sigma}_x$, $\boldsymbol{\sigma}_y$, $c \le 1/\sqrt{2}$:
$\mathbb{E}(\mathbf{x}^{\mathsf{H}}\mathbf{E}\mathbf{x})^2 \le c^2 \|\mathbf{x}\|^4$,
$\mathbb{E}\lvert\mathbf{e}_1^{\mathsf{H}}\mathbf{E}\mathbf{e}_2\rvert^2 = 2 c^2$).
Result: amm-ose -/
theorem HasJLMoment.integral_frobNorm_conjTranspose_mul_sub_rpow_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 ≤ ε) (hp : 2 ≤ p) (hS : AEMeasurable S μ) (A : Matrix n q ℝ) (B : Matrix n r ℝ) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ p ∂μ ≤
      (ε * frobNorm A * frobNorm B) ^ p * δ := by
  have hp0 : 0 < p := by linarith
  by_cases hAB : A = 0 ∨ B = 0
  · simp only [frobNorm_conjTranspose_mul_sub_rpow_eq_zero hp0 _ hAB, integral_zero]
    rcases hAB with rfl | rfl <;>
      simp only [frobNorm_zero, mul_zero, zero_mul, Real.zero_rpow hp0.ne', le_refl]
  · obtain ⟨hA, hB⟩ := not_or.1 hAB
    refine (integral_frobNorm_rpow_le_of_ne_zero h hp hS hA hB).2.trans_eq ?_
    rw [mul_assoc ε, Real.mul_rpow hε (mul_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _))]
    ring

/-- **Approximate matrix multiplication, tail form**: for $\varepsilon > 0$, $p \ge 2$ and nonzero
$\mathbf{A}$, $\mathbf{B}$,
$$\mathbb{P}\bigl[\varepsilon \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}
\le \|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}\bigr] \le \delta\,.$$
[Woodruff2014, Theorem 13]; there $3 \varepsilon$. -/
theorem HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 < ε) (hp : 2 ≤ p) (hS : AEMeasurable S μ) {A : Matrix n q ℝ} {B : Matrix n r ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      δ := by
  have hp0 : 0 < p := by linarith
  have hc : 0 < ε * frobNorm A * frobNorm B :=
    mul_pos (mul_pos hε (lt_of_le_of_ne (frobNorm_nonneg _)
      (Ne.symm (mt frobNorm_eq_zero_iff.1 hA)))) (lt_of_le_of_ne (frobNorm_nonneg _)
      (Ne.symm (mt frobNorm_eq_zero_iff.1 hB)))
  have hint := h.integrable_frobNorm_conjTranspose_mul_sub_rpow hp hS A B
  have hle := h.integral_frobNorm_conjTranspose_mul_sub_rpow_le hε.le hp hS A B
  have e : {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} =
      {ω | ε * frobNorm A * frobNorm B ≤ |frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)|} := by
    simp only [abs_of_nonneg (frobNorm_nonneg _)]
  rw [e]
  refine (measureReal_abs_ge_le_integral_rpow_div hp0 ?_ hc).trans ?_
  · simpa only [abs_of_nonneg (frobNorm_nonneg _)] using hint
  · simp only [abs_of_nonneg (frobNorm_nonneg _)]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hc p), mul_comm]
    exact hle

/-- The JL moment property gives a random embedding of every subspace of the column space of
an orthonormal $\mathbf{U}$, with any constants weaker than $1 \mp \varepsilon \lvert q \rvert$. -/
private theorem hasSubspaceEmbedding_of_range_le [DecidableEq q] (h : HasJLMoment S ε δ p μ)
    (hε : 0 < ε) (hp : 2 ≤ p) (hS : AEMeasurable S μ) (hδ : 0 ≤ δ) {U : Matrix n q ℝ}
    (hU : HasOrthonormalCols U) {q' : Type*} [Fintype q'] {V : Matrix n q' ℝ}
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) {a b : ℝ}
    (ha : a ≤ 1 - ε * Fintype.card q) (hb : 1 + ε * Fintype.card q ≤ b) :
    HasSubspaceEmbedding S V a b δ μ := by
  have hp0 : 0 < p := by linarith
  set c := ε * (Fintype.card q : ℝ) with hc
  have hsub : {ω | ¬ IsSubspaceEmbedding (S ω) V a b} ⊆
      {ω | ¬ IsSubspaceEmbedding (S ω) U (1 - c) (1 + c)} :=
    Set.ofPred_subset_ofPred.2 fun ω hω h' => hω ((h'.of_range_le hVU).mono ha hb)
  unfold HasSubspaceEmbedding
  rcases isEmpty_or_nonempty q with hq | hq
  · have he : {ω | ¬ IsSubspaceEmbedding (S ω) U (1 - c) (1 + c)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω =>
        hω ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
    rw [he, Set.subset_empty_iff] at hsub
    rw [hsub, measureReal_empty]
    exact hδ
  have hU0 : U ≠ 0 := by
    intro h0
    have h1 := hU.conjTranspose_mul_self
    rw [h0, Matrix.conjTranspose_zero, Matrix.zero_mul] at h1
    obtain ⟨i⟩ := hq
    have h2 := congrFun (congrFun h1 i) i
    rw [Matrix.zero_apply, Matrix.one_apply_eq] at h2
    exact zero_ne_one h2
  have hFU : frobNorm U * frobNorm U = Fintype.card q := by
    rw [← sq, frobNorm_sq_eq_re_trace, hU.conjTranspose_mul_self, Matrix.trace_one]
    rfl
  have htail := h.measureReal_frobNorm_conjTranspose_mul_sub_ge_le hε hp hS hU0 hU0
  rw [mul_assoc, hFU, ← hc] at htail
  have hsub2 : {ω | ¬ IsSubspaceEmbedding (S ω) U (1 - c) (1 + c)} ⊆
      {ω | c ≤ frobNorm (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U)} :=
    Set.ofPred_subset_ofPred.2 fun ω hω => by
      by_contra hlt
      rw [not_le] at hlt
      exact hω (hU.isSubspaceEmbedding_of_frobNorm_le hlt.le)
  have hc0 : 0 < c := mul_pos hε (Nat.cast_pos.2 Fintype.card_pos)
  have hfin : μ {ω | c ≤ frobNorm (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U)} ≠ ⊤ := by
    have hint := h.integrable_frobNorm_conjTranspose_mul_sub_rpow hp hS U U
    have e : {ω | c ≤ frobNorm (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U)} =
        {ω | c ^ p ≤ ‖frobNorm (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U) ^ p‖} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (frobNorm_nonneg _) _)]
      exact (Real.rpow_le_rpow_iff hc0.le (frobNorm_nonneg _) hp0).symm
    rw [e]
    exact (hint.measure_norm_ge_lt_top (Real.rpow_pos_of_pos hc0 p)).ne
  exact (measureReal_mono (hsub.trans hsub2) hfin).trans htail

/-- **The JL moment property gives subspace embeddings**: for $\mathbf{U}$ with orthonormal
columns indexed by $q$, a real sketch with the $(\varepsilon, \delta, p)$ JL moment property,
$\varepsilon > 0$, $p \ge 2$, $\delta \ge 0$, is a random subspace embedding for
$\operatorname{range}\mathbf{U}$ with distortion $\varepsilon \lvert q \rvert$ and failure
probability $\delta$. [Woodruff2014, proof of Theorem 9] (Theorems 13 and 14). -/
theorem HasJLMoment.hasSubspaceEmbedding [DecidableEq q] (h : HasJLMoment S ε δ p μ)
    (hε : 0 < ε) (hp : 2 ≤ p) (hS : AEMeasurable S μ) (hδ : 0 ≤ δ) {U : Matrix n q ℝ}
    (hU : HasOrthonormalCols U) :
    HasSubspaceEmbedding S U (1 - ε * Fintype.card q) (1 + ε * Fintype.card q) δ μ := by
  exact hasSubspaceEmbedding_of_range_le h hε hp hS hδ hU le_rfl le_rfl le_rfl

/-- **The JL moment property gives an OSE**: a real sketch with the $(\varepsilon, \delta, p)$ JL
moment property, $\varepsilon > 0$, $p \ge 2$, $\delta \ge 0$, is an OSE for every dimension $d$
with distortion $\varepsilon d$ and failure probability $\delta$; no $d \le \lvert n \rvert$ is
needed. [Woodruff2014, proof of Theorem 9] (Theorems 13 and 14). -/
theorem HasJLMoment.isObliviousSubspaceEmbedding (h : HasJLMoment S ε δ p μ) (hε : 0 < ε)
    (hp : 2 ≤ p) (hS : AEMeasurable S μ) (hδ : 0 ≤ δ) (d : ℕ) :
    IsObliviousSubspaceEmbedding S d (1 - ε * d) (1 + ε * d) δ μ := by
  intro U hU
  obtain ⟨Q, hQ, hUQ⟩ := exists_hasOrthonormalCols_range_le (p := Fin (min d (Fintype.card n)))
    U (by rw [Fintype.card_fin]; exact le_min hU (Matrix.rank_le_card_width U))
    (by rw [Fintype.card_fin]; exact min_le_right _ _)
  have hm : ε * (Fintype.card (Fin (min d (Fintype.card n))) : ℝ) ≤ ε * d := by
    rw [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 (min_le_left _ _)) hε.le
  exact hasSubspaceEmbedding_of_range_le h hε hp hS hδ hQ hUQ (by linarith) (by linarith)

end NLAlib
