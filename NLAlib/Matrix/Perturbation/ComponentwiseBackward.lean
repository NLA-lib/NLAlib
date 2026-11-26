/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Componentwise backward solutions of linear systems

A vector $\mathbf{x}$ is a componentwise backward solution of $\mathbf{M}\mathbf{x} = \mathbf{b}$
with the relative perturbation $\varepsilon$ and the diagonal floor $\sigma$ if
$(\mathbf{M} + \Delta)\mathbf{x} = \mathbf{b}$ for some $\Delta$ with
$\lvert\Delta_{ik}\rvert \le \varepsilon\lvert m_{ik}\rvert + \sigma[i = k]$. The residual of such
a solution is small in the Euclidean norm, and conversely a small residual in each row gives a
componentwise backward solution (the theorem of Oettli and Prager, [Higham2002, Theorem 7.3],
with a diagonal floor). The converse is how the rounding of a substitution is turned into a
backward error.

## Main definitions

* `NLAlib.IsComponentwiseBackwardSolution`: the backward solution predicate.

## Main results

* `NLAlib.IsComponentwiseBackwardSolution.norm_mulVec_sub_le`: the residual is at most
  $(\varepsilon\|\mathbf{M}\|_{\mathsf F} + \sigma)\|\mathbf{x}\|$.
* `NLAlib.isComponentwiseBackwardSolution_of_norm_sub_le`: a small residual in each row gives a
  backward solution (Oettli–Prager).
* `NLAlib.IsComponentwiseBackwardSolution.mono`: larger perturbations are weaker.
* `NLAlib.IsComponentwiseBackwardSolution.reindex`: relabeling preserves both allowances.
* `NLAlib.IsComponentwiseBackwardSolution.norm_sub_mulVec_le`: entrywise residual bounds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **A componentwise backward solution**: `x` solves $(\mathbf{M} + \Delta)\mathbf{x} = \mathbf{b}$
for a perturbation with $\lvert\Delta_{ik}\rvert \le \varepsilon\lvert m_{ik}\rvert$ off the
diagonal and $\lvert\Delta_{ii}\rvert \le \varepsilon\lvert m_{ii}\rvert + \sigma$ on it. -/
def IsComponentwiseBackwardSolution (ε σ : ℝ) (M : Matrix n n 𝕜) (b x : n → 𝕜) : Prop :=
  ∃ Δ : Matrix n n 𝕜, (∀ i k, ‖Δ i k‖ ≤ ε * ‖M i k‖ + if i = k then σ else 0) ∧
    (M + Δ) *ᵥ x = b

/-- A backward solution with $(\varepsilon, \sigma)$ is one
with any $\varepsilon' \ge \varepsilon$ and $\sigma' \ge \sigma$. -/
theorem IsComponentwiseBackwardSolution.mono {ε σ ε' σ' : ℝ} {M : Matrix n n 𝕜} {b x : n → 𝕜}
    (h : IsComponentwiseBackwardSolution ε σ M b x) (hε : ε ≤ ε') (hσ : σ ≤ σ') :
    IsComponentwiseBackwardSolution ε' σ' M b x := by
  obtain ⟨Δ, hΔ, hx⟩ := h
  refine ⟨Δ, fun i k => (hΔ i k).trans ?_, hx⟩
  have hM := norm_nonneg (M i k)
  exact add_le_add (mul_le_mul_of_nonneg_right hε hM) (by split_ifs <;> linarith)

/-- Relabeling a nearby system by the same finite equivalence in rows, columns and vectors
preserves both the relative allowance and the diagonal floor. -/
theorem IsComponentwiseBackwardSolution.reindex {ε σ : ℝ} {M : Matrix n n 𝕜}
    {b x : n → 𝕜} {m : Type*} [Fintype m] [DecidableEq m]
    (h : IsComponentwiseBackwardSolution ε σ M b x) (e : m ≃ n) :
    IsComponentwiseBackwardSolution ε σ (M.submatrix e e) (b ∘ e) (x ∘ e) := by
  obtain ⟨Δ, hΔ, heq⟩ := h
  refine ⟨Δ.submatrix e e, fun i j => ?_, ?_⟩
  · simpa only [Matrix.submatrix_apply, EmbeddingLike.apply_eq_iff_eq] using hΔ (e i) (e j)
  · have he : (x ∘ e) ∘ e.symm = x := by
      ext i
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    change (M + Δ).submatrix e e *ᵥ (x ∘ e) = b ∘ e
    rw [Matrix.submatrix_mulVec_equiv, he, heq]

/-- An exact solution satisfies every nonnegative relative allowance and diagonal floor. -/
theorem IsComponentwiseBackwardSolution.of_mulVec_eq {ε σ : ℝ} {M : Matrix n n 𝕜}
    {b x : n → 𝕜} (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (h : M *ᵥ x = b) :
    IsComponentwiseBackwardSolution ε σ M b x := by
  refine ⟨0, fun i j => ?_, ?_⟩
  · simp only [Matrix.zero_apply, norm_zero]
    split_ifs <;> positivity
  · simpa using h

/-- Zero relative allowance and zero floor recover an exact solution of the original system. -/
theorem IsComponentwiseBackwardSolution.mulVec_eq {M : Matrix n n 𝕜} {b x : n → 𝕜}
    (h : IsComponentwiseBackwardSolution 0 0 M b x) : M *ᵥ x = b := by
  obtain ⟨Δ, hΔ, heq⟩ := h
  have hzero : Δ = 0 := by
    ext i j
    exact norm_eq_zero.mp (le_antisymm (by simpa using hΔ i j) (norm_nonneg _))
  simpa [hzero] using heq

/-- Each entry of the original-system residual is bounded by the coefficient magnitudes
weighted by the solution magnitudes, with the diagonal floor contributing only at that row.
No invertibility or triangular shape is required. -/
theorem IsComponentwiseBackwardSolution.norm_sub_mulVec_le {ε σ : ℝ}
    {M : Matrix n n 𝕜} {b x : n → 𝕜}
    (h : IsComponentwiseBackwardSolution ε σ M b x) (i : n) :
    ‖(b - M *ᵥ x) i‖ ≤ ε * ∑ j, ‖M i j‖ * ‖x j‖ + σ * ‖x i‖ := by
  obtain ⟨Δ, hΔ, heq⟩ := h
  have hres : b - M *ᵥ x = Δ *ᵥ x := by
    rw [← heq, Matrix.add_mulVec]
    abel
  rw [hres]
  calc
    ‖(Δ *ᵥ x) i‖ ≤ ∑ j, ‖Δ i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (ε * ‖M i j‖ + if i = j then σ else 0) * ‖x j‖ := by
      simp_rw [norm_mul]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hΔ i j) (norm_nonneg _)
    _ = ε * ∑ j, ‖M i j‖ * ‖x j‖ + σ * ‖x i‖ := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

/-- **The residual of a componentwise backward solution**: for $\varepsilon, \sigma \ge 0$,
$\|\mathbf{M}\mathbf{x} - \mathbf{b}\| \le (\varepsilon\|\mathbf{M}\|_{\mathsf F} + \sigma)
\|\mathbf{x}\|$ in the Euclidean norm. [Higham2002, Theorem 7.3] -/
theorem IsComponentwiseBackwardSolution.norm_mulVec_sub_le {ε σ : ℝ} {M : Matrix n n 𝕜}
    {b x : n → 𝕜} (h : IsComponentwiseBackwardSolution ε σ M b x) (hε : 0 ≤ ε) (hσ : 0 ≤ σ) :
    ‖WithLp.toLp 2 (M *ᵥ x - b)‖ ≤ (ε * frobNorm M + σ) * ‖WithLp.toLp 2 x‖ := by
  obtain ⟨Mn, hMn⟩ : ∃ Mn : Matrix n n ℝ, Mn = Matrix.of fun i k => ‖M i k‖ := ⟨_, rfl⟩
  obtain ⟨xn, hxn⟩ : ∃ xn : n → ℝ, xn = fun k => ‖x k‖ := ⟨_, rfl⟩
  have hrow (i : n) : ‖(M *ᵥ x - b) i‖ ≤ ‖(ε • (Mn *ᵥ xn) + σ • xn) i‖ := by
    have hres : ‖(b - M *ᵥ x) i‖ ≤ ε * (Mn *ᵥ xn) i + σ * xn i := by
      simpa only [hMn, hxn, Matrix.of_apply, Matrix.mulVec, dotProduct] using
        h.norm_sub_mulVec_le i
    have h0 : 0 ≤ ε * (Mn *ᵥ xn) i + σ * xn i := by
      have : 0 ≤ (Mn *ᵥ xn) i :=
        Finset.sum_nonneg fun k _ => mul_nonneg (by simp [hMn]) (by simp [hxn])
      exact add_nonneg (mul_nonneg hε this) (mul_nonneg hσ (by simp [hxn]))
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      Real.norm_of_nonneg h0]
    simpa only [Pi.sub_apply, norm_sub_rev] using hres
  calc ‖WithLp.toLp 2 (M *ᵥ x - b)‖ ≤ ‖WithLp.toLp 2 (ε • (Mn *ᵥ xn) + σ • xn)‖ :=
        (EuclideanSpace.norm_toLp_norm (M *ᵥ x - b)).symm.trans_le
          (EuclideanSpace.norm_toLp_le_norm_toLp fun i => by rw [norm_norm]; exact hrow i)
    _ ≤ ε * (frobNorm Mn * ‖WithLp.toLp 2 xn‖) + σ * ‖WithLp.toLp 2 xn‖ := by
        rw [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hε, Real.norm_of_nonneg hσ]
        gcongr
        exact norm_toLp_mulVec_le_frobNorm_mul Mn xn
    _ = (ε * frobNorm M + σ) * ‖WithLp.toLp 2 x‖ := by
        have hF : frobNorm Mn = frobNorm M := by
          refine (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
          rw [frobNorm_sq_eq_sum, frobNorm_sq_eq_sum]
          simp only [hMn, Matrix.of_apply, norm_norm]
        rw [hF, hxn, EuclideanSpace.norm_toLp_norm]; ring

/-- **Oettli–Prager with a diagonal floor**: for $\varepsilon, \sigma \ge 0$, if every row of the
residual satisfies $\lvert(\mathbf{M}\mathbf{x} - \mathbf{b})_i\rvert \le
\varepsilon\sum_k\lvert m_{ik}\rvert\lvert x_k\rvert + \sigma\lvert x_i\rvert$, then `x` is a
componentwise backward solution of $\mathbf{M}\mathbf{x} = \mathbf{b}$ with
$(\varepsilon, \sigma)$. [Higham2002, Theorem 7.3] -/
theorem isComponentwiseBackwardSolution_of_norm_sub_le {ε σ : ℝ} {M : Matrix n n 𝕜}
    {b x : n → 𝕜} (hε : 0 ≤ ε) (hσ : 0 ≤ σ)
    (h : ∀ i, ‖(M *ᵥ x - b) i‖ ≤ ε * ∑ k, ‖M i k‖ * ‖x k‖ + σ * ‖x i‖) :
    IsComponentwiseBackwardSolution ε σ M b x := by
  set r := M *ᵥ x - b
  set w : n → n → ℝ := fun i k => ε * ‖M i k‖ + if i = k then σ else 0
  set S : n → ℝ := fun i => ε * ∑ k, ‖M i k‖ * ‖x k‖ + σ * ‖x i‖
  have hw0 (i k : n) : 0 ≤ w i k := by
    have := norm_nonneg (M i k); simp only [w]; split_ifs <;> positivity
  have hS (i : n) : ∑ k, w i k * ‖x k‖ = S i := by
    simp only [w, S, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
  have hsgn (z : 𝕜) : star z / (‖z‖ : 𝕜) * z = (‖z‖ : 𝕜) := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · have h0 : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      rw [div_mul_eq_mul_div, RCLike.star_def, RCLike.conj_mul, div_eq_iff h0]; ring
  set Δ : Matrix n n 𝕜 :=
    Matrix.of fun i k => -(r i / (S i : 𝕜)) * (w i k : 𝕜) * (star (x k) / (‖x k‖ : 𝕜)) with hΔ
  refine ⟨Δ, fun i k => ?_, ?_⟩
  · have hq : ‖r i / (S i : 𝕜)‖ ≤ 1 := by
      rw [norm_div, RCLike.norm_ofReal]
      exact div_le_one_of_le₀ ((h i).trans (le_abs_self _)) (abs_nonneg _)
    have hs : ‖star (x k) / (‖x k‖ : 𝕜)‖ ≤ 1 := by
      rw [norm_div, norm_star, RCLike.norm_ofReal, abs_norm]
      exact div_self_le_one _
    rw [hΔ, Matrix.of_apply, norm_mul, norm_mul, norm_neg, RCLike.norm_ofReal,
      abs_of_nonneg (hw0 i k)]
    calc ‖r i / (S i : 𝕜)‖ * w i k * ‖star (x k) / (‖x k‖ : 𝕜)‖ ≤ 1 * w i k * 1 := by
          gcongr
      _ = _ := by simp [w]
  · funext i
    rw [Matrix.add_mulVec]
    have hΔx : (Δ *ᵥ x) i = -(r i / (S i : 𝕜)) * (S i : 𝕜) := by
      simp_rw [Matrix.mulVec, dotProduct, hΔ, Matrix.of_apply, mul_assoc, hsgn, ← Finset.mul_sum]
      rw [← hS i]; push_cast; rfl
    rw [Pi.add_apply, hΔx]
    by_cases hS0 : S i = 0
    · have hr0 : r i = 0 := norm_le_zero_iff.mp (by simpa [S, hS0] using h i)
      have : (M *ᵥ x) i = b i := by
        have : (M *ᵥ x - b) i = 0 := hr0
        simpa [sub_eq_zero] using this
      simp [hS0, this]
    · have h0 : (S i : 𝕜) ≠ 0 := by exact_mod_cast hS0
      rw [neg_mul, div_mul_cancel₀ _ h0]
      simp [r]

end NLAlib
