/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.ComponentwiseBackward
public import NLAlib.Ops.Catalog.Scalar

/-!
# Rounded scaling of a vector

Normalizing a computed vector multiplies each of its parts by a rounded reciprocal. A
componentwise backward solution of a homogeneous system stays one under such a scaling, with
slightly larger constants, and the norm of the scaled vector is close to $1$.

## Main results

* `NLAlib.isComponentwiseBackwardSolution_of_norm_sub_smul_le`: a scaled backward solution.
* `NLAlib.abs_norm_roundedScale_sub_one_le`: the norm of a rounded normalization.
* `NLAlib.Ops.StdModel.norm_mul_pair_sub_le`, `NLAlib.Ops.StdModel.norm_scaled_sub_le`,
  `NLAlib.Ops.StdModel.norm_mul_unit_sub_le`: the rounded scaling of a number, a vector and a
  rounded unit.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

section Scaling

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A rounded scaling of a componentwise backward solution**: if $\mathbf{y}$ is a
componentwise backward solution of $\mathbf{M}\mathbf{y} = \mathbf{0}$ with $(\varepsilon,
\sigma)$ and every $z_k$ is within $\delta\lvert cy_k\rvert$ of $cy_k$, $0 \le \delta < 1$, then
$\mathbf{z}$ is one with $((\varepsilon + \delta)/(1 - \delta), \sigma/(1 - \delta))$. -/
theorem isComponentwiseBackwardSolution_of_norm_sub_smul_le {ε σ δ : ℝ}
    {M : Matrix n n ℂ} {y z : n → ℂ} {c : ℂ} (h : IsComponentwiseBackwardSolution ε σ M 0 y)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hz : ∀ k, ‖z k - c * y k‖ ≤ δ * ‖c * y k‖) :
    IsComponentwiseBackwardSolution ((ε + δ) / (1 - δ)) (σ / (1 - δ)) M 0 z := by
  obtain ⟨Δ, hΔ, hsol⟩ := h
  have h1δ : 0 < 1 - δ := by linarith
  have hzlo : ∀ k, (1 - δ) * ‖c * y k‖ ≤ ‖z k‖ := fun k => by
    have := norm_sub_norm_le (c * y k) (z k)
    rw [norm_sub_rev] at this
    linarith [hz k]
  have hz0 : ∀ k, c * y k = 0 → z k = 0 := fun k h0 => by
    have := hz k; rw [h0, norm_zero, mul_zero, sub_zero] at this
    exact norm_le_zero_iff.mp this
  have hzne : ∀ k, c * y k ≠ 0 → z k ≠ 0 := fun k hne h0 => by
    have := hzlo k
    rw [h0, norm_zero] at this
    have : 0 < (1 - δ) * ‖c * y k‖ := mul_pos h1δ (norm_pos_iff.mpr hne)
    linarith
  refine ⟨fun i k => if c * y k = 0 then 0 else (M i k + Δ i k) * (c * y k) / z k - M i k,
    fun i k => ?_, ?_⟩
  · have hb := hΔ i k
    have hRHS : (ε + δ) / (1 - δ) * ‖M i k‖ + (if i = k then σ / (1 - δ) else 0) =
        ((ε * ‖M i k‖ + (if i = k then σ else 0)) + δ * ‖M i k‖) / (1 - δ) := by
      split_ifs <;> field_simp <;> ring
    rw [hRHS]
    have hM := norm_nonneg (M i k)
    change ‖if c * y k = 0 then 0 else (M i k + Δ i k) * (c * y k) / z k - M i k‖ ≤ _
    by_cases h0 : c * y k = 0
    · rw [if_pos h0, norm_zero]
      exact div_nonneg (by nlinarith [norm_nonneg (Δ i k)]) h1δ.le
    · have hzk := hzne k h0
      have e : (M i k + Δ i k) * (c * y k) / z k - M i k =
          (Δ i k * (c * y k) + M i k * (c * y k - z k)) / z k := by
        field_simp; ring
      rw [if_neg h0, e, norm_div, div_le_div_iff₀ (norm_pos_iff.mpr hzk) h1δ]
      have hcy := norm_pos_iff.mpr h0
      have h2 : ‖Δ i k * (c * y k) + M i k * (c * y k - z k)‖ ≤
          (‖Δ i k‖ + δ * ‖M i k‖) * ‖c * y k‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul (Δ i k), norm_mul (M i k), norm_sub_rev (c * y k)]
        nlinarith [mul_le_mul_of_nonneg_left (hz k) hM]
      calc ‖Δ i k * (c * y k) + M i k * (c * y k - z k)‖ * (1 - δ)
          ≤ (‖Δ i k‖ + δ * ‖M i k‖) * ‖c * y k‖ * (1 - δ) :=
            mul_le_mul_of_nonneg_right h2 h1δ.le
        _ = (‖Δ i k‖ + δ * ‖M i k‖) * ((1 - δ) * ‖c * y k‖) := by ring
        _ ≤ (‖Δ i k‖ + δ * ‖M i k‖) * ‖z k‖ :=
            mul_le_mul_of_nonneg_left (hzlo k) (by positivity)
        _ ≤ (ε * ‖M i k‖ + (if i = k then σ else 0) + δ * ‖M i k‖) * ‖z k‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · funext i
    have hi := congrFun hsol i
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Pi.zero_apply] at hi ⊢
    have e : ∀ k, (M i k + (if c * y k = 0 then 0 else
        (M i k + Δ i k) * (c * y k) / z k - M i k)) * z k = c * ((M i k + Δ i k) * y k) := by
      intro k
      split_ifs with h0
      · rw [hz0 k h0, mul_zero]
        have : c = 0 ∨ y k = 0 := mul_eq_zero.mp h0
        rcases this with hc | hy
        · rw [hc, zero_mul]
        · rw [hy, mul_zero, mul_zero]
      · have hzk := hzne k h0
        field_simp
        ring
    refine (Finset.sum_congr rfl fun k _ => e k).trans ?_
    rw [← Finset.mul_sum, hi, mul_zero]

/-- The norm of a rounded scaled column: if $\nu$ is within the factors $1 \pm a$ of $W > 0$,
$\ell$ within $\boldsymbol{u}$ of $1$, $r$ a rounded $\ell/\nu$ and $Z$ within the relative error
$\boldsymbol{u}$ of $\lvert r\rvert W$, then $\lvert Z - 1\rvert \le 2a + 4\boldsymbol{u}$, for
$a \le 1/16$ and $\boldsymbol{u} \le 1/64$. -/
theorem abs_norm_roundedScale_sub_one_le {u a W ν l r Z : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 64)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 16) (hW : 0 < W) (h1 : (1 - a) * W ≤ ν) (h2 : ν ≤ (1 + a) * W)
    (hl : |l - 1| ≤ u) (hr : |r - l / ν| ≤ u * |l / ν|) (hZ : |Z - |r| * W| ≤ u * (|r| * W)) :
    |Z - 1| ≤ 2 * a + 4 * u := by
  have hν : 0 < ν := lt_of_lt_of_le (mul_pos (by linarith) hW) h1
  obtain ⟨hl₁, hl₂⟩ := abs_le.mp hl
  have hl0 : 0 < l := by linarith
  have hq : 0 < l / ν := div_pos hl0 hν
  rw [abs_of_pos hq] at hr
  obtain ⟨hr₁, hr₂⟩ := abs_le.mp hr
  have hr0 : 0 < r := by nlinarith
  rw [abs_of_pos hr0] at hZ
  obtain ⟨hZ₁, hZ₂⟩ := abs_le.mp hZ
  set p := W / ν with hp
  have hp0 : 0 < p := div_pos hW hν
  have hpν : p * ν = W := by rw [hp]; field_simp
  have hp₁ : 1 ≤ (1 + a) * p := by
    have : ν ≤ (1 + a) * (p * ν) := by rw [hpν]; exact h2
    have h' : 1 * ν ≤ ((1 + a) * p) * ν := by linarith [this, mul_assoc (1 + a) p ν]
    exact le_of_mul_le_mul_right h' hν
  have hp₂ : (1 - a) * p ≤ 1 := by
    have : (1 - a) * (p * ν) ≤ ν := by rw [hpν]; exact h1
    have h' : ((1 - a) * p) * ν ≤ 1 * ν := by linarith [this, mul_assoc (1 - a) p ν]
    exact le_of_mul_le_mul_right h' hν
  have hpu : p ≤ 1 + 2 * a := by nlinarith
  have hpl : 1 - a ≤ p := by nlinarith
  have hqW : l / ν * W = l * p := by rw [hp]; ring
  have hX₁ : (1 - u) * (l * p) ≤ r * W := by
    have := mul_le_mul_of_nonneg_right (show (1 - u) * (l / ν) ≤ r by linarith) hW.le
    rwa [mul_assoc, hqW] at this
  have hX₂ : r * W ≤ (1 + u) * (l * p) := by
    have := mul_le_mul_of_nonneg_right (show r ≤ (1 + u) * (l / ν) by linarith) hW.le
    rwa [mul_assoc, hqW] at this
  have hlp₁ : (1 - u) * (1 - a) ≤ l * p :=
    mul_le_mul (by linarith) hpl (by linarith) hl0.le
  have hlp₂ : l * p ≤ (1 + u) * (1 + 2 * a) :=
    mul_le_mul (by linarith) hpu hp0.le (by linarith)
  have hup : Z ≤ 1 + 2 * a + 4 * u := by
    have h3 : r * W ≤ (1 + u) * ((1 + u) * (1 + 2 * a)) :=
      hX₂.trans (mul_le_mul_of_nonneg_left hlp₂ (by linarith))
    have h4 : Z ≤ (1 + u) * (r * W) := by linarith
    have h5 : (1 + u) * (r * W) ≤ (1 + u) * ((1 + u) * ((1 + u) * (1 + 2 * a))) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    have h6 : (1 + u) * ((1 + u) * ((1 + u) * (1 + 2 * a))) ≤ 1 + 2 * a + 4 * u := by
      have hc : (1 + u) * ((1 + u) * (1 + u)) ≤ 1 + 7 / 2 * u := by nlinarith [mul_nonneg hu0 hu0]
      have : (1 + u) * ((1 + u) * ((1 + u) * (1 + 2 * a))) =
          (1 + u) * ((1 + u) * (1 + u)) * (1 + 2 * a) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ 1 + 2 * a by linarith),
        mul_nonneg hu0 ha0]
    linarith
  have hlo : 1 - 2 * a - 4 * u ≤ Z := by
    have h3 : (1 - u) * ((1 - u) * (1 - a)) ≤ r * W :=
      (mul_le_mul_of_nonneg_left hlp₁ (by linarith)).trans hX₁
    have h4 : (1 - u) * (r * W) ≤ Z := by linarith
    have h5 : (1 - u) * ((1 - u) * ((1 - u) * (1 - a))) ≤ (1 - u) * (r * W) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    have h6 : 1 - 2 * a - 4 * u ≤ (1 - u) * ((1 - u) * ((1 - u) * (1 - a))) := by
      have hc : 1 - 3 * u ≤ (1 - u) * ((1 - u) * (1 - u)) := by
        nlinarith [mul_nonneg hu0 hu0, mul_nonneg (mul_nonneg hu0 hu0) hu0]
      have : (1 - u) * ((1 - u) * ((1 - u) * (1 - a))) =
          (1 - u) * ((1 - u) * (1 - u)) * (1 - a) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ 1 - a by linarith), mul_nonneg hu0 ha0]
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A rounded real scaling of a complex number: each part of $z$ times $r$ is rounded with the
relative error $\boldsymbol{u}$. -/
theorem Ops.StdModel.norm_mul_pair_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u)
    (z : ℂ) (r : ℝ) :
    ‖(⟨M.mul z.re r, M.mul z.im r⟩ : ℂ) - (r : ℂ) * z‖ ≤ u * ‖(r : ℂ) * z‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  have h1 := hM.mul z.re r
  have h2 := hM.mul z.im r
  simp only [id] at h1 h2
  have e1 := mul_self_le_mul_self (abs_nonneg _) h1
  have e2 := mul_self_le_mul_self (abs_nonneg _) h2
  rw [abs_mul_abs_self, mul_mul_mul_comm, abs_mul_abs_self] at e1 e2
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  nlinarith [mul_self_nonneg u]

end Scaling

/-- **The rounded scaling of a vector, in the Euclidean norm**: rounding each part of $r w_k$
under the standard model moves $r\mathbf{w}$ by at most
$\boldsymbol{u}\lvert r\rvert\|\mathbf{w}\|$. -/
theorem Ops.StdModel.norm_scaled_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u)
    {N : ℕ} (w : Fin N → ℂ) (r : ℝ) :
    ‖WithLp.toLp 2 (fun i => (⟨M.mul (w i).re r, M.mul (w i).im r⟩ : ℂ)) -
        (r : ℂ) • WithLp.toLp 2 w‖ ≤ u * (|r| * ‖WithLp.toLp 2 w‖) := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := hM.norm_mul_pair_sub_le hu (w k) r
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  calc _ ≤ (u * (|r| * ‖w k‖)) ^ 2 := h2
    _ = _ := by ring

/-- The rounded scaling of a rounded unit: $\hat 1$ within $\boldsymbol{u} \le 1/4$ of $1$, the
pair $(\mathrm{fl}(\hat 1 r), \mathrm{fl}(0 \cdot r))$ is within $3\boldsymbol{u}\lvert r\rvert$
of $r$. -/
theorem Ops.StdModel.norm_mul_unit_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) {l : ℝ} (hl : |l - 1| ≤ u) (r : ℝ) :
    ‖(⟨M.mul l r, M.mul 0 r⟩ : ℂ) - (r : ℂ)‖ ≤ 3 * u * |r| := by
  have h0 : M.mul 0 r = 0 := by simpa using hM.mul 0 r
  have e : (⟨M.mul l r, M.mul 0 r⟩ : ℂ) - (r : ℂ) = ((M.mul l r - r : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [h0]
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hM.mul l r
  simp only [id, abs_mul] at h1
  have h2 : |l| ≤ 1 + u := by
    have := abs_sub_abs_le_abs_sub l 1
    simp only [abs_one] at this
    linarith
  have h3 : |l * r - r| ≤ u * |r| := by
    rw [show l * r - r = (l - 1) * r by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right hl (abs_nonneg _)
  have h4 := abs_sub_le (M.mul l r) (l * r) r
  have h5 : u * (|l| * |r|) ≤ u * ((1 + u) * |r|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) hu0
  nlinarith [abs_nonneg r, mul_nonneg hu0 (abs_nonneg r)]

end NLAlib
