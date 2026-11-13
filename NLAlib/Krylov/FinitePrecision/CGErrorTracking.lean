/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGEnergyEstimator

/-!
# Relative tracking of physical CG energy decrements

The actual energy of computed iterates admits an exact one-step expansion. Explicit
input-only estimates give a relative allowance proportional to the computed decrement,
plus an additive update allowance. The exact backward-model decrement identity cancels
its initial model-distance term. Existing absolute estimator bounds remain canonical;
the inverse-tridiagonal consequence reuses their stronger local remainder.

## Main results

* `NLAlib.CGRun.quadForm_sub_x_sub_quadForm_sub_x_succ_eq`: exact one-step identity.
* `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le`: relative tracking.
* `NLAlib.CGRun.abs_quadForm_sub_x_succ_sub_sub_inv_cgTridiagonal_le`: quadrature error.
* `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_backwardH_le`:
  model-decrement comparison without initial model distance.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- Relative decrement coefficient, currently <!-- value cgEnergyTrackingRelativeFactor k -->$60k$.
This is an explicit allowance for the local arithmetic model, not a printed source constant. -/
noncomputable irreducible_def cgEnergyTrackingRelativeFactor (k : ℕ) : ℝ := 60 * (k : ℝ)

/-- The relative decrement factor is nonnegative. -/
theorem cgEnergyTrackingRelativeFactor_nonneg (k : ℕ) :
    0 ≤ cgEnergyTrackingRelativeFactor k := by
  rw [cgEnergyTrackingRelativeFactor_def]
  positivity

/-- The factor is at most <!-- value cgEnergyTrackingRelativeFactor k -->$60k$. -/
theorem cgEnergyTrackingRelativeFactor_le (k : ℕ) :
    cgEnergyTrackingRelativeFactor k ≤ 60 * (k : ℝ) := by
  rw [cgEnergyTrackingRelativeFactor_def]

/-- Update coefficient, currently <!-- value cgEnergyTrackingUpdateFactor j -->$36j+16$.
It multiplies precision, the spectral condition ratio and the input energy scale. -/
noncomputable irreducible_def cgEnergyTrackingUpdateFactor (j : ℕ) : ℝ := 36 * (j : ℝ) + 16

/-- The additive update factor is nonnegative. -/
theorem cgEnergyTrackingUpdateFactor_nonneg (j : ℕ) : 0 ≤ cgEnergyTrackingUpdateFactor j := by
  rw [cgEnergyTrackingUpdateFactor_def]
  positivity

/-- The update factor is at most <!-- value cgEnergyTrackingUpdateFactor j -->$36j+16$. -/
theorem cgEnergyTrackingUpdateFactor_le (j : ℕ) :
    cgEnergyTrackingUpdateFactor j ≤ 36 * (j : ℝ) + 16 := by
  rw [cgEnergyTrackingUpdateFactor_def]

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- The exact one-step identity for the computed error: for $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$ and $j < k$, with the gap $\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j -
\mathbf{r}_j$ and $\mathbf{w}_j = \mathbf{x}_\star - \mathbf{x}_j - \gamma_j\mathbf{p}_j$,
$$E_j^2 - E_{j+1}^2 = \gamma_j\rho_j^2 + 2\gamma_j(\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j -
\rho_j^2) - (\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j - \gamma_j\rho_j^2) +
2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{g}_j +
2\,\mathbf{e}^{x\mathsf{T}}_j\mathbf{A}\mathbf{w}_j - \|\mathbf{e}^x_j\|_{\mathbf{A}}^2 .$$
No smallness hypothesis: this is algebra on the iterate update
$\mathbf{x}_{j+1} = \mathbf{x}_j + \gamma_j\mathbf{p}_j + \mathbf{e}^x_j$ and
$\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_j) = \mathbf{r}_j + \mathbf{g}_j$. -/
theorem quadForm_sub_x_sub_quadForm_sub_x_succ_eq {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b)
    {j : ℕ} (hj : j < k) :
    quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + 1)) =
      C.γ j * C.ρ j ^ 2 + 2 * C.γ j * (C.p j ⬝ᵥ C.r j - C.ρ j ^ 2) -
        (C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) - C.γ j * C.ρ j ^ 2) +
        2 * C.γ j * (C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j)) +
        2 * (C.ex j ⬝ᵥ (C.A *ᵥ (xs - C.x j - C.γ j • C.p j))) - quadForm C.A (C.ex j) := by
  have hw := C.quadForm_sub_x_sub_smul_p_eq hx j
  set w := xs - C.x j - C.γ j • C.p j with hwdef
  set v := C.ex j
  have hxe : xs - C.x (j + 1) = w - v := by
    rw [C.x_succ j hj, hwdef]
    abel
  rw [hxe, C.quadForm_sub_eq w v, hw]
  ring

/-- The existing per-index pairing bound implies its horizon-uniform relaxation. -/
private theorem abs_p_dotProduct_r_sub_sq_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    |C.p j ⬝ᵥ C.r j - C.ρ j ^ 2| ≤ 26 * k * C.ε * (a' / a) * C.ρ j ^ 2 := by
  have h := C.abs_p_dotProduct_r_sub_le ha hs hsmall hj
  have hκ := (C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall).2.1
  have hε := C.ε_nonneg
  have hjr : (j : ℝ) ≤ k := by exact_mod_cast hj.le
  refine h.trans ?_
  gcongr

/-- The curvature error: $\mu_j = \mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j + t_j$ with
$\lvert t_j\rvert \le 3\varepsilon\kappa\,\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j$. -/
private theorem trk_curvature {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {j : ℕ} (hj : j < k) :
    0 ≤ C.p j ⬝ᵥ (C.A *ᵥ C.p j) ∧
      C.μ j = C.p j ⬝ᵥ (C.A *ᵥ C.p j) + (C.p j ⬝ᵥ C.es j + C.eμ j) ∧
      |C.p j ⬝ᵥ C.es j + C.eμ j| ≤ 3 * (C.ε * (a' / a)) * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) := by
  obtain ⟨haa', hκ, hspec, hε5, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  set N := ‖WithLp.toLp 2 (C.p j)‖ with hN
  have hNn : 0 ≤ N := norm_nonneg _
  set P := C.p j ⬝ᵥ (C.A *ᵥ C.p j) with hPdef
  have hP0 : a * N ^ 2 ≤ P := by
    have := (C.mul_norm_sq_le_quadForm hs (C.p j))
    rwa [C.quadForm_eq_dotProduct_mulVec] at this
  have hP0' : 0 ≤ P := le_trans (by positivity) hP0
  have hμ : C.μ j = P + (C.p j ⬝ᵥ C.es j + C.eμ j) := by
    rw [C.μ_eq j hj, C.s_eq j hj, dotProduct_add]
    ring
  have h1 : |C.p j ⬝ᵥ C.es j| ≤ C.ε * a' * N ^ 2 := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    have := C.norm_es_le j hj
    calc N * ‖WithLp.toLp 2 (C.es j)‖ ≤ N * (C.ε * specNorm C.A * N) :=
          mul_le_mul_of_nonneg_left this hNn
      _ ≤ N * (C.ε * a' * N) := by gcongr
      _ = _ := by ring
  have h2 : |C.eμ j| ≤ 2 * C.ε * a' * N ^ 2 := by
    refine (C.abs_eμ_le j hj).trans ?_
    have hs' := C.norm_s_le hj
    have : ‖WithLp.toLp 2 (C.s j)‖ ≤ 2 * a' * N := by
      refine hs'.trans ?_
      have : (1 + C.ε) * specNorm C.A ≤ 2 * a' := by nlinarith [specNorm_nonneg C.A]
      exact mul_le_mul_of_nonneg_right this hNn
    calc C.ε * N * ‖WithLp.toLp 2 (C.s j)‖ ≤ C.ε * N * (2 * a' * N) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have h3 : a' * N ^ 2 ≤ a' / a * P := by
    have := mul_le_mul_of_nonneg_left hP0 (by linarith : 0 ≤ a' / a)
    calc a' * N ^ 2 = a' / a * (a * N ^ 2) := by field_simp
      _ ≤ _ := this
  have htP : |C.p j ⬝ᵥ C.es j + C.eμ j| ≤ 3 * (C.ε * (a' / a)) * P := by
    have h4 : C.ε * (a' * N ^ 2) ≤ C.ε * (a' / a * P) := mul_le_mul_of_nonneg_left h3 hε0
    calc |C.p j ⬝ᵥ C.es j + C.eμ j| ≤ |C.p j ⬝ᵥ C.es j| + |C.eμ j| := abs_add_le _ _
      _ ≤ 3 * (C.ε * (a' / a)) * P := by nlinarith
  exact ⟨hP0', hμ, htP⟩

/-- **The curvature error, relative**: under (H), for $j < k$,
$\lvert\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j - \gamma_j\|\mathbf{r}_j\|^2\rvert
\le 6\,\varepsilon\kappa\,\gamma_j\|\mathbf{r}_j\|^2$. The two-sided form of
`NLAlib.CGRun.γ_sq_mul_dotProduct_mulVec_le` with the $\varepsilon$-dependence kept. -/
private theorem abs_γ_sq_mul_dotProduct_mulVec_sub_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    |C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) - C.γ j * C.ρ j ^ 2| ≤
      6 * C.ε * (a' / a) * (C.γ j * C.ρ j ^ 2) := by
  obtain ⟨haa', hκ, hspec, hε5, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hG2 := C.γ_sq_mul_dotProduct_mulVec_le ha hs hsmall hj
  obtain ⟨hP0', hμ, htP⟩ := C.trk_curvature ha hs hsmall hj
  set P := C.p j ⬝ᵥ (C.A *ᵥ C.p j) with hPdef
  set t := C.p j ⬝ᵥ C.es j + C.eμ j with ht
  have hgm := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le, hμ] at hgm
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have he := abs_le.mp (C.abs_eγ_le j hj)
  have hρ2 : 0 ≤ C.ρ j ^ 2 := sq_nonneg _
  -- `γP ≤ 1.001ρ²`
  have hγP : C.γ j * P ≤ (1 + 1 / 1000) * C.ρ j ^ 2 := by
    have : C.γ j * (C.γ j * P) ≤ C.γ j * ((1 + 1 / 1000) * C.ρ j ^ 2) := by
      calc C.γ j * (C.γ j * P) = C.γ j ^ 2 * P := by ring
        _ ≤ _ := hG2
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hγ
  have hγP0 : 0 ≤ C.γ j * P := by positivity
  have hεκ : C.ε ≤ C.ε * (a' / a) := le_mul_of_one_le_right hε0 hκ
  -- `|γP - ρ²| ≤ 6εκρ²`
  have hid : C.γ j * P - C.ρ j ^ 2 =
      C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j) - C.γ j * t := by
    have : C.γ j * P = C.γ j * (P + t) - C.γ j * t := by ring
    rw [this, hgm]
    ring
  have hθe : |C.θ j + C.eγ j + C.θ j * C.eγ j| ≤ 21 / 10 * C.ε := by
    rw [abs_le]
    constructor <;> nlinarith
  have hA : |C.γ j * P - C.ρ j ^ 2| ≤ 6 * C.ε * (a' / a) * C.ρ j ^ 2 := by
    rw [hid]
    have hγt : |C.γ j * t| ≤ 3 * (C.ε * (a' / a)) * (C.γ j * P) := by
      rw [abs_mul, abs_of_pos hγ]
      calc C.γ j * |t| ≤ C.γ j * (3 * (C.ε * (a' / a)) * P) :=
            mul_le_mul_of_nonneg_left htP hγ.le
        _ = _ := by ring
    have hρθ : |C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)| ≤
        C.ρ j ^ 2 * (21 / 10 * C.ε) := by
      rw [abs_mul, abs_of_nonneg hρ2]
      exact mul_le_mul_of_nonneg_left hθe hρ2
    have hT0 : 0 ≤ C.ε * (a' / a) := le_trans hε0 hεκ
    have h5 : 3 * (C.ε * (a' / a)) * (C.γ j * P) ≤
        3 * (C.ε * (a' / a)) * ((1 + 1 / 1000) * C.ρ j ^ 2) :=
      mul_le_mul_of_nonneg_left hγP (by positivity)
    have h6 : C.ρ j ^ 2 * (21 / 10 * C.ε) ≤ 21 / 10 * (C.ε * (a' / a)) * C.ρ j ^ 2 := by
      nlinarith
    calc |C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j) - C.γ j * t| ≤
          |C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)| + |C.γ j * t| := abs_sub _ _
      _ ≤ 6 * C.ε * (a' / a) * C.ρ j ^ 2 := by
          have : 0 ≤ C.ε * (a' / a) * C.ρ j ^ 2 := by positivity
          linarith
  have e : C.γ j ^ 2 * P - C.γ j * C.ρ j ^ 2 = C.γ j * (C.γ j * P - C.ρ j ^ 2) := by ring
  rw [e, abs_mul, abs_of_pos hγ]
  calc C.γ j * |C.γ j * P - C.ρ j ^ 2| ≤ C.γ j * (6 * C.ε * (a' / a) * C.ρ j ^ 2) :=
        mul_le_mul_of_nonneg_left hA hγ.le
    _ = _ := by ring

/-- The gap term of the one-step identity:
$2\gamma_j\lvert\mathbf{p}_j^{\mathsf{T}}\mathbf{g}_j\rvert \le 36j\varepsilon\kappa
\|\mathbf{b}\|^2/a$. -/
private theorem trk_gap_term {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {j : ℕ} (hj : j < k) :
    |2 * C.γ j * (C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j))| ≤
      36 * j * (C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)) := by
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hG := C.norm_sub_mulVec_x_sub_r_le_norm_b ha hs hsmall hj.le
  have hγp := C.γ_mul_norm_p_le ha hs hsmall hj
  set g := C.b - C.A *ᵥ C.x j - C.r j
  set B := ‖WithLp.toLp 2 C.b‖
  have hκ0 : 0 ≤ a' / a := by linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * C.γ j)]
  have h1 : |C.p j ⬝ᵥ g| ≤ ‖WithLp.toLp 2 (C.p j)‖ * ‖WithLp.toLp 2 g‖ :=
    EuclideanSpace.abs_dotProduct_le_norm _ _
  calc 2 * C.γ j * |C.p j ⬝ᵥ g| ≤
        2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 g‖ := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * C.γ j)
        linarith
    _ ≤ 2 * (3 / 2 * B / a) * (12 * j * C.ε * (a' / a) * B) :=
        mul_le_mul (by linarith) hG (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The energy of $\mathbf{w}_j = \mathbf{x}_\star - \mathbf{x}_j - \gamma_j\mathbf{p}_j$:
$\|\mathbf{w}_j\|_{\mathbf{A}}^2 \le 4\|\mathbf{b}\|^2/a$. -/
private theorem trk_quadForm_w_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    quadForm C.A (xs - C.x j - C.γ j • C.p j) ≤ 4 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  obtain ⟨hjT, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le_of_le ha hs hsmall hj.le
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hpg := abs_le.mp (C.trk_gap_term ha hs hsmall hj)
  have hG1 := C.p_dotProduct_r_ge ha hs hsmall hj
  have hG2 := C.γ_sq_mul_dotProduct_mulVec_le ha hs hsmall hj
  have hsum := C.sum_γ_mul_ρ_sq_le ha hs hsmall
  have hQe := C.quadForm_sub_x_le ha hs hsmall hx hj.le
  have hQs := C.quadForm_le_norm_b_sq_div_of_mulVec_eq ha hs hx
  set g := C.b - C.A *ᵥ C.x j - C.r j with hg
  set e := xs - C.x j with he
  set u := ‖WithLp.toLp 2 C.b‖ ^ 2 / a with hu
  have hu0 : 0 ≤ u := by positivity
  have hγρu : C.γ j * C.ρ j ^ 2 ≤ 2 * u := by
    have hle : C.γ j * C.ρ j ^ 2 ≤ ∑ i ∈ Finset.range k, C.γ i * C.ρ i ^ 2 :=
      Finset.single_le_sum (f := fun i => C.γ i * C.ρ i ^ 2)
        (fun i hi => mul_nonneg (C.γ_pos (Finset.mem_range.mp hi)).le (sq_nonneg _))
        (Finset.mem_range.mpr hj)
    have : 2 * ‖WithLp.toLp 2 C.b‖ ^ 2 / a = 2 * u := by rw [hu]; ring
    linarith
  rw [C.quadForm_sub_x_sub_smul_p_eq hx j]
  have h1 : 0 ≤ 2 * C.γ j * (C.p j ⬝ᵥ C.r j) := by
    have : 0 ≤ C.p j ⬝ᵥ C.r j := le_trans (by positivity) hG1
    positivity
  have h3 : 36 * (j : ℝ) * (C.ε * (a' / a) * u) ≤ 36 / 10 ^ 5 * u := by
    have := mul_le_mul_of_nonneg_right hjT hu0
    have e1 : 36 * (j : ℝ) * (C.ε * (a' / a) * u) = 36 * ((j : ℝ) * C.ε * (a' / a) * u) := by
      ring
    linarith
  linarith

/-- The iterate update error, a priori: $\|\mathbf{e}^x_j\| \le 3.6\varepsilon\|\mathbf{b}\|/a$. -/
private theorem trk_norm_ex_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.ex j)‖ ≤ 18 / 5 * C.ε * ‖WithLp.toLp 2 C.b‖ / a := by
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hγp := C.γ_mul_norm_p_le ha hs hsmall hj
  have hQs := C.quadForm_le_norm_b_sq_div_of_mulVec_eq ha hs hx
  have hxs := C.norm_le_norm_b_div_of_mulVec_eq ha hs hx
  have hxj := C.norm_x_le ha hs hsmall hx hj.le
  set B := ‖WithLp.toLp 2 C.b‖
  have hB0 : 0 ≤ B := norm_nonneg _
  have hxj' : ‖WithLp.toLp 2 (C.x j)‖ ≤ (1 + 1 / 1000) * (2 * B / a) := by
    refine hxj.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    have h1 : Real.sqrt (quadForm C.A xs) ≤ B / Real.sqrt a := by
      rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt ha.le]
      exact hQs
    have h2 : Real.sqrt (quadForm C.A xs) / Real.sqrt a ≤ B / a := by
      rw [div_le_iff₀ hsa]
      calc Real.sqrt (quadForm C.A xs) ≤ B / Real.sqrt a := h1
        _ = B / a * Real.sqrt a := by
            field_simp
            rw [Real.sq_sqrt ha.le]
    have : 2 * B / a = B / a + B / a := by ring
    linarith
  refine (C.norm_ex_le j hj).trans ?_
  rw [abs_of_pos hγ]
  have : (1 + 1 / 1000) * (2 * B / a) + 3 / 2 * B / a ≤ 18 / 5 * B / a := by
    have : 0 ≤ B / a := by positivity
    have e1 : (1 + 1 / 1000) * (2 * B / a) + 3 / 2 * B / a = 3502 / 1000 * (B / a) := by ring
    have e2 : 18 / 5 * B / a = 36 / 10 * (B / a) := by ring
    linarith
  calc C.ε * (‖WithLp.toLp 2 (C.x j)‖ + C.γ j * ‖WithLp.toLp 2 (C.p j)‖) ≤
        C.ε * (18 / 5 * B / a) := mul_le_mul_of_nonneg_left (by linarith) hε0
    _ = _ := by ring

/-- The iterate update terms of the one-step identity:
$2\lvert\mathbf{e}^{x\mathsf{T}}_j\mathbf{A}\mathbf{w}_j\rvert \le 15\varepsilon\kappa
\|\mathbf{b}\|^2/a$ and $0 \le \|\mathbf{e}^x_j\|_{\mathbf{A}}^2 \le \varepsilon\kappa
\|\mathbf{b}\|^2/a$. -/
private theorem trk_update_terms {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    |2 * (C.ex j ⬝ᵥ (C.A *ᵥ (xs - C.x j - C.γ j • C.p j)))| ≤
        15 * (C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)) ∧
      0 ≤ quadForm C.A (C.ex j) ∧
      quadForm C.A (C.ex j) ≤ C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  obtain ⟨haa', hκ, -, hε5, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hQw := C.trk_quadForm_w_le ha hs hsmall hx hj
  have hex := C.trk_norm_ex_le ha hs hsmall hx hj
  set w := xs - C.x j - C.γ j • C.p j
  set v := C.ex j
  set κ := a' / a with hκdef
  set B := ‖WithLp.toLp 2 C.b‖ with hB
  set u := B ^ 2 / a with hu
  have hB0 : 0 ≤ B := norm_nonneg _
  have hu0 : 0 ≤ u := by positivity
  have hκ0 : 0 ≤ κ := by linarith
  have ha' : 0 ≤ a' := by linarith
  have ha'κ : a' = κ * a := by rw [hκdef]; field_simp
  have hεκu : 0 ≤ C.ε * κ * u := by positivity
  have hex2 : ‖WithLp.toLp 2 v‖ ^ 2 ≤ (18 / 5 * C.ε * B / a) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hex 2
  have hsq : a' * (18 / 5 * C.ε * B / a) ^ 2 = 324 / 25 * C.ε ^ 2 * κ * u := by
    rw [hu, ha'κ]
    field_simp
    ring
  have hQv : quadForm C.A v ≤ C.ε * κ * u := by
    have h1 := (C.quadForm_le_mul_norm_sq hs v)
    have h2 : a' * ‖WithLp.toLp 2 v‖ ^ 2 ≤ a' * (18 / 5 * C.ε * B / a) ^ 2 :=
      mul_le_mul_of_nonneg_left hex2 ha'
    have h3 : 324 / 25 * C.ε ^ 2 * κ * u ≤ C.ε * κ * u := by
      have e1 : 324 / 25 * C.ε ^ 2 * κ * u = (324 / 25 * C.ε) * (C.ε * κ * u) := by ring
      rw [e1]
      exact mul_le_of_le_one_left hεκu (by linarith)
    exact h1.trans (h2.trans (hsq.le.trans h3))
  have hQv0 : 0 ≤ quadForm C.A v := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs v)
  refine ⟨?_, hQv0, hQv⟩
  have hAw := C.norm_mulVec_sq_le_mul_quadForm ha hs w
  set X := ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 (C.A *ᵥ w)‖ with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : |v ⬝ᵥ (C.A *ᵥ w)| ≤ X := EuclideanSpace.abs_dotProduct_le_norm _ _
  have hκ2 : κ ≤ κ ^ 2 := by nlinarith
  have h4 : (18 / 5 * C.ε * B / a) ^ 2 * (a' * (4 * u)) ≤ (15 / 2 * (C.ε * κ * u)) ^ 2 := by
    have e1 : (18 / 5 * C.ε * B / a) ^ 2 * (a' * (4 * u)) =
        1296 / 25 * (C.ε ^ 2 * u ^ 2) * κ := by
      calc (18 / 5 * C.ε * B / a) ^ 2 * (a' * (4 * u)) =
            4 * u * (a' * (18 / 5 * C.ε * B / a) ^ 2) := by ring
        _ = _ := by rw [hsq]; ring
    have e2 : (15 / 2 * (C.ε * κ * u)) ^ 2 = 225 / 4 * (C.ε ^ 2 * u ^ 2) * κ ^ 2 := by ring
    rw [e1, e2]
    have h3 : 0 ≤ C.ε ^ 2 * u ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hκ2 h3
    have h5 : 0 ≤ C.ε ^ 2 * u ^ 2 * κ := by positivity
    linarith
  have h2 : X ^ 2 ≤ (15 / 2 * (C.ε * κ * u)) ^ 2 := by
    rw [hX, mul_pow]
    refine le_trans ?_ h4
    exact mul_le_mul hex2 (hAw.trans (mul_le_mul_of_nonneg_left hQw ha')) (sq_nonneg _)
      (sq_nonneg _)
  have h3 : X ≤ 15 / 2 * (C.ε * κ * u) :=
    (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).mp h2
  rw [abs_mul, abs_two]
  linarith

/-- A successful CG run with spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$ has one-step energy-decrement error bounded
relative to the computed decrement plus an input-only additive allowance. For a solution
$\mathbf A\mathbf x_\star=\mathbf b$ and $j<k$, write
$E_i=\|\mathbf x_\star-\mathbf x_i\|_{\mathbf A}^2$. The coefficients are
currently <!-- value cgEnergyTrackingRelativeFactor k -->$60k$. The additive coefficient is
currently <!-- value cgEnergyTrackingUpdateFactor j -->$36j+16$:

$$\lvert E_j-E_{j+1}-\gamma_j\rho_j^2\rvert\le
60k\varepsilon\kappa\gamma_j\rho_j^2+(36j+16)\varepsilon\kappa\|\mathbf b\|^2/a.$$
No energy-monotonicity assumption or linearization of the roundoff terms is used. -/
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_succ_sub_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + 1)) - C.γ j * C.ρ j ^ 2| ≤
      cgEnergyTrackingRelativeFactor k * C.ε * (a' / a) * (C.γ j * C.ρ j ^ 2) +
        cgEnergyTrackingUpdateFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  rw [cgEnergyTrackingRelativeFactor_def, cgEnergyTrackingUpdateFactor_def]
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  have hid := C.quadForm_sub_x_sub_quadForm_sub_x_succ_eq hx hj
  have hT1 := C.abs_p_dotProduct_r_sub_sq_le ha hs hsmall hj
  have hT2 := C.abs_γ_sq_mul_dotProduct_mulVec_sub_le ha hs hsmall hj
  have a3 := abs_le.mp (C.trk_gap_term ha hs hsmall hj)
  obtain ⟨hvw, hQv0, hQv⟩ := C.trk_update_terms ha hs hsmall hx hj
  have a4 := abs_le.mp hvw
  set κ := a' / a with hκdef
  set u := ‖WithLp.toLp 2 C.b‖ ^ 2 / a with hu
  have hκ0 : 0 ≤ κ := by linarith
  have hu0 : 0 ≤ u := by positivity
  have hγρ : 0 ≤ C.γ j * C.ρ j ^ 2 := by positivity
  have hr1 : |2 * C.γ j * (C.p j ⬝ᵥ C.r j - C.ρ j ^ 2)| ≤
      52 * ((k : ℝ) * C.ε * κ) * (C.γ j * C.ρ j ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * C.γ j)]
    calc 2 * C.γ j * |C.p j ⬝ᵥ C.r j - C.ρ j ^ 2| ≤
          2 * C.γ j * (26 * k * C.ε * κ * C.ρ j ^ 2) :=
          mul_le_mul_of_nonneg_left hT1 (by positivity)
      _ = _ := by ring
  have hr2 : |C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) - C.γ j * C.ρ j ^ 2| ≤
      6 * ((k : ℝ) * C.ε * κ) * (C.γ j * C.ρ j ^ 2) := by
    refine hT2.trans ?_
    have : C.ε * κ ≤ (k : ℝ) * C.ε * κ := by
      have := mul_le_mul_of_nonneg_right hk1 (by positivity : 0 ≤ C.ε * κ)
      linarith
    have := mul_le_mul_of_nonneg_right this hγρ
    linarith
  have a1 := abs_le.mp hr1
  have a2 := abs_le.mp hr2
  have h0 : 0 ≤ ((k : ℝ) * C.ε * κ) * (C.γ j * C.ρ j ^ 2) := by positivity
  have h00 : 0 ≤ C.ε * κ * u := by positivity
  rw [hid, abs_le]
  constructor
  · linarith only [a1.1, a2.2, a3.1, a4.1, hQv, h0, h00]
  · linarith only [a1.2, a2.1, a3.2, a4.2, hQv0, h0, h00]

/-- **Relative reliability of computed CG energy decrements.** For a successful $k$-step
run with spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$,
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$ and solution
$\mathbf A\mathbf x_\star=\mathbf b$, let
$E_i=\|\mathbf x_\star-\mathbf x_i\|_{\mathbf A}^2$ and
$\nu_{j,d}=\sum_{i=j}^{j+d-1}\gamma_i\rho_i^2$. For $j+d\le k$, the allowance is
currently <!-- value cgEnergyTrackingRelativeFactor k -->$60k$. The additive coefficient is
currently <!-- value cgEnergyTrackingUpdateFactor (j+d) -->$36(j+d)+16$:
$$\lvert E_j-E_{j+d}-\nu_{j,d}\rvert\le60k\varepsilon\kappa\nu_{j,d}
 +(36(j+d)+16)d\varepsilon\kappa\|\mathbf b\|^2/a.$$
[StrakosTichy2002, Theorem 10.1]; the arithmetic model and explicit input-only constants
here retain the quadratic roundoff terms. Scalar summation is exact and physical energy
need not decrease. Unlike the existing absolute delayed bound, this form retains dependence
on the measured decrement and can be useful when that decrement is small.
Result: cg-relative-energy-decrement-reliability -/
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j d : ℕ} (hjd : j + d ≤ k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d)) -
        ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2| ≤
      cgEnergyTrackingRelativeFactor k * C.ε * (a' / a) *
          ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2 +
        cgEnergyTrackingUpdateFactor (j + d) * d * C.ε * (a' / a) *
          (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  rw [cgEnergyTrackingRelativeFactor_def, cgEnergyTrackingUpdateFactor_def]
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  set κ := a' / a with hκdef
  set u := ‖WithLp.toLp 2 C.b‖ ^ 2 / a with hu
  have hκ0 : 0 ≤ κ := by linarith
  have hu0 : 0 ≤ u := by positivity
  have hT : 0 ≤ C.ε * κ * u := by positivity
  induction d with
  | zero => simp
  | succ d ih =>
    have hjd' : j + d < k := by omega
    have h1 := ih (by omega)
    have h2 := C.abs_quadForm_sub_x_sub_quadForm_sub_x_succ_sub_le ha hs hsmall hx hjd'
    rw [cgEnergyTrackingRelativeFactor_def, cgEnergyTrackingUpdateFactor_def] at h2
    rw [← hκdef, ← hu] at h2
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    set S := ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2
    set Q0 := quadForm C.A (xs - C.x j)
    set Q1 := quadForm C.A (xs - C.x (j + d))
    set Q2 := quadForm C.A (xs - C.x (j + d + 1))
    set t := C.γ (j + d) * C.ρ (j + d) ^ 2
    have e : Q0 - Q2 - (S + t) = (Q0 - Q1 - S) + (Q1 - Q2 - t) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have hd : (0 : ℝ) ≤ d := d.cast_nonneg
    have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
    have h3 : (36 * ((j : ℝ) + d) + 16) * d * C.ε * κ * u + (36 * ((j + d : ℕ) : ℝ) + 16) *
        C.ε * κ * u ≤
          (36 * ((j : ℝ) + ((d + 1 : ℕ) : ℝ)) + 16) * ((d + 1 : ℕ) : ℝ) * C.ε * κ * u := by
      push_cast
      have : (36 * ((j : ℝ) + d) + 16) * d * C.ε * κ * u + (36 * ((j : ℝ) + d) + 16) *
          C.ε * κ * u + 36 * (d + 1) * (C.ε * κ * u) =
          (36 * ((j : ℝ) + (d + 1)) + 16) * (d + 1) * C.ε * κ * u := by ring
      nlinarith
    have e2 : 60 * (k : ℝ) * C.ε * κ * (S + t) = 60 * (k : ℝ) * C.ε * κ * S +
        60 * (k : ℝ) * C.ε * κ * t := by ring
    push_cast at h1 h2 h3 ⊢
    linarith

/-- **Physical CG energy as computed Gauss quadrature error.** For a successful $k$-step
run with spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$,
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$ and solution
$\mathbf A\mathbf x_\star=\mathbf b$, put
$\mathbf T_{j+1}=\mathsf{cgTridiagonal}(\gamma,\rho,j+1)$. For $j+1\le k$,
the physical squared energy differs from
$\|\mathbf x_\star\|_{\mathbf A}^2-\|\mathbf b\|^2(\mathbf T_{j+1}^{-1})_{00}$
by at most $\mathsf{cgEnergyEstimatorFactor}(0,j+1)\varepsilon\kappa\|\mathbf b\|^2/a$.
The factor is currently <!-- value cgEnergyEstimatorFactor 0 (j+1) -->$150(j+1)(0+(j+1))$.
[MeurantStrakos2006, (3.17)]; the exact quadrature identity is applied to computed
coefficients, with the existing absolute physical-energy remainder. No residual-to-energy
norm conversion is used.
Result: cg-physical-energy-quadrature -/
theorem abs_quadForm_sub_x_succ_sub_sub_inv_cgTridiagonal_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j + 1 ≤ k) :
    |quadForm C.A (xs - C.x (j + 1)) -
        (quadForm C.A xs - ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgTridiagonal C.γ C.ρ (j + 1))⁻¹ 0 0)| ≤
      cgEnergyEstimatorFactor 0 (j + 1) * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have h := C.abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le ha hs hsmall hx
    (j := 0) (d := j + 1) (by simpa using hj)
  rw [C.x_zero, sub_zero, zero_add, ← Finset.range_eq_Ico] at h
  have hT := sq_mul_inv_cgTridiagonal_zero_zero (γ := C.γ) (ρ := C.ρ) (k := j)
    (fun i hi => C.γ_pos (by omega)) (fun i hi => (C.ρ_pos (by omega)).ne')
  have hρ0 : C.ρ 0 = ‖WithLp.toLp 2 C.b‖ := by rw [ρ, C.r_zero]
  rw [hρ0] at hT
  rw [hT]
  have heq : quadForm C.A (xs - C.x (j + 1)) -
      (quadForm C.A xs - ∑ i ∈ Finset.range (j + 1), C.γ i * C.ρ i ^ 2) =
      -(quadForm C.A xs - quadForm C.A (xs - C.x (j + 1)) -
        ∑ i ∈ Finset.range (j + 1), C.γ i * C.ρ i ^ 2) := by ring
  rw [heq, abs_neg]
  exact h

/-- For a successful run with spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, computed physical-energy decrements track
those of exact $\mathsf{cgIterate}$ on the full-horizon backward model. For physical and
model solutions and $j+d\le k$, the relative and additive allowances are
currently <!-- value cgEnergyTrackingRelativeFactor k -->$60k$. The additive coefficient is
currently <!-- value cgEnergyTrackingUpdateFactor (j+d) -->$36(j+d)+16$. No initial model-distance
term enters this decrement comparison; the computed decrement is the exact model decrement.
The scalar decrement sum is evaluated exactly. No printed source. -/
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_backwardH_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {xs' : Fin n × Fin (k + 1) → ℝ}
    (hxs' : C.backwardH *ᵥ xs' = C.dilatedRhs) {j d : ℕ} (hjd : j + d ≤ k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d)) -
        (quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 j) -
          quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 (j + d)))| ≤
      cgEnergyTrackingRelativeFactor k * C.ε * (a' / a) *
          (quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 j) -
            quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 (j + d))) +
        cgEnergyTrackingUpdateFactor (j + d) * d * C.ε * (a' / a) *
          (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  rw [C.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate ha hs hsmall hxs'
    hjd]
  exact C.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le ha hs hsmall hx hjd


end CGRun

end NLAlib
