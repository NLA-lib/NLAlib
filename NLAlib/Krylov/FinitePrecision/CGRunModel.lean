/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGRun
public import NLAlib.Matrix.FinitePrecision.ResidualGap

/-!
# Local orthogonality and the a posteriori backward model of a conjugate gradient run

Continues `NLAlib/Krylov/FinitePrecision/CGRun.lean` (the run, its Lanczos data and
Lemma A) with Lemma B, the a posteriori backward model, the next division and
the residual gap. Geometric accumulation estimates apply at every run length; their linear
corollaries assume $k\varepsilon\le1/100$ explicitly.

## Main results

* `NLAlib.CGRun.abs_p_dotProduct_r_succ_le`: the line search inner products.
* `NLAlib.CGRun.abs_p_dotProduct_r_succ_le_geom_sum`: the accumulated line search defect.
* `NLAlib.CGRun.abs_adjacentInner_le` (Lemma B): local orthogonality.
* `NLAlib.CGRun.abs_adjacentInner_le_geom_sum`: local orthogonality at every horizon.
* `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates`: the a posteriori model.
* `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_geom_sum_of_certificates`:
  the a posteriori model with geometric accumulation and two run certificates.
* `NLAlib.CGRun.norm_r_le_two_mul_norm_p`: a nonzero terminal residual gives a nonzero direction.
* `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le`: the residual gap.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- Accumulated line-search error over $m$ steps,
currently <!-- value cgLineSearchFactor m \varepsilon -->
$(41/10)\varepsilon\sum_{i=0}^{m-1}(1+(31/10)\varepsilon)^i$.
No printed source. The factor sums the local forcing estimate without a horizon restriction;
the finite sum also covers $\varepsilon=0$ and $m=0$. -/
noncomputable irreducible_def cgLineSearchFactor (m : ℕ) (ε : ℝ) : ℝ :=
  41 / 10 * ε * ∑ i ∈ Finset.range m, (1 + 31 / 10 * ε) ^ i

/-- Accumulated adjacent-inner-product error over $m$ steps,
currently <!-- value cgAdjacentInnerFactor m \varepsilon -->
$13\varepsilon\sum_{i=0}^{m-1}(1+(31/10)\varepsilon)^i$.
No printed source. The factor retains geometric propagation of local orthogonality errors;
the finite sum also covers $\varepsilon=0$ and $m=0$. -/
noncomputable irreducible_def cgAdjacentInnerFactor (m : ℕ) (ε : ℝ) : ℝ :=
  13 * ε * ∑ i ∈ Finset.range m, (1 + 31 / 10 * ε) ^ i

/-- The accumulated line-search factor is nonnegative for nonnegative accuracy. -/
theorem cgLineSearchFactor_nonneg (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ cgLineSearchFactor m ε := by
  rw [cgLineSearchFactor_def]
  positivity

/-- The accumulated adjacent-inner-product factor is nonnegative for nonnegative accuracy. -/
theorem cgAdjacentInnerFactor_nonneg (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ cgAdjacentInnerFactor m ε := by
  rw [cgAdjacentInnerFactor_def]
  positivity

/-- The accumulated line-search factor increases with the number of steps. -/
theorem cgLineSearchFactor_mono {m l : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hml : m ≤ l) :
    cgLineSearchFactor m ε ≤ cgLineSearchFactor l ε := by
  rw [cgLineSearchFactor_def, cgLineSearchFactor_def]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hml)
    (fun _ _ _ => pow_nonneg (by positivity) _)

/-- The accumulated adjacent-inner-product factor increases with the number of steps. -/
theorem cgAdjacentInnerFactor_mono {m l : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hml : m ≤ l) :
    cgAdjacentInnerFactor m ε ≤ cgAdjacentInnerFactor l ε := by
  rw [cgAdjacentInnerFactor_def, cgAdjacentInnerFactor_def]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hml)
    (fun _ _ _ => pow_nonneg (by positivity) _)

/-- One additional step propagates the previous line-search error and adds its local forcing. -/
private theorem cgLineSearchFactor_succ (m : ℕ) (ε : ℝ) :
    cgLineSearchFactor (m + 1) ε =
      (1 + 31 / 10 * ε) * cgLineSearchFactor m ε + 41 / 10 * ε := by
  rw [cgLineSearchFactor_def, cgLineSearchFactor_def, geom_sum_succ]
  ring

/-- One additional step propagates the previous adjacent-inner-product error and adds forcing. -/
private theorem cgAdjacentInnerFactor_succ (m : ℕ) (ε : ℝ) :
    cgAdjacentInnerFactor (m + 1) ε =
      (1 + 31 / 10 * ε) * cgAdjacentInnerFactor m ε + 13 * ε := by
  rw [cgAdjacentInnerFactor_def, cgAdjacentInnerFactor_def, geom_sum_succ]
  ring

/-- For $0\le\varepsilon$ and $m\varepsilon\le1/100$, the line-search factor is at most
$5m\varepsilon$. -/
theorem cgLineSearchFactor_le_mul {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : (m : ℝ) * ε ≤ 1 / 100) : cgLineSearchFactor m ε ≤ 5 * m * ε := by
  induction m with
  | zero => simp only [cgLineSearchFactor_def, Finset.range_zero, Finset.sum_empty,
      mul_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ m ih =>
    have hm : (m : ℝ) * ε ≤ 1 / 100 := by
      push_cast at hsmall
      nlinarith
    have h := mul_le_mul_of_nonneg_right hm hε
    rw [cgLineSearchFactor_succ]
    calc (1 + 31 / 10 * ε) * cgLineSearchFactor m ε + 41 / 10 * ε
        ≤ (1 + 31 / 10 * ε) * (5 * m * ε) + 41 / 10 * ε := by
          gcongr
          exact ih hm
      _ ≤ 5 * ((m + 1 : ℕ) : ℝ) * ε := by push_cast; nlinarith

/-- For $0\le\varepsilon$ and $m\varepsilon\le1/100$, the adjacent-inner-product factor is at
most $16m\varepsilon$. -/
theorem cgAdjacentInnerFactor_le_mul {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : (m : ℝ) * ε ≤ 1 / 100) : cgAdjacentInnerFactor m ε ≤ 16 * m * ε := by
  have h := cgLineSearchFactor_le_mul hε hsmall
  rw [cgLineSearchFactor_def] at h
  rw [cgAdjacentInnerFactor_def]
  have hmε : 0 ≤ (m : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε
  nlinarith only [h, hmε]

/-! ### Vector norms -/

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- The line search identity of a step taken, before the direction update:
$\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_{j+1} = \mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j -
\rho_j^2(1+\theta_j)(1+\eta^\gamma_j) + \gamma_je^\mu_j +
\mathbf{p}_j^{\mathsf{T}}\mathbf{e}^r_j$. -/
private theorem p_dotProduct_r_succ_eq {j : ℕ} (hj : j < k) :
    C.p j ⬝ᵥ C.r (j + 1) = C.p j ⬝ᵥ C.r j - C.ρ j ^ 2 * (1 + C.θ j) * (1 + C.eγ j) +
      C.γ j * C.eμ j + C.p j ⬝ᵥ C.er j := by
  have h1 : C.p j ⬝ᵥ C.s j = C.μ j - C.eμ j := by rw [C.μ_eq j hj]; ring
  have h2 := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le] at h2
  rw [C.r_succ j hj, dotProduct_add, dotProduct_sub, dotProduct_smul, h1, smul_eq_mul]
  linear_combination -h2

/-- The direction against its own residual: $\mathbf{p}_0^{\mathsf{T}}\mathbf{r}_0 = \rho_0^2$
and $\mathbf{p}_{i+1}^{\mathsf{T}}\mathbf{r}_{i+1} = \rho_{i+1}^2 +
\delta_i\mathbf{p}_i^{\mathsf{T}}\mathbf{r}_{i+1} + \mathbf{e}^{p\mathsf{T}}_i\mathbf{r}_{i+1}$. -/
private theorem p_dotProduct_r_self_zero : C.p 0 ⬝ᵥ C.r 0 = C.ρ 0 ^ 2 := by
  rw [C.p_zero, ← C.r_zero, ρ, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]

private theorem p_dotProduct_r_self_succ {i : ℕ} (hi : i < k) :
    C.p (i + 1) ⬝ᵥ C.r (i + 1) =
      C.ρ (i + 1) ^ 2 + C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) + C.ep i ⬝ᵥ C.r (i + 1) := by
  rw [C.p_succ i hi, add_dotProduct, add_dotProduct, smul_dotProduct, ρ,
    EuclideanSpace.norm_toLp_sq_eq_dotProduct_self,
    smul_eq_mul]

/-- The local term of the line search recursion,
$\lvert -\rho_j^2(\theta_j + \eta^\gamma_j + \theta_j\eta^\gamma_j) + \gamma_je^\mu_j +
\mathbf{p}_j^{\mathsf{T}}\mathbf{e}^r_j\rvert \le \varepsilon(2.01 + \Pi + 2.02K)\rho_j^2$. -/
private theorem abs_lineSearch_local_le {P K : ℝ} {j : ℕ} (hj : j < k)
    (hP : ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2) :
    |-(C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)) + C.γ j * C.eμ j + C.p j ⬝ᵥ C.er j| ≤
      C.ε * (201 / 100 + P + 202 / 100 * K) * C.ρ j ^ 2 := by
  have hγ := C.γ_pos hj
  have hρ := C.ρ_pos hj
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hθ := C.abs_θ_le j hj.le
  have he := C.abs_eγ_le j hj
  have hs := C.norm_s_le hj
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p j))
  have hN := specNorm_nonneg C.A
  set p := ‖WithLp.toLp 2 (C.p j)‖
  set G := specNorm C.A * C.γ j * p ^ 2
  have hG0 : 0 ≤ G := by positivity
  have a1 : |C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)| ≤ 201 / 100 * C.ε * C.ρ j ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ C.ρ j ^ 2)]
    have : |C.θ j + C.eγ j + C.θ j * C.eγ j| ≤ 201 / 100 * C.ε := by
      have h1 := abs_add_three (C.θ j) (C.eγ j) (C.θ j * C.eγ j)
      rw [abs_mul] at h1
      have h2 := mul_le_mul hθ he (abs_nonneg _) hε0
      nlinarith
    nlinarith
  have hsp : C.γ j * (p * ‖WithLp.toLp 2 (C.s j)‖) ≤ (1 + C.ε) * G := by
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg hγ.le hp0)
    calc _ = C.γ j * p * ‖WithLp.toLp 2 (C.s j)‖ := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have a2 : |C.γ j * C.eμ j| ≤ C.ε * ((1 + C.ε) * G) := by
    rw [abs_mul, abs_of_pos hγ]
    have := mul_le_mul_of_nonneg_left (C.abs_eμ_le j hj) hγ.le
    calc _ ≤ _ := this
      _ = C.ε * (C.γ j * (p * ‖WithLp.toLp 2 (C.s j)‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsp hε0
  have a3 : |C.p j ⬝ᵥ C.er j| ≤ C.ε * (p * C.ρ j) + C.ε * ((1 + C.ε) * G) := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    have := mul_le_mul_of_nonneg_left (C.norm_er_le_of_lt hj) hp0
    calc _ ≤ _ := this
      _ = C.ε * (p * C.ρ j) + C.ε * (C.γ j * (p * ‖WithLp.toLp 2 (C.s j)‖)) := by ring
      _ ≤ _ := by gcongr
  have hpρ : p * C.ρ j ≤ P * C.ρ j ^ 2 := by
    have := mul_le_mul_of_nonneg_right hP hρ.le
    linarith
  have hG : (1 + C.ε) * G ≤ 101 / 100 * (K * C.ρ j ^ 2) :=
    (mul_le_mul_of_nonneg_right (by linarith) hG0).trans
      (mul_le_mul_of_nonneg_left hK (by norm_num))
  have b1 := mul_le_mul_of_nonneg_left hpρ hε0
  have b2 := mul_le_mul_of_nonneg_left hG hε0
  have t := abs_add_three (-(C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j))) (C.γ j * C.eμ j)
    (C.p j ⬝ᵥ C.er j)
  rw [abs_neg] at t
  linarith only [t, a1, a2, a3, b1, b2]

/-- The direction-update term of the line search recursion:
$\lvert\mathbf{e}^{p\mathsf{T}}_i\mathbf{r}_{i+1}\rvert \le \varepsilon(2.05 + 1.05\Pi)
\rho_{i+1}^2$. -/
private theorem abs_ep_dotProduct_r_le {P : ℝ} {i : ℕ} (hi : i < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1)) :
    |C.ep i ⬝ᵥ C.r (i + 1)| ≤ C.ε * (41 / 20 + 21 / 20 * P) * C.ρ (i + 1) ^ 2 := by
  have hε0 := C.ε_nonneg
  have hρ := C.ρ_nonneg (i + 1)
  have hD := C.δ_mul_norm_p_le hi
  have h1 := mul_le_mul_of_nonneg_right (C.norm_ep_le_of_lt hi) hρ
  refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans (h1.trans ?_)
  have h2 : C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖ ≤ (41 / 20 + 21 / 20 * P) * C.ρ (i + 1) :=
    by nlinarith
  have := mul_le_mul_of_nonneg_left h2 hε0
  have := mul_le_mul_of_nonneg_right this hρ
  simp only [ρ] at *
  nlinarith

/-- The line-search defect for certificates $\|\mathbf{p}_i\|\le P\rho_i$ and
$\|\mathbf{A}\|_2\gamma_i\|\mathbf{p}_i\|^2\le K\rho_i^2$ ($i<k$), at any $j<k$,
satisfies <!-- value cgLineSearchFactor j+1 \varepsilon -->
$$\lvert\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_{j+1}\rvert\le
(41/10)\varepsilon\sum_{i=0}^{j+1-1}(1+(31/10)\varepsilon)^i(1+P+K)\rho_j^2.$$
This retains the geometric propagation omitted by the linear small-horizon bound.
[StrakosTichy2002, Theorem 9.1] gives a related condition-number estimate with higher-order
terms; the bound here follows from the run's explicit local errors. -/
theorem abs_p_dotProduct_r_succ_le_geom_sum {P K : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    {j : ℕ} (hj : j < k) :
    |C.p j ⬝ᵥ C.r (j + 1)| ≤
      cgLineSearchFactor (j + 1) C.ε * (1 + P + K) * C.ρ j ^ 2 := by
  have hk := C.k_pos
  have hε0 := C.ε_nonneg
  have hP0 := C.P_nonneg hk (hP 0 hk)
  have hK0 := C.nonneg_of_specNorm_mul_γ_mul_norm_p_sq_le hk (hK 0 hk)
  have hX : 0 ≤ 1 + P + K := by linarith
  induction j with
  | zero =>
    have h := C.abs_lineSearch_local_le hk (hP 0 hk) (hK 0 hk)
    have e : C.p 0 ⬝ᵥ C.r (0 + 1) = -(C.ρ 0 ^ 2 * (C.θ 0 + C.eγ 0 + C.θ 0 * C.eγ 0)) +
        C.γ 0 * C.eμ 0 + C.p 0 ⬝ᵥ C.er 0 := by
      rw [C.p_dotProduct_r_succ_eq hk, C.p_dotProduct_r_self_zero]
      ring
    rw [e]
    refine h.trans ?_
    simp only [cgLineSearchFactor_def, Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one]
    have hcoef : 201 / 100 + P + 202 / 100 * K ≤ 41 / 10 * (1 + P + K) := by linarith
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hε0)
      (sq_nonneg (C.ρ 0))
    linarith only [this]
  | succ i ih =>
    have hi : i < k := by omega
    have ih := ih hi
    have h1 := C.abs_lineSearch_local_le hj (hP (i + 1) hj) (hK (i + 1) hj)
    have h2 := C.abs_ep_dotProduct_r_le hi (hP (i + 1) hj)
    obtain ⟨hδ0, hδ1, -⟩ := C.δ_bounds hi
    have e : C.p (i + 1) ⬝ᵥ C.r (i + 1 + 1) = C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) +
        C.ep i ⬝ᵥ C.r (i + 1) + (-(C.ρ (i + 1) ^ 2 * (C.θ (i + 1) + C.eγ (i + 1) +
          C.θ (i + 1) * C.eγ (i + 1))) + C.γ (i + 1) * C.eμ (i + 1) +
          C.p (i + 1) ⬝ᵥ C.er (i + 1)) := by
      rw [C.p_dotProduct_r_succ_eq hj, C.p_dotProduct_r_self_succ hi]
      ring
    rw [e]
    have t := abs_add_three (C.δ i * (C.p i ⬝ᵥ C.r (i + 1))) (C.ep i ⬝ᵥ C.r (i + 1))
      (-(C.ρ (i + 1) ^ 2 * (C.θ (i + 1) + C.eγ (i + 1) + C.θ (i + 1) * C.eγ (i + 1))) +
        C.γ (i + 1) * C.eμ (i + 1) + C.p (i + 1) ⬝ᵥ C.er (i + 1))
    rw [abs_mul, abs_of_nonneg hδ0] at t
    set Y := cgLineSearchFactor (i + 1) C.ε * (1 + P + K)
    have hY0 : 0 ≤ Y := mul_nonneg (cgLineSearchFactor_nonneg _ hε0) hX
    have h3 : C.δ i * |C.p i ⬝ᵥ C.r (i + 1)| ≤
        Y * ((1 + 31 / 10 * C.ε) * C.ρ (i + 1) ^ 2) := by
      calc _ ≤ C.δ i * (Y * C.ρ i ^ 2) := mul_le_mul_of_nonneg_left ih hδ0
        _ = Y * (C.δ i * C.ρ i ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hδ1 hY0
    have hcoef : (41 / 20 + 21 / 20 * P) + (201 / 100 + P + 202 / 100 * K) ≤
        41 / 10 * (1 + P + K) := by linarith
    have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hε0)
      (sq_nonneg (C.ρ (i + 1)))
    rw [cgLineSearchFactor_succ]
    dsimp only [Y] at h3
    nlinarith only [t, h1, h2, h3, h4]

/-- **The line search defect** [StrakosTichy2002, Theorem 9.1], a posteriori: with
$k\varepsilon\le1/100$, $\|\mathbf{p}_i\|\le P\rho_i$ and
$\|\mathbf{A}\|_2\gamma_i\|\mathbf{p}_i\|^2\le K\rho_i^2$ ($i<k$),
$$\lvert\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_{j+1}\rvert\le
5(j+1)\varepsilon(1+P+K)\rho_j^2,\qquad j<k.$$
Strakoš and Tichý state a condition-number bound with higher-order terms and residual ratios;
here normalized multipliers telescope. [BakeCarsonMa2025, Lemma 3] gives a related local
orthogonality bound for mixed-precision PCG with a different error model. -/
theorem abs_p_dotProduct_r_succ_le {P K : ℝ} (hsmall : (k : ℝ) * C.ε ≤ 1 / 100)
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    {j : ℕ} (hj : j < k) :
    |C.p j ⬝ᵥ C.r (j + 1)| ≤ 5 * (j + 1) * C.ε * (1 + P + K) * C.ρ j ^ 2 := by
  have hP0 := C.P_nonneg C.k_pos (hP 0 C.k_pos)
  have hK0 := C.nonneg_of_specNorm_mul_γ_mul_norm_p_sq_le C.k_pos (hK 0 C.k_pos)
  have h := cgLineSearchFactor_le_mul C.ε_nonneg
    (C.mul_ε_le_of_le hsmall (show j + 1 ≤ k by omega))
  refine (C.abs_p_dotProduct_r_succ_le_geom_sum hP hK hj).trans ?_
  have := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 1 + P + K)
  have := mul_le_mul_of_nonneg_right this (sq_nonneg (C.ρ j))
  exact_mod_cast this

/-- The adjacent inner product of the run's Lanczos data:
$\bar p_j = -\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_{j+1}/(\gamma_j\rho_j^2)$. -/
private theorem adjacentInner_eq {j : ℕ} (hj : j < k) :
    C.toLanczosData.adjacentInner j = -(C.r j ⬝ᵥ C.r (j + 1)) / (C.γ j * C.ρ j ^ 2) := by
  have hγ := (C.γ_pos hj).ne'
  have hρ := (C.ρ_pos hj).ne'
  simp only [LanczosData.adjacentInner, toLanczosData]
  rw [C.lanczosβ_smul_lanczosV hj, C.lanczosV_succ hj, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  have : (-1 : ℝ) ^ (j * 2) = 1 := by rw [mul_comm, pow_mul, neg_one_sq, one_pow]
  field_simp
  linear_combination (-(C.r j ⬝ᵥ C.r (j + 1))) * this

/-- The consecutive residuals of a step taken:
$\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_{j+1} =
\rho_j^2 - \gamma_j\mathbf{r}_j^{\mathsf{T}}\mathbf{s}_j
+ \mathbf{r}_j^{\mathsf{T}}\mathbf{e}^r_j$. -/
private theorem r_dotProduct_r_succ_eq {j : ℕ} (hj : j < k) :
    C.r j ⬝ᵥ C.r (j + 1) = C.ρ j ^ 2 - C.γ j * (C.r j ⬝ᵥ C.s j) + C.r j ⬝ᵥ C.er j := by
  rw [C.r_succ j hj, dotProduct_add, dotProduct_sub, dotProduct_smul, ρ,
    EuclideanSpace.norm_toLp_sq_eq_dotProduct_self,
    smul_eq_mul]

/-- The local part $R_j = -\rho_j^2(\theta_j + \eta^\gamma_j + \theta_j\eta^\gamma_j) +
\gamma_je^\mu_j + \mathbf{r}_j^{\mathsf{T}}\mathbf{e}^r_j$ of the consecutive-residual identity. -/
private noncomputable def localR (j : ℕ) : ℝ :=
  -(C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)) + C.γ j * C.eμ j + C.r j ⬝ᵥ C.er j

/-- The first consecutive residuals: $\mathbf{r}_0^{\mathsf{T}}\mathbf{r}_1 = R_0$. -/
private theorem r_dotProduct_r_one_eq : C.r 0 ⬝ᵥ C.r (0 + 1) = C.localR 0 := by
  have hk := C.k_pos
  have h1 : C.r 0 ⬝ᵥ C.s 0 = C.μ 0 - C.eμ 0 := by
    rw [C.μ_eq 0 hk, C.p_zero, ← C.r_zero]
    ring
  have h2 := C.γ_mul_μ hk
  rw [C.ν_eq' hk.le] at h2
  rw [C.r_dotProduct_r_succ_eq hk, h1, localR]
  linear_combination -h2

/-- The conjugacy defect $\zeta_{i+1} = \mathbf{p}_i^{\mathsf{T}}\mathbf{s}_{i+1}$ transports the
previous consecutive residuals: $\gamma_i\zeta_{i+1} = \mathbf{r}_i^{\mathsf{T}}\mathbf{r}_{i+1} +
S_{i+1}$ (one use of $\mathbf{A}^{\mathsf{T}} = \mathbf{A}$). -/
private theorem γ_mul_p_dotProduct_s_succ_eq {i : ℕ} (hi : i + 1 < k) :
    C.γ i * (C.p i ⬝ᵥ C.s (i + 1)) = C.r i ⬝ᵥ C.r (i + 1) +
      ((C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2) -
        C.δ i * (C.γ i * C.eμ i) - C.δ i * (C.p i ⬝ᵥ C.er i) +
        (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i + C.er i ⬝ᵥ C.p (i + 1) -
        C.γ i * (C.es i ⬝ᵥ C.p (i + 1)) + C.γ i * (C.p i ⬝ᵥ C.es (i + 1))) := by
  have hi' : i < k := by omega
  have hγ := (C.γ_pos hi').ne'
  -- symmetry
  have hsym : C.p i ⬝ᵥ (C.A *ᵥ C.p (i + 1)) = (C.A *ᵥ C.p i) ⬝ᵥ C.p (i + 1) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, C.transpose_A, dotProduct_comm]
  have hz : C.p i ⬝ᵥ C.s (i + 1) =
      (C.γ i)⁻¹ * ((C.r i - C.r (i + 1)) ⬝ᵥ C.p (i + 1) + C.er i ⬝ᵥ C.p (i + 1)) -
        C.es i ⬝ᵥ C.p (i + 1) + C.p i ⬝ᵥ C.es (i + 1) := by
    rw [C.s_eq (i + 1) hi, dotProduct_add, hsym, C.mulVec_p_eq hi', sub_dotProduct,
      smul_dotProduct, add_dotProduct, smul_eq_mul]
  -- the direction update against the residual difference
  have hpr : (C.r i - C.r (i + 1)) ⬝ᵥ C.p (i + 1) = C.r i ⬝ᵥ C.r (i + 1) +
      C.δ i * (C.p i ⬝ᵥ (C.r i - C.r (i + 1))) - C.ρ (i + 1) ^ 2 +
      (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i := by
    rw [C.p_succ i hi', dotProduct_add, dotProduct_add, dotProduct_smul, sub_dotProduct,
      sub_dotProduct, ρ, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, smul_eq_mul,
        dotProduct_comm (C.r i) (C.p i),
      dotProduct_comm (C.r (i + 1)) (C.p i), dotProduct_sub]
    ring
  have hpd : C.p i ⬝ᵥ (C.r i - C.r (i + 1)) =
      C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i) - C.γ i * C.eμ i - C.p i ⬝ᵥ C.er i := by
    have h1 := C.p_dotProduct_r_succ_eq hi'
    rw [dotProduct_sub]
    linarith
  rw [hz, hpr, hpd]
  field_simp
  ring

/-- **The consecutive-residual recursion**:
$\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_{j+1} = (\gamma_j\delta_i/\gamma_i)(\mathbf{r}_i^{\mathsf{T}}
\mathbf{r}_j + S_j) + R_j + \gamma_j\mathbf{e}^{p\mathsf{T}}_i\mathbf{s}_j$, $j = i + 1 < k$. -/
private theorem r_dotProduct_r_succ_succ_eq {i : ℕ} (hi : i + 1 < k) :
    C.r (i + 1) ⬝ᵥ C.r (i + 1 + 1) = C.γ (i + 1) * C.δ i / C.γ i *
      (C.γ i * (C.p i ⬝ᵥ C.s (i + 1))) + C.localR (i + 1) +
        C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1)) := by
  have hi' : i < k := by omega
  have hγ := (C.γ_pos hi').ne'
  have h1 : C.r (i + 1) ⬝ᵥ C.s (i + 1) =
      C.μ (i + 1) - C.eμ (i + 1) - C.δ i * (C.p i ⬝ᵥ C.s (i + 1)) - C.ep i ⬝ᵥ C.s (i + 1) := by
    have hr : C.r (i + 1) = C.p (i + 1) - C.δ i • C.p i - C.ep i := by
      rw [C.p_succ i hi']
      abel
    rw [hr, sub_dotProduct, sub_dotProduct, smul_dotProduct, C.μ_eq (i + 1) hi, smul_eq_mul]
    ring
  have h2 := C.γ_mul_μ hi
  rw [C.ν_eq' hi.le] at h2
  rw [C.r_dotProduct_r_succ_eq hi, h1, localR]
  field_simp
  linear_combination -h2

/-- $\lvert(1+x)(1+y)(1+z) - 1\rvert \le 3.04\varepsilon$ for $\lvert x\rvert, \lvert y\rvert,
\lvert z\rvert \le \varepsilon \le 1/100$. -/
private theorem abs_one_add_mul_three_sub_one_le {x y z ε : ℝ} (hx : |x| ≤ ε) (hy : |y| ≤ ε)
    (hz : |z| ≤ ε) (hε : ε ≤ 1 / 100) :
    |(1 + x) * (1 + y) * (1 + z) - 1| ≤ 304 / 100 * ε := by
  have hε0 : 0 ≤ ε := (abs_nonneg x).trans hx
  have e : (1 + x) * (1 + y) * (1 + z) - 1 = x + y + z + (x * y + y * z + x * z) + x * y * z := by
    ring
  rw [e]
  have h1 : |x * y| ≤ ε * ε := by rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hε0
  have h2 : |y * z| ≤ ε * ε := by rw [abs_mul]; exact mul_le_mul hy hz (abs_nonneg _) hε0
  have h3 : |x * z| ≤ ε * ε := by rw [abs_mul]; exact mul_le_mul hx hz (abs_nonneg _) hε0
  have h4 : |x * y * z| ≤ ε * ε * ε := by
    rw [abs_mul]; exact mul_le_mul h1 hz (abs_nonneg _) (by positivity)
  have t1 := abs_add_three x y z
  have t2 := abs_add_three (x * y) (y * z) (x * z)
  have t3 := abs_add_le (x + y + z + (x * y + y * z + x * z)) (x * y * z)
  have t4 := abs_add_le (x + y + z) (x * y + y * z + x * z)
  have hεε : ε * ε ≤ 1 / 100 * ε := mul_le_mul_of_nonneg_right hε hε0
  have hεεε : ε * ε * ε ≤ 1 / 100 * ε := by
    have h5 := mul_le_mul_of_nonneg_right hεε hε0
    have h6 : 1 / 100 * ε * ε ≤ 1 / 100 * ε := by nlinarith
    linarith
  linarith

/-- The local part of the consecutive-residual recursion, with the direction-update term,
relative to $\|\mathbf{A}\|_2\gamma_j\rho_j^2$:
$\lvert R_j\rvert \le \varepsilon(5\Pi^2 + 2\Pi)\|\mathbf{A}\|_2\gamma_j\rho_j^2$. -/
private theorem abs_localR_le {P : ℝ} {j : ℕ} (hj : j < k)
    (hP : ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j) :
    |C.localR j| ≤ C.ε * (5 * P ^ 2 + 2 * P) * (specNorm C.A * C.γ j * C.ρ j ^ 2) := by
  have hγ := C.γ_pos hj
  have hρ := C.ρ_pos hj
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p j))
  have hP0 := C.P_nonneg hj hP
  have hs := C.norm_s_le hj
  have heμ := C.abs_eμ_le j hj
  have her := C.norm_er_le_of_lt hj
  set N := specNorm C.A
  set ρ := C.ρ j
  set γ := C.γ j
  set p := ‖WithLp.toLp 2 (C.p j)‖
  set G := N * γ * ρ ^ 2 with hG
  have hG0 : 0 ≤ G := mul_nonneg (mul_nonneg hN hγ.le) (sq_nonneg ρ)
  have hp2 : p ^ 2 ≤ P ^ 2 * ρ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hp0 hP 2
  have hNγp : N * γ * p ^ 2 ≤ P ^ 2 * G := by
    have := mul_le_mul_of_nonneg_left hp2 (mul_nonneg hN hγ.le)
    linarith only [this]
  have hρ2 : ρ ^ 2 ≤ 21 / 20 * (P ^ 2 * G) := by
    have := C.ρ_sq_le hj
    have : 21 / 20 * N * γ * p ^ 2 ≤ 21 / 20 * (P ^ 2 * G) := by linarith only [hNγp]
    linarith
  -- three terms
  have a1 : |-(ρ ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j))| ≤ C.ε * (212 / 100 * (P ^ 2 * G)) := by
    rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg ρ)]
    have h1 : |C.θ j + C.eγ j + C.θ j * C.eγ j| ≤ 201 / 100 * C.ε := by
      have h2 := abs_add_three (C.θ j) (C.eγ j) (C.θ j * C.eγ j)
      have h3 : |C.θ j * C.eγ j| ≤ C.ε * C.ε := by
        rw [abs_mul]
        exact mul_le_mul (C.abs_θ_le j hj.le) (C.abs_eγ_le j hj) (abs_nonneg _) hε0
      have := mul_le_mul_of_nonneg_right hε hε0
      linarith [C.abs_θ_le j hj.le, C.abs_eγ_le j hj]
    have := mul_le_mul h1 hρ2 (sq_nonneg _) (by linarith)
    have := mul_nonneg hε0 (mul_nonneg (sq_nonneg P) hG0)
    linarith
  have hγps : γ * (p * ‖WithLp.toLp 2 (C.s j)‖) ≤ (1 + C.ε) * (N * γ * p ^ 2) := by
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg hγ.le hp0)
    linarith only [this]
  have a2 : |γ * C.eμ j| ≤ C.ε * (101 / 100 * (P ^ 2 * G)) := by
    rw [abs_mul, abs_of_pos hγ]
    have h1 := mul_le_mul_of_nonneg_left heμ hγ.le
    have h2 : (1 + C.ε) * (N * γ * p ^ 2) ≤ 101 / 100 * (P ^ 2 * G) :=
      (mul_le_mul_of_nonneg_right (by linarith : 1 + C.ε ≤ 101 / 100)
        (mul_nonneg (mul_nonneg hN hγ.le) (sq_nonneg p))).trans
        (mul_le_mul_of_nonneg_left hNγp (by norm_num))
    have h3 := mul_le_mul_of_nonneg_left (hγps.trans h2) hε0
    linarith only [h1, h3]
  have a3 : |C.r j ⬝ᵥ C.er j| ≤ C.ε * (21 / 20 * (P ^ 2 * G)) + C.ε * (101 / 100 * (P * G)) := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    change ρ * ‖WithLp.toLp 2 (C.er j)‖ ≤ _
    have h1 := mul_le_mul_of_nonneg_left her hρ.le
    have h2 : ρ * (γ * ‖WithLp.toLp 2 (C.s j)‖) ≤ 101 / 100 * (P * G) := by
      have := mul_le_mul_of_nonneg_left hs (mul_nonneg hρ.le hγ.le)
      have h3 : ρ * γ * ((1 + C.ε) * N * p) ≤ ρ * γ * ((1 + C.ε) * N * (P * ρ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (mul_nonneg (by linarith) hN))
          (mul_nonneg hρ.le hγ.le)
      have h4 : ρ * γ * ((1 + C.ε) * N * (P * ρ)) = (1 + C.ε) * (P * G) := by
        simp only [hG]; ring
      have h5 : (1 + C.ε) * (P * G) ≤ 101 / 100 * (P * G) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hP0 hG0)
      linarith only [this, h3, h4, h5]
    have h6 : ρ * (C.ε * (ρ + γ * ‖WithLp.toLp 2 (C.s j)‖)) =
        C.ε * ρ ^ 2 + C.ε * (ρ * (γ * ‖WithLp.toLp 2 (C.s j)‖)) := by ring
    have h7 := mul_le_mul_of_nonneg_left hρ2 hε0
    have h8 := mul_le_mul_of_nonneg_left h2 hε0
    linarith only [h1, h6, h7, h8]
  have t := abs_add_three (-(ρ ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j))) (γ * C.eμ j)
    (C.r j ⬝ᵥ C.er j)
  have hPG : 0 ≤ P * G := mul_nonneg hP0 hG0
  have e : C.ε * (5 * P ^ 2 + 2 * P) * G = C.ε * (5 * (P ^ 2 * G)) + C.ε * (2 * (P * G)) := by ring
  rw [localR, e]
  have hεPG := mul_nonneg hε0 hPG
  have hεP2G := mul_nonneg hε0 (mul_nonneg (sq_nonneg P) hG0)
  linarith only [t, a1, a2, a3, hεPG, hεP2G]

/-- The direction-update term of the consecutive-residual recursion:
$\gamma_j\lvert\mathbf{e}^{p\mathsf{T}}_i\mathbf{s}_j\rvert \le
\varepsilon(1.1\Pi^2 + 2.1\Pi)\|\mathbf{A}\|_2\gamma_j\rho_j^2$, $j = i + 1$. -/
private theorem abs_γ_mul_ep_dotProduct_s_le {P : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1)) :
    |C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1))| ≤
      C.ε * (11 / 10 * P ^ 2 + 21 / 10 * P) * (specNorm C.A * C.γ (i + 1) * C.ρ (i + 1) ^ 2) := by
  have hi' : i < k := by omega
  have hγ := C.γ_pos hi
  have hρ := C.ρ_pos hi
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  have hP0 := C.P_nonneg hi hP
  rw [abs_mul, abs_of_pos hγ]
  have h1 := EuclideanSpace.abs_dotProduct_le_norm (C.ep i) (C.s (i + 1))
  have h2 := C.norm_ep_le_of_lt hi'
  have h3 := C.norm_s_le hi
  have hD := C.δ_mul_norm_p_le hi'
  have hep : ‖WithLp.toLp 2 (C.ep i)‖ ≤ C.ε * ((41 / 20 + 21 / 20 * P) * C.ρ (i + 1)) := by
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hε0)
    nlinarith
  have hsn : ‖WithLp.toLp 2 (C.s (i + 1))‖ ≤ 101 / 100 * specNorm C.A * (P * C.ρ (i + 1)) := by
    refine h3.trans ?_
    have := mul_le_mul_of_nonneg_left hP (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + C.ε) hN)
    have h4 : (1 + C.ε) * specNorm C.A * (P * C.ρ (i + 1)) ≤
        101 / 100 * specNorm C.A * (P * C.ρ (i + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hN) (by positivity)
    linarith
  have h5 := mul_le_mul hep hsn (norm_nonneg _) (by positivity)
  have h6 : C.ε * ((41 / 20 + 21 / 20 * P) * C.ρ (i + 1)) *
      (101 / 100 * specNorm C.A * (P * C.ρ (i + 1))) ≤
      C.ε * (11 / 10 * P ^ 2 + 21 / 10 * P) * (specNorm C.A * C.ρ (i + 1) ^ 2) := by
    have hX : 0 ≤ C.ε * specNorm C.A * C.ρ (i + 1) ^ 2 := by positivity
    have : (41 / 20 + 21 / 20 * P) * (101 / 100 * P) ≤ 11 / 10 * P ^ 2 + 21 / 10 * P := by
      nlinarith
    have := mul_le_mul_of_nonneg_left this hX
    linarith only [this]
  have h7 := mul_le_mul_of_nonneg_left (h1.trans (h5.trans h6)) hγ.le
  linarith only [h7]

/-- The scalar inequality behind the bound on the transported term of Lemma B. -/
private theorem transport_scalar_le {ε N B P ρ D p q b : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (hN : 0 ≤ N) (hB : 0 ≤ B) (hP : 0 ≤ P) (hρ : 0 ≤ ρ) (hD0 : 0 ≤ D) (hp0 : 0 ≤ p)
    (hq0 : 0 ≤ q) (hD : D ≤ 21 / 20 * (p + ρ)) (hp : p ≤ P * ρ)
    (hq : q ≤ (1 + 31 / 10 * ε) * B * ρ) (hb : b ≤ B) :
    N * ((1 + ε) * D ^ 2 + (1 + ε) * D ^ 2 + (1 + ε) * D * p + D * p + D * p) + q * D +
      (q + b * ρ) * (ρ + D) + q * p + 304 / 100 * B * ρ ^ 2 ≤
      6 * (N * (1 + P) ^ 2 * ρ ^ 2) + 10 * (B * (1 + P) * ρ ^ 2) := by
  have hDm : D ≤ 21 / 20 * ((1 + P) * ρ) := by nlinarith
  have hpm : p ≤ (1 + P) * ρ := by nlinarith
  have hqm : q ≤ 1031 / 1000 * B * ρ := by nlinarith [mul_nonneg hB hρ]
  have hX : 0 ≤ (1 + P) * ρ := by positivity
  have hD2 : D ^ 2 ≤ (21 / 20) ^ 2 * ((1 + P) * ρ) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hD0 hDm 2
  have hDp : D * p ≤ 21 / 20 * ((1 + P) * ρ) * (P * ρ) := mul_le_mul hDm hp hp0 (by positivity)
  have hqD : q * D ≤ 1031 / 1000 * B * ρ * (21 / 20 * ((1 + P) * ρ)) :=
    mul_le_mul hqm hDm hD0 (by positivity)
  have hqp : q * p ≤ 1031 / 1000 * B * ρ * (P * ρ) := mul_le_mul hqm hp hp0 (by positivity)
  have hqb : (q + b * ρ) * (ρ + D) ≤
      (1031 / 1000 * B * ρ + B * ρ) * (ρ + 21 / 20 * ((1 + P) * ρ)) :=
    mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
  have hN1 : N * ((1 + ε) * D ^ 2 + (1 + ε) * D ^ 2 + (1 + ε) * D * p + D * p + D * p) ≤
      N * (2 * (101 / 100) * ((21 / 20) ^ 2 * ((1 + P) * ρ) ^ 2) +
        (101 / 100 + 2) * (21 / 20 * ((1 + P) * ρ) * (P * ρ))) := by
    apply mul_le_mul_of_nonneg_left _ hN
    have h1 : (1 + ε) * D ^ 2 ≤ 101 / 100 * ((21 / 20) ^ 2 * ((1 + P) * ρ) ^ 2) :=
      mul_le_mul (by linarith) hD2 (sq_nonneg _) (by norm_num)
    have h2 : (1 + ε) * D * p ≤ 101 / 100 * (21 / 20 * ((1 + P) * ρ) * (P * ρ)) := by
      rw [mul_assoc]
      exact mul_le_mul (by linarith) hDp (by positivity) (by norm_num)
    linarith
  have hN2 : N * (2 * (101 / 100) * ((21 / 20) ^ 2 * ((1 + P) * ρ) ^ 2) +
        (101 / 100 + 2) * (21 / 20 * ((1 + P) * ρ) * (P * ρ))) ≤ 6 * (N * (1 + P) ^ 2 * ρ ^ 2) := by
    have h1 : 0 ≤ N * ρ ^ 2 * P := by positivity
    have h2 : 0 ≤ N * ρ ^ 2 := by positivity
    have h3 : 0 ≤ N * ρ ^ 2 * P ^ 2 := by positivity
    nlinarith
  have hB1 : 0 ≤ B * ρ ^ 2 := by positivity
  have hB2 : 0 ≤ B * ρ ^ 2 * P := by positivity
  nlinarith

/-- $\delta_i\|\mathbf{s}_i\| \le (1 + \varepsilon)\|\mathbf{A}\|_2\delta_i\|\mathbf{p}_i\|$. -/
private theorem δ_mul_norm_s_le {i : ℕ} (hi : i < k) :
    C.δ i * ‖WithLp.toLp 2 (C.s i)‖ ≤
      (1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) := by
  have := mul_le_mul_of_nonneg_left (C.norm_s_le hi) (C.δ_bounds hi).1
  linarith only [this]

/-- The first transported term: $\lvert\delta_i\rho_i^2(1+\theta_i)(1+\eta^\gamma_i) -
\rho_{i+1}^2\rvert \le 3.04\varepsilon\rho_{i+1}^2$. -/
private theorem abs_transport_first_le {i : ℕ} (hi : i + 1 < k) :
    |C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2| ≤
      304 / 100 * C.ε * C.ρ (i + 1) ^ 2 := by
  have hi' : i < k := by omega
  have hε := C.ε_le
  have hρ' := C.ρ_pos hi'
  have hν : C.δ i * (C.ρ i ^ 2 * (1 + C.θ i)) = C.ρ (i + 1) ^ 2 * (1 + C.θ (i + 1)) *
      (1 + C.eδ i) := by
    have h1 := C.one_add_θ_pos hi'.le
    rw [C.δ_eq i hi', C.ν_eq' hi.le, C.ν_eq' hi'.le]
    field_simp
  have e : C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2 =
      C.ρ (i + 1) ^ 2 * ((1 + C.θ (i + 1)) * (1 + C.eδ i) * (1 + C.eγ i) - 1) := by
    linear_combination (1 + C.eγ i) * hν
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have := abs_one_add_mul_three_sub_one_le (C.abs_θ_le (i + 1) hi.le) (C.abs_eδ_le i hi')
    (C.abs_eγ_le i hi') hε
  have := mul_le_mul_of_nonneg_left this (sq_nonneg (C.ρ (i + 1)))
  linarith only [this]

/-- The transported terms with $e^\mu_i$ and $\mathbf{e}^r_i$ against $\mathbf{p}_i$. -/
private theorem transport_mu_er_le {i : ℕ} (hi : i + 1 < k) :
    (C.δ i / C.γ i * |C.δ i * (C.γ i * C.eμ i)| ≤
      C.ε * ((1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) ^ 2)) ∧
    (C.δ i / C.γ i * |C.δ i * (C.p i ⬝ᵥ C.er i)| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i) * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) +
        (1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) ^ 2)) := by
  have hi' : i < k := by omega
  have hγ' := C.γ_pos hi'
  have hρ' := C.ρ_pos hi'
  have hε0 := C.ε_nonneg
  obtain ⟨hδ0, -, -⟩ := C.δ_bounds hi'
  have hb0 : 0 ≤ C.δ i / C.γ i := div_nonneg hδ0 hγ'.le
  have hD0 : 0 ≤ C.δ i * ‖WithLp.toLp 2 (C.p i)‖ := mul_nonneg hδ0 (norm_nonneg _)
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p (i + 1)))
  have hpi0 := norm_nonneg (WithLp.toLp 2 (C.p i))
  have her' := C.norm_er_le_of_lt hi'
  have hδs := C.δ_mul_norm_s_le hi'
  have heμ' := C.abs_eμ_le i hi'
  have hb' : C.δ i / C.γ i * |C.δ i * (C.γ i * C.eμ i)| ≤
      C.ε * ((1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) ^ 2) := by
    have e : C.δ i / C.γ i * |C.δ i * (C.γ i * C.eμ i)| = C.δ i ^ 2 * |C.eμ i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hδ0, abs_of_pos hγ']
      field_simp
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left heμ' (sq_nonneg (C.δ i))
    have h2 : C.δ i ^ 2 * (C.ε * ‖WithLp.toLp 2 (C.p i)‖ * ‖WithLp.toLp 2 (C.s i)‖) =
        C.ε * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) * (C.δ i * ‖WithLp.toLp 2 (C.s i)‖) := by ring
    have h3 := mul_le_mul_of_nonneg_left hδs (mul_nonneg hε0 hD0)
    nlinarith
  have hc : C.δ i / C.γ i * |C.δ i * (C.p i ⬝ᵥ C.er i)| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i) * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) +
        (1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hδ0]
    have h1 := EuclideanSpace.abs_dotProduct_le_norm (C.p i) (C.er i)
    have h2 := mul_le_mul_of_nonneg_left her' hpi0
    have h3 : C.δ i / C.γ i * (C.δ i * (‖WithLp.toLp 2 (C.p i)‖ *
        (C.ε * (C.ρ i + C.γ i * ‖WithLp.toLp 2 (C.s i)‖)))) =
        C.ε * ((C.δ i * C.ρ i / C.γ i) * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) +
          (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) * (C.δ i * ‖WithLp.toLp 2 (C.s i)‖)) := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_left hδs hD0
    have h5 : C.δ i / C.γ i * (C.δ i * |C.p i ⬝ᵥ C.er i|) ≤
        C.δ i / C.γ i * (C.δ i * (‖WithLp.toLp 2 (C.p i)‖ *
          (C.ε * (C.ρ i + C.γ i * ‖WithLp.toLp 2 (C.s i)‖)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h1.trans h2) hδ0) hb0
    rw [h3] at h5
    have h6 := mul_le_mul_of_nonneg_left h4 hε0
    nlinarith
  exact ⟨hb', hc⟩

/-- The transported terms with $\mathbf{e}^p_i$, $\mathbf{e}^r_i$ against $\mathbf{p}_{i+1}$,
and the product errors. -/
private theorem transport_ep_es_le {i : ℕ} (hi : i + 1 < k) :
    (C.δ i / C.γ i * |(C.r i - C.r (i + 1)) ⬝ᵥ C.ep i| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i + C.δ i / C.γ i * C.ρ (i + 1)) *
        (C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖))) ∧
    (C.δ i / C.γ i * |C.er i ⬝ᵥ C.p (i + 1)| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i) * ‖WithLp.toLp 2 (C.p (i + 1))‖ +
        (1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) *
          ‖WithLp.toLp 2 (C.p (i + 1))‖)) ∧
    (C.δ i / C.γ i * |C.γ i * (C.es i ⬝ᵥ C.p (i + 1))| ≤
      C.ε * (specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) *
        ‖WithLp.toLp 2 (C.p (i + 1))‖)) ∧
    (C.δ i / C.γ i * |C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| ≤
      C.ε * (specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) *
        ‖WithLp.toLp 2 (C.p (i + 1))‖)) := by
  have hi' : i < k := by omega
  have hγ' := C.γ_pos hi'
  have hρ' := C.ρ_pos hi'
  have hε0 := C.ε_nonneg
  obtain ⟨hδ0, -, -⟩ := C.δ_bounds hi'
  have hb0 : 0 ≤ C.δ i / C.γ i := div_nonneg hδ0 hγ'.le
  have hD0 : 0 ≤ C.δ i * ‖WithLp.toLp 2 (C.p i)‖ := mul_nonneg hδ0 (norm_nonneg _)
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p (i + 1)))
  have hpi0 := norm_nonneg (WithLp.toLp 2 (C.p i))
  have her' := C.norm_er_le_of_lt hi'
  have hδs := C.δ_mul_norm_s_le hi'
  have hep := C.norm_ep_le_of_lt hi'
  have hes := C.norm_es_le (i + 1) hi
  have hes' := C.norm_es_le i hi'
  have hd : C.δ i / C.γ i * |(C.r i - C.r (i + 1)) ⬝ᵥ C.ep i| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i + C.δ i / C.γ i * C.ρ (i + 1)) *
        (C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖)) := by
    have h1 := EuclideanSpace.abs_dotProduct_le_norm (C.r i - C.r (i + 1)) (C.ep i)
    have h2 := EuclideanSpace.norm_toLp_sub_le (C.r i) (C.r (i + 1))
    have h3 := mul_le_mul h2 hep (norm_nonneg _) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h3) hb0
    have e : C.δ i / C.γ i * ((‖WithLp.toLp 2 (C.r i)‖ + ‖WithLp.toLp 2 (C.r (i + 1))‖) *
        (C.ε * (C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖))) =
        C.ε * ((C.δ i * C.ρ i / C.γ i + C.δ i / C.γ i * C.ρ (i + 1)) *
          (C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖)) := by
      simp only [ρ]
      ring
    linarith only [h4, e]
  have he : C.δ i / C.γ i * |C.er i ⬝ᵥ C.p (i + 1)| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i) * ‖WithLp.toLp 2 (C.p (i + 1))‖ +
        (1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) *
          ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
    have h1 := EuclideanSpace.abs_dotProduct_le_norm (C.er i) (C.p (i + 1))
    have h2 := mul_le_mul_of_nonneg_right her' hp0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hb0
    have e : C.δ i / C.γ i * (C.ε * (C.ρ i + C.γ i * ‖WithLp.toLp 2 (C.s i)‖) *
        ‖WithLp.toLp 2 (C.p (i + 1))‖) = C.ε * ((C.δ i * C.ρ i / C.γ i) *
          ‖WithLp.toLp 2 (C.p (i + 1))‖ + (C.δ i * ‖WithLp.toLp 2 (C.s i)‖) *
            ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδs hp0) hε0
    linarith only [h3, e, h4]
  have hf : C.δ i / C.γ i * |C.γ i * (C.es i ⬝ᵥ C.p (i + 1))| ≤
      C.ε * (specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) *
        ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
    have e : C.δ i / C.γ i * |C.γ i * (C.es i ⬝ᵥ C.p (i + 1))| =
        C.δ i * |C.es i ⬝ᵥ C.p (i + 1)| := by
      rw [abs_mul, abs_of_pos hγ']
      field_simp
    rw [e]
    have h1 := EuclideanSpace.abs_dotProduct_le_norm (C.es i) (C.p (i + 1))
    have h2 := mul_le_mul_of_nonneg_right hes' hp0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hδ0
    linarith only [h3]
  have hg : C.δ i / C.γ i * |C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| ≤
      C.ε * (specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) *
        ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
    have e : C.δ i / C.γ i * |C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| =
        C.δ i * |C.p i ⬝ᵥ C.es (i + 1)| := by
      rw [abs_mul, abs_of_pos hγ']
      field_simp
    rw [e]
    have h1 := EuclideanSpace.abs_dotProduct_le_norm (C.p i) (C.es (i + 1))
    have h2 := mul_le_mul_of_nonneg_left hes hpi0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hδ0
    linarith only [h3]
  exact ⟨hd, he, hf, hg⟩

/-- **The transported term of Lemma B**: with $b = \delta_i/\gamma_i$,
$b\lvert S_{i+1}\rvert \le \varepsilon\bigl(6\|\mathbf{A}\|_2(1+\Pi)^2 + 10B(1+\Pi)\bigr)
\rho_{i+1}^2$; only $\delta_i/\gamma_i$ and $\beta_{i+1}$ enter. -/
private theorem transport_le {P B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1))
    (hβ : C.lanczosβ (i + 1) ≤ B) (hδB : C.δ i ≤ B * C.γ i) :
    C.δ i / C.γ i * |(C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2) -
        C.δ i * (C.γ i * C.eμ i) - C.δ i * (C.p i ⬝ᵥ C.er i) +
        (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i + C.er i ⬝ᵥ C.p (i + 1) -
        C.γ i * (C.es i ⬝ᵥ C.p (i + 1)) + C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| ≤
      C.ε * (6 * (specNorm C.A * (1 + P) ^ 2 * C.ρ (i + 1) ^ 2) +
        10 * (B * (1 + P) * C.ρ (i + 1) ^ 2)) := by
  have hi' : i < k := by omega
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hρ' := C.ρ_pos hi'
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  obtain ⟨hδ0, -, -⟩ := C.δ_bounds hi'
  have hP0 := C.P_nonneg hi hP
  have hb0 : 0 ≤ C.δ i / C.γ i := div_nonneg hδ0 hγ'.le
  have hb : C.δ i / C.γ i ≤ B := by rw [div_le_iff₀ hγ']; exact hδB
  have hB0 : 0 ≤ B := hb0.trans hb
  have hq := C.δ_mul_ρ_div_γ_le hi hβ
  have hq0 : 0 ≤ C.δ i * C.ρ i / C.γ i := div_nonneg (mul_nonneg hδ0 hρ'.le) hγ'.le
  have hD0 : 0 ≤ C.δ i * ‖WithLp.toLp 2 (C.p i)‖ := mul_nonneg hδ0 (norm_nonneg _)
  have ha := C.abs_transport_first_le hi
  obtain ⟨hb', hc⟩ := C.transport_mu_er_le hi
  obtain ⟨hd, he, hf, hg⟩ := C.transport_ep_es_le hi
  -- the triangle inequality
  have tri : C.δ i / C.γ i * |(C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2) -
        C.δ i * (C.γ i * C.eμ i) - C.δ i * (C.p i ⬝ᵥ C.er i) +
        (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i + C.er i ⬝ᵥ C.p (i + 1) -
        C.γ i * (C.es i ⬝ᵥ C.p (i + 1)) + C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| ≤
      C.δ i / C.γ i * |C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2| +
      C.δ i / C.γ i * |C.δ i * (C.γ i * C.eμ i)| + C.δ i / C.γ i * |C.δ i * (C.p i ⬝ᵥ C.er i)| +
      C.δ i / C.γ i * |(C.r i - C.r (i + 1)) ⬝ᵥ C.ep i| +
      C.δ i / C.γ i * |C.er i ⬝ᵥ C.p (i + 1)| +
      C.δ i / C.γ i * |C.γ i * (C.es i ⬝ᵥ C.p (i + 1))| +
      C.δ i / C.γ i * |C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| := by
    simp only [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hb0
    refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
    refine (abs_sub _ _).trans (add_le_add_left ?_ _)
    refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
    refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
    refine (abs_sub _ _).trans (add_le_add_left ?_ _)
    exact abs_sub _ _
  have ha' : C.δ i / C.γ i * |C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) -
      C.ρ (i + 1) ^ 2| ≤ C.ε * (304 / 100 * B * C.ρ (i + 1) ^ 2) := by
    have := mul_le_mul hb ha (abs_nonneg _) hB0
    linarith only [this]
  have hsc := transport_scalar_le hε0 hε hN hB0 hP0 hρ.le hD0 (norm_nonneg _) hq0
    (C.δ_mul_norm_p_le hi') hP hq hb
  have hsc' := mul_le_mul_of_nonneg_left hsc hε0
  linarith only [tri, ha', hb', hc, hd, he, hf, hg, hsc']

/-- **The recursion of Lemma B**: $\lvert\bar p_{i+1}\rvert \le (1 + 3.1\varepsilon)
\lvert\bar p_i\rvert + \varepsilon\bigl(13\|\mathbf{A}\|_2(1+\Pi)^2 + 10B(1+\Pi)\bigr)$. -/
private theorem abs_adjacentInner_succ_le {P B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1))
    (hβ : C.lanczosβ (i + 1) ≤ B) (hδB : C.δ i ≤ B * C.γ i) :
    |C.toLanczosData.adjacentInner (i + 1)| ≤
      (1 + 31 / 10 * C.ε) * |C.toLanczosData.adjacentInner i| +
        C.ε * (13 * (specNorm C.A * (1 + P) ^ 2) + 10 * (B * (1 + P))) := by
  have hi' : i < k := by omega
  have hγ := C.γ_pos hi
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hρ' := C.ρ_pos hi'
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  obtain ⟨hδ0, hδ1, -⟩ := C.δ_bounds hi'
  have hP0 := C.P_nonneg hi hP
  have hG : 0 < C.γ (i + 1) * C.ρ (i + 1) ^ 2 := by positivity
  rw [C.adjacentInner_eq hi, C.adjacentInner_eq hi', abs_div, abs_div, abs_neg, abs_neg,
    abs_of_pos hG, abs_of_pos (by positivity : 0 < C.γ i * C.ρ i ^ 2), div_le_iff₀ hG]
  rw [C.r_dotProduct_r_succ_succ_eq hi, C.γ_mul_p_dotProduct_s_succ_eq hi]
  set S := (C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2) -
        C.δ i * (C.γ i * C.eμ i) - C.δ i * (C.p i ⬝ᵥ C.er i) +
        (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i + C.er i ⬝ᵥ C.p (i + 1) -
        C.γ i * (C.es i ⬝ᵥ C.p (i + 1)) + C.γ i * (C.p i ⬝ᵥ C.es (i + 1)) with hS
  have hT := C.transport_le hi hP hβ hδB
  rw [← hS] at hT
  have hR := C.abs_localR_le hi hP
  have hE := C.abs_γ_mul_ep_dotProduct_s_le hi hP
  set ψ := C.r i ⬝ᵥ C.r (i + 1)
  have hc0 : 0 ≤ C.γ (i + 1) * C.δ i / C.γ i := div_nonneg (mul_nonneg hγ.le hδ0) hγ'.le
  have t1 : |C.γ (i + 1) * C.δ i / C.γ i * (ψ + S) + C.localR (i + 1) +
      C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1))| ≤
      C.γ (i + 1) * C.δ i / C.γ i * |ψ| + C.γ (i + 1) * (C.δ i / C.γ i * |S|) +
        |C.localR (i + 1)| + |C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1))| := by
    have h1 := abs_add_three (C.γ (i + 1) * C.δ i / C.γ i * (ψ + S)) (C.localR (i + 1))
      (C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1)))
    rw [abs_mul, abs_of_nonneg hc0] at h1
    have h2 := mul_le_mul_of_nonneg_left (abs_add_le ψ S) hc0
    have e : C.γ (i + 1) * C.δ i / C.γ i * |S| = C.γ (i + 1) * (C.δ i / C.γ i * |S|) := by ring
    linarith only [h1, h2, e]
  -- the transported previous defect
  have t2 : C.γ (i + 1) * C.δ i / C.γ i * |ψ| ≤
      (1 + 31 / 10 * C.ε) * (|ψ| / (C.γ i * C.ρ i ^ 2)) * (C.γ (i + 1) * C.ρ (i + 1) ^ 2) := by
    have e : C.γ (i + 1) * C.δ i / C.γ i * |ψ| =
        C.γ (i + 1) * (C.δ i * C.ρ i ^ 2) * (|ψ| / (C.γ i * C.ρ i ^ 2)) := by
      field_simp
    rw [e]
    have hq0 : 0 ≤ |ψ| / (C.γ i * C.ρ i ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left hδ1 hγ.le
    have := mul_le_mul_of_nonneg_right this hq0
    linarith only [this]
  have t3 := mul_le_mul_of_nonneg_left hT hγ.le
  have hX : 0 ≤ C.ε * specNorm C.A * C.γ (i + 1) * C.ρ (i + 1) ^ 2 := by positivity
  have hpoly : 5 * P ^ 2 + 2 * P + (11 / 10 * P ^ 2 + 21 / 10 * P) ≤ 7 * (1 + P) ^ 2 := by
    nlinarith
  have t4 := mul_le_mul_of_nonneg_left hpoly hX
  have e : (C.ε * (13 * (specNorm C.A * (1 + P) ^ 2) + 10 * (B * (1 + P)))) *
      (C.γ (i + 1) * C.ρ (i + 1) ^ 2) = C.γ (i + 1) * (C.ε * (6 * (specNorm C.A * (1 + P) ^ 2 *
        C.ρ (i + 1) ^ 2) + 10 * (B * (1 + P) * C.ρ (i + 1) ^ 2))) +
        C.ε * specNorm C.A * C.γ (i + 1) * C.ρ (i + 1) ^ 2 * (7 * (1 + P) ^ 2) := by ring
  rw [add_mul, e]
  linarith only [t1, t2, t3, t4, hR, hE]

/-- Local orthogonality at any horizon: if $\|\mathbf{p}_i\|\le P\rho_i$ ($i<k$),
$\beta_{i+1}\le B$ and $\delta_i\le B\gamma_i$ ($i+1<k$), and $B\ge0$,
then for $j<k$, <!-- value cgAdjacentInnerFactor j+1 \varepsilon -->
$$\lvert\bar p_j\rvert\le13\varepsilon\sum_{i=0}^{j+1-1}(1+(31/10)\varepsilon)^i
\bigl(\|\mathbf{A}\|_2(1+P)^2+B(1+P)\bigr).$$
Here $\bar p_j$ is the adjacent inner product of the normalized Lanczos data.
No printed source. This retains geometric propagation instead of restricting the run length. -/
theorem abs_adjacentInner_le_geom_sum {P B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j)
    (hB0 : 0 ≤ B) {j : ℕ} (hj : j < k) :
    |C.toLanczosData.adjacentInner j| ≤ cgAdjacentInnerFactor (j + 1) C.ε *
      (specNorm C.A * (1 + P) ^ 2 + B * (1 + P)) := by
  have hk := C.k_pos
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  have hP0 := C.P_nonneg hk (hP 0 hk)
  have hX : 0 ≤ specNorm C.A * (1 + P) ^ 2 + B * (1 + P) := by positivity
  induction j with
  | zero =>
    have hγ := C.γ_pos hk
    have hρ0 := C.ρ_pos hk
    have hG : 0 < C.γ 0 * C.ρ 0 ^ 2 := by positivity
    rw [C.adjacentInner_eq hk, C.r_dotProduct_r_one_eq, abs_div, abs_neg, abs_of_pos hG,
      div_le_iff₀ hG]
    simp only [cgAdjacentInnerFactor_def, Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one]
    have hR := C.abs_localR_le hk (hP 0 hk)
    have h1 : 5 * P ^ 2 + 2 * P ≤ 13 * (1 + P) ^ 2 := by nlinarith
    have h2 : specNorm C.A * (1 + P) ^ 2 ≤
        specNorm C.A * (1 + P) ^ 2 + B * (1 + P) :=
      le_add_of_nonneg_right (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h1
      (by positivity : 0 ≤ C.ε * specNorm C.A * C.γ 0 * C.ρ 0 ^ 2)
    have h4 := mul_le_mul_of_nonneg_left h2
      (by positivity : (0 : ℝ) ≤ 13 * C.ε * (C.γ 0 * C.ρ 0 ^ 2))
    nlinarith only [hR, h3, h4]
  | succ i ih =>
    have hi : i < k := by omega
    have ih := ih hi
    obtain ⟨hβ, hδ⟩ := hB i hj
    have h := C.abs_adjacentInner_succ_le hj (hP (i + 1) hj) hβ hδ
    have hL : C.ε * (13 * (specNorm C.A * (1 + P) ^ 2) + 10 * (B * (1 + P))) ≤
        13 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P)) := by
      have hBp : 0 ≤ C.ε * (B * (1 + P)) := by positivity
      nlinarith only [hBp]
    have h2 := mul_le_mul_of_nonneg_left ih
      (by positivity : 0 ≤ 1 + 31 / 10 * C.ε)
    rw [cgAdjacentInnerFactor_succ]
    nlinarith only [h, hL, h2]

/-- **Local orthogonality with a linear horizon factor:** if $k\varepsilon\le1/100$,
$\|\mathbf{p}_i\|\le P\rho_i$ and
$\|\mathbf{A}\|_2\gamma_i\|\mathbf{p}_i\|^2\le K\rho_i^2$ ($i<k$),
$\beta_{i+1}\le B$ and $\delta_i\le B\gamma_i$ ($i+1<k$), and $B\ge0$, then
$$\lvert\bar p_j\rvert\le16(j+1)\varepsilon
\bigl(\|\mathbf{A}\|_2(1+P)^2+B(1+P+K)\bigr),\qquad j<k.$$
No printed source. The consecutive residual inner product is transported by the preceding
conjugacy defect. Nonnegative $B$ must be explicit for a one-step run. -/
theorem abs_adjacentInner_le {P K B : ℝ} (hsmall : (k : ℝ) * C.ε ≤ 1 / 100)
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) (hB0 : 0 ≤ B) {j : ℕ}
    (hj : j < k) :
    |C.toLanczosData.adjacentInner j| ≤
      16 * (j + 1) * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K)) := by
  have hP0 := C.P_nonneg C.k_pos (hP 0 C.k_pos)
  have hK0 := C.nonneg_of_specNorm_mul_γ_mul_norm_p_sq_le C.k_pos (hK 0 C.k_pos)
  have hN := specNorm_nonneg C.A
  have hε0 := C.ε_nonneg
  have h := cgAdjacentInnerFactor_le_mul hε0
    (C.mul_ε_le_of_le hsmall (show j + 1 ≤ k by omega))
  refine (C.abs_adjacentInner_le_geom_sum hP hB hB0 hj).trans ?_
  calc _ ≤ (16 * (j + 1) * C.ε) * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast h
    _ ≤ _ := by
      have hBPK : B * (1 + P) ≤ B * (1 + P + K) :=
        mul_le_mul_of_nonneg_left (by linarith) hB0
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hBPK) (by positivity)

/-- **Geometric a posteriori CG backward error**: a posteriori backward error without a run-length
restriction: if
$\|\mathbf{p}_i\|\le P\rho_i$ ($i<k$), $\beta_{i+1}\le B$ and
$\delta_i\le B\gamma_i$ ($i+1<k$), and $B\ge0$, then <!-- value normalizedBackwardBound k f p -->
$$\|\tilde{\mathbf{H}}-\mathbf{I}_{k+1}\otimes\mathbf{A}\|_{\mathsf{F}}
\le22k^2f+17k\sqrt{k}p,$$
where $f=8\varepsilon(\|\mathbf{A}\|_2(1+P)^2+B)$ and
with <!-- value cgAdjacentInnerFactor k \varepsilon -->
$$p=13\varepsilon\sum_{i=0}^{k-1}(1+(31/10)\varepsilon)^i
\bigl(\|\mathbf{A}\|_2(1+P)^2+B(1+P)\bigr).$$
No printed source. The certificate can grow with the horizon; positive definiteness is not
required for this backward-error bound.
Result: cg-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le_geom_sum_of_certificates {P B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j)
    (hB0 : 0 ≤ B) :
    frobNorm (C.backwardH - C.dilatedH) ≤
      normalizedBackwardBound k (8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B))
        (cgAdjacentInnerFactor k C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P))) := by
  have hP0 := C.P_nonneg C.k_pos (hP 0 C.k_pos)
  have hN := specNorm_nonneg C.A
  refine C.toNormalizedLanczosData.frobNorm_backwardH_sub_dilatedH_le
    (fun j hj => C.norm_recurrenceError_le hP hB hB0 hj) (fun j hj => ?_)
  refine (C.abs_adjacentInner_le_geom_sum hP hB hB0 hj).trans ?_
  exact mul_le_mul_of_nonneg_right
    (cgAdjacentInnerFactor_mono C.ε_nonneg (show j + 1 ≤ k by omega)) (by positivity)

/-- **The a posteriori backward model**: with $k\varepsilon\le1/100$ and the
certificates $\|\mathbf p_j\|\le\Pi\rho_j$ and
$\|\mathbf A\|_2\gamma_j\|\mathbf p_j\|^2\le K\rho_j^2$ for $j<k$,
and $\beta_{j+1}\le B$, $\delta_j\le B\gamma_j$ for $j+1<k$,
where $\rho_j=\|\mathbf r_j\|$,

$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}}
\le 22k^2 f + 17k\sqrt{k}\,p,
\quad f = 8\varepsilon(\|\mathbf{A}\|_2(1+\Pi)^2 + B),\
p = 16k\varepsilon(\|\mathbf{A}\|_2(1+\Pi)^2 + B(1+\Pi+K)) .$$
The certificates are computable from the run; in practice $\Pi \ll \sqrt{\kappa}$. It is the
engine of the a priori induction (`NLAlib/Krylov/FinitePrecision/CGBackward.lean`): the
model of the prefix `C.take j` needs $B$ for the steps $i + 1 < j$ only, which the models of the
shorter prefixes provide.
The hypothesis $0 \le B$ is automatic for $k \ge 2$ ($0 < \beta_1 \le B$) and is needed
for $k = 1$, where `hB` is vacuous.
No printed source.
Result: cg-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le_of_certificates {P K B : ℝ}
    (hsmall : (k : ℝ) * C.ε ≤ 1 / 100)
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) (hB0 : 0 ≤ B) :
    frobNorm (C.backwardH - C.dilatedH) ≤
      normalizedBackwardBound k (8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B))
        (16 * k * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K))) := by
  have hk := C.k_pos
  have hρ0 := C.ρ_pos hk
  have hP0 := C.P_nonneg hk (hP 0 hk)
  have hK0 := C.nonneg_of_specNorm_mul_γ_mul_norm_p_sq_le hk (hK 0 hk)
  have hX : 0 ≤ C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K)) := by
    have := C.ε_nonneg
    have := specNorm_nonneg C.A
    positivity
  refine C.toNormalizedLanczosData.frobNorm_backwardH_sub_dilatedH_le (fun j hj => ?_)
    (fun j hj => ?_)
  · exact C.norm_recurrenceError_le hP hB hB0 hj
  · refine (C.abs_adjacentInner_le hsmall hP hK hB hB0 hj).trans ?_
    have hjk : ((j : ℝ) + 1) ≤ k := by exact_mod_cast hj
    have := mul_le_mul_of_nonneg_right hjk hX
    linarith only [this]

/-- **The next direction is not small**: with $k\varepsilon\le1/100$ and certificates
$\Pi$, $K$ on the steps $j < k$ and
$20k\varepsilon(1 + \Pi + K) \le 1$, the direction after the last step satisfies
$\rho_k \le 2\|\mathbf{p}_k\|$. Thus $\mathbf{p}_k \ne \mathbf{0}$ whenever
$\mathbf{r}_k \ne \mathbf{0}$.
Positive next curvature additionally needs the spectral and rounding assumptions of
`NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`; this norm bound alone does not imply it. -/
theorem norm_r_le_two_mul_norm_p {P K : ℝ} (hwindow : (k : ℝ) * C.ε ≤ 1 / 100)
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hsmall : 20 * k * C.ε * (1 + P + K) ≤ 1) :
    C.ρ k ≤ 2 * ‖WithLp.toLp 2 (C.p k)‖ := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by have := C.k_pos; omega⟩
  have hi : i < i + 1 := Nat.lt_succ_self i
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hρi := C.ρ_pos hi
  have hρ := C.ρ_nonneg (i + 1)
  obtain ⟨hδ0, hδ1, -⟩ := C.δ_bounds hi
  have hτ := C.abs_p_dotProduct_r_succ_le hwindow hP hK hi
  set D := C.δ i * ‖WithLp.toLp 2 (C.p i)‖ with hD
  have hD0 : 0 ≤ D := mul_nonneg hδ0 (norm_nonneg _)
  set y := C.r (i + 1) + C.δ i • C.p i with hy
  -- the squared norm of `y`
  have hy2 : ‖WithLp.toLp 2 y‖ ^ 2 = C.ρ (i + 1) ^ 2 + D ^ 2 +
      2 * C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hy, hD, ρ, mul_pow,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self,
        EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (C.r (i + 1)) (C.p i)]
    ring
  -- the line search term is small
  have hτ' : |C.p i ⬝ᵥ C.r (i + 1)| ≤ 1 / 4 * C.ρ i ^ 2 := by
    refine hτ.trans ?_
    have e : 5 * ((i : ℝ) + 1) * C.ε * (1 + P + K) = 1 / 4 * (20 * ((i + 1 : ℕ) : ℝ) * C.ε *
        (1 + P + K)) := by
      push_cast
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 1 / 4)
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hcross : |2 * C.δ i * (C.p i ⬝ᵥ C.r (i + 1))| ≤ 52 / 100 * C.ρ (i + 1) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hδ0, abs_two]
    have h1 := mul_le_mul_of_nonneg_left hτ' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ0)
    have h2 : 2 * C.δ i * (1 / 4 * C.ρ i ^ 2) ≤
        1 / 2 * ((1 + 31 / 10 * C.ε) * C.ρ (i + 1) ^ 2) := by
      linarith only [hδ1]
    have h3 : 1 / 2 * ((1 + 31 / 10 * C.ε) * C.ρ (i + 1) ^ 2) ≤ 52 / 100 * C.ρ (i + 1) ^ 2 := by
      have := mul_le_mul_of_nonneg_right (show 1 + 31 / 10 * C.ε ≤ 104 / 100 by linarith)
        (sq_nonneg (C.ρ (i + 1)))
      linarith only [this]
    linarith only [h1, h2, h3]
  have hylow : 48 / 100 * C.ρ (i + 1) ^ 2 + D ^ 2 ≤ ‖WithLp.toLp 2 y‖ ^ 2 := by
    rw [hy2]
    linarith only [(abs_le.mp hcross).1]
  -- the update error
  have hep := C.norm_ep_le_of_lt hi
  rw [← hD] at hep
  have hpk : C.p (i + 1) = y + C.ep i := by rw [C.p_succ i hi, hy]
  have hpk' : ‖WithLp.toLp 2 y‖ - ‖WithLp.toLp 2 (C.ep i)‖ ≤ ‖WithLp.toLp 2 (C.p (i + 1))‖ := by
    have h := EuclideanSpace.norm_toLp_sub_le (C.p (i + 1)) (C.ep i)
    have e : C.p (i + 1) - C.ep i = y := by rw [hpk]; abel
    rw [e] at h
    linarith only [h]
  -- `‖y‖ ≥ ρ/2 + ε(ρ + D)`
  set T := C.ρ (i + 1) / 2 + C.ε * (C.ρ (i + 1) + D) with hT
  have hT0 : 0 ≤ T := by
    have := mul_nonneg hε0 (add_nonneg hρ hD0)
    linarith only [this, hρ, hT]
  have hT2 : T ^ 2 ≤ ‖WithLp.toLp 2 y‖ ^ 2 := by
    have h1 : T ≤ 51 / 100 * C.ρ (i + 1) + 1 / 100 * D := by
      have := mul_le_mul_of_nonneg_right hε (add_nonneg hρ hD0)
      linarith only [this, hT]
    have h2 : T ^ 2 ≤ (51 / 100 * C.ρ (i + 1) + 1 / 100 * D) ^ 2 := pow_le_pow_left₀ hT0 h1 2
    nlinarith [sq_nonneg (C.ρ (i + 1) - D), mul_nonneg hρ hD0]
  have hTy : T ≤ ‖WithLp.toLp 2 y‖ := (pow_le_pow_iff_left₀ hT0 (norm_nonneg _) two_ne_zero).1 hT2
  linarith only [hTy, hpk', hep, hT]

/-- **One step of the residual gap**: $\mathbf{g}_{j+1} = \mathbf{g}_j +
\gamma_j\mathbf{e}^s_j - \mathbf{A}\mathbf{e}^x_j - \mathbf{e}^r_j$ for
$\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j$, so for $j < k$
$$\|\mathbf{g}_{j+1}\| \le \|\mathbf{g}_j\| + \varepsilon\bigl(\|\mathbf{A}\|_2(\|\mathbf{x}_j\| +
4\gamma_j\|\mathbf{p}_j\|) + \|\mathbf{r}_j\|\bigr) .$$ -/
theorem norm_sub_mulVec_x_sub_r_succ_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x (j + 1) - C.r (j + 1))‖ ≤
      ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ + C.ε * (specNorm C.A *
        (‖WithLp.toLp 2 (C.x j)‖ + 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) := by
  have hstep := norm_sub_mulVec_sub_succ_le C.A C.b C.x C.p C.ex C.r C.s C.es C.er C.γ j
    (C.s_eq j hj) (C.x_succ j hj) (C.r_succ j hj)
  have hγ := C.γ_pos hj
  rw [Real.norm_eq_abs, abs_of_pos hγ] at hstep
  have h5 := C.norm_ex_le j hj
  have h6 := C.norm_er_le j hj
  have h7 := C.norm_es_le j hj
  have h8 := C.norm_s_le hj
  rw [abs_of_pos hγ] at h5 h6
  have hN := specNorm_nonneg C.A
  have hε := C.ε_nonneg
  have hε1 := C.ε_le
  have hp := norm_nonneg (WithLp.toLp 2 (C.p j))
  have hx := norm_nonneg (WithLp.toLp 2 (C.x j))
  have e1 := mul_le_mul_of_nonneg_left h5 hN
  have e2 := mul_le_mul_of_nonneg_left h7 hγ.le
  have e3 := mul_le_mul_of_nonneg_left h8 (mul_nonneg hε hγ.le)
  have e4 : C.ε * C.γ j * ((1 + C.ε) * specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖) ≤
      C.ε * C.γ j * (2 * specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖) := by
    gcongr
    linarith
  simp only [ρ] at *
  nlinarith

/-- **The residual gap** (true minus updated residual): with $\mathbf{x}_0 = \mathbf{0}$,
$\mathbf{r}_0 = \mathbf{b}$,
$$\|(\mathbf{b} - \mathbf{A}\mathbf{x}_k) - \mathbf{r}_k\| \le \varepsilon\sum_{j<k}
\bigl(\|\mathbf{A}\|_2(\|\mathbf{x}_j\| + 4\gamma_j\|\mathbf{p}_j\|) + \|\mathbf{r}_j\|\bigr) .$$
[Greenbaum1997SIMAX]; [StrakosTichy2002, (7.16)], there with $\|\mathbf{x}\| +
\max_j\|\mathbf{x}_j\|$ and $+O(\varepsilon^2)$. Local: no Lanczos reduction, no $\kappa$.
[BakeCarsonMa2025, Theorem 1] gives a related PCG gap bound through the same telescoping
mechanism, retaining a maximum-iterate factor.
Result: cg-residual-gap -/
theorem norm_sub_mulVec_x_sub_r_le :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      C.ε * ∑ j ∈ Finset.range k, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
        4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) := by
  suffices h : ∀ m ≤ k, ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x m - C.r m)‖ ≤
      C.ε * ∑ j ∈ Finset.range m, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
        4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) from h k le_rfl
  intro m hm
  induction m with
  | zero =>
    rw [C.x_zero, C.r_zero, Matrix.mulVec_zero, sub_zero, sub_self, WithLp.toLp_zero, norm_zero,
      Finset.sum_range_zero, mul_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add]
    exact (C.norm_sub_mulVec_x_sub_r_succ_le (by omega)).trans (by linarith [ih (by omega)])

end CGRun

end NLAlib
