/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.NormalizedBackward
public import NLAlib.Krylov.LinearSystems.CGTridiagonal

/-!
# A conjugate gradient run with bounded local errors

`NLAlib.CGRun n k` is $k$ steps of the Hestenes–Stiefel recurrence from $\mathbf{x}_0 = \mathbf{0}$,
$\mathbf{r}_0 = \mathbf{p}_0 = \mathbf{b}$, for a real symmetric $\mathbf{A}$, with a local error
in each operation bounded relative to its operands by one accuracy parameter $\varepsilon$
(0-based, step $j < k$):
$$\nu_j = \|\mathbf{r}_j\|^2(1 + \theta_j),\quad
\mathbf{s}_j = \mathbf{A}\mathbf{p}_j + \mathbf{e}^s_j,\quad
\mu_j = \mathbf{p}_j^{\mathsf{T}}\mathbf{s}_j + e^\mu_j,\quad
\gamma_j = \frac{\nu_j}{\mu_j}(1 + \eta^\gamma_j),$$
$$\mathbf{x}_{j+1} = \mathbf{x}_j + \gamma_j\mathbf{p}_j + \mathbf{e}^x_j,\quad
\mathbf{r}_{j+1} = \mathbf{r}_j - \gamma_j\mathbf{s}_j + \mathbf{e}^r_j,\quad
\delta_j = \frac{\nu_{j+1}}{\nu_j}(1 + \eta^\delta_j),\quad
\mathbf{p}_{j+1} = \mathbf{r}_{j+1} + \delta_j\mathbf{p}_j + \mathbf{e}^p_j .$$
This is an abstract local-error interface for the stability analysis. Applying its guarantees
to a particular program requires a separate execution theorem constructing this interface
from the decoded computed states; the recurrence assumptions alone do not provide that theorem.

The **Lanczos data of the run** (`NLAlib.CGRun.toNormalizedLanczosData`) are the normalised
residuals $\bar{\mathbf{v}}_{j+1} = (-1)^j\mathbf{r}_j/\|\mathbf{r}_j\|$ with the tridiagonal
matrix `NLAlib.cgTridiagonal` of the computed $\gamma_j$ and the norms $\rho_j =
\|\mathbf{r}_j\|$ of the computed residuals. The local errors of this datum (Lemmas A and B) are
bounded a posteriori in terms of three run certificates: $\Pi \ge
\|\mathbf{p}_j\|/\|\mathbf{r}_j\|$, $K \ge \|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2/
\|\mathbf{r}_j\|^2$, and $B$ bounding the coefficients $\beta_{j+1} =
\rho_{j+1}/(\gamma_j\rho_j)$ and $\delta_j/\gamma_j$ for $j + 1 < k$ (the last pair,
$\beta_k$ and $\delta_{k-1}/\gamma_{k-1}$, does not enter the local errors of $k$ steps). The
a priori bounds on the certificates are in
`NLAlib/Krylov/FinitePrecision/CGBackward.lean`.

Constants are unoptimised.

## Main definitions

* `NLAlib.CGPrecisionHorizon`: the sufficient accumulated-error horizon.
* `NLAlib.CGRun`: a run of $k$ steps with accuracy parameter $\varepsilon$.
* `NLAlib.CGRun.toLanczosData`, `NLAlib.CGRun.toNormalizedLanczosData`: its Lanczos data.
* `NLAlib.CGRun.backwardH`: the backward model of the run.

## Main results

* `NLAlib.CGRun.tridiagonal_toLanczosData`: the tridiagonal matrix is `NLAlib.cgTridiagonal`.
* `NLAlib.CGRun.norm_recurrenceError_le` (Lemma A): the recurrence error, for $0 \le B$.
* `NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`: the next curvature is positive.

Lemma B, the a posteriori backward model, the next division and the residual gap are in
`NLAlib/Krylov/FinitePrecision/CGRunModel.lean`.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The sufficient CG precision horizon $q^{5/2}\varepsilon\kappa^2\le10^{-5}$.
It is a hypothesis on requested steps, an error allowance and a condition ratio, not a
necessary condition for convergence or a finite-format range certificate.
[CarsonMaShao2026, (H)]. -/
def CGPrecisionHorizon (q : ℕ) (ε κ : ℝ) : Prop :=
  (q : ℝ) ^ 2 * Real.sqrt q * ε * κ ^ 2 ≤ 1 / 10 ^ 5

/-- Every shorter prefix satisfies a CG precision horizon when the error allowance is
nonnegative. The condition ratio may have either sign because it is squared. -/
theorem CGPrecisionHorizon.mono {m q : ℕ} {ε κ : ℝ} (h : CGPrecisionHorizon q ε κ)
    (hε : 0 ≤ ε) (hm : m ≤ q) : CGPrecisionHorizon m ε κ := by
  unfold CGPrecisionHorizon at h ⊢
  refine le_trans ?_ h
  gcongr

/-- **A conjugate gradient run with bounded local errors**: $k \ge 1$ steps of the
Hestenes–Stiefel recurrence from $\mathbf{x}_0 = \mathbf{0}$ for a real symmetric $\mathbf{A}$,
every operation exact up to an error bounded by $\varepsilon$ times its operands (the normwise
standard model), $\nu_j > 0$ and $\mu_j > 0$ at every step taken, and $\varepsilon \le 1/100$.
The run length is unrestricted; accumulated-error bounds state their horizon assumptions.
The computed $\nu_k$ after the last step may be $0$ (the program stops there).
Algorithm: cg (run model) -/
structure CGRun (n k : ℕ) where
  /-- The matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The right-hand side. -/
  b : Fin n → ℝ
  /-- The iterates $\mathbf{x}_j$. -/
  x : ℕ → Fin n → ℝ
  /-- The updated residuals $\mathbf{r}_j$. -/
  r : ℕ → Fin n → ℝ
  /-- The search directions $\mathbf{p}_j$. -/
  p : ℕ → Fin n → ℝ
  /-- The products $\mathbf{s}_j$. -/
  s : ℕ → Fin n → ℝ
  /-- The computed squared residual norms $\nu_j$. -/
  ν : ℕ → ℝ
  /-- The computed curvatures $\mu_j$. -/
  μ : ℕ → ℝ
  /-- The step lengths $\gamma_j$. -/
  γ : ℕ → ℝ
  /-- The direction coefficients $\delta_j$. -/
  δ : ℕ → ℝ
  /-- The error of the product. -/
  es : ℕ → Fin n → ℝ
  /-- The relative error of the squared residual norm. -/
  θ : ℕ → ℝ
  /-- The error of the curvature. -/
  eμ : ℕ → ℝ
  /-- The relative error of the step length. -/
  eγ : ℕ → ℝ
  /-- The error of the iterate update. -/
  ex : ℕ → Fin n → ℝ
  /-- The error of the residual update. -/
  er : ℕ → Fin n → ℝ
  /-- The relative error of the direction coefficient. -/
  eδ : ℕ → ℝ
  /-- The error of the direction update. -/
  ep : ℕ → Fin n → ℝ
  /-- The accuracy parameter. -/
  ε : ℝ
  /-- The matrix is symmetric. -/
  transpose_A : Aᵀ = A
  /-- The accuracy parameter is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- At least one step. -/
  k_pos : 0 < k
  /-- Small accuracy parameter. -/
  ε_le : ε ≤ 1 / 100
  /-- $\mathbf{x}_0 = \mathbf{0}$. -/
  x_zero : x 0 = 0
  /-- $\mathbf{r}_0 = \mathbf{b}$. -/
  r_zero : r 0 = b
  /-- $\mathbf{p}_0 = \mathbf{b}$. -/
  p_zero : p 0 = b
  /-- The computed squared residual norm. -/
  ν_eq : ∀ j ≤ k, ν j = ‖WithLp.toLp 2 (r j)‖ ^ 2 * (1 + θ j)
  /-- Its relative error. -/
  abs_θ_le : ∀ j ≤ k, |θ j| ≤ ε
  /-- No stop before the last step. -/
  ν_pos : ∀ j < k, 0 < ν j
  /-- The computed product. -/
  s_eq : ∀ j < k, s j = A *ᵥ p j + es j
  /-- The product error. -/
  norm_es_le : ∀ j < k,
    ‖WithLp.toLp 2 (es j)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 (p j)‖
  /-- The computed curvature. -/
  μ_eq : ∀ j < k, μ j = p j ⬝ᵥ s j + eμ j
  /-- The curvature error. -/
  abs_eμ_le : ∀ j < k, |eμ j| ≤ ε * ‖WithLp.toLp 2 (p j)‖ * ‖WithLp.toLp 2 (s j)‖
  /-- The curvature is positive at every step taken (the division succeeded). -/
  μ_pos : ∀ j < k, 0 < μ j
  /-- The step length. -/
  γ_eq : ∀ j < k, γ j = ν j / μ j * (1 + eγ j)
  /-- Its relative error. -/
  abs_eγ_le : ∀ j < k, |eγ j| ≤ ε
  /-- The iterate update. -/
  x_succ : ∀ j < k, x (j + 1) = x j + γ j • p j + ex j
  /-- The iterate update error. -/
  norm_ex_le : ∀ j < k, ‖WithLp.toLp 2 (ex j)‖ ≤
    ε * (‖WithLp.toLp 2 (x j)‖ + |γ j| * ‖WithLp.toLp 2 (p j)‖)
  /-- The residual update. -/
  r_succ : ∀ j < k, r (j + 1) = r j - γ j • s j + er j
  /-- The residual update error. -/
  norm_er_le : ∀ j < k, ‖WithLp.toLp 2 (er j)‖ ≤
    ε * (‖WithLp.toLp 2 (r j)‖ + |γ j| * ‖WithLp.toLp 2 (s j)‖)
  /-- The direction coefficient. -/
  δ_eq : ∀ j < k, δ j = ν (j + 1) / ν j * (1 + eδ j)
  /-- Its relative error. -/
  abs_eδ_le : ∀ j < k, |eδ j| ≤ ε
  /-- The direction update. -/
  p_succ : ∀ j < k, p (j + 1) = r (j + 1) + δ j • p j + ep j
  /-- The direction update error. -/
  norm_ep_le : ∀ j < k, ‖WithLp.toLp 2 (ep j)‖ ≤
    ε * (‖WithLp.toLp 2 (r (j + 1))‖ + |δ j| * ‖WithLp.toLp 2 (p j)‖)

/-! ### Vector norms -/

/-- The two spectral facts used for a symmetric matrix with spectrum in $[a, a']$, $a \ge 0$:
$\|\mathbf{A}\|_2 \le a'$ and $a\|\mathbf{p}\|^2 \le \mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$,
for a nonzero $\mathbf{p}$ (which makes the spectrum nonempty). -/
private theorem specNorm_le_and_le_dotProduct {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 ≤ a) (hs : spectrum ℝ A ⊆ Set.Icc a a') {p : Fin n → ℝ}
    (hp : p ≠ 0) :
    a ≤ a' ∧ specNorm A ≤ a' ∧ a * ‖WithLp.toLp 2 p‖ ^ 2 ≤ p ⬝ᵥ (A *ᵥ p) := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  have h₁ : a • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A :=
    (hH.smul_one_le_iff_spectrum_subset_Ici a).2 fun x hx => (hs hx).1
  have h₂ : A ≤ a' • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    (hH.le_smul_one_iff_spectrum_subset_Iic a').2 fun x hx => (hs hx).2
  have hq : ∀ x : Fin n → ℝ, a * ‖WithLp.toLp 2 x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) ∧
      x ⬝ᵥ (A *ᵥ x) ≤ a' * ‖WithLp.toLp 2 x‖ ^ 2 := by
    intro x
    have e1 := re_quadForm_le_re_quadForm_of_le h₁ x
    have e2 := re_quadForm_le_re_quadForm_of_le h₂ x
    rw [re_quadForm_real_smul_one] at e1 e2
    simp only [quadForm_def, star_trivial, RCLike.re_to_real] at e1 e2
    exact ⟨e1, e2⟩
  have hp0 : 0 < ‖WithLp.toLp 2 p‖ := by
    rw [norm_pos_iff]
    exact fun h => hp (by simpa using congrArg WithLp.ofLp h)
  have haa : a ≤ a' := by
    have := (hq p).1.trans (hq p).2
    exact le_of_mul_le_mul_right this (by positivity)
  refine ⟨haa, ?_, (hq p).1⟩
  refine (hH.specNorm_le_iff_abs_re_quadForm_le (ha.trans haa)).2 fun x => ?_
  simp only [quadForm_def, star_trivial, RCLike.re_to_real]
  have h1 := (hq x).1
  have h2 := (hq x).2
  rw [abs_of_nonneg (le_trans (by positivity) h1)]
  exact h2

/-- **The computed curvature is positive** for a nonzero direction: if the spectrum of the
symmetric $\mathbf{A}$ lies in $[a, a']$, $a > 0$, $\mathbf{s} = \mathbf{A}\mathbf{p} +
\mathbf{e}$ with $\|\mathbf{e}\| \le \varepsilon\|\mathbf{A}\|_2\|\mathbf{p}\|$ and
$\lvert e'\rvert \le \varepsilon\|\mathbf{p}\|\|\mathbf{s}\|$, and $3\varepsilon a' \le a$, then
$\mathbf{p}^{\mathsf{T}}\mathbf{s} + e' > 0$. So the division by the computed
$\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$ succeeds. [StrakosTichy2002, (7.14)]. -/
theorem dotProduct_add_pos_of_spectrum_subset_Icc {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {a a' ε : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hε : 0 ≤ ε)
    (hsmall : 3 * ε * a' ≤ a) {p e : Fin n → ℝ} {e' : ℝ} (hp : p ≠ 0)
    (he : ‖WithLp.toLp 2 e‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 p‖)
    (he' : |e'| ≤ ε * ‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 (A *ᵥ p + e)‖) :
    0 < p ⬝ᵥ (A *ᵥ p + e) + e' := by
  obtain ⟨haa, hN, hq⟩ := specNorm_le_and_le_dotProduct hA ha.le hs hp
  have hp0 : 0 < ‖WithLp.toLp 2 p‖ := by
    rw [norm_pos_iff]
    exact fun h => hp (by simpa using congrArg WithLp.ofLp h)
  have hN0 := specNorm_nonneg A
  set P := ‖WithLp.toLp 2 p‖
  have hAp := norm_toLp_mulVec_le A p
  have hs' : ‖WithLp.toLp 2 (A *ᵥ p + e)‖ ≤ (1 + ε) * specNorm A * P := by
    have := EuclideanSpace.norm_toLp_add_le (A *ᵥ p) e
    nlinarith
  have hpe := EuclideanSpace.abs_dotProduct_le_norm p e
  have hε3 : 3 * ε ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith
  rw [dotProduct_add]
  have hE : ε * specNorm A ≤ a / 3 := by nlinarith
  have h1 : |p ⬝ᵥ e| ≤ ε * specNorm A * P ^ 2 := by nlinarith
  have h2 : |e'| ≤ ε * (1 + ε) * specNorm A * P ^ 2 := by
    have := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ ε * P)
    nlinarith
  have h3 : ε * (1 + ε) * specNorm A ≤ 4 / 9 * a := by nlinarith
  have hP2 : 0 < P ^ 2 := by positivity
  nlinarith [abs_le.mp h1, abs_le.mp h2, mul_le_mul_of_nonneg_right h3 hP2.le,
    mul_le_mul_of_nonneg_right hE hP2.le]

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- The norms of the computed residuals, $\rho_j = \|\mathbf{r}_j\|$. -/
noncomputable def ρ (j : ℕ) : ℝ :=
  ‖WithLp.toLp 2 (C.r j)‖

/-! ### Elementary consequences of the interface -/

/-- $j\varepsilon \le 1/100$ when $j \le k$ and $k\varepsilon \le 1/100$. -/
theorem mul_ε_le_of_le (hsmall : (k : ℝ) * C.ε ≤ 1 / 100) {j : ℕ} (hj : j ≤ k) :
    (j : ℝ) * C.ε ≤ 1 / 100 :=
  (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) C.ε_nonneg).trans hsmall

/-- The residual norms are nonnegative. -/
theorem ρ_nonneg (j : ℕ) : 0 ≤ C.ρ j := norm_nonneg _

private theorem toLp_eq_zero_iff {m : ℕ} (x : Fin m → ℝ) : WithLp.toLp 2 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    simpa using congrArg WithLp.ofLp h
  · rintro rfl
    rfl

/-- `NLAlib.CGRun.ν_eq` with the residual norm: $\nu_j = \rho_j^2(1 + \theta_j)$. -/
theorem ν_eq' {j : ℕ} (hj : j ≤ k) : C.ν j = C.ρ j ^ 2 * (1 + C.θ j) := C.ν_eq j hj

/-- The relative error of $\nu_j$ keeps it positive: $1 + \theta_j > 0$. -/
theorem one_add_θ_pos {j : ℕ} (hj : j ≤ k) : 0 < 1 + C.θ j := by
  have := (abs_le.mp (C.abs_θ_le j hj)).1
  linarith [C.ε_le]

/-- The residuals of the steps taken are nonzero: $\rho_j > 0$ for $j < k$. -/
theorem ρ_pos {j : ℕ} (hj : j < k) : 0 < C.ρ j := by
  have h := C.ν_pos j hj
  rw [C.ν_eq' hj.le] at h
  rcases (C.ρ_nonneg j).lt_or_eq with h' | h'
  · exact h'
  · rw [← h'] at h
    simp at h

/-- $\|\mathbf{s}_j\| \le (1 + \varepsilon)\|\mathbf{A}\|_2\|\mathbf{p}_j\|$. -/
theorem norm_s_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.s j)‖ ≤ (1 + C.ε) * specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖ := by
  rw [C.s_eq j hj]
  have h1 := EuclideanSpace.norm_toLp_add_le (C.A *ᵥ C.p j) (C.es j)
  have h2 := norm_toLp_mulVec_le C.A (C.p j)
  have h3 := C.norm_es_le j hj
  nlinarith

private theorem μ_le {j : ℕ} (hj : j < k) :
    C.μ j ≤ (1 + C.ε) ^ 2 * specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 := by
  rw [C.μ_eq j hj]
  have h1 := (abs_le.mp (EuclideanSpace.abs_dotProduct_le_norm (C.p j) (C.s j))).2
  have h2 := (abs_le.mp (C.abs_eμ_le j hj)).2
  have h3 := C.norm_s_le hj
  have hp := norm_nonneg (WithLp.toLp 2 (C.p j))
  have hε := C.ε_nonneg
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ (1 + C.ε) * ‖WithLp.toLp 2 (C.p j)‖)
  nlinarith

/-- $\gamma_j\mu_j = \nu_j(1 + \eta^\gamma_j)$. -/
theorem γ_mul_μ {j : ℕ} (hj : j < k) : C.γ j * C.μ j = C.ν j * (1 + C.eγ j) := by
  rw [C.γ_eq j hj]
  field_simp [(C.μ_pos j hj).ne']

/-- The **Lanczos vectors of the run**, 1-based as `NLAlib.LanczosData`:
$\bar{\mathbf{v}}_0 = \mathbf{0}$,
$\bar{\mathbf{v}}_{j+1} = (-1)^j\mathbf{r}_j/\|\mathbf{r}_j\|$, and
$\bar{\mathbf{v}}_{j+1} = \mathbf{b}/\|\mathbf{b}\|$ if $\mathbf{r}_j = \mathbf{0}$ (only at the
last index, where it is multiplied by $\beta_k = 0$). -/
noncomputable def lanczosV (j : ℕ) : Fin n → ℝ :=
  if j = 0 then 0
  else if C.r (j - 1) = 0 then (‖WithLp.toLp 2 C.b‖⁻¹ : ℝ) • C.b
  else ((-1 : ℝ) ^ (j - 1) * (C.ρ (j - 1))⁻¹) • C.r (j - 1)

/-- The diagonal coefficients of the run's Lanczos data, 1-based: $\alpha_{j+1}$ is the
$(j, j)$ entry of `NLAlib.cgTridiagonal C.γ C.ρ k`. -/
noncomputable def lanczosα (j : ℕ) : ℝ :=
  (C.γ (j - 1))⁻¹ + if j ≤ 1 then 0 else (C.ρ (j - 1) / C.ρ (j - 2)) ^ 2 / C.γ (j - 2)

/-- The off-diagonal coefficients of the run's Lanczos data, 1-based:
$\beta_0 = 0$, $\beta_{j+1} = \rho_{j+1}/(\gamma_j\rho_j)$. -/
noncomputable def lanczosβ (j : ℕ) : ℝ :=
  if j = 0 then 0 else C.ρ j / (C.γ (j - 1) * C.ρ (j - 1))

/-- **The Lanczos data of a conjugate gradient run**: the normalised residuals with the
coefficients of `NLAlib.cgTridiagonal`. -/
noncomputable def toLanczosData : LanczosData n k where
  H := C.A
  v := C.lanczosV
  α := C.lanczosα
  β := C.lanczosβ
  transpose_H := C.transpose_A
  k_pos := C.k_pos
  v_zero := by simp [lanczosV]
  β_zero := by simp [lanczosβ]

/-- **The computed squared residual norm vanishes exactly with the residual**:
$\nu_j = 0 \iff \mathbf{r}_j = \mathbf{0}$, $j \le k$. This is a statement about the model
of computation without underflow (`NLAlib.CGRun.ν_eq`); in IEEE arithmetic
$\mathrm{fl}(\|\mathbf{r}\|^2)$ can underflow to $0$ with $\mathbf{r} \ne \mathbf{0}$. -/
theorem ν_eq_zero_iff {j : ℕ} (hj : j ≤ k) : C.ν j = 0 ↔ C.r j = 0 := by
  rw [C.ν_eq' hj, mul_eq_zero, or_iff_left (C.one_add_θ_pos hj).ne', ρ, sq_eq_zero_iff,
    norm_eq_zero, toLp_eq_zero_iff]

/-- The step lengths are positive. -/
theorem γ_pos {j : ℕ} (hj : j < k) : 0 < C.γ j := by
  rw [C.γ_eq j hj]
  have := (abs_le.mp (C.abs_eγ_le j hj)).1
  have := C.ε_le
  exact mul_pos (div_pos (C.ν_pos j hj) (C.μ_pos j hj)) (by linarith)

/-- The Lanczos vectors of the run are unit vectors. -/
theorem norm_lanczosV {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k + 1) :
    ‖WithLp.toLp 2 (C.lanczosV j)‖ = 1 := by
  have _ : j ≤ k + 1 := h2
  have hb : C.b ≠ 0 := by
    rw [← C.r_zero, Ne, ← C.ν_eq_zero_iff (Nat.zero_le k)]
    exact (C.ν_pos 0 C.k_pos).ne'
  have hb' : ‖WithLp.toLp 2 C.b‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact fun h => hb ((toLp_eq_zero_iff _).1 h)
  unfold lanczosV
  rw [if_neg (by omega)]
  split_ifs with h
  · rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hb']
  · have hρ : C.ρ (j - 1) ≠ 0 := by
      rw [ρ, norm_ne_zero_iff]
      exact fun h' => h ((toLp_eq_zero_iff _).1 h')
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_inv,
      abs_of_nonneg (C.ρ_nonneg _), ← ρ, inv_mul_cancel₀ hρ]

/-- The coefficients $\beta_j$ of the run are nonnegative. -/
theorem lanczosβ_nonneg {j : ℕ} (hj : j ≤ k) : 0 ≤ C.lanczosβ j := by
  unfold lanczosβ
  split_ifs with h
  · exact le_rfl
  · have := C.γ_pos (j := j - 1) (by omega)
    exact div_nonneg (C.ρ_nonneg j) (mul_nonneg this.le (C.ρ_nonneg _))

/-- The coefficients $\beta_j$, $1 \le j < k$, are positive. -/
theorem lanczosβ_pos {j : ℕ} (h1 : 1 ≤ j) (h2 : j < k) : 0 < C.lanczosβ j := by
  unfold lanczosβ
  rw [if_neg (by omega)]
  exact div_pos (C.ρ_pos h2) (mul_pos (C.γ_pos (by omega)) (C.ρ_pos (by omega)))

/-- **The run as normalised Lanczos data** (`NLAlib.NormalizedLanczosData`). -/
noncomputable def toNormalizedLanczosData : NormalizedLanczosData n k :=
  { C.toLanczosData with
    norm_v := fun _ h1 h2 => C.norm_lanczosV h1 h2
    β_nonneg := fun _ hj => C.lanczosβ_nonneg hj
    β_pos := fun _ h1 h2 => C.lanczosβ_pos h1 h2 }

/-- The **backward model of the run**: `NLAlib.NormalizedLanczosData.backwardH` of its Lanczos
data. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  C.toNormalizedLanczosData.backwardH

/-- The dilated matrix $\mathbf{I}_{k+1} \otimes \mathbf{A}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => C.A

/-- The **dilated right-hand side** $(\mathbf{b}, \mathbf{0}, \dots, \mathbf{0})$: the start of
exact CG on the model, $\|\mathbf{b}\|$ times the dilated Lanczos start. -/
def dilatedRhs : Fin n × Fin (k + 1) → ℝ :=
  fun x => if (x.2 : ℕ) = 0 then C.b x.1 else 0

/-- **The tridiagonal matrix of the run is the CG tridiagonal matrix** of the computed step
lengths and residual norms. -/
theorem tridiagonal_toLanczosData : C.toLanczosData.tridiagonal = cgTridiagonal C.γ C.ρ k := by
  ext i j
  simp only [LanczosData.tridiagonal, cgTridiagonal, toLanczosData, Matrix.of_apply, lanczosα,
    lanczosβ]
  split_ifs <;> first
    | rfl
    | (exfalso; omega)
    | (rw [show (i : ℕ) - 1 = j by omega])
    | (rw [show (j : ℕ) - 1 = i by omega])

/-- The direction coefficient against the exact residual ratio:
$\lvert\delta_j - \rho_{j+1}^2/\rho_j^2\rvert \le 4\varepsilon\rho_{j+1}^2/\rho_j^2$, $j < k$. -/
theorem abs_δ_sub_le {j : ℕ} (hj : j < k) :
    |C.δ j - C.ρ (j + 1) ^ 2 / C.ρ j ^ 2| ≤ 4 * C.ε * (C.ρ (j + 1) ^ 2 / C.ρ j ^ 2) := by
  have hρ := C.ρ_pos hj
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have hθ' := abs_le.mp (C.abs_θ_le (j + 1) hj)
  have he := abs_le.mp (C.abs_eδ_le j hj)
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  set R := C.ρ (j + 1) ^ 2 / C.ρ j ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have h1 := C.one_add_θ_pos hj.le
  have hδ : C.δ j = R * ((1 + C.θ (j + 1)) * (1 + C.eδ j) / (1 + C.θ j)) := by
    rw [C.δ_eq j hj, C.ν_eq' hj, C.ν_eq' hj.le, hR]
    field_simp
  have hu : |(1 + C.θ (j + 1)) * (1 + C.eδ j) / (1 + C.θ j) - 1| ≤ 4 * C.ε := by
    rw [div_sub_one h1.ne', abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_le]
    constructor <;> nlinarith
  rw [hδ, ← mul_sub_one, abs_mul, abs_of_nonneg hR0, mul_comm]
  exact mul_le_mul_of_nonneg_right hu hR0

/-- **The step length against the direction** (the computed Rayleigh quotient):
$\rho_j^2 \le \tfrac{21}{20}\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2$, $j < k$, i.e.
$\gamma_j^{-1} \le 1.05\|\mathbf{A}\|_2\pi_j^2$. -/
theorem ρ_sq_le {j : ℕ} (hj : j < k) :
    C.ρ j ^ 2 ≤ 21 / 20 * specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 := by
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have he := abs_le.mp (C.abs_eγ_le j hj)
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hμ := C.μ_le hj
  have hgm := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le] at hgm
  have hX : 0 ≤ specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 := by
    have := specNorm_nonneg C.A
    positivity
  have hρ2 : 0 ≤ C.ρ j ^ 2 := by positivity
  have h1 : C.ρ j ^ 2 * (1 - C.ε) ^ 2 ≤ C.γ j * C.μ j := by
    rw [hgm]
    have : (1 - C.ε) ^ 2 ≤ (1 + C.θ j) * (1 + C.eγ j) := by nlinarith
    exact mul_le_mul_of_nonneg_left this hρ2 |>.trans (le_of_eq (by ring))
  have h2 := mul_le_mul_of_nonneg_left hμ hγ.le
  have h3 : (1 + C.ε) ^ 2 ≤ 21 / 20 * (1 - C.ε) ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hγ.le hX)
  have h5 : C.ρ j ^ 2 * (1 - C.ε) ^ 2 ≤
      21 / 20 * specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 * (1 - C.ε) ^ 2 := by
    nlinarith
  exact le_of_mul_le_mul_right h5 (by nlinarith)

/-! ### Step relations used by Lemmas A and B -/

/-- The sharper form of `NLAlib.CGRun.abs_δ_sub_le`:
$\lvert\delta_j - \rho_{j+1}^2/\rho_j^2\rvert \le 3.1\varepsilon\rho_{j+1}^2/\rho_j^2$. -/
private theorem abs_δ_sub_le' {j : ℕ} (hj : j < k) :
    |C.δ j - C.ρ (j + 1) ^ 2 / C.ρ j ^ 2| ≤ 31 / 10 * C.ε * (C.ρ (j + 1) ^ 2 / C.ρ j ^ 2) := by
  have hρ := C.ρ_pos hj
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have hθ' := abs_le.mp (C.abs_θ_le (j + 1) hj)
  have he := abs_le.mp (C.abs_eδ_le j hj)
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  set R := C.ρ (j + 1) ^ 2 / C.ρ j ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have h1 := C.one_add_θ_pos hj.le
  have hδ : C.δ j = R * ((1 + C.θ (j + 1)) * (1 + C.eδ j) / (1 + C.θ j)) := by
    rw [C.δ_eq j hj, C.ν_eq' hj, C.ν_eq' hj.le, hR]
    field_simp
  have hu : |(1 + C.θ (j + 1)) * (1 + C.eδ j) / (1 + C.θ j) - 1| ≤ 31 / 10 * C.ε := by
    rw [div_sub_one h1.ne', abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_le]
    constructor <;> nlinarith
  rw [hδ, ← mul_sub_one, abs_mul, abs_of_nonneg hR0, mul_comm]
  exact mul_le_mul_of_nonneg_right hu hR0

/-- The bounds on $\delta_j$ that follow: $\delta_j \ge 0$,
$\delta_j\rho_j^2 \le (1 + 3.1\varepsilon)\rho_{j+1}^2$ and
$\rho_{j+1}^2 \le (1 + 3.2\varepsilon)\delta_j\rho_j^2$. -/
theorem δ_bounds {j : ℕ} (hj : j < k) :
    0 ≤ C.δ j ∧ C.δ j * C.ρ j ^ 2 ≤ (1 + 31 / 10 * C.ε) * C.ρ (j + 1) ^ 2 ∧
      C.ρ (j + 1) ^ 2 ≤ (1 + 16 / 5 * C.ε) * (C.δ j * C.ρ j ^ 2) := by
  have h := abs_le.mp (C.abs_δ_sub_le' hj)
  have hρ := C.ρ_pos hj
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hρ2 : 0 < C.ρ j ^ 2 := by positivity
  set R := C.ρ (j + 1) ^ 2 / C.ρ j ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have hRe : R * C.ρ j ^ 2 = C.ρ (j + 1) ^ 2 := by
    rw [hR]
    field_simp
  refine ⟨by nlinarith, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right (by linarith : C.δ j ≤ (1 + 31 / 10 * C.ε) * R) hρ2.le
    nlinarith
  · have h2 : R ≤ (1 + 16 / 5 * C.ε) * C.δ j := by nlinarith
    have := mul_le_mul_of_nonneg_right h2 hρ2.le
    nlinarith

/-- The residual update error with $\gamma_j > 0$: $\|\mathbf{e}^r_j\| \le \varepsilon(\rho_j +
\gamma_j\|\mathbf{s}_j\|)$. -/
theorem norm_er_le_of_lt {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.er j)‖ ≤ C.ε * (C.ρ j + C.γ j * ‖WithLp.toLp 2 (C.s j)‖) := by
  have := C.norm_er_le j hj
  rwa [abs_of_pos (C.γ_pos hj)] at this

/-- The direction update error with $\delta_j \ge 0$: $\|\mathbf{e}^p_j\| \le
\varepsilon(\rho_{j+1} + \delta_j\|\mathbf{p}_j\|)$. -/
theorem norm_ep_le_of_lt {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.ep j)‖ ≤ C.ε * (C.ρ (j + 1) + C.δ j * ‖WithLp.toLp 2 (C.p j)‖) := by
  have := C.norm_ep_le j hj
  rwa [abs_of_nonneg (C.δ_bounds hj).1] at this

/-- The previous direction, scaled, is controlled by the current one:
$\delta_j\|\mathbf{p}_j\| \le 1.05(\|\mathbf{p}_{j+1}\| + \rho_{j+1})$ (from the direction update),
so no residual ratio is needed. -/
theorem δ_mul_norm_p_le {j : ℕ} (hj : j < k) :
    C.δ j * ‖WithLp.toLp 2 (C.p j)‖ ≤
      21 / 20 * (‖WithLp.toLp 2 (C.p (j + 1))‖ + C.ρ (j + 1)) := by
  have hid : C.δ j • C.p j = C.p (j + 1) - C.r (j + 1) - C.ep j := by
    rw [C.p_succ j hj]
    abel
  have h1 : C.δ j * ‖WithLp.toLp 2 (C.p j)‖ ≤
      ‖WithLp.toLp 2 (C.p (j + 1))‖ + C.ρ (j + 1) + ‖WithLp.toLp 2 (C.ep j)‖ := by
    have := EuclideanSpace.norm_toLp_sub_le (C.p (j + 1) - C.r (j + 1)) (C.ep j)
    have h2 := EuclideanSpace.norm_toLp_sub_le (C.p (j + 1)) (C.r (j + 1))
    rw [← hid, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (C.δ_bounds hj).1] at this
    simp only [ρ]
    linarith
  have h3 := C.norm_ep_le_of_lt hj
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hp := norm_nonneg (WithLp.toLp 2 (C.p (j + 1)))
  have hρ := C.ρ_nonneg (j + 1)
  have hD : 0 ≤ C.δ j * ‖WithLp.toLp 2 (C.p j)‖ :=
    mul_nonneg (C.δ_bounds hj).1 (norm_nonneg _)
  nlinarith

/-- The Lanczos vector of the run at a step taken. -/
theorem lanczosV_succ {j : ℕ} (hj : j < k) :
    C.lanczosV (j + 1) = ((-1 : ℝ) ^ j * (C.ρ j)⁻¹) • C.r j := by
  have hr : C.r j ≠ 0 := by
    rw [Ne, ← C.ν_eq_zero_iff hj.le]
    exact (C.ν_pos j hj).ne'
  simp only [lanczosV, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero j), if_neg hr]

/-- The normalisation step is exact:
$\beta_{j+1}\bar{\mathbf{v}}_{j+2} = (-1)^{j+1}\mathbf{r}_{j+1}/(\gamma_j\rho_j)$, also when
$\mathbf{r}_{j+1} = \mathbf{0}$. -/
theorem lanczosβ_smul_lanczosV {j : ℕ} (hj : j < k) :
    C.lanczosβ (j + 1) • C.lanczosV (j + 2) =
      (-((-1 : ℝ) ^ j * (C.γ j * C.ρ j)⁻¹)) • C.r (j + 1) := by
  have hγ := C.γ_pos hj
  have hρ := C.ρ_pos hj
  by_cases hr : C.r (j + 1) = 0
  · have h0 : C.ρ (j + 1) = 0 := by rw [ρ, hr, WithLp.toLp_zero, norm_zero]
    rw [hr, smul_zero, lanczosβ, if_neg (Nat.succ_ne_zero j), h0, zero_div, zero_smul]
  · have hρ' : C.ρ (j + 1) ≠ 0 := by
      rw [ρ, norm_ne_zero_iff]
      exact fun h => hr ((toLp_eq_zero_iff _).1 h)
    simp only [lanczosV, lanczosβ, show j + 2 - 1 = j + 1 by omega, Nat.add_sub_cancel,
      if_neg (show j + 2 ≠ 0 by omega), if_neg (Nat.succ_ne_zero j), if_neg hr, smul_smul]
    congr 1
    field_simp
    ring

/-- The backward term $\beta_j\bar{\mathbf{v}}_j$, $1 \le j < k$. -/
private theorem lanczosβ_smul_lanczosV_self {i : ℕ} (hi : i + 1 < k) :
    C.lanczosβ (i + 1) • C.lanczosV (i + 1) =
      ((-1 : ℝ) ^ i * (C.ρ (i + 1) / (C.γ i * C.ρ i ^ 2))) • C.r i := by
  have hγ := C.γ_pos (by omega : i < k)
  have hρ := C.ρ_pos (by omega : i < k)
  rw [C.lanczosV_succ (by omega), smul_smul, lanczosβ, if_neg (Nat.succ_ne_zero i),
    Nat.add_sub_cancel]
  congr 1
  field_simp

/-- The matrix–direction product of a step taken, solved from the residual update:
$\mathbf{A}\mathbf{p}_j = \gamma_j^{-1}(\mathbf{r}_j - \mathbf{r}_{j+1} + \mathbf{e}^r_j) -
\mathbf{e}^s_j$. -/
theorem mulVec_p_eq {j : ℕ} (hj : j < k) :
    C.A *ᵥ C.p j = (C.γ j)⁻¹ • (C.r j - C.r (j + 1) + C.er j) - C.es j := by
  have hγ := (C.γ_pos hj).ne'
  rw [C.r_succ j hj, C.s_eq j hj]
  match_scalars <;> field_simp <;> ring

/-- **The recurrence error at the first step**:
$\rho_0\bar{\mathbf{f}}_0 = -\mathbf{e}^s_0 + \gamma_0^{-1}\mathbf{e}^r_0$. -/
private theorem recurrenceError_zero :
    C.toLanczosData.recurrenceError 0 =
      (C.ρ 0)⁻¹ • (-C.es 0 + (C.γ 0)⁻¹ • C.er 0) := by
  have hk := C.k_pos
  have hγ := (C.γ_pos hk).ne'
  have hρ := (C.ρ_pos hk).ne'
  have h1 := C.lanczosV_succ hk
  have h2 := C.lanczosβ_smul_lanczosV hk
  simp only [pow_zero, one_mul] at h1 h2
  simp only [LanczosData.recurrenceError, toLanczosData, zero_add]
  rw [show (2 : ℕ) = 0 + 2 from rfl, h2, h1, show C.lanczosβ 0 = 0 by simp [lanczosβ], zero_smul,
    sub_zero, show C.lanczosα 1 = (C.γ 0)⁻¹ by simp [lanczosα]]
  rw [C.r_succ 0 hk, C.s_eq 0 hk, C.p_zero, ← C.r_zero]
  simp only [Matrix.mulVec_smul]
  match_scalars <;> field_simp <;> ring

/-- **The recurrence error at a later step** $j = i + 1 < k$, with
$c = \rho_j^2/(\rho_i^2\gamma_i)$ the diagonal convention of `NLAlib.cgTridiagonal`:
$(-1)^j\rho_j\bar{\mathbf{f}}_j = -\mathbf{e}^s_j + \gamma_j^{-1}\mathbf{e}^r_j -
\mathbf{A}\mathbf{e}^p_i + \delta_i\mathbf{e}^s_i - (\delta_i/\gamma_i)\mathbf{e}^r_i +
(c - \delta_i/\gamma_i)(\mathbf{r}_i - \mathbf{r}_j)$. -/
private theorem recurrenceError_succ {i : ℕ} (hi : i + 1 < k) :
    C.toLanczosData.recurrenceError (i + 1) =
      ((-1 : ℝ) ^ (i + 1) * (C.ρ (i + 1))⁻¹) • (-C.es (i + 1) + (C.γ (i + 1))⁻¹ • C.er (i + 1) -
        C.A *ᵥ C.ep i + C.δ i • C.es i - (C.δ i / C.γ i) • C.er i +
        (C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i - C.δ i / C.γ i) • (C.r i - C.r (i + 1))) := by
  have hi' : i < k := by omega
  have hγ := (C.γ_pos hi).ne'
  have hγ' := (C.γ_pos hi').ne'
  have hρ := (C.ρ_pos hi).ne'
  have hρ' := (C.ρ_pos hi').ne'
  simp only [LanczosData.recurrenceError, toLanczosData]
  rw [C.lanczosβ_smul_lanczosV hi, C.lanczosβ_smul_lanczosV_self hi, C.lanczosV_succ hi]
  rw [show C.lanczosα (i + 1 + 1) = (C.γ (i + 1))⁻¹ + (C.ρ (i + 1) / C.ρ i) ^ 2 / C.γ i by
    simp [lanczosα]]
  rw [C.r_succ (i + 1) hi, C.s_eq (i + 1) hi, C.p_succ i hi']
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [C.mulVec_p_eq hi']
  match_scalars <;> field_simp <;> ring

/-- The inverse step length against a direction certificate: $\gamma_j^{-1} \le
1.05\|\mathbf{A}\|_2\Pi^2$ when $\|\mathbf{p}_j\| \le \Pi\rho_j$ (from `NLAlib.CGRun.ρ_sq_le`). -/
private theorem inv_γ_le {P : ℝ} {j : ℕ} (hj : j < k)
    (hP : ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j) :
    (C.γ j)⁻¹ ≤ 21 / 20 * specNorm C.A * P ^ 2 := by
  have hγ := C.γ_pos hj
  have hρ := C.ρ_pos hj
  have h1 := C.ρ_sq_le hj
  have hN := specNorm_nonneg C.A
  have hp2 : ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ P ^ 2 * C.ρ j ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hP 2
  have h2 : C.ρ j ^ 2 * 1 ≤ C.ρ j ^ 2 * (21 / 20 * specNorm C.A * P ^ 2 * C.γ j) := by
    have := mul_le_mul_of_nonneg_left hp2 (by positivity : 0 ≤ 21 / 20 * specNorm C.A * C.γ j)
    nlinarith
  have h3 := le_of_mul_le_mul_left h2 (by positivity)
  rw [inv_le_iff_one_le_mul₀ hγ]
  linarith

/-- A direction certificate is nonnegative: $\Pi \ge \|\mathbf{p}_j\|/\rho_j \ge 0$. -/
theorem P_nonneg {P : ℝ} {j : ℕ} (hj : j < k)
    (hP : ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j) : 0 ≤ P := by
  by_contra h
  push Not at h
  have := mul_neg_of_neg_of_pos h (C.ρ_pos hj)
  linarith [norm_nonneg (WithLp.toLp 2 (C.p j))]

/-- A curvature certificate is nonnegative. -/
theorem nonneg_of_specNorm_mul_γ_mul_norm_p_sq_le {K : ℝ} {j : ℕ} (hj : j < k)
    (hK : specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2) : 0 ≤ K := by
  by_contra h
  push Not at h
  have := mul_neg_of_neg_of_pos h (pow_pos (C.ρ_pos hj) 2)
  have : 0 ≤ specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 :=
    mul_nonneg (mul_nonneg (specNorm_nonneg _) (C.γ_pos hj).le) (sq_nonneg _)
  linarith

/-- The coefficient ratio against $\beta_j$: $\delta_i\rho_i/\gamma_i \le (1 + 3.1\varepsilon)
\beta_{i+1}\rho_{i+1}$, so at most $(1 + 3.1\varepsilon)B\rho_{i+1}$. -/
theorem δ_mul_ρ_div_γ_le {B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hβ : C.lanczosβ (i + 1) ≤ B) :
    C.δ i * C.ρ i / C.γ i ≤ (1 + 31 / 10 * C.ε) * B * C.ρ (i + 1) := by
  have hi' : i < k := by omega
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hρ' := C.ρ_pos hi'
  have hε0 := C.ε_nonneg
  obtain ⟨-, hδ1, -⟩ := C.δ_bounds hi'
  have hβ' : C.ρ (i + 1) / (C.γ i * C.ρ i) ≤ B := by simpa [lanczosβ] using hβ
  have e1 : C.δ i * C.ρ i / C.γ i = C.δ i * C.ρ i ^ 2 / (C.γ i * C.ρ i) := by field_simp
  have e2 : (1 + 31 / 10 * C.ε) * C.ρ (i + 1) ^ 2 / (C.γ i * C.ρ i) =
      (1 + 31 / 10 * C.ε) * C.ρ (i + 1) * (C.ρ (i + 1) / (C.γ i * C.ρ i)) := by
    field_simp
  have hpos : 0 < C.γ i * C.ρ i := mul_pos hγ' hρ'
  have hc : 0 ≤ (1 + 31 / 10 * C.ε) * C.ρ (i + 1) :=
    mul_nonneg (by linarith) hρ.le
  rw [e1]
  calc C.δ i * C.ρ i ^ 2 / (C.γ i * C.ρ i)
      ≤ (1 + 31 / 10 * C.ε) * C.ρ (i + 1) ^ 2 / (C.γ i * C.ρ i) :=
        div_le_div_of_nonneg_right hδ1 hpos.le
    _ = (1 + 31 / 10 * C.ε) * C.ρ (i + 1) * (C.ρ (i + 1) / (C.γ i * C.ρ i)) := e2
    _ ≤ (1 + 31 / 10 * C.ε) * C.ρ (i + 1) * B := mul_le_mul_of_nonneg_left hβ' hc
    _ = _ := by ring

/-- The diagonal-convention term of Lemma A: with $c = \rho_j^2/(\rho_i^2\gamma_i)$,
$\lvert c - \delta_i/\gamma_i\rvert\|\mathbf{r}_i - \mathbf{r}_j\| \le
3.1\varepsilon(1 + 1.032)B\rho_j$, $j = i + 1$. -/
private theorem norm_convention_le {B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hβ : C.lanczosβ (i + 1) ≤ B) (hδB : C.δ i ≤ B * C.γ i) :
    ‖WithLp.toLp 2 ((C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i - C.δ i / C.γ i) •
        (C.r i - C.r (i + 1)))‖ ≤
      31 / 10 * C.ε * (C.ρ (i + 1) * B + (1 + 16 / 5 * C.ε) * B * C.ρ (i + 1)) := by
  have hi' : i < k := by omega
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hρ' := C.ρ_pos hi'
  have hε0 := C.ε_nonneg
  obtain ⟨hδ0, -, hδ2⟩ := C.δ_bounds hi'
  have hβ' : C.ρ (i + 1) / (C.γ i * C.ρ i) ≤ B := by simpa [lanczosβ] using hβ
  have hB0 : 0 ≤ B := le_trans (by positivity) hβ'
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
  have hr := EuclideanSpace.norm_toLp_sub_le (C.r i) (C.r (i + 1))
  have hd := C.abs_δ_sub_le' hi'
  have hR0 : 0 ≤ C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 := by positivity
  have e1 : C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i - C.δ i / C.γ i =
      -(C.δ i - C.ρ (i + 1) ^ 2 / C.ρ i ^ 2) / C.γ i := by ring
  rw [e1, abs_div, abs_neg, abs_of_pos hγ']
  have hRρ' : C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 * C.ρ i / C.γ i =
      C.ρ (i + 1) * (C.ρ (i + 1) / (C.γ i * C.ρ i)) := by
    field_simp
  have hRρ : C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i ≤ (1 + 16 / 5 * C.ε) * B := by
    have h1 : C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 ≤ (1 + 16 / 5 * C.ε) * C.δ i := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i ≤ (1 + 16 / 5 * C.ε) * C.δ i / C.γ i :=
          div_le_div_of_nonneg_right h1 hγ'.le
      _ ≤ (1 + 16 / 5 * C.ε) * (B * C.γ i) / C.γ i :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hδB (by linarith)) hγ'.le
      _ = _ := by field_simp
  calc |C.δ i - C.ρ (i + 1) ^ 2 / C.ρ i ^ 2| / C.γ i * ‖WithLp.toLp 2 (C.r i - C.r (i + 1))‖
      ≤ 31 / 10 * C.ε * (C.ρ (i + 1) ^ 2 / C.ρ i ^ 2) / C.γ i * (C.ρ i + C.ρ (i + 1)) :=
        mul_le_mul (div_le_div_of_nonneg_right hd hγ'.le) hr (norm_nonneg _) (by positivity)
    _ = 31 / 10 * C.ε * (C.ρ (i + 1) * (C.ρ (i + 1) / (C.γ i * C.ρ i)) +
          C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i * C.ρ (i + 1)) := by
        rw [← hRρ']
        ring
    _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left hβ' hρ.le
        have h2 := mul_le_mul_of_nonneg_right hRρ hρ.le
        have := add_le_add h1 h2
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 31 / 10 * C.ε)
        linarith only [this]

/-- The scalar inequality behind Lemma A at a later step. -/
private theorem recurrenceError_scalar_le {ε N B P ρ g p D e₁ e₂ e₃ e₄ e₅ e₆ : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) (hN : 0 ≤ N) (hB : 0 ≤ B) (hP : 0 ≤ P) (hρ : 0 ≤ ρ)
    (hp0 : 0 ≤ p) (hD0 : 0 ≤ D) (hp : p ≤ P * ρ) (hD : D ≤ 21 / 20 * (p + ρ))
    (hg : g ≤ 21 / 20 * N * P ^ 2)
    (h₁ : e₁ ≤ ε * N * p) (h₂ : e₂ ≤ ε * (g * ρ) + ε * ((1 + ε) * N * p))
    (h₃ : e₃ ≤ N * (ε * (ρ + D))) (h₄ : e₄ ≤ ε * N * D)
    (h₅ : e₅ ≤ ε * ((1 + 31 / 10 * ε) * B * ρ) + ε * ((1 + ε) * N * D))
    (h₆ : e₆ ≤ 31 / 10 * ε * (ρ * B + (1 + 16 / 5 * ε) * B * ρ)) :
    e₁ + e₂ + e₃ + e₄ + e₅ + e₆ ≤ 8 * ε * (N * (1 + P) ^ 2 + B) * ρ := by
  have hNp : N * p ≤ N * (P * ρ) := mul_le_mul_of_nonneg_left hp hN
  have hND : N * D ≤ N * (21 / 20 * (P * ρ + ρ)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hD, hp]) hN
  have hgρ : ε * (g * ρ) ≤ ε * (21 / 20 * N * P ^ 2 * ρ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg hρ) hε0
  have hNp0 : 0 ≤ N * p := mul_nonneg hN hp0
  have hND0 : 0 ≤ N * D := mul_nonneg hN hD0
  have hBρ0 : 0 ≤ B * ρ := mul_nonneg hB hρ
  have a1 : ε * ((1 + ε) * N * p) ≤ ε * (2 * (N * (P * ρ))) := by
    have : (1 + ε) * (N * p) ≤ 2 * (N * (P * ρ)) :=
      (mul_le_mul_of_nonneg_right (show 1 + ε ≤ 2 by linarith) hNp0).trans (by linarith)
    have := mul_le_mul_of_nonneg_left this hε0
    linarith only [this]
  have a2 : ε * ((1 + ε) * N * D) ≤ ε * (2 * (N * (21 / 20 * (P * ρ + ρ)))) := by
    have : (1 + ε) * (N * D) ≤ 2 * (N * (21 / 20 * (P * ρ + ρ))) :=
      (mul_le_mul_of_nonneg_right (show 1 + ε ≤ 2 by linarith) hND0).trans (by linarith)
    have := mul_le_mul_of_nonneg_left this hε0
    linarith only [this]
  have a3 := mul_le_mul_of_nonneg_left hNp hε0
  have a4 := mul_le_mul_of_nonneg_left hND hε0
  have a5 : ε * ((1 + 31 / 10 * ε) * B * ρ) ≤ ε * (1031 / 1000 * (B * ρ)) := by
    have : (1 + 31 / 10 * ε) * (B * ρ) ≤ 1031 / 1000 * (B * ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) hBρ0
    have := mul_le_mul_of_nonneg_left this hε0
    linarith only [this]
  have a6 : 31 / 10 * ε * (ρ * B + (1 + 16 / 5 * ε) * B * ρ) ≤ ε * (63 / 10 * (B * ρ)) := by
    have h1 : (1 + 16 / 5 * ε) * (B * ρ) ≤ (1 + 32 / 1000) * (B * ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) hBρ0
    have h2 : 31 / 10 * (ρ * B + (1 + 16 / 5 * ε) * B * ρ) ≤ 63 / 10 * (B * ρ) := by linarith
    have := mul_le_mul_of_nonneg_left h2 hε0
    linarith only [this]
  have hpoly : N * (P * ρ) + 21 / 20 * N * P ^ 2 * ρ + 2 * (N * (P * ρ)) + (N * ρ +
      N * (21 / 20 * (P * ρ + ρ))) + N * (21 / 20 * (P * ρ + ρ)) +
      2 * (N * (21 / 20 * (P * ρ + ρ))) ≤ 8 * (N * (1 + P) ^ 2) * ρ := by
    have h1 : 0 ≤ N * ρ := mul_nonneg hN hρ
    have h2 : 0 ≤ N * ρ * P := mul_nonneg h1 hP
    have h3 : 0 ≤ N * ρ * P ^ 2 := mul_nonneg h1 (sq_nonneg P)
    linarith only [h1, h2, h3]
  have a7 := mul_le_mul_of_nonneg_left hpoly hε0
  have a8 := mul_nonneg hε0 hBρ0
  have e : 8 * ε * (N * (1 + P) ^ 2 + B) * ρ =
      ε * (8 * (N * (1 + P) ^ 2) * ρ) + ε * (8 * B * ρ) := by ring
  rw [e]
  linarith only [h₁, h₂, h₃, h₄, h₅, h₆, hgρ, a1, a2, a3, a4, a5, a6, a7, a8]

/-- The norm of the vector of `NLAlib.CGRun.recurrenceError_succ`, relative to $\rho_j$. -/
private theorem norm_recurrenceError_succ_mul_le {P B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1))
    (hβ : C.lanczosβ (i + 1) ≤ B) (hδB : C.δ i ≤ B * C.γ i) :
    ‖WithLp.toLp 2 (-C.es (i + 1) + (C.γ (i + 1))⁻¹ • C.er (i + 1) -
        C.A *ᵥ C.ep i + C.δ i • C.es i - (C.δ i / C.γ i) • C.er i +
        (C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i - C.δ i / C.γ i) • (C.r i - C.r (i + 1)))‖ ≤
      8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B) * C.ρ (i + 1) := by
  have hi' : i < k := by omega
  have hγ := C.γ_pos hi
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hN := specNorm_nonneg C.A
  have hε0 := C.ε_nonneg
  obtain ⟨hδ0, -, -⟩ := C.δ_bounds hi'
  have hb0 := div_nonneg hδ0 hγ'.le
  have hβ' : C.ρ (i + 1) / (C.γ i * C.ρ i) ≤ B := by simpa [lanczosβ] using hβ
  have hB0 : 0 ≤ B := le_trans (div_nonneg hρ.le (mul_pos hγ' (C.ρ_pos hi')).le) hβ'
  have hs := C.norm_s_le hi
  have hs' := C.norm_s_le hi'
  -- the six terms
  have t2 : ‖WithLp.toLp 2 ((C.γ (i + 1))⁻¹ • C.er (i + 1))‖ ≤ C.ε * ((C.γ (i + 1))⁻¹ *
      C.ρ (i + 1)) + C.ε * ((1 + C.ε) * specNorm C.A * ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hγ]
    have := mul_le_mul_of_nonneg_left (C.norm_er_le_of_lt hi) (inv_nonneg.2 hγ.le)
    have e : (C.γ (i + 1))⁻¹ * (C.ε * (C.ρ (i + 1) + C.γ (i + 1) *
        ‖WithLp.toLp 2 (C.s (i + 1))‖)) = C.ε * ((C.γ (i + 1))⁻¹ * C.ρ (i + 1)) +
          C.ε * ‖WithLp.toLp 2 (C.s (i + 1))‖ := by
      field_simp
    have := mul_le_mul_of_nonneg_left hs hε0
    linarith
  have t3 : ‖WithLp.toLp 2 (C.A *ᵥ C.ep i)‖ ≤
      specNorm C.A * (C.ε * (C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖)) :=
    (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (C.norm_ep_le_of_lt hi') hN)
  have t4 : ‖WithLp.toLp 2 (C.δ i • C.es i)‖ ≤
      C.ε * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ0]
    have := mul_le_mul_of_nonneg_left (C.norm_es_le i hi') hδ0
    linarith only [this]
  have t5 : ‖WithLp.toLp 2 ((C.δ i / C.γ i) • C.er i)‖ ≤
      C.ε * ((1 + 31 / 10 * C.ε) * B * C.ρ (i + 1)) +
        C.ε * ((1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖)) := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0]
    have := mul_le_mul_of_nonneg_left (C.norm_er_le_of_lt hi') hb0
    have e : C.δ i / C.γ i * (C.ε * (C.ρ i + C.γ i * ‖WithLp.toLp 2 (C.s i)‖)) =
        C.ε * (C.δ i * C.ρ i / C.γ i) + C.ε * (C.δ i * ‖WithLp.toLp 2 (C.s i)‖) := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hs' hδ0
    have h3 := mul_le_mul_of_nonneg_left (C.δ_mul_ρ_div_γ_le hi hβ) hε0
    have h4 := mul_le_mul_of_nonneg_left h2 hε0
    linarith
  have hsum : ‖WithLp.toLp 2 (-C.es (i + 1) + (C.γ (i + 1))⁻¹ • C.er (i + 1) -
        C.A *ᵥ C.ep i + C.δ i • C.es i - (C.δ i / C.γ i) • C.er i +
        (C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i - C.δ i / C.γ i) • (C.r i - C.r (i + 1)))‖
      ≤ ‖WithLp.toLp 2 (C.es (i + 1))‖ + ‖WithLp.toLp 2 ((C.γ (i + 1))⁻¹ • C.er (i + 1))‖ +
        ‖WithLp.toLp 2 (C.A *ᵥ C.ep i)‖ + ‖WithLp.toLp 2 (C.δ i • C.es i)‖ +
        ‖WithLp.toLp 2 ((C.δ i / C.γ i) • C.er i)‖ +
        ‖WithLp.toLp 2 ((C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i - C.δ i / C.γ i) •
          (C.r i - C.r (i + 1)))‖ := by
      refine (EuclideanSpace.norm_toLp_add_le _ _).trans (add_le_add_left ?_ _)
      refine (EuclideanSpace.norm_toLp_sub_le _ _).trans (add_le_add_left ?_ _)
      refine (EuclideanSpace.norm_toLp_add_le _ _).trans (add_le_add_left ?_ _)
      refine (EuclideanSpace.norm_toLp_sub_le _ _).trans (add_le_add_left ?_ _)
      refine (EuclideanSpace.norm_toLp_add_le _ _).trans (le_of_eq ?_)
      rw [WithLp.toLp_neg, norm_neg]
  exact hsum.trans (recurrenceError_scalar_le hε0 C.ε_le hN hB0 (C.P_nonneg hi hP) hρ.le
    (norm_nonneg _) (mul_nonneg hδ0 (norm_nonneg _)) hP (C.δ_mul_norm_p_le hi') (C.inv_γ_le hi hP)
    (C.norm_es_le (i + 1) hi) t2 t3 t4 t5 (C.norm_convention_le hi hβ hδB))

/-- The first step of Lemma A:
$\|\bar{\mathbf{f}}_0\| \le 8\varepsilon\|\mathbf{A}\|_2(1+\Pi)^2$. -/
private theorem norm_recurrenceError_zero_le {P : ℝ}
    (hP : ‖WithLp.toLp 2 (C.p 0)‖ ≤ P * C.ρ 0) :
    ‖WithLp.toLp 2 (C.toLanczosData.recurrenceError 0)‖ ≤
      8 * C.ε * (specNorm C.A * (1 + P) ^ 2) := by
  have hk := C.k_pos
  have hγ := C.γ_pos hk
  have hρ := C.ρ_pos hk
  have hN := specNorm_nonneg C.A
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p 0))
  have hP0 := C.P_nonneg hk hP
  rw [C.recurrenceError_zero, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
  have t := EuclideanSpace.norm_toLp_add_le (-C.es 0) ((C.γ 0)⁻¹ • C.er 0)
  rw [WithLp.toLp_neg, norm_neg, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hγ] at t
  have t1 := C.norm_es_le 0 hk
  have t2 := mul_le_mul_of_nonneg_left (C.norm_er_le_of_lt hk) (inv_nonneg.2 hγ.le)
  have hs := C.norm_s_le hk
  have hinv := C.inv_γ_le hk hP
  have e : (C.γ 0)⁻¹ * (C.ε * (C.ρ 0 + C.γ 0 * ‖WithLp.toLp 2 (C.s 0)‖)) =
      C.ε * ((C.γ 0)⁻¹ * C.ρ 0) + C.ε * ‖WithLp.toLp 2 (C.s 0)‖ := by
    field_simp
  rw [e] at t2
  have h1 : C.ε * ((C.γ 0)⁻¹ * C.ρ 0) ≤ C.ε * (21 / 20 * specNorm C.A * P ^ 2 * C.ρ 0) := by
    gcongr
  have h2 : C.ε * ‖WithLp.toLp 2 (C.s 0)‖ ≤ C.ε * (2 * specNorm C.A * (P * C.ρ 0)) := by
    gcongr
    calc _ ≤ _ := hs
      _ ≤ 2 * specNorm C.A * (P * C.ρ 0) := by gcongr; linarith
  have h3 : C.ε * specNorm C.A * ‖WithLp.toLp 2 (C.p 0)‖ ≤ C.ε * specNorm C.A * (P * C.ρ 0) := by
    gcongr
  have hpoly : C.ε * (specNorm C.A * (P * C.ρ 0)) + C.ε * (21 / 20 * specNorm C.A * P ^ 2 * C.ρ 0) +
      C.ε * (2 * specNorm C.A * (P * C.ρ 0)) ≤ 8 * C.ε * (specNorm C.A * (1 + P) ^ 2) * C.ρ 0 := by
    have a1 : 0 ≤ C.ε * specNorm C.A * C.ρ 0 := by positivity
    have a2 : 0 ≤ C.ε * specNorm C.A * C.ρ 0 * P := by positivity
    have a3 : 0 ≤ C.ε * specNorm C.A * C.ρ 0 * P ^ 2 := by positivity
    linarith only [a1, a2, a3]
  rw [inv_mul_le_iff₀ hρ]
  linarith only [t, t1, t2, h1, h2, h3, hpoly]

/-- **Lemma A (recurrence error)**: with certificates $\|\mathbf{p}_j\| \le \Pi\rho_j$
($j < k$) and $\beta_{j+1}, \delta_j/\gamma_j \le B$ ($j + 1 < k$), the Lanczos data of the
run satisfy
$$\|\bar{\mathbf{f}}_j\| \le 8\varepsilon\bigl(\|\mathbf{A}\|_2(1 + \Pi)^2 + B\bigr),
\qquad j < k .$$
No residual ratio enters. No printed source; after
[GreenbaumLiuChen2021, (2.2)–(2.4)], who derive the perturbation term but do not bound it.
The hypothesis $0 \le B$ is automatic for $k \ge 2$ ($0 < \beta_1 \le B$) and is needed
for $k = 1$, where `hB` is vacuous. -/
theorem norm_recurrenceError_le {P B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) (hB0 : 0 ≤ B) {j : ℕ}
    (hj : j < k) :
    ‖WithLp.toLp 2 (C.toLanczosData.recurrenceError j)‖ ≤
      8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B) := by
  rcases j with _ | i
  · have h := C.norm_recurrenceError_zero_le (hP 0 C.k_pos)
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) C.ε_nonneg) hB0
    nlinarith
  · have hρ := C.ρ_pos hj
    obtain ⟨hβ, hδ⟩ := hB i hj
    have h := C.norm_recurrenceError_succ_mul_le hj (hP (i + 1) hj) hβ hδ
    rw [C.recurrenceError_succ hj, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_inv, abs_of_pos hρ, inv_mul_le_iff₀ hρ]
    linarith

end CGRun

end NLAlib
