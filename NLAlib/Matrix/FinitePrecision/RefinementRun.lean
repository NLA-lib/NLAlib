/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.Inverse

/-!
# An iterative refinement run with bounded local errors

`NLAlib.RefinementRun A b θ η ζ ε k` is $k$ steps of iterative refinement for
$\mathbf{A}\mathbf{x} = \mathbf{b}$ with $\mathbf{A}$ invertible, each of the three operations of
a step carrying its own accuracy parameter (0-based, step $j < k$):
$$\mathbf{r}_j \approx \mathbf{b} - \mathbf{A}\mathbf{x}_j,\quad
\mathbf{d}_j \approx \mathbf{A}^{-1}\mathbf{r}_j,\quad
\mathbf{x}_{j+1} \approx \mathbf{x}_j + \mathbf{d}_j .$$
The residual has error at most $\zeta\|\mathbf{b} - \mathbf{A}\mathbf{x}_j\| +
\eta(\|\mathbf{b}\| + \|\mathbf{A}\|_2\|\mathbf{x}_j\|)$, the correction has relative
error at most $\theta$, and the update has relative error at most $\varepsilon$. In
refinement in three precisions [CarsonHigham2018] the residual is computed at unit roundoff
$u_r$ and stored at the working unit roundoff $u$, the correction is solved with factors computed
at unit roundoff $u_f$, and the update is at $u$: then $\eta$ is of order $u_r$,
$\zeta$ and $\varepsilon$ are of order $u$, and $\theta$ is of order
$\kappa(\mathbf{A})u_f$ (`NLAlib.norm_inv_mulVec_sub_le_of_add_mulVec_eq`).

This is an abstract local-error interface, in the Euclidean and spectral norms. Applying its
guarantees to a particular program requires a separate execution theorem constructing this
interface from the decoded computed states.

With $\kappa = \kappa(\mathbf{A})$, the error contracts at each step by the factor
`NLAlib.refinementContractionFactor`,
whose value is <!-- value refinementContractionFactor \kappa \theta \eta \zeta \varepsilon -->
$(1+\varepsilon)(\theta+(1+\theta)\kappa(\zeta+\eta))$, up to $\|\mathbf{x}_\star\|$ times
`NLAlib.refinementAccuracyBound`,
whose value is <!-- value refinementAccuracyBound \kappa \theta \eta \varepsilon -->
$(1+\varepsilon)(1+\theta)2\kappa\eta+\varepsilon$. The solve accuracy $\theta$ sets the rate.
It enters the limiting term $\xi/(1 - \varphi)$ only through $1 + \theta$ and $1 - \varphi$, so
for $\varphi$ bounded away from one a less accurate solve changes that term by a constant factor.

Constants are unoptimised.

## Main definitions

* `NLAlib.RefinementRun`: a run of $k$ steps with its four accuracy parameters.
* `NLAlib.RefinementRun.start`, `NLAlib.RefinementRun.extend`: the run of no steps, and
  one more step.

## Main results

* `NLAlib.RefinementRun.norm_sub_x_succ_le`: one step contracts the error up to an additive term.
* `NLAlib.RefinementRun.norm_sub_x_le`: the error after $j$ steps.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The rate and the limiting accuracy -/

/-- The **contraction factor of one refinement step**, for condition number $\kappa$ and accuracy
parameters $\theta$ (correction), $\eta$, $\zeta$ (residual) and $\varepsilon$ (update). Its
value is <!-- value refinementContractionFactor \kappa \theta \eta \zeta \varepsilon -->
$$(1+\varepsilon)(\theta+(1+\theta)\kappa(\zeta+\eta))\,.$$
It is the coefficient of the current error in `NLAlib.RefinementRun.norm_sub_x_succ_le`. No
printed value: the normwise analogue of the coefficient of the error in
[CarsonHigham2018, Theorem 3.2]. -/
def refinementContractionFactor (κ θ η ζ ε : ℝ) : ℝ :=
  (1 + ε) * (θ + (1 + θ) * (κ * (ζ + η)))

/-- The **accuracy bound of one refinement step**, for condition number $\kappa$ and accuracy
parameters $\theta$ (correction), $\eta$ (residual) and $\varepsilon$ (update). Its value is
the following. <!-- value refinementAccuracyBound \kappa \theta \eta \varepsilon -->
$$(1+\varepsilon)(1+\theta)2\kappa\eta+\varepsilon\,.$$
It multiplies $\|\mathbf{x}_\star\|$ in `NLAlib.RefinementRun.norm_sub_x_succ_le`. For small
parameters it is about $2\kappa\eta + \varepsilon$. It plays the role of the limiting accuracy
$4 p u_r \operatorname{cond}(\mathbf{A}, \mathbf{x}) + u$ of [CarsonHigham2018, (3.10)], with
$p$ the largest number of nonzeros in a row of $[\mathbf{A}\ \mathbf{b}]$. -/
def refinementAccuracyBound (κ θ η ε : ℝ) : ℝ :=
  (1 + ε) * ((1 + θ) * (2 * κ * η)) + ε

/-- The contraction factor is nonnegative for nonnegative arguments. -/
theorem refinementContractionFactor_nonneg {κ θ η ζ ε : ℝ} (hκ : 0 ≤ κ) (hs : 0 ≤ θ)
    (hr : 0 ≤ η) (hc : 0 ≤ ζ) (hx : 0 ≤ ε) :
    0 ≤ refinementContractionFactor κ θ η ζ ε := by
  unfold refinementContractionFactor
  positivity

/-- The accuracy bound is nonnegative for nonnegative arguments. -/
theorem refinementAccuracyBound_nonneg {κ θ η ε : ℝ} (hκ : 0 ≤ κ) (hs : 0 ≤ θ)
    (hr : 0 ≤ η) (hx : 0 ≤ ε) : 0 ≤ refinementAccuracyBound κ θ η ε := by
  unfold refinementAccuracyBound
  positivity

/-! ### The run -/

/-- **An iterative refinement run with bounded local errors**: $k$ steps of
$\mathbf{r}_j \approx \mathbf{b} - \mathbf{A}\mathbf{x}_j$,
$\mathbf{d}_j \approx \mathbf{A}^{-1}\mathbf{r}_j$,
$\mathbf{x}_{j+1} \approx \mathbf{x}_j + \mathbf{d}_j$ for an invertible
$\mathbf{A} \in \Bbbk^{n \times n}$, with four nonnegative accuracy parameters: the residual has
error at most $\zeta\|\mathbf{b} - \mathbf{A}\mathbf{x}_j\| +
\eta(\|\mathbf{b}\| + \|\mathbf{A}\|_2\|\mathbf{x}_j\|)$, the correction has error at
most $\theta\|\mathbf{A}^{-1}\mathbf{r}_j\|$, and the update has error at most
$\varepsilon\|\mathbf{x}_j + \mathbf{d}_j\|$. The start $\mathbf{x}_0$ is unrestricted and no
smallness of the parameters is assumed; the convergence theorems state it.
[CarsonHigham2018, Algorithm 1.1]; analysed there componentwise and in the $\infty$-norm for
three unit roundoffs, here in the Euclidean norm for abstract accuracy parameters.
Algorithm: iterative-refinement (run model) -/
structure RefinementRun (A : Matrix n n 𝕜) (b : n → 𝕜) (θ η ζ ε : ℝ) (k : ℕ) where
  /-- The iterates $\mathbf{x}_j$. -/
  x : ℕ → n → 𝕜
  /-- The computed residuals $\mathbf{r}_j$. -/
  r : ℕ → n → 𝕜
  /-- The computed corrections $\mathbf{d}_j$. -/
  d : ℕ → n → 𝕜
  /-- The matrix is invertible. -/
  isUnit_A : IsUnit A
  /-- The solve accuracy is nonnegative. -/
  θ_nonneg : 0 ≤ θ
  /-- The operand-relative residual accuracy is nonnegative. -/
  η_nonneg : 0 ≤ η
  /-- The residual-relative residual accuracy is nonnegative. -/
  ζ_nonneg : 0 ≤ ζ
  /-- The update accuracy is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- The error of the computed residual. -/
  norm_sub_mulVec_sub_r_le : ∀ j < k, ‖WithLp.toLp 2 (b - A *ᵥ x j - r j)‖ ≤
    ζ * ‖WithLp.toLp 2 (b - A *ᵥ x j)‖ +
      η * (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 (x j)‖)
  /-- The error of the computed correction. -/
  norm_inv_mulVec_sub_d_le : ∀ j < k,
    ‖WithLp.toLp 2 (A⁻¹ *ᵥ r j - d j)‖ ≤ θ * ‖WithLp.toLp 2 (A⁻¹ *ᵥ r j)‖
  /-- The error of the update. -/
  norm_add_sub_x_succ_le : ∀ j < k,
    ‖WithLp.toLp 2 (x j + d j - x (j + 1))‖ ≤ ε * ‖WithLp.toLp 2 (x j + d j)‖

namespace RefinementRun

variable {k : ℕ}

/-- The scalar inequality of one refinement step: with $E$ the current error, $X$ the size of the
solution, $a$ the error of $\mathbf{A}^{-1}\mathbf{r}$, $f$ that of the correction and $g$ that of
the update, the local bounds give $a + f + g \le \varphi E + \xi X$ with $\varphi$ the contraction
factor and $\xi$ the accuracy bound. -/
private theorem add_add_le_factor_mul_add_bound_mul {sA sA' θ η ζ ε E X a f g T res tr nb nx
    nxd : ℝ} (hsA : 0 ≤ sA) (hsA' : 0 ≤ sA') (hs : 0 ≤ θ) (hr : 0 ≤ η) (hc : 0 ≤ ζ)
    (hx : 0 ≤ ε) (h₁ : a ≤ sA' * res) (h₂ : res ≤ ζ * tr + η * (nb + sA * nx))
    (h₃ : tr ≤ sA * E) (h₄ : nb ≤ sA * X) (h₅ : nx ≤ X + E) (h₆ : T ≤ E + a)
    (h₇ : f ≤ θ * T) (h₈ : g ≤ ε * nxd) (h₉ : nxd ≤ X + a + f) :
    a + f + g ≤ refinementContractionFactor (sA * sA') θ η ζ ε * E +
      refinementAccuracyBound (sA * sA') θ η ε * X := by
  have hres : res ≤ ζ * (sA * E) + η * (sA * X + sA * (X + E)) :=
    h₂.trans (add_le_add (mul_le_mul_of_nonneg_left h₃ hc)
      (mul_le_mul_of_nonneg_left (add_le_add h₄ (mul_le_mul_of_nonneg_left h₅ hsA)) hr))
  have ha : a ≤ sA * sA' * ((ζ + η) * E + 2 * η * X) := by
    calc a ≤ sA' * (ζ * (sA * E) + η * (sA * X + sA * (X + E))) :=
          h₁.trans (mul_le_mul_of_nonneg_left hres hsA')
      _ = sA * sA' * ((ζ + η) * E + 2 * η * X) := by ring
  set ρ := sA * sA' * ((ζ + η) * E + 2 * η * X) with hρ
  have hf : f ≤ θ * (E + ρ) :=
    h₇.trans (mul_le_mul_of_nonneg_left (h₆.trans (by linarith)) hs)
  have hg : g ≤ ε * (X + ρ + θ * (E + ρ)) :=
    h₈.trans (mul_le_mul_of_nonneg_left (h₉.trans (by linarith)) hx)
  calc a + f + g ≤ ρ + θ * (E + ρ) + ε * (X + ρ + θ * (E + ρ)) := by linarith
    _ = refinementContractionFactor (sA * sA') θ η ζ ε * E +
        refinementAccuracyBound (sA * sA') θ η ε * X := by
      rw [hρ, refinementContractionFactor, refinementAccuracyBound]
      ring

variable {A : Matrix n n 𝕜} {b : n → 𝕜} {θ η ζ ε : ℝ}

/-- **The run of no steps** from the start $\mathbf{x}_0$, for an invertible $\mathbf{A}$ and
nonnegative accuracy parameters. -/
def start (hA : IsUnit A) (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hε : 0 ≤ ε) (x₀ : n → 𝕜) :
    RefinementRun A b θ η ζ ε 0 where
  x _ := x₀
  r _ := 0
  d _ := 0
  isUnit_A := hA
  θ_nonneg := hθ
  η_nonneg := hη
  ζ_nonneg := hζ
  ε_nonneg := hε
  norm_sub_mulVec_sub_r_le j hj := absurd hj (Nat.not_lt_zero j)
  norm_inv_mulVec_sub_d_le j hj := absurd hj (Nat.not_lt_zero j)
  norm_add_sub_x_succ_le j hj := absurd hj (Nat.not_lt_zero j)

/-- The iterates of the run of no steps are the start. -/
@[simp]
theorem start_x (hA : IsUnit A) (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hε : 0 ≤ ε)
    (x₀ : n → 𝕜) (j : ℕ) : (start (b := b) hA hθ hη hζ hε x₀).x j = x₀ :=
  rfl

/-- **One more step of a run**: a run of $k$ steps, with a residual $\mathbf{r}$, a correction
$\mathbf{d}$ and a next iterate $\mathbf{x}'$ that meet the three local bounds at
$\mathbf{x}_k$, is a run of $k + 1$ steps with $\mathbf{x}_{k+1} = \mathbf{x}'$. An execution
theorem builds its run with it, one step of the program at a time. -/
def extend (R : RefinementRun A b θ η ζ ε k) (r d x' : n → 𝕜)
    (hr : ‖WithLp.toLp 2 (b - A *ᵥ R.x k - r)‖ ≤ ζ * ‖WithLp.toLp 2 (b - A *ᵥ R.x k)‖ +
      η * (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 (R.x k)‖))
    (hd : ‖WithLp.toLp 2 (A⁻¹ *ᵥ r - d)‖ ≤ θ * ‖WithLp.toLp 2 (A⁻¹ *ᵥ r)‖)
    (hx : ‖WithLp.toLp 2 (R.x k + d - x')‖ ≤ ε * ‖WithLp.toLp 2 (R.x k + d)‖) :
    RefinementRun A b θ η ζ ε (k + 1) where
  x := Function.update R.x (k + 1) x'
  r := Function.update R.r k r
  d := Function.update R.d k d
  isUnit_A := R.isUnit_A
  θ_nonneg := R.θ_nonneg
  η_nonneg := R.η_nonneg
  ζ_nonneg := R.ζ_nonneg
  ε_nonneg := R.ε_nonneg
  norm_sub_mulVec_sub_r_le j hj := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact R.norm_sub_mulVec_sub_r_le j hlt
    · rw [Function.update_of_ne (by omega), Function.update_self]
      exact hr
  norm_inv_mulVec_sub_d_le j hj := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact R.norm_inv_mulVec_sub_d_le j hlt
    · rw [Function.update_self, Function.update_self]
      exact hd
  norm_add_sub_x_succ_le j hj := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact R.norm_add_sub_x_succ_le j hlt
    · rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
      exact hx

/-- Extending a run keeps its first $k + 1$ iterates. -/
theorem extend_x_of_le (R : RefinementRun A b θ η ζ ε k) (r d x' : n → 𝕜)
    (hr : ‖WithLp.toLp 2 (b - A *ᵥ R.x k - r)‖ ≤ ζ * ‖WithLp.toLp 2 (b - A *ᵥ R.x k)‖ +
      η * (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 (R.x k)‖))
    (hd : ‖WithLp.toLp 2 (A⁻¹ *ᵥ r - d)‖ ≤ θ * ‖WithLp.toLp 2 (A⁻¹ *ᵥ r)‖)
    (hx : ‖WithLp.toLp 2 (R.x k + d - x')‖ ≤ ε * ‖WithLp.toLp 2 (R.x k + d)‖) {j : ℕ}
    (hj : j ≤ k) : (R.extend r d x' hr hd hx).x j = R.x j :=
  Function.update_of_ne (by omega) _ _

/-- The last iterate of an extended run is the new iterate. -/
@[simp]
theorem extend_x_succ (R : RefinementRun A b θ η ζ ε k) (r d x' : n → 𝕜)
    (hr : ‖WithLp.toLp 2 (b - A *ᵥ R.x k - r)‖ ≤ ζ * ‖WithLp.toLp 2 (b - A *ᵥ R.x k)‖ +
      η * (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 (R.x k)‖))
    (hd : ‖WithLp.toLp 2 (A⁻¹ *ᵥ r - d)‖ ≤ θ * ‖WithLp.toLp 2 (A⁻¹ *ᵥ r)‖)
    (hx : ‖WithLp.toLp 2 (R.x k + d - x')‖ ≤ ε * ‖WithLp.toLp 2 (R.x k + d)‖) :
    (R.extend r d x' hr hd hx).x (k + 1) = x' :=
  Function.update_self _ _ _

/-- **One step of iterative refinement contracts the error.** For an invertible
$\mathbf{A} \in \Bbbk^{n \times n}$, a run with accuracy parameters $\theta$, $\eta$, $\zeta$,
$\varepsilon$ and the solution $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, every step $j < k$
satisfies
$$\|\mathbf{x}_\star - \mathbf{x}_{j+1}\| \le \varphi\,\|\mathbf{x}_\star - \mathbf{x}_j\| +
\xi\,\|\mathbf{x}_\star\|\,.$$
Here, with $\kappa = \kappa(\mathbf{A})$, the contraction factor is
the following, <!-- value refinementContractionFactor \kappa \theta \eta \zeta \varepsilon -->
$\varphi = (1+\varepsilon)(\theta+(1+\theta)\kappa(\zeta+\eta))$, and the accuracy bound is
the following, <!-- value refinementAccuracyBound \kappa \theta \eta \varepsilon -->
$\xi = (1+\varepsilon)(1+\theta)2\kappa\eta+\varepsilon$. No smallness of the parameters is
assumed.
[CarsonHigham2018, Theorem 3.2]; stated there in the $\infty$-norm with a componentwise residual
bound, here in the Euclidean norm. -/
theorem norm_sub_x_succ_le (R : RefinementRun A b θ η ζ ε k) {xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (xs - R.x (j + 1))‖ ≤
      refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε *
          ‖WithLp.toLp 2 (xs - R.x j)‖ +
        refinementAccuracyBound (pseudoConditionNumber A) θ η ε *
          ‖WithLp.toLp 2 xs‖ := by
  have hinv : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp R.isUnit_A)
  have hres : b - A *ᵥ R.x j = A *ᵥ (xs - R.x j) := by rw [Matrix.mulVec_sub, hxs]
  have ht : xs - R.x j - A⁻¹ *ᵥ R.r j = A⁻¹ *ᵥ (b - A *ᵥ R.x j - R.r j) := by
    rw [Matrix.mulVec_sub, hres, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h₁ : ‖WithLp.toLp 2 (xs - R.x j - A⁻¹ *ᵥ R.r j)‖ ≤
      specNorm A⁻¹ * ‖WithLp.toLp 2 (b - A *ᵥ R.x j - R.r j)‖ := by
    rw [ht]
    exact norm_toLp_mulVec_le _ _
  have h₃ : ‖WithLp.toLp 2 (b - A *ᵥ R.x j)‖ ≤
      specNorm A * ‖WithLp.toLp 2 (xs - R.x j)‖ := by
    rw [hres]
    exact norm_toLp_mulVec_le _ _
  have h₄ : ‖WithLp.toLp 2 b‖ ≤ specNorm A * ‖WithLp.toLp 2 xs‖ := by
    rw [← hxs]
    exact norm_toLp_mulVec_le _ _
  have h₅ : ‖WithLp.toLp 2 (R.x j)‖ ≤ ‖WithLp.toLp 2 xs‖ + ‖WithLp.toLp 2 (xs - R.x j)‖ := by
    have : WithLp.toLp 2 (R.x j) = WithLp.toLp 2 xs - WithLp.toLp 2 (xs - R.x j) := by
      rw [← WithLp.toLp_sub, sub_sub_cancel]
    rw [this]
    exact norm_sub_le _ _
  have h₆ : ‖WithLp.toLp 2 (A⁻¹ *ᵥ R.r j)‖ ≤ ‖WithLp.toLp 2 (xs - R.x j)‖ +
      ‖WithLp.toLp 2 (xs - R.x j - A⁻¹ *ᵥ R.r j)‖ := by
    have : WithLp.toLp 2 (A⁻¹ *ᵥ R.r j) = WithLp.toLp 2 (xs - R.x j) -
        WithLp.toLp 2 (xs - R.x j - A⁻¹ *ᵥ R.r j) := by
      rw [← WithLp.toLp_sub, sub_sub_cancel]
    rw [this]
    exact norm_sub_le _ _
  have h₉ : ‖WithLp.toLp 2 (R.x j + R.d j)‖ ≤ ‖WithLp.toLp 2 xs‖ +
      ‖WithLp.toLp 2 (xs - R.x j - A⁻¹ *ᵥ R.r j)‖ +
      ‖WithLp.toLp 2 (A⁻¹ *ᵥ R.r j - R.d j)‖ := by
    have : WithLp.toLp 2 (R.x j + R.d j) = WithLp.toLp 2 xs -
        WithLp.toLp 2 (xs - R.x j - A⁻¹ *ᵥ R.r j) -
        WithLp.toLp 2 (A⁻¹ *ᵥ R.r j - R.d j) := by
      rw [← WithLp.toLp_sub, ← WithLp.toLp_sub]
      congr 1
      ext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
  have hsplit : ‖WithLp.toLp 2 (xs - R.x (j + 1))‖ ≤
      ‖WithLp.toLp 2 (xs - R.x j - A⁻¹ *ᵥ R.r j)‖ +
        ‖WithLp.toLp 2 (A⁻¹ *ᵥ R.r j - R.d j)‖ +
        ‖WithLp.toLp 2 (R.x j + R.d j - R.x (j + 1))‖ := by
    have : WithLp.toLp 2 (xs - R.x (j + 1)) = WithLp.toLp 2 (xs - R.x j - A⁻¹ *ᵥ R.r j) +
        WithLp.toLp 2 (A⁻¹ *ᵥ R.r j - R.d j) +
        WithLp.toLp 2 (R.x j + R.d j - R.x (j + 1)) := by
      rw [← WithLp.toLp_add, ← WithLp.toLp_add]
      congr 1
      ext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  rw [pseudoConditionNumber_of_isUnit R.isUnit_A]
  exact hsplit.trans (add_add_le_factor_mul_add_bound_mul (specNorm_nonneg _) (specNorm_nonneg _)
    R.θ_nonneg R.η_nonneg R.ζ_nonneg R.ε_nonneg h₁ (R.norm_sub_mulVec_sub_r_le j hj) h₃ h₄ h₅
    h₆ (R.norm_inv_mulVec_sub_d_le j hj) (R.norm_add_sub_x_succ_le j hj) h₉)

/-- **Forward error of iterative refinement.** For an invertible
$\mathbf{A} \in \Bbbk^{n \times n}$, a run of $k$ steps with accuracy parameters $\theta$,
$\eta$, $\zeta$, $\varepsilon$, the solution $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and
contraction factor $\varphi < 1$, every $j \le k$ satisfies
$$\|\mathbf{x}_\star - \mathbf{x}_j\| \le \varphi^j\|\mathbf{x}_\star - \mathbf{x}_0\| +
\frac{\xi}{1 - \varphi}\,\|\mathbf{x}_\star\|\,.$$
Here, with $\kappa = \kappa(\mathbf{A})$, the contraction factor is
the following, <!-- value refinementContractionFactor \kappa \theta \eta \zeta \varepsilon -->
$\varphi = (1+\varepsilon)(\theta+(1+\theta)\kappa(\zeta+\eta))$, and the accuracy bound is
the following, <!-- value refinementAccuracyBound \kappa \theta \eta \varepsilon -->
$\xi = (1+\varepsilon)(1+\theta)2\kappa\eta+\varepsilon$.
[CarsonHigham2018, Corollary 3.3]; stated there in the $\infty$-norm as a limiting accuracy
$4 p u_r \operatorname{cond}(\mathbf{A}, \mathbf{x}) + u$, with $p$ the largest number of nonzeros
in a row of $[\mathbf{A}\ \mathbf{b}]$, and a rate that depends only on the solve; here in the
Euclidean norm with the transient term, and the rate also has the term
$\kappa(\mathbf{A})(\zeta + \eta)$.

Note: the limiting term involves the solve accuracy $\theta$ only through $1 + \theta$ and
$1 - \varphi$, so for $\varphi$ bounded away from one a less accurate solve changes it by a
constant factor. One step is `NLAlib.RefinementRun.norm_sub_x_succ_le`.
Result: iterative-refinement-forward-error -/
theorem norm_sub_x_le (R : RefinementRun A b θ η ζ ε k) {xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (hφ : refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε < 1)
    {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (xs - R.x j)‖ ≤
      refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε ^ j *
          ‖WithLp.toLp 2 (xs - R.x 0)‖ +
        refinementAccuracyBound (pseudoConditionNumber A) θ η ε /
          (1 - refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε) *
          ‖WithLp.toLp 2 xs‖ := by
  set φ := refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε with hφdef
  set ξ := refinementAccuracyBound (pseudoConditionNumber A) θ η ε with hξdef
  have hφ0 : 0 ≤ φ := refinementContractionFactor_nonneg (pseudoConditionNumber_nonneg _)
    R.θ_nonneg R.η_nonneg R.ζ_nonneg R.ε_nonneg
  have hden : 0 < 1 - φ := by linarith
  induction j with
  | zero =>
    have hξ0 : 0 ≤ ξ := refinementAccuracyBound_nonneg (pseudoConditionNumber_nonneg _)
      R.θ_nonneg R.η_nonneg R.ε_nonneg
    have : 0 ≤ ξ / (1 - φ) * ‖WithLp.toLp 2 xs‖ := by positivity
    simpa using this
  | succ j ih =>
    have hstep := R.norm_sub_x_succ_le hxs (Nat.lt_of_succ_le hj)
    have hih := mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hj)) hφ0
    calc ‖WithLp.toLp 2 (xs - R.x (j + 1))‖
        ≤ φ * ‖WithLp.toLp 2 (xs - R.x j)‖ + ξ * ‖WithLp.toLp 2 xs‖ := hstep
      _ ≤ φ * (φ ^ j * ‖WithLp.toLp 2 (xs - R.x 0)‖ + ξ / (1 - φ) * ‖WithLp.toLp 2 xs‖) +
          ξ * ‖WithLp.toLp 2 xs‖ := by linarith
      _ = φ ^ (j + 1) * ‖WithLp.toLp 2 (xs - R.x 0)‖ + ξ / (1 - φ) * ‖WithLp.toLp 2 xs‖ := by
        field_simp
        ring

end RefinementRun

end NLAlib
