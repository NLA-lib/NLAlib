/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.CholeskyRoundingError
public import NLAlib.Matrix.FinitePrecision.RefinementRun

/-!
# The local errors of one round of three-precision refinement

Three statements about values, with no memory in them: the residual computed in the residual
precision and cast to the working precision, the correction solved with the computed Cholesky
factor, and the update in the working precision. Each is one of the local bounds of
`NLAlib.RefinementRun`. All norms are Euclidean.

## Main results

* `NLAlib.LinearSystems.Refinement.Rounded.norm_toLp_sub_le_of_abs_sub_le`: a componentwise
  relative error is a normwise one.
* `NLAlib.LinearSystems.Refinement.Rounded.norm_sub_mulVec_sub_cast_le`: the residual bound.
* `NLAlib.LinearSystems.Refinement.Rounded.norm_inv_mulVec_sub_correction_le`: the solve bound.
* `NLAlib.LinearSystems.Refinement.Rounded.norm_add_sub_update_le`: the update bound.
-/

@[expose] public section

namespace NLAlib.LinearSystems.Refinement.Rounded

open Computation
open scoped Matrix

variable {n : ℕ}

/-- A componentwise relative error is a normwise one. For $c \ge 0$, if
$\lvert y_i - x_i \rvert \le c \lvert x_i \rvert$ for every $i$, then
$\|\mathbf{x} - \mathbf{y}\| \le c \|\mathbf{x}\|$ in the Euclidean norm. -/
theorem norm_toLp_sub_le_of_abs_sub_le {x y : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |y i - x i| ≤ c * |x i|) :
    ‖WithLp.toLp 2 (x - y)‖ ≤ c * ‖WithLp.toLp 2 x‖ := by
  have hdom := EuclideanSpace.norm_toLp_le_norm_toLp (x := x - y)
    (y := c • fun i => |x i|) fun i => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.sub_apply, abs_sub_comm]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [abs_of_nonneg (mul_nonneg hc (abs_nonneg _))]
      exact h i
  refine hdom.trans ?_
  rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hc]
  have hb : ‖WithLp.toLp 2 (fun i => |x i|)‖ = ‖WithLp.toLp 2 x‖ := by
    simp [EuclideanSpace.norm_eq]
  rw [hb]

/-- The residual computed in the residual precision and cast to the working precision. Let
$\hat{\mathbf{r}}$ be computed from $\mathbf{b}$, $\mathbf{A}$, $\mathbf{x}$ row by row at unit
roundoff $u_r \ge 0$ with $(n + 1) u_r < 1$, and let $\tilde{\mathbf{r}}$ be $\hat{\mathbf{r}}$
with relative error $u \ge 0$ in each entry. With $\mathbf{r} = \mathbf{b} - \mathbf{A}\mathbf{x}$
and $\gamma_{n+1} = (1 - u_r)^{-(n+1)} - 1$,
$$\|\mathbf{r} - \tilde{\mathbf{r}}\| \le u \|\mathbf{r}\| +
(1 + u)(n + 1)\gamma_{n+1} \bigl(\|\mathbf{b}\| + \|\mathbf{A}\|_2 \|\mathbf{x}\|\bigr).$$ -/
theorem norm_sub_mulVec_sub_cast_le {A : Matrix (Fin n) (Fin n) ℝ} {b x rh rt : Fin n → ℝ}
    {u ur : ℝ} (hu : 0 ≤ u) (hur : 0 ≤ ur) (hn : ((n : ℝ) + 1) * ur < 1)
    (htr : ∀ i : Fin n, ∃ s : ℕ → ℝ, IsSubstRowTrace (fun _ => RelErr ur)
      (fun i j => if hi : i < n then if hj : j < n then A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
      (fun i => if hi : i < n then b ⟨i, hi⟩ else 0)
      (fun j => if hj : j < n then x ⟨j, hj⟩ else 0) i n s ∧ s n = rh i)
    (hc : ∀ i, |rt i - rh i| ≤ u * |rh i|) :
    ‖WithLp.toLp 2 (b - A *ᵥ x - rt)‖ ≤ u * ‖WithLp.toLp 2 (b - A *ᵥ x)‖ +
      (1 + u) * (((n : ℝ) + 1) * roundingFactor (n + 1) ur) *
        (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 x‖) := by
  have he := norm_sub_mulVec_sub_le_of_isSubstRowTrace hur hn htr
  have hcast := norm_toLp_sub_le_of_abs_sub_le hu hc
  set r := b - A *ᵥ x with hr
  have hsplit : ‖WithLp.toLp 2 (r - rt)‖ ≤
      ‖WithLp.toLp 2 (r - rh)‖ + ‖WithLp.toLp 2 (rh - rt)‖ := by
    rw [show WithLp.toLp 2 (r - rt) = WithLp.toLp 2 (r - rh) + WithLp.toLp 2 (rh - rt) by
      rw [← WithLp.toLp_add, sub_add_sub_cancel]]
    exact norm_add_le _ _
  have hrh : ‖WithLp.toLp 2 rh‖ ≤ ‖WithLp.toLp 2 r‖ + ‖WithLp.toLp 2 (r - rh)‖ := by
    rw [show WithLp.toLp 2 rh = WithLp.toLp 2 r - WithLp.toLp 2 (r - rh) by
      rw [← WithLp.toLp_sub, sub_sub_cancel]]
    exact norm_sub_le _ _
  have hmul := mul_le_mul_of_nonneg_left hrh hu
  have heu := mul_le_mul_of_nonneg_left he hu
  nlinarith

/-- **The correction solved with the computed Cholesky factor.** Let $\mathbf{A}$ be positive
definite of order $n$, let $l$ be a trace of left-looking Cholesky at unit roundoff $u_f \ge 0$
on entries $a_{ij}$ read with relative error $u_f$, with
$24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A}) \le 1$. Let $\hat{\mathbf{r}}$ be $\mathbf{r}$ with
relative error $u_f$ in each entry, $\mathbf{y}$ a forward substitution trace from
$\hat{\mathbf{r}}$ and $\mathbf{d}$ a back substitution trace from $\mathbf{y}$, at unit roundoff
$u_f$. Then
$$\|\mathbf{A}^{-1}\mathbf{r} - \mathbf{d}\| \le 24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A})
\|\mathbf{A}^{-1}\mathbf{r}\|.$$
[CarsonHigham2018, (2.3)]; the assumption there on the solver, for Cholesky. -/
theorem norm_inv_mulVec_sub_correction_le {A : Matrix (Fin n) (Fin n) ℝ} {a L : ℕ → ℕ → ℝ}
    {uf : ℝ} (h : IsCholTrace uf a L n) (hA : A.PosDef) (huf : 0 ≤ uf)
    (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ uf * |A i j|)
    (hsmall : 24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A ≤ 1)
    {r : Fin n → ℝ} {rh y d : ℕ → ℝ} (hr : ∀ i : Fin n, |rh i - r i| ≤ uf * |r i|)
    (hy : IsSubstTrace (fun _ => RelErr uf) L rh n y) (hd : IsBackSubstTrace uf L y n d)
    {dW : Fin n → ℝ} (hdW : ∀ i : Fin n, dW i = d i) :
    ‖WithLp.toLp 2 (A⁻¹ *ᵥ r - dW)‖ ≤
      24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A *
        ‖WithLp.toLp 2 (A⁻¹ *ᵥ r)‖ := by
  have hfun : dW = fun i : Fin n => d i := funext hdW
  rw [hfun]
  exact norm_inv_mulVec_sub_le_of_isCholTrace h hA huf huf ha hsmall hr hy hd

/-- The update in the working precision. If each entry of $\mathbf{x}'$ is
$x_i + d_i$ with relative error at most $u \ge 0$, then
$\|\mathbf{x} + \mathbf{d} - \mathbf{x}'\| \le u \|\mathbf{x} + \mathbf{d}\|$. -/
theorem norm_add_sub_update_le {x d x' : Fin n → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (h : ∀ i, |x' i - (x i + d i)| ≤ u * |x i + d i|) :
    ‖WithLp.toLp 2 (x + d - x')‖ ≤ u * ‖WithLp.toLp 2 (x + d)‖ :=
  norm_toLp_sub_le_of_abs_sub_le hu h

end NLAlib.LinearSystems.Refinement.Rounded
