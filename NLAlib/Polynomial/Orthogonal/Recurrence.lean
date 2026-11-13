/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import NLAlib.Polynomial.Orthogonal.Basic

/-!
# The three-term recurrence of orthogonal polynomials

The monic orthogonal polynomials $\pi_0, \pi_1, \dots$ of a measure $\mu$ on $\mathbb{R}$, defined
by the Stieltjes procedure: $\pi_0 = 1$, $\pi_1 = x - \alpha_0$ and
$$\pi_{k+2} = (x - \alpha_{k+1})\pi_{k+1} - \beta_{k+1}\pi_k\,,$$
with $\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$ and
$\beta_k = \int\pi_k^2\,d\mu/\int\pi_{k-1}^2\,d\mu$, $\beta_0 = \mu(\mathbb{R})$ (Gautschi's
convention). The recurrence is the definition, so it holds by `rfl`; orthogonality, uniqueness
and moment invariance are theorems. The definitions are total: a zero norm gives a zero
coefficient (Lean's $x/0 = 0$), and $\pi_k$ is monic of degree $k$ for every measure. For a
measure with $N$ support points, $\pi_N$ is then the nodal polynomial of the support and every
later $\pi_k$ a multiple of it (not proved here).

The Jacobi matrix of order $k$ carries $\alpha_0, \dots, \alpha_{k-1}$ on its diagonal and
$\sqrt{\beta_1}, \dots, \sqrt{\beta_{k-1}}$ beside it, in the layout of the Lanczos tridiagonal
matrix. [Gautschi2004]; [Szego1975].

## Main definitions

* `NLAlib.orthogonalPolynomial`: the monic orthogonal polynomials, by the Stieltjes recurrence.
* `NLAlib.jacobiAlpha`, `NLAlib.jacobiBeta`: the recurrence coefficients.
* `NLAlib.jacobiMatrix`: the Jacobi matrix.

## Main results

* `NLAlib.orthogonalPolynomial_add_two`: the three-term recurrence (by definition).
* `NLAlib.orthogonalPolynomial_zero`, `NLAlib.orthogonalPolynomial_one`,
  `NLAlib.jacobiBeta_zero`: the initial values.
* `NLAlib.monic_orthogonalPolynomial`, `NLAlib.natDegree_orthogonalPolynomial`: monic of
  degree $k$.
* `NLAlib.isOrthogonalPolynomial_orthogonalPolynomial`: existence of the orthogonal polynomials.
* `NLAlib.integral_orthogonalPolynomial_succ_sq`, `NLAlib.integral_orthogonalPolynomial_sq_eq_prod`:
  the norms.
* `NLAlib.isMomentPosDef_succ_iff`: definiteness is positivity of the last norm.
* `NLAlib.IsMomentPosDef.eq_orthogonalPolynomial`: uniqueness.
* `NLAlib.MatchesMoments.orthogonalPolynomial_eq`, `NLAlib.MatchesMoments.jacobiMatrix_eq`:
  moment invariance.
* `NLAlib.isHermitian_jacobiMatrix`: the Jacobi matrix is symmetric.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- The **monic orthogonal polynomials** of $\mu$, by the Stieltjes procedure:
$\pi_0 = 1$, $\pi_1 = x - \alpha_0$ and
$\pi_{k+2} = (x - \alpha_{k+1})\pi_{k+1} - \beta_{k+1}\pi_k$, with
$\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$ and
$\beta_k = \int\pi_k^2\,d\mu/\int\pi_{k-1}^2\,d\mu$ (`jacobiAlpha`, `jacobiBeta`).
$\pi_k$ is monic of degree $k$ for every $\mu$ and $k$. For a finite measure with compact support
it is orthogonal to every polynomial of degree less than $k$
(`isOrthogonalPolynomial_orthogonalPolynomial`), and it is the only monic such polynomial of
degree $k$ when $\mu$ is positive definite up to degree $k$
(`IsMomentPosDef.eq_orthogonalPolynomial`). Junk: a zero norm gives a zero coefficient
($x/0 = 0$); for a measure with $N$ support points, $\pi_N$ is then the nodal polynomial of the
support and every later $\pi_k$ a multiple of it (not proved here).
[Gautschi2004, Theorem 1.27]. -/
noncomputable def orthogonalPolynomial (μ : Measure ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - C ((∫ x, x * (1 : ℝ[X]).eval x ^ 2 ∂μ) / ∫ x, (1 : ℝ[X]).eval x ^ 2 ∂μ)
  | k + 2 =>
    (X - C ((∫ x, x * (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ)) * orthogonalPolynomial μ (k + 1) -
      C ((∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) * orthogonalPolynomial μ k

/-- The **diagonal recurrence coefficient** $\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$;
$0$ when $\pi_k$ has norm $0$. -/
noncomputable def jacobiAlpha (μ : Measure ℝ) (k : ℕ) : ℝ :=
  (∫ x, x * (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) /
    ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ

/-- The **off-diagonal recurrence coefficient** $\beta_k = \int\pi_k^2\,d\mu/
\int\pi_{k-1}^2\,d\mu$ for $k \ge 1$, and $\beta_0 = \mu(\mathbb{R})$ (Gautschi's convention);
$0$ when $\pi_{k-1}$ has norm $0$. The Jacobi matrix carries $\sqrt{\beta_k}$. -/
noncomputable def jacobiBeta (μ : Measure ℝ) : ℕ → ℝ
  | 0 => μ.real Set.univ
  | k + 1 => (∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
      ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ

/-- The **Jacobi matrix** of order $k$: $\alpha_0, \dots, \alpha_{k-1}$ on the diagonal,
$\sqrt{\beta_1}, \dots, \sqrt{\beta_{k-1}}$ beside it; the same layout as `lanczosTridiagonal`. -/
noncomputable def jacobiMatrix (μ : Measure ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then jacobiAlpha μ i
    else if (i : ℕ) = j + 1 then √(jacobiBeta μ i)
    else if (j : ℕ) = i + 1 then √(jacobiBeta μ j)
    else 0

/-- The orthogonal polynomial of degree $0$ is $\pi_0 = 1$, by definition. -/
theorem orthogonalPolynomial_zero (μ : Measure ℝ) : orthogonalPolynomial μ 0 = 1 := rfl

/-- The orthogonal polynomial of degree $1$ is $\pi_1 = x - \alpha_0$, by definition. -/
theorem orthogonalPolynomial_one (μ : Measure ℝ) :
    orthogonalPolynomial μ 1 = X - C (jacobiAlpha μ 0) := rfl

/-- **The three-term recurrence**: for every measure $\mu$ on $\mathbb{R}$ and every $k$,
$$\pi_{k+2} = (x - \alpha_{k+1})\pi_{k+1} - \beta_{k+1}\pi_k\,,$$
with $\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$ and
$\beta_k = \int\pi_k^2\,d\mu/\int\pi_{k-1}^2\,d\mu$ (zero when the denominator is).
[Gautschi2004, Theorem 1.27]; [Szego1975, Theorem 3.2.1]; there as a theorem
about the orthogonal polynomials, here the definition.
Result: orthogonal-polynomial-recurrence -/
theorem orthogonalPolynomial_add_two (μ : Measure ℝ) (k : ℕ) :
    orthogonalPolynomial μ (k + 2) =
      (X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1) -
        C (jacobiBeta μ (k + 1)) * orthogonalPolynomial μ k := rfl

/-- The first off-diagonal coefficient is the mass, $\beta_0 = \mu(\mathbb{R})$, by
definition. -/
theorem jacobiBeta_zero (μ : Measure ℝ) : jacobiBeta μ 0 = μ.real Set.univ := rfl

/-! ### Algebra and moment invariance (no support hypothesis) -/

section Algebra

variable {μ ν : Measure ℝ}

/-- Monicity and degree of $\pi_k$, proved together by two-step induction: the leading term
$(x - \alpha_{k+1})\pi_{k+1}$ is monic of degree $k + 2$ and $C(\beta_{k+1})\pi_k$ has degree
at most $k$. -/
private theorem monic_and_natDegree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).Monic ∧ (orthogonalPolynomial μ k).natDegree = k := by
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨monic_one, natDegree_one⟩
  | one =>
    rw [orthogonalPolynomial_one]
    exact ⟨monic_X_sub_C _, natDegree_X_sub_C _⟩
  | more k ih0 ih1 =>
    rw [orthogonalPolynomial_add_two]
    have hR : ((X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1)).natDegree =
        k + 2 := by
      rw [Monic.natDegree_mul' (monic_X_sub_C _) ih1.1.ne_zero, natDegree_X_sub_C, ih1.2]
      omega
    have hlt : (C (jacobiBeta μ (k + 1)) * orthogonalPolynomial μ k).natDegree <
        ((X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1)).natDegree := by
      rw [hR]
      exact ((natDegree_C_mul_le _ _).trans_eq ih0.2).trans_lt (by omega)
    exact ⟨((monic_X_sub_C _).mul ih1.1).sub_of_left (degree_lt_degree hlt),
      (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hR⟩

/-- The orthogonal polynomial $\pi_k$ of every measure $\mu$ on $\mathbb{R}$ is monic. -/
theorem monic_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) : (orthogonalPolynomial μ k).Monic :=
  (monic_and_natDegree_orthogonalPolynomial μ k).1

/-- The orthogonal polynomial $\pi_k$ of every measure $\mu$ on $\mathbb{R}$ has degree exactly
$k$. -/
theorem natDegree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).natDegree = k :=
  (monic_and_natDegree_orthogonalPolynomial μ k).2

/-- The orthogonal polynomial $\pi_k$ of every measure $\mu$ on $\mathbb{R}$ has degree $k$, as
`Polynomial.degree`. -/
theorem degree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).degree = k := by
  rw [degree_eq_natDegree (monic_orthogonalPolynomial μ k).ne_zero,
    natDegree_orthogonalPolynomial]

/-- $X\pi_k - \pi_{k+1}$ has degree at most $k$: both are monic of degree $k + 1$. -/
private theorem degree_X_mul_sub_orthogonalPolynomial_succ_lt (μ : Measure ℝ) (k : ℕ) :
    (X * orthogonalPolynomial μ k - orthogonalPolynomial μ (k + 1)).degree <
      ((k + 1 : ℕ) : WithBot ℕ) := by
  have hXm : (X * orthogonalPolynomial μ k).Monic := monic_X.mul (monic_orthogonalPolynomial μ k)
  have hXd : (X * orthogonalPolynomial μ k).degree = ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_X, degree_orthogonalPolynomial]; norm_cast; omega
  exact hXd ▸ degree_sub_lt_left (by rw [hXd, degree_orthogonalPolynomial]) hXm.ne_zero
    (by rw [hXm.leadingCoeff, (monic_orthogonalPolynomial μ _).leadingCoeff])

/-- The off-diagonal recurrence coefficients are nonnegative: $\beta_k \ge 0$ for every measure
$\mu$ on $\mathbb{R}$ and every $k$. -/
theorem jacobiBeta_nonneg (μ : Measure ℝ) (k : ℕ) : 0 ≤ jacobiBeta μ k := by
  cases k with
  | zero =>
      change 0 ≤ μ.real Set.univ
      exact measureReal_nonneg
  | succ k =>
      change 0 ≤ (∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ
      exact div_nonneg (integral_nonneg fun x => sq_nonneg _)
        (integral_nonneg fun x => sq_nonneg _)

/-- Matching moments transfer the squared norm of $\pi_j(\mu)$, a polynomial of degree $2j$. -/
private theorem MatchesMoments.integral_orthogonalPolynomial_sq_eq {N j : ℕ}
    (h : MatchesMoments μ ν N) (hj : 2 * j < N) :
    ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ =
      ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂ν := by
  have hsq := h (orthogonalPolynomial μ j ^ 2) (by
    rw [degree_eq_natDegree ((monic_orthogonalPolynomial μ j).pow 2).ne_zero, natDegree_pow,
      natDegree_orthogonalPolynomial]
    exact_mod_cast hj)
  simpa only [eval_pow] using hsq

/-- If $\pi_j(\mu) = \pi_j(\nu)$ and the first $2j + 2$ moments match, then
$\alpha_j(\mu) = \alpha_j(\nu)$: both integrals are of polynomials of degree at most $2j + 1$. -/
private theorem MatchesMoments.jacobiAlpha_eq_of_eq {N j : ℕ} (h : MatchesMoments μ ν N)
    (hj : 2 * j + 1 < N) (hp : orthogonalPolynomial μ j = orthogonalPolynomial ν j) :
    jacobiAlpha μ j = jacobiAlpha ν j := by
  have hm := (monic_orthogonalPolynomial μ j).pow 2
  have hx := h (X * orthogonalPolynomial μ j ^ 2) (by
    rw [degree_eq_natDegree (monic_X.mul hm).ne_zero, monic_X.natDegree_mul hm, natDegree_X,
      natDegree_pow, natDegree_orthogonalPolynomial]
    exact_mod_cast (by omega : 1 + 2 * j < N))
  simp only [eval_mul, eval_X, eval_pow] at hx
  rw [jacobiAlpha, jacobiAlpha, ← hp, hx, h.integral_orthogonalPolynomial_sq_eq (by omega)]

/-- If $\pi_{j+1}$ and $\pi_j$ of $\mu$ and $\nu$ agree and the first $2j + 3$ moments match,
then $\beta_{j+1}(\mu) = \beta_{j+1}(\nu)$. -/
private theorem MatchesMoments.jacobiBeta_succ_eq_of_eq {N j : ℕ} (h : MatchesMoments μ ν N)
    (hj : 2 * (j + 1) < N) (hp1 : orthogonalPolynomial μ (j + 1) = orthogonalPolynomial ν (j + 1))
    (hp : orthogonalPolynomial μ j = orthogonalPolynomial ν j) :
    jacobiBeta μ (j + 1) = jacobiBeta ν (j + 1) := by
  simp only [jacobiBeta]
  rw [← hp1, ← hp, h.integral_orthogonalPolynomial_sq_eq hj,
    h.integral_orthogonalPolynomial_sq_eq (by omega)]

/-- The orthogonal polynomial depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k$ moments, then $\pi_k(\mu) = \pi_k(\nu)$. No support
hypothesis: $\pi_k$ is a formula in integrals of polynomials of degree less than $2k$. -/
theorem MatchesMoments.orthogonalPolynomial_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k)) :
    orthogonalPolynomial μ k = orthogonalPolynomial ν k := by
  revert h
  induction k using Nat.twoStepInduction with
  | zero => intro _; rfl
  | one =>
    intro h
    rw [orthogonalPolynomial_one, orthogonalPolynomial_one, h.jacobiAlpha_eq_of_eq (by omega) rfl]
  | more n ihn ih1 =>
    intro h
    have hp := ihn (h.mono (by omega))
    have hp1 := ih1 (h.mono (by omega))
    rw [orthogonalPolynomial_add_two μ n, orthogonalPolynomial_add_two ν n,
      h.jacobiAlpha_eq_of_eq (by omega) hp1, h.jacobiBeta_succ_eq_of_eq (by omega) hp1 hp, hp1, hp]

/-- The diagonal coefficient depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k + 2$ moments, then $\alpha_k(\mu) = \alpha_k(\nu)$. -/
theorem MatchesMoments.jacobiAlpha_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 2)) :
    jacobiAlpha μ k = jacobiAlpha ν k :=
  h.jacobiAlpha_eq_of_eq (by omega) (MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega)))

/-- The off-diagonal coefficient depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k + 1$ moments, then $\beta_k(\mu) = \beta_k(\nu)$. -/
theorem MatchesMoments.jacobiBeta_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 1)) :
    jacobiBeta μ k = jacobiBeta ν k := by
  rcases k with _ | k
  · exact h.measureReal_univ_eq (by omega)
  · exact h.jacobiBeta_succ_eq_of_eq (by omega)
      (MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega)))
      (MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega)))

/-- The Jacobi matrix depends only on the moments: if two measures $\mu$, $\nu$ on $\mathbb{R}$
match their first $2k$ moments, then $\mathbf{J}_k(\mu) = \mathbf{J}_k(\nu)$. -/
theorem MatchesMoments.jacobiMatrix_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k)) :
    jacobiMatrix μ k = jacobiMatrix ν k := by
  ext i j
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · exact MatchesMoments.jacobiAlpha_eq (h.mono (by omega))
  · rw [MatchesMoments.jacobiBeta_eq (h.mono (by omega))]
  · rw [MatchesMoments.jacobiBeta_eq (h.mono (by omega))]
  · rfl

/-- The Jacobi matrix $\mathbf{J}_k(\mu)$ of every measure $\mu$ on $\mathbb{R}$ is symmetric. -/
theorem isHermitian_jacobiMatrix (μ : Measure ℝ) (k : ℕ) : (jacobiMatrix μ k).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  rcases eq_or_ne i j with rfl | h
  · rfl
  simp only [jacobiMatrix, Matrix.of_apply, star_trivial, h, h.symm, if_false]
  split_ifs <;> first | omega | rfl

end Algebra

/-! ### Orthogonality, norms and uniqueness -/

section Orthogonality

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- A polynomial multiple of a polynomial of norm zero has norm zero: for a finite measure $\mu$
supported in $[a, b]$, a real polynomial $p$ with $\int p^2\,d\mu = 0$ and every real polynomial
$q$, $\int (qp)^2\,d\mu = 0$. The degenerate branch of the norm recurrence. -/
private theorem integral_eval_mul_sq_eq_zero_of_integral_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p q : ℝ[X]}
    (hp : ∫ x, p.eval x ^ 2 ∂μ = 0) : ∫ x, (q * p).eval x ^ 2 ∂μ = 0 := by
  have he : ∀ x, (q * p).eval x ^ 2 = p.eval x * (q ^ 2 * p).eval x := by
    intro x
    simp only [eval_mul, eval_pow]
    ring
  simp only [he]
  exact integral_eval_mul_eq_zero_of_integral_sq_eq_zero hμ hp (q ^ 2 * p)

/-- The norm recurrence: for a finite measure $\mu$ supported in $[a, b]$ and every $k$,
$\|\pi_{k+1}\|^2 = \beta_{k+1}\|\pi_k\|^2$ in $L^2(\mu)$, also when $\|\pi_k\| = 0$.
[Gautschi2004, Theorem 1.27, (1.3.4)], in the positive-norm range. -/
theorem integral_orthogonalPolynomial_succ_sq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ =
      jacobiBeta μ (k + 1) * ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ := by
  rcases eq_or_ne (∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) 0 with h0 | h0
  · -- degenerate: $\|\pi_k\|^2 = 0$ gives $\beta_{k+1} = 0$ and $\pi_{k+1} = (X - \alpha_k)\pi_k$
    have hb : jacobiBeta μ (k + 1) = 0 := by
      simp only [jacobiBeta]
      rw [h0, div_zero]
    rw [hb, zero_mul]
    have hp : orthogonalPolynomial μ (k + 1) =
        (X - C (jacobiAlpha μ k)) * orthogonalPolynomial μ k := by
      cases k with
      | zero => rw [orthogonalPolynomial_one, orthogonalPolynomial_zero, mul_one]
      | succ j =>
          have hbj : jacobiBeta μ (j + 1) = 0 := by
            simp only [jacobiBeta]
            rw [h0, zero_div]
          rw [orthogonalPolynomial_add_two μ j]
          simp only [hbj, Polynomial.C_0, zero_mul, sub_zero]
    rw [hp]
    exact integral_eval_mul_sq_eq_zero_of_integral_sq_eq_zero hμ h0
  · rw [jacobiBeta, div_mul_cancel₀ _ h0]

/-- The defining property of $\alpha_k$: for a finite measure $\mu$ supported in $[a, b]$ and
every $k$, $\int(x - \alpha_k)\pi_k(x)^2\,d\mu = 0$, also when $\|\pi_k\| = 0$ ($x/0 = 0$). -/
theorem integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (x - jacobiAlpha μ k) * (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = 0 := by
  set π := orthogonalPolynomial μ k
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have hx : ∀ x, x * π.eval x ^ 2 = π.eval x * (X * π).eval x := fun x => by
    simp only [eval_mul, eval_X]
    ring
  have himul : Integrable (fun x => x * π.eval x ^ 2) μ :=
    (hint (π * (X * π))).congr (ae_of_all μ fun x => by simp only [hx, eval_mul])
  have hisq : Integrable (fun x => π.eval x ^ 2) μ :=
    (hint (π ^ 2)).congr (ae_of_all μ fun _ => eval_pow 2)
  simp only [sub_mul]
  rw [integral_sub himul (hisq.const_mul _), integral_const_mul]
  rcases eq_or_ne (∫ x, π.eval x ^ 2 ∂μ) 0 with hD | hD
  · -- degenerate case: the norm is $0$, so both integrals vanish
    rw [hD, mul_zero, sub_zero, integral_congr_ae (ae_of_all μ hx)]
    exact integral_eval_mul_eq_zero_of_integral_sq_eq_zero hμ hD _
  · rw [jacobiAlpha, div_mul_cancel₀ _ hD, sub_self]

/-- Step (a) of the orthogonality induction: if $\pi_{k+1}$ and $\pi_k$ are orthogonal to the
lower degrees, then $\pi_{k+2}$ is orthogonal to every polynomial of degree less than $k$. -/
private theorem integral_orthogonalPolynomial_add_two_mul_eq_zero_of_degree_lt
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1)))
    (h0 : IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k)) {r : ℝ[X]} (hr : r.degree < k) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * r.eval x ∂μ = 0 := by
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have hXr : (X * r).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
    by_cases hr0 : r = 0
    · subst hr0; simp
    · have hnr : r.natDegree < k := (natDegree_lt_iff_degree_lt hr0).mpr hr
      rw [← natDegree_lt_iff_degree_lt (mul_ne_zero X_ne_zero hr0), natDegree_X_mul hr0]
      omega
  have hpoly : ∀ x : ℝ, (orthogonalPolynomial μ (k + 2)).eval x * r.eval x =
      (orthogonalPolynomial μ (k + 1) * (X * r) -
        C (jacobiAlpha μ (k + 1)) * (orthogonalPolynomial μ (k + 1) * r) -
        C (jacobiBeta μ (k + 1)) * (orthogonalPolynomial μ k * r)).eval x := by
    intro x
    rw [orthogonalPolynomial_add_two]
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_mul]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly)]
  simp only [eval_sub]
  rw [integral_sub, integral_sub]
  · have hX := h1 _ hXr
    simp only [eval_mul, eval_C, integral_const_mul] at hX ⊢
    rw [hX, h1 r (hr.trans_le (by exact_mod_cast k.le_succ)), h0 r hr]
    ring
  all_goals fun_prop

/-- Step (b) of the orthogonality induction: if $\pi_{k+1}$ is orthogonal to the lower degrees,
then $\int\pi_{k+2}\pi_{k+1}\,d\mu = 0$. -/
private theorem integral_orthogonalPolynomial_add_two_mul_succ
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1))) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ (k + 1)).eval x ∂μ =
      0 := by
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have key : ∀ x : ℝ,
      (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ (k + 1)).eval x =
      ((X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1) ^ 2 -
        C (jacobiBeta μ (k + 1)) *
          (orthogonalPolynomial μ (k + 1) * orthogonalPolynomial μ k)).eval x := by
    intro x
    rw [orthogonalPolynomial_add_two]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [integral_congr_ae (ae_of_all μ key)]
  simp only [eval_sub]
  rw [integral_sub (hint _) (hint _)]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, integral_const_mul]
  rw [integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero hμ (k + 1),
    h1 _ (by rw [degree_orthogonalPolynomial]; exact_mod_cast k.lt_succ_self), mul_zero, sub_zero]

/-- Step (c) of the orthogonality induction: if $\pi_{k+1}$ is orthogonal to the lower degrees,
then $\int\pi_{k+2}\pi_k\,d\mu = 0$. -/
private theorem integral_orthogonalPolynomial_add_two_mul_self
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1))) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ k).eval x ∂μ = 0 := by
  set P := orthogonalPolynomial μ
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have hpoly : ∀ x, (P (k + 2)).eval x * (P k).eval x =
      (P (k + 1) * (X * P k - P (k + 1)) + P (k + 1) ^ 2 -
        C (jacobiAlpha μ (k + 1)) * (P (k + 1) * P k) -
        C (jacobiBeta μ (k + 1)) * P k ^ 2).eval x := by
    intro x
    rw [show P (k + 2) = _ from orthogonalPolynomial_add_two μ k]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly)]
  simp only [eval_add, eval_sub]
  rw [integral_sub, integral_sub, integral_add]
  · simp only [eval_mul, eval_pow, eval_C, integral_const_mul]
    rw [h1 _ (degree_X_mul_sub_orthogonalPolynomial_succ_lt μ k),
      h1 (P k) (by rw [degree_orthogonalPolynomial]; exact_mod_cast k.lt_succ_self),
      integral_orthogonalPolynomial_succ_sq hμ k]
    ring
  all_goals fun_prop

/-- Division by a monic polynomial, one degree at a time: if $p$ is monic of degree $d$ and
$\deg r < d + 1$, then $r = c\,p + r'$ for a constant $c$ with $\deg r' < d$. -/
private theorem exists_eq_C_mul_add_of_degree_lt {d : ℕ} {p r : ℝ[X]} (hp : p.Monic)
    (hpd : p.degree = (d : WithBot ℕ)) (hr : r.degree < (d + 1 : WithBot ℕ)) :
    ∃ (c : ℝ) (r' : ℝ[X]), r = C c * p + r' ∧ r'.degree < (d : WithBot ℕ) := by
  have hn : (r /ₘ p).natDegree = 0 := by
    rw [natDegree_divByMonic r hp, natDegree_eq_of_degree_eq_some hpd]
    have : r.natDegree ≤ d := natDegree_le_iff_degree_le.mpr (Order.lt_succ_iff.mp hr)
    omega
  refine ⟨(r /ₘ p).coeff 0, r %ₘ p, ?_, hpd ▸ degree_modByMonic_lt r hp⟩
  rw [← eq_C_of_natDegree_eq_zero hn, mul_comm, add_comm, modByMonic_add_div r p]

/-- Step (d) of the orthogonality induction: if $\pi_{k+1}$ and $\pi_k$ are orthogonal to the
lower degrees, so is $\pi_{k+2}$. -/
private theorem isOrthogonalPolynomial_orthogonalPolynomial_add_two
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1)))
    (h0 : IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k)) :
    IsOrthogonalPolynomial μ (k + 2) (orthogonalPolynomial μ (k + 2)) := by
  intro r hr
  -- split off the multiples of $\pi_{k+1}$ and of $\pi_k$: $r = c_1\pi_{k+1} + c_0\pi_k + r_0$
  obtain ⟨c₁, r₁, hr₁, hdeg₁⟩ := exists_eq_C_mul_add_of_degree_lt
    (monic_orthogonalPolynomial μ (k + 1)) (degree_orthogonalPolynomial μ (k + 1)) hr
  obtain ⟨c₀, r₀, hr₀, hdeg₀⟩ := exists_eq_C_mul_add_of_degree_lt
    (monic_orthogonalPolynomial μ k) (degree_orthogonalPolynomial μ k) hdeg₁
  have hint := integrable_eval_of_ae_mem_Icc hμ
  set P := orthogonalPolynomial μ
  have hsplit : ∀ x, (P (k + 2)).eval x * r.eval x =
      (C c₁ * (P (k + 2) * P (k + 1)) + C c₀ * (P (k + 2) * P k) + P (k + 2) * r₀).eval x := by
    intro x
    rw [hr₁, hr₀]
    simp only [eval_add, eval_mul, eval_C]
    ring
  rw [integral_congr_ae (ae_of_all μ hsplit)]
  simp only [eval_add]
  rw [integral_add, integral_add]
  · -- steps (a), (b) and (c)
    simp only [eval_mul, eval_C, integral_const_mul]
    rw [integral_orthogonalPolynomial_add_two_mul_succ hμ h1,
      integral_orthogonalPolynomial_add_two_mul_self hμ h1,
      integral_orthogonalPolynomial_add_two_mul_eq_zero_of_degree_lt hμ h1 h0 hdeg₀]
    ring
  all_goals fun_prop

/-- **Existence of the orthogonal polynomials**: for a finite measure $\mu$ supported in
$[a, b]$ and every $k$, the monic polynomial $\pi_k$ of degree $k$ is orthogonal in $L^2(\mu)$
to every real polynomial of degree less than $k$. No nondegeneracy is needed: past the number of
support points, $\pi_k$ vanishes on the support. [Gautschi2004, Theorems 1.6 and 1.7] gives the
positive-definite and finite-degree cases.
Theorem 1.27 gives the recurrence on its nondegenerate range.
Result: orthogonal-polynomial-existence -/
theorem isOrthogonalPolynomial_orthogonalPolynomial (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k) := by
  induction k using Nat.twoStepInduction with
  | zero =>
    intro r hr
    rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hr
    simp only [hr, eval_zero, mul_zero, integral_zero]
  | one =>
    intro r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · simp only [eval_zero, mul_zero, integral_zero]
    · have hrC : r = Polynomial.C (r.coeff 0) :=
        Polynomial.eq_C_of_natDegree_le_zero
          (Nat.lt_one_iff.mp ((Polynomial.natDegree_lt_iff_degree_lt (n := 1) hr0).mpr hr)).le
      rw [hrC, orthogonalPolynomial_one]
      simp only [eval_sub, eval_X, eval_C]
      have h := integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero hμ 0
      rw [orthogonalPolynomial_zero] at h
      simp only [Polynomial.eval_one, one_pow, mul_one] at h
      rw [integral_mul_const _ _, h, zero_mul]
  | more _ h0 h1 =>
    exact isOrthogonalPolynomial_orthogonalPolynomial_add_two hμ h1 h0

/-- The norms as products of the coefficients: for a finite measure $\mu$ supported in $[a, b]$
and every $k$, $\|\pi_k\|^2 = \beta_0\beta_1\cdots\beta_k$ in $L^2(\mu)$, with
$\beta_0 = \mu(\mathbb{R})$. [Gautschi2004, Theorem 1.27, (1.3.4)], in the positive-norm range. -/
theorem integral_orthogonalPolynomial_sq_eq_prod (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = ∏ i ∈ Finset.range (k + 1), jacobiBeta μ i := by
  induction k with
  | zero =>
    simp only [orthogonalPolynomial_zero, eval_one, one_pow, integral_const, jacobiBeta_zero,
      Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, smul_eq_mul, mul_one]
  | succ k ih =>
    rw [integral_orthogonalPolynomial_succ_sq hμ k, Finset.prod_range_succ, ih, mul_comm]

/-- The off-diagonal entry as an integral: for a finite measure $\mu$ supported in $[a, b]$ and
every $k$, $\int x\,\pi_k(x)\pi_{k+1}(x)\,d\mu = \|\pi_{k+1}\|^2$, since
$x\pi_k = \pi_{k+1} + {}$(lower degree). -/
theorem integral_mul_orthogonalPolynomial_mul_orthogonalPolynomial_succ
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, x * (orthogonalPolynomial μ k).eval x * (orthogonalPolynomial μ (k + 1)).eval x ∂μ =
      ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ := by
  have hint := integrable_eval_of_ae_mem_Icc hμ
  set P := orthogonalPolynomial μ
  have hpoly : ∀ x, x * (P k).eval x * (P (k + 1)).eval x =
      (P (k + 1) * (X * P k - P (k + 1)) + P (k + 1) ^ 2).eval x := by
    intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly)]
  simp only [eval_add]
  rw [integral_add (hint _) (hint _)]
  simp only [eval_mul, eval_pow]
  rw [isOrthogonalPolynomial_orthogonalPolynomial hμ (k + 1) _
    (degree_X_mul_sub_orthogonalPolynomial_succ_lt μ k), zero_add]

/-- Definiteness is positivity of the last norm: a finite measure $\mu$ supported in $[a, b]$ is
positive definite on the polynomials of degree at most $k$ exactly when
$\int\pi_k^2\,d\mu > 0$ (the norms vanish from the first zero one on). -/
theorem isMomentPosDef_succ_iff (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsMomentPosDef μ (k + 1) ↔ 0 < ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ := by
  refine ⟨fun h => h _ (monic_orthogonalPolynomial μ k).ne_zero ?_, fun hpos p hp0 hpdeg => ?_⟩
  · rw [degree_orthogonalPolynomial]
    exact_mod_cast k.lt_succ_self
  have hint := integrable_eval_of_ae_mem_Icc hμ
  -- the norms of $\pi_j$, $j \le k$, are positive, as $\|\pi_{j+1}\|^2 = \beta_{j+1}\|\pi_j\|^2$
  have hlow : ∀ j ≤ k, 0 < ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ := fun j hj =>
    Nat.decreasingInduction (motive := fun j _ => 0 < ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ)
      (fun j _ ih => pos_of_mul_pos_right (integral_orthogonalPolynomial_succ_sq hμ j ▸ ih)
        (jacobiBeta_nonneg μ (j + 1))) hpos hj
  -- $p = c\,\pi_n + r$ with $n = \deg p$, $c$ the leading coefficient and $\deg r < n$
  set π := orthogonalPolynomial μ p.natDegree
  set c := p.leadingCoeff
  set r := p - C c * π
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hrdeg : r.degree < p.natDegree := by
    rw [← degree_eq_natDegree hp0]
    refine degree_sub_lt_left ?_ hp0 ?_
    · rw [degree_C_mul hc, degree_orthogonalPolynomial, degree_eq_natDegree hp0]
    · rw [leadingCoeff_mul, leadingCoeff_C, (monic_orthogonalPolynomial μ _).leadingCoeff, mul_one]
  have hpoly : ∀ x, p.eval x ^ 2 = (C (c ^ 2) * π ^ 2 + C (2 * c) * (π * r) + r ^ 2).eval x := by
    intro x
    simp only [r, eval_add, eval_sub, eval_mul, eval_pow, eval_C]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly)]
  simp only [eval_add]
  rw [integral_add, integral_add]
  · simp only [eval_mul, eval_pow, eval_C, integral_const_mul]
    rw [isOrthogonalPolynomial_orthogonalPolynomial hμ _ r hrdeg, mul_zero, add_zero]
    have hdk : p.natDegree ≤ k := Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hp0).mpr hpdeg)
    exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) (hlow _ hdk))
      (integral_nonneg fun x => sq_nonneg _)
  all_goals fun_prop

/-- **Uniqueness of the monic orthogonal polynomial**: if a finite measure $\mu$ supported in
$[a, b]$ is positive definite on the polynomials of degree less than $k$, then every monic real
polynomial $p$ of degree $k$ orthogonal in $L^2(\mu)$ to the polynomials of degree less than $k$
is $\pi_k$. [Gautschi2004, Theorem 1.6]. -/
theorem IsMomentPosDef.eq_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : p.Monic) (hpk : p.natDegree = k)
    (hpo : IsOrthogonalPolynomial μ k p) : p = orthogonalPolynomial μ k := by
  set π := orthogonalPolynomial μ k
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have hdeg : (p - π).degree < k := by
    have h1 : p.degree = k := by rw [degree_eq_natDegree hp.ne_zero, hpk]
    exact h1 ▸ degree_sub_lt_left (by rw [h1, degree_orthogonalPolynomial]) hp.ne_zero
      (by rw [hp.leadingCoeff, (monic_orthogonalPolynomial μ k).leadingCoeff])
  by_contra hne
  refine (h _ (sub_ne_zero.mpr hne) hdeg).ne' ?_
  calc ∫ x, (p - π).eval x ^ 2 ∂μ
      = ∫ x, p.eval x * (p - π).eval x - π.eval x * (p - π).eval x ∂μ := by
        congr 1; ext x; simp only [eval_sub]; ring
    _ = 0 := by
        rw [integral_sub (by simpa only [eval_mul] using hint (p * (p - π)))
          (by simpa only [eval_mul] using hint (π * (p - π))),
          hpo _ hdeg, isOrthogonalPolynomial_orthogonalPolynomial hμ k _ hdeg, sub_zero]

end Orthogonality

end NLAlib
