/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Moments

/-!
# Orthogonality to lower degrees

A real polynomial $p$ is orthogonal to the polynomials of degree less than $k$ in
$L^2(\mu)$ when $\int p\,r\,d\mu = 0$ for every real polynomial $r$ with $\deg r < k$. Monicity
and the degree of $p$ are separate hypotheses where a statement needs them; the predicate is the
hypothesis of Gauss quadrature (`NLAlib.Polynomial.Orthogonal.Gauss`) and the conclusion of the
Ritz-polynomial theorem of Lanczos quadrature. It depends on $\mu$ only through finitely many
moments.

A measure $\mu$ is positive definite on the polynomials of degree less than $k$ when every
nonzero such polynomial has positive $L^2(\mu)$ norm; this is the hypothesis of uniqueness of the
monic orthogonal polynomial, of the reality and simplicity of its zeros and of positive Gauss
weights.

## Main definitions

* `NLAlib.IsOrthogonalPolynomial`: orthogonality to every polynomial of degree less than $k$.
* `NLAlib.IsMomentPosDef`: positive definiteness on the polynomials of degree less than $k$.

## Main results

* `NLAlib.IsOrthogonalPolynomial.mono`: orthogonality to fewer degrees.
* `NLAlib.MatchesMoments.isOrthogonalPolynomial_iff`: orthogonality depends only on the moments.
* `NLAlib.IsMomentPosDef.mono`: definiteness up to a lower degree.
* `NLAlib.isMomentPosDef_iff_forall_finset`: for a finite measure carried by a bounded interval,
  definiteness counts support points.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- $p$ is **orthogonal to every polynomial of degree less than $k$** in $L^2(\mu)$:
$\int p\,r\,d\mu = 0$ for every real polynomial $r$ with $\deg r < k$. -/
def IsOrthogonalPolynomial (μ : Measure ℝ) (k : ℕ) (p : ℝ[X]) : Prop :=
  ∀ r : ℝ[X], r.degree < k → ∫ x, p.eval x * r.eval x ∂μ = 0

/-- The measure $\mu$ is **positive definite on the polynomials of degree less than $k$**:
$\int p^2\,d\mu > 0$ for every nonzero real polynomial $p$ with $\deg p < k$.
For a finite measure carried by a bounded interval, this is equivalent to positive definiteness
of the Hankel matrix $(\int x^{i+j}\,d\mu)_{i,j<k}$ and to having at least $k$ support points
(`isMomentPosDef_iff_forall_finset`). The definition accepts any measure, but a nonintegrable
Bochner integral is $0$, so the support interpretation needs the integrability hypotheses.
Vacuous at $k = 0$. For the degree-restricted inner product and its Hankel criterion, see
[Gautschi2004, Definition 1.1 and Theorem 1.2]. -/
def IsMomentPosDef (μ : Measure ℝ) (k : ℕ) : Prop :=
  ∀ p : ℝ[X], p ≠ 0 → p.degree < k → 0 < ∫ x, p.eval x ^ 2 ∂μ

/-- Orthogonality to the polynomials of degree less than $k$ gives orthogonality to those of
degree less than $j \le k$. -/
theorem IsOrthogonalPolynomial.mono {μ : Measure ℝ} {j k : ℕ} {p : ℝ[X]}
    (h : IsOrthogonalPolynomial μ k p) (hjk : j ≤ k) : IsOrthogonalPolynomial μ j p :=
  fun r hr => h r (hr.trans_le (by exact_mod_cast hjk))

/-- Orthogonality depends only on the moments: if $\mu$ and $\nu$ match their first $N$
moments and $\deg p + k \le N$, then $p$ is orthogonal to the polynomials of degree less than $k$
in $L^2(\mu)$ exactly when it is in $L^2(\nu)$. -/
theorem MatchesMoments.isOrthogonalPolynomial_iff {μ ν : Measure ℝ} {N k : ℕ} {p : ℝ[X]}
    (h : MatchesMoments μ ν N) (hN : p.natDegree + k ≤ N) :
    IsOrthogonalPolynomial μ k p ↔ IsOrthogonalPolynomial ν k p := by
  have key : ∀ r : ℝ[X], r.degree < k →
      ∫ x, p.eval x * r.eval x ∂μ = ∫ x, p.eval x * r.eval x ∂ν := by
    intro r hr
    simp_rw [← eval_mul]
    apply h
    by_cases hpr : p * r = 0
    · rw [hpr, degree_zero]
      exact WithBot.bot_lt_coe _
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hpr (mul_zero p)
    rw [degree_eq_natDegree hpr, Nat.cast_lt]
    have h1 := (natDegree_lt_iff_degree_lt hr0).mpr hr
    have h2 := natDegree_mul_le (p := p) (q := r)
    omega
  exact forall₂_congr fun r hr => by rw [key r hr]

/-- Positive definiteness on the polynomials of degree less than $k$ gives it on those of degree
less than $j \le k$. -/
theorem IsMomentPosDef.mono {μ : Measure ℝ} {j k : ℕ} (h : IsMomentPosDef μ k) (hjk : j ≤ k) :
    IsMomentPosDef μ j :=
  fun p hp hpdeg => h p hp (hpdeg.trans_le (by exact_mod_cast hjk))

/-- **Positive definiteness counts support points**: a finite measure $\mu$ supported in
$[a, b]$ is positive definite on the polynomials of degree less than $k$ exactly when no finite
set of fewer than $k$ points carries it: every finite $s$ with $x \in s$ for $\mu$-almost every
$x$ has $k \le \lvert s\rvert$. [Gautschi2004, §1.1]. -/
theorem isMomentPosDef_iff_forall_finset {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsMomentPosDef μ k ↔ ∀ s : Finset ℝ, (∀ᵐ x ∂μ, x ∈ s) → k ≤ s.card := by
  constructor
  · -- the nodal polynomial of a carrying set of fewer than `k` points has norm zero
    intro h s hs
    by_contra! hlt
    have hdeg : (Lagrange.nodal s id).degree < k := by
      rw [Lagrange.degree_nodal]
      exact_mod_cast hlt
    refine (h _ Lagrange.nodal_ne_zero hdeg).ne' ?_
    exact integral_eq_zero_of_ae <| hs.mono fun x hx =>
      (pow_eq_zero_iff two_ne_zero).mpr (Lagrange.eval_nodal_at_node (v := id) hx)
  · -- a polynomial of norm zero vanishes off its roots, which are fewer than `k`
    intro h p hp0 hpdeg
    refine (integral_nonneg fun x => sq_nonneg _).lt_of_ne' fun h0 => ?_
    have h1 := h _ <| (ae_eval_eq_zero_of_integral_sq_eq_zero hμ h0).mono fun x hx =>
      Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr hx)
    have h2 := (Multiset.toFinset_card_le p.roots).trans (card_roots' p)
    have h3 := (natDegree_lt_iff_degree_lt hp0).mpr hpdeg
    omega

end NLAlib
