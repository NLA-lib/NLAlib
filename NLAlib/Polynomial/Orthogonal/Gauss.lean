/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Polynomial.Orthogonal.Basic
public import NLAlib.Polynomial.Orthogonal.Zeros
public import NLAlib.Polynomial.Approximation.Jackson
public import NLAlib.Polynomial.Approximation.MinimaxError
public import NLAlib.Polynomial.Interpolation.Hermite
public import NLAlib.ForMathlib.MeasureTheory.Integral.MeanValue

/-!
# Gauss quadrature

The interpolatory quadrature rule of a measure $\mu$ at distinct nodes $s \subseteq \mathbb{R}$
puts at each node $x$ the weight $\int\ell_x\,d\mu$, $\ell_x$ the Lagrange basis polynomial of
$x$ (Mathlib's `Lagrange.basis s id x`); it integrates every polynomial of degree less than
$\lvert s\rvert$ exactly. When the nodal polynomial $\pi_s(z) = \prod_{x\in s}(z - x)$ is
orthogonal to the polynomials of degree less than $\lvert s\rvert$ (the nodes are the zeros of
the degree-$\lvert s\rvert$ orthogonal polynomial of $\mu$), it is the Gauss rule: its weights
are nonnegative, $\int\ell_x\,d\mu = \int\ell_x^2\,d\mu$, and it integrates every polynomial of
degree less than $2\lvert s\rvert$ exactly, so it matches the first $2\lvert s\rvert$ moments of
$\mu$.

The canonical $k$-point Gauss rule of $\mu$, `gaussQuadrature μ k`, is the interpolatory rule at
the Gauss nodes `gaussNodes μ k`, the distinct real zeros of the monic orthogonal polynomial
`orthogonalPolynomial μ k` (`NLAlib.Polynomial.Orthogonal.Zeros`). It is defined for every
measure and every $k$; past the number of support points of $\mu$ it is $\mu$ itself. For
spectral measures the Ritz values of the Lanczos method are Gauss nodes
(`NLAlib.HasOrthonormalCols.isOrthogonalPolynomial_nodal`).

For $f$ continuous on $[a, b]$ and $C^{2k}$ on $(a, b)$ the $k$-point Gauss rule has the
remainder
$$\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k) =
\frac{f^{(2k)}(\xi)}{(2k)!}\int\pi_k^2\,d\mu\,,\qquad \xi \in (a, b)\,,$$
so it is a lower bound when $f^{(2k)} \ge 0$ and an upper bound when $f^{(2k)} \le 0$.

## Main definitions

* `NLAlib.interpolatoryQuadrature`: the interpolatory rule as a measure.
* `NLAlib.gaussQuadrature`: the canonical Gauss rule of a measure.

## Main results

* `NLAlib.integral_eval_eq_sum_of_degree_lt`: interpolatory quadrature is exact below the number
  of nodes.
* `NLAlib.IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add`: the exactness
  degree of an interpolatory rule.
* `NLAlib.IsOrthogonalPolynomial.integral_eval_eq_sum`: Gauss quadrature is exact through degree
  $2\lvert s\rvert - 1$.
* `NLAlib.IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq`: the weights are
  nonnegative.
* `NLAlib.IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature`: the rule matches
  $2\lvert s\rvert$ moments.
* `NLAlib.integral_gaussQuadrature_eq_sum`, `NLAlib.integral_gaussQuadrature`: the rule as a
  finite sum, in both weight forms.
* `NLAlib.matchesMoments_gaussQuadrature`: Gauss quadrature, for every $k$.
* `NLAlib.ae_mem_Icc_gaussQuadrature`, `NLAlib.gaussQuadrature_real_univ`: support and mass.
* `NLAlib.gaussQuadrature_real_singleton`: the mass at a node is $\int\ell_x\,d\mu$.
* `NLAlib.IsMomentPosDef.gaussQuadrature_real_singleton_pos`: positive weights.
* `NLAlib.MatchesMoments.eq_gaussQuadrature`: uniqueness of the Gauss rule.
* `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn`,
  `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith`: error bounds.
* `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_continuousOn`: the bound
  $2E_{2k + 1}(f)\mu(\mathbb{R})$.
* `NLAlib.gaussQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`: the terminating
  case.
* `NLAlib.exists_integral_sub_integral_eval_eq`: the mean-value step shared by the Gauss, Radau
  and Lobatto remainders.
* `NLAlib.exists_integral_sub_integral_gaussQuadrature_eq`: the Gauss remainder.
* `NLAlib.integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg`,
  `NLAlib.integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos`: one-sided bounds.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped NNReal

namespace NLAlib

/-- The **interpolatory quadrature rule** of $\mu$ at the nodes $s$, as a measure: weight
$\int \ell_x\,d\mu$ at each node $x$, $\ell_x$ the Lagrange basis polynomial. At Gauss nodes the
weights are nonnegative (`IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq`), and the
rule is the Gauss rule. Junk: negative weights are truncated at $0$, so at nodes that are not
Gauss nodes the measure need not be the interpolatory rule. -/
noncomputable def interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) : Measure ℝ :=
  ∑ x ∈ s, ENNReal.ofReal (∫ t, (Lagrange.basis s id x).eval t ∂μ) • Measure.dirac x

/-- An interpolatory quadrature rule is a finite measure. -/
instance isFiniteMeasure_interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) :
    IsFiniteMeasure (interpolatoryQuadrature μ s) := by
  unfold interpolatoryQuadrature
  have : ∀ x : ℝ, IsFiniteMeasure (ENNReal.ofReal (∫ t, (Lagrange.basis s id x).eval t ∂μ) •
      Measure.dirac x) := fun x => Measure.smul_finite _ ENNReal.ofReal_ne_top
  infer_instance

/-- Interpolatory quadrature is exact below the number of nodes: for a finite measure $\mu$
supported in $[a, b]$, distinct real nodes $s$ and a real polynomial $r$ of degree less than
$\lvert s\rvert$,
$$\int r\,d\mu = \sum_{x\in s}\Bigl(\int\ell_x\,d\mu\Bigr)r(x)\,,$$
$\ell_x$ the Lagrange basis polynomial of $x$: $r$ is its own Lagrange interpolant. -/
theorem integral_eval_eq_sum_of_degree_lt {μ : Measure ℝ} {s : Finset ℝ}
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {r : ℝ[X]}
    (hr : r.degree < s.card) :
    ∫ x, r.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * r.eval x := by
  have hint : ∀ x ∈ s, Integrable (fun t => r.eval x * (Lagrange.basis s id x).eval t) μ :=
    fun x _ => (integrable_eval_of_ae_mem_Icc hμ _).const_mul _
  have hr' := Lagrange.eq_interpolate (v := id) (Set.injOn_id _) hr
  rw [Lagrange.interpolate_apply] at hr'
  calc ∫ x, r.eval x ∂μ
      = ∫ t, ∑ x ∈ s, r.eval x * (Lagrange.basis s id x).eval t ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        dsimp only
        conv_lhs => rw [hr']
        simp only [eval_finsetSum, eval_mul, eval_C, id]
    _ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * r.eval x := by
        rw [integral_finsetSum _ hint]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [integral_const_mul, mul_comm]

/-- **The exactness degree of an interpolatory rule**: if the nodal polynomial of distinct real
nodes $s$ is orthogonal in $L^2(\mu)$ to the polynomials of degree less than $m$, for a finite
measure $\mu$ supported in $[a, b]$, then
$$\int p\,d\mu = \sum_{x\in s}\Bigl(\int\ell_x\,d\mu\Bigr)p(x)$$
for every real polynomial $p$ of degree less than $\lvert s\rvert + m$, $\ell_x$ the Lagrange
basis polynomial of $x$. [Gautschi2004, Theorem 1.45]; there as an
equivalence for $m \le \lvert s\rvert$; here the direction used, for every $m$. -/
theorem IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add {μ : Measure ℝ}
    {s : Finset ℝ} {m : ℕ} (hs : IsOrthogonalPolynomial μ m (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]}
    (hp : p.degree < (s.card + m : ℕ)) :
    ∫ x, p.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x := by
  set w := Lagrange.nodal s id with hwdef
  have hw : w.Monic := Lagrange.nodal_monic
  have hsplit := modByMonic_add_div p w
  have hmod : (p %ₘ w).degree < s.card := by
    have := degree_modByMonic_lt p hw
    rwa [Lagrange.degree_nodal] at this
  have hdiv : (p /ₘ w).degree < m := by
    by_cases hq : p /ₘ w = 0
    · rw [hq, degree_zero]
      exact WithBot.bot_lt_coe _
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hq (zero_divByMonic w)
    have hle : w.degree ≤ p.degree :=
      not_lt.mp fun h => hq ((divByMonic_eq_zero_iff hw).mpr h)
    have hle' : s.card ≤ p.natDegree := by
      have := natDegree_le_natDegree hle
      rwa [Lagrange.natDegree_nodal] at this
    rw [degree_eq_natDegree hq, Nat.cast_lt, natDegree_divByMonic p hw, Lagrange.natDegree_nodal]
    rw [degree_eq_natDegree hp0] at hp
    have : p.natDegree < s.card + m := by exact_mod_cast hp
    omega
  have hint1 := integrable_eval_of_ae_mem_Icc hμ (p %ₘ w)
  have hint2 := integrable_eval_of_ae_mem_Icc hμ (w * (p /ₘ w))
  calc ∫ x, p.eval x ∂μ = ∫ x, ((p %ₘ w).eval x + (w * (p /ₘ w)).eval x) ∂μ := by
        conv_lhs => rw [← hsplit]
        simp only [eval_add]
    _ = ∫ x, (p %ₘ w).eval x ∂μ := by
        rw [integral_add hint1 hint2]
        simp only [eval_mul]
        rw [hs _ hdiv, add_zero]
    _ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * (p %ₘ w).eval x :=
        integral_eval_eq_sum_of_degree_lt hμ hmod
    _ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        congr 1
        conv_rhs => rw [← hsplit]
        have h0 : w.eval x = 0 := Lagrange.eval_nodal_at_node (v := id) hx
        rw [eval_add, eval_mul, h0, zero_mul, add_zero]

/-- **Gauss quadrature**: if the nodal polynomial $\pi_s$ of distinct real nodes $s$ is
orthogonal in $L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite
measure $\mu$ supported in $[a, b]$, then
$$\int p\,d\mu = \sum_{x\in s}\Bigl(\int\ell_x\,d\mu\Bigr)p(x)$$
for every real polynomial $p$ of degree less than $2\lvert s\rvert$, $\ell_x$ the Lagrange basis
polynomial of $x$. [Gautschi2004, Theorems 1.45 and 1.46]; [GolubMeurant2010, Ch. 6];
there at the zeros of the orthogonal polynomial of a positive measure; here at any nodes whose
nodal polynomial is orthogonal.
Result: gauss-quadrature -/
theorem IsOrthogonalPolynomial.integral_eval_eq_sum {μ : Measure ℝ} {s : Finset ℝ}
    (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id)) [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : p.degree < 2 * s.card) :
    ∫ x, p.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x := by
  exact hs.integral_eval_eq_sum_of_degree_lt_card_add hμ (by rwa [← two_mul])

/-- The Gauss weights are nonnegative: if the nodal polynomial of $s$ is orthogonal in
$L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite measure $\mu$
supported in $[a, b]$, then the weight of each node $x \in s$ is
$\int\ell_x\,d\mu = \int\ell_x^2\,d\mu \ge 0$, $\ell_x$ the Lagrange basis polynomial of $x$:
$\ell_x^2 - \ell_x$ vanishes at the nodes and has degree less than $2\lvert s\rvert$. -/
theorem IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ s) :
    ∫ t, (Lagrange.basis s id x).eval t ∂μ = ∫ t, (Lagrange.basis s id x).eval t ^ 2 ∂μ := by
  set ℓ := Lagrange.basis s id x
  have hcard : 0 < s.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hdeg : (ℓ ^ 2).degree < 2 * s.card := by
    have h1 : (ℓ ^ 2).natDegree < 2 * s.card := by
      have := natDegree_pow_le (p := ℓ) (n := 2)
      rw [Lagrange.natDegree_basis (Set.injOn_id _) hx] at this
      omega
    have h2 : (ℓ ^ 2).degree < ((2 * s.card : ℕ) : WithBot ℕ) :=
      degree_le_natDegree.trans_lt (by exact_mod_cast h1)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h2
  have h := hs.integral_eval_eq_sum hμ hdeg
  simp only [eval_pow] at h
  rw [h, Finset.sum_eq_single x]
  · have : ℓ.eval x = 1 := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hx
    rw [this, one_pow, mul_one]
  · intro y hy hyx
    have : ℓ.eval y = 0 := Lagrange.eval_basis_of_ne (v := id) (Ne.symm hyx) hy
    rw [this]
    ring
  · intro hx'
    exact absurd hx hx'

/-- The integral against the Gauss rule: if the nodal polynomial of $s$ is orthogonal in
$L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite measure $\mu$
supported in $[a, b]$, then for every $f : \mathbb{R} \to \mathbb{R}$ the integral of $f$ against
the interpolatory rule at $s$ is $\sum_{x\in s}\bigl(\int\ell_x\,d\mu\bigr)f(x)$, $\ell_x$ the
Lagrange basis polynomial of $x$; the truncation of the weights at $0$ does not act. -/
theorem IsOrthogonalPolynomial.integral_interpolatoryQuadrature {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (f : ℝ → ℝ) :
    ∫ x, f x ∂interpolatoryQuadrature μ s =
      ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * f x := by
  unfold interpolatoryQuadrature
  rw [integral_finsetSum_measure fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal]
  rw [hs.integral_eval_basis_eq_integral_sq hμ hx]
  exact integral_nonneg fun t => sq_nonneg _

/-- **The Gauss rule matches $2\lvert s\rvert$ moments**: if the nodal polynomial of $s$ is
orthogonal in $L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite
measure $\mu$ supported in $[a, b]$, then $\mu$ and its interpolatory rule at $s$ match their
first $2\lvert s\rvert$ moments.
[Gautschi2004, Theorems 1.45 and 1.46]; [GolubMeurant2010, Ch. 6].
Result: gauss-quadrature -/
theorem IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    MatchesMoments μ (interpolatoryQuadrature μ s) (2 * s.card) := by
  intro p hp
  rw [hs.integral_interpolatoryQuadrature hμ,
    hs.integral_eval_eq_sum hμ (by exact_mod_cast hp)]

/-! ### The canonical Gauss rule -/

/-- The **$k$-point Gauss rule** of $\mu$: the interpolatory rule at the Gauss nodes. It matches
the first $2k$ moments of $\mu$ for every $k$; past the number of support points it is $\mu$
itself. -/
noncomputable def gaussQuadrature (μ : Measure ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (gaussNodes μ k)

/-- The Gauss rule is a finite measure (the definition is not reducible, so
`isFiniteMeasure_interpolatoryQuadrature` is not found through it). -/
instance isFiniteMeasure_gaussQuadrature (μ : Measure ℝ) (k : ℕ) :
    IsFiniteMeasure (gaussQuadrature μ k) := by
  unfold gaussQuadrature
  infer_instance

/-! ### Every measure -/

/-- An interpolatory rule lives on its nodes: for every measure $\mu$ on $\mathbb{R}$ and every
finite set $s$, almost every point of the interpolatory rule of $\mu$ at $s$ lies in $s$. -/
theorem ae_mem_interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) :
    ∀ᵐ x ∂interpolatoryQuadrature μ s, x ∈ s := by
  unfold interpolatoryQuadrature
  rw [ae_finsetSum_measure_iff]
  exact fun x hx => Measure.ae_smul_measure (by simpa using hx) _

/-- Every real function is integrable against the Gauss rule: for every measure $\mu$ on
$\mathbb{R}$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$, $f$ is integrable against
`gaussQuadrature μ k`, a finite sum of Dirac masses. -/
theorem integrable_gaussQuadrature (μ : Measure ℝ) (k : ℕ) (f : ℝ → ℝ) :
    Integrable f (gaussQuadrature μ k) := by
  unfold gaussQuadrature interpolatoryQuadrature
  exact integrable_finsetSum_measure.mpr fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- The Gauss rule as a sum of point masses: for every measure $\mu$ on $\mathbb{R}$, every
$k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{gaussQuadrature}(\mu, k) = \sum_{x\in G}w_x f(x)\,,$$
with $G$ the Gauss nodes of order $k$ and $w_x$ the mass of the rule at $x$. No support
hypothesis: the rule is a finite sum of Dirac masses. -/
theorem integral_gaussQuadrature_eq_sum (μ : Measure ℝ) (k : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussQuadrature μ k = ∑ x ∈ gaussNodes μ k, (gaussQuadrature μ k).real {x} * f x :=
  integral_eq_sum_measureReal_singleton_mul (μ := gaussQuadrature μ k)
    (ae_mem_interpolatoryQuadrature μ (gaussNodes μ k)) f

/-! ### Finite measures with compact support -/

section Finite

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- A measure carried by the nodes is its own interpolatory rule: if a finite measure $\mu$ is
carried by a finite set $s$, then the interpolatory rule of $\mu$ at $s$ is $\mu$ (its weights
$\int\ell_x\,d\mu$ are the masses $\mu\{x\}$). -/
theorem interpolatoryQuadrature_eq_self_of_ae_mem {s : Finset ℝ} (hs : ∀ᵐ x ∂μ, x ∈ s) :
    interpolatoryQuadrature μ s = μ := by
  refine Eq.trans ?_ (Measure.ae_mem_finset_iff.mp hs).symm
  simp only [interpolatoryQuadrature]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_eval_basis_of_ae_mem hs hx, ofReal_measureReal]

/-- **Gauss quadrature**: for a finite measure $\mu$ supported in $[a, b]$ and every $k$, the
$k$-point Gauss rule matches the first $2k$ moments of $\mu$: it integrates every real polynomial
of degree less than $2k$ exactly. [Gautschi2004, Theorem 1.45]; [GolubMeurant2010, Ch. 6];
there for $k$ at most the number of support points; past it the rule is $\mu$ itself.
Result: gauss-quadrature -/
theorem matchesMoments_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    MatchesMoments μ (gaussQuadrature μ k) (2 * k) := by
  by_cases h : IsMomentPosDef μ k
  · have := (isOrthogonalPolynomial_nodal_gaussNodes hμ k).matchesMoments_interpolatoryQuadrature hμ
    rwa [h.card_gaussNodes hμ] at this
  · unfold gaussQuadrature
    rw [interpolatoryQuadrature_eq_self_of_ae_mem (ae_mem_gaussNodes_of_not_isMomentPosDef hμ h)]
    exact MatchesMoments.refl _ _

/-- The integral against the Gauss rule with the interpolatory weights: for a finite measure
$\mu$ supported in $[a, b]$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{gaussQuadrature}(\mu, k) = \sum_{x\in G}\Bigl(\int\ell_x\,d\mu\Bigr)f(x)\,,$$
$G$ the Gauss nodes of order $k$ and $\ell_x$ the Lagrange basis polynomial of $x$. -/
theorem integral_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussQuadrature μ k =
      ∑ x ∈ gaussNodes μ k, (∫ t, (Lagrange.basis (gaussNodes μ k) id x).eval t ∂μ) * f x :=
  IsOrthogonalPolynomial.integral_interpolatoryQuadrature
    (isOrthogonalPolynomial_nodal_gaussNodes hμ k) hμ f

/-- The Gauss rule lives in every interval carrying the measure: for a finite measure $\mu$
supported in $[a, b]$ and every $k$, almost every point of the $k$-point Gauss rule lies in
$[a, b]$. With `matchesMoments_gaussQuadrature`, the two hypotheses moment-matching error bounds
need. -/
theorem ae_mem_Icc_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∀ᵐ x ∂gaussQuadrature μ k, x ∈ Set.Icc a b := by
  by_cases h : IsMomentPosDef μ k
  · unfold gaussQuadrature
    filter_upwards [ae_mem_interpolatoryQuadrature μ (gaussNodes μ k)] with x hx
    exact h.gaussNodes_subset_Icc hμ (Finset.mem_coe.mpr hx)
  · unfold gaussQuadrature
    rw [interpolatoryQuadrature_eq_self_of_ae_mem (ae_mem_gaussNodes_of_not_isMomentPosDef hμ h)]
    exact hμ

/-- The mass of the Gauss rule: for a finite measure $\mu$ supported in $[a, b]$ and $k > 0$,
the $k$-point Gauss rule has mass $\mu(\mathbb{R})$. -/
theorem gaussQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ} (hk : 0 < k) :
    (gaussQuadrature μ k).real Set.univ = μ.real Set.univ :=
  ((matchesMoments_gaussQuadrature hμ k).measureReal_univ_eq (by omega)).symm

/-- The mass of the Gauss rule at a node is the interpolatory weight: for a finite measure $\mu$
supported in $[a, b]$, every $k$ and every Gauss node $x$ of order $k$,
$$\mathsf{gaussQuadrature}(\mu, k)(\{x\}) = \int\ell_x\,d\mu\,,$$
$\ell_x$ the Lagrange basis polynomial of $x$ at the Gauss nodes; by
`IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq` this is also $\int\ell_x^2\,d\mu$.
The link between the two weight forms of `integral_gaussQuadrature_eq_sum` and
`integral_gaussQuadrature`. -/
theorem gaussQuadrature_real_singleton (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ} {x : ℝ}
    (hx : x ∈ gaussNodes μ k) :
    (gaussQuadrature μ k).real {x} = ∫ t, (Lagrange.basis (gaussNodes μ k) id x).eval t ∂μ := by
  -- integrate the indicator of $\{x\}$ in both weight forms
  have h := (integral_gaussQuadrature_eq_sum μ k fun t => if t = x then (1 : ℝ) else 0).symm
    |>.trans (integral_gaussQuadrature hμ k _)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hx, if_true] using h

/-- The Gauss weights are positive: if a finite measure $\mu$ supported in $[a, b]$ is positive
definite up to degree $k$, then the $k$-point Gauss rule gives every Gauss node positive mass.
[Gautschi2004, Theorem 1.46]. -/
theorem IsMomentPosDef.gaussQuadrature_real_singleton_pos {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ gaussNodes μ k) :
    0 < (gaussQuadrature μ k).real {x} := by
  have hG : (gaussNodes μ k).card = k := h.card_gaussNodes hμ
  rw [gaussQuadrature_real_singleton hμ hx,
    (isOrthogonalPolynomial_nodal_gaussNodes hμ k).integral_eval_basis_eq_integral_sq hμ hx]
  refine h _ (Lagrange.basis_ne_zero (Set.injOn_id _) hx) ?_
  rw [Lagrange.degree_basis (Set.injOn_id _) hx, hG]
  exact_mod_cast Nat.sub_lt (hG ▸ Finset.card_pos.mpr ⟨x, hx⟩) one_pos

/-- **Uniqueness of the Gauss rule**: if a finite measure $\nu$ carried by a set of at most $k$
points matches the first $2k$ moments of a finite measure $\mu$ supported in $[a, b]$, then $\nu$
is the $k$-point Gauss rule of $\mu$. [Gautschi2004, §1.4]; there among
interpolatory rules with $k$ distinct nodes and positive weights; here any measure on at most $k$
points.
Result: gauss-quadrature-uniqueness -/
theorem MatchesMoments.eq_gaussQuadrature [IsFiniteMeasure ν] {k : ℕ}
    (h : MatchesMoments μ ν (2 * k)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {s : Finset ℝ}
    (hν : ∀ᵐ x ∂ν, x ∈ s) (hs : s.card ≤ k) : ν = gaussQuadrature μ k := by
  have hM : MatchesMoments ν (gaussQuadrature μ k) (2 * k) :=
    h.symm.trans (matchesMoments_gaussQuadrature hμ k)
  have hνT : ∀ᵐ x ∂ν, x ∈ s ∪ gaussNodes μ k :=
    hν.mono fun x hx => Finset.mem_union_left _ hx
  have hGT : ∀ᵐ x ∂gaussQuadrature μ k, x ∈ s ∪ gaussNodes μ k := by
    exact (ae_mem_interpolatoryQuadrature μ (gaussNodes μ k)).mono fun x hx =>
      Finset.mem_union_right _ hx
  have hcard : (s ∪ gaussNodes μ k).card ≤ 2 * k :=
    (Finset.card_union_le _ _).trans (by have := card_gaussNodes_le μ k; omega)
  exact MatchesMoments.eq_of_ae_mem (hM.mono hcard) hνT hGT

/-- **The Gauss-rule error from uniform approximation**: for a finite measure $\mu$ supported in
$[a, b]$, $f$ integrable against $\mu$, and a real polynomial $p$ of degree less than $2k$ within
$\varepsilon$ of $f$ on $[a, b]$,
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k)\Bigr\rvert \le
2\varepsilon\,\mu(\mathbb{R})\,.$$
[GolubMeurant2010, Ch. 6]; the composition of exactness with the moment-matching transfer. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {f : ℝ → ℝ} (hf : Integrable f μ) {k : ℕ} {p : ℝ[X]}
    (hp : p.degree < 2 * k) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ k| ≤ 2 * ε * μ.real Set.univ := by
  have h := MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn
    (matchesMoments_gaussQuadrature hμ k) hμ (ae_mem_Icc_gaussQuadrature hμ k) hf
    (integrable_gaussQuadrature μ k f) hp hε
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- at $k = 0$ the rule is $0$, and the bound $\mu(\mathbb{R})\varepsilon$ is nonnegative
    have hnu : (gaussQuadrature μ 0).real Set.univ = 0 := by
      simp only [gaussQuadrature, interpolatoryQuadrature, gaussNodes, orthogonalPolynomial_zero,
        roots_one, Multiset.empty_eq_zero, Multiset.toFinset_zero, Finset.sum_empty,
        measureReal_zero, Pi.zero_apply]
    rw [hnu, add_zero] at h
    linarith [abs_nonneg (∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ 0)]
  · rw [gaussQuadrature_real_univ hμ hk] at h
    linarith

/-- **The Gauss-rule error for Lipschitz functions**: for a finite measure $\mu$ supported in
$[a, b]$, $a < b$, and $f$ $L$-Lipschitz on $[a, b]$, the $(k + 1)$-point Gauss rule
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k + 1)\Bigr\rvert \le
\frac{\pi L(b - a)}{2k + 3}\mu(\mathbb{R})\,,$$
from Jackson's theorem on $[a, b]$ in degree $2k + 1$ (the constant is
`jacksonApproximationConstant`). [GolubMeurant2010, Ch. 6]; the approximation step is
[ChenTrogdonUbaru2022, Appendix C, Theorem 38]; constants composed here. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) (k : ℕ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ (k + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * k + 3) * μ.real Set.univ := by
  have hint : Integrable f μ := hf.continuousOn.integrable_of_ae_mem_Icc hμ
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) hab hf (2 * k + 1)
  have hp' : p.degree < 2 * ((k + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * k + 1 < 2 * (k + 1)))
  have h := abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn hμ hint hp' hε
  refine h.trans_eq ?_
  push_cast
  field_simp
  ring

/-- **The Gauss-rule error and the minimax error**: for a finite measure $\mu$ supported in
$[a, b]$ and $f$ continuous on $[a, b]$, the $(k + 1)$-point Gauss rule satisfies
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k + 1)\Bigr\rvert \le
2E_{2k + 1}(f; [a, b])\,\mu(\mathbb{R})\,,$$
$E_{2k + 1}$ the error of the best uniform approximation of $f$ on $[a, b]$ by polynomials of
degree at most $2k + 1$ (`minimaxError`). [GolubMeurant2010, §6.2.1]; [Trefethen2019, Theorem
19.1]. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_continuousOn
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) (k : ℕ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ (k + 1)| ≤
      2 * minimaxError f (Set.Icc a b) (2 * k + 1) * μ.real Set.univ := by
  have hint : Integrable f μ := hf.integrable_of_ae_mem_Icc hμ
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc hf (2 * k + 1)
  have hp' : p.degree < 2 * ((k + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * k + 1 < 2 * (k + 1)))
  exact abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn hμ hint hp' hε

/-! ### The Gauss remainder -/

/-- The terminating case: if the orthogonal polynomial $\pi_k$ of a finite measure $\mu$
supported in $[a, b]$ has norm $0$ in $L^2(\mu)$ ($\mu$ has at most $k$ support points), then
the $k$-point Gauss rule of $\mu$ is $\mu$ itself. -/
theorem gaussQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = 0) : gaussQuadrature μ k = μ := by
  unfold gaussQuadrature
  refine interpolatoryQuadrature_eq_self_of_ae_mem ?_
  filter_upwards [ae_eval_eq_zero_of_integral_sq_eq_zero hμ h] with x hx
  exact mem_gaussNodes.mpr hx

/-- The pointwise Hermite remainder at doubled nodes: for a nonempty finite set $G \subseteq (a, b)$
and $H$ of degree less than $2\lvert G\rvert$ matching the values and first derivatives of $f$ on
$G$, $f(x) - H(x) = f^{(2\lvert G\rvert)}(\xi)\,\omega_G(x)^2/(2\lvert G\rvert)!$. -/
private theorem exists_sub_eval_eq_iteratedDeriv_mul_nodal_sq {a b : ℝ} (hab : a < b)
    {G : Finset ℝ} (hG : G.Nonempty) (hGab : (G : Set ℝ) ⊆ Set.Ioo a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * G.card : ℕ) f (Set.Ioo a b))
    {H : ℝ[X]} (hH : H.degree < (G.val + G.val).card)
    (hjet : ∀ y ∈ G.val + G.val, ∀ k < (G.val + G.val).count y,
      (derivative^[k] H).eval y = iteratedDeriv k f y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, f x - H.eval x =
      iteratedDeriv (2 * G.card) f ξ / (2 * G.card).factorial *
        (Lagrange.nodal G id).eval x ^ 2 := by
  have hcard : (G.val + G.val).card = 2 * G.card := by
    rw [Multiset.card_add, Finset.card_val]; ring
  have hmem : ∀ y ∈ G.val + G.val, y ∈ Set.Ioo a b := fun y hy => by
    rcases Multiset.mem_add.mp hy with h | h <;> exact hGab h
  obtain ⟨ξ, hξ, h⟩ := exists_sub_eval_eq_iteratedDeriv_mul hab
    (by simpa using hG.ne_empty) (fun y hy => Set.Ioo_subset_Icc_self (hmem y hy))
    (fun y hy _ => hmem y hy) hf (hcard ▸ hf') hH hjet hx
  refine ⟨ξ, hξ, h.trans ?_⟩
  rw [hcard, Multiset.map_add, Multiset.prod_add, Lagrange.nodal, Finset.prod_eq_multiset_prod]
  rw [sq, eval_mul]; rfl

/-- The mean-value step of the Gauss, Radau and Lobatto remainders: for a finite measure
$\mu$ supported in $[a, b]$, $a < b$, $f$ continuous on $[a, b]$ and $C^n$ on $(a, b)$, and a
polynomial $H$, if for every $x \in [a, b]$ there is $\xi_x \in (a, b)$ with
$f(x) - H(x) = f^{(n)}(\xi_x)\,W(x)/n!$, $W$ integrable and of one sign $\mu$-almost
everywhere, then one $\xi \in (a, b)$ serves the integral:
$$\int f\,d\mu - \int H\,d\mu = \frac{f^{(n)}(\xi)}{n!}\int W\,d\mu\,.$$ -/
theorem exists_integral_sub_integral_eval_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) {n : ℕ} {f W : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ n f (Set.Ioo a b)) (hW : Integrable W μ)
    (hWs : (∀ᵐ x ∂μ, 0 ≤ W x) ∨ ∀ᵐ x ∂μ, W x ≤ 0) {H : ℝ[X]}
    (hpt : ∀ x ∈ Set.Icc a b, ∃ ξ ∈ Set.Ioo a b,
      f x - H.eval x = iteratedDeriv n f ξ / n.factorial * W x) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, H.eval x ∂μ =
      iteratedDeriv n f ξ / n.factorial * ∫ x, W x ∂μ := by
  have hfint : Integrable f μ := hf.integrable_of_ae_mem_Icc hμ
  have hD : ContinuousOn (fun ξ => iteratedDeriv n f ξ / n.factorial) (Set.Ioo a b) :=
    ((hf'.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ioo a b)).congr
      fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm).div_const _
  have hint := hfint.sub (integrable_eval_of_ae_mem_Icc hμ H)
  rw [← integral_sub hfint (integrable_eval_of_ae_mem_Icc hμ H)]
  rcases hWs with hWs | hWs
  · exact exists_integral_eq_mul_integral_of_ae_nonneg hint hW hWs (isConnected_Ioo hab) hD
      (hμ.mono hpt)
  · exact exists_integral_eq_mul_integral_of_ae_nonpos hint hW hWs (isConnected_Ioo hab) hD
      (hμ.mono hpt)

/-- **The Gauss quadrature remainder**: for a finite measure $\mu$ supported in $[a, b]$,
$a < b$, $k > 0$, and $f$ continuous on $[a, b]$ and $C^{2k}$ on $(a, b)$, there is
$\xi \in (a, b)$ with
$$\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k) =
\frac{f^{(2k)}(\xi)}{(2k)!}\int\pi_k^2\,d\mu\,,$$
$\pi_k$ the monic orthogonal polynomial of degree $k$. When $\mu$ has at most $k$ support
points both sides are $0$. [Gautschi2004, corollary to Theorem 1.48, (1.4.14)]; [GolubMeurant2010,
§6.2.1]; there for $f \in C^{2k}[a, b]$.
Result: gauss-quadrature-remainder -/
theorem exists_integral_sub_integral_gaussQuadrature_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) {k : ℕ} (hk : 0 < k) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ k =
      iteratedDeriv (2 * k) f ξ / (2 * k).factorial *
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ := by
  set π := orthogonalPolynomial μ k
  rcases (integral_nonneg fun x => sq_nonneg (π.eval x) : 0 ≤ ∫ x, π.eval x ^ 2 ∂μ).eq_or_lt
    with h0 | hpos
  · refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [← h0, gaussQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero hμ h0.symm,
      sub_self, mul_zero]
  have hPD := (isMomentPosDef_succ_iff hμ k).mpr hpos
  set G := gaussNodes μ k
  have hcard : G.card = k := (hPD.mono k.le_succ).card_gaussNodes hμ
  have hGab : (G : Set ℝ) ⊆ Set.Ioo a b := hPD.gaussNodes_subset_Ioo hμ
  have hnodal : Lagrange.nodal G id = π := (hPD.mono k.le_succ).nodal_gaussNodes hμ
  have hG : G.Nonempty := Finset.card_pos.mp (hcard ▸ hk)
  obtain ⟨H, hHdeg, hHjet⟩ :=
    exists_degree_lt_forall_iterate_derivative_eval_eq (G.val + G.val)
      fun y j => iteratedDeriv j f y
  have hm : (G.val + G.val).card = 2 * k := by
    rw [Multiset.card_add, Finset.card_val, hcard]; ring
  -- the rule integrates `f` as it integrates `H`, exactly
  have hquad : ∫ x, f x ∂gaussQuadrature μ k = ∫ x, H.eval x ∂μ := by
    rw [matchesMoments_gaussQuadrature hμ k H (by rw [← hm]; exact_mod_cast hHdeg),
      integral_gaussQuadrature_eq_sum, integral_gaussQuadrature_eq_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : y ∈ G.val + G.val := Multiset.mem_add.mpr (Or.inl hy)
    have := hHjet y hy' 0 (Multiset.count_pos.mpr hy')
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero] at this
    rw [this]
  rw [hquad]
  refine exists_integral_sub_integral_eval_eq hμ hab hf hf'
    ((integrable_eval_of_ae_mem_Icc hμ (π ^ 2)).congr (ae_of_all _ fun x => by simp))
    (.inl (ae_of_all _ fun x => sq_nonneg _)) fun x hx => ?_
  obtain ⟨ξ, hξ, h⟩ := exists_sub_eval_eq_iteratedDeriv_mul_nodal_sq hab hG hGab hf
    (hcard ▸ hf') hHdeg hHjet hx
  rw [hcard, hnodal] at h
  exact ⟨ξ, hξ, h⟩

/-- **Gauss quadrature is a lower bound** for $f$ with nonnegative derivative of order $2k$: for
a finite measure $\mu$ supported in $[a, b]$, $a < b$, $k > 0$, and $f$ continuous on $[a, b]$,
$C^{2k}$ on $(a, b)$ with $f^{(2k)} \ge 0$ there,
$$\int f\,d\,\mathsf{gaussQuadrature}(\mu, k) \le \int f\,d\mu\,.$$
[Gautschi2004, corollary to Theorem 1.48, (1.4.14)]; [GolubMeurant2010, §6.2.1]. -/
theorem integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {k : ℕ} (hk : 0 < k) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv (2 * k) f x) :
    ∫ x, f x ∂gaussQuadrature μ k ≤ ∫ x, f x ∂μ := by
  obtain ⟨ξ, hξ, h⟩ := exists_integral_sub_integral_gaussQuadrature_eq hμ hab hk hf hf'
  have h1 : 0 ≤ iteratedDeriv (2 * k) f ξ / (2 * k).factorial :=
    div_nonneg (hD ξ hξ) (Nat.cast_nonneg _)
  have h2 : 0 ≤ ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have h3 := mul_nonneg h1 h2
  linarith

/-- **Gauss quadrature is an upper bound** for $f$ with nonpositive derivative of order $2k$:
for a finite measure $\mu$ supported in $[a, b]$, $a < b$, $k > 0$, and $f$ continuous on
$[a, b]$, $C^{2k}$ on $(a, b)$ with $f^{(2k)} \le 0$ there,
$$\int f\,d\mu \le \int f\,d\,\mathsf{gaussQuadrature}(\mu, k)\,.$$
[Gautschi2004, corollary to Theorem 1.48, (1.4.14)]; [GolubMeurant2010, §6.2.1]. -/
theorem integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {k : ℕ} (hk : 0 < k) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, iteratedDeriv (2 * k) f x ≤ 0) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂gaussQuadrature μ k := by
  have h := integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg (μ := μ) hμ hab hk
    (f := fun x => -f x) hf.neg hf'.neg
    (fun x hx => by
      have h0 := hD x hx
      rw [show (fun x => -f x) = -f from rfl, iteratedDeriv_neg]
      simpa using h0)
  simp only [integral_neg] at h
  linarith

end Finite

end NLAlib
