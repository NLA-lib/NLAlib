/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Recurrence
public import Mathlib.Analysis.Polynomial.Order

/-!
# Zeros of orthogonal polynomials

The Gauss nodes of order $k$ of a measure $\mu$ on $\mathbb{R}$ are the distinct real zeros of
its monic orthogonal polynomial $\pi_k$ (`NLAlib.orthogonalPolynomial`). When $\mu$, finite and
supported in $[a, b]$, is positive definite up to degree $k$, $\pi_k$ has $k$ real simple zeros
in $[a, b]$ and is their nodal polynomial; otherwise $\mu$ is carried by the zeros of $\pi_k$.
In both cases the nodal polynomial of the Gauss nodes is orthogonal to the polynomials of lower
degree, the hypothesis of Gauss quadrature (`NLAlib.Polynomial.Orthogonal.Gauss`).
[Gautschi2004]; [Szego1975].

## Main definitions

* `NLAlib.gaussNodes`: the distinct real zeros of $\pi_k$.

## Main results

* `NLAlib.mem_gaussNodes`: the Gauss nodes are the zeros of $\pi_k$, and
  `NLAlib.exists_orthogonalPolynomial_eq_X_sub_C_mul` splits off the linear factor of a zero.
* `NLAlib.card_gaussNodes_le`: at most $k$ Gauss nodes.
* `NLAlib.IsMomentPosDef.card_roots_orthogonalPolynomial`,
  `NLAlib.IsMomentPosDef.nodup_roots_orthogonalPolynomial`: real simple zeros.
* `NLAlib.IsMomentPosDef.nodal_gaussNodes`, `NLAlib.IsMomentPosDef.card_gaussNodes`,
  `NLAlib.IsMomentPosDef.gaussNodes_subset_Icc`: $k$ nodes in $[a, b]$, with nodal polynomial
  $\pi_k$.
* `NLAlib.IsMomentPosDef.gaussNodes_subset_Ioo`: with one more support point, the Gauss nodes
  are interior.
* `NLAlib.ae_mem_gaussNodes_of_not_isMomentPosDef`: the degenerate case.
* `NLAlib.isOrthogonalPolynomial_nodal_gaussNodes`: the Gauss hypothesis for every $k$.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- The **Gauss nodes** of order $k$: the distinct real zeros of $\pi_k$. When $\mu$ is positive
definite up to degree $k$ there are $k$ of them, in every interval carrying $\mu$, and
$\pi_k$ is their nodal polynomial. Junk: past the number of support points, the support and
possibly $0$. -/
noncomputable def gaussNodes (μ : Measure ℝ) (k : ℕ) : Finset ℝ :=
  (orthogonalPolynomial μ k).roots.toFinset

/-- Membership in the Gauss nodes: for every measure $\mu$ on $\mathbb{R}$, $x$ is a Gauss node
of order $k$ iff it is a zero of $\pi_k$. -/
theorem mem_gaussNodes {μ : Measure ℝ} {k : ℕ} {x : ℝ} :
    x ∈ gaussNodes μ k ↔ (orthogonalPolynomial μ k).IsRoot x := by
  rw [gaussNodes, Multiset.mem_toFinset, mem_roots (monic_orthogonalPolynomial μ k).ne_zero]

/-- A zero of $\pi_k$ splits off a linear factor: for every measure $\mu$ on $\mathbb{R}$, if
$\pi_k(x) = 0$ then $\pi_k = (X - x)g$ with $g \ne 0$ of degree less than $k$. -/
theorem exists_orthogonalPolynomial_eq_X_sub_C_mul {μ : Measure ℝ} {k : ℕ} {x : ℝ}
    (hx : (orthogonalPolynomial μ k).IsRoot x) :
    ∃ g : ℝ[X], g ≠ 0 ∧ g.degree < k ∧ orthogonalPolynomial μ k = (X - C x) * g := by
  have hπ := (mul_divByMonic_eq_iff_isRoot.mpr hx).symm
  set g := orthogonalPolynomial μ k /ₘ (X - C x)
  have hg : g ≠ 0 := fun h0 => (monic_orthogonalPolynomial μ k).ne_zero (by rw [hπ, h0, mul_zero])
  have hdeg := natDegree_mul (X_sub_C_ne_zero x) hg
  rw [← hπ, natDegree_orthogonalPolynomial, natDegree_X_sub_C] at hdeg
  exact ⟨g, hg, degree_le_natDegree.trans_lt (by exact_mod_cast (by omega : g.natDegree < k)), hπ⟩

/-- There are at most $k$ Gauss nodes of order $k$, for every measure $\mu$ on $\mathbb{R}$. -/
theorem card_gaussNodes_le (μ : Measure ℝ) (k : ℕ) : (gaussNodes μ k).card ≤ k := by
  unfold gaussNodes
  calc (orthogonalPolynomial μ k).roots.toFinset.card ≤
      Multiset.card (orthogonalPolynomial μ k).roots := Multiset.toFinset_card_le _
    _ ≤ (orthogonalPolynomial μ k).natDegree := card_roots' _
    _ = k := natDegree_orthogonalPolynomial μ k

section Definite

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- The shared step of the three zero theorems: if $\mu$, finite and supported in $[a, b]$, is
positive definite up to degree $k$, $p$ is orthogonal to the polynomials of degree less than $k$,
$\deg r < k$, $pr \ge 0$ $\mu$-almost everywhere, and the zeros of $pr$ in $[a, b]$ lie in a set
$s$ of fewer than $k$ points, then we have a contradiction. -/
private theorem IsMomentPosDef.false_of_ae_nonneg_mul {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : IsOrthogonalPolynomial μ k p) {r : ℝ[X]}
    (hr : r.degree < k) (hnn : ∀ᵐ x ∂μ, 0 ≤ (p * r).eval x) {s : Finset ℝ} (hs : s.card < k)
    (hz : ∀ x ∈ Set.Icc a b, (p * r).eval x = 0 → x ∈ s) : False := by
  have hint : ∫ x, (p * r).eval x ∂μ = 0 := by simpa only [eval_mul] using hp r hr
  have hzero : ∀ᵐ x ∂μ, (p * r).eval x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn (integrable_eval_of_ae_mem_Icc hμ _)).mp hint
  have hcar : ∀ᵐ x ∂μ, x ∈ s := (hμ.and hzero).mono fun x hx => hz x hx.1 hx.2
  exact Nat.lt_irrefl s.card
    (Nat.lt_of_lt_of_le hs ((isMomentPosDef_iff_forall_finset hμ k).mp h s hcar))

/-- **The zeros of the orthogonal polynomial are real**: if $\mu$, finite and supported in
$[a, b]$, is positive definite up to degree $k$, then $\pi_k$ has $k$ real zeros counted with
multiplicity. [Gautschi2004, Theorem 1.19]; [Szego1975, Theorem 3.3.1].
Result: orthogonal-polynomial-zeros -/
theorem IsMomentPosDef.card_roots_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : Multiset.card (orthogonalPolynomial μ k).roots = k := by
  set π := orthogonalPolynomial μ k
  refine (natDegree_orthogonalPolynomial μ k ▸ card_roots' π).antisymm (not_lt.mp fun hlt => ?_)
  -- $\pi_k = Rg$ with $R$ the product over the real roots and $g > 0$ root-free
  obtain ⟨g, hg, -, hg0⟩ := exists_prod_multiset_X_sub_C_mul π
  set R : ℝ[X] := (π.roots.map fun a => X - C a).prod with hR
  have hRm : R.Monic := monic_multisetProd_X_sub_C _
  have hgm : g.Monic := Monic.of_mul_monic_left hRm (hg ▸ monic_orthogonalPolynomial μ k)
  have hgpos : ∀ x, 0 < g.eval x := fun x => zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun y hy => (Multiset.notMem_zero y (hg0 ▸ (mem_roots hgm.ne_zero).mpr hy)).elim)
    (by rw [hgm.leadingCoeff]; exact zero_le_one)
  have hRk : R.natDegree < k := by rwa [hR, natDegree_multiset_prod_X_sub_C_eq_card]
  have he : ∀ x, (π * R).eval x = R.eval x ^ 2 * g.eval x := fun x => by
    rw [← hg]
    simp only [eval_mul]
    ring
  refine h.false_of_ae_nonneg_mul hμ (isOrthogonalPolynomial_orthogonalPolynomial hμ k)
    (degree_le_natDegree.trans_lt (by exact_mod_cast hRk))
    (ae_of_all _ fun x => he x ▸ mul_nonneg (sq_nonneg _) (hgpos x).le)
    ((Multiset.toFinset_card_le R.roots).trans_lt ((card_roots' R).trans_lt hRk)) fun x _ hx => ?_
  rw [he, mul_eq_zero, pow_eq_zero_iff two_ne_zero] at hx
  exact Multiset.mem_toFinset.mpr ((mem_roots hRm.ne_zero).mpr (hx.resolve_right (hgpos x).ne'))

/-- The zeros of the orthogonal polynomial are simple: if $\mu$, finite and supported in
$[a, b]$, is positive definite up to degree $k$, then the real zeros of $\pi_k$ are distinct.
[Gautschi2004, Theorem 1.19]; [Szego1975, Theorem 3.3.1]. -/
theorem IsMomentPosDef.nodup_roots_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (orthogonalPolynomial μ k).roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  rw [count_roots]
  by_contra! hlt
  -- a double zero $x$ gives $\pi_k = (X - x)^2g$, and $\pi_k g = ((X - x)g)^2 \ge 0$
  have hne := (monic_orthogonalPolynomial μ k).ne_zero
  obtain ⟨g, hg⟩ := (le_rootMultiplicity_iff hne).mp hlt
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hne (by rw [hg, mul_zero])
  have hXg : (X - C x) * g ≠ 0 := mul_ne_zero (X_sub_C_ne_zero x) hg0
  have hdeg : 2 + g.natDegree = k := by
    rw [← natDegree_orthogonalPolynomial μ k, hg,
      natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero x)) hg0, natDegree_pow, natDegree_X_sub_C]
  have hsq : orthogonalPolynomial μ k * g = ((X - C x) * g) ^ 2 := by rw [hg]; ring
  refine h.false_of_ae_nonneg_mul hμ (isOrthogonalPolynomial_orthogonalPolynomial hμ k)
    (degree_le_natDegree.trans_lt (by exact_mod_cast (by omega : g.natDegree < k)))
    (ae_of_all _ fun y => ?_) ((Multiset.toFinset_card_le _).trans_lt ((card_roots' _).trans_lt
      (by rw [natDegree_mul (X_sub_C_ne_zero x) hg0, natDegree_X_sub_C]; omega)))
    (fun y _ hy => ?_)
  · rw [hsq, eval_pow]
    exact sq_nonneg _
  · rw [hsq, eval_pow, pow_eq_zero_iff two_ne_zero] at hy
    exact Multiset.mem_toFinset.mpr ((mem_roots hXg).mpr hy)

/-- The orthogonal polynomial is the nodal polynomial of the Gauss nodes: if $\mu$, finite and
supported in $[a, b]$, is positive definite up to degree $k$, then
$\pi_k(z) = \prod_{x\in G}(z - x)$, $G$ the Gauss nodes of order $k$. -/
theorem IsMomentPosDef.nodal_gaussNodes {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    Lagrange.nodal (gaussNodes μ k) id = orthogonalPolynomial μ k := by
  have hnd := h.nodup_roots_orthogonalPolynomial hμ
  rw [Lagrange.nodal_eq]
  have : (gaussNodes μ k).val = (orthogonalPolynomial μ k).roots := by
    simp only [gaussNodes, Multiset.toFinset_val, hnd.dedup]
  simp only [id, Finset.prod_eq_multiset_prod, this]
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (monic_orthogonalPolynomial μ k) (by rw [h.card_roots_orthogonalPolynomial hμ,
      natDegree_orthogonalPolynomial])

/-- There are exactly $k$ Gauss nodes: if $\mu$, finite and supported in $[a, b]$, is positive
definite up to degree $k$, then $\pi_k$ has $k$ distinct real zeros. -/
theorem IsMomentPosDef.card_gaussNodes {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (gaussNodes μ k).card = k := by
  unfold gaussNodes
  rw [Multiset.toFinset_card_of_nodup (h.nodup_roots_orthogonalPolynomial hμ),
    h.card_roots_orthogonalPolynomial hμ]

/-- Shared step for `IsMomentPosDef.gaussNodes_subset_Icc`: if $\pi_k(x) = 0$ and
$(t - x)c > 0$ on $[a, b]$, then $\mu$ (supported in $[a, b]$) is positive definite up to
degree $k$ only if false. With $\pi_k = (X - x)g$, $\pi_k \cdot (c g) = (t-x)c\,g^2 \ge 0$ on
$[a, b]$, and its zeros there are roots of $g$, fewer than $k$ of them. -/
private theorem IsMomentPosDef.false_of_isRoot {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x c : ℝ} (hx : (orthogonalPolynomial μ k).IsRoot x)
    (hc : c ≠ 0) (hsgn : ∀ t ∈ Set.Icc a b, 0 < (t - x) * c) : False := by
  obtain ⟨g, hg, hgd, hπ⟩ := exists_orthogonalPolynomial_eq_X_sub_C_mul hx
  have hgk : g.natDegree < k := (natDegree_lt_iff_degree_lt hg).mpr hgd
  have he : ∀ t, (orthogonalPolynomial μ k * (C c * g)).eval t = (t - x) * c * g.eval t ^ 2 := by
    intro t
    rw [hπ]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    ring
  refine h.false_of_ae_nonneg_mul hμ (isOrthogonalPolynomial_orthogonalPolynomial hμ k)
    ((degree_C_mul hc).trans_lt (degree_le_natDegree.trans_lt (by exact_mod_cast hgk))) ?_
    ((Multiset.toFinset_card_le _).trans_lt ((card_roots' g).trans_lt hgk)) fun t ht hz => ?_
  · filter_upwards [hμ] with t ht
    rw [he]
    exact mul_nonneg (hsgn t ht).le (sq_nonneg _)
  · rw [he, mul_eq_zero, pow_eq_zero_iff two_ne_zero] at hz
    exact Multiset.mem_toFinset.mpr ((mem_roots hg).mpr (hz.resolve_left (hsgn t ht).ne'))

/-- The Gauss nodes lie in every interval carrying the measure: if $\mu$, finite and supported in
$[a, b]$, is positive definite up to degree $k$, then every real zero of $\pi_k$ lies in
$[a, b]$, hence in the convex hull of the support of $\mu$. -/
theorem IsMomentPosDef.gaussNodes_subset_Icc {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (gaussNodes μ k : Set ℝ) ⊆ Set.Icc a b := by
  intro y hy
  have hroot : (orthogonalPolynomial μ k).IsRoot y := mem_gaussNodes.mp hy
  exact ⟨le_of_not_gt fun hya =>
      h.false_of_isRoot hμ hroot one_ne_zero fun t ht => by linarith [ht.1],
    le_of_not_gt fun hyb =>
      h.false_of_isRoot hμ hroot (neg_ne_zero.mpr one_ne_zero) fun t ht => by linarith [ht.2]⟩

/-- Shared step for `IsMomentPosDef.gaussNodes_subset_Ioo`: if $\pi_k(x) = 0$ and
$(t - x)c \ge 0$ on $[a, b]$, then $\mu$ (supported in $[a, b]$) is not positive definite up to
degree $k + 1$. With $\pi_k = (X - x)g$, $\pi_k \cdot (c g) = (t-x)c\,g^2 \ge 0$ on $[a, b]$ and
$\int \pi_k\,cg\,d\mu = 0$, so $\pi_k^2 = 0$ a.e. -/
private theorem IsMomentPosDef.false_of_isRoot_endpoint {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x c : ℝ} (hx : (orthogonalPolynomial μ k).IsRoot x)
    (hc : c ≠ 0) (hsgn : ∀ t ∈ Set.Icc a b, 0 ≤ (t - x) * c) : False := by
  obtain ⟨g, hg, hgd, hπ⟩ := exists_orthogonalPolynomial_eq_X_sub_C_mul hx
  have hgk : g.natDegree < k := (natDegree_lt_iff_degree_lt hg).mpr hgd
  have hint : ∫ t, (orthogonalPolynomial μ k * (C c * g)).eval t ∂μ = 0 := by
    simpa only [eval_mul] using
      isOrthogonalPolynomial_orthogonalPolynomial hμ k (C c * g)
        ((degree_C_mul hc).trans_lt (degree_le_natDegree.trans_lt (by exact_mod_cast hgk)))
  have hnn : ∀ᵐ t ∂μ, 0 ≤ (orthogonalPolynomial μ k * (C c * g)).eval t := by
    filter_upwards [hμ] with t ht
    rw [hπ]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    nlinarith [mul_nonneg (hsgn t ht) (sq_nonneg (g.eval t))]
  have hzero : ∀ᵐ t ∂μ, (orthogonalPolynomial μ k * (C c * g)).eval t = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn (integrable_eval_of_ae_mem_Icc hμ _)).mp hint
  have hsq : ∀ᵐ t ∂μ, (orthogonalPolynomial μ k).eval t ^ 2 = 0 := by
    filter_upwards [hzero] with t ht
    rw [hπ] at ht ⊢
    simp only [eval_mul, eval_sub, eval_X, eval_C] at ht ⊢
    have h1 : (t - x) * g.eval t ^ 2 = 0 := by
      have : c * ((t - x) * g.eval t ^ 2) = 0 := by linear_combination ht
      exact (mul_eq_zero.mp this).resolve_left hc
    linear_combination (t - x) * h1
  have hdeg : (orthogonalPolynomial μ k).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree (monic_orthogonalPolynomial μ k).ne_zero,
      natDegree_orthogonalPolynomial]
    exact_mod_cast Nat.lt_succ_self k
  have hpos := h (orthogonalPolynomial μ k) (monic_orthogonalPolynomial μ k).ne_zero hdeg
  exact hpos.ne' (integral_eq_zero_of_ae (hsq.mono fun t ht => ht))

/-- **The Gauss nodes are interior**: if a finite measure $\mu$ supported in $[a, b]$ is positive
definite up to degree $k + 1$ (it has more than $k$ support points), then every zero of the
orthogonal polynomial $\pi_k$ lies in $(a, b)$. Definiteness up to degree $k$ is not enough:
$\mu = \delta_a + \delta_b$ has $\pi_2 = (x - a)(x - b)$. [Gautschi2004, Theorem 1.19];
[Szego1975, Theorem 3.3.1]; there in the interior of the support interval. -/
theorem IsMomentPosDef.gaussNodes_subset_Ioo {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    (gaussNodes μ k : Set ℝ) ⊆ Set.Ioo a b := by
  intro y hy
  have hroot : (orthogonalPolynomial μ k).IsRoot y := mem_gaussNodes.mp hy
  have hIcc : y ∈ Set.Icc a b :=
    (h.mono (by omega)).gaussNodes_subset_Icc hμ hy
  exact ⟨lt_of_le_of_ne hIcc.1 fun e => h.false_of_isRoot_endpoint hμ hroot one_ne_zero
      fun t ht => by linarith [ht.1, e],
    lt_of_le_of_ne hIcc.2 fun e => h.false_of_isRoot_endpoint hμ hroot
      (neg_ne_zero.mpr one_ne_zero) fun t ht => by linarith [ht.2, e]⟩

/-- The degenerate case: if $\mu$, finite and supported in $[a, b]$, is not positive definite up
to degree $k$, then $\mu$ is carried by the Gauss nodes of order $k$, the zeros of $\pi_k$. -/
theorem ae_mem_gaussNodes_of_not_isMomentPosDef (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ¬ IsMomentPosDef μ k) : ∀ᵐ x ∂μ, x ∈ gaussNodes μ k := by
  cases k with
  | zero =>
    exfalso
    exact h fun p hp hdeg => absurd hdeg (not_lt.mpr (zero_le_degree_iff.mpr hp))
  | succ j =>
    rw [isMomentPosDef_succ_iff hμ j, not_lt] at h
    have hsq : ∫ x, (orthogonalPolynomial μ (j + 1)).eval x ^ 2 ∂μ = 0 := by
      rw [integral_orthogonalPolynomial_succ_sq hμ j,
        le_antisymm h (integral_nonneg fun x => sq_nonneg _), mul_zero]
    filter_upwards [ae_eval_eq_zero_of_integral_sq_eq_zero hμ hsq] with x hx
    exact mem_gaussNodes.mpr hx

/-- The Gauss hypothesis holds for every order: for a finite measure $\mu$ supported in $[a, b]$
and every $k$, the nodal polynomial of the Gauss nodes $G$ of order $k$ is orthogonal in
$L^2(\mu)$ to the polynomials of degree less than $\lvert G\rvert$; this is the hypothesis
of every Gauss theorem on `interpolatoryQuadrature`. -/
theorem isOrthogonalPolynomial_nodal_gaussNodes (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsOrthogonalPolynomial μ (gaussNodes μ k).card (Lagrange.nodal (gaussNodes μ k) id) := by
  by_cases h : IsMomentPosDef μ k
  · rw [h.nodal_gaussNodes hμ, h.card_gaussNodes hμ]
    exact isOrthogonalPolynomial_orthogonalPolynomial hμ k
  · intro r _
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_mem_gaussNodes_of_not_isMomentPosDef hμ h] with x hx
    have h0 : (Lagrange.nodal (gaussNodes μ k) id).eval x = 0 :=
      Lagrange.eval_nodal_at_node (v := id) hx
    simp only [Pi.zero_apply, h0, zero_mul]

end Definite

end NLAlib
