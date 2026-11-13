/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Gauss

/-!
# Gauss–Radau rules

The Gauss–Radau rule of a measure $\mu$ with a prescribed node $c$ and $k$ free nodes puts the
free nodes at the zeros of the degree-$k$ orthogonal polynomial of the modified measure
$\lvert x - c\rvert\,d\mu(x)$ (`radauMeasure`) and takes interpolatory weights at the $k + 1$
nodes. It is built on `interpolatoryQuadrature` and `gaussNodes`, as `gaussQuadrature` is, and
is defined for every measure, every prescribed node and every $k$.

For a finite measure $\mu$ supported in $[a, b]$ and $c \in \{a, b\}$, the Radau rule with
prescribed node $c$ and $k$ free nodes integrates every polynomial of degree at most $2k$
exactly (it matches the first $2k + 1$ moments of $\mu$), is the only measure on $c$ and at most
$k$ further points that does, and has the remainder
$$\int f\,d\mu - \int f\,d\,\mathsf{radauQuadrature}(\mu, c, k) =
\frac{f^{(2k+1)}(\xi)}{(2k+1)!}\int(x - c)\,\tilde\pi_k(x)^2\,d\mu(x)\,,$$
$\tilde\pi_k$ the orthogonal polynomial of `radauMeasure μ c`. At $c = a$ the weight is
nonnegative and at $c = b$ nonpositive, which gives the four one-sided bounds. The Lobatto rule
is in `NLAlib.Polynomial.Orthogonal.Lobatto` and the Radau Jacobi matrix in
`NLAlib.Polynomial.Orthogonal.RadauJacobi`.

## Main definitions

* `NLAlib.radauMeasure`, `NLAlib.radauNodes`, `NLAlib.radauQuadrature`: the Radau rule.

## Main results

* `NLAlib.matchesMoments_radauQuadrature`, `NLAlib.MatchesMoments.eq_radauQuadrature`: Radau
  exactness and uniqueness.
* `NLAlib.integral_eval_basis_radauNodes_nonneg`: nonnegative weights.
* `NLAlib.exists_integral_sub_integral_radauQuadrature_eq`: the Radau remainder.
* `NLAlib.integral_radauQuadrature_le_integral_of_iteratedDeriv_nonneg` and its three siblings:
  the Radau bounds.
* `NLAlib.ae_eq_zero_of_integral_mul_sub_eq_zero`, `NLAlib.integral_eval_basis_nonneg_of_exact`:
  the endpoint-factor and weight-sign steps shared with the Lobatto rule.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-! ### The Gauss–Radau rule -/

/-- The **Radau modified measure** $\lvert x - c\rvert\,d\mu(x)$. For $\mu$ supported in
$[a, b]$ it is $(x - a)\,d\mu$ at $c = a$ and $(b - x)\,d\mu$ at $c = b$; its orthogonal
polynomials give the free nodes of the Radau rule with prescribed node $c$. -/
noncomputable def radauMeasure (μ : Measure ℝ) (c : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ‖x - c‖ₑ

/-- The **nodes of the Radau rule** with prescribed node $c$ and $k$ free nodes: $c$ and the
Gauss nodes of order $k$ of `radauMeasure μ c`. For $\mu$ supported in $[a, b]$ and
$c \in \{a, b\}$ there are $k + 1$ of them when the modified measure is positive definite up to
degree $k$; otherwise there may be fewer, and the rule is $\mu$ itself. -/
noncomputable def radauNodes (μ : Measure ℝ) (c : ℝ) (k : ℕ) : Finset ℝ :=
  insert c (gaussNodes (radauMeasure μ c) k)

/-- The **Gauss–Radau rule** of $\mu$ with prescribed node $c$ and $k$ free nodes: the
interpolatory rule of $\mu$ at `radauNodes μ c k`. For $\mu$ supported in $[a, b]$ and
$c \in \{a, b\}$ it matches the first $2k + 1$ moments of $\mu$. Junk: for $c$ inside the
support it is still a measure on at most $k + 1$ points, with no exactness claimed. -/
noncomputable def radauQuadrature (μ : Measure ℝ) (c : ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (radauNodes μ c k)

/-- The Radau rule is a finite measure. -/
instance isFiniteMeasure_radauQuadrature (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    IsFiniteMeasure (radauQuadrature μ c k) := by
  unfold radauQuadrature
  infer_instance

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] {a b c : ℝ}

/-! ### The Radau modified measure -/

/-- Integrals against the Radau modified measure: for every measure $\mu$ on $\mathbb{R}$, every
$c$ and every $g : \mathbb{R} \to \mathbb{R}$,
$\int g\,d\,\mathsf{radauMeasure}(\mu, c) = \int\lvert x - c\rvert\,g(x)\,d\mu(x)$. -/
theorem integral_radauMeasure (μ : Measure ℝ) (c : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂radauMeasure μ c = ∫ x, |x - c| * g x ∂μ := by
  unfold radauMeasure
  have hd : (fun x : ℝ => ‖x - c‖ₑ) = fun x => ((‖x - c‖₊ : NNReal) : ENNReal) :=
    funext fun x => enorm_eq_nnnorm _
  rw [hd, integral_withDensity_eq_integral_smul
    (f := fun x : ℝ => ‖x - c‖₊) (measurable_nnnorm.comp (measurable_id.sub_const c))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, coe_nnnorm, Real.norm_eq_abs, mul_comm]

/-- The Radau modified measure of a finite measure supported in $[a, b]$ is finite. -/
theorem isFiniteMeasure_radauMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (c : ℝ) :
    IsFiniteMeasure (radauMeasure μ c) :=
  isFiniteMeasure_withDensity ((integrable_eval_of_ae_mem_Icc hμ (X - C c)).congr
    (ae_of_all μ fun x => by simp) : Integrable (fun x => x - c) μ).2.ne

omit [IsFiniteMeasure μ] in
/-- The Radau modified measure lives where $\mu$ does: for $\mu$ supported in $[a, b]$ and every
$c$, almost every point of `radauMeasure μ c` lies in $[a, b]$. -/
theorem ae_mem_Icc_radauMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (c : ℝ) :
    ∀ᵐ x ∂radauMeasure μ c, x ∈ Set.Icc a b := by
  unfold radauMeasure
  exact (withDensity_absolutelyContinuous μ _).ae_le hμ

/-! ### Radau exactness -/

/-- A one-signed factor at an endpoint: for $\mu$ supported in $[a, b]$, $t \in \{a, b\}$ and a
continuous $F \ge 0$ with $F(t) = 0$, if $\int F(x)(x - t)\,d\mu = 0$ then $F = 0$
$\mu$-almost everywhere. -/
theorem ae_eq_zero_of_integral_mul_sub_eq_zero (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {t : ℝ} (ht : t = a ∨ t = b) {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x)
    (hFt : F t = 0) (h : ∫ x, F x * (x - t) ∂μ = 0) :
    ∀ᵐ x ∂μ, F x = 0 := by
  have hint : Integrable (fun x => F x * (x - t)) μ :=
    (by fun_prop : Continuous fun x => F x * (x - t)).continuousOn.integrable_of_ae_mem_Icc hμ
  have hz : ∀ᵐ x ∂μ, F x * (x - t) = 0 := by
    rcases ht with rfl | rfl
    · refine (integral_eq_zero_iff_of_nonneg_ae ?_ hint).mp h
      filter_upwards [hμ] with x hx using mul_nonneg (hF0 x) (sub_nonneg.2 hx.1)
    · have hn : ∀ᵐ x ∂μ, 0 ≤ -(F x * (x - t)) := by
        filter_upwards [hμ] with x hx
        exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (hF0 x) (sub_nonpos.2 hx.2))
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hn hint.neg).mp
        (by rw [integral_neg, h, neg_zero])] with x hx
      exact neg_eq_zero.mp hx
  filter_upwards [hz] with x hx
  rcases mul_eq_zero.mp hx with hx | hx
  · exact hx
  · rwa [sub_eq_zero.mp hx]

/-- The prescribed node is not a free node: if $\mu$, finite and supported in $[a, b]$, has a
Radau modified measure at $c \in \{a, b\}$ that is positive definite up to degree $k$, then $c$
is not a Gauss node of order $k$ of `radauMeasure μ c`. -/
theorem IsMomentPosDef.notMem_gaussNodes_radauMeasure {k : ℕ}
    (h : IsMomentPosDef (radauMeasure μ c) k) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hc : c = a ∨ c = b) : c ∉ gaussNodes (radauMeasure μ c) k := by
  have := isFiniteMeasure_radauMeasure hμ c
  intro hmem
  obtain ⟨g, hg0, hgdeg, hπ⟩ :=
    exists_orthogonalPolynomial_eq_X_sub_C_mul (mem_gaussNodes.mp hmem)
  have hO := isOrthogonalPolynomial_orthogonalPolynomial (ae_mem_Icc_radauMeasure hμ c) k g hgdeg
  rw [integral_radauMeasure, hπ] at hO
  refine (h g hg0 hgdeg).ne' ?_
  rw [integral_radauMeasure]
  refine integral_eq_zero_of_ae (ae_eq_zero_of_integral_mul_sub_eq_zero hμ hc
    (F := fun x => |x - c| * g.eval x ^ 2) (by fun_prop) (fun x => by positivity) (by simp) ?_)
  rw [← hO]
  congr 1 with x
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  ring

/-- The number of Radau nodes: if $\mu$, finite and supported in $[a, b]$, has a Radau modified
measure at $c \in \{a, b\}$ positive definite up to degree $k$, then the Radau rule has
$k + 1$ nodes. -/
theorem IsMomentPosDef.card_radauNodes {k : ℕ} (h : IsMomentPosDef (radauMeasure μ c) k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) : (radauNodes μ c k).card = k + 1 := by
  have := isFiniteMeasure_radauMeasure hμ c
  unfold radauNodes
  rw [Finset.card_insert_of_notMem (h.notMem_gaussNodes_radauMeasure hμ hc),
    IsMomentPosDef.card_gaussNodes h (ae_mem_Icc_radauMeasure hμ c)]

omit [IsFiniteMeasure μ] in
/-- The sign of $x - c$: for $\mu$ supported in $[a, b]$ and $c \in \{a, b\}$ there is a constant
$s$ ($1$ at $c = a$, $-1$ at $c = b$) with
$\int(x - c)g(x)\,d\mu = s\int g\,d\,\mathsf{radauMeasure}(\mu, c)$ for every $g$. -/
private theorem exists_integral_sub_mul_eq_mul_integral_radauMeasure
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) :
    ∃ s : ℝ, ∀ g : ℝ → ℝ, ∫ x, (x - c) * g x ∂μ = s * ∫ x, g x ∂radauMeasure μ c := by
  simp only [integral_radauMeasure]
  rcases hc with rfl | rfl
  · refine ⟨1, fun g => ?_⟩
    rw [one_mul]
    refine integral_congr_ae ?_
    filter_upwards [hμ] with x hx
    rw [abs_of_nonneg (sub_nonneg.2 hx.1)]
  · refine ⟨-1, fun g => ?_⟩
    rw [neg_one_mul, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hμ] with x hx
    rw [abs_of_nonpos (sub_nonpos.2 hx.2)]
    ring

/-- **The Radau nodal polynomial is orthogonal**: if $\mu$, finite and supported in $[a, b]$,
has a Radau modified measure at $c \in \{a, b\}$ positive definite up to degree $k$, then
$\prod_{x\in R}(x - y)$ over the Radau nodes $R$ is orthogonal in $L^2(\mu)$ to the polynomials
of degree less than $k$. [Gautschi2004, §1.4.2, (1.4.21)]. -/
theorem isOrthogonalPolynomial_nodal_radauNodes (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hc : c = a ∨ c = b) {k : ℕ} (h : IsMomentPosDef (radauMeasure μ c) k) :
    IsOrthogonalPolynomial μ k (Lagrange.nodal (radauNodes μ c k) id) := by
  have hν := ae_mem_Icc_radauMeasure hμ c
  have := isFiniteMeasure_radauMeasure hμ c
  have hnodal : Lagrange.nodal (radauNodes μ c k) id =
      (X - C c) * orthogonalPolynomial (radauMeasure μ c) k := by
    rw [radauNodes, Lagrange.nodal_insert_eq_nodal (h.notMem_gaussNodes_radauMeasure hμ hc),
      h.nodal_gaussNodes hν]
    rfl
  obtain ⟨s, hs⟩ := exists_integral_sub_mul_eq_mul_integral_radauMeasure hμ hc
  intro r hr
  simp only [hnodal, eval_mul, eval_sub, eval_X, eval_C, mul_assoc]
  rw [hs, isOrthogonalPolynomial_orthogonalPolynomial hν k r hr, mul_zero]

omit [IsFiniteMeasure μ] in
/-- Where the Radau density vanishes: if `radauMeasure μ c` is carried by its Gauss nodes of
order $k$, then $\mu$ is carried by the Radau nodes (the density vanishes only at $c$). -/
private theorem ae_mem_radauNodes_of_ae_mem_gaussNodes {k : ℕ}
    (hG : ∀ᵐ x ∂radauMeasure μ c, x ∈ gaussNodes (radauMeasure μ c) k) :
    ∀ᵐ x ∂μ, x ∈ radauNodes μ c k := by
  filter_upwards [(ae_withDensity_iff (by fun_prop)).mp hG] with x hx
  by_cases hxc : x = c
  · simp [radauNodes, hxc]
  · exact Finset.mem_insert_of_mem (hx (by simpa [sub_eq_zero] using hxc))

/-- The terminating case of the Radau rule: if the orthogonal polynomial $\tilde\pi_k$ of the
Radau modified measure of $\mu$ at $c$ has norm $0$ there, for $\mu$ finite and supported in
$[a, b]$, then the Radau rule is $\mu$ itself. Covers the case that the modified measure is not
positive definite up to degree $k$ (then $\tilde\pi_k$ has norm $0$ by `isMomentPosDef_succ_iff`
and `IsMomentPosDef.mono`). -/
theorem radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ∫ x, (orthogonalPolynomial (radauMeasure μ c) k).eval x ^ 2 ∂radauMeasure μ c = 0) :
    radauQuadrature μ c k = μ := by
  have := isFiniteMeasure_radauMeasure hμ c
  refine interpolatoryQuadrature_eq_self_of_ae_mem (ae_mem_radauNodes_of_ae_mem_gaussNodes ?_)
  filter_upwards [ae_eval_eq_zero_of_integral_sq_eq_zero (ae_mem_Icc_radauMeasure hμ c) h]
    with x hx
  exact mem_gaussNodes.mpr hx

/-- The degenerate Radau case: if `radauMeasure μ c` is not positive definite up to degree $k$,
then $\mu$, finite and supported in $[a, b]$, is carried by the Radau nodes. -/
private theorem ae_mem_radauNodes_of_not_isMomentPosDef (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {k : ℕ} (h : ¬IsMomentPosDef (radauMeasure μ c) k) : ∀ᵐ x ∂μ, x ∈ radauNodes μ c k := by
  have := isFiniteMeasure_radauMeasure hμ c
  exact ae_mem_radauNodes_of_ae_mem_gaussNodes
    (ae_mem_gaussNodes_of_not_isMomentPosDef (ae_mem_Icc_radauMeasure hμ c) h)

/-- Exactness at a node: if $p$ is nonnegative on $[a, b]$, vanishes at the other nodes of $s$
and is positive at $x \in s$, and the nodal polynomial of $s$ is orthogonal of order $m$ with
$\deg p < \lvert s\rvert + m$, then $\int\ell_x\,d\mu \ge 0$. -/
theorem integral_eval_basis_nonneg_of_exact (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {s : Finset ℝ} {m : ℕ} (hs : IsOrthogonalPolynomial μ m (Lagrange.nodal s id))
    {x : ℝ} (hx : x ∈ s) {p : ℝ[X]} (hdeg : p.natDegree < s.card + m)
    (hp : ∀ t ∈ Set.Icc a b, 0 ≤ p.eval t) (h0 : ∀ y ∈ s, y ≠ x → p.eval y = 0)
    (hpos : 0 < p.eval x) : 0 ≤ ∫ t, (Lagrange.basis s id x).eval t ∂μ := by
  have hex := hs.integral_eval_eq_sum_of_degree_lt_card_add hμ
    (degree_le_natDegree.trans_lt (by exact_mod_cast hdeg))
  rw [Finset.sum_eq_single x (fun y hy hne => by rw [h0 y hy hne, mul_zero])
    (fun hn => absurd hx hn)] at hex
  have hnn : 0 ≤ ∫ t, p.eval t ∂μ := integral_nonneg_of_ae (hμ.mono fun t ht => hp t ht)
  rw [hex] at hnn
  exact nonneg_of_mul_nonneg_left hnn hpos

/-- **The Radau weights are nonnegative**: for a finite measure $\mu$ supported in $[a, b]$,
$c \in \{a, b\}$ and every $k$, the interpolatory weight $\int\ell_x\,d\mu$ of every Radau
node $x$ is nonnegative, $\ell_x$ its Lagrange basis polynomial. [Gautschi2004, Theorem 3.2];
there positive, for $\mu$ with more than $k$ support points. -/
theorem integral_eval_basis_radauNodes_nonneg (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hc : c = a ∨ c = b) (k : ℕ) {x : ℝ} (hx : x ∈ radauNodes μ c k) :
    0 ≤ ∫ t, (Lagrange.basis (radauNodes μ c k) id x).eval t ∂μ := by
  by_cases hp : IsMomentPosDef (radauMeasure μ c) k
  · -- $p = \ell_x^2$, of degree $2k < \lvert R\rvert + k$
    set ℓ := Lagrange.basis (radauNodes μ c k) id x
    have hℓ : ℓ.natDegree = (radauNodes μ c k).card - 1 :=
      Lagrange.natDegree_basis (Set.injOn_id _) hx
    have hℓx : ℓ.eval x = 1 := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hx
    refine integral_eval_basis_nonneg_of_exact hμ (isOrthogonalPolynomial_nodal_radauNodes hμ hc hp)
      hx (p := ℓ ^ 2) ?_ (fun t _ => by rw [eval_pow]; positivity) (fun y hy hyx => ?_)
      (by rw [eval_pow, hℓx]; norm_num)
    · have := natDegree_pow_le (p := ℓ) (n := 2)
      have := hp.card_radauNodes hμ hc
      omega
    · have hℓy : ℓ.eval y = 0 := Lagrange.eval_basis_of_ne (v := id) hyx.symm hy
      rw [eval_pow, hℓy, zero_pow two_ne_zero]
  · rw [integral_eval_basis_of_ae_mem (ae_mem_radauNodes_of_not_isMomentPosDef hμ hp) hx]
    exact measureReal_nonneg

/-- The Radau rule with the interpolatory weights: for a finite measure $\mu$ supported in
$[a, b]$, $c \in \{a, b\}$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu, c, k) =
\sum_{x\in R}\Bigl(\int\ell_x\,d\mu\Bigr)f(x)\,,$$
$R$ the Radau nodes and $\ell_x$ their Lagrange basis polynomials. -/
theorem integral_radauQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) (k : ℕ)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂radauQuadrature μ c k =
      ∑ x ∈ radauNodes μ c k, (∫ t, (Lagrange.basis (radauNodes μ c k) id x).eval t ∂μ) * f x := by
  unfold radauQuadrature interpolatoryQuadrature
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (integral_eval_basis_radauNodes_nonneg hμ hc k hx)]
  · intro x _
    exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- **Gauss–Radau quadrature**: for a finite measure $\mu$ supported in $[a, b]$,
$c \in \{a, b\}$ and every $k$, the Radau rule with prescribed node $c$ and $k$ free nodes
matches the first $2k + 1$ moments of $\mu$: it integrates every real polynomial of degree at
most $2k$ exactly. [Gautschi2004, §1.4.2, (1.4.21)]; [GolubMeurant2010, §6.2.2];
there for $\mu$ with more than $k$ support points; otherwise the rule is $\mu$ itself.
Result: gauss-radau-quadrature -/
theorem matchesMoments_radauQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    (k : ℕ) : MatchesMoments μ (radauQuadrature μ c k) (2 * k + 1) := by
  by_cases h : IsMomentPosDef (radauMeasure μ c) k
  · have hs := isOrthogonalPolynomial_nodal_radauNodes hμ hc h
    intro p hp
    rw [integral_radauQuadrature hμ hc k (fun x => p.eval x)]
    exact hs.integral_eval_eq_sum_of_degree_lt_card_add hμ
      (by rwa [h.card_radauNodes hμ hc, show k + 1 + k = 2 * k + 1 by ring])
  · rw [radauQuadrature, interpolatoryQuadrature_eq_self_of_ae_mem
      (ae_mem_radauNodes_of_not_isMomentPosDef hμ h)]
    exact MatchesMoments.refl _ _

/-- The Radau rule lives in every interval carrying the measure: for a finite measure $\mu$
supported in $[a, b]$, $c \in \{a, b\}$ and every $k$, almost every point of the Radau rule lies
in $[a, b]$. -/
theorem ae_mem_Icc_radauQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    (k : ℕ) : ∀ᵐ x ∂radauQuadrature μ c k, x ∈ Set.Icc a b := by
  by_cases h0 : μ = 0
  · subst h0
    simp [radauQuadrature, interpolatoryQuadrature]
  have : (ae μ).NeBot := ae_neBot.mpr h0
  obtain ⟨x0, hx0⟩ := hμ.exists
  have hab : a ≤ b := hx0.1.trans hx0.2
  have hcI : c ∈ Set.Icc a b := by
    rcases hc with h | h <;> rw [h] <;> simp [hab]
  by_cases h : IsMomentPosDef (radauMeasure μ c) k
  · have := isFiniteMeasure_radauMeasure hμ c
    filter_upwards [ae_mem_interpolatoryQuadrature μ (radauNodes μ c k)] with x hx
    simp only [radauNodes, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hcI
    · exact h.gaussNodes_subset_Icc (ae_mem_Icc_radauMeasure hμ c) (Finset.mem_coe.mpr hx)
  · rw [radauQuadrature, interpolatoryQuadrature_eq_self_of_ae_mem
      (ae_mem_radauNodes_of_not_isMomentPosDef hμ h)]
    exact hμ

/-- The mass of the Radau rule: for a finite measure $\mu$ supported in $[a, b]$,
$c \in \{a, b\}$ and every $k$, the Radau rule has mass $\mu(\mathbb{R})$. -/
theorem radauQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    (k : ℕ) : (radauQuadrature μ c k).real Set.univ = μ.real Set.univ :=
  ((matchesMoments_radauQuadrature hμ hc k).measureReal_univ_eq (by omega)).symm

/-- **Uniqueness of the Radau rule**: if a finite measure $\nu$ carried by $c$ and at most $k$
further points matches the first $2k + 1$ moments of a finite measure $\mu$ supported in
$[a, b]$, $c \in \{a, b\}$, then $\nu$ is the Radau rule of $\mu$ with prescribed node $c$ and
$k$ free nodes. [Gautschi2004, §3.1.1]; there among rules with positive
weights.
Result: gauss-radau-quadrature-uniqueness -/
theorem MatchesMoments.eq_radauQuadrature [IsFiniteMeasure ν] {k : ℕ}
    (h : MatchesMoments μ ν (2 * k + 1)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    {s : Finset ℝ} (hν : ∀ᵐ x ∂ν, x ∈ insert c s) (hs : s.card ≤ k) :
    ν = radauQuadrature μ c k := by
  have hM : MatchesMoments ν (radauQuadrature μ c k) (2 * k + 1) :=
    h.symm.trans (matchesMoments_radauQuadrature hμ hc k)
  have hνT : ∀ᵐ x ∂ν, x ∈ insert c (s ∪ gaussNodes (radauMeasure μ c) k) :=
    hν.mono fun x hx => Finset.insert_subset_insert c Finset.subset_union_left hx
  have hρT : ∀ᵐ x ∂radauQuadrature μ c k, x ∈ insert c (s ∪ gaussNodes (radauMeasure μ c) k) :=
    (ae_mem_interpolatoryQuadrature μ (radauNodes μ c k)).mono fun x hx =>
      Finset.insert_subset_insert c Finset.subset_union_right hx
  have hcard : (insert c (s ∪ gaussNodes (radauMeasure μ c) k)).card ≤ 2 * k + 1 :=
    (Finset.card_insert_le _ _).trans (by
      have := (Finset.card_union_le s _).trans (Nat.add_le_add_left
        (card_gaussNodes_le (radauMeasure μ c) k) s.card)
      omega)
  exact MatchesMoments.eq_of_ae_mem (hM.mono hcard) hνT hρT

/-! ### The Radau remainder and bounds -/

/-- **The Gauss–Radau remainder**: for a finite measure $\mu$ supported in $[a, b]$, $a < b$,
$c \in \{a, b\}$, every $k$, and $f$ continuous on $[a, b]$ and $C^{2k+1}$ on $(a, b)$, there
is $\xi \in (a, b)$ with
$$\int f\,d\mu - \int f\,d\,\mathsf{radauQuadrature}(\mu, c, k) =
\frac{f^{(2k+1)}(\xi)}{(2k+1)!}\int(x - c)\,\tilde\pi_k(x)^2\,d\mu(x)\,,$$
$\tilde\pi_k$ the monic orthogonal polynomial of degree $k$ of `radauMeasure μ c`.
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, §6.2.2].
Result: gauss-radau-remainder -/
theorem exists_integral_sub_integral_radauQuadrature_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) (hc : c = a ∨ c = b) (k : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂radauQuadrature μ c k =
      iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial *
        ∫ x, (x - c) * (orthogonalPolynomial (radauMeasure μ c) k).eval x ^ 2 ∂μ := by
  set μc := radauMeasure μ c
  have := isFiniteMeasure_radauMeasure hμ c
  have hμc : ∀ᵐ x ∂μc, x ∈ Set.Icc a b := ae_mem_Icc_radauMeasure hμ c
  set π := orthogonalPolynomial μc k
  have hπint : Integrable (fun x => (x - c) * π.eval x ^ 2) μ :=
    (integrable_eval_of_ae_mem_Icc hμ ((X - C c) * π ^ 2)).congr (ae_of_all μ fun x => by simp)
  rcases (integral_nonneg fun x => sq_nonneg (π.eval x) : 0 ≤ ∫ x, π.eval x ^ 2 ∂μc).eq_or_lt
    with h0 | hpos
  · obtain ⟨s, hs⟩ := exists_integral_sub_mul_eq_mul_integral_radauMeasure hμ hc
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero hμ h0.symm, sub_self,
      hs, ← h0, mul_zero, mul_zero]
  · have hpd : IsMomentPosDef μc (k + 1) := (isMomentPosDef_succ_iff hμc k).mpr hpos
    set G := gaussNodes μc k
    have hGI : (G : Set ℝ) ⊆ Set.Ioo a b := hpd.gaussNodes_subset_Ioo hμc
    have hcI : c ∈ Set.Icc a b := by rcases hc with rfl | rfl <;> constructor <;> linarith
    have hcG : c ∉ G := fun h => by
      rcases hc with rfl | rfl
      · exact lt_irrefl _ (hGI h).1
      · exact lt_irrefl _ (hGI h).2
    set m : Multiset ℝ := c ::ₘ (G.val + G.val)
    have hcard : m.card = 2 * k + 1 := by
      have hGk : G.card = k := (hpd.mono k.le_succ).card_gaussNodes hμc
      simp only [m, Multiset.card_cons, Multiset.card_add, Finset.card_val, hGk]
      ring
    have hmem : ∀ y ∈ m, y = c ∨ y ∈ G := fun y hy => by simpa [m] using hy
    obtain ⟨H, hHdeg, hjet⟩ :=
      exists_degree_lt_forall_iterate_derivative_eval_eq m (fun y j => iteratedDeriv j f y)
    rw [hcard] at hHdeg
    have hexact : ∫ x, f x ∂radauQuadrature μ c k = ∫ x, H.eval x ∂μ := by
      rw [matchesMoments_radauQuadrature hμ hc k H hHdeg, integral_radauQuadrature hμ hc,
        integral_radauQuadrature hμ hc]
      refine Finset.sum_congr rfl fun y hy => ?_
      have hy' : y ∈ m := by simpa [m, radauNodes] using hy
      rw [show f y = H.eval y by simpa using (hjet y hy' 0 (Multiset.count_pos.2 hy')).symm]
    have hprod : (m.map fun y => X - C y).prod = (X - C c) * π ^ 2 := by
      have hnod : Lagrange.nodal G id = π := (hpd.mono k.le_succ).nodal_gaussNodes hμc
      rw [← hnod]
      simp only [m, Lagrange.nodal, Multiset.map_cons, Multiset.prod_cons, Multiset.map_add,
        Multiset.prod_add, Finset.prod_eq_multiset_prod, id, sq]
    rw [hexact]
    refine exists_integral_sub_integral_eval_eq hμ hab hf hf' hπint ?_ fun x hx => ?_
    · rcases hc with rfl | rfl
      · exact .inl (hμ.mono fun x hx => mul_nonneg (sub_nonneg.2 hx.1) (sq_nonneg _))
      · exact .inr (hμ.mono fun x hx =>
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx.2) (sq_nonneg _))
    obtain ⟨ξ, hξ, h⟩ := exists_sub_eval_eq_iteratedDeriv_mul hab (Multiset.cons_ne_zero)
      (fun y hy => (hmem y hy).elim (fun h => h ▸ hcI) fun h => Set.Ioo_subset_Icc_self (hGI h))
      (fun y hy h => by
        rcases hmem y hy with rfl | hyG
        · simp [Multiset.count_eq_zero.mpr (show y ∉ G.val from hcG)] at h
        · exact hGI hyG) hf (hcard ▸ hf') (hcard ▸ hHdeg) hjet hx
    refine ⟨ξ, hξ, ?_⟩
    rw [h, hprod, hcard]
    simp

/-- **The left Radau rule is a lower bound** for $f$ with nonnegative derivative of order
$2k + 1$: for a finite measure $\mu$ supported in $[a, b]$, $a < b$, every $k$, and $f$
continuous on $[a, b]$, $C^{2k+1}$ on $(a, b)$ with $f^{(2k+1)} \ge 0$ there,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu, a, k) \le \int f\,d\mu\,.$$
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, §6.2.2]. -/
theorem integral_radauQuadrature_le_integral_of_iteratedDeriv_nonneg
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv (2 * k + 1) f x) :
    ∫ x, f x ∂radauQuadrature μ a k ≤ ∫ x, f x ∂μ := by
  obtain ⟨ξ, hξ, h⟩ :=
    exists_integral_sub_integral_radauQuadrature_eq hμ hab (Or.inl rfl) k hf hf'
  have hW : 0 ≤ ∫ x, (x - a) * (orthogonalPolynomial (radauMeasure μ a) k).eval x ^ 2 ∂μ :=
    integral_nonneg_of_ae (by
      filter_upwards [hμ] with x hx
      exact mul_nonneg (by linarith [hx.1]) (sq_nonneg _))
  have hR : 0 ≤ iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial *
      ∫ x, (x - a) * (orthogonalPolynomial (radauMeasure μ a) k).eval x ^ 2 ∂μ :=
    mul_nonneg (div_nonneg (hD ξ hξ) (Nat.cast_nonneg _)) hW
  linarith

/-- **The left Radau rule is an upper bound** for $f$ with nonpositive derivative of order
$2k + 1$ (such as $x \mapsto x^{-1}$ on $[a, b]$, $a > 0$): for a finite measure $\mu$
supported in $[a, b]$, $a < b$, every $k$, and $f$ continuous on $[a, b]$, $C^{2k+1}$ on
$(a, b)$ with $f^{(2k+1)} \le 0$ there,
$$\int f\,d\mu \le \int f\,d\,\mathsf{radauQuadrature}(\mu, a, k)\,.$$
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, §6.2.2]. -/
theorem integral_le_integral_radauQuadrature_of_iteratedDeriv_nonpos
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, iteratedDeriv (2 * k + 1) f x ≤ 0) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂radauQuadrature μ a k := by
  obtain ⟨ξ, hξ, heq⟩ :=
    exists_integral_sub_integral_radauQuadrature_eq hμ hab (Or.inl rfl) k hf hf'
  have hW : 0 ≤ ∫ x, (x - a) * (orthogonalPolynomial (radauMeasure μ a) k).eval x ^ 2 ∂μ :=
    integral_nonneg_of_ae (hμ.mono fun x hx => mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _))
  have hq : iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (hD ξ hξ) (Nat.cast_nonneg _)
  have hprod := mul_nonpos_of_nonpos_of_nonneg hq hW
  linarith

/-- **The right Radau rule is an upper bound** for $f$ with nonnegative derivative of order
$2k + 1$: for a finite measure $\mu$ supported in $[a, b]$, $a < b$, every $k$, and $f$
continuous on $[a, b]$, $C^{2k+1}$ on $(a, b)$ with $f^{(2k+1)} \ge 0$ there,
$$\int f\,d\mu \le \int f\,d\,\mathsf{radauQuadrature}(\mu, b, k)\,.$$
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, §6.2.2]. -/
theorem integral_le_integral_radauQuadrature_of_iteratedDeriv_nonneg
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv (2 * k + 1) f x) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂radauQuadrature μ b k := by
  obtain ⟨ξ, hξ, h⟩ :=
    exists_integral_sub_integral_radauQuadrature_eq hμ hab (Or.inr rfl) k hf hf'
  have hW : ∫ x, (x - b) * (orthogonalPolynomial (radauMeasure μ b) k).eval x ^ 2 ∂μ ≤ 0 :=
    integral_nonpos_of_ae (hμ.mono fun x hx =>
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _))
  linarith [mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hD ξ hξ) (Nat.cast_nonneg (2 * k + 1).factorial)) hW]

/-- **The right Radau rule is a lower bound** for $f$ with nonpositive derivative of order
$2k + 1$ (such as $x \mapsto x^{-1}$ on $[a, b]$, $a > 0$): for a finite measure $\mu$
supported in $[a, b]$, $a < b$, every $k$, and $f$ continuous on $[a, b]$, $C^{2k+1}$ on
$(a, b)$ with $f^{(2k+1)} \le 0$ there,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu, b, k) \le \int f\,d\mu\,.$$
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, §6.2.2]. -/
theorem integral_radauQuadrature_le_integral_of_iteratedDeriv_nonpos
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, iteratedDeriv (2 * k + 1) f x ≤ 0) :
    ∫ x, f x ∂radauQuadrature μ b k ≤ ∫ x, f x ∂μ := by
  obtain ⟨ξ, hξ, h⟩ :=
    exists_integral_sub_integral_radauQuadrature_eq hμ hab (Or.inr rfl) k hf hf'
  have hW : ∫ x, (x - b) * (orthogonalPolynomial (radauMeasure μ b) k).eval x ^ 2 ∂μ ≤ 0 :=
    integral_nonpos_of_ae (hμ.mono fun x hx =>
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _))
  linarith [mul_nonneg_of_nonpos_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (hD ξ hξ) (Nat.cast_nonneg (2 * k + 1).factorial)) hW]

end NLAlib
