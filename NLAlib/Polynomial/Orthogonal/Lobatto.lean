/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Radau

/-!
# Gauss–Lobatto rules

The Gauss–Lobatto rule of a measure $\mu$ on $[a, b]$ prescribes both endpoints $a$ and $b$, puts
$k$ free nodes at the zeros of the orthogonal polynomial of the modified measure
$\lvert(x - a)(x - b)\rvert\,d\mu(x)$ (`lobattoMeasure`), and takes interpolatory weights at the
$k + 2$ nodes. Like the Radau rule (`NLAlib.Polynomial.Orthogonal.Radau`), whose endpoint and
weight steps it reuses, it is defined for every measure, all $a, b$ and every $k$.

For a finite measure $\mu$ supported in $[a, b]$ and $a < b$, the Lobatto rule integrates every
polynomial of degree at most $2k + 1$ exactly (it matches $2k + 2$ moments), and its remainder
is $f^{(2k+2)}(\xi)/(2k+2)!$ times $\int(x - a)(x - b)\hat\pi_k(x)^2\,d\mu(x)$, a nonpositive
weight, which gives two one-sided bounds.

## Main definitions

* `NLAlib.lobattoMeasure`, `NLAlib.lobattoNodes`, `NLAlib.lobattoQuadrature`: the Lobatto rule.

## Main results

* `NLAlib.integral_eval_basis_lobattoNodes_nonneg`: nonnegative weights.
* `NLAlib.matchesMoments_lobattoQuadrature`,
  `NLAlib.exists_integral_sub_integral_lobattoQuadrature_eq`: Lobatto exactness and remainder,
  with two bounds.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-! ### The Gauss–Lobatto rule -/

/-- The **Lobatto modified measure** $\lvert(x - a)(x - b)\rvert\,d\mu(x)$; for $\mu$ supported
in $[a, b]$ it is $(x - a)(b - x)\,d\mu$. -/
noncomputable def lobattoMeasure (μ : Measure ℝ) (a b : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ‖(x - a) * (x - b)‖ₑ

/-- The **nodes of the Lobatto rule** on $[a, b]$ with $k$ free nodes: $a$, $b$ and the Gauss
nodes of order $k$ of `lobattoMeasure μ a b`. -/
noncomputable def lobattoNodes (μ : Measure ℝ) (a b : ℝ) (k : ℕ) : Finset ℝ :=
  insert a (insert b (gaussNodes (lobattoMeasure μ a b) k))

/-- The **Gauss–Lobatto rule** of $\mu$ on $[a, b]$ with $k$ free nodes: the interpolatory rule
of $\mu$ at `lobattoNodes μ a b k`. For $\mu$ supported in $[a, b]$, $a < b$, it matches the
first $2k + 2$ moments of $\mu$. -/
noncomputable def lobattoQuadrature (μ : Measure ℝ) (a b : ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (lobattoNodes μ a b k)

/-- The Lobatto rule is a finite measure. -/
instance isFiniteMeasure_lobattoQuadrature (μ : Measure ℝ) (a b : ℝ) (k : ℕ) :
    IsFiniteMeasure (lobattoQuadrature μ a b k) := by
  unfold lobattoQuadrature
  infer_instance

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] {a b c : ℝ}

/-! ### The Lobatto rule -/

/-- Integrals against the Lobatto modified measure: for every measure $\mu$ on $\mathbb{R}$,
all $a, b$ and every $g : \mathbb{R} \to \mathbb{R}$,
$\int g\,d\,\mathsf{lobattoMeasure}(\mu, a, b) = \int\lvert(x - a)(x - b)\rvert\,g(x)\,d\mu(x)$. -/
theorem integral_lobattoMeasure (μ : Measure ℝ) (a b : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂lobattoMeasure μ a b = ∫ x, |(x - a) * (x - b)| * g x ∂μ := by
  unfold lobattoMeasure
  rw [show (fun x : ℝ => ‖(x - a) * (x - b)‖ₑ) =
      fun x => ((‖(x - a) * (x - b)‖₊ : NNReal) : ENNReal) from funext fun x => enorm_eq_nnnorm _,
    integral_withDensity_eq_integral_smul (f := fun x : ℝ => ‖(x - a) * (x - b)‖₊) (by fun_prop)]
  simp [NNReal.smul_def, Real.norm_eq_abs, abs_mul, smul_eq_mul, mul_comm]

/-- The Lobatto modified measure of a finite measure supported in $[a, b]$ is finite. -/
theorem isFiniteMeasure_lobattoMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    IsFiniteMeasure (lobattoMeasure μ a b) :=
  isFiniteMeasure_withDensity ((integrable_eval_of_ae_mem_Icc hμ ((X - C a) * (X - C b))).congr
    (ae_of_all μ fun x => by simp) : Integrable (fun x => (x - a) * (x - b)) μ).2.ne

omit [IsFiniteMeasure μ] in
/-- The Lobatto modified measure lives where $\mu$ does: for $\mu$ supported in $[a, b]$, almost
every point of `lobattoMeasure μ a b` lies in $[a, b]$. -/
theorem ae_mem_Icc_lobattoMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    ∀ᵐ x ∂lobattoMeasure μ a b, x ∈ Set.Icc a b :=
  (withDensity_absolutelyContinuous μ _).ae_le hμ

/-- The endpoints are not free Lobatto nodes: if $\mu$, finite and supported in $[a, b]$, has a
Lobatto modified measure positive definite up to degree $k$, then neither endpoint
$t \in \{a, b\}$ is a Gauss node of order $k$ of `lobattoMeasure μ a b`. -/
theorem IsMomentPosDef.notMem_gaussNodes_lobattoMeasure {k : ℕ}
    (h : IsMomentPosDef (lobattoMeasure μ a b) k) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {t : ℝ}
    (ht : t = a ∨ t = b) : t ∉ gaussNodes (lobattoMeasure μ a b) k := by
  have := isFiniteMeasure_lobattoMeasure hμ
  intro hmem
  obtain ⟨r, hr0, hrdeg, hπ⟩ :=
    exists_orthogonalPolynomial_eq_X_sub_C_mul (mem_gaussNodes.mp hmem)
  have hO := isOrthogonalPolynomial_orthogonalPolynomial (ae_mem_Icc_lobattoMeasure hμ) k r hrdeg
  rw [integral_lobattoMeasure, hπ] at hO
  refine (h r hr0 hrdeg).ne' ?_
  rw [integral_lobattoMeasure]
  refine integral_eq_zero_of_ae (ae_eq_zero_of_integral_mul_sub_eq_zero hμ ht
    (F := fun x => |(x - a) * (x - b)| * r.eval x ^ 2) (by fun_prop) (fun x => by positivity)
    (by rcases ht with rfl | rfl <;> simp) ?_)
  rw [← hO]
  congr 1 with x
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  ring

/-- The endpoints are not free Lobatto nodes, in the form the node count needs. -/
private theorem IsMomentPosDef.notMem_insert_gaussNodes_lobattoMeasure {k : ℕ}
    (h : IsMomentPosDef (lobattoMeasure μ a b) k) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) :
    a ∉ insert b (gaussNodes (lobattoMeasure μ a b) k) ∧ b ∉ gaussNodes (lobattoMeasure μ a b) k :=
  ⟨Finset.mem_insert.not.2 (not_or.2 ⟨hab.ne, h.notMem_gaussNodes_lobattoMeasure hμ (.inl rfl)⟩),
    h.notMem_gaussNodes_lobattoMeasure hμ (.inr rfl)⟩

/-- The number of Lobatto nodes: if $\mu$, finite and supported in $[a, b]$, $a < b$, has a
Lobatto modified measure positive definite up to degree $k$, the Lobatto rule has $k + 2$
nodes. -/
theorem IsMomentPosDef.card_lobattoNodes {k : ℕ} (h : IsMomentPosDef (lobattoMeasure μ a b) k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) : (lobattoNodes μ a b k).card = k + 2 := by
  have := isFiniteMeasure_lobattoMeasure hμ
  obtain ⟨ha, hb⟩ := h.notMem_insert_gaussNodes_lobattoMeasure hμ hab
  rw [lobattoNodes, Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
    h.card_gaussNodes (ae_mem_Icc_lobattoMeasure hμ)]

omit [IsFiniteMeasure μ] in
/-- The sign of $(x - a)(x - b)$: for $\mu$ supported in $[a, b]$ and every $g$,
$\int(x - a)(x - b)g(x)\,d\mu = -\int g\,d\,\mathsf{lobattoMeasure}(\mu, a, b)$. -/
private theorem integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (g : ℝ → ℝ) :
    ∫ x, (x - a) * (x - b) * g x ∂μ = -∫ x, g x ∂lobattoMeasure μ a b := by
  rw [integral_lobattoMeasure, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hμ] with x hx
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hx.1) (sub_nonpos.2 hx.2))]
  ring

/-- **The Lobatto nodal polynomial is orthogonal**: if $\mu$, finite and supported in $[a, b]$,
$a < b$, has a Lobatto modified measure positive definite up to degree $k$, then the nodal
polynomial of the Lobatto nodes is orthogonal in $L^2(\mu)$ to the polynomials of degree less
than $k$. [Gautschi2004, §1.4.2, (1.4.22)]. -/
theorem isOrthogonalPolynomial_nodal_lobattoNodes (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b)
    {k : ℕ} (h : IsMomentPosDef (lobattoMeasure μ a b) k) :
    IsOrthogonalPolynomial μ k (Lagrange.nodal (lobattoNodes μ a b k) id) := by
  have := isFiniteMeasure_lobattoMeasure hμ
  have hν := ae_mem_Icc_lobattoMeasure hμ
  obtain ⟨ha, hb⟩ := h.notMem_insert_gaussNodes_lobattoMeasure hμ hab
  have hnodal : Lagrange.nodal (lobattoNodes μ a b k) id =
      (X - C a) * ((X - C b) * orthogonalPolynomial (lobattoMeasure μ a b) k) := by
    rw [lobattoNodes, Lagrange.nodal_insert_eq_nodal ha, Lagrange.nodal_insert_eq_nodal hb,
      h.nodal_gaussNodes hν]
    rfl
  intro r hr
  have hs := integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure hμ
    fun x => (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x * r.eval x
  simp only [mul_assoc] at hs
  simp only [hnodal, eval_mul, eval_sub, eval_X, eval_C, mul_assoc]
  rw [hs, isOrthogonalPolynomial_orthogonalPolynomial hν k r hr, neg_zero]

omit [IsFiniteMeasure μ] in
/-- Where the Lobatto density vanishes: if `lobattoMeasure μ a b` is carried by its Gauss nodes
of order $k$, then $\mu$ is carried by the Lobatto nodes (the density vanishes only at $a$
and $b$). -/
private theorem ae_mem_lobattoNodes_of_ae_mem_gaussNodes {k : ℕ}
    (hG : ∀ᵐ x ∂lobattoMeasure μ a b, x ∈ gaussNodes (lobattoMeasure μ a b) k) :
    ∀ᵐ x ∂μ, x ∈ lobattoNodes μ a b k := by
  filter_upwards [(ae_withDensity_iff (by fun_prop)).mp hG] with x hx
  by_cases hxab : x = a ∨ x = b
  · rcases hxab with rfl | rfl <;> simp [lobattoNodes]
  · have hne : ‖(x - a) * (x - b)‖ₑ ≠ 0 := by
      simpa [sub_eq_zero] using hxab
    simp [lobattoNodes, hx hne]

/-- The terminating case of the Lobatto rule: if the orthogonal polynomial $\hat\pi_k$ of the
Lobatto modified measure has norm $0$ there, for $\mu$ finite and supported in $[a, b]$, then
the Lobatto rule is $\mu$ itself. -/
theorem lobattoQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ∫ x, (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂lobattoMeasure μ a b =
      0) :
    lobattoQuadrature μ a b k = μ := by
  have := isFiniteMeasure_lobattoMeasure hμ
  refine interpolatoryQuadrature_eq_self_of_ae_mem (ae_mem_lobattoNodes_of_ae_mem_gaussNodes ?_)
  filter_upwards [ae_eval_eq_zero_of_integral_sq_eq_zero (ae_mem_Icc_lobattoMeasure hμ) h]
    with x hx
  exact mem_gaussNodes.mpr hx

/-- The degenerate Lobatto case: if `lobattoMeasure μ a b` is not positive definite up to degree
$k$, then $\mu$, finite and supported in $[a, b]$, is carried by the Lobatto nodes. -/
private theorem ae_mem_lobattoNodes_of_not_isMomentPosDef (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {k : ℕ} (h : ¬IsMomentPosDef (lobattoMeasure μ a b) k) :
    ∀ᵐ x ∂μ, x ∈ lobattoNodes μ a b k := by
  have := isFiniteMeasure_lobattoMeasure hμ
  exact ae_mem_lobattoNodes_of_ae_mem_gaussNodes
    (ae_mem_gaussNodes_of_not_isMomentPosDef (ae_mem_Icc_lobattoMeasure hμ) h)

/-- The degree of $\prod_{y\in s}(X - y)^2$ is at most $2\lvert s\rvert$. -/
private theorem natDegree_prod_X_sub_C_sq_le (s : Finset ℝ) :
    (∏ y ∈ s, (X - C y) ^ 2).natDegree ≤ 2 * s.card := by
  refine (natDegree_prod_le _ _).trans ?_
  calc _ ≤ ∑ _y ∈ s, 2 := Finset.sum_le_sum fun y _ => natDegree_pow_le.trans (by simp)
    _ = 2 * s.card := by simp [mul_comm]

/-- A Lobatto weight from a factor: if $\mu$, finite and supported in $[a, b]$, has a Lobatto
modified measure definite up to degree $k$, $x$ is a Lobatto node, and $q \ge 0$ on $[a, b]$ is
positive at $x$, vanishes at the endpoints other than $x$ and has
$\deg q + 2\lvert G \setminus \{x\}\rvert < 2k + 2$ ($G$ the free nodes), then the weight of $x$
is nonnegative: apply `integral_eval_basis_nonneg_of_exact` to
$q\prod_{y\in G\setminus\{x\}}(X - y)^2$. -/
private theorem integral_eval_basis_lobattoNodes_nonneg_of_factor
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {k : ℕ}
    (h : IsMomentPosDef (lobattoMeasure μ a b) k) {x : ℝ} (hx : x ∈ lobattoNodes μ a b k)
    {q : ℝ[X]}
    (hdeg : q.natDegree + 2 * ((gaussNodes (lobattoMeasure μ a b) k).erase x).card < 2 * k + 2)
    (hq : ∀ t ∈ Set.Icc a b, 0 ≤ q.eval t) (hqx : 0 < q.eval x) (hqa : x ≠ a → q.eval a = 0)
    (hqb : x ≠ b → q.eval b = 0) :
    0 ≤ ∫ t, (Lagrange.basis (lobattoNodes μ a b k) id x).eval t ∂μ := by
  set G := gaussNodes (lobattoMeasure μ a b) k
  refine integral_eval_basis_nonneg_of_exact hμ (isOrthogonalPolynomial_nodal_lobattoNodes hμ hab h)
    hx (p := q * ∏ y ∈ G.erase x, (X - C y) ^ 2) ?_ (fun t ht => ?_) (fun y hy hyx => ?_) ?_
  · have := natDegree_mul_le (p := q) (q := ∏ y ∈ G.erase x, (X - C y) ^ 2)
    have := natDegree_prod_X_sub_C_sq_le (G.erase x)
    rw [h.card_lobattoNodes hμ hab]
    omega
  · rw [eval_mul, eval_prod]
    exact mul_nonneg (hq t ht) (Finset.prod_nonneg fun y _ => by rw [eval_pow]; positivity)
  · rw [eval_mul]
    simp only [lobattoNodes, Finset.mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · rw [hqa hyx.symm, zero_mul]
    · rw [hqb hyx.symm, zero_mul]
    · rw [eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hyx, hy⟩) (by simp), mul_zero]
  · rw [eval_mul, eval_prod]
    refine mul_pos hqx (Finset.prod_pos fun y hy => ?_)
    have hxy : x - y ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hy).symm
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    positivity

/-- **The Lobatto weights are nonnegative**: for a finite measure $\mu$ supported in $[a, b]$,
$a < b$, and every $k$, the interpolatory weight $\int\ell_x\,d\mu$ of every Lobatto node $x$ is
nonnegative, $\ell_x$ its Lagrange basis polynomial. [Gautschi2004, Theorem 3.6]; there positive,
for $\mu$ with more than $k$ interior support points. -/
theorem integral_eval_basis_lobattoNodes_nonneg (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b)
    (k : ℕ) {x : ℝ} (hx : x ∈ lobattoNodes μ a b k) :
    0 ≤ ∫ t, (Lagrange.basis (lobattoNodes μ a b k) id x).eval t ∂μ := by
  by_cases h : IsMomentPosDef (lobattoMeasure μ a b) k
  · have := isFiniteMeasure_lobattoMeasure hμ
    set G := gaussNodes (lobattoMeasure μ a b) k with hG
    have hGk : G.card = k := h.card_gaussNodes (ae_mem_Icc_lobattoMeasure hμ)
    have hGa := Finset.card_erase_le (s := G) (a := x)
    have hXa : (X - C a : ℝ[X]).natDegree ≤ 1 := by compute_degree!
    have hbX : (C b - X : ℝ[X]).natDegree ≤ 1 := by compute_degree!
    have hx' : x = a ∨ x = b ∨ x ∈ G := by simpa [lobattoNodes] using hx
    rcases hx' with hxa | hxb | hxG
    · -- the endpoint $a$: $q = b - X$
      refine integral_eval_basis_lobattoNodes_nonneg_of_factor hμ hab h hx (q := C b - X)
        (by rw [← hG]; omega) (fun t ht => by simpa using ht.2) (by simpa [hxa] using hab)
        (fun h' => absurd hxa h') (fun _ => by simp)
    · -- the endpoint $b$: $q = X - a$
      refine integral_eval_basis_lobattoNodes_nonneg_of_factor hμ hab h hx (q := X - C a)
        (by rw [← hG]; omega) (fun t ht => by simpa using ht.1) (by simpa [hxb] using hab)
        (fun _ => by simp) (fun h' => absurd hxb h')
    · -- a free node: $q = (X - a)(b - X)$
      have hxI := h.gaussNodes_subset_Icc (ae_mem_Icc_lobattoMeasure hμ)
        (Finset.mem_coe.2 hxG)
      have hxa : x ≠ a := fun e => h.notMem_gaussNodes_lobattoMeasure hμ (.inl e) hxG
      have hxb : x ≠ b := fun e => h.notMem_gaussNodes_lobattoMeasure hμ (.inr e) hxG
      have hE : (G.erase x).card = k - 1 := by rw [Finset.card_erase_of_mem hxG, hGk]
      have hk : 0 < k := hGk ▸ Finset.card_pos.2 ⟨x, hxG⟩
      have hq := natDegree_mul_le (p := X - C a) (q := C b - X)
      refine integral_eval_basis_lobattoNodes_nonneg_of_factor hμ hab h hx
        (q := (X - C a) * (C b - X)) (by rw [← hG]; omega) (fun t ht => ?_) ?_ (fun _ => by simp)
        (fun _ => by simp)
      · simp only [eval_mul, eval_sub, eval_X, eval_C]
        exact mul_nonneg (sub_nonneg.2 ht.1) (sub_nonneg.2 ht.2)
      · simp only [eval_mul, eval_sub, eval_X, eval_C]
        exact mul_pos (sub_pos.2 (hxI.1.lt_of_ne' hxa)) (sub_pos.2 (hxI.2.lt_of_ne hxb))
  · rw [integral_eval_basis_of_ae_mem (ae_mem_lobattoNodes_of_not_isMomentPosDef hμ h) hx]
    exact measureReal_nonneg

/-- The Lobatto rule with the interpolatory weights: for a finite measure $\mu$ supported in
$[a, b]$, $a < b$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{lobattoQuadrature}(\mu, a, b, k) =
\sum_{x\in L}\Bigl(\int\ell_x\,d\mu\Bigr)f(x)\,,$$
$L$ the Lobatto nodes and $\ell_x$ their Lagrange basis polynomials. -/
theorem integral_lobattoQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂lobattoQuadrature μ a b k =
      ∑ x ∈ lobattoNodes μ a b k,
        (∫ t, (Lagrange.basis (lobattoNodes μ a b k) id x).eval t ∂μ) * f x := by
  unfold lobattoQuadrature interpolatoryQuadrature
  rw [integral_finsetSum_measure fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (integral_eval_basis_lobattoNodes_nonneg hμ hab k hx)]

/-- **Gauss–Lobatto quadrature**: for a finite measure $\mu$ supported in $[a, b]$, $a < b$, and
every $k$, the Lobatto rule with $k$ free nodes matches the first $2k + 2$ moments of $\mu$: it
integrates every real polynomial of degree at most $2k + 1$ exactly. [Gautschi2004,
§1.4.2, (1.4.22)]; [GolubMeurant2010, §6.2.3]; there for $\mu$ with more than
$k$ interior support points; otherwise the rule is $\mu$ itself.
Result: gauss-lobatto-quadrature -/
theorem matchesMoments_lobattoQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) :
    MatchesMoments μ (lobattoQuadrature μ a b k) (2 * k + 2) := by
  by_cases h : IsMomentPosDef (lobattoMeasure μ a b) k
  · have hs := isOrthogonalPolynomial_nodal_lobattoNodes hμ hab h
    intro p hp
    rw [integral_lobattoQuadrature hμ hab k]
    exact hs.integral_eval_eq_sum_of_degree_lt_card_add hμ
      (by rwa [h.card_lobattoNodes hμ hab, show k + 2 + k = 2 * k + 2 by ring])
  · rw [lobattoQuadrature, interpolatoryQuadrature_eq_self_of_ae_mem
      (ae_mem_lobattoNodes_of_not_isMomentPosDef hμ h)]
    exact MatchesMoments.refl _ _

/-- The Lobatto rule lives in every interval carrying the measure: for a finite measure $\mu$
supported in $[a, b]$, $a < b$, and every $k$, almost every point of the Lobatto rule lies in
$[a, b]$. -/
theorem ae_mem_Icc_lobattoQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) :
    ∀ᵐ x ∂lobattoQuadrature μ a b k, x ∈ Set.Icc a b := by
  by_cases h : IsMomentPosDef (lobattoMeasure μ a b) k
  · have := isFiniteMeasure_lobattoMeasure hμ
    filter_upwards [ae_mem_interpolatoryQuadrature μ (lobattoNodes μ a b k)] with x hx
    simp only [lobattoNodes, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact h.gaussNodes_subset_Icc (ae_mem_Icc_lobattoMeasure hμ) (Finset.mem_coe.mpr hx)
  · rw [lobattoQuadrature, interpolatoryQuadrature_eq_self_of_ae_mem
      (ae_mem_lobattoNodes_of_not_isMomentPosDef hμ h)]
    exact hμ

/-- The mass of the Lobatto rule: for a finite measure $\mu$ supported in $[a, b]$, $a < b$,
and every $k$, the Lobatto rule has mass $\mu(\mathbb{R})$. -/
theorem lobattoQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) :
    (lobattoQuadrature μ a b k).real Set.univ = μ.real Set.univ :=
  ((matchesMoments_lobattoQuadrature hμ hab k).measureReal_univ_eq (by omega)).symm

/-- The Lobatto interpolation multiset $\{a, b\} + G + G$, for $a < b$ and $G \subseteq (a, b)$,
lies in $[a, b]$, and its repeated points lie in $(a, b)$. -/
private theorem mem_Icc_and_mem_Ioo_of_one_lt_count_cons_cons {a b : ℝ} (hab : a < b)
    {G : Finset ℝ} (hGI : (G : Set ℝ) ⊆ Set.Ioo a b) :
    (∀ y ∈ a ::ₘ b ::ₘ (G.val + G.val), y ∈ Set.Icc a b) ∧
      ∀ y ∈ a ::ₘ b ::ₘ (G.val + G.val),
        1 < (a ::ₘ b ::ₘ (G.val + G.val)).count y → y ∈ Set.Ioo a b := by
  have haG : a ∉ G := fun h => lt_irrefl a (hGI h).1
  have hbG : b ∉ G := fun h => lt_irrefl b (hGI h).2
  refine ⟨fun y hy => ?_, fun y hy hc => ?_⟩ <;>
    simp only [Multiset.mem_cons, Multiset.mem_add, Finset.mem_val, or_self] at hy <;>
    rcases hy with rfl | rfl | hy
  · exact ⟨le_rfl, hab.le⟩
  · exact ⟨hab.le, le_rfl⟩
  · exact Set.Ioo_subset_Icc_self (hGI hy)
  · simp [hab.ne, Multiset.count_eq_zero.mpr haG] at hc
  · simp [hab.ne', Multiset.count_eq_zero.mpr hbG] at hc
  · exact hGI hy

/-- **The Gauss–Lobatto remainder**: for a finite measure $\mu$ supported in $[a, b]$, $a < b$,
every $k$, and $f$ continuous on $[a, b]$ and $C^{2k+2}$ on $(a, b)$, there is $\xi \in (a, b)$
with
$$\int f\,d\mu - \int f\,d\,\mathsf{lobattoQuadrature}(\mu, a, b, k) =
\frac{f^{(2k+2)}(\xi)}{(2k+2)!}\int(x - a)(x - b)\,\hat\pi_k(x)^2\,d\mu(x)\,,$$
$\hat\pi_k$ the monic orthogonal polynomial of degree $k$ of `lobattoMeasure μ a b`.
[Gautschi2004, Theorem 3.7]; [GolubMeurant2010, §6.2.3].
Result: gauss-lobatto-remainder -/
theorem exists_integral_sub_integral_lobattoQuadrature_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) (k : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k + 2 : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂lobattoQuadrature μ a b k =
      iteratedDeriv (2 * k + 2) f ξ / (2 * k + 2).factorial *
        ∫ x, (x - a) * (x - b) * (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂μ := by
  set μ' := lobattoMeasure μ a b
  have := isFiniteMeasure_lobattoMeasure hμ
  have hμ'I := ae_mem_Icc_lobattoMeasure hμ
  set π := orthogonalPolynomial μ' k
  set W : ℝ → ℝ := fun x => (x - a) * (x - b) * π.eval x ^ 2 with hW
  have hWint : Integrable W μ :=
    (integrable_eval_of_ae_mem_Icc hμ ((X - C a) * (X - C b) * π ^ 2)).congr
      (ae_of_all μ fun x => by simp [hW])
  rcases (integral_nonneg fun x => sq_nonneg (π.eval x) : 0 ≤ ∫ x, π.eval x ^ 2 ∂μ').eq_or_lt
    with h0 | hpos
  · -- degenerate case: the rule is `μ` and the weight vanishes
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [lobattoQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero hμ h0.symm, sub_self,
      integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure hμ, ← h0, neg_zero, mul_zero]
  -- nondegenerate case: Hermite interpolation on `m = {a, b} + G + G`
  have hpd : IsMomentPosDef μ' (k + 1) := (isMomentPosDef_succ_iff hμ'I k).mpr hpos
  set G := gaussNodes μ' k
  have hGI : (G : Set ℝ) ⊆ Set.Ioo a b := hpd.gaussNodes_subset_Ioo hμ'I
  have hGc : G.card = k := (hpd.mono k.le_succ).card_gaussNodes hμ'I
  have hGπ : Lagrange.nodal G id = π := (hpd.mono k.le_succ).nodal_gaussNodes hμ'I
  set m : Multiset ℝ := a ::ₘ b ::ₘ (G.val + G.val) with hm
  have hmc : m.card = 2 * k + 2 := by
    simp only [hm, Multiset.card_cons, Multiset.card_add, Finset.card_val, hGc]
    ring
  obtain ⟨hmem, hrep⟩ := mem_Icc_and_mem_Ioo_of_one_lt_count_cons_cons hab hGI
  have hprod : ∀ x, ((m.map fun y => X - C y).prod).eval x = W x := by
    intro x
    have : (G.val.map fun y => X - C y).prod = π := by
      rw [← hGπ, Lagrange.nodal]
      rfl
    simp only [hm, Multiset.map_cons, Multiset.prod_cons, Multiset.map_add, Multiset.prod_add,
      this, hW, eval_mul, eval_sub, eval_X, eval_C]
    ring
  obtain ⟨H, hHdeg, hHjet⟩ :=
    exists_degree_lt_forall_iterate_derivative_eval_eq m fun y j => iteratedDeriv j f y
  have hHf : ∀ x ∈ lobattoNodes μ a b k, H.eval x = f x := by
    intro x hx
    have hxm : x ∈ m := by simpa [hm, lobattoNodes] using hx
    simpa using hHjet x hxm 0 (Multiset.count_pos.mpr hxm)
  have hQ : ∫ x, f x ∂lobattoQuadrature μ a b k = ∫ x, H.eval x ∂μ := by
    rw [matchesMoments_lobattoQuadrature hμ hab k H (by exact_mod_cast hmc ▸ hHdeg),
      integral_lobattoQuadrature hμ hab k f, integral_lobattoQuadrature hμ hab k]
    exact Finset.sum_congr rfl fun x hx => by rw [hHf x hx]
  rw [hQ]
  refine exists_integral_sub_integral_eval_eq hμ hab hf hf' hWint (.inr ?_) fun x hx => ?_
  · filter_upwards [hμ] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hx.1) (sub_nonpos.2 hx.2)) (sq_nonneg _)
  obtain ⟨ξ, hξ, h⟩ := exists_sub_eval_eq_iteratedDeriv_mul hab (by simp) hmem hrep hf
    (hmc ▸ hf') (hmc ▸ hHdeg) hHjet hx
  exact ⟨ξ, hξ, by rw [h, hprod, hmc]⟩

/-- **The Lobatto rule is an upper bound** for $f$ with nonnegative derivative of order $2k + 2$:
for a finite measure $\mu$ supported in $[a, b]$, $a < b$, every $k$, and $f$ continuous on
$[a, b]$, $C^{2k+2}$ on $(a, b)$ with $f^{(2k+2)} \ge 0$ there,
$$\int f\,d\mu \le \int f\,d\,\mathsf{lobattoQuadrature}(\mu, a, b, k)\,.$$
[Gautschi2004, Theorem 3.7]; [GolubMeurant2010, §6.2.3]. -/
theorem integral_le_integral_lobattoQuadrature_of_iteratedDeriv_nonneg
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 2 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv (2 * k + 2) f x) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂lobattoQuadrature μ a b k := by
  obtain ⟨ξ, hξ, h⟩ := exists_integral_sub_integral_lobattoQuadrature_eq hμ hab k hf hf'
  have hW : ∫ x, (x - a) * (x - b) * (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂μ
      ≤ 0 := by
    rw [integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure hμ, neg_nonpos]
    exact integral_nonneg fun x => sq_nonneg _
  linarith [mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hD ξ hξ) (Nat.cast_nonneg (2 * k + 2).factorial)) hW]

/-- **The Lobatto rule is a lower bound** for $f$ with nonpositive derivative of order
$2k + 2$: for a finite measure $\mu$ supported in $[a, b]$, $a < b$, every $k$, and $f$
continuous on $[a, b]$, $C^{2k+2}$ on $(a, b)$ with $f^{(2k+2)} \le 0$ there,
$$\int f\,d\,\mathsf{lobattoQuadrature}(\mu, a, b, k) \le \int f\,d\mu\,.$$
[Gautschi2004, Theorem 3.7]; [GolubMeurant2010, §6.2.3]. -/
theorem integral_lobattoQuadrature_le_integral_of_iteratedDeriv_nonpos
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 2 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, iteratedDeriv (2 * k + 2) f x ≤ 0) :
    ∫ x, f x ∂lobattoQuadrature μ a b k ≤ ∫ x, f x ∂μ := by
  obtain ⟨ξ, hξ, h⟩ := exists_integral_sub_integral_lobattoQuadrature_eq hμ hab k hf hf'
  have hW : ∫ x, (x - a) * (x - b) * (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂μ
      ≤ 0 := by
    rw [integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure hμ, neg_nonpos]
    exact integral_nonneg fun x => sq_nonneg _
  linarith [mul_nonneg_of_nonpos_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (hD ξ hξ) (Nat.cast_nonneg (2 * k + 2).factorial)) hW]

end NLAlib
