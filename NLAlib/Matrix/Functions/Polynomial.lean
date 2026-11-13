/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.SVD

/-!
# Polynomials in a matrix

Real polynomials $p$ evaluated at a matrix, $p(\mathbf{A})$, spelled `Polynomial.aeval`. For a
Hermitian matrix this is the functional calculus of $p$ (Mathlib's `cfc_polynomial`), so its norm
is the largest value of $\lvert p \rvert$ on the eigenvalues: the fact behind every polynomial
convergence bound for Krylov methods. For a rectangular matrix, polynomials in the two Gram
matrices intertwine,
$p(\mathbf{A}\mathbf{A}^{\mathsf{H}})\mathbf{A} = \mathbf{A}\,p(\mathbf{A}^{\mathsf{H}}\mathbf{A})$,
and act on the singular values.

## Main results

* `Matrix.IsHermitian.exists_cfc_eq_aeval`: every function of $\mathbf{A}$ is a polynomial in
  $\mathbf{A}$.
* `NLAlib.exists_eval_eq_of_mem_spectrum`: one interpolating polynomial on two spectra.
* `Matrix.IsHermitian.aeval_nodal_eq_zero`: the nodal polynomial of a set containing the
  spectrum annihilates $\mathbf{A}$.
* `Matrix.IsHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum`: a vector with
  prescribed spectral weights.
* `Matrix.IsHermitian.specNorm_aeval_le`:
  $\|p(\mathbf{A})\|_2 \le \max_i \lvert p(\lambda_i(\mathbf{A})) \rvert$.
* `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le`: the same bound for the quadratic form
  of a polynomial weight $g(\mathbf{A})$, with `NLAlib.re_quadForm_aeval_mulVec_le` the case
  $g(t) = t$.
* `NLAlib.specNorm_cfc_sub_aeval_le`: polynomial approximation of $f(\mathbf{A})$.
* `NLAlib.aeval_diagonal_self`: $p(\operatorname{diag}(\mathbf{d})) = \operatorname{diag}(p(d_i))$.
* `NLAlib.aeval_mul_eq_mul_aeval_of_mul_eq_mul`: polynomials intertwine, for real polynomials
  and polynomials over $\Bbbk$.
* `NLAlib.aeval_mul_conjTranspose_self_mul`: intertwining.
* `NLAlib.IsSVD.mul_aeval_conjTranspose_mul_self`: a polynomial filter applied to an SVD.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-! ### Polynomials in a Hermitian matrix -/

/-- A polynomial in a real diagonal matrix:
$p(\operatorname{diag}(\mathbf{d})) = \operatorname{diag}(p(\mathbf{d}_i))$. -/
theorem aeval_diagonal (d : n → ℝ) (p : ℝ[X]) :
    aeval (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) p =
      Matrix.diagonal fun i => ((p.eval (d i) : ℝ) : 𝕜) := by
  have hD : IsSelfAdjoint (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) := by
    change (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)).IsHermitian
    rw [Matrix.isHermitian_diagonal_iff]
    exact fun i => RCLike.conj_ofReal (d i)
  rw [← cfc_polynomial p _ hD, cfc_diagonal]

/-- A polynomial in a diagonal matrix over its own scalars is the diagonal of its values:
$p(\operatorname{diag}(\mathbf{d})) = \operatorname{diag}(p(d_i))$ for $p \in R[X]$. -/
theorem aeval_diagonal_self {R : Type*} [CommSemiring R] (d : n → R) (p : R[X]) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal fun i => p.eval (d i) := by
  change aeval (Matrix.diagonalAlgHom R d) p = _
  rw [aeval_algHom_apply, aeval_pi_apply]
  simp only [coe_aeval_eq_eval]
  rfl

/-- A polynomial commutes with unitary conjugation:
$p(\mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}})
= \mathbf{U}\,p(\mathbf{A})\,\mathbf{U}^{\mathsf{H}}$ for $\mathbf{U}$ with orthonormal columns
and as many columns as rows. -/
theorem HasOrthonormalCols.aeval_mul_mul_conjTranspose {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U)
    (hr : Fintype.card r = Fintype.card n) (A : Matrix r r 𝕜) (p : ℝ[X]) :
    aeval (U * A * Uᴴ) p = U * aeval A p * Uᴴ := by
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq hr.symm
  have hpow : ∀ j : ℕ, (U * A * Uᴴ) ^ j = U * A ^ j * Uᴴ := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hUU]
    | succ j ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial j a =>
    rw [aeval_monomial, aeval_monomial, hpow, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- A function of a Hermitian matrix is the polynomial that agrees with it on the eigenvalues: if
$p(x) = f(x)$ for every $x$ in the spectrum of $\mathbf{A}$, then
$f(\mathbf{A}) = p(\mathbf{A})$. -/
theorem _root_.Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {p : ℝ[X]} (h : ∀ x ∈ spectrum ℝ A, p.eval x = f x) :
    cfc f A = aeval A p := by
  have hsa : IsSelfAdjoint A := hA
  rw [← cfc_polynomial p A hsa]
  exact cfc_congr fun x hx => (h x hx).symm

/-- The nodal polynomial of a set containing the spectrum annihilates a Hermitian matrix:
if $\sigma(\mathbf{A}) \subseteq s$ then $\pi_s(\mathbf{A}) = \mathbf{0}$ for
$\pi_s(z) = \prod_{\theta \in s}(z - \theta)$ (`Lagrange.nodal s id`). -/
theorem _root_.Matrix.IsHermitian.aeval_nodal_eq_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {s : Finset ℝ} (hs : spectrum ℝ A ⊆ ↑s) : aeval A (Lagrange.nodal s id) = 0 := by
  have hA' : IsSelfAdjoint A := hA
  rw [← cfc_polynomial (Lagrange.nodal s id) A hA', ← cfc_const_zero ℝ A]
  exact cfc_congr fun x hx => Lagrange.eval_nodal_at_node (v := id) (Finset.mem_coe.mp (hs hx))

/-- Every function of a Hermitian matrix is a polynomial in it of degree less than the size:
$f(\mathbf{A}) = p(\mathbf{A})$ for a real polynomial $p$ of degree less than $\lvert n \rvert$,
so $f(\mathbf{A})\mathbf{b}$ lies in the Krylov space of $\mathbf{A}$ and $\mathbf{b}$. -/
theorem _root_.Matrix.IsHermitian.exists_cfc_eq_aeval {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : ∃ p : ℝ[X], p.degree < (Fintype.card n : WithBot ℕ) ∧ cfc f A = aeval A p := by
  classical
  refine ⟨Lagrange.interpolate (Finset.univ.image hA.eigenvalues) id f, ?_, ?_⟩
  · refine (Lagrange.degree_interpolate_lt (r := f) (Set.injOn_id _)).trans_le ?_
    exact_mod_cast Finset.card_image_le.trans Finset.card_univ.le
  · refine hA.cfc_eq_aeval_of_forall_eval_eq fun x hx => ?_
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- One polynomial for two matrices: for any square matrices $\mathbf{M}$, $\mathbf{N}$
(of possibly different sizes) and $f : \mathbb{R} \to \mathbb{R}$, some real polynomial $p$
satisfies $p(x) = f(x)$ on the real spectra of both, the Lagrange interpolant on their union,
which is finite. With `Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq` it writes
$f(\mathbf{M})$ and $f(\mathbf{N})$ as the same polynomial. -/
theorem exists_eval_eq_of_mem_spectrum (M : Matrix n n 𝕜) (N : Matrix m m 𝕜) (f : ℝ → ℝ) :
    ∃ p : ℝ[X], (∀ x ∈ spectrum ℝ M, p.eval x = f x) ∧ ∀ x ∈ spectrum ℝ N, p.eval x = f x := by
  classical
  set s := (M.finite_real_spectrum.union N.finite_real_spectrum).toFinset
  refine ⟨Lagrange.interpolate s id f, fun x hx => ?_, fun x hx => ?_⟩
  · exact Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _)
      ((Set.Finite.mem_toFinset _).mpr (Or.inl hx))
  · exact Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _)
      ((Set.Finite.mem_toFinset _).mpr (Or.inr hx))

/-- A polynomial in a Hermitian matrix is Hermitian. -/
theorem _root_.Matrix.IsHermitian.aeval {A : Matrix n n 𝕜} (hA : A.IsHermitian) (p : ℝ[X]) :
    (Polynomial.aeval A p).IsHermitian := by
  have hsa : IsSelfAdjoint A := hA
  rw [← cfc_polynomial p A hsa]
  exact cfc_predicate p.eval A

/-- **The norm of a polynomial in a Hermitian matrix** is at most the largest value of
$\lvert p \rvert$ on its eigenvalues: if $c \ge 0$ and $\lvert p(x) \rvert \le c$ for every $x$ in
the spectrum of $\mathbf{A}$, then $\|p(\mathbf{A})\|_2 \le c$.
[Saad2003, §6.11]; [Saad2011, §6.6].
Result: polynomial-spectral-bound -/
theorem _root_.Matrix.IsHermitian.specNorm_aeval_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (p : ℝ[X]) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ A, |p.eval x| ≤ c) :
    specNorm (Polynomial.aeval A p) ≤ c := by
  have hsa : IsSelfAdjoint A := hA
  rw [← cfc_polynomial p A hsa]
  exact hA.specNorm_cfc_le hc h

/-- The norm of a polynomial in a matrix with spectrum in $[a, b]$ is at most the largest value
of $\lvert p \rvert$ on $[a, b]$: if $a\mathbf{I} \preceq \mathbf{A} \preceq b\mathbf{I}$, $c \ge 0$
and $\lvert p(x) \rvert \le c$ on $[a, b]$, then $\|p(\mathbf{A})\|_2 \le c$. This is the form used
with Chebyshev polynomials.
[Saad2003, §6.11.3]. -/
theorem specNorm_aeval_le_of_forall_mem_Icc {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) (p : ℝ[X]) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x ∈ Set.Icc a b, |p.eval x| ≤ c) : specNorm (aeval A p) ≤ c := by
  exact (isHermitian_of_le_smul_one h₂).specNorm_aeval_le p hc fun x hx =>
    h x (spectrum_subset_Icc_of_le h₁ h₂ hx)

/-- **The error of a polynomial approximation of $f(\mathbf{A})$** is at most the error of the
scalar approximation on an interval containing the spectrum: if
$a\mathbf{I} \preceq \mathbf{A} \preceq b\mathbf{I}$, $c \ge 0$ and
$\lvert f(x) - p(x) \rvert \le c$ on $[a, b]$, then $\|f(\mathbf{A}) - p(\mathbf{A})\|_2 \le c$.
The shared `Metric.IsUniformApproxOn` interface transfers scalar approximation constructors
directly to matrix error bounds, including Krylov methods for $f(\mathbf{A})\mathbf{b}$.
[Higham2008, §13.2 context]; [Saad2003, §6.11]. -/
theorem specNorm_cfc_sub_aeval_le {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) {f : ℝ → ℝ} (p : ℝ[X])
    {c : ℝ} (hc : 0 ≤ c) (h : Metric.IsUniformApproxOn p.eval f (Set.Icc a b) c) :
    specNorm (cfc f A - aeval A p) ≤ c := by
  have hA := isHermitian_of_le_smul_one h₂
  have hsa : IsSelfAdjoint A := hA
  rw [← cfc_polynomial p A hsa, ← cfc_sub f p.eval A (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _)]
  exact hA.specNorm_cfc_le hc fun x hx => by
    simpa only [Real.dist_eq, abs_sub_comm] using
      h.apply (spectrum_subset_Icc_of_le h₁ h₂ hx)

/-- The trace of a polynomial in a Hermitian matrix:
$\operatorname{Re} \operatorname{tr} p(\mathbf{A})
= \sum_{i < \lvert n \rvert} p(\lambda_i(\mathbf{A}))$. -/
theorem _root_.Matrix.IsHermitian.re_trace_aeval {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (p : ℝ[X]) :
    RCLike.re (Polynomial.aeval A p).trace =
      ∑ i ∈ Finset.range (Fintype.card n), p.eval (eigenvalue A i) := by
  have hsa : IsSelfAdjoint A := hA
  rw [← cfc_polynomial p A hsa]
  exact hA.re_trace_cfc p.eval

/-- **The polynomial bound in a polynomial weight.** For Hermitian $\mathbf{A}$ with spectrum in a
set $S$, a real polynomial $g$ that is nonnegative on $S$ and a real polynomial $p$ with
$\lvert p \rvert \le c$ on $S$, the quadratic form of $g(\mathbf{A})$ satisfies
$$\operatorname{Re}\bigl((p(\mathbf{A})\mathbf{x})^{\mathsf{H}} g(\mathbf{A})
  (p(\mathbf{A})\mathbf{x})\bigr)
  \le c^2 \operatorname{Re}(\mathbf{x}^{\mathsf{H}} g(\mathbf{A}) \mathbf{x}) \,.$$
With $g(t) = t$ this is the energy-norm bound behind the conjugate gradient method
(`NLAlib.re_quadForm_aeval_mulVec_le`), with $g(t) = t^2$ the residual-norm bound behind MINRES,
which holds for indefinite $\mathbf{A}$. [Saad2003, Lemma 6.28 context]. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {S : Set ℝ} (hS : spectrum ℝ A ⊆ S) (g p : ℝ[X]) {c : ℝ}
    (hg : ∀ x ∈ S, 0 ≤ g.eval x) (hp : ∀ x ∈ S, |p.eval x| ≤ c) (x : n → 𝕜) :
    RCLike.re (quadForm (Polynomial.aeval A g) (Polynomial.aeval A p *ᵥ x)) ≤
      c ^ 2 * RCLike.re (quadForm (Polynomial.aeval A g) x) := by
  have hsa : IsSelfAdjoint A := hA
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f =>
    A.finite_real_spectrum.continuousOn f
  have hPGP : (Polynomial.aeval A p)ᴴ * Polynomial.aeval A g * Polynomial.aeval A p =
      cfc (fun t => p.eval t * g.eval t * p.eval t) A := by
    rw [(hA.aeval p).eq, cfc_mul (fun t => p.eval t * g.eval t) p.eval A (hcont _) (hcont _),
      cfc_mul p.eval g.eval A (hcont _) (hcont _), cfc_polynomial p A hsa,
      cfc_polynomial g A hsa]
  have hle : cfc (fun t => p.eval t * g.eval t * p.eval t) A ≤ c ^ 2 • Polynomial.aeval A g := by
    have h2 : cfc (fun t : ℝ => c ^ 2 * g.eval t) A = c ^ 2 • Polynomial.aeval A g := by
      rw [cfc_const_mul (c ^ 2) g.eval A (hcont _), cfc_polynomial g A hsa]
    rw [← h2]
    refine cfc_mono (fun x hx => ?_) (hcont _) (hcont _)
    have hp' := abs_le.mp (hp x (hS hx))
    calc p.eval x * g.eval x * p.eval x = p.eval x ^ 2 * g.eval x := by ring
      _ ≤ c ^ 2 * g.eval x :=
        mul_le_mul_of_nonneg_right (sq_le_sq' hp'.1 hp'.2) (hg x (hS hx))
  have hq := re_quadForm_le_re_quadForm_of_le hle x
  rw [← hPGP, quadForm_conjTranspose_mul_mul, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    quadForm_smul_left, RCLike.re_ofReal_mul] at hq
  exact hq

/-- The energy norm of $p(\mathbf{A})\mathbf{x}$ for positive semidefinite $\mathbf{A}$ is
controlled by $\lvert p \rvert$ on an interval containing the spectrum: if $0 \le a$,
$a\mathbf{I} \preceq \mathbf{A} \preceq b\mathbf{I}$ and $\lvert p(x) \rvert \le c$ on $[a, b]$,
then
$$\operatorname{Re}\bigl((p(\mathbf{A})\mathbf{x})^{\mathsf{H}} \mathbf{A}
  (p(\mathbf{A})\mathbf{x})\bigr)
  \le c^2 \operatorname{Re}(\mathbf{x}^{\mathsf{H}} \mathbf{A} \mathbf{x}) \,.$$
This is the energy-norm bound for a polynomial error,
`Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le` with the weight $g(t) = t$.
[Saad2003, Lemma 6.28 context]. -/
theorem re_quadForm_aeval_mulVec_le {A : Matrix n n 𝕜} {a b : ℝ} (ha : 0 ≤ a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) (p : ℝ[X]) {c : ℝ}
    (h : ∀ x ∈ Set.Icc a b, |p.eval x| ≤ c) (x : n → 𝕜) :
    RCLike.re (quadForm A (aeval A p *ᵥ x)) ≤ c ^ 2 * RCLike.re (quadForm A x) := by
  have hq := (isHermitian_of_le_smul_one h₂).re_quadForm_aeval_aeval_mulVec_le
    (spectrum_subset_Icc_of_le h₁ h₂) X p (fun t ht => by rw [eval_X]; exact ha.trans ht.1) h x
  rwa [aeval_X] at hq

/-! ### Intertwining and singular values -/

/-- Powers intertwine: if $\mathbf{B}\mathbf{A} = \mathbf{A}\mathbf{C}$ then
$\mathbf{B}^j\mathbf{A} = \mathbf{A}\mathbf{C}^j$. -/
theorem pow_mul_eq_mul_pow_of_mul_eq_mul {R : Type*} [Semiring R] {B : Matrix m m R}
    {A : Matrix m n R} {C : Matrix n n R} (h : B * A = A * C) (j : ℕ) :
    B ^ j * A = A * C ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ j ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
      ← pow_succ]

/-- Polynomials intertwine: if $\mathbf{B}\mathbf{A} = \mathbf{A}\mathbf{C}$ then
$p(\mathbf{B})\mathbf{A} = \mathbf{A}\,p(\mathbf{C})$ for every polynomial $p$ with
coefficients in any scalar ring $S$ acting on $\Bbbk$ (real polynomials, or polynomials over
$\Bbbk$ itself). -/
theorem aeval_mul_eq_mul_aeval_of_mul_eq_mul {𝕜 S : Type*}
    [CommSemiring 𝕜] [CommSemiring S] [Algebra S 𝕜]
    {B : Matrix m m 𝕜} {A : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : B * A = A * C) (p : S[X]) :
    aeval B p * A = A * aeval C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial j a =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, pow_mul_eq_mul_pow_of_mul_eq_mul h]

/-- A polynomial of a diagonalisable matrix is bounded through its eigenvalues: if
$\mathbf{A}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and
$\lvert p(d_i) \rvert \le \eta$ for every $i$, then
$\|p(\mathbf{A})\|_2 \le \kappa(\mathbf{V})\,\eta$, with
$\kappa(\mathbf{V}) = \|\mathbf{V}\|_2 \|\mathbf{V}^{-1}\|_2$. -/
theorem specNorm_aeval_le_pseudoConditionNumber_mul {A V : Matrix n n 𝕜}
    {d : n → 𝕜} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) (p : 𝕜[X]) {η : ℝ}
    (hη : ∀ i, ‖p.eval (d i)‖ ≤ η) : specNorm (aeval A p) ≤ pseudoConditionNumber V * η := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩
  · rw [Subsingleton.elim (aeval A p) 0, Subsingleton.elim V 0, specNorm_zero,
      pseudoConditionNumber_zero, zero_mul]
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη i)
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hpA : aeval A p = V * Matrix.diagonal (fun i => p.eval (d i)) * V⁻¹ := by
    rw [← aeval_diagonal_self, ← aeval_mul_eq_mul_aeval_of_mul_eq_mul hAV, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [hpA, pseudoConditionNumber_of_isUnit hV]
  calc specNorm (V * Matrix.diagonal (fun i => p.eval (d i)) * V⁻¹)
      ≤ specNorm V * specNorm (Matrix.diagonal fun i => p.eval (d i)) * specNorm V⁻¹ :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ specNorm V * η * specNorm V⁻¹ := by
        gcongr
        exact specNorm_diagonal_le hη0 hη
    _ = specNorm V * specNorm V⁻¹ * η := by ring

/-- Polynomials in the two Gram matrices intertwine:
$p(\mathbf{A}\mathbf{A}^{\mathsf{H}})\mathbf{A} = \mathbf{A}\,p(\mathbf{A}^{\mathsf{H}}\mathbf{A})$.
-/
theorem aeval_mul_conjTranspose_self_mul (A : Matrix m n 𝕜) (p : ℝ[X]) :
    aeval (A * Aᴴ) p * A = A * aeval (Aᴴ * A) p := by
  exact aeval_mul_eq_mul_aeval_of_mul_eq_mul (Matrix.mul_assoc A Aᴴ A) p

omit [DecidableEq m] in
/-- A polynomial filter on an SVD: if
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\sigma_i)\mathbf{V}^{\mathsf{H}}$ is an SVD (in the
sense of `NLAlib.IsSVD`), then
$$\mathbf{A}\,p(\mathbf{A}^{\mathsf{H}}\mathbf{A})
  = \mathbf{U}\operatorname{diag}\bigl(\sigma_i\, p(\sigma_i^2)\bigr)\mathbf{V}^{\mathsf{H}} \,:$$
the part of $p(\mathbf{A}^{\mathsf{H}}\mathbf{A})$ outside the row space is annihilated by
$\mathbf{A}$. -/
theorem IsSVD.mul_aeval_conjTranspose_mul_self {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {σ : r → ℝ} {V : Matrix n r 𝕜} (h : IsSVD A U σ V) (p : ℝ[X]) :
    A * aeval (Aᴴ * A) p =
      U * Matrix.diagonal (fun i => ((σ i * p.eval (σ i ^ 2) : ℝ) : 𝕜)) * Vᴴ := by
  have hV := h.hasOrthonormalCols_right
  have hint : Matrix.diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) * Vᴴ = Vᴴ * (Aᴴ * A) := by
    rw [h.conjTranspose_mul_self_eq]
    simp only [← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul]
  have hp := aeval_mul_eq_mul_aeval_of_mul_eq_mul hint p
  calc A * aeval (Aᴴ * A) p
      = U * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * (Vᴴ * aeval (Aᴴ * A) p) := by
        rw [← Matrix.mul_assoc, ← h.eq]
    _ = U * Matrix.diagonal (fun i => ((σ i * p.eval (σ i ^ 2) : ℝ) : 𝕜)) * Vᴴ := by
        rw [← hp, aeval_diagonal, ← Matrix.mul_assoc, Matrix.mul_assoc U,
          Matrix.diagonal_mul_diagonal]
        simp only [RCLike.ofReal_mul]

omit [DecidableEq n] in
/-- **Singular values of a power-iterated matrix**:
$\sigma_i((\mathbf{A}\mathbf{A}^{\mathsf{H}})^q\mathbf{A}) = \sigma_i(\mathbf{A})^{2q + 1}$ for
every $i$. [HalkoMartinssonTropp2011, §4.5]. -/
theorem singularValues_pow_mul_conjTranspose_self_mul (A : Matrix m n 𝕜) (q i : ℕ) :
    singularValues ((A * Aᴴ) ^ q * A) i = singularValues A i ^ (2 * q + 1) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hB : IsSVD ((A * Aᴴ) ^ q * A) U (fun j => singularValues A j ^ (2 * q + 1)) V := by
    refine ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_right,
      fun j => pow_nonneg (singularValues_nonneg A j) _, ?_⟩
    have hp := h.mul_aeval_conjTranspose_mul_self (X ^ q)
    rw [aeval_X_pow] at hp
    rw [pow_mul_eq_mul_pow_of_mul_eq_mul (Matrix.mul_assoc A Aᴴ A) q, hp]
    congr 3
    funext j
    rw [eval_pow, eval_X, ← pow_mul, ← pow_succ']
  have hanti : Antitone fun j : Fin A.rank => singularValues A j ^ (2 * q + 1) := fun a b hab =>
    pow_le_pow_left₀ (singularValues_nonneg A b) (singularValues_antitone A hab) _
  by_cases hi : i < A.rank
  · exact hB.singularValues_eq hanti ⟨i, hi⟩
  · rw [hB.singularValues_of_le (not_lt.mp hi), (singularValues_eq_zero_iff A).mpr (not_lt.mp hi),
      zero_pow (Nat.succ_ne_zero _)]

omit [DecidableEq n] in
/-- The rank of a power-iterated matrix is the rank of the matrix:
$\operatorname{rank}((\mathbf{A}\mathbf{A}^{\mathsf{H}})^q\mathbf{A})
= \operatorname{rank} \mathbf{A}$. -/
theorem rank_pow_mul_conjTranspose_self_mul (A : Matrix m n 𝕜) (q : ℕ) :
    ((A * Aᴴ) ^ q * A).rank = A.rank := by
  refine eq_of_forall_lt_iff fun k => ?_
  rw [← singularValues_pos_iff ((A * Aᴴ) ^ q * A), ← singularValues_pos_iff A,
    singularValues_pow_mul_conjTranspose_self_mul]
  exact (odd_two_mul_add_one q).pow_pos_iff

/-! ### Vectors with prescribed spectral weights -/

/-- A vector with prescribed spectral weights: for Hermitian $\mathbf{A}$ with spectrum the
finite set $s$ and weights $w \ge 0$ on $s$ there is a vector $\mathbf{v}$ whose spectral
measure is $\sum_{x \in s} w_x\delta_x$: for every real function $g$ and all
$p, r \in \Bbbk[X]$,
$$\bigl(p(\mathbf{A})\mathbf{v}\bigr)^{\mathsf{H}} g(\mathbf{A})\, r(\mathbf{A})\mathbf{v} =
\sum_{x \in s} w_x\, g(x)\,\overline{p(x)}\,r(x) \,.$$
With $p = r$ and $g = 1$, $g = \mathrm{id}$ or $g = \nu$ this is the squared Euclidean,
$\mathbf{A}$- or $\nu(\mathbf{A})$-norm of $p(\mathbf{A})\mathbf{v}$; weights vanishing off a
subset $T \subseteq s$ give a vector in the span of eigenvectors of the eigenvalues in $T$.
The vector is $\mathbf{v} = \sum_{x \in s}\sqrt{w_x}\,\mathbf{u}_x$ for one unit eigenvector
$\mathbf{u}_x$ of each eigenvalue $x$. -/
theorem _root_.Matrix.IsHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {s : Finset ℝ} (hs : spectrum ℝ A = ↑s)
    {w : ℝ → ℝ} (hw : ∀ x ∈ s, 0 ≤ w x) :
    ∃ v : n → 𝕜, ∀ (g : ℝ → ℝ) (p r : 𝕜[X]),
      star (aeval A p *ᵥ v) ⬝ᵥ (cfc g A *ᵥ (aeval A r *ᵥ v)) =
        ∑ x ∈ s, ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜)) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜)
  set e := hA.eigenvalues
  have hU : HasOrthonormalCols U := hA.hasOrthonormalCols_eigenvectorUnitary
  have hAU : A * U = U * Matrix.diagonal fun j => ((e j : ℝ) : 𝕜) := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    conv_lhs => rw [h]
    simp only [U, e, Matrix.mul_assoc]
    rw [Matrix.star_eq_conjTranspose, hU.conjTranspose_mul_self, Matrix.mul_one]
    rfl
  have hcU : ∀ g : ℝ → ℝ, cfc g A * U = U * Matrix.diagonal fun j => ((g (e j) : ℝ) : 𝕜) := by
    intro g
    rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    change U * _ * star U * U = _
    rw [Matrix.mul_assoc, Matrix.star_eq_conjTranspose, hU.conjTranspose_mul_self, Matrix.mul_one]
    rfl
  have hpU : ∀ p : 𝕜[X], aeval A p * U = U * Matrix.diagonal fun j => p.eval ((e j : ℝ) : 𝕜) :=
    fun p => by rw [aeval_mul_eq_mul_aeval_of_mul_eq_mul hAU p, aeval_diagonal_self]
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun g p r => by simp only [Matrix.mulVec_zero, dotProduct_zero, Finset.sum_empty]⟩
  -- one eigenvalue index for each point of the spectrum
  have hmem : ∀ x ∈ s, ∃ j, e j = x := fun x hx => by
    have : x ∈ spectrum ℝ A := by rw [hs]; exact hx
    rwa [hA.spectrum_real_eq_range_eigenvalues] at this
  have : Nonempty n := ⟨(hmem x₀ hx₀).choose⟩
  choose! idx hidx using hmem
  set T := s.image idx
  set c : n → 𝕜 := fun j => if j ∈ T then ((Real.sqrt (w (e j)) : ℝ) : 𝕜) else 0
  refine ⟨U *ᵥ c, fun g p r => ?_⟩
  have hmv : ∀ {M D : Matrix n n 𝕜}, M * U = U * D → ∀ y, M *ᵥ (U *ᵥ y) = U *ᵥ (D *ᵥ y) :=
    fun h y => by rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
  rw [hmv (hpU r), hmv (hcU g), hmv (hpU p), hU.star_mulVec_dotProduct_mulVec, dotProduct]
  set F : ℝ → 𝕜 := fun x => ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜))
  have key : ∀ j, star ((Matrix.diagonal fun j => p.eval ((e j : ℝ) : 𝕜)) *ᵥ c) j *
      ((Matrix.diagonal fun j => ((g (e j) : ℝ) : 𝕜)) *ᵥ
        ((Matrix.diagonal fun j => r.eval ((e j : ℝ) : 𝕜)) *ᵥ c)) j =
      if j ∈ T then F (e j) else 0 := by
    intro j
    simp only [Matrix.mulVec_diagonal, Pi.star_apply, c, F]
    split_ifs with hj
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      have hw' : 0 ≤ w (e (idx x)) := by rw [hidx x hx]; exact hw x hx
      have hsq : ((Real.sqrt (w (e (idx x))) : ℝ) : 𝕜) * ((Real.sqrt (w (e (idx x))) : ℝ) : 𝕜) =
          ((w (e (idx x)) : ℝ) : 𝕜) := by
        rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hw']
      have hc : star ((Real.sqrt (w (e (idx x))) : ℝ) : 𝕜) =
          ((Real.sqrt (w (e (idx x))) : ℝ) : 𝕜) := RCLike.conj_ofReal _
      rw [star_mul', hc, RCLike.ofReal_mul]
      linear_combination (star (p.eval ((e (idx x) : ℝ) : 𝕜)) * ((g (e (idx x)) : ℝ) : 𝕜) *
        r.eval ((e (idx x) : ℝ) : 𝕜)) * hsq
    · rw [mul_zero, mul_zero, star_zero, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_image fun x hx y hy hxy => by rw [← hidx x hx, ← hidx y hy, hxy]]
  exact Finset.sum_congr rfl fun x hx => by rw [hidx x hx]

end NLAlib
