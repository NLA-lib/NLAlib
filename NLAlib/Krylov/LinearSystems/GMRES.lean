/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Grade
public import NLAlib.Krylov.LinearSystems.MinResidual
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.Diagonalizable
public import NLAlib.Matrix.Spectral.HermitianPart
public import NLAlib.ForMathlib.Algebra.Polynomial.Div
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Matrix.Functions.Polynomial
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# The GMRES iterate

The GMRES iterate is defined mathematically: from a start $\mathbf{x}_0$ it is $\mathbf{x}_0$
plus the minimal residual approximation from the Krylov space of the initial residual,
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{K}_q(\mathbf{A}, \mathbf{r}_0))\,\mathbf{r}_0$,
for every square $\mathbf{A}$. It minimises the residual over $\mathbf{x}_0 + \mathcal{K}_q$, its
residual is $(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{K}_q})\mathbf{r}_0 =
p(\mathbf{A})\mathbf{r}_0$
for a residual polynomial $p$, it beats every residual polynomial, and it terminates at the
grade. MINRES is the Hermitian case, with its bounds in `NLAlib.Krylov.LinearSystems.MINRES`; the
Arnoldi realisation is in `NLAlib.Krylov.LinearSystems.GMRESArnoldi`.

Residual norms are the Euclidean `‖WithLp.toLp 2 _‖`, unsquared. Polynomials are over $\Bbbk$,
since the eigenvalues of a general $\mathbf{A}$ are complex; a real matrix with complex
eigenvalues is moved to $\mathbb{C}$ by `complexify` before the diagonalisable bound applies.

## Main definitions

* `NLAlib.gmresIterate`.

## Main results

* `NLAlib.HasOrthonormalCols.gmresIterate_eq`: the frame form.
* `NLAlib.sub_mulVec_gmresIterate`: the residual is a projection residual.
* `NLAlib.isMinOn_gmresIterate`: residual optimality over $\mathbf{x}_0 + \mathcal{K}_q$.
* `NLAlib.eq_gmresIterate_of_conjTranspose_mul_krylovMatrix_mulVec_sub_eq_zero`: the
  Petrov–Galerkin characterisation.
* `NLAlib.norm_sub_mulVec_gmresIterate_succ_le`: the residual norms do not increase.
* `NLAlib.exists_sub_mulVec_gmresIterate_eq_aeval`: the residual polynomial.
* `NLAlib.norm_sub_mulVec_gmresIterate_le_norm_aeval_mulVec`: GMRES beats every residual
  polynomial.
* `NLAlib.gmresIterate_eq_of_krylovGrade_le`: finite termination.
* `NLAlib.norm_sub_mulVec_gmresIterate_le_pseudoConditionNumber_mul`: the bound for
  diagonalisable $\mathbf{A}$.
* `NLAlib.norm_sub_mulVec_gmresIterate_le_sqrt_one_sub_sq_pow`: the field-of-values bound.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-- The **GMRES iterate** after $q$ steps from $\mathbf{x}_0$, with
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$:
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) := \mathbf{x}_0 +
\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{K}_q(\mathbf{A}, \mathbf{r}_0))\,\mathbf{r}_0$,
which is $\mathbf{x}_0 + \mathbf{Q}(\mathbf{A}\mathbf{Q})^{+}\mathbf{r}_0$ for every orthonormal
basis $\mathbf{Q}$ of $\mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$. For Hermitian $\mathbf{A}$ it is
the MINRES iterate. Basis-free, total, not an algorithm; for singular $\mathbf{A}$ the correction
of least norm among the minimisers. Arnoldi with a small least-squares problem computes it
(`gmresIterate_eq_mgsArnoldiMatrix`); for Hermitian $\mathbf{A}$, Lanczos does
(`Matrix.IsHermitian.gmresIterate_eq_lanczosMatrix`).
[SaadSchultz1986, Algorithm 3]; [Saad2003, §6.5]; [PaigeSaunders1975, §6]. Saad and Schultz define
the iterate as the minimiser (4) of the residual over $\mathbf{x}_0 + \mathcal{K}_q$, computed in
the Arnoldi basis; Paige and Saunders define MINRES, the real symmetric case with
$\mathbf{x}_0 = \mathbf{0}$, by the minimum residual problem (2.7) in the Lanczos basis, whose
solution is the one of minimum length. -/
noncomputable def gmresIterate (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  x₀ + minResidualInverse A (krylovMatrix A (b - A *ᵥ x₀) q) *ᵥ (b - A *ᵥ x₀)

/-- The correction $\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) - \mathbf{x}_0$
lies in the Krylov space of the initial residual. -/
theorem gmresIterate_sub_mem_krylovSpace (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    gmresIterate A b x₀ q - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) q := by
  rw [gmresIterate, add_sub_cancel_left]
  exact minResidualInverse_mulVec_mem A _ _

/-- The zeroth iterate $\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, 0)$ is the
start. -/
@[simp]
theorem gmresIterate_zero (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) : gmresIterate A b x₀ 0 = x₀ := by
  have h := gmresIterate_sub_mem_krylovSpace A b x₀ 0
  rwa [krylovSpace_zero, Submodule.mem_bot, sub_eq_zero] at h

/-- **GMRES in any orthonormal basis of the Krylov space**, for every $\mathbf{A}$:
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\mathbf{Q}(\mathbf{A}\mathbf{Q})^{+}\mathbf{r}_0$. [Saad2003, §6.5.1]. -/
theorem HasOrthonormalCols.gmresIterate_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} {b x₀ : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A (b - A *ᵥ x₀) q) :
    gmresIterate A b x₀ q = x₀ + Q *ᵥ (pinv (A * Q) *ᵥ (b - A *ᵥ x₀)) := by
  rw [gmresIterate, hQ.minResidualInverse_eq hK A, Matrix.mulVec_mulVec]

omit [Fintype r] [DecidableEq r] in
/-- The GMRES residual is a projection residual:
$\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) =
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{K}_q})\mathbf{r}_0$, for every $\mathbf{A}$. -/
theorem sub_mulVec_gmresIterate (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    b - A *ᵥ gmresIterate A b x₀ q =
      (1 - rangeProjector (A * krylovMatrix A (b - A *ᵥ x₀) q)) *ᵥ (b - A *ᵥ x₀) := by
  rw [gmresIterate, Matrix.mulVec_add, Matrix.mulVec_mulVec, mul_minResidualInverse,
    Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

omit [Fintype r] [DecidableEq r] in
/-- **The Petrov–Galerkin condition characterises GMRES** for invertible $\mathbf{A}$: with
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$, a vector $\mathbf{y}$ of
$\mathbf{x}_0 + \mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$ with
$(\mathbf{A}\mathbf{K}_q(\mathbf{A}, \mathbf{r}_0))^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\mathbf{y})
= \mathbf{0}$, a residual orthogonal to $\mathbf{A}\mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$, is
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)$. The parallel of
`Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`.
[Saad2003, Proposition 5.3]; [Saad2003, §6.5]. Saad shows, for any square matrix, that this
condition is equivalent to minimising the residual over $\mathbf{x}_0 + \mathcal{K}$, and GMRES
is the method with $\mathcal{K} = \mathcal{K}_q$; invertibility makes the minimiser unique.
Result: gmres-petrov-galerkin -/
theorem eq_gmresIterate_of_conjTranspose_mul_krylovMatrix_mulVec_sub_eq_zero {A : Matrix n n 𝕜}
    (hA : IsUnit A) {b x₀ y : n → 𝕜} {q : ℕ} (hy : y - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) q)
    (h : (A * krylovMatrix A (b - A *ᵥ x₀) q)ᴴ *ᵥ (b - A *ᵥ y) = 0) :
    y = gmresIterate A b x₀ q := by
  have h' : (A * krylovMatrix A (b - A *ᵥ x₀) q)ᴴ *ᵥ ((b - A *ᵥ x₀) - A *ᵥ (y - x₀)) = 0 := by
    rwa [Matrix.mulVec_sub A y x₀, sub_sub_sub_cancel_right]
  rw [gmresIterate, ← eq_minResidualInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero
    (Matrix.mulVec_injective_iff_isUnit.mpr hA) hy h', add_sub_cancel]

omit [Fintype r] [DecidableEq r] in
/-- **GMRES minimises the residual** over $\mathbf{x}_0 + \mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$,
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$, for every $\mathbf{A}$:
$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
\|\mathbf{b} - \mathbf{A}\mathbf{y}\|$ for every such $\mathbf{y}$.
[SaadSchultz1986, §3.1]; [Saad2003, §6.5.1]. Both define GMRES by this property, (4) and (6.26)
there; [Saad2003, Proposition 5.3] proves it from the Petrov–Galerkin condition.
Result: gmres-optimality -/
theorem isMinOn_gmresIterate (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (AffineSubspace.mk' x₀ (krylovSpace A (b - A *ᵥ x₀) q) : Set (n → 𝕜))
      (gmresIterate A b x₀ q) := by
  refine isMinOn_iff.mpr fun y hy => ?_
  have hy' : y - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) q := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub] at hy
    exact hy
  have h := isMinOn_iff.mp (isMinOn_minResidualInverse_mulVec A
    (krylovMatrix A (b - A *ᵥ x₀) q) (b - A *ᵥ x₀)) (y - x₀) hy'
  have e : ∀ w, b - A *ᵥ x₀ - A *ᵥ w = b - A *ᵥ (x₀ + w) := fun w => by
    rw [Matrix.mulVec_add]
    abel
  rwa [e, e, add_sub_cancel] at h

omit [Fintype r] [DecidableEq r] in
/-- The residual norms do not increase, for every $\mathbf{A}$: the residual of
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q + 1)$ is no larger than that of
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)$. -/
theorem norm_sub_mulVec_gmresIterate_succ_le (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ (q + 1))‖ ≤
      ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ := by
  have hmem : gmresIterate A b x₀ q ∈
      (AffineSubspace.mk' x₀ (krylovSpace A (b - A *ᵥ x₀) (q + 1)) : Set (n → 𝕜)) := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
    exact krylovSpace_mono A _ (Nat.le_succ q) (gmresIterate_sub_mem_krylovSpace A b x₀ q)
  exact isMinOn_iff.mp (isMinOn_gmresIterate A b x₀ (q + 1)) _ hmem

omit [Fintype r] [DecidableEq r] in
/-- **The GMRES residual polynomial**: there is $p \in \Bbbk[X]$ with $\deg p \le q$, $p(0) = 1$
and $\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) =
p(\mathbf{A})\mathbf{r}_0$, for every $\mathbf{A}$. [Saad2003, §6.11.4]. -/
theorem exists_sub_mulVec_gmresIterate_eq_aeval (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    ∃ p : 𝕜[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
      b - A *ᵥ gmresIterate A b x₀ q = aeval A p *ᵥ (b - A *ᵥ x₀) := by
  obtain ⟨s, hs, hsb⟩ := mem_krylovSpace_iff.1 (gmresIterate_sub_mem_krylovSpace A b x₀ q)
  refine ⟨1 - X * s, ?_, by simp, ?_⟩
  · rcases eq_or_ne s 0 with rfl | h0
    · simp only [mul_zero, sub_zero]
      exact degree_one_le.trans (by exact_mod_cast Nat.zero_le q)
    · have hnat : s.natDegree < q := (natDegree_lt_iff_degree_lt h0).2 hs
      refine degree_le_of_natDegree_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
      · rw [natDegree_one]
        exact Nat.zero_le q
      · exact natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  · rw [map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hsb, Matrix.mulVec_sub]
    abel

omit [Fintype r] [DecidableEq r] in
/-- **GMRES beats every residual polynomial**: for every $\mathbf{A}$ and $p \in \Bbbk[X]$ with
$\deg p \le q$, $p(0) = 1$, $\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A},
\mathbf{b}, \mathbf{x}_0, q)\| \le \|p(\mathbf{A})\mathbf{r}_0\|$. [Saad2003, §6.11.4].
Result: gmres-polynomial-bound -/
theorem norm_sub_mulVec_gmresIterate_le_norm_aeval_mulVec (A : Matrix n n 𝕜) (b x₀ : n → 𝕜)
    {q : ℕ} {p : 𝕜[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
      ‖WithLp.toLp 2 (aeval A p *ᵥ (b - A *ᵥ x₀))‖ := by
  obtain ⟨s, hs, hps⟩ := exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one hp hp₀
  have hy : aeval A s *ᵥ (b - A *ᵥ x₀) ∈ krylovSpace A (b - A *ᵥ x₀) q :=
    aeval_mulVec_mem_krylovSpace A _ hs
  have hp' : p = 1 - X * s := by rw [← hps, sub_sub_cancel]
  have heq : b - A *ᵥ (x₀ + aeval A s *ᵥ (b - A *ᵥ x₀)) = aeval A p *ᵥ (b - A *ᵥ x₀) := by
    rw [hp', map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_add]
    abel
  have hmem : x₀ + aeval A s *ᵥ (b - A *ᵥ x₀) ∈
      (AffineSubspace.mk' x₀ (krylovSpace A (b - A *ᵥ x₀) q) : Set (n → 𝕜)) := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left]
    exact hy
  have h := isMinOn_iff.mp (isMinOn_gmresIterate A b x₀ q) _ hmem
  rwa [heq] at h

omit [Fintype r] [DecidableEq r] in
/-- **Finite termination**: for invertible $\mathbf{A}$ and $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$, GMRES reaches the solution once $q$ is at least the grade of
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$:
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_\star$.
[SaadSchultz1986, Proposition 2]; [Saad2003, Proposition 6.10]. Both state that the iterate at
the breakdown step, which is the grade ([Saad2003, Proposition 6.6]), is exact.
Result: gmres-finite-termination -/
theorem gmresIterate_eq_of_krylovGrade_le {A : Matrix n n 𝕜} (hA : IsUnit A) {b xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) {q : ℕ} (h : krylovGrade A (b - A *ᵥ x₀) ≤ q) :
    gmresIterate A b x₀ q = xs := by
  have hxs' : A *ᵥ (xs - x₀) = b - A *ᵥ x₀ := by rw [Matrix.mulVec_sub, hxs]
  rw [gmresIterate, minResidualInverse_mulVec_eq_of_mem (Matrix.mulVec_injective_iff_isUnit.mpr hA)
    hxs' (mem_krylovSpace_of_krylovGrade_le hA hxs' h), add_sub_cancel]

omit [Fintype r] [DecidableEq r] in
/-- **The GMRES bound for diagonalisable $\mathbf{A}$**: if
$\mathbf{A}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and
$p \in \Bbbk[X]$, $\deg p \le q$, $p(0) = 1$, satisfies $\lvert p(d_i) \rvert \le \eta$ for every
eigenvalue, then
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
\kappa(\mathbf{V})\,\eta\,\|\mathbf{r}_0\| \,.$$
The hypothesis is the body of `IsDiagonalizable` with its witness ($\mathbf{V}$ invertible, as
`IsUnit V`; `Matrix.isUnit_iff_isUnit_det` converts from `IsDiagonalizable`'s determinant form).
[SaadSchultz1986, Proposition 4, p. 866]; [TrefethenBau1997, Theorem 35.2, p. 271].
Result: gmres-diagonalizable-bound -/
theorem norm_sub_mulVec_gmresIterate_le_pseudoConditionNumber_mul {A V : Matrix n n 𝕜}
    {d : n → 𝕜} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) (b x₀ : n → 𝕜)
    {q : ℕ} {p : 𝕜[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) {η : ℝ}
    (hη : ∀ i, ‖p.eval (d i)‖ ≤ η) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
      pseudoConditionNumber V * η * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  refine (norm_sub_mulVec_gmresIterate_le_norm_aeval_mulVec A b x₀ hp hp₀).trans ?_
  exact (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
    (specNorm_aeval_le_pseudoConditionNumber_mul hV hAV p hη) (norm_nonneg _))

omit [Fintype r] [DecidableEq r] in
/-- **The field-of-values bound** (Elman): if the Hermitian part of $\mathbf{A}$ has spectrum in
$[a, \infty)$, $0 < a$, and $\|\mathbf{A}\|_2 \le a'$, then
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
\Bigl(1 - \frac{a^2}{a'^2}\Bigr)^{q/2}\|\mathbf{r}_0\| \,.$$
The residual polynomial is $(1 - \alpha x)^q$ with $\alpha = a/a'^2$.
[EisenstatElmanSchultz1983, Theorem 3.3, pp. 350–351]; [Saad2003, Theorems 5.10 and 6.30].
Result: gmres-field-of-values-bound -/
theorem norm_sub_mulVec_gmresIterate_le_sqrt_one_sub_sq_pow {A : Matrix n n 𝕜} {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ (hermitianPart A) ⊆ Set.Ici a) (hA : specNorm A ≤ a')
    (b x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
      Real.sqrt (1 - (a / a') ^ 2) ^ q * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  have hH : a • (1 : Matrix n n 𝕜) ≤ hermitianPart A :=
    ((isHermitian_hermitianPart A).smul_one_le_iff_spectrum_subset_Ici a).mpr hs
  set α : ℝ := a / a' ^ 2
  have hB : specNorm (1 - (α : 𝕜) • A) ≤ Real.sqrt (1 - (a / a') ^ 2) := by
    rw [← RCLike.real_smul_eq_coe_smul]
    exact specNorm_one_sub_smul_le_of_smul_one_le_hermitianPart ha.le hH hA
  have hd1 : (1 - C (α : 𝕜) * X : 𝕜[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; exact zero_le_one)
      ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X])))
  have hp : ((1 - C (α : 𝕜) * X) ^ q).degree ≤ (q : WithBot ℕ) :=
    degree_le_of_natDegree_le (natDegree_pow_le.trans
      ((Nat.mul_le_mul_left q hd1).trans_eq (mul_one q)))
  have hp₀ : ((1 - C (α : 𝕜) * X) ^ q).eval 0 = 1 := by
    simp only [eval_pow, eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_zero, sub_zero, one_pow]
  have haeval : aeval A ((1 - C (α : 𝕜) * X) ^ q) = (1 - (α : 𝕜) • A) ^ q := by
    rw [map_pow, map_sub, map_one, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul]
  refine (norm_sub_mulVec_gmresIterate_le_norm_aeval_mulVec A b x₀ hp hp₀).trans ?_
  rw [haeval]
  refine (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact (specNorm_pow_le _ q).trans (pow_le_pow_left₀ (specNorm_nonneg _) hB q)

end NLAlib
