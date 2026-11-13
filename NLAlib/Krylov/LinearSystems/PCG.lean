/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CG
public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Matrix.Spectral.Congruence

/-!
# The preconditioned conjugate gradient iterate

With a preconditioner $\mathbf{M}$ applied as $\mathbf{M}$ (an approximation of
$\mathbf{A}^{-1}$), the PCG iterate is $\mathbf{x}_0$ plus the Galerkin approximation to the
error from the preconditioned Krylov space
$\mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$:
$\mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{K}_q(\mathbf{M}\mathbf{A},
\mathbf{M}\mathbf{r}_0))\,\mathbf{r}_0$. No square root of $\mathbf{M}$ appears; the definition
needs no hypothesis on $\mathbf{M}$, and $\mathbf{M} = \mathbf{I}$ is CG (`pcgIterate_one`).

For positive definite $\mathbf{A}$ it is the $\mathbf{A}$-norm-optimal point of
$\mathbf{x}_0 + \mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$, and for any factor
$\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$ it is $\mathbf{C}$ times CG on the split system
$\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}\,\hat{\mathbf{x}} = \mathbf{C}^{\mathsf{H}}\mathbf{b}$
(`Matrix.PosDef.pcgIterate_eq_mulVec_cgIterate`), through which every CG bound transfers with the
spectrum of $\mathbf{M}\mathbf{A}$ in place of that of $\mathbf{A}$. The spectral hypothesis is
`spectrum ℝ (M * A) ⊆ s`; spectral equivalence $a\mathbf{M}^{-1} \preceq \mathbf{A} \preceq
a'\mathbf{M}^{-1}$ reaches it through `Matrix.PosDef.spectrum_mul_subset_Icc_of_le`, and the
relative-spectrum form `Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset` covers a
preconditioner given as the matrix it approximates.

Polynomial bounds are written $\lvert p \rvert \le \eta$, since $\mathbf{M}$ names the
preconditioner.

[Saad2003, §9.2] writes the preconditioner as the matrix it approximates; their $\mathbf{M}$ is our
$\mathbf{M}^{-1}$.

## Main definitions

* `NLAlib.pcgIterate`.

## Main results

* `Matrix.PosDef.pcgIterate_eq`: the frame form.
* `Matrix.PosDef.isMinOn_pcgIterate`: $\mathbf{A}$-norm optimality.
* `Matrix.PosDef.eq_pcgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`: the Galerkin
  characterisation.
* `Matrix.PosDef.pcgIterate_eq_mulVec_cgIterate`: PCG is CG on the split system.
* `Matrix.PosDef.re_quadForm_sub_pcgIterate_le`,
  `Matrix.IsHermitian.re_quadForm_sub_pcgIterate_le_four_mul_pow`,
  `Matrix.PosDef.re_quadForm_sub_pcgIterate_le_four_mul_sq_mul_pow`: the polynomial, $\kappa$ and
  outlier bounds in the spectrum of $\mathbf{M}\mathbf{A}$.
* `Matrix.PosDef.re_quadForm_sub_pcgIterate_le_residualMinimax_sq_mul`: the spectrum-optimal
  bound.
* `Matrix.PosDef.pcgIterate_eq_of_krylovGrade_le`: finite termination.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-- The **preconditioned conjugate gradient iterate** after $q$ steps from $\mathbf{x}_0$, with
preconditioner $\mathbf{M}$ applied as $\mathbf{M}$ and $\mathbf{r}_0 = \mathbf{b} -
\mathbf{A}\mathbf{x}_0$:
$\mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) := \mathbf{x}_0 +
\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{K}_q(\mathbf{M}\mathbf{A},
\mathbf{M}\mathbf{r}_0))\,\mathbf{r}_0$. Basis-free, total, no square root; the preconditioned
Hestenes–Stiefel recurrence computes it (`Matrix.PosDef.pcgState_x_eq`). Junk value: that of
`galerkinInverse` when the compression of $\mathbf{A}$ is singular.
[Saad2003, §9.2.1]; [Greenbaum1997, Chapter 8, Algorithm 2P].
Algorithm: pcg (specification) -/
noncomputable def pcgIterate (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  x₀ + galerkinInverse A (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) *ᵥ (b - A *ᵥ x₀)

/-- The correction
$\mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) - \mathbf{x}_0$
lies in the preconditioned Krylov space, for every $\mathbf{A}$, $\mathbf{M}$. -/
theorem pcgIterate_sub_mem_krylovSpace (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    pcgIterate A M b x₀ q - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q := by
  rw [pcgIterate, add_sub_cancel_left]
  exact galerkinInverse_mulVec_mem A _ _

/-- The zeroth iterate $\mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, 0)$
is the start. -/
@[simp]
theorem pcgIterate_zero (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) : pcgIterate A M b x₀ 0 = x₀ := by
  have h := pcgIterate_sub_mem_krylovSpace A M b x₀ 0
  rwa [krylovSpace_zero, Submodule.mem_bot, sub_eq_zero] at h

/-- No preconditioner is CG: $\mathsf{pcgIterate}(\mathbf{A}, \mathbf{I}, \mathbf{b},
\mathbf{x}_0, q) = \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)$. -/
@[simp]
theorem pcgIterate_one (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    pcgIterate A 1 b x₀ q = cgIterate A b x₀ q := by
  rw [pcgIterate, cgIterate, Matrix.one_mul, Matrix.one_mulVec]

/-- **PCG in any orthonormal basis of the preconditioned Krylov space**, for positive definite
$\mathbf{A}$: $\mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) =
\mathbf{x}_0 + \mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}
\mathbf{Q}^{\mathsf{H}}\mathbf{r}_0$. [Saad2003, §9.2]. -/
theorem _root_.Matrix.PosDef.pcgIterate_eq {A : Matrix n n 𝕜} (hA : A.PosDef) (M : Matrix n n 𝕜)
    {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) {b x₀ : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) :
    pcgIterate A M b x₀ q = x₀ + Q *ᵥ ((Qᴴ * A * Q)⁻¹ *ᵥ (Qᴴ *ᵥ (b - A *ᵥ x₀))) := by
  rw [pcgIterate, hA.galerkinInverse_eq hQ hK, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

omit [Fintype r] [DecidableEq r] in
/-- The Galerkin condition characterises PCG: for positive definite $\mathbf{A}$, a vector
of $\mathbf{x}_0 + \mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$ whose residual is
orthogonal to that space is the PCG iterate
$\mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)$. -/
theorem _root_.Matrix.PosDef.eq_pcgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero
    {A : Matrix n n 𝕜} (hA : A.PosDef) {M : Matrix n n 𝕜} {b x₀ y : n → 𝕜} {q : ℕ}
    (hy : y - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q)
    (h : (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q)ᴴ *ᵥ (b - A *ᵥ y) = 0) :
    y = pcgIterate A M b x₀ q := by
  have h' : (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q)ᴴ *ᵥ
      ((b - A *ᵥ x₀) - A *ᵥ (y - x₀)) = 0 := by
    rwa [Matrix.mulVec_sub A y x₀, sub_sub_sub_cancel_right]
  rw [pcgIterate, ← hA.eq_galerkinInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero hy h',
    add_sub_cancel]

omit [Fintype r] [DecidableEq r] in
/-- **PCG minimises the $\mathbf{A}$-norm error** over
$\mathbf{x}_0 + \mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$, for positive definite
$\mathbf{A}$ and every $\mathbf{M}$, with $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$:
$\|\mathbf{x}_\star - \mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0,
q)\|_{\mathbf{A}}^2 \le \|\mathbf{x}_\star - \mathbf{y}\|_{\mathbf{A}}^2$ for every such
$\mathbf{y}$. [Saad2003, §9.2].
Result: pcg-optimality -/
theorem _root_.Matrix.PosDef.isMinOn_pcgIterate {A : Matrix n n 𝕜} (hA : A.PosDef)
    (M : Matrix n n 𝕜) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    IsMinOn (fun y => RCLike.re (quadForm A (xs - y)))
      (AffineSubspace.mk' x₀ (krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) : Set (n → 𝕜))
      (pcgIterate A M b x₀ q) := by
  refine isMinOn_iff.mpr fun y hy => ?_
  have hy' : y - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub] at hy
    exact hy
  have hxs' : A *ᵥ (xs - x₀) = b - A *ᵥ x₀ := by rw [Matrix.mulVec_sub, hxs]
  have h := isMinOn_iff.mp (hA.isMinOn_galerkinInverse_mulVec
    (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) hxs') (y - x₀) hy'
  rwa [sub_sub_sub_cancel_right, ← sub_add_eq_sub_sub_swap, add_comm] at h

omit [Fintype r] [DecidableEq r] in
/-- **PCG is CG on the split system**: for positive definite $\mathbf{A}$, invertible
$\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$ and
$\mathbf{C}\mathbf{y}_0 = \mathbf{x}_0$,
$\mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) =
\mathbf{C}\,\mathsf{cgIterate}(\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C},
\mathbf{C}^{\mathsf{H}}\mathbf{b}, \mathbf{y}_0, q)$. Any factor works, the Cholesky factor or
$\mathbf{M}^{1/2}$. [Saad2003, §9.2.1].
Result: pcg-split-system -/
theorem _root_.Matrix.PosDef.pcgIterate_eq_mulVec_cgIterate {A : Matrix n n 𝕜} (hA : A.PosDef)
    {M C : Matrix n n 𝕜} (hC : IsUnit C) (hM : M = C * Cᴴ) {b x₀ y₀ : n → 𝕜}
    (hy₀ : C *ᵥ y₀ = x₀) (q : ℕ) :
    pcgIterate A M b x₀ q = C *ᵥ cgIterate (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ q := by
  have hA' : (Cᴴ * A * C).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hC).mpr hA
  have hr := Matrix.conjTranspose_mulVec_sub_mulVec_mulVec A C b y₀
  rw [hy₀] at hr
  have hK : krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q =
      C * krylovMatrix (Cᴴ * A * C) (Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y₀) q := by
    have h := krylovMatrix_mul_mulVec (Cᴴ * A) C (Cᴴ *ᵥ (b - A *ᵥ x₀)) q
    rwa [← Matrix.mul_assoc, Matrix.mulVec_mulVec, ← hM, hr] at h
  refine (hA.eq_pcgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero ?_ ?_).symm
  · obtain ⟨w, hw⟩ := cgIterate_sub_mem_krylovSpace (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ q
    refine ⟨w, ?_⟩
    rw [Matrix.mulVecLin_apply] at hw ⊢
    rw [hK, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_sub, hy₀]
  · have h := hA'.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero (Cᴴ *ᵥ b) y₀ q
    rwa [hK, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec,
      Matrix.conjTranspose_mulVec_sub_mulVec_mulVec]

/-- The split system behind every PCG bound: a factor $\mathbf{M} =
\mathbf{S}\mathbf{S}^{\mathsf{H}}$, the solution and start $\mathbf{S}^{-1}\mathbf{x}_\star$,
$\mathbf{S}^{-1}\mathbf{x}_0$ of the split system, its spectrum, and the $\mathbf{A}$-norm errors
of PCG as the errors of CG on it. -/
private lemma exists_split {A M : Matrix n n 𝕜} (hA : A.PosDef) (hM : M.PosDef) {b xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) :
    ∃ S : Matrix n n 𝕜, ∃ ys y₀ : n → 𝕜, (Sᴴ * A * S).PosDef ∧
      spectrum ℝ (Sᴴ * A * S) = spectrum ℝ (M * A) ∧ (Sᴴ * A * S) *ᵥ ys = Sᴴ *ᵥ b ∧
      RCLike.re (quadForm A (xs - x₀)) = RCLike.re (quadForm (Sᴴ * A * S) (ys - y₀)) ∧
      ∀ q, RCLike.re (quadForm A (xs - pcgIterate A M b x₀ q)) =
        RCLike.re (quadForm (Sᴴ * A * S) (ys - cgIterate (Sᴴ * A * S) (Sᴴ *ᵥ b) y₀ q)) := by
  obtain ⟨S, hS, hMS⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  have hSu := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hSv : ∀ v, S *ᵥ (S⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hSu, Matrix.one_mulVec]
  refine ⟨S, S⁻¹ *ᵥ xs, S⁻¹ *ᵥ x₀, (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hA,
    ?_, ?_, ?_, fun q => ?_⟩
  · rw [hMS, spectrum_mul_conjTranspose_mul hS]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSv, hxs]
  · rw [quadForm_conjTranspose_mul_mul, Matrix.mulVec_sub, hSv, hSv]
  · rw [quadForm_conjTranspose_mul_mul, Matrix.mulVec_sub, hSv,
      ← hA.pcgIterate_eq_mulVec_cgIterate hS hMS (hSv x₀) q]

omit [Fintype r] [DecidableEq r] in
/-- **The polynomial bound for PCG**: for positive definite $\mathbf{A}$ and $\mathbf{M}$ with
the spectrum of $\mathbf{M}\mathbf{A}$ in $s$, and a real $p$ with $\deg p \le q$, $p(0) = 1$,
$\lvert p \rvert \le \eta$ on $s$,
$$\|\mathbf{x}_\star - \mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0,
q)\|_{\mathbf{A}}^2 \le \eta^2\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,.$$
[Saad2003, §9.2]. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_pcgIterate_le {A M : Matrix n n 𝕜} (hA : A.PosDef)
    (hM : M.PosDef) {s : Set ℝ} (hs : spectrum ℝ (M * A) ⊆ s) {b xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) {q : ℕ} {p : ℝ[X]} (hp : p.degree ≤ q)
    (hp₀ : p.eval 0 = 1) {η : ℝ} (hη : ∀ x ∈ s, |p.eval x| ≤ η) :
    RCLike.re (quadForm A (xs - pcgIterate A M b x₀ q)) ≤
      η ^ 2 * RCLike.re (quadForm A (xs - x₀)) := by
  obtain ⟨S, ys, y₀, hA', hspec, hys, h₀, hq⟩ := exists_split hA hM hxs x₀
  rw [hq, h₀]
  exact hA'.re_quadForm_sub_cgIterate_le (hspec.subset.trans hs) hys y₀ hp hp₀ hη

omit [Fintype r] [DecidableEq r] in
/-- **The Chebyshev bound for PCG** in $\kappa = a'/a$: for Hermitian $\mathbf{A}$, positive
definite $\mathbf{M}$ and the spectrum of $\mathbf{M}\mathbf{A}$ in $[a, a']$, $0 < a$,
$$\|\mathbf{x}_\star - \mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0,
q)\|_{\mathbf{A}}^2 \le 4\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2q}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,.$$
Spectral equivalence $a\mathbf{M}^{-1} \preceq \mathbf{A} \preceq a'\mathbf{M}^{-1}$ gives the
hypothesis by `Matrix.PosDef.spectrum_mul_subset_Icc_of_le`. [Saad2003, §9.2.1, Theorem 6.29];
[Greenbaum1997, Chapter 8, Eq. (8.2), Theorem 3.1.1].
Result: pcg-chebyshev-bound -/
theorem _root_.Matrix.IsHermitian.re_quadForm_sub_pcgIterate_le_four_mul_pow
    {A M : Matrix n n 𝕜} (hA : A.IsHermitian) (hM : M.PosDef) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ (M * A) ⊆ Set.Icc a a') {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    RCLike.re (quadForm A (xs - pcgIterate A M b x₀ q)) ≤
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q) *
        RCLike.re (quadForm A (xs - x₀)) := by
  have hpd : A.PosDef := by
    obtain ⟨S, hS, hMS⟩ := hM.exists_isUnit_eq_mul_conjTranspose
    have hH : (Sᴴ * A * S).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul S hA
    have hs' : spectrum ℝ (Sᴴ * A * S) ⊆ Set.Icc a a' := by
      rwa [← spectrum_mul_conjTranspose_mul hS, ← hMS]
    refine (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mp ?_
    exact hH.posDef_iff_eigenvalue_pos.mpr fun k hk =>
      ha.trans_le (hH.spectrum_subset_iff.mp hs' k hk).1
  obtain ⟨p, hp, hp₀, hpI⟩ := exists_degree_le_eval_zero_eq_one_abs_eval_le (a' := a') ha q
  refine (hpd.re_quadForm_sub_pcgIterate_le hM hs hxs x₀ hp hp₀ hpI).trans_eq ?_
  ring

omit [Fintype r] [DecidableEq r] in
/-- **PCG kills outlying eigenvalues of $\mathbf{M}\mathbf{A}$**: for positive definite
$\mathbf{A}$ and $\mathbf{M}$ with the spectrum of $\mathbf{M}\mathbf{A}$ in $[a, a'] \cup T$,
$0 < a$, and $\lvert\prod_{t \in T}(1 - x/t)\rvert \le C$ on $[a, a']$,
$$\|\mathbf{x}_\star - \mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0,
m + d)\|_{\mathbf{A}}^2 \le 4C^2\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2d}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,,$$
$m = \lvert T \rvert$. The form used for low-rank-plus-identity preconditioners.
Result: pcg-outlier-bound -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_pcgIterate_le_four_mul_sq_mul_pow
    {A M : Matrix n n 𝕜} (hA : A.PosDef) (hM : M.PosDef) {a a' : ℝ} (ha : 0 < a)
    {T : Finset ℝ} (hs : spectrum ℝ (M * A) ⊆ Set.Icc a a' ∪ ↑T) {C : ℝ}
    (hC : ∀ x ∈ Set.Icc a a', |∏ t ∈ T, (1 - x / t)| ≤ C) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (x₀ : n → 𝕜) (d : ℕ) :
    RCLike.re (quadForm A (xs - pcgIterate A M b x₀ (T.card + d))) ≤
      4 * C ^ 2 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * d) *
        RCLike.re (quadForm A (xs - x₀)) := by
  obtain ⟨S, ys, y₀, hA', hspec, hys, h₀, hq⟩ := exists_split hA hM hxs x₀
  rw [hq, h₀]
  exact hA'.re_quadForm_sub_cgIterate_le_four_mul_sq_mul_pow ha (hspec.subset.trans hs) hC hys
    y₀ d

omit [Fintype r] [DecidableEq r] in
/-- **The spectrum-optimal bound for PCG**: for positive definite $\mathbf{A}$ and $\mathbf{M}$
and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{x}_\star - \mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0,
q)\|_{\mathbf{A}}^2 \le \mathsf{residualMinimax}(\sigma(\mathbf{M}\mathbf{A}), q)^2
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,,$$
where $\mathsf{residualMinimax}(\sigma(\mathbf{M}\mathbf{A}), q) =
\min_{p}\max_{\lambda \in \sigma(\mathbf{M}\mathbf{A})}\lvert p(\lambda) \rvert$ over real $p$
with $\deg p \le q$, $p(0) = 1$. It is the CG theorem for the split system.
[Saad2003, Theorem 6.29]; [Saad2003, §9.2.1]. The proof of Theorem 6.29 gives the CG bound with
the maximum over the eigenvalues, and §9.2.1 shows that PCG is CG on the split system
$\mathbf{L}^{-1}\mathbf{A}\mathbf{L}^{-\mathsf{H}}$, $\mathbf{M}^{-1} =
\mathbf{L}\mathbf{L}^{\mathsf{H}}$, whose spectrum is that of $\mathbf{M}\mathbf{A}$ (Saad's
preconditioner is $\mathbf{M}^{-1}$ here); Saad works over $\mathbb{R}$.
Result: pcg-spectrum-minimax-bound -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_pcgIterate_le_residualMinimax_sq_mul
    {A M : Matrix n n 𝕜} (hA : A.PosDef) (hM : M.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - pcgIterate A M b x₀ q)) ≤
      residualMinimax (spectrum ℝ (M * A)) q ^ 2 * RCLike.re (quadForm A (xs - x₀)) := by
  obtain ⟨S, ys, y₀, hA', hspec, hys, h₀, hq⟩ := exists_split hA hM hxs x₀
  rw [hq, h₀, ← hspec]
  exact hA'.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul hys y₀ q

omit [Fintype r] [DecidableEq r] in
/-- **Finite termination**: for positive definite $\mathbf{A}$ and $\mathbf{M}$ and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, PCG reaches the solution once $q$ is at least the grade
of $\mathbf{M}\mathbf{r}_0$ for $\mathbf{M}\mathbf{A}$, $\mathbf{r}_0 = \mathbf{b} -
\mathbf{A}\mathbf{x}_0$:
$\mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_\star$.
[Saad2003, Proposition 5.6]; [Saad2003, §9.2.1]. A projection method onto an invariant subspace
containing the right side is exact (Proposition 5.6), the Krylov space is invariant from the
grade on ([Saad2003, Proposition 6.1]), and PCG is CG on the split system (§9.2.1).
Result: pcg-finite-termination -/
theorem _root_.Matrix.PosDef.pcgIterate_eq_of_krylovGrade_le {A M : Matrix n n 𝕜}
    (hA : A.PosDef) (hM : M.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) {q : ℕ}
    (h : krylovGrade (M * A) (M *ᵥ (b - A *ᵥ x₀)) ≤ q) : pcgIterate A M b x₀ q = xs := by
  obtain ⟨S, hS, hMS⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  have hSu := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hSv : ∀ v, S *ᵥ (S⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hSu, Matrix.one_mulVec]
  have hA' : (Sᴴ * A * S).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hA
  have hys : (Sᴴ * A * S) *ᵥ (S⁻¹ *ᵥ xs) = Sᴴ *ᵥ b := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSv, hxs]
  have hr := Matrix.conjTranspose_mulVec_sub_mulVec_mulVec A S b (S⁻¹ *ᵥ x₀)
  rw [hSv] at hr
  have hg : krylovGrade (Sᴴ * A * S) (Sᴴ *ᵥ b - (Sᴴ * A * S) *ᵥ (S⁻¹ *ᵥ x₀)) ≤ q := by
    rwa [← hr, ← krylovGrade_mul_mulVec hS (Sᴴ * A), Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      ← hMS]
  rw [hA.pcgIterate_eq_mulVec_cgIterate hS hMS (hSv x₀) q,
    hA'.cgIterate_eq_of_krylovGrade_le hys _ hg, hSv]

end NLAlib
