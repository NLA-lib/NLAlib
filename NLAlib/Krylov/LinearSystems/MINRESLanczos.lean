/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.GMRESArnoldi
public import NLAlib.Krylov.LinearSystems.MINRES
public import NLAlib.Krylov.Processes.PreconditionedLanczos

/-!
# MINRES through the Lanczos recurrence

For Hermitian $\mathbf{A}$ the Hessenberg matrix of GMRES is tridiagonal, and the Lanczos
recurrence computes the basis and the $(q + 1) \times q$ tridiagonal matrix
$\underline{\mathbf{T}}_q$, the first $q$ columns of the computed $\mathbf{T}_{q+1}$. MINRES is
then $\mathbf{x}_0 + \|\mathbf{r}_0\|\,\mathbf{Q}_q\underline{\mathbf{T}}_q^{+}\mathbf{e}_0$, for
every $q$. Preconditioned MINRES is the same with the preconditioned Lanczos recurrence (one
application of $\mathbf{M}$ per step) and $\beta_0 = \|\mathbf{r}_0\|_{\mathbf{M}}$.

The Paige–Saunders short recurrence, which updates the iterate through Givens rotations of
$\underline{\mathbf{T}}_q$ with three vectors of storage, is proved equal to these forms in
`NLAlib/Krylov/LinearSystems/MINRESRecurrence.lean` (`Matrix.IsHermitian.minresState_x_eq`).

## Main results

* `Matrix.IsHermitian.gmresIterate_eq_lanczosMatrix`: the Lanczos recurrence yields MINRES.
* `Matrix.IsHermitian.pminresIterate_eq_preconditionedLanczosMatrix`: the preconditioned
  Lanczos recurrence yields preconditioned MINRES.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Lanczos recurrence yields MINRES**: for Hermitian $\mathbf{A}$ and every $q$,
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\|\mathbf{r}_0\|\,\mathbf{Q}_q\underline{\mathbf{T}}_q^{+}\mathbf{e}_0$ with $\mathbf{Q}_q$ and
$\underline{\mathbf{T}}_q$ computed by the Lanczos recurrence from $\mathbf{r}_0$, with no grade
hypothesis. [PaigeSaunders1975, §6]; [Greenbaum1997, §2.5, Algorithm 4]. Paige
and Saunders put the Lanczos vectors into the minimum residual problem (2.7) through (6.1) and
(6.2), for real symmetric $\mathbf{A}$ and up to termination.
Result: minres-lanczos -/
theorem _root_.Matrix.IsHermitian.gmresIterate_eq_lanczosMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b x₀ : n → 𝕜) (q : ℕ) :
    gmresIterate A b x₀ q = x₀ + (‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ : 𝕜) •
      (lanczosMatrix A (b - A *ᵥ x₀) q *ᵥ
        (pinv ((lanczosTridiagonal A (b - A *ᵥ x₀) (q + 1)).submatrix id Fin.castSucc) *ᵥ
          Pi.single 0 1)) := by
  rw [hA.lanczosMatrix_eq_arnoldiMatrix, hA.lanczosTridiagonal_eq,
    submatrix_conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_castSucc,
    gmresIterate_eq_arnoldiMatrix]

/-- **The preconditioned Lanczos recurrence yields preconditioned MINRES**: for invertible
Hermitian $\mathbf{A}$, positive definite $\mathbf{M}$ and every $q$,
$\mathsf{pminresIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\|\mathbf{r}_0\|_{\mathbf{M}}\,\mathbf{Z}_q\underline{\mathbf{T}}_q^{+}\mathbf{e}_0$ with
$\mathbf{Z}_q$ and $\underline{\mathbf{T}}_q$ computed by the preconditioned recurrence from
$\mathbf{r}_0$, with no grade hypothesis. [Greenbaum1997, Chapter 8, pp. 121–122, Algorithm 4P].
Result: pminres-lanczos -/
theorem _root_.Matrix.IsHermitian.pminresIterate_eq_preconditionedLanczosMatrix
    {A M : Matrix n n 𝕜} (hA : A.IsHermitian) (hAu : IsUnit A) (hM : M.PosDef) (b x₀ : n → 𝕜)
    (q : ℕ) :
    pminresIterate A M b x₀ q = x₀ +
      ((Real.sqrt (RCLike.re (quadForm M (b - A *ᵥ x₀))) : ℝ) : 𝕜) •
      (preconditionedLanczosMatrix A M (b - A *ᵥ x₀) q *ᵥ
        (pinv ((preconditionedLanczosTridiagonal A M (b - A *ᵥ x₀) (q + 1)).submatrix id
          Fin.castSucc) *ᵥ Pi.single 0 1)) := by
  obtain ⟨C, hC, hMC⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, C *ᵥ y₀ = x₀ :=
    ⟨C⁻¹ *ᵥ x₀, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv C
      ((Matrix.isUnit_iff_isUnit_det C).mp hC), Matrix.one_mulVec]⟩
  have hr : Cᴴ *ᵥ (b - A *ᵥ x₀) = Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y₀ := by
    rw [← hy₀]
    exact Matrix.conjTranspose_mulVec_sub_mulVec_mulVec A C b y₀
  have hn : Real.sqrt (RCLike.re (quadForm M (b - A *ᵥ x₀))) =
      ‖WithLp.toLp 2 (Cᴴ *ᵥ (b - A *ᵥ x₀))‖ := by
    rw [hMC, quadForm_mul_conjTranspose_self, RCLike.ofReal_re, Real.sqrt_sq (norm_nonneg _)]
  have hH := Matrix.isHermitian_conjTranspose_mul_mul C hA
  rw [pminresIterate_eq_mulVec_gmresIterate hAu hC hMC hy₀, hH.gmresIterate_eq_lanczosMatrix,
    hA.preconditionedLanczosMatrix_eq hMC, hA.preconditionedLanczosTridiagonal_eq hMC,
    hH.lanczosMatrix_eq_arnoldiMatrix, hH.lanczosTridiagonal_eq, hn, hr, Matrix.mulVec_add, hy₀,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]

end NLAlib
