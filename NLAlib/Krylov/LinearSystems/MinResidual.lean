/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.Galerkin
public import NLAlib.Matrix.Basic.ComplementaryProjector
public import NLAlib.Matrix.Pseudoinverse.LeastSquares
public import Mathlib.Analysis.Matrix.Order

/-!
# Minimal residual approximation on a subspace

The minimal residual inverse of $\mathbf{A}$ on the column space of $\mathbf{X}$ is
$(\mathbf{A}\mathbf{P}_{\mathbf{X}})^{+}$. Applied to $\mathbf{b}$ it gives the minimum-norm
vector of the subspace minimising $\|\mathbf{b} - \mathbf{A}\mathbf{y}\|$, for every
$\mathbf{A}$; it depends on the subspace only, and in any orthonormal basis $\mathbf{Q}$ of it
equals $\mathbf{Q}(\mathbf{A}\mathbf{Q})^{+}$. The optimal residual is
$(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{X}})\mathbf{b}$. GMRES and MINRES are the case of a
Krylov space (`NLAlib.gmresIterate`).

It is the Galerkin inverse of the normal equations restricted to the subspace,
$(\mathbf{A}\mathbf{P}_{\mathbf{X}})^{+} =
\mathsf{galerkinInverse}(\mathbf{A}^{\mathsf{H}}\mathbf{A},
\mathbf{X})\,\mathbf{A}^{\mathsf{H}}$ (`minResidualInverse_eq_galerkinInverse`). The residual in
the norm of a positive definite $\mathbf{M}$ is minimised by
$\mathsf{galerkinInverse}(\mathbf{A}^{\mathsf{H}}\mathbf{M}\mathbf{A}, \mathbf{X})\,
\mathbf{A}^{\mathsf{H}}\mathbf{M}\mathbf{b}$
(`Matrix.PosDef.isMinOn_galerkinInverse_conjTranspose_mul_mul_mulVec`),
the core of preconditioned MINRES; at $\mathbf{M} = \mathbf{I}$ the two agree.

## Main definitions

* `NLAlib.minResidualInverse`: $(\mathbf{A}\mathbf{P}_{\mathbf{X}})^{+}$.

## Main results

* `NLAlib.minResidualInverse_eq_of_range_eq`: it depends only on the column space.
* `NLAlib.HasOrthonormalCols.minResidualInverse_eq`: the frame form.
* `NLAlib.mul_minResidualInverse`: $\mathbf{A}$ times it is $\mathbf{P}_{\mathbf{A}\mathbf{X}}$.
* `NLAlib.isMinOn_minResidualInverse_mulVec`: residual optimality.
* `NLAlib.minResidualInverse_eq_galerkinInverse`: the normal-equations form.
* `NLAlib.eq_minResidualInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero`: the
  Petrov–Galerkin characterisation at full column rank.
* `Matrix.PosDef.isMinOn_galerkinInverse_conjTranspose_mul_mul_mulVec`: the weighted residual.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p r : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype r]
  [DecidableEq r]

/-- The **minimal residual inverse** of $\mathbf{A}$ on the column space of $\mathbf{X}$:
$\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X}) := (\mathbf{A}\mathbf{P}_{\mathbf{X}})^{+}$.
For every $\mathbf{A}$, of any shape ($m \times n$, with $\mathbf{X}$ having $n$ rows),
$\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X})\,\mathbf{b}$ is the minimum-norm vector of the
column space minimising $\|\mathbf{b} - \mathbf{A}\mathbf{y}\|$; for $\mathbf{A}$ of full column
rank it is the unique minimiser. Rectangular $\mathbf{A}$ serves sketched GMRES
($\mathbf{S}\mathbf{A}$) and LSQR-type methods. It depends on $\mathbf{X}$ only through its
column space. No junk value: the minimiser always exists. [Saad2003, §5.3.2]. -/
noncomputable def minResidualInverse (A : Matrix m n 𝕜) (X : Matrix n p 𝕜) : Matrix n m 𝕜 :=
  pinv (A * rangeProjector X)

omit [DecidableEq r] in
/-- The range of the minimal residual inverse lies in the column space of $\mathbf{X}$. -/
private lemma range_mulVecLin_minResidualInverse_le (A : Matrix m n 𝕜) (X : Matrix n p 𝕜) :
    LinearMap.range (minResidualInverse A X).mulVecLin ≤ LinearMap.range X.mulVecLin := by
  rw [minResidualInverse, range_pinv, Matrix.conjTranspose_mul,
    conjTranspose_rangeProjector, Matrix.mulVecLin_mul, ← range_rangeProjector X]
  exact LinearMap.range_comp_le_range _ _

omit [DecidableEq r] in
/-- $\mathbf{P}_{\mathbf{X}}$ fixes the minimal residual inverse. -/
private lemma rangeProjector_mul_minResidualInverse (A : Matrix m n 𝕜) (X : Matrix n p 𝕜) :
    rangeProjector X * minResidualInverse A X = minResidualInverse A X :=
  rangeProjector_mul_eq_self_iff.mpr (range_mulVecLin_minResidualInverse_le A X)

omit [DecidableEq r] in
/-- The Galerkin inverse absorbs $\mathbf{P}_{\mathbf{X}}$ on the right:
$(\mathbf{P}\mathbf{G}\mathbf{P})^{+}\mathbf{P} = (\mathbf{P}\mathbf{G}\mathbf{P})^{+}$. -/
private lemma galerkinInverse_mul_rangeProjector (G : Matrix n n 𝕜) (X : Matrix n p 𝕜) :
    galerkinInverse G X * rangeProjector X = galerkinInverse G X := by
  set P := rangeProjector X
  set H := P * G * P
  have hle : LinearMap.range H.mulVecLin ≤ LinearMap.range P.mulVecLin :=
    range_le_iff_exists_mul.mpr ⟨G * P, by simp only [H, Matrix.mul_assoc]⟩
  have hHP : rangeProjector H * P = rangeProjector H := by
    have h := rangeProjector_mul_rangeProjector_of_range_le' hle
    rwa [(isStarProjection_rangeProjector X).rangeProjector_eq] at h
  change pinv H * P = pinv H
  conv_lhs =>
    rw [← pinv_mul_mul_pinv H, Matrix.mul_assoc (pinv H) H, mul_pinv, Matrix.mul_assoc, hHP]
  rw [← mul_pinv, ← Matrix.mul_assoc, pinv_mul_mul_pinv]

omit [DecidableEq r] in
/-- The minimal residual inverse $\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X})$ depends only
on the column space. -/
theorem minResidualInverse_eq_of_range_eq (A : Matrix m n 𝕜) {X : Matrix n p 𝕜}
    {Y : Matrix n r 𝕜} (h : LinearMap.range X.mulVecLin = LinearMap.range Y.mulVecLin) :
    minResidualInverse A X = minResidualInverse A Y := by
  rw [minResidualInverse, minResidualInverse, rangeProjector_inj.mpr h]

/-- **Frame form**, for every $\mathbf{A}$: for $\mathbf{Q}$ with orthonormal columns and the
column space of $\mathbf{X}$, $\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X}) =
\mathbf{Q}(\mathbf{A}\mathbf{Q})^{+}$. [Saad2003, §6.5.1]. -/
theorem HasOrthonormalCols.minResidualInverse_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {X : Matrix n p 𝕜} (h : LinearMap.range Q.mulVecLin = LinearMap.range X.mulVecLin)
    (A : Matrix m n 𝕜) : minResidualInverse A X = Q * pinv (A * Q) := by
  rw [minResidualInverse, ← rangeProjector_inj.mpr h, hQ.rangeProjector_eq, ← Matrix.mul_assoc,
    hQ.pinv_mul_conjTranspose_right]

omit [DecidableEq r] in
/-- The minimal residual approximation
$\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X})\,\mathbf{b}$ lies in the column space, for
every $\mathbf{A}$. -/
theorem minResidualInverse_mulVec_mem (A : Matrix m n 𝕜) (X : Matrix n p 𝕜) (b : m → 𝕜) :
    minResidualInverse A X *ᵥ b ∈ LinearMap.range X.mulVecLin :=
  range_mulVecLin_minResidualInverse_le A X ⟨b, rfl⟩

omit [DecidableEq r] in
/-- The optimal residual projector: $\mathbf{A}\,\mathsf{minResidualInverse}(\mathbf{A},
\mathbf{X}) = \mathbf{P}_{\mathbf{A}\mathbf{X}}$, so the residual of $\mathbf{b}$ is
$(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{X}})\mathbf{b}$. -/
theorem mul_minResidualInverse (A : Matrix m n 𝕜) (X : Matrix n p 𝕜) :
    A * minResidualInverse A X = rangeProjector (A * X) := by
  rw [← rangeProjector_mul_minResidualInverse, ← Matrix.mul_assoc, minResidualInverse, mul_pinv,
    rangeProjector_inj]
  exact range_mul_eq_of_range_eq A (range_rangeProjector X)

omit [DecidableEq r] in
/-- **Minimal residual approximations minimise the residual**: for every $\mathbf{A}$,
$\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X})\,\mathbf{b}$ minimises
$\|\mathbf{b} - \mathbf{A}\mathbf{y}\|$ over the column space of $\mathbf{X}$.
[Saad2003, §5.3.2].
Result: min-residual-optimality -/
theorem isMinOn_minResidualInverse_mulVec (A : Matrix m n 𝕜) (X : Matrix n p 𝕜) (b : m → 𝕜) :
    IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (LinearMap.range X.mulVecLin : Set (n → 𝕜)) (minResidualInverse A X *ᵥ b) := by
  classical
  rintro _ ⟨c, rfl⟩
  have hr : b - A *ᵥ (minResidualInverse A X *ᵥ b) = (1 - rangeProjector (A * X)) *ᵥ b := by
    rw [Matrix.mulVec_mulVec, mul_minResidualInverse, Matrix.sub_mulVec, Matrix.one_mulVec]
  change ‖WithLp.toLp 2 (b - A *ᵥ (minResidualInverse A X *ᵥ b))‖ ≤
    ‖WithLp.toLp 2 (b - A *ᵥ (X *ᵥ c))‖
  rw [hr, Matrix.mulVec_mulVec]
  exact norm_one_sub_rangeProjector_mulVec_le (A * X) b c

omit [DecidableEq r] in
/-- The normal-equations form: $\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X}) =
\mathsf{galerkinInverse}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{X})\,\mathbf{A}^{\mathsf{H}}$,
for every $\mathbf{A}$: the minimal residual method is the Galerkin method for
$\mathbf{A}^{\mathsf{H}}\mathbf{A}$ on the same space. -/
theorem minResidualInverse_eq_galerkinInverse (A : Matrix m n 𝕜) (X : Matrix n p 𝕜) :
    minResidualInverse A X = galerkinInverse (Aᴴ * A) X * Aᴴ := by
  have hG : (A * rangeProjector X)ᴴ * (A * rangeProjector X) =
      rangeProjector X * (Aᴴ * A) * rangeProjector X := by
    rw [Matrix.conjTranspose_mul, conjTranspose_rangeProjector]
    simp only [Matrix.mul_assoc]
  rw [minResidualInverse, pinv_eq_pinv_conjTranspose_mul_self_mul, hG, Matrix.conjTranspose_mul,
    conjTranspose_rangeProjector, ← Matrix.mul_assoc]
  exact congrArg (· * Aᴴ) (galerkinInverse_mul_rangeProjector (Aᴴ * A) X)

omit [DecidableEq r] in
/-- **The Petrov–Galerkin condition characterises the minimal residual approximation** for
$\mathbf{A}$ of full column rank: a vector $\mathbf{y}$ of the column space with
$(\mathbf{A}\mathbf{X})^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\mathbf{y}) = \mathbf{0}$ is
$\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X})\,\mathbf{b}$. [Saad2003, §5.2.2]. -/
theorem eq_minResidualInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero
    {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) {X : Matrix n p 𝕜} {b : m → 𝕜}
    {y : n → 𝕜}
    (hy : y ∈ LinearMap.range X.mulVecLin) (h : (A * X)ᴴ *ᵥ (b - A *ᵥ y) = 0) :
    y = minResidualInverse A X *ᵥ b := by
  obtain ⟨c, rfl⟩ := hy
  rw [Matrix.mulVecLin_apply] at h ⊢
  refine hA ?_
  have h0 := rangeProjector_mulVec_eq_zero_iff.mpr h
  have hAX : A *ᵥ (X *ᵥ c) = (A * X) *ᵥ c := Matrix.mulVec_mulVec c A X
  rw [Matrix.mulVec_sub, hAX, rangeProjector_mulVec_mulVec, sub_eq_zero] at h0
  rw [Matrix.mulVec_mulVec b A (minResidualInverse A X), mul_minResidualInverse, hAX, h0]

omit [DecidableEq r] in
/-- Exactness: for $\mathbf{A}$ of full column rank, if the solution lies in the column space
the
minimal residual approximation $\mathsf{minResidualInverse}(\mathbf{A}, \mathbf{X})\,\mathbf{b}$
is the solution. -/
theorem minResidualInverse_mulVec_eq_of_mem {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {X : Matrix n p 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : A *ᵥ xs = b)
    (h : xs ∈ LinearMap.range X.mulVecLin) : minResidualInverse A X *ᵥ b = xs := by
  refine (eq_minResidualInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero hA h ?_).symm
  rw [hxs, sub_self, Matrix.mulVec_zero]

omit [DecidableEq r] in
/-- **The residual in the $\mathbf{M}$-norm**: for positive definite $\mathbf{M}$ and every
$\mathbf{A}$, $\mathsf{galerkinInverse}(\mathbf{A}^{\mathsf{H}}\mathbf{M}\mathbf{A},
\mathbf{X})\,\mathbf{A}^{\mathsf{H}}\mathbf{M}\mathbf{b}$ minimises
$\|\mathbf{b} - \mathbf{A}\mathbf{y}\|_{\mathbf{M}}^2 = \operatorname{Re}\bigl((\mathbf{b} -
\mathbf{A}\mathbf{y})^{\mathsf{H}}\mathbf{M}(\mathbf{b} - \mathbf{A}\mathbf{y})\bigr)$ over the
column space of $\mathbf{X}$: with $\mathbf{M} = \mathbf{D}^{\mathsf{H}}\mathbf{D}$ and
$\mathbf{B} = \mathbf{D}\mathbf{A}\mathbf{P}_{\mathbf{X}}$ the vector is the least-squares
solution $\mathbf{B}^{+}\mathbf{D}\mathbf{b}$. [Greenbaum1997, Chapter 8, Eq. (8.2), Algorithm 4P];
the source treats the split preconditioned
MINRES instance; the arbitrary weighted least-squares statement here is the generalisation. -/
theorem _root_.Matrix.PosDef.isMinOn_galerkinInverse_conjTranspose_mul_mul_mulVec
    {M : Matrix m m 𝕜} (hM : M.PosDef) (A : Matrix m n 𝕜) (X : Matrix n p 𝕜)
    (b : m → 𝕜) :
    IsMinOn (fun y => RCLike.re (quadForm M (b - A *ᵥ y)))
      (LinearMap.range X.mulVecLin : Set (n → 𝕜))
      (galerkinInverse (Aᴴ * M * A) X *ᵥ (Aᴴ *ᵥ (M *ᵥ b))) := by
  classical
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hD
  subst hD
  set P := rangeProjector X
  set B := D * A * P
  set z := galerkinInverse (Aᴴ * (Dᴴ * D) * A) X *ᵥ (Aᴴ *ᵥ ((Dᴴ * D) *ᵥ b))
  have hq : ∀ v, RCLike.re (quadForm (Dᴴ * D) v) = ‖WithLp.toLp 2 (D *ᵥ v)‖ ^ 2 := fun v => by
    rw [quadForm_conjTranspose_mul_self, RCLike.ofReal_re]
  have hBB : Bᴴ * B = P * (Aᴴ * (Dᴴ * D) * A) * P := by
    simp only [B, Matrix.conjTranspose_mul, conjTranspose_rangeProjector, P, Matrix.mul_assoc]
  have hz : z = pinv B *ᵥ (D *ᵥ b) := by
    have hBv : Bᴴ *ᵥ (D *ᵥ b) = P *ᵥ (Aᴴ *ᵥ ((Dᴴ * D) *ᵥ b)) := by
      simp only [B, Matrix.conjTranspose_mul, conjTranspose_rangeProjector, P,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [pinv_eq_pinv_conjTranspose_mul_self_mul, ← Matrix.mulVec_mulVec, hBv, hBB,
      Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ _) (galerkinInverse_mul_rangeProjector (Aᴴ * (Dᴴ * D) * A) X).symm
  have hPz : P *ᵥ z = z := rangeProjector_mulVec_eq_self_iff.mpr (galerkinInverse_mulVec_mem _ _ _)
  rintro _ ⟨c, rfl⟩
  have hls := isLeastSquaresSolution_pinv_mulVec B (D *ᵥ b) (X *ᵥ c)
  rw [← hz] at hls
  have hBz : B *ᵥ z = D *ᵥ (A *ᵥ z) := by
    rw [← hPz]
    simp only [B, Matrix.mulVec_mulVec, Matrix.mul_assoc, rangeProjector_mul_rangeProjector, P]
  have hBy : B *ᵥ (X *ᵥ c) = D *ᵥ (A *ᵥ (X *ᵥ c)) := by
    simp only [B, P, Matrix.mulVec_mulVec, Matrix.mul_assoc, rangeProjector_mul_self]
  rw [hBz, hBy, ← Matrix.mulVec_sub, ← Matrix.mulVec_sub] at hls
  change RCLike.re (quadForm (Dᴴ * D) (b - A *ᵥ z)) ≤
    RCLike.re (quadForm (Dᴴ * D) (b - A *ᵥ (X *ᵥ c)))
  rw [hq, hq]
  exact pow_le_pow_left₀ (norm_nonneg _) hls 2

end NLAlib
