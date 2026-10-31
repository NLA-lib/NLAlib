/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.Matrix.Spectral.EigenvalueListing

/-!
# Left and right eigenvectors

A right eigenvector of a square matrix over a field is a vector $\mathbf{x}$ with
$\mathbf{A}\mathbf{x} = \mu\mathbf{x}$, a left eigenvector a vector $\mathbf{y}$ with
$\mathbf{y}^{\mathsf{T}}\mathbf{A} = \mu\mathbf{y}^{\mathsf{T}}$. Left and right eigenvectors for
different eigenvalues are orthogonal for the pairing $\mathbf{y}^{\mathsf{T}}\mathbf{x}$; for an
eigenvalue whose eigenspace is a line, the pairing of its left and right eigenvectors decides
whether the eigenvalue is a simple root of the characteristic polynomial, and the adjugate of
$\mathbf{A} - \mu\mathbf{I}$ is a nonzero multiple of $\mathbf{x}\mathbf{y}^{\mathsf{T}}$.

## Main results

* `NLAlib.exists_mulVec_eq_smul_of_mem_spectrum`, `NLAlib.exists_vecMul_eq_smul_of_mem_spectrum`:
  eigenvalues have right and left eigenvectors.
* `NLAlib.dotProduct_eq_zero_of_vecMul_eq_smul_of_mulVec_eq_smul`: biorthogonality.
* `NLAlib.rootMultiplicity_charpoly_eq_one_iff_dotProduct_ne_zero`: simple eigenvalues through
  the pairing.
* `NLAlib.exists_adjugate_eq_smul_vecMulVec`: the adjugate at a geometrically simple eigenvalue.
* `NLAlib.exists_inv_mul_mul_apply_eq_of_dotProduct_ne_zero`: paired-basis deflation with a
  normalized inverse row and the corresponding rank-one projector.
* `NLAlib.exists_inv_mul_mul_apply_eq_of_rootMultiplicity_eq_one`: a simple eigenvalue is
  excluded from the complementary block.
* `NLAlib.nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div`: the perturbation entry in a
  paired basis.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Existence and biorthogonality -/

/-- Every eigenvalue has a right eigenvector: for $\mu$ in the spectrum of $\mathbf{A}$ there is
$\mathbf{x} \ne \mathbf{0}$ with $\mathbf{A}\mathbf{x} = \mu\mathbf{x}$. -/
theorem exists_mulVec_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ x : n → K, x ≠ 0 ∧ A *ᵥ x = μ • x := by
  have hdet : (Matrix.scalar n μ - A).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
  obtain ⟨x, hx, h⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨x, hx, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  rw [← h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- Every eigenvalue has a left eigenvector: for $\mu$ in the spectrum of $\mathbf{A}$ there is
$\mathbf{y} \ne \mathbf{0}$ with $\mathbf{y}^{\mathsf{T}}\mathbf{A} = \mu\mathbf{y}^{\mathsf{T}}$.
-/
theorem exists_vecMul_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ y : n → K, y ≠ 0 ∧ y ᵥ* A = μ • y := by
  have hT : μ ∈ spectrum K Aᵀ := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose,
      ← Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact hμ
  obtain ⟨y, hy, h⟩ := exists_mulVec_eq_smul_of_mem_spectrum hT
  exact ⟨y, hy, by rwa [Matrix.mulVec_transpose] at h⟩

omit [DecidableEq n] in
/-- **Biorthogonality**: left and right eigenvectors for different eigenvalues are orthogonal: if
$\mathbf{A}\mathbf{x} = \alpha\mathbf{x}$, $\mathbf{y}^{\mathsf{T}}\mathbf{A} =
\mu\mathbf{y}^{\mathsf{T}}$ and $\alpha \ne \mu$, then $\mathbf{y}^{\mathsf{T}}\mathbf{x} = 0$.
[HornJohnson2013, Theorem 1.4.7]. -/
theorem dotProduct_eq_zero_of_vecMul_eq_smul_of_mulVec_eq_smul {A : Matrix n n K} {x y : n → K}
    {α μ : K} (hx : A *ᵥ x = α • x) (hy : y ᵥ* A = μ • y) (h : α ≠ μ) : y ⬝ᵥ x = 0 := by
  have h1 : α * (y ⬝ᵥ x) = μ * (y ⬝ᵥ x) := by
    rw [← smul_eq_mul, ← dotProduct_smul, ← hx, Matrix.dotProduct_mulVec, hy, smul_dotProduct,
      smul_eq_mul]
  exact (mul_eq_mul_right_iff.mp h1).resolve_left h

/-! ### Simple eigenvalues -/

/-- The kernel of $\mathbf{A} - \mu\mathbf{I}$ is the eigenspace of $\mu$. -/
private theorem ker_mulVecLin_sub_smul_one (A : Matrix n n K) (μ : K) :
    LinearMap.ker (A - μ • (1 : Matrix n n K)).mulVecLin =
      Module.End.eigenspace (Matrix.toLin' A) μ := by
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Module.End.mem_eigenspace_iff,
    Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

/-- Powers of $\mathbf{A} - \mu\mathbf{I}$ as a linear map and as a matrix. -/
private theorem toLin'_sub_smul_one_pow_apply (A : Matrix n n K) (μ : K) (k : ℕ) (z : n → K) :
    ((Matrix.toLin' A - μ • 1) ^ k) z = (A - μ • (1 : Matrix n n K)) ^ k *ᵥ z := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_pow, map_sub, map_smul, Matrix.toLin'_one]
  rfl

omit [DecidableEq n] in
/-- A matrix with a kernel of dimension one has in its range every vector orthogonal to a
nonzero left null vector: if $\mathbf{y}^{\mathsf{T}}\mathbf{N} = \mathbf{0}$,
$\mathbf{y} \ne \mathbf{0}$ and $\mathbf{y}^{\mathsf{T}}\mathbf{x} = 0$, then
$\mathbf{N}\mathbf{z} = \mathbf{x}$ for some $\mathbf{z}$. -/
private theorem exists_mulVec_eq_of_dotProduct_eq_zero {N : Matrix n n K} {x y : n → K}
    (hy : y ≠ 0) (hyN : y ᵥ* N = 0) (hker : Module.finrank K (LinearMap.ker N.mulVecLin) = 1)
    (hpair : y ⬝ᵥ x = 0) : ∃ z : n → K, N *ᵥ z = x := by
  classical
  let ℓ : (n → K) →ₗ[K] K :=
    { toFun z := y ⬝ᵥ z
      map_add' := dotProduct_add y
      map_smul' c z := by rw [dotProduct_smul]; rfl }
  have hle : LinearMap.range N.mulVecLin ≤ LinearMap.ker ℓ := by
    rintro _ ⟨z, rfl⟩
    change y ⬝ᵥ (N *ᵥ z) = 0
    rw [Matrix.dotProduct_mulVec, hyN, zero_dotProduct]
  have hℓ : Function.Surjective ℓ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    intro c
    refine ⟨Pi.single i (c / y i), ?_⟩
    change y ⬝ᵥ Pi.single i (c / y i) = c
    rw [dotProduct_single]
    exact mul_div_cancel₀ c hi
  have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker ℓ
  rw [LinearMap.range_eq_top.mpr hℓ, finrank_top, Module.finrank_self] at h2
  have heq : LinearMap.range N.mulVecLin = LinearMap.ker ℓ :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hx : x ∈ LinearMap.ker ℓ := hpair
  rw [← heq] at hx
  exact hx

/-- If the eigenspace of $\mu$ is spanned by $\mathbf{x}$ and a left eigenvector $\mathbf{y}$ has
$\mathbf{y}^{\mathsf{T}}\mathbf{x} \ne 0$, the generalized eigenspace of $\mu$ is the
eigenspace. -/
private theorem maxGenEigenspace_eq_eigenspace_of_dotProduct_ne_zero {A : Matrix n n K}
    {x y : n → K} {μ : K} (hyA : y ᵥ* A = μ • y)
    (hspan : Module.End.eigenspace (Matrix.toLin' A) μ ≤ K ∙ x) (hpair : y ⬝ᵥ x ≠ 0) :
    Module.End.maxGenEigenspace (Matrix.toLin' A) μ =
      Module.End.eigenspace (Matrix.toLin' A) μ := by
  have hyN : y ᵥ* (A - μ • (1 : Matrix n n K)) = 0 := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, hyA, sub_self]
  have hstep : ∀ z : n → K, (A - μ • (1 : Matrix n n K)) *ᵥ ((A - μ • (1 : Matrix n n K)) *ᵥ z)
      = 0 → (A - μ • (1 : Matrix n n K)) *ᵥ z = 0 := by
    intro z hz
    have hmem : (A - μ • (1 : Matrix n n K)) *ᵥ z ∈ K ∙ x := by
      refine hspan ?_
      rw [← ker_mulVecLin_sub_smul_one]
      exact hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hp : y ⬝ᵥ ((A - μ • (1 : Matrix n n K)) *ᵥ z) = 0 := by
      rw [Matrix.dotProduct_mulVec, hyN, zero_dotProduct]
    rw [← hc, dotProduct_smul, smul_eq_mul] at hp
    rw [← hc, (mul_eq_zero.mp hp).resolve_right hpair, zero_smul]
  have hpow : ∀ (k : ℕ) (z : n → K), (A - μ • (1 : Matrix n n K)) ^ k *ᵥ z = 0 →
      (A - μ • (1 : Matrix n n K)) *ᵥ z = 0 := by
    intro k
    induction k with
    | zero =>
      intro z hz
      rw [pow_zero, Matrix.one_mulVec] at hz
      rw [hz, Matrix.mulVec_zero]
    | succ k ih =>
      intro z hz
      refine hstep z (ih _ ?_)
      rwa [Matrix.mulVec_mulVec, ← pow_succ]
  refine le_antisymm (fun z hz => ?_) Module.End.eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hz
  have hkM : (A - μ • (1 : Matrix n n K)) ^ k *ᵥ z = 0 := by
    rw [← toLin'_sub_smul_one_pow_apply]
    exact hk
  rw [← ker_mulVecLin_sub_smul_one]
  exact hpow k z hkM

/-- **A geometrically simple eigenvalue is algebraically simple exactly when its left and right
eigenvectors are not orthogonal**: if the eigenspace of $\mu$ has dimension one,
$\mathbf{A}\mathbf{x} = \mu\mathbf{x}$ and $\mathbf{y}^{\mathsf{T}}\mathbf{A} =
\mu\mathbf{y}^{\mathsf{T}}$ with $\mathbf{x}, \mathbf{y} \ne \mathbf{0}$, then $\mu$ is a simple
root of the characteristic polynomial if and only if $\mathbf{y}^{\mathsf{T}}\mathbf{x} \ne 0$.
[HornJohnson2013, Theorem 1.4.12]. -/
theorem rootMultiplicity_charpoly_eq_one_iff_dotProduct_ne_zero
    {A : Matrix n n K} {x y : n → K} {μ : K} (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x)
    (hyA : y ᵥ* A = μ • y)
    (h : Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) = 1) :
    A.charpoly.rootMultiplicity μ = 1 ↔ y ⬝ᵥ x ≠ 0 := by
  have hm := LinearMap.finrank_maxGenEigenspace_eq (Matrix.toLin' A) μ
  rw [Matrix.charpoly_toLin'] at hm
  have hxmem : x ∈ Module.End.eigenspace (Matrix.toLin' A) μ := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hAx]
  refine ⟨fun hmult hpair => ?_, fun hpair => ?_⟩
  · have hyN : y ᵥ* (A - μ • (1 : Matrix n n K)) = 0 := by
      rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, hyA, sub_self]
    obtain ⟨z, hz⟩ := exists_mulVec_eq_of_dotProduct_eq_zero hy hyN
      (by rw [ker_mulVecLin_sub_smul_one, h]) hpair
    have hmax : Module.End.eigenspace (Matrix.toLin' A) μ =
        Module.End.maxGenEigenspace (Matrix.toLin' A) μ :=
      Submodule.eq_of_le_of_finrank_eq Module.End.eigenspace_le_maxGenEigenspace
        (by rw [h, hm, hmult])
    have hzmem : z ∈ Module.End.maxGenEigenspace (Matrix.toLin' A) μ := by
      refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨2, ?_⟩
      rw [toLin'_sub_smul_one_pow_apply, pow_two, ← Matrix.mulVec_mulVec, hz,
        ← Matrix.mulVecLin_apply, ← LinearMap.mem_ker, ker_mulVecLin_sub_smul_one]
      exact hxmem
    rw [← hmax, ← ker_mulVecLin_sub_smul_one, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      hz] at hzmem
    exact hx hzmem
  · have hspan : Module.End.eigenspace (Matrix.toLin' A) μ ≤ K ∙ x :=
      (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem x _).mpr hxmem)
        (by rw [finrank_span_singleton hx, h])).ge
    rw [← hm, maxGenEigenspace_eq_eigenspace_of_dotProduct_ne_zero hyA hspan hpair, h]

/-! ### The adjugate -/

omit [DecidableEq n] in
/-- Transposition preserves the dimension of the kernel of a square matrix. -/
private theorem finrank_ker_mulVecLin_transpose (M : Matrix n n K) :
    Module.finrank K (LinearMap.ker Mᵀ.mulVecLin) =
      Module.finrank K (LinearMap.ker M.mulVecLin) := by
  have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hT := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
  change M.rank + _ = _ at hM
  change Mᵀ.rank + _ = _ at hT
  rw [Matrix.rank_transpose] at hT
  omega

/-- A square matrix whose kernel has dimension one has a nonzero adjugate: its rank normal form
has a nonzero cofactor. -/
private theorem adjugate_ne_zero_of_finrank_ker_eq_one {M : Matrix n n K}
    (h : Module.finrank K (LinearMap.ker M.mulVecLin) = 1) : M.adjugate ≠ 0 := by
  have hr := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + Module.finrank K (LinearMap.ker M.mulVecLin) = Module.finrank K (n → K) at hr
  rw [h, Module.finrank_fintype_fun_eq_card] at hr
  have hnull : Fintype.card n - M.rank = 1 := by omega
  obtain ⟨V, U, e, hV, hU, hM⟩ := Matrix.exists_rank_normal_form M
  obtain ⟨j, hj⟩ : ∃ j : Fin M.rank ⊕ Fin (Fintype.card n - M.rank), ∀ k, k ≠ j → k.isLeft :=
    ⟨Sum.inr ⟨0, by omega⟩, fun k hk => by
      rcases k with k | k
      · rfl
      · exact (hk (congrArg Sum.inr (Fin.ext (by have := k.isLt; simp; omega)))).elim⟩
  have hblock : (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) K) 0 0
      (0 : Matrix (Fin (Fintype.card n - M.rank)) (Fin (Fintype.card n - M.rank)) K)) =
      Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => 0) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  have hdiag : (Matrix.diagonal (Sum.elim (fun _ : Fin M.rank => (1 : K))
      fun _ : Fin (Fintype.card n - M.rank) => (0 : K))).adjugate j j = 1 := by
    rw [Matrix.adjugate_diagonal, Matrix.diagonal_apply_eq]
    refine Finset.prod_eq_one fun k hk => ?_
    have hk' := hj k (Finset.mem_erase.mp hk).1
    rcases k with k | k
    · rfl
    · simp at hk'
  intro hzero
  have hadj : (V * M * U).adjugate = 0 := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hzero, Matrix.zero_mul,
      Matrix.mul_zero]
  rw [hM, hblock, Matrix.adjugate_submatrix_equiv_self] at hadj
  have h0 := congrFun (congrFun hadj (e.symm j)) (e.symm j)
  rw [Matrix.submatrix_apply, Equiv.apply_symm_apply, hdiag, Matrix.zero_apply] at h0
  exact one_ne_zero h0

/-- **The adjugate at a geometrically simple eigenvalue.** If the kernel of $\mathbf{M}$ has
dimension one, $\mathbf{M}\mathbf{x} = \mathbf{0}$ and $\mathbf{y}^{\mathsf{T}}\mathbf{M} =
\mathbf{0}$ with $\mathbf{x}, \mathbf{y} \ne \mathbf{0}$, then
$\operatorname{adj} \mathbf{M} = c\,\mathbf{x}\mathbf{y}^{\mathsf{T}}$ for some $c \ne 0$. With
$\mathbf{M} = \mathbf{A} - \mu\mathbf{I}$, $\mathbf{x}$ is a right and $\mathbf{y}$ a left
eigenvector of $\mathbf{A}$ for $\mu$. [HornJohnson2013, §1.4.11]. -/
theorem exists_adjugate_eq_smul_vecMulVec {M : Matrix n n K} {x y : n → K} (hx : x ≠ 0)
    (hy : y ≠ 0) (hMx : M *ᵥ x = 0) (hyM : y ᵥ* M = 0)
    (h : Module.finrank K (LinearMap.ker M.mulVecLin) = 1) :
    ∃ c : K, c ≠ 0 ∧ M.adjugate = c • Matrix.vecMulVec x y := by
  have hdet : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hMx⟩
  have hspan : K ∙ x = LinearMap.ker M.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem x _).mpr hMx)
      (by rw [finrank_span_singleton hx, h])
  have hyT : y ∈ LinearMap.ker Mᵀ.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, hyM]
  have hspanT : K ∙ y = LinearMap.ker Mᵀ.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem y _).mpr hyT)
      (by rw [finrank_span_singleton hy, finrank_ker_mulVecLin_transpose, h])
  have hMadj : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
  have hadjM : M.adjugate * M = 0 := by rw [Matrix.adjugate_mul, hdet, zero_smul]
  have hcols : ∀ j : n, ∃ c : K, c • x = fun i => M.adjugate i j := by
    intro j
    have hk : (fun i => M.adjugate i j) ∈ LinearMap.ker M.mulVecLin :=
      funext fun i => congrFun (congrFun hMadj i) j
    rw [← hspan] at hk
    exact Submodule.mem_span_singleton.mp hk
  choose c hc using hcols
  have hadj : M.adjugate = Matrix.vecMulVec x c := by
    ext i j
    rw [Matrix.vecMulVec_apply, ← congrFun (hc j) i, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hcM : c ᵥ* M = 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    rw [hadj, Matrix.vecMulVec_mul] at hadjM
    funext j
    have h1 := congrFun (congrFun hadjM i) j
    rw [Matrix.vecMulVec_apply] at h1
    exact (mul_eq_zero.mp h1).resolve_left hi
  have hcT : c ∈ LinearMap.ker Mᵀ.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, hcM]
  rw [← hspanT] at hcT
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hcT
  have hform : M.adjugate = γ • Matrix.vecMulVec x y := by
    rw [hadj, ← hγ, Matrix.vecMulVec_smul]
  refine ⟨γ, fun hzero => adjugate_ne_zero_of_finrank_ker_eq_one h ?_, hform⟩
  rw [hform, hzero, zero_smul]

/-! ### Paired bases and spectral deflation -/

omit [DecidableEq n] in
/-- Left multiplication acts on any scalar multiple of a right eigenvector's outer product by
its eigenvalue: if $\mathbf{A}\mathbf{x}=\mu\mathbf{x}$, then
$\mathbf{A}(c\mathbf{x}\mathbf{y}^{\mathsf{T}})=
\mu(c\mathbf{x}\mathbf{y}^{\mathsf{T}})$ for every scalar $c$ and vector $\mathbf{y}$.
Generalizes the left half of `NLAlib.mul_normalized_vecMulVec_eq_smul` from
`tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`. -/
theorem mul_smul_vecMulVec_eq_smul {A : Matrix n n K} {x y : n → K}
    {μ : K} (hx : A *ᵥ x = μ • x) (c : K) :
    A * (c • Matrix.vecMulVec x y) = μ • (c • Matrix.vecMulVec x y) := by
  rw [Matrix.mul_smul, Matrix.mul_vecMulVec, hx, Matrix.smul_vecMulVec]
  exact smul_comm _ _ _

omit [DecidableEq n] in
/-- Right multiplication acts on any scalar multiple of a left eigenvector's outer product by
its eigenvalue: if $\mathbf{y}^{\mathsf{T}}\mathbf{A}=\mu\mathbf{y}^{\mathsf{T}}$, then
$(c\mathbf{x}\mathbf{y}^{\mathsf{T}})\mathbf{A}=
\mu(c\mathbf{x}\mathbf{y}^{\mathsf{T}})$ for every scalar $c$ and vector $\mathbf{x}$.
Generalizes the right half of `NLAlib.mul_normalized_vecMulVec_eq_smul` from
`tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`. -/
theorem smul_vecMulVec_mul_eq_smul {A : Matrix n n K} {x y : n → K}
    {μ : K} (hy : y ᵥ* A = μ • y) (c : K) :
    (c • Matrix.vecMulVec x y) * A = μ • (c • Matrix.vecMulVec x y) := by
  rw [Matrix.smul_mul, Matrix.vecMulVec_mul, hy, Matrix.vecMulVec_smul]
  exact smul_comm _ _ _


open Module Polynomial in
private theorem inv_smul_vecMulVec_eq_mul_diagonal_mul_inv
    (S : Matrix n n K) (i : n) (x y : n → K)
    (hcol : Matrix.col S i = x) (hrow : ∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) :
    (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y =
      S * Matrix.diagonal (Pi.single i 1) * S⁻¹ := by
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Pi.single_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hrow]
  have hkl : S k i = x k := congrFun hcol k
  rw [hkl]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
  ring

open Module Polynomial in
/-- **Left-right eigenvector deflation.** If $\mathbf{A}\mathbf{x}=\mu\mathbf{x}$ and
$\mathbf{y}^{\mathsf{T}}\mathbf{A}=\mu\mathbf{y}^{\mathsf{T}}$ with
$\mathbf{y}^{\mathsf{T}}\mathbf{x}\ne0$, an invertible $\mathbf{S}$ has a column $\mathbf{x}$
and the corresponding inverse row
$$\frac{\mathbf{y}^{\mathsf{T}}}{\mathbf{y}^{\mathsf{T}}\mathbf{x}}.$$
That coordinate of
$\mathbf{S}^{-1}\mathbf{A}\mathbf{S}$ has diagonal entry $\mu$ and all other row and column
entries zero. The normalized outer product is the conjugate of that coordinate projector.
[HornJohnson2013, Theorem 1.4.7], generalized to arbitrary fields and finite index types, with
bilinear left rows in place of conjugated columns.
Adapted from `NLAlib.exists_isolated_eigenvector_similarity` in `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`.
Result: left-right-eigenvectors -/
theorem exists_inv_mul_mul_apply_eq_of_dotProduct_ne_zero {A : Matrix n n K} {x y : n → K} {μ : K}
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y) (hpair : y ⬝ᵥ x ≠ 0) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y =
        S * Matrix.diagonal (Pi.single i 1) * S⁻¹ := by
  classical
  let ℓ : (n → K) →ₗ[K] K :=
    { toFun z := y ⬝ᵥ z
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' c z := by rw [dotProduct_smul]; rfl }
  obtain ⟨s, b, j, hx, hcoord⟩ := exists_basis_of_pairing_ne_zero (f := ℓ) (v := x) hpair
  let : Fintype s := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card s = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let e : s ≃ n := Fintype.equivOfCardEq hcard
  let c : Basis n K (n → K) := b.reindex e
  let i : n := e j
  let p := Pi.basisFun K n
  let S : Matrix n n K := p.toMatrix c
  let : Invertible S := Basis.invertibleToMatrix p c
  have hS : IsUnit S := isUnit_of_invertible S
  have hci : c i = x := by
    simpa only [c, i, Basis.reindex_apply, Equiv.symm_apply_apply] using hx.symm
  have hcol : Matrix.col S i = x := by
    funext k
    simpa only [S, p, Matrix.col_apply, Basis.toMatrix_apply, Pi.basisFun_repr] using congrFun hci k
  have hℓ : ℓ = (y ⬝ᵥ x) • c.coord i := by
    apply LinearMap.ext
    intro z
    have h := LinearMap.congr_fun hcoord z
    simpa only [LinearMap.smul_apply, ℓ, LinearMap.coe_mk, AddHom.coe_mk,
      Basis.coord_apply, c, i, Basis.repr_reindex_apply, Equiv.symm_apply_apply] using h
  have hSinv : S⁻¹ = c.toMatrix p :=
    Matrix.inv_eq_left_inv (Basis.toMatrix_mul_toMatrix_flip c p)
  have hrow (k : n) : S⁻¹ i k = y k / (y ⬝ᵥ x) := by
    have h := LinearMap.congr_fun hℓ (p k)
    have hval : y k = (y ⬝ᵥ x) * (c.repr (p k) i) := by
      simpa only [ℓ, p, LinearMap.coe_mk, AddHom.coe_mk, Pi.basisFun_apply, dotProduct_single,
        mul_one, LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply] using h
    rw [hSinv, Basis.toMatrix_apply]
    apply (eq_div_iff hpair).mpr
    simpa only [mul_comm] using hval.symm
  have hM : S⁻¹ * A * S = A.toLin'.toMatrix c c := by
    have hstd : A.toLin'.toMatrix p p = A := by
      simpa only [p, Matrix.toLin_eq_toLin'] using LinearMap.toMatrix_toLin p p A
    rw [hSinv]
    nth_rw 1 [← hstd]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c p c p A.toLin'
  have hright (k : n) : (S⁻¹ * A * S) k i = if k = i then μ else 0 := by
    rw [hM, LinearMap.toMatrix_apply, hci, Matrix.toLin'_apply, hAx,
      map_smul, ← hci, c.repr_self]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, eq_comm]
  have hleft (z : n → K) : c.coord i (A *ᵥ z) = μ * c.coord i z := by
    have h : ℓ (A *ᵥ z) = μ * ℓ z := by
      change y ⬝ᵥ (A *ᵥ z) = μ * (y ⬝ᵥ z)
      rw [Matrix.dotProduct_mulVec, hyA, smul_dotProduct]
      rfl
    rw [hℓ, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
    apply mul_left_cancel₀ hpair
    convert h using 1
    ring
  have htop (k : n) : (S⁻¹ * A * S) i k = if k = i then μ else 0 := by
    rw [hM, LinearMap.toMatrix_apply]
    change c.coord i (A *ᵥ c k) = _
    rw [hleft, Basis.coord_apply, c.repr_self]
    simp only [Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  refine ⟨S, i, hS, hcol, hrow, hright, htop, ?_⟩
  exact inv_smul_vecMulVec_eq_mul_diagonal_mul_inv S i x y hcol hrow

open Module Polynomial in
/-- If column $i$ of $\mathbf{M}$ is $\mu\mathbf{e}_i$ and $\mu$ is a simple root of its
characteristic polynomial, the principal submatrix deleting $i$ has no eigenvalue $\mu$.
[HornJohnson2013, Lemma 6.3.10], in isolated coordinates; the row need not be isolated.
Adapted from `NLAlib.not_mem_spectrum_submatrix_of_isolated_coordinate_of_simple` in
`tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`. -/
theorem not_mem_spectrum_submatrix_of_rootMultiplicity_eq_one
    (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hμ : M.charpoly.rootMultiplicity μ = 1) :
    μ ∉ spectrum K
      (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  classical
  let B := M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)
  have hfactor : M.charpoly = (X - C μ) * B.charpoly :=
    charpoly_eq_X_sub_C_mul_charpoly_submatrix hcol
  have hprod : (X - C μ) * B.charpoly ≠ 0 := hfactor ▸ M.charpoly_monic.ne_zero
  rw [hfactor, Polynomial.rootMultiplicity_mul hprod] at hμ
  simp only [Polynomial.rootMultiplicity_X_sub_C] at hμ
  have hB : B.charpoly.rootMultiplicity μ = 0 := Nat.add_eq_left.mp hμ
  intro hspec
  have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hspec
  have hpos := Polynomial.rootMultiplicity_pos'.mpr ⟨B.charpoly_monic.ne_zero, hroot⟩
  rw [hB] at hpos
  exact (Nat.lt_irrefl 0) hpos

open Module Polynomial in
/-- Nonzero right and left eigenvectors $\mathbf{x},\mathbf{y}$ for a simple eigenvalue
$\mu$ admit an invertible paired basis with column $\mathbf{x}$, inverse row
$\mathbf{y}^{\mathsf{T}}/(\mathbf{y}^{\mathsf{T}}\mathbf{x})$, and isolated coordinate
$\mu$. The complementary principal block does not have $\mu$ in its spectrum.
[HornJohnson2013, Lemma 6.3.10], over an arbitrary field, without algebraic closure.
Adapted from `NLAlib.exists_simple_eigenvalue_isolated_similarity` in `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`. -/
theorem exists_inv_mul_mul_apply_eq_of_rootMultiplicity_eq_one
    {A : Matrix n n K} {x y : n → K} {μ : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      μ ∉ spectrum K ((S⁻¹ * A * S).submatrix
        (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  have hxmem : x ∈ Module.End.eigenspace A.toLin' μ :=
    Module.End.mem_eigenspace_iff.mpr hAx
  have hdim : Module.finrank K (Module.End.eigenspace A.toLin' μ) = 1 := by
    apply Nat.le_antisymm
    · have hle := Submodule.finrank_mono
        (Module.End.eigenspace_le_maxGenEigenspace (f := A.toLin') (μ := μ))
      rwa [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin', hμ] at hle
    · have hle := Submodule.finrank_mono
        ((Submodule.span_singleton_le_iff_mem x _).mpr hxmem)
      rwa [finrank_span_singleton hx] at hle
  have hpair := (rootMultiplicity_charpoly_eq_one_iff_dotProduct_ne_zero
    hx hy hAx hyA hdim).mp hμ
  obtain ⟨S, i, hS, hcol, hrow, hright, hleft, hproj⟩ :=
    exists_inv_mul_mul_apply_eq_of_dotProduct_ne_zero hAx hyA hpair
  have hchar : (S⁻¹ * A * S).charpoly = A.charpoly :=
    charpoly_mul_mul_of_mul_eq_one
      (Matrix.nonsing_inv_mul S (S.isUnit_iff_isUnit_det.mp hS)) A
  exact ⟨S, i, hS, hcol, hrow, hright, hleft,
    not_mem_spectrum_submatrix_of_rootMultiplicity_eq_one (S⁻¹ * A * S) i μ
      hright (by simpa only [hchar] using hμ)⟩

/-- An isolated column of $\mathbf{S}^{-1}\mathbf{A}\mathbf{S}$ with value $\mu$ makes the
corresponding column of the invertible $\mathbf{S}$ a right eigenvector of $\mathbf{A}$.
Only the transformed column, not its row, is prescribed.
[HornJohnson2013, Theorem 1.4.7], the right-eigenvector part of the converse.
Adapted from `NLAlib.eigenpair_of_isolated_similarity` in `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`. -/
theorem mulVec_col_eq_smul_of_inv_mul_mul_apply_eq
    (A S : Matrix n n K) (i : n) (μ : K) (hS : IsUnit S)
    (hcol : ∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) :
    A *ᵥ Matrix.col S i = μ • Matrix.col S i := by
  let := hS.nonempty_invertible.some
  have hAS : A * S = S * (S⁻¹ * A * S) := by
    simp only [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  funext j
  change (A * S) j i = μ * S j i
  rw [hAS, Matrix.mul_apply]
  simp only [hcol, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_comm _ _

/-- An isolated row of $\mathbf{S}^{-1}\mathbf{A}\mathbf{S}$ with value $\mu$ makes the
corresponding row of the inverse of $\mathbf{S}$ a left eigenvector of $\mathbf{A}$.
Only the transformed row, not its column, is prescribed.
[HornJohnson2013, Theorem 1.4.7], the left-eigenvector part of the converse.
Adapted from `NLAlib.eigenpair_of_isolated_similarity` in `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`. -/
theorem vecMul_eq_smul_of_inv_mul_mul_apply_eq
    (A S : Matrix n n K) (i : n) (μ : K) (hS : IsUnit S)
    (hrow : ∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) :
    (fun j => S⁻¹ i j) ᵥ* A = μ • (fun j => S⁻¹ i j) := by
  let := hS.nonempty_invertible.some
  have hSA : S⁻¹ * A = (S⁻¹ * A * S) * S⁻¹ := by
    simp only [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
  funext j
  change (S⁻¹ * A) i j = μ * S⁻¹ i j
  rw [hSA, Matrix.mul_apply]
  simp only [hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

open Module Polynomial in
/-- If column $i$ of $\mathbf{S}$ is $\mathbf{x}$ and row $i$ of its inverse is
$\mathbf{y}^{\mathsf{T}}/(\mathbf{y}^{\mathsf{T}}\mathbf{x})$, then the diagonal entry of a
perturbation in that basis is
$$(\mathbf{S}^{-1}\mathbf{E}\mathbf{S})_{i,i}=
\frac{\mathbf{y}^{\mathsf{T}}\mathbf{E}\mathbf{x}}
{\mathbf{y}^{\mathsf{T}}\mathbf{x}}\,.$$
This is the coefficient used in first-order eigenvalue perturbation.
Adapted from `NLAlib.nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div` in
`tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`. -/
theorem nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div
    (S E : Matrix n n K) (i : n) (x y : n → K)
    (hcol : Matrix.col S i = x) (hrow : ∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) :
    (S⁻¹ * E * S) i i = (y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x) := by
  rw [Matrix.mul_assoc]
  change (fun j => S⁻¹ i j) ⬝ᵥ (E *ᵥ Matrix.col S i) = _
  rw [hcol]
  have hrowfun : (fun j => S⁻¹ i j) = (y ⬝ᵥ x)⁻¹ • y := by
    funext j
    simp only [hrow, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hrowfun, smul_dotProduct, smul_eq_mul, div_eq_mul_inv, mul_comm]

end NLAlib
