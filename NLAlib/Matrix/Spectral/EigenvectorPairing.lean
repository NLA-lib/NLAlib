/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Left and right eigenvectors

A right eigenvector of a square matrix over a field is a vector `x` with `A *ᵥ x = μ • x`, a left
eigenvector a vector `y` with `y ᵥ* A = μ • y`. Left and right eigenvectors for different
eigenvalues are orthogonal for the pairing `y ⬝ᵥ x`; for an eigenvalue whose eigenspace is a
line, the pairing of its left and right eigenvectors decides whether the eigenvalue is a simple
root of the characteristic polynomial, and the adjugate of `A - μ • 1` is a nonzero multiple of
`x yᵀ`.

## Main results

* `NLAlib.exists_mulVec_eq_smul_of_mem_spectrum`, `NLAlib.exists_vecMul_eq_smul_of_mem_spectrum`:
  eigenvalues have right and left eigenvectors.
* `NLAlib.dotProduct_eq_zero_of_vecMul_eq_smul_of_mulVec_eq_smul`: biorthogonality.
* `NLAlib.rootMultiplicity_charpoly_eq_one_iff_dotProduct_ne_zero`: simple eigenvalues through
  the pairing.
* `NLAlib.exists_adjugate_eq_smul_vecMulVec`: the adjugate at a geometrically simple eigenvalue.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Existence and biorthogonality -/

/-- Every eigenvalue has a right eigenvector.
Port of `NLAlib.exists_mulVec_eq_smul_of_mem_spectrum`. -/
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

/-- Every eigenvalue has a left eigenvector.
Port of `NLAlib.exists_vecMul_eq_smul_of_mem_spectrum`. -/
theorem exists_vecMul_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ y : n → K, y ≠ 0 ∧ y ᵥ* A = μ • y := by
  have hT : μ ∈ spectrum K Aᵀ := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose,
      ← Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact hμ
  obtain ⟨y, hy, h⟩ := exists_mulVec_eq_smul_of_mem_spectrum hT
  exact ⟨y, hy, by rwa [Matrix.mulVec_transpose] at h⟩

omit [DecidableEq n] in
/-- **Biorthogonality**: left and right eigenvectors for different eigenvalues are orthogonal.
[HornJohnson2013, Theorem 1.4.7].
Port of `NLAlib.dotProduct_eq_zero_of_left_right_eigenvalues_ne`. -/
theorem dotProduct_eq_zero_of_vecMul_eq_smul_of_mulVec_eq_smul {A : Matrix n n K} {x y : n → K}
    {α μ : K} (hx : A *ᵥ x = α • x) (hy : y ᵥ* A = μ • y) (h : α ≠ μ) : y ⬝ᵥ x = 0 := by
  have h1 : α * (y ⬝ᵥ x) = μ * (y ⬝ᵥ x) := by
    rw [← smul_eq_mul, ← dotProduct_smul, ← hx, Matrix.dotProduct_mulVec, hy, smul_dotProduct,
      smul_eq_mul]
  exact (mul_eq_mul_right_iff.mp h1).resolve_left h

/-! ### Simple eigenvalues -/

/-- The kernel of `A - μ • 1` is the eigenspace of `μ`. -/
private theorem ker_mulVecLin_sub_smul_one (A : Matrix n n K) (μ : K) :
    LinearMap.ker (A - μ • (1 : Matrix n n K)).mulVecLin =
      Module.End.eigenspace (Matrix.toLin' A) μ := by
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Module.End.mem_eigenspace_iff,
    Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

/-- Powers of `A - μ • 1` as a linear map and as a matrix. -/
private theorem toLin'_sub_smul_one_pow_apply (A : Matrix n n K) (μ : K) (k : ℕ) (z : n → K) :
    ((Matrix.toLin' A - μ • 1) ^ k) z = (A - μ • (1 : Matrix n n K)) ^ k *ᵥ z := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_pow, map_sub, map_smul, Matrix.toLin'_one]
  rfl

omit [DecidableEq n] in
/-- A matrix with a kernel of dimension one has in its range every vector orthogonal to a
nonzero left null vector. -/
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

/-- If the eigenspace of `μ` is spanned by `x` and a left eigenvector `y` has `y ⬝ᵥ x ≠ 0`, the
generalized eigenspace of `μ` is the eigenspace. -/
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
eigenvectors are not orthogonal.** [HornJohnson2013, Theorem 1.4.12].
Port of `NLAlib.rootMultiplicity_eq_one_iff_pairing_ne_zero_of_finrank_eigenspace_eq_one`. -/
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

/-- **The adjugate at a geometrically simple eigenvalue** is a nonzero multiple of `x yᵀ`, with
`x` a right and `y` a left eigenvector. [HornJohnson2013, §1.4.11].
Port of `NLAlib.exists_adjugate_shift_eq_smul_vecMulVec_of_finrank_eigenspace_eq_one`. -/
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

end NLAlib
