/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Normal
public import NLAlib.Matrix.Factorizations.QR

/-!
# Simultaneous triangularisation and diagonalisation

A commuting family of complex matrices has a common eigenvector and is simultaneously unitarily
triangularisable; over a general `RCLike` field the same holds when the characteristic
polynomials split. A family of normal matrices commutes exactly when it is simultaneously
unitarily diagonalisable; for Hermitian matrices over $\Bbbk$ the diagonals are real, and over
$\mathbb{R}$ the unitary matrix is orthogonal. The families are indexed by an arbitrary type.

## Main results

* `NLAlib.exists_mulVec_eq_smul_of_pairwise_commute`: a common eigenvector.
* `NLAlib.exists_forall_isUpperTriangular_inv_mul_mul_iff`: simultaneous triangularisation
  by an arbitrary invertible basis is equivalent to triangularisation by an orthonormal basis.
* `NLAlib.exists_hasOrthonormalCols_forall_isUpperTriangular_of_forall_splits`: simultaneous
  unitary triangularisation over $\Bbbk$ when the characteristic polynomials split.
* `NLAlib.exists_hasOrthonormalCols_forall_isUpperTriangular_of_pairwise_commute`: over
  $\mathbb{C}$.
* `NLAlib.pairwise_commute_iff_exists_forall_eq_mul_diagonal_mul_conjTranspose`: normal families.
* `NLAlib.exists_hasOrthonormalCols_forall_eq_mul_diagonal_of_pairwise_commute`: Hermitian
  families over $\Bbbk$.

## Implementation notes

The triangular form comes from an induction over the size: a common eigenvector, found in a
minimal invariant subspace, is completed to a unitary matrix, and the complementary blocks are
triangularised by the induction hypothesis. The block lemmas are those of
`NLAlib.Matrix.Spectral.EigenvalueListing`, used there for a pair and a general similarity.
-/

@[expose] public section

open scoped Matrix ComplexOrder
open Polynomial

universe u

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {K : Type*} [Field K] {ι n : Type*} [Fintype n] [DecidableEq n]

/-! ### Common eigenvectors -/

/-- A matrix whose characteristic polynomial splits has an eigenvector in every nonzero invariant
subspace. -/
private theorem exists_mem_mulVec_eq_smul {A : Matrix n n K} (hA : A.charpoly.Splits)
    {W : Submodule K (n → K)} (hW : ∀ x ∈ W, A *ᵥ x ∈ W) (hne : W ≠ ⊥) :
    ∃ x ∈ W, x ≠ 0 ∧ ∃ μ : K, A *ᵥ x = μ • x := by
  have key : ∀ l : List K, ∀ x ∈ W, x ≠ 0 →
      (l.map fun c => A - c • (1 : Matrix n n K)).prod *ᵥ x = 0 →
      ∃ y ∈ W, y ≠ 0 ∧ ∃ μ : K, A *ᵥ y = μ • y := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      intro x _ hx h
      rw [List.map_nil, List.prod_nil, Matrix.one_mulVec] at h
      exact (hx h).elim
    | append_singleton l c ih =>
      intro x hxW hx h
      rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
        ← Matrix.mulVec_mulVec] at h
      by_cases hz : (A - c • (1 : Matrix n n K)) *ᵥ x = 0
      · refine ⟨x, hxW, hx, c, ?_⟩
        rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
      · refine ih _ ?_ hz h
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.sub_mem (hW x hxW) (W.smul_mem c hxW)
  obtain ⟨x, hxW, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine key A.charpoly.roots.toList x hxW hx ?_
  have h := Matrix.aeval_self_charpoly A
  rw [hA.eq_prod_roots_of_monic A.charpoly_monic, ← Multiset.prod_map_toList, map_list_prod,
    List.map_map] at h
  have hfun : (⇑(Polynomial.aeval A) ∘ fun c : K => X - C c) =
      fun c => A - c • (1 : Matrix n n K) := by
    funext c
    simp [Algebra.algebraMap_eq_smul_one]
  rw [← hfun, h, Matrix.zero_mulVec]

/-- A commuting family of matrices whose characteristic polynomials split has a common
eigenvector in every nonzero subspace invariant under the family, by induction on the dimension
of the subspace. -/
private theorem exists_mem_forall_mulVec_eq_smul (A : ι → Matrix n n K)
    (h : Pairwise fun i j => Commute (A i) (A j)) (hA : ∀ i, (A i).charpoly.Splits) (d : ℕ) :
    ∀ W : Submodule K (n → K), Module.finrank K W = d → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, A i *ᵥ x ∈ W) → ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ μ : K, A i *ᵥ x = μ • x := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro W hd hne hW
    by_cases hscalar : ∀ i, ∃ μ : K, ∀ x ∈ W, A i *ᵥ x = μ • x
    · obtain ⟨x, hxW, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact ⟨x, hxW, hx, fun i => (hscalar i).imp fun μ hμ => hμ x hxW⟩
    · push Not at hscalar
      obtain ⟨i, hi⟩ := hscalar
      obtain ⟨y, hyW, hy, μ, hμ⟩ := exists_mem_mulVec_eq_smul (hA i) (hW i) hne
      obtain ⟨z, hzW, hz⟩ := hi μ
      have hmem : ∀ x, x ∈ W ⊓ LinearMap.ker (A i - μ • (1 : Matrix n n K)).mulVecLin ↔
          x ∈ W ∧ A i *ᵥ x = μ • x := by
        intro x
        simp only [Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
          Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
      have hlt : W ⊓ LinearMap.ker (A i - μ • (1 : Matrix n n K)).mulVecLin < W :=
        lt_of_le_of_ne inf_le_left fun heq => hz ((hmem z).mp (heq.ge hzW)).2
      have hne' : W ⊓ LinearMap.ker (A i - μ • (1 : Matrix n n K)).mulVecLin ≠ ⊥ := fun h0 =>
        hy ((Submodule.eq_bot_iff _).mp h0 y ((hmem y).mpr ⟨hyW, hμ⟩))
      have hW' : ∀ j, ∀ x ∈ W ⊓ LinearMap.ker (A i - μ • (1 : Matrix n n K)).mulVecLin,
          A j *ᵥ x ∈ W ⊓ LinearMap.ker (A i - μ • (1 : Matrix n n K)).mulVecLin := by
        intro j x hx
        rw [hmem] at hx ⊢
        refine ⟨hW j x hx.1, ?_⟩
        have hc : A i * A j = A j * A i := by
          rcases eq_or_ne i j with rfl | hij
          · rfl
          · exact (h hij).eq
        rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hx.2, Matrix.mulVec_smul]
      obtain ⟨x, hx, hx0, hxe⟩ :=
        ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne' hW'
      exact ⟨x, ((hmem x).mp hx).1, hx0, hxe⟩

omit [DecidableEq n] in
/-- **A commuting family of complex matrices has a common eigenvector**: for a nonempty index
type there is $\mathbf{x} \ne \mathbf{0}$ with $\mathbf{A}_i\mathbf{x} = d_i\mathbf{x}$ for every
member $\mathbf{A}_i$ of the family.
[HornJohnson2013, Lemma 1.3.19]. -/
theorem exists_mulVec_eq_smul_of_pairwise_commute [Nonempty n] (A : ι → Matrix n n ℂ)
    (h : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ (x : n → ℂ) (d : ι → ℂ), x ≠ 0 ∧ ∀ i, A i *ᵥ x = d i • x := by
  classical
  obtain ⟨x, -, hx, hxe⟩ := exists_mem_forall_mulVec_eq_smul A h (fun i => IsAlgClosed.splits _)
    _ ⊤ rfl top_ne_bot fun _ _ _ => Submodule.mem_top
  choose d hd using hxe
  exact ⟨x, d, hx, hd⟩

/-! ### Simultaneous triangularisation -/

/-- A nonzero vector is, up to a scalar, a prescribed column of a unitary matrix. -/
private theorem exists_hasOrthonormalCols_col_eq_smul {x : n → 𝕜} (hx : x ≠ 0) (i₀ : n) :
    ∃ (W : Matrix n n 𝕜) (c : 𝕜), HasOrthonormalCols W ∧ (fun i => W i i₀) = c • x := by
  have hpos : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr fun h => hx (by simpa using h)
  have hQ : HasOrthonormalCols (Matrix.of fun (i : n) (_ : {i // i = i₀}) =>
      (((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x) i) := by
    ext a b
    have h1 : ((Matrix.of fun (i : n) (_ : {i // i = i₀}) =>
        (((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x) i)ᴴ * Matrix.of fun (i : n) (_ : {i // i = i₀}) =>
        (((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x) i) a b =
        star (((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x) ⬝ᵥ (((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x) :=
      rfl
    rw [h1, Subsingleton.elim a b, Matrix.one_apply_eq, star_smul, smul_dotProduct,
      dotProduct_smul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, RCLike.star_def,
      RCLike.conj_ofReal, smul_eq_mul, smul_eq_mul]
    norm_cast
    field_simp
  obtain ⟨Q', hQ'⟩ := hQ.exists_fromCols (p := {i // ¬i = i₀})
    (Fintype.card_sum.symm.trans (Fintype.card_congr (Equiv.sumCompl (· = i₀))))
  refine ⟨(Matrix.fromCols _ Q').submatrix id (Equiv.sumCompl (· = i₀)).symm,
    ((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜), hQ'.submatrix (Equiv.refl n) (Equiv.injective _),
    funext fun i => ?_⟩
  rw [Matrix.submatrix_apply, Equiv.sumCompl_symm_apply_of_pos (p := (· = i₀)) rfl]
  rfl

/-- Conjugating by a unitary matrix one of whose columns is an eigenvector puts a multiple of a
coordinate vector in that column: if the column $i_0$ of $\mathbf{W}$ is an eigenvector of
$\mathbf{A}$ for $\alpha$, the column $i_0$ of $\mathbf{W}^{\mathsf{H}}\mathbf{A}\mathbf{W}$ is
$\alpha$ times the coordinate vector $\mathbf{e}_{i_0}$. -/
private theorem conjTranspose_mul_mul_apply_of_mulVec_eq_smul {A W : Matrix n n 𝕜}
    (hW : HasOrthonormalCols W) {i₀ : n} {α : 𝕜}
    (hA : (A *ᵥ fun i => W i i₀) = α • fun i => W i i₀) (i : n) :
    (Wᴴ * A * W) i i₀ = if i = i₀ then α else 0 := by
  have h1 : (Wᴴ * A * W) i i₀ = (Wᴴ *ᵥ (A *ᵥ fun k => W k i₀)) i := by
    rw [Matrix.mulVec_mulVec]
    rfl
  have h2 : (Wᴴ *ᵥ fun k => W k i₀) = fun k => (1 : Matrix n n 𝕜) k i₀ := by
    rw [← hW.conjTranspose_mul_self]
    rfl
  rw [h1, hA, Matrix.mulVec_smul, h2, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

/-- Simultaneous unitary triangularisation of a commuting family whose characteristic polynomials
split, by induction on the size: a common eigenvector is completed to a unitary matrix, and the
complementary blocks are triangularised by the induction hypothesis. -/
private theorem exists_triangular_family_aux (k : ℕ) :
    ∀ (n : Type u) [Fintype n] [DecidableEq n] [LinearOrder n], Fintype.card n = k →
      ∀ A : ι → Matrix n n 𝕜, (Pairwise fun i j => Commute (A i) (A j)) →
        (∀ i, (A i).charpoly.Splits) →
        ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ ∀ i, (Uᴴ * A i * U).IsUpperTriangular := by
  induction k with
  | zero =>
    intro n _ _ _ hn A _ _
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    exact ⟨1, Subsingleton.elim _ _, fun i a => isEmptyElim a⟩
  | succ k ih =>
    intro n _ _ _ hn A hcomm hsplit
    have : Nonempty n := Fintype.card_pos_iff.mp (hn ▸ k.succ_pos)
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min (id : n → n)
    obtain ⟨x, -, hx, hxe⟩ := exists_mem_forall_mulVec_eq_smul A hcomm hsplit
      _ ⊤ rfl top_ne_bot fun _ _ _ => Submodule.mem_top
    choose d hd using hxe
    obtain ⟨W, c, hW, hWx⟩ := exists_hasOrthonormalCols_col_eq_smul hx i₀
    have hcol : ∀ i j, (Wᴴ * A i * W) j i₀ = if j = i₀ then d i else 0 := fun i =>
      conjTranspose_mul_mul_apply_of_mulVec_eq_smul hW
        (by rw [hWx, Matrix.mulVec_smul, hd, smul_comm])
    have hM := fun i => submatrix_sumCompl_eq_fromBlocks (hcol i)
    have hcard : Fintype.card {i // ¬i = i₀} = k := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hn, Nat.add_sub_cancel]
    have hsplit' : ∀ i, ((Wᴴ * A i * W).submatrix
        (Subtype.val : {i // ¬i = i₀} → n) Subtype.val).charpoly.Splits := by
      intro i
      have h : (Wᴴ * A i * W).charpoly = (A i).charpoly := by
        rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hW.mul_conjTranspose_self,
          Matrix.one_mul]
      have h2 := Matrix.charpoly_reindex (Equiv.sumCompl (· = i₀)).symm (Wᴴ * A i * W)
      rw [Matrix.reindex_apply, Equiv.symm_symm, hM, Matrix.charpoly_fromBlocks_zero₂₁, h] at h2
      exact (hsplit i).of_dvd (Matrix.charpoly_monic _).ne_zero (h2 ▸ dvd_mul_left _ _)
    have hcomm' : Pairwise fun a b => Commute
        ((Wᴴ * A a * W).submatrix Subtype.val Subtype.val :
          Matrix {i // ¬i = i₀} {i // ¬i = i₀} 𝕜)
        ((Wᴴ * A b * W).submatrix Subtype.val Subtype.val) := by
      intro i j hij
      have h : (Wᴴ * A i * W) * (Wᴴ * A j * W) = (Wᴴ * A j * W) * (Wᴴ * A i * W) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc W Wᴴ, ← Matrix.mul_assoc W Wᴴ, hW.mul_conjTranspose_self,
          Matrix.one_mul, Matrix.one_mul, ← Matrix.mul_assoc (A i), (hcomm hij).eq,
          Matrix.mul_assoc]
      have h' : (Wᴴ * A i * W).submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) *
            (Wᴴ * A j * W).submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) =
          (Wᴴ * A j * W).submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) *
            (Wᴴ * A i * W).submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) := by
        rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]
      rw [hM, hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_inj] at h'
      have h2 := h'.2.2.2
      rw [Matrix.zero_mul, zero_add, Matrix.zero_mul, zero_add] at h2
      exact h2
    obtain ⟨U₁, hU₁, hT⟩ := ih {i // ¬i = i₀} hcard _ hcomm' hsplit'
    have hF : ((Matrix.fromBlocks (1 : Matrix {i // i = i₀} {i // i = i₀} 𝕜) 0 0 U₁).submatrix
        (Equiv.sumCompl (· = i₀)).symm (Equiv.sumCompl (· = i₀)).symm)ᴴ =
        (Matrix.fromBlocks (1 : Matrix {i // i = i₀} {i // i = i₀} 𝕜) 0 0 U₁ᴴ).submatrix
          (Equiv.sumCompl (· = i₀)).symm (Equiv.sumCompl (· = i₀)).symm := by
      rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
      simp
    refine ⟨W * (Matrix.fromBlocks (1 : Matrix {i // i = i₀} {i // i = i₀} 𝕜) 0 0 U₁).submatrix
        (Equiv.sumCompl (· = i₀)).symm (Equiv.sumCompl (· = i₀)).symm, hW.mul ?_, fun i => ?_⟩
    · rw [hasOrthonormalCols_iff, hF, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
      simp [hU₁.conjTranspose_mul_self, Matrix.fromBlocks_one]
    · rw [Matrix.conjTranspose_mul, hF, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc (A i), ← Matrix.mul_assoc Wᴴ, ← Matrix.mul_assoc Wᴴ,
        ← Matrix.mul_assoc _ (Wᴴ * A i * W),
        fromBlocks_one_submatrix_mul_mul_fromBlocks_one _ (hM i)]
      exact isUpperTriangular_fromBlocks_submatrix_sumCompl_symm hi₀ _ _ (hT i)

/-- **Simultaneous triangularization by a similarity is equivalent to unitary
triangularization.** For an arbitrary family $\mathbf{A}_i$ over the real or complex field
$\Bbbk$, indexed by any type,
there is an invertible $\mathbf{V}$ with every $\mathbf{V}^{-1}\mathbf{A}_i\mathbf{V}$ upper
triangular if and only if there is a unitary $\mathbf{U}$ with every
$\mathbf{U}^{\mathsf{H}}\mathbf{A}_i\mathbf{U}$ upper triangular. The matrix labels form a
finite linearly ordered type, which may be empty; the family may be infinite and need not
commute. Over $\mathbb{R}$ the unitary matrix is orthogonal.
No printed source. Generalized from `tchen-research/NLAlib`, commit
`77514ce42a0e437d837797a063ac161f41022730`,
`exists_simultaneous_triangular_similarity_iff_unitary`, using the existing QR factorization.
Result: simultaneous-triangularization -/
theorem exists_forall_isUpperTriangular_inv_mul_mul_iff [LinearOrder n]
    (A : ι → Matrix n n 𝕜) :
    (∃ V : Matrix n n 𝕜, IsUnit V ∧
      ∀ i, (V⁻¹ * A i * V).IsUpperTriangular) ↔
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧
      ∀ i, (Uᴴ * A i * U).IsUpperTriangular := by
  constructor
  · rintro ⟨V, hV, htri⟩
    obtain ⟨Q, R, hQR, -⟩ := exists_isQR V le_rfl
    have hR : IsUnit R := by
      apply (Matrix.isUnit_iff_isUnit_det R).mpr
      have hv := (Matrix.isUnit_iff_isUnit_det V).mp hV
      rw [hQR.eq_mul, Matrix.det_mul] at hv
      exact isUnit_of_mul_isUnit_right hv
    have hVdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
    have hRinv : R * V⁻¹ = Qᴴ := by
      rw [← hQR.conjTranspose_mul_eq, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv V hVdet, Matrix.mul_one]
    refine ⟨Q, hQR.hasOrthonormalCols, fun i => ?_⟩
    have heq : Qᴴ * A i * Q = R * (V⁻¹ * A i * V) * R⁻¹ := by
      rw [← hRinv, ← hQR.mul_inv_eq hR]
      simp only [Matrix.mul_assoc]
    rw [heq]
    exact (hQR.isUpperTriangular.mul (htri i)).mul hQR.isUpperTriangular.inv
  · rintro ⟨U, hU, htri⟩
    have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU.conjTranspose_mul_self
    exact ⟨U, hU.isUnit, by simpa only [hinv] using htri⟩

/-- **A commuting family of matrices whose characteristic polynomials split is simultaneously
unitarily triangularisable**: there is a unitary $\mathbf{U}$ with
$\mathbf{U}^{\mathsf{H}}\mathbf{A}_i\mathbf{U}$ upper triangular for every $i$. Over $\mathbb{R}$
this is simultaneous orthogonal triangularisation of commuting matrices with real eigenvalues;
the family may be infinite.
[HornJohnson2013, Theorem 2.3.3], there over $\mathbb{C}$. -/
theorem exists_hasOrthonormalCols_forall_isUpperTriangular_of_forall_splits [LinearOrder n]
    (A : ι → Matrix n n 𝕜) (h : Pairwise fun i j => Commute (A i) (A j))
    (hA : ∀ i, (A i).charpoly.Splits) :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ ∀ i, (Uᴴ * A i * U).IsUpperTriangular :=
  exists_triangular_family_aux _ n rfl A h hA

/-- **A commuting family of complex matrices is simultaneously unitarily triangularisable**:
there is a unitary $\mathbf{U}$ with $\mathbf{U}^{\mathsf{H}}\mathbf{A}_i\mathbf{U}$ upper
triangular for every $i$.
[HornJohnson2013, Theorem 2.3.3].
Result: simultaneous-triangularization -/
theorem exists_hasOrthonormalCols_forall_isUpperTriangular_of_pairwise_commute [LinearOrder n]
    (A : ι → Matrix n n ℂ) (h : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧ ∀ i, (Uᴴ * A i * U).IsUpperTriangular :=
  exists_hasOrthonormalCols_forall_isUpperTriangular_of_forall_splits A h
    fun _ => IsAlgClosed.splits _

/-! ### Simultaneous diagonalisation -/

/-- Unitarily diagonalised matrices with the same unitary factor commute. -/
private theorem commute_mul_diagonal_mul_conjTranspose {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) (a b : n → 𝕜) :
    Commute (U * Matrix.diagonal a * Uᴴ) (U * Matrix.diagonal b * Uᴴ) := by
  rw [Commute, SemiconjBy]
  simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
  rw [← Matrix.mul_assoc (Matrix.diagonal a), ← Matrix.mul_assoc (Matrix.diagonal b),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  simp only [mul_comm]

/-- **A family of normal matrices commutes exactly when it is simultaneously unitarily
diagonalisable**: the complex normal $\mathbf{A}_i$ commute pairwise if and only if there is a
unitary $\mathbf{U}$ with
$\mathbf{A}_i = \mathbf{U} \operatorname{diag}(\mathbf{d}_i) \mathbf{U}^{\mathsf{H}}$ for every
$i$. [HornJohnson2013, Theorem 2.5.5].
Result: simultaneous-diagonalization -/
theorem pairwise_commute_iff_exists_forall_eq_mul_diagonal_mul_conjTranspose
    {A : ι → Matrix n n ℂ} (hA : ∀ i, IsStarNormal (A i)) :
    (Pairwise fun i j => Commute (A i) (A j)) ↔
      ∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧
        ∀ i, ∃ d : n → ℂ, A i = U * Matrix.diagonal d * Uᴴ := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
    obtain ⟨U, hU, hT⟩ :=
      exists_hasOrthonormalCols_forall_isUpperTriangular_of_pairwise_commute A h
    exact ⟨U, hU, fun i =>
      ⟨_, (hA i).eq_mul_diagonal_mul_conjTranspose_of_isUpperTriangular hU (hT i)⟩⟩
  · rintro ⟨U, hU, hd⟩ i j -
    obtain ⟨a, ha⟩ := hd i
    obtain ⟨b, hb⟩ := hd j
    rw [ha, hb]
    exact commute_mul_diagonal_mul_conjTranspose hU a b

/-- **A commuting family of Hermitian matrices is simultaneously unitarily diagonalisable**,
with real diagonals: there is a unitary $\mathbf{U}$ with
$\mathbf{A}_i = \mathbf{U} \operatorname{diag}(\mathbf{d}_i) \mathbf{U}^{\mathsf{H}}$,
$\mathbf{d}_i$ real, for every $i$; over $\mathbb{R}$ the unitary matrix is orthogonal.
[HornJohnson2013, Theorem 4.1.6 context].
Result: simultaneous-diagonalization -/
theorem exists_hasOrthonormalCols_forall_eq_mul_diagonal_of_pairwise_commute
    {A : ι → Matrix n n 𝕜} (hA : ∀ i, (A i).IsHermitian)
    (h : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧
      ∀ i, ∃ d : n → ℝ, A i = U * Matrix.diagonal (fun j => ((d j : ℝ) : 𝕜)) * Uᴴ := by
  classical
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨U, hU, hT⟩ := exists_hasOrthonormalCols_forall_isUpperTriangular_of_forall_splits A h
    fun i => (hA i).splits_charpoly
  refine ⟨U, hU, fun i => ⟨fun j => RCLike.re ((Uᴴ * A i * U) j j), ?_⟩⟩
  have hH : (Uᴴ * A i * U).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul U (hA i)
  have hN : IsStarNormal (A i) := (hA i).isSelfAdjoint.isStarNormal
  have h1 := hN.eq_mul_diagonal_mul_conjTranspose_of_isUpperTriangular hU (hT i)
  simpa only [hH.coe_re_apply_self] using h1

/-- Two Hermitian matrices commute exactly when they are simultaneously unitarily
diagonalisable: $\mathbf{A} = \mathbf{U} \operatorname{diag}(\mathbf{a}) \mathbf{U}^{\mathsf{H}}$
and $\mathbf{B} = \mathbf{U} \operatorname{diag}(\mathbf{b}) \mathbf{U}^{\mathsf{H}}$ with
$\mathbf{U}$ unitary and $\mathbf{a}$, $\mathbf{b}$ real. -/
theorem _root_.Matrix.IsHermitian.commute_iff_exists_eq_mul_diagonal_mul_conjTranspose
    {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Commute A B ↔
      ∃ (U : Matrix n n 𝕜) (a b : n → ℝ), HasOrthonormalCols U ∧
        A = U * Matrix.diagonal (fun j => ((a j : ℝ) : 𝕜)) * Uᴴ ∧
        B = U * Matrix.diagonal (fun j => ((b j : ℝ) : 𝕜)) * Uᴴ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨U, hU, hd⟩ := exists_hasOrthonormalCols_forall_eq_mul_diagonal_of_pairwise_commute
      (A := fun c : Bool => cond c A B) (fun c => by cases c <;> assumption)
      (fun c c' hcc' => by
        cases c <;> cases c' <;> first | exact absurd rfl hcc' | exact h | exact h.symm)
    obtain ⟨a, ha⟩ := hd true
    obtain ⟨b, hb⟩ := hd false
    exact ⟨U, a, b, hU, ha, hb⟩
  · rintro ⟨U, a, b, hU, rfl, rfl⟩
    exact commute_mul_diagonal_mul_conjTranspose hU _ _

end NLAlib
