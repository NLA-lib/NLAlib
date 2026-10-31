/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import NLAlib.Matrix.Factorizations.Triangular
public import NLAlib.Matrix.Functions.Complexification

/-!
# Listings of the eigenvalues of a matrix

The eigenvalues of a matrix that need not be Hermitian are given by a listing:
`NLAlib.IsEigenvalueListing A d` says that the family $\mathbf{d}$, indexed by any finite type,
lists the roots of the characteristic polynomial of $\mathbf{A}$ with multiplicity. Over
$\mathbb{C}$ every matrix has a listing; over a general field the existence of one says that the
characteristic polynomial splits. This file has the predicate, its basic interface, and
triangularisation by a similarity over any field; Schur's unitary triangularisation and what
follows from it are in `NLAlib.Matrix.Spectral.Schur`.

## Main definitions

* `NLAlib.IsEigenvalueListing`:
  $\det(X\mathbf{I} - \mathbf{A}) = \prod_i (X - \mathbf{d}_i)$.

## Main results

* `NLAlib.exists_isEigenvalueListing`: a complex matrix has a listing.
* `NLAlib.IsEigenvalueListing.exists_equiv_eq`: two listings differ by a relabelling.
* `NLAlib.IsEigenvalueListing.spectrum_eq_range`, `NLAlib.IsEigenvalueListing.trace_eq_sum`,
  `NLAlib.IsEigenvalueListing.det_eq_prod`: spectrum, trace and determinant through a listing.
* `Matrix.IsUpperTriangular.isEigenvalueListing_diag`: the diagonal of a triangular matrix.
* `NLAlib.exists_isEigenvalueListing_of_forall_im_eq_zero`: a real matrix with real eigenvalues
  has a real listing.
* `NLAlib.charpoly_mul_mul_of_mul_eq_one`: similar matrices have the same characteristic
  polynomial.
* `NLAlib.submatrix_sumCompl_eq_fromBlocks`,
  `NLAlib.fromBlocks_one_submatrix_mul_mul_fromBlocks_one`,
  `NLAlib.isUpperTriangular_fromBlocks_submatrix_sumCompl_symm`: the block lemmas of a deflation
  step, shared with `NLAlib.Matrix.Spectral.Simultaneous`.
* `NLAlib.IsEigenvalueListing.exists_isUpperTriangular_inv_mul_mul_of_commute`: a commuting pair
  over a field is simultaneously similar to triangular matrices, with a prescribed diagonal.
* `NLAlib.IsEigenvalueListing.pow`: the eigenvalues of a power.

## Implementation notes

The triangular forms come from one induction over the size, for a commuting pair: a common
eigenvector is completed to an invertible matrix, and the complementary block is triangularised
by the induction hypothesis.
-/

@[expose] public section

open scoped Matrix
open Polynomial

universe u

namespace NLAlib

variable {K : Type*} [Field K] {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq n]

/-! ### Listings of the eigenvalues -/

/-- `IsEigenvalueListing A d`: the family $\mathbf{d}$ **lists the eigenvalues** of $\mathbf{A}$
with algebraic multiplicity, $\det(X\mathbf{I} - \mathbf{A}) = \prod_i (X - \mathbf{d}_i)$. Over
$\mathbb{C}$ every matrix has a listing; over a general field the existence of one says that the
characteristic polynomial splits. For a Hermitian matrix the sorted `eigenvalue A` is a
listing. -/
def IsEigenvalueListing (A : Matrix n n K) (d : ι → K) : Prop :=
  A.charpoly = ∏ i, (X - C (d i))

/-- `IsEigenvalueListing` unfolded. -/
theorem isEigenvalueListing_iff {A : Matrix n n K} {d : ι → K} :
    IsEigenvalueListing A d ↔ A.charpoly = ∏ i, (X - C (d i)) :=
  Iff.rfl

/-- A listing has as many entries as the matrix has rows: $\lvert \iota \rvert = \lvert n \rvert$.
-/
theorem IsEigenvalueListing.card_eq {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : Fintype.card ι = Fintype.card n := by
  have h1 := congrArg Polynomial.natDegree h
  rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finsetProd_X_sub_C_eq_card] at h1
  rw [h1, Finset.card_univ]

/-- A monic polynomial $p$ that splits is the product of the $X - \mathbf{d}_i$ over a family
$\mathbf{d}$ indexed by any type with as many elements as the degree of $p$. -/
private theorem exists_eq_prod_X_sub_C {p : K[X]} (hp : p.Splits) (hm : p.Monic)
    (hdeg : p.natDegree = Fintype.card ι) : ∃ d : ι → K, p = ∏ i, (X - C (d i)) := by
  have hcard : Fintype.card ι = p.roots.toList.length := by
    rw [Multiset.length_toList, ← hp.natDegree_eq_card_roots, hdeg]
  refine ⟨fun i => p.roots.toList.get (Fintype.equivFinOfCardEq hcard i), ?_⟩
  rw [(Fintype.equivFinOfCardEq hcard).prod_comp fun j => X - C (p.roots.toList.get j),
    ← List.prod_ofFn, show (fun j => X - C (p.roots.toList.get j)) =
      (fun z => X - C z) ∘ p.roots.toList.get from rfl, ← List.map_ofFn, List.ofFn_get,
    Multiset.prod_map_toList]
  exact hp.eq_prod_roots_of_monic hm

/-- A complex matrix has a listing of its eigenvalues. -/
theorem exists_isEigenvalueListing (A : Matrix n n ℂ) : ∃ d : n → ℂ, IsEigenvalueListing A d :=
  exists_eq_prod_X_sub_C (IsAlgClosed.splits _) A.charpoly_monic A.charpoly_natDegree_eq_dim

/-- Two listings of the eigenvalues differ by a relabelling: if $\mathbf{a}$ and $\mathbf{b}$
both list the eigenvalues of $\mathbf{A}$, then $\mathbf{a}_i = \mathbf{b}_{e(i)}$ for a
bijection $e$. -/
theorem IsEigenvalueListing.exists_equiv_eq {A : Matrix n n K} {a : ι → K} {b : κ → K}
    (ha : IsEigenvalueListing A a) (hb : IsEigenvalueListing A b) :
    ∃ e : ι ≃ κ, a = b ∘ e := by
  classical
  have hprod : ((Finset.univ.val.map a).map fun z => X - C z).prod =
      ((Finset.univ.val.map b).map fun z => X - C z).prod := by
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val] using ha.symm.trans hb
  have hroots := congrArg Polynomial.roots hprod
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  have hcount : ∀ c : K, Fintype.card {i // a i = c} = Fintype.card {j // b j = c} := by
    intro c
    have h := congrArg (Multiset.count c) hroots
    rw [Multiset.count_map, Multiset.count_map] at h
    simp only [@eq_comm _ c] at h
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcount c),
    funext fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

/-- A relabelling of a listing is a listing. -/
theorem IsEigenvalueListing.comp_equiv {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) (e : κ ≃ ι) : IsEigenvalueListing A (d ∘ e) := by
  rw [isEigenvalueListing_iff, h]
  exact (e.prod_comp fun i => X - C (d i)).symm

/-- The spectrum is the set of listed eigenvalues: $\{\mathbf{d}_i\}$. -/
theorem IsEigenvalueListing.spectrum_eq_range {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : spectrum K A = Set.range d := by
  ext c
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, h, Polynomial.IsRoot.def, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, eval_sub, eval_X, eval_C, sub_eq_zero, true_and, Set.mem_range,
    eq_comm]

/-- The trace is the sum of the listed eigenvalues:
$\operatorname{tr} \mathbf{A} = \sum_i \mathbf{d}_i$. -/
theorem IsEigenvalueListing.trace_eq_sum {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : A.trace = ∑ i, d i := by
  classical
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, h, ← Matrix.charpoly_diagonal,
    ← Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_diagonal]

/-- The determinant is the product of the listed eigenvalues:
$\det \mathbf{A} = \prod_i \mathbf{d}_i$. -/
theorem IsEigenvalueListing.det_eq_prod {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : A.det = ∏ i, d i := by
  rw [Matrix.det_eq_sign_charpoly_coeff, h, ← h.card_eq, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_prod]
  simp only [eval_sub, eval_X, eval_C, zero_sub, Finset.prod_neg, Finset.card_univ, ← mul_assoc,
    ← mul_pow, neg_mul_neg, one_mul, one_pow]

/-- A matrix with a listing of its eigenvalues has a characteristic polynomial that splits. -/
theorem IsEigenvalueListing.splits_charpoly {A : Matrix n n K} {d : ι → K}
    (h : IsEigenvalueListing A d) : A.charpoly.Splits :=
  h ▸ Splits.prod fun i _ => Splits.X_sub_C (d i)

/-- The diagonal of an upper triangular matrix lists its eigenvalues: $\mathbf{T}_{i,i}$,
$i \in n$. -/
theorem _root_.Matrix.IsUpperTriangular.isEigenvalueListing_diag [LinearOrder n]
    {T : Matrix n n K} (hT : T.IsUpperTriangular) : IsEigenvalueListing T fun i => T i i :=
  Matrix.charpoly_of_isUpperTriangular T hT

/-- A real matrix all of whose complex eigenvalues are real has a real listing of its
eigenvalues. -/
theorem exists_isEigenvalueListing_of_forall_im_eq_zero {A : Matrix n n ℝ}
    (h : ∀ μ ∈ spectrum ℂ (complexify A), μ.im = 0) :
    ∃ d : n → ℝ, IsEigenvalueListing A d := by
  obtain ⟨c, hc⟩ := exists_isEigenvalueListing (complexify A)
  have hval : ∀ i, ((c i).re : ℂ) = c i := fun i =>
    Complex.ext rfl (h (c i) (hc.spectrum_eq_range ▸ Set.mem_range_self i)).symm
  refine ⟨fun i => (c i).re, ?_⟩
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  have hmap : (complexify A).charpoly = A.charpoly.map Complex.ofRealHom := by
    rw [← Matrix.charpoly_map]
    congr 1
  rw [← hmap, hc, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Complex.ofRealHom_eq_coe, hval]

/-! ### Triangularisation over a field -/

/-- A listed eigenvalue has an eigenvector: $\mathbf{x} \ne \mathbf{0}$ with
$\mathbf{A}\mathbf{x} = \mathbf{a}_i\mathbf{x}$. -/
private theorem exists_mulVec_eq_smul {A : Matrix n n K} {a : ι → K}
    (ha : IsEigenvalueListing A a) (i : ι) : ∃ x : n → K, x ≠ 0 ∧ A *ᵥ x = a i • x := by
  have hdet : (Matrix.scalar n (a i) - A).det = 0 := by
    rw [← Matrix.eval_charpoly, ha, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  obtain ⟨x, hx, h⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨x, hx, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  rw [← h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- If a product of factors $\mathbf{B} - c\mathbf{I}$ kills an eigenvector of a matrix
$\mathbf{A}$ commuting with $\mathbf{B}$, then $\mathbf{A}$ and $\mathbf{B}$ have a common
eigenvector for the same eigenvalue of $\mathbf{A}$. -/
private theorem exists_common_eigenvector_of_list_prod {A B : Matrix n n K} (hAB : Commute A B)
    {α : K} (l : List K) : ∀ x : n → K, x ≠ 0 → A *ᵥ x = α • x →
      (l.map fun c => B - c • (1 : Matrix n n K)).prod *ᵥ x = 0 →
      ∃ y : n → K, y ≠ 0 ∧ A *ᵥ y = α • y ∧ ∃ β : K, B *ᵥ y = β • y := by
  induction l using List.reverseRecOn with
  | nil =>
    intro x hx _ h
    rw [List.map_nil, List.prod_nil, Matrix.one_mulVec] at h
    exact (hx h).elim
  | append_singleton l c ih =>
    intro x hx hAx h
    rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      ← Matrix.mulVec_mulVec] at h
    by_cases hz : (B - c • (1 : Matrix n n K)) *ᵥ x = 0
    · refine ⟨x, hx, hAx, c, ?_⟩
      rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
    · refine ih _ hz ?_ h
      have hcomm : Commute A (B - c • (1 : Matrix n n K)) :=
        hAB.sub_right ((Commute.one_right A).smul_right c)
      rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hAx, Matrix.mulVec_smul]

/-- A matrix commuting with $\mathbf{A}$ whose characteristic polynomial splits has an
eigenvector in every eigenspace of $\mathbf{A}$ that belongs to a listed eigenvalue. -/
private theorem exists_common_eigenvector {A B : Matrix n n K} (hAB : Commute A B) {a : ι → K}
    (ha : IsEigenvalueListing A a) (i : ι) (hB : B.charpoly.Splits) :
    ∃ y : n → K, y ≠ 0 ∧ A *ᵥ y = a i • y ∧ ∃ β : K, B *ᵥ y = β • y := by
  obtain ⟨x, hx, hAx⟩ := exists_mulVec_eq_smul ha i
  refine exists_common_eigenvector_of_list_prod hAB B.charpoly.roots.toList x hx hAx ?_
  have h := Matrix.aeval_self_charpoly B
  rw [hB.eq_prod_roots_of_monic B.charpoly_monic, ← Multiset.prod_map_toList, map_list_prod,
    List.map_map] at h
  have hfun : (⇑(Polynomial.aeval B) ∘ fun c : K => X - C c) =
      fun c => B - c • (1 : Matrix n n K) := by
    funext c
    simp [Algebra.algebraMap_eq_smul_one]
  rw [← hfun, h, Matrix.zero_mulVec]

/-- A nonzero vector is a prescribed column of an invertible matrix. -/
private theorem exists_isUnit_det_apply_eq {y : n → K} (hy : y ≠ 0) (i₀ : n) :
    ∃ S : Matrix n n K, IsUnit S.det ∧ ∀ i, S i i₀ = y i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  refine ⟨((1 : Matrix n n K).updateCol j y).submatrix id (Equiv.swap i₀ j), ?_, fun i => ?_⟩
  · rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    exact ((Equiv.Perm.sign _).isUnit.map (Int.castRingHom K)).mul (IsUnit.mk0 _ hj)
  · rw [Matrix.submatrix_apply, Equiv.swap_apply_left, Matrix.updateCol_self, id]

/-- Conjugating by an invertible matrix one of whose columns is an eigenvector puts a multiple of
a coordinate vector in that column: if the column $i_0$ of $\mathbf{S}$ is an eigenvector of
$\mathbf{A}$ for $\alpha$, the column $i_0$ of $\mathbf{S}^{-1}\mathbf{A}\mathbf{S}$ is $\alpha$
times the coordinate vector $\mathbf{e}_{i_0}$. -/
private theorem inv_mul_mul_apply_of_mulVec_eq_smul {A S : Matrix n n K} (hS : IsUnit S.det)
    {i₀ : n} {α : K} (hA : (A *ᵥ fun i => S i i₀) = α • fun i => S i i₀) (i : n) :
    (S⁻¹ * A * S) i i₀ = if i = i₀ then α else 0 := by
  have h1 : (S⁻¹ * A * S) i i₀ = (S⁻¹ *ᵥ (A *ᵥ fun k => S k i₀)) i := by
    rw [Matrix.mulVec_mulVec]
    rfl
  have h2 : (S⁻¹ *ᵥ fun k => S k i₀) = fun k => (1 : Matrix n n K) k i₀ := by
    rw [← Matrix.nonsing_inv_mul S hS]
    rfl
  rw [h1, hA, Matrix.mulVec_smul, h2, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

/-- Similar matrices have the same characteristic polynomial: conjugation by a pair of
mutually inverse matrices over a commutative ring preserves it. For a unit of the matrix ring
this is Mathlib's `Matrix.charpoly_units_conj'`; here the similarity is given by the equation
$\mathbf{S}'\mathbf{S} = \mathbf{I}$, as $\mathbf{S}^{-1}$ with `IsUnit S.det` or
$\mathbf{U}^{\mathsf{H}}$ with `HasOrthonormalCols U` provide it. -/
theorem charpoly_mul_mul_of_mul_eq_one {R : Type*} [CommRing R] {S S' : Matrix n n R}
    (hS : S' * S = 1) (M : Matrix n n R) : (S' * M * S).charpoly = M.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, mul_eq_one_comm.mp hS, Matrix.one_mul]

omit [Fintype n] in
/-- Deflation, block form: a matrix $\mathbf{M}$ whose column $i_0$ is $\alpha$ times a
coordinate vector is block upper triangular for the splitting of the indices into $i_0$ and the
others: reindexed by `Equiv.sumCompl (· = i₀)` it is
$\begin{bmatrix} \alpha & \mathbf{r} \\ \mathbf{0} & \mathbf{M}' \end{bmatrix}$ with
$\mathbf{M}'$ the matrix with the row and the column $i_0$ deleted. This is the step of every
triangularisation by induction on the size, after a similarity has put an eigenvector in the
column $i_0$. -/
theorem submatrix_sumCompl_eq_fromBlocks {M : Matrix n n K} {i₀ : n} {α : K}
    (hcol : ∀ i, M i i₀ = if i = i₀ then α else 0) :
    M.submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) =
      Matrix.fromBlocks (Matrix.diagonal fun _ => α)
        (Matrix.of fun (i : {i // i = i₀}) (j : {i // ¬i = i₀}) => M i j) 0
        (M.submatrix Subtype.val Subtype.val) := by
  ext (⟨i, hi⟩ | ⟨i, hi⟩) (⟨j, hj⟩ | ⟨j, hj⟩)
  · subst hi hj
    simp [hcol]
  · simp
  · subst hj
    simp [hcol, hi]
  · simp

omit [Fintype n] in
/-- Isolating row and column $i$ of $\mathbf{M}$ at $\mu$ gives the scalar direct-sum block
$[\mu]\oplus\mathbf{B}$, where $\mathbf{B}$ deletes row and column $i$.
This derives the paired deflation block from the existing one-column block decomposition.
Adapted from `NLAlib.submatrix_eq_fromBlocks_of_isolated_coordinate` in
`tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`. -/
theorem submatrix_eq_fromBlocks_of_isolated_coordinate (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hrow : ∀ j, M i j = if j = i then μ else 0) :
    M.submatrix (Equiv.sumCompl (fun j => j = i)) (Equiv.sumCompl (fun j => j = i)) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : {j : n // j = i} => μ)) 0 0
        (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  rw [submatrix_sumCompl_eq_fromBlocks hcol]
  congr 1
  ext ⟨j, hj⟩ ⟨k, hk⟩
  change M j k = 0
  rw [hj, hrow, if_neg hk]

/-- The characteristic polynomial of a matrix with a multiple $\alpha$ of a coordinate vector in
the column $i_0$ loses a linear factor $X - \alpha$ when the row and the column $i_0$ are
deleted. -/
theorem charpoly_eq_X_sub_C_mul_charpoly_submatrix {M : Matrix n n K} {i₀ : n} {α : K}
    [DecidableEq {i // ¬i = i₀}] (hcol : ∀ i, M i i₀ = if i = i₀ then α else 0) :
    M.charpoly = (X - C α) *
      (M.submatrix (Subtype.val : {i // ¬i = i₀} → n) Subtype.val).charpoly := by
  rw [← Matrix.charpoly_reindex (Equiv.sumCompl (· = i₀)).symm M, Matrix.reindex_apply,
    Equiv.symm_symm, submatrix_sumCompl_eq_fromBlocks hcol, Matrix.charpoly_fromBlocks_zero₂₁,
    Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_subtype_eq,
    pow_one]

omit [DecidableEq n] in
/-- Conjugating a block upper triangular matrix by block diagonal matrices
$\operatorname{diag}(\mathbf{I}, \mathbf{S}')$ and $\operatorname{diag}(\mathbf{I}, \mathbf{S})$,
in the original indices: for $\mathbf{M}$ with block form
$\begin{bmatrix} \mathbf{D} & \mathbf{r} \\ \mathbf{0} & \mathbf{M}' \end{bmatrix}$ along
$e : q \oplus p \simeq n$, the product
$\operatorname{diag}(\mathbf{I}, \mathbf{S}') \, \mathbf{M} \operatorname{diag}(\mathbf{I},
\mathbf{S})$ has block form
$\begin{bmatrix} \mathbf{D} & \mathbf{r}\mathbf{S} \\ \mathbf{0} & \mathbf{S}'\mathbf{M}'\mathbf{S}
\end{bmatrix}$. The induction step of a triangularisation applies it with
$\mathbf{S}' = \mathbf{S}^{-1}$ or $\mathbf{S}' = \mathbf{S}^{\mathsf{H}}$. -/
theorem fromBlocks_one_submatrix_mul_mul_fromBlocks_one {p q : Type*} [Fintype p]
    [Finite q] [DecidableEq q] (e : q ⊕ p ≃ n) {M : Matrix n n K} {D : Matrix q q K}
    {r : Matrix q p K} {M' : Matrix p p K} (hM : M.submatrix e e = Matrix.fromBlocks D r 0 M')
    (S S' : Matrix p p K) :
    (Matrix.fromBlocks (1 : Matrix q q K) 0 0 S').submatrix e.symm e.symm * M *
        (Matrix.fromBlocks (1 : Matrix q q K) 0 0 S).submatrix e.symm e.symm =
      (Matrix.fromBlocks D (r * S) 0 (S' * M' * S)).submatrix e.symm e.symm := by
  cases nonempty_fintype q
  have hM' : M = (Matrix.fromBlocks D r 0 M').submatrix e.symm e.symm := by
    rw [← hM, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
  rw [hM', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

omit [Fintype n] in
/-- A block upper triangular matrix for the splitting of the indices into $i_0$ and the others is
upper triangular when its second diagonal block is and $i_0$ is the least index. -/
theorem isUpperTriangular_fromBlocks_submatrix_sumCompl_symm [LinearOrder n] {i₀ : n}
    (hi₀ : ∀ j, i₀ ≤ j) (D : Matrix {i // i = i₀} {i // i = i₀} K)
    (r : Matrix {i // i = i₀} {i // ¬i = i₀} K) {T : Matrix {i // ¬i = i₀} {i // ¬i = i₀} K}
    (hT : T.IsUpperTriangular) :
    ((Matrix.fromBlocks D r 0 T).submatrix (Equiv.sumCompl (· = i₀)).symm
      (Equiv.sumCompl (· = i₀)).symm).IsUpperTriangular := by
  intro i j hji
  have hi : ¬i = i₀ := fun h => (hi₀ j).not_gt (h ▸ hji)
  rw [Matrix.submatrix_apply, Equiv.sumCompl_symm_apply_of_neg (p := (· = i₀)) hi]
  by_cases hj : j = i₀
  · rw [Equiv.sumCompl_symm_apply_of_pos (p := (· = i₀)) hj, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
  · rw [Equiv.sumCompl_symm_apply_of_neg (p := (· = i₀)) hj, Matrix.fromBlocks_apply₂₂]
    exact hT (show (⟨j, hj⟩ : {i // ¬i = i₀}) < ⟨i, hi⟩ from hji)

/-- Simultaneous triangularisation of a commuting pair over a field, by induction on the size:
the first matrix has a listing of its eigenvalues, which becomes the diagonal, and the
characteristic polynomial of the second splits. -/
private theorem exists_triangular_pair_aux (k : ℕ) :
    ∀ (n : Type u) [Fintype n] [DecidableEq n] [LinearOrder n], Fintype.card n = k →
      ∀ (A B : Matrix n n K) (a : n → K), Commute A B → IsEigenvalueListing A a →
        B.charpoly.Splits → ∃ S S' : Matrix n n K, S' * S = 1 ∧
          (S' * A * S).IsUpperTriangular ∧ (∀ i, (S' * A * S) i i = a i) ∧
          (S' * B * S).IsUpperTriangular := by
  induction k with
  | zero =>
    intro n _ _ _ hn A B a _ _ _
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    exact ⟨1, 1, Subsingleton.elim _ _, fun i => isEmptyElim i, fun i => isEmptyElim i,
      fun i => isEmptyElim i⟩
  | succ k ih =>
    intro n _ _ _ hn A B a hAB ha hB
    have : Nonempty n := Fintype.card_pos_iff.mp (hn ▸ k.succ_pos)
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min (id : n → n)
    obtain ⟨y, hy, hAy, β, hBy⟩ := exists_common_eigenvector hAB ha i₀ hB
    obtain ⟨W, hW, hWy⟩ := exists_isUnit_det_apply_eq hy i₀
    obtain rfl : (fun i => W i i₀) = y := funext hWy
    have hcolA := inv_mul_mul_apply_of_mulVec_eq_smul hW hAy
    have hcolB := inv_mul_mul_apply_of_mulVec_eq_smul hW hBy
    have hMA := submatrix_sumCompl_eq_fromBlocks hcolA
    have hMB := submatrix_sumCompl_eq_fromBlocks hcolB
    have hcard : Fintype.card {i // ¬i = i₀} = k := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hn, Nat.add_sub_cancel]
    have hA' : IsEigenvalueListing ((W⁻¹ * A * W).submatrix
        (Subtype.val : {i // ¬i = i₀} → n) Subtype.val) fun i : {i // ¬i = i₀} => a i := by
      have h := charpoly_eq_X_sub_C_mul_charpoly_submatrix hcolA
      have hsplit : ∏ i, (X - C (a i)) =
          (X - C (a i₀)) * ∏ i : {i // ¬i = i₀}, (X - C (a i)) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
          Finset.prod_subtype (Finset.univ.erase i₀) (p := fun i => ¬i = i₀) (by simp)]
      rw [charpoly_mul_mul_of_mul_eq_one (Matrix.nonsing_inv_mul _ hW), ha, hsplit] at h
      exact (mul_left_cancel₀ (X_sub_C_ne_zero (a i₀)) h).symm
    have hB' : ((W⁻¹ * B * W).submatrix
        (Subtype.val : {i // ¬i = i₀} → n) Subtype.val).charpoly.Splits := by
      have h := charpoly_eq_X_sub_C_mul_charpoly_submatrix hcolB
      rw [charpoly_mul_mul_of_mul_eq_one (Matrix.nonsing_inv_mul _ hW)] at h
      exact splits_X_sub_C_mul_iff.mp (h ▸ hB)
    have hcomm : Commute
        ((W⁻¹ * A * W).submatrix Subtype.val Subtype.val :
          Matrix {i // ¬i = i₀} {i // ¬i = i₀} K)
        ((W⁻¹ * B * W).submatrix Subtype.val Subtype.val) := by
      have h : (W⁻¹ * A * W) * (W⁻¹ * B * W) = (W⁻¹ * B * W) * (W⁻¹ * A * W) := by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hW]
        rw [← Matrix.mul_assoc A, hAB.eq, Matrix.mul_assoc]
      have h' : (W⁻¹ * A * W).submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) *
            (W⁻¹ * B * W).submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) =
          (W⁻¹ * B * W).submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) *
            (W⁻¹ * A * W).submatrix (Equiv.sumCompl (· = i₀)) (Equiv.sumCompl (· = i₀)) := by
        rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]
      rw [hMA, hMB, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_inj] at h'
      have h2 := h'.2.2.2
      rw [Matrix.zero_mul, zero_add, Matrix.zero_mul, zero_add] at h2
      exact h2
    obtain ⟨S₁, S₁', h11, hTA, hdA, hTB⟩ := ih {i // ¬i = i₀} hcard _ _ _ hcomm hA' hB'
    have key : ∀ F F' M : Matrix n n K, F' * W⁻¹ * M * (W * F) = F' * (W⁻¹ * M * W) * F :=
      fun F F' M => by simp only [Matrix.mul_assoc]
    refine ⟨W * (Matrix.fromBlocks (1 : Matrix {i // i = i₀} {i // i = i₀} K) 0 0 S₁).submatrix
        (Equiv.sumCompl (· = i₀)).symm (Equiv.sumCompl (· = i₀)).symm,
      (Matrix.fromBlocks (1 : Matrix {i // i = i₀} {i // i = i₀} K) 0 0 S₁').submatrix
        (Equiv.sumCompl (· = i₀)).symm (Equiv.sumCompl (· = i₀)).symm * W⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hW, Matrix.submatrix_mul_equiv,
        Matrix.fromBlocks_multiply]
      simp [h11, Matrix.fromBlocks_one]
    · rw [key, fromBlocks_one_submatrix_mul_mul_fromBlocks_one _ hMA]
      exact isUpperTriangular_fromBlocks_submatrix_sumCompl_symm hi₀ _ _ hTA
    · intro i
      rw [key, fromBlocks_one_submatrix_mul_mul_fromBlocks_one _ hMA, Matrix.submatrix_apply]
      by_cases hi : i = i₀
      · rw [Equiv.sumCompl_symm_apply_of_pos (p := (· = i₀)) hi, Matrix.fromBlocks_apply₁₁,
          Matrix.diagonal_apply_eq, hi]
      · rw [Equiv.sumCompl_symm_apply_of_neg (p := (· = i₀)) hi, Matrix.fromBlocks_apply₂₂]
        exact hdA ⟨i, hi⟩
    · rw [key, fromBlocks_one_submatrix_mul_mul_fromBlocks_one _ hMB]
      exact isUpperTriangular_fromBlocks_submatrix_sumCompl_symm hi₀ _ _ hTB

/-- **Triangularisation over a field.** Commuting matrices $\mathbf{A}$ and $\mathbf{B}$ over a
field, where $\mathbf{a}$ lists the eigenvalues of $\mathbf{A}$ and the characteristic polynomial
of $\mathbf{B}$ splits, are simultaneously similar to upper triangular matrices: there is an
invertible $\mathbf{S}$ with $\mathbf{S}^{-1}\mathbf{A}\mathbf{S}$ and
$\mathbf{S}^{-1}\mathbf{B}\mathbf{S}$ upper triangular and
$(\mathbf{S}^{-1}\mathbf{A}\mathbf{S})_{i,i} = \mathbf{a}_i$ for every $i$. With
$\mathbf{B} = \mathbf{A}$ this is triangularisation of one matrix whose characteristic polynomial
splits. Over an `RCLike` field the similarity can be taken unitary:
`NLAlib.IsEigenvalueListing.exists_hasOrthonormalCols_isUpperTriangular`.
[HornJohnson2013, Theorem 2.3.3], there for commuting families of complex matrices. -/
theorem IsEigenvalueListing.exists_isUpperTriangular_inv_mul_mul_of_commute [LinearOrder n]
    {A B : Matrix n n K} {a : n → K} (ha : IsEigenvalueListing A a) (hAB : Commute A B)
    (hB : B.charpoly.Splits) :
    ∃ S : Matrix n n K, IsUnit S.det ∧ (S⁻¹ * A * S).IsUpperTriangular ∧
      (∀ i, (S⁻¹ * A * S) i i = a i) ∧ (S⁻¹ * B * S).IsUpperTriangular := by
  obtain ⟨S, S', hS, h⟩ := exists_triangular_pair_aux _ n rfl A B a hAB ha hB
  rw [← Matrix.inv_eq_left_inv hS] at h
  exact ⟨S, Matrix.isUnit_det_of_left_inverse hS, h⟩

/-! ### Powers -/

/-- The diagonal of a power of an upper triangular matrix:
$(\mathbf{T}^k)_{i,i} = (\mathbf{T}_{i,i})^k$. -/
private theorem pow_apply_self_of_isUpperTriangular [LinearOrder n] {T : Matrix n n K}
    (hT : T.IsUpperTriangular) (k : ℕ) (i : n) : (T ^ k) i i = T i i ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.one_apply_eq]
  | succ k ih => rw [pow_succ, Matrix.IsUpperTriangular.mul_apply_self (hT.pow k) hT, ih, pow_succ]

/-- The eigenvalues of a power are the powers of the eigenvalues: if $\mathbf{d}$ lists the
eigenvalues of $\mathbf{A}$, then $(\mathbf{d}_i^k)_i$ lists those of $\mathbf{A}^k$. -/
theorem IsEigenvalueListing.pow {A : Matrix n n K} {d : ι → K} (h : IsEigenvalueListing A d)
    (k : ℕ) : IsEigenvalueListing (A ^ k) (fun i => d i ^ k) := by
  classical
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  have h' := h.comp_equiv (Fintype.equivOfCardEq h.card_eq.symm)
  obtain ⟨S, hS, hT, hdiag, -⟩ :=
    h'.exists_isUpperTriangular_inv_mul_mul_of_commute (Commute.refl A) h.splits_charpoly
  have hpow : S⁻¹ * A ^ k * S = (S⁻¹ * A * S) ^ k := by
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.nonsing_inv_mul _ hS]
    | succ k ih =>
      rw [pow_succ, pow_succ, ← ih]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hS]
  rw [isEigenvalueListing_iff, ← charpoly_mul_mul_of_mul_eq_one (Matrix.nonsing_inv_mul _ hS),
    hpow, Matrix.charpoly_of_isUpperTriangular _ (hT.pow k)]
  simp only [pow_apply_self_of_isUpperTriangular hT, hdiag, Function.comp_apply]
  exact (Fintype.equivOfCardEq h.card_eq.symm).prod_comp fun i => X - C (d i ^ k)

end NLAlib
