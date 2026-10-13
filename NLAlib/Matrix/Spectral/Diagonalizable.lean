/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import NLAlib.Matrix.Spectral.EigenvectorPairing
public import NLAlib.Matrix.Spectral.Simultaneous

/-!
# Diagonalisable matrices

A square matrix over a field is diagonalisable when it has a basis of eigenvectors,
`NLAlib.IsDiagonalizable A`. This file gives the equivalent forms, the standard sufficient
conditions and simultaneous diagonalisation of commuting families. Left and right eigenvectors
are in `NLAlib.Matrix.Spectral.EigenvectorPairing`, the Sylvester equation `A X - X B = C` in
`NLAlib.Matrix.Spectral.SylvesterEquation`.

## Main definitions

* `NLAlib.IsDiagonalizable`: `A * V = V * diagonal d` for an invertible `V`.

## Main results

* `NLAlib.isDiagonalizable_iff_exists_eq_mul_diagonal_mul_inv`.
* `NLAlib.isDiagonalizable_of_injective_of_forall_mem_spectrum`: distinct eigenvalues.
* `NLAlib.isDiagonalizable_iff_isSemisimple`.
* `NLAlib.exists_forall_mul_eq_mul_diagonal_of_pairwise_commute`: commuting families.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {K : Type*} [Field K] {ι m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Diagonalisability -/

/-- A square matrix is **diagonalisable** if `A * V = V * diagonal d` for an invertible `V`: the
columns of `V` are a basis of eigenvectors. [HornJohnson2013, Definition 1.3.6].
Port of `NLAlib.IsDiagonalizable`. -/
def IsDiagonalizable (A : Matrix n n K) : Prop :=
  ∃ (V : Matrix n n K) (d : n → K), IsUnit V.det ∧ A * V = V * Matrix.diagonal d

/-- Diagonalisability as a similarity `A = V D V⁻¹`.
Port of `NLAlib.isDiagonalizable_iff_exists_similarity`. -/
theorem isDiagonalizable_iff_exists_eq_mul_diagonal_mul_inv {A : Matrix n n K} :
    IsDiagonalizable A ↔
      ∃ (V : Matrix n n K) (d : n → K), IsUnit V.det ∧ A = V * Matrix.diagonal d * V⁻¹ := by
  refine exists_congr fun V => exists_congr fun d => and_congr_right fun hV => ⟨fun h => ?_,
    fun h => ?_⟩
  · rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]
  · rw [h, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hV, Matrix.mul_one]

/-- A matrix equation `A * V = V * diagonal d` says that the columns of `V` are eigenvectors. -/
private theorem mul_eq_mul_diagonal_iff {A V : Matrix n n K} {d : n → K} :
    A * V = V * Matrix.diagonal d ↔ ∀ j, A *ᵥ V.col j = d j • V.col j := by
  refine ⟨fun h j => funext fun i => ?_, fun h => Matrix.ext fun i j => ?_⟩
  · have h1 := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal] at h1
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, Matrix.col_apply, ← h1]
    rfl
  · have h1 := congrFun (h j) i
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, Matrix.col_apply] at h1
    rw [Matrix.mul_diagonal, ← h1]
    rfl

/-- Diagonalisability as a linearly independent family of eigenvectors.
Port of `NLAlib.isDiagonalizable_iff_exists_independent_eigenvectors`. -/
theorem isDiagonalizable_iff_exists_linearIndependent {A : Matrix n n K} :
    IsDiagonalizable A ↔
      ∃ (v : n → n → K) (d : n → K), LinearIndependent K v ∧ ∀ j, A *ᵥ v j = d j • v j := by
  constructor
  · rintro ⟨V, d, hV, h⟩
    exact ⟨V.col, d, Matrix.linearIndependent_cols_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det V).mpr hV), mul_eq_mul_diagonal_iff.mp h⟩
  · rintro ⟨v, d, hv, h⟩
    have hcol : (Matrix.of fun i j => v j i : Matrix n n K).col = v := rfl
    refine ⟨Matrix.of fun i j => v j i, d, (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp (hcol ▸ hv)), mul_eq_mul_diagonal_iff.mpr ?_⟩
    rw [hcol]
    exact h

/-- The diagonal of a diagonalisation lists the eigenvalues. -/
theorem isEigenvalueListing_of_mul_eq_mul_diagonal {A V : Matrix n n K} {d : n → K}
    (hV : IsUnit V.det) (h : A * V = V * Matrix.diagonal d) :
    IsEigenvalueListing A d := by
  have hA : A = V * Matrix.diagonal d * V⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]
  rw [isEigenvalueListing_iff, hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hV, Matrix.one_mul, Matrix.charpoly_diagonal]

/-- **A matrix with distinct eigenvalues is diagonalisable.**
[HornJohnson2013, Theorem 1.3.9]. Port of `NLAlib.isDiagonalizable_of_distinct_eigenvalues`. -/
theorem isDiagonalizable_of_injective_of_forall_mem_spectrum {A : Matrix n n K} {d : n → K}
    (hd : Function.Injective d) (h : ∀ j, d j ∈ spectrum K A) : IsDiagonalizable A := by
  choose v hv hAv using fun j => exists_mulVec_eq_smul_of_mem_spectrum (h j)
  refine isDiagonalizable_iff_exists_linearIndependent.mpr ⟨v, d,
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) d hd v fun j =>
      ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv j⟩, hAv⟩
  rw [Matrix.toLin'_apply, hAv]

omit [Fintype n] [DecidableEq n] in
/-- A spanning set of vectors contains a linearly independent family indexed by `n`. -/
private theorem exists_linearIndependent_of_span_eq_top [Finite n] {S : Set (n → K)}
    (hS : Submodule.span K S = ⊤) :
    ∃ v : n → n → K, LinearIndependent K v ∧ ∀ j, v j ∈ S := by
  cases nonempty_fintype n
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent K S
  have := hli.setFinite.fintype
  have hcard : Fintype.card b = Fintype.card n := by
    have h1 := finrank_span_eq_card hli
    rw [Subtype.range_val, hspan, hS, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
    exact h1.symm
  exact ⟨fun j => ((Fintype.equivOfCardEq hcard).symm j : n → K),
    hli.comp _ (Fintype.equivOfCardEq hcard).symm.injective,
    fun j => hbS ((Fintype.equivOfCardEq hcard).symm j).2⟩

/-- A matrix is diagonalisable exactly when its eigenspaces span.
Port of `NLAlib.isDiagonalizable_iff_iSup_eigenspace_eq_top`. -/
theorem isDiagonalizable_iff_iSup_eigenspace_eq_top {A : Matrix n n K} :
    IsDiagonalizable A ↔ ⨆ μ, Module.End.eigenspace (Matrix.toLin' A) μ = ⊤ := by
  rw [isDiagonalizable_iff_exists_linearIndependent]
  constructor
  · rintro ⟨v, d, hv, h⟩
    rw [eq_top_iff, ← hv.span_eq_top_of_card_eq_finrank'
      (Module.finrank_fintype_fun_eq_card K).symm, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.mem_iSup_of_mem (d j) (Module.End.mem_eigenspace_iff.mpr ?_)
    rw [Matrix.toLin'_apply, h]
  · intro h
    have hS : Submodule.span K {x : n → K | ∃ μ : K, A *ᵥ x = μ • x} = ⊤ := by
      rw [eq_top_iff, ← h]
      refine iSup_le fun μ x hx => Submodule.subset_span ⟨μ, ?_⟩
      rw [← Matrix.toLin'_apply]
      exact Module.End.mem_eigenspace_iff.mp hx
    obtain ⟨v, hv, hvS⟩ := exists_linearIndependent_of_span_eq_top hS
    choose d hd using hvS
    exact ⟨v, d, hv, hd⟩

/-- A diagonalisable matrix is semisimple. Port of `NLAlib.IsDiagonalizable.isSemisimple`. -/
theorem IsDiagonalizable.isSemisimple {A : Matrix n n K} (hA : IsDiagonalizable A) :
    Module.End.IsSemisimple (Matrix.toLin' A) := by
  classical
  obtain ⟨v, d, hv, h⟩ := isDiagonalizable_iff_exists_linearIndependent.mp hA
  have hsq : Squarefree (∏ μ ∈ Finset.univ.image d, (X - C μ)) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun α _ β _ hαβ => ?_) fun μ _ =>
      (Polynomial.irreducible_X_sub_C μ).squarefree
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hαβ))).isRelPrime
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (LinearMap.ext_on
    (hv.span_eq_top_of_card_eq_finrank' (Module.finrank_fintype_fun_eq_card K).symm) ?_)
  rintro _ ⟨j, rfl⟩
  have hj : Matrix.toLin' A (v j) = d j • v j := by rw [Matrix.toLin'_apply, h]
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hj, Polynomial.eval_prod,
    Finset.prod_eq_zero (Finset.mem_image_of_mem d (Finset.mem_univ j)) (by simp), zero_smul,
    LinearMap.zero_apply]

/-- Over an algebraically closed field a semisimple matrix is diagonalisable.
Port of `NLAlib.isDiagonalizable_of_isSemisimple`. -/
theorem isDiagonalizable_of_isSemisimple [IsAlgClosed K] {A : Matrix n n K}
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) : IsDiagonalizable A :=
  isDiagonalizable_iff_iSup_eigenspace_eq_top.mpr hA.iSup_eigenspace_eq_top

/-- Over an algebraically closed field, diagonalisable means semisimple.
Port of `NLAlib.isDiagonalizable_iff_isSemisimple`. -/
theorem isDiagonalizable_iff_isSemisimple [IsAlgClosed K] {A : Matrix n n K} :
    IsDiagonalizable A ↔ Module.End.IsSemisimple (Matrix.toLin' A) :=
  ⟨IsDiagonalizable.isSemisimple, isDiagonalizable_of_isSemisimple⟩

/-- Diagonalisability passes along a surjective linear map that intertwines two matrices. -/
private theorem IsDiagonalizable.of_surjective {A : Matrix m m K} {B : Matrix n n K}
    (hB : IsDiagonalizable B) (T : (n → K) →ₗ[K] (m → K)) (hT : Function.Surjective T)
    (h : ∀ x, T (B *ᵥ x) = A *ᵥ T x) : IsDiagonalizable A := by
  rw [isDiagonalizable_iff_iSup_eigenspace_eq_top, eq_top_iff, ← LinearMap.range_eq_top.mpr hT,
    ← Submodule.map_top, ← isDiagonalizable_iff_iSup_eigenspace_eq_top.mp hB,
    Submodule.map_iSup]
  refine iSup_mono fun μ => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : B *ᵥ x = μ • x := by
    rw [← Matrix.toLin'_apply]
    exact Module.End.mem_eigenspace_iff.mp hx
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, ← h, hx', map_smul]

/-- A block diagonal matrix is diagonalisable exactly when its blocks are.
Port of `NLAlib.isDiagonalizable_fromBlocks_zero_zero_iff`. -/
theorem isDiagonalizable_fromBlocks_diagonal_iff {A : Matrix m m K} {B : Matrix n n K} :
    IsDiagonalizable (Matrix.fromBlocks A 0 0 B) ↔ IsDiagonalizable A ∧ IsDiagonalizable B := by
  constructor
  · intro h
    constructor
    · refine h.of_surjective (LinearMap.funLeft K K Sum.inl) (fun x => ⟨Sum.elim x 0, rfl⟩)
        fun x => funext fun i => ?_
      simp [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    · refine h.of_surjective (LinearMap.funLeft K K Sum.inr) (fun x => ⟨Sum.elim 0 x, rfl⟩)
        fun x => funext fun i => ?_
      simp [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · rintro ⟨⟨V, d, hV, hAV⟩, ⟨W, e, hW, hBW⟩⟩
    refine ⟨Matrix.fromBlocks V 0 0 W, Sum.elim d e, ?_, ?_⟩
    · rw [Matrix.det_fromBlocks_zero₂₁]
      exact hV.mul hW
    · rw [← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, hAV, hBW]

/-- A Hermitian matrix is diagonalisable. Port of `NLAlib.isDiagonalizable_of_isHermitian`. -/
theorem _root_.Matrix.IsHermitian.isDiagonalizable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : IsDiagonalizable A := by
  obtain ⟨U, hU, hd⟩ := exists_hasOrthonormalCols_forall_eq_mul_diagonal_of_pairwise_commute
    (A := fun _ : Unit => A) (fun _ => hA) (fun i j hij => (hij (Subsingleton.elim i j)).elim)
  obtain ⟨d, rfl⟩ := hd ()
  refine ⟨U, fun j => ((d j : ℝ) : 𝕜), (Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit, ?_⟩
  rw [Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]

/-- A normal complex matrix is diagonalisable. -/
theorem _root_.IsStarNormal.isDiagonalizable {A : Matrix n n ℂ} (hA : IsStarNormal A) :
    IsDiagonalizable A := by
  obtain ⟨U, d, hU, rfl⟩ := isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose.mp hA
  refine ⟨U, d, (Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit, ?_⟩
  rw [Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]

/-- **A commuting family of diagonalisable matrices is simultaneously diagonalisable.**
[HornJohnson2013, Theorem 1.3.21].
Port of `NLAlib.exists_simultaneous_diagonalization_of_commute`. -/
theorem exists_forall_mul_eq_mul_diagonal_of_pairwise_commute {A : ι → Matrix n n K}
    (hA : ∀ i, IsDiagonalizable (A i)) (h : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ V : Matrix n n K, IsUnit V.det ∧ ∀ i, ∃ d : n → K, A i * V = V * Matrix.diagonal d := by
  have hcomm : Pairwise fun i j => Commute (Matrix.toLin' (A i)) (Matrix.toLin' (A j)) :=
    fun i j hij => (h hij).map Matrix.toLinAlgEquiv'
  have hgen : ∀ (i : ι) (μ : K), Module.End.maxGenEigenspace (Matrix.toLin' (A i)) μ =
      Module.End.eigenspace (Matrix.toLin' (A i)) μ := fun i μ =>
    (hA i).isSemisimple.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hspan :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun i => Matrix.toLin' (A i)) hcomm fun i => by
        simp only [hgen]
        exact isDiagonalizable_iff_iSup_eigenspace_eq_top.mp (hA i)
  simp only [hgen] at hspan
  have hS : Submodule.span K {x : n → K | ∀ i, ∃ μ : K, A i *ᵥ x = μ • x} = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup_le fun χ x hx => Submodule.subset_span fun i => ⟨χ i, ?_⟩
    rw [← Matrix.toLin'_apply]
    exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx i)
  obtain ⟨v, hv, hvS⟩ := exists_linearIndependent_of_span_eq_top hS
  have hcol : (Matrix.of fun i j => v j i : Matrix n n K).col = v := rfl
  refine ⟨Matrix.of fun i j => v j i, (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp (hcol ▸ hv)), fun i => ?_⟩
  choose d hd using fun j => hvS j i
  exact ⟨d, mul_eq_mul_diagonal_iff.mpr (hcol ▸ hd)⟩

/-- Simultaneously diagonalisable matrices commute.
Port of `NLAlib.commute_of_simultaneous_diagonalization`. -/
theorem commute_of_mul_eq_mul_diagonal {A B V : Matrix n n K} {a b : n → K} (hV : IsUnit V.det)
    (hA : A * V = V * Matrix.diagonal a) (hB : B * V = V * Matrix.diagonal b) : Commute A B := by
  have h : A * B * V = B * A * V := by
    rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc, Matrix.mul_assoc, hA,
      ← Matrix.mul_assoc B V, hB, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]
  have h' : A * B = B * A := by
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one] using
      congrArg (· * V⁻¹) h
  exact h'

end NLAlib
