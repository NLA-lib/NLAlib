/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.EigenvectorPairing
public import NLAlib.Matrix.Spectral.Normal
public import NLAlib.Matrix.Spectral.Simultaneous

/-!
# Diagonalisable matrices

A square matrix over a field is diagonalisable when it has a basis of eigenvectors,
`NLAlib.IsDiagonalizable A`. This file gives the equivalent forms, the standard sufficient
conditions and simultaneous diagonalisation of commuting families; over $\mathbb{C}$, it computes
polynomials of a diagonalised matrix in its eigenbasis. Left and right eigenvectors are in
`NLAlib.Matrix.Spectral.EigenvectorPairing`, the Sylvester equation
$\mathbf{A}\mathbf{X} - \mathbf{X}\mathbf{B} = \mathbf{C}$ in
`NLAlib.Matrix.Spectral.SylvesterEquation`.

## Main definitions

* `NLAlib.IsDiagonalizable`: $\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d})$
  for an invertible $\mathbf{V}$.

## Main results

* `NLAlib.mul_eq_mul_diagonal_iff`: columns of an eigenvector matrix are eigenvectors.

* `NLAlib.isDiagonalizable_iff_exists_eq_mul_diagonal_mul_inv`.
* `NLAlib.isDiagonalizable_of_injective_of_forall_mem_spectrum`: distinct eigenvalues.
* `NLAlib.isDiagonalizable_iff_isSemisimple`.
* `NLAlib.isDiagonalizable_iff_forall_finrank_eigenspace_eq_rootMultiplicity`:
  equality of geometric and algebraic multiplicities.
* `NLAlib.card_add_finrank_eigenspace_le`: geometric multiplicity under principal compression.
* `NLAlib.mem_spectrum_submatrix_of_card_lt_add_finrank_eigenspace`: eigenvalue survival.
* `NLAlib.inv_mul_apply_eq_zero_of_ne`: coordinates in an eigenvector basis.
* `NLAlib.exists_forall_mul_eq_mul_diagonal_of_pairwise_commute`: commuting families.
* `NLAlib.aeval_eq_mul_diagonal_mul_inv`, `NLAlib.inv_aeval_eq_mul_diagonal_mul_inv`,
  `NLAlib.mul_diagonal_mul_inv_pow`: polynomials, their inverses and powers of a diagonalised
  complex matrix in its eigenbasis.
* `NLAlib.norm_le_specNorm_of_mul_eq_mul_diagonal`: an eigenvalue is at most the spectral norm.
* `IsStarNormal.exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_eq_one`: a normal
  matrix has a unitary eigenvector matrix.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {K : Type*} [Field K] {ι m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Diagonalisability -/

/-- A square matrix is **diagonalisable** if
$\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d})$ for an invertible $\mathbf{V}$:
the columns of $\mathbf{V}$ are a basis of eigenvectors. [HornJohnson2013, Definition 1.3.6]. -/
def IsDiagonalizable (A : Matrix n n K) : Prop :=
  ∃ (V : Matrix n n K) (d : n → K), IsUnit V.det ∧ A * V = V * Matrix.diagonal d

/-- Diagonalisability as a similarity
$\mathbf{A} = \mathbf{V} \operatorname{diag}(\mathbf{d}) \mathbf{V}^{-1}$ with $\mathbf{V}$
invertible. -/
theorem isDiagonalizable_iff_exists_eq_mul_diagonal_mul_inv {A : Matrix n n K} :
    IsDiagonalizable A ↔
      ∃ (V : Matrix n n K) (d : n → K), IsUnit V.det ∧ A = V * Matrix.diagonal d * V⁻¹ := by
  refine exists_congr fun V => exists_congr fun d => and_congr_right fun hV => ⟨fun h => ?_,
    fun h => ?_⟩
  · rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]
  · rw [h, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hV, Matrix.mul_one]

/-- A matrix equation $\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d})$ says
that the columns of $\mathbf{V}$ are eigenvectors: $\mathbf{A}\mathbf{v}_j = \mathbf{d}_j
\mathbf{v}_j$ for each column $\mathbf{v}_j$. -/
theorem mul_eq_mul_diagonal_iff {A V : Matrix n n K} {d : n → K} :
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

/-- Diagonalisability as a linearly independent family of eigenvectors: vectors $\mathbf{v}_j$,
$j \in n$, linearly independent, with $\mathbf{A}\mathbf{v}_j = \mathbf{d}_j \mathbf{v}_j$. -/
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

/-- The diagonal of a diagonalisation lists the eigenvalues: if $\mathbf{V}$ is invertible and
$\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d})$, the entries of $\mathbf{d}$
are the eigenvalues of $\mathbf{A}$ with multiplicity (`IsEigenvalueListing`). -/
theorem isEigenvalueListing_of_mul_eq_mul_diagonal {A V : Matrix n n K} {d : n → K}
    (hV : IsUnit V.det) (h : A * V = V * Matrix.diagonal d) :
    IsEigenvalueListing A d := by
  have hA : A = V * Matrix.diagonal d * V⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]
  rw [isEigenvalueListing_iff, hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hV, Matrix.one_mul, Matrix.charpoly_diagonal]

/-- **A matrix with distinct eigenvalues is diagonalisable**: if the entries of $\mathbf{d}$ are
pairwise distinct and each lies in the spectrum of $\mathbf{A}$, then $\mathbf{A}$ is
diagonalisable.
[HornJohnson2013, Theorem 1.3.9]. -/
theorem isDiagonalizable_of_injective_of_forall_mem_spectrum {A : Matrix n n K} {d : n → K}
    (hd : Function.Injective d) (h : ∀ j, d j ∈ spectrum K A) : IsDiagonalizable A := by
  choose v hv hAv using fun j => exists_mulVec_eq_smul_of_mem_spectrum (h j)
  refine isDiagonalizable_iff_exists_linearIndependent.mpr ⟨v, d,
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) d hd v fun j =>
      ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv j⟩, hAv⟩
  rw [Matrix.toLin'_apply, hAv]

omit [Fintype n] [DecidableEq n] in
/-- A spanning set of vectors contains a linearly independent family indexed by $n$. -/
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

/-- A matrix is diagonalisable exactly when its eigenspaces span. -/
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

/-- A diagonalisable matrix is semisimple. -/
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

/-- Over an algebraically closed field a semisimple matrix is diagonalisable. -/
theorem isDiagonalizable_of_isSemisimple [IsAlgClosed K] {A : Matrix n n K}
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) : IsDiagonalizable A :=
  isDiagonalizable_iff_iSup_eigenspace_eq_top.mpr hA.iSup_eigenspace_eq_top

/-- Over an algebraically closed field, diagonalisable means semisimple. -/
theorem isDiagonalizable_iff_isSemisimple [IsAlgClosed K] {A : Matrix n n K} :
    IsDiagonalizable A ↔ Module.End.IsSemisimple (Matrix.toLin' A) :=
  ⟨IsDiagonalizable.isSemisimple, isDiagonalizable_of_isSemisimple⟩

/-- A diagonalisable matrix over any field has equal geometric and algebraic multiplicities:
$\dim E_\mu(\mathbf{A})$ equals the multiplicity of $\mu$ in its characteristic polynomial,
including scalars outside the spectrum. [HornJohnson2013, §§1.3–1.4]; the field is generalized.
Formal source: `tchen-research/NLAlib`, commit `77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib.IsDiagonalizable.finrank_eigenspace_eq_rootMultiplicity`. -/
theorem IsDiagonalizable.finrank_eigenspace_eq_rootMultiplicity
    {A : Matrix n n K} (hA : IsDiagonalizable A) (μ : K) :
    Module.finrank K (Module.End.eigenspace A.toLin' μ) =
      A.charpoly.rootMultiplicity μ := by
  have hm := LinearMap.finrank_maxGenEigenspace_eq A.toLin' μ
  have heq : Module.End.maxGenEigenspace A.toLin' μ = Module.End.eigenspace A.toLin' μ :=
    hA.isSemisimple.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  rw [heq] at hm
  simpa only [Matrix.charpoly_toLin'] using hm

/-- **Diagonalizability by multiplicities.** Over an algebraically closed field, a matrix
$\mathbf{A}$ is diagonalisable exactly when $\dim E_\mu(\mathbf{A})$ equals the multiplicity
of $\mu$ in its characteristic polynomial for every scalar $\mu$. Empty matrices and scalars
outside the spectrum are included. [HornJohnson2013, §§1.3–1.4]; generalized from complex scalars.
Formal source: `tchen-research/NLAlib`, commit `77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib.isDiagonalizable_iff_finrank_eigenspace_eq_rootMultiplicity`.
Result: diagonalizable-def -/
theorem isDiagonalizable_iff_forall_finrank_eigenspace_eq_rootMultiplicity
    [IsAlgClosed K] (A : Matrix n n K) :
    IsDiagonalizable A ↔ ∀ μ : K,
      Module.finrank K (Module.End.eigenspace A.toLin' μ) =
        A.charpoly.rootMultiplicity μ := by
  constructor
  · exact fun hA μ => hA.finrank_eigenspace_eq_rootMultiplicity μ
  · intro hmult
    have heq (μ : K) : Module.End.eigenspace A.toLin' μ =
        Module.End.maxGenEigenspace A.toLin' μ := by
      apply Submodule.eq_of_le_of_finrank_eq Module.End.eigenspace_le_maxGenEigenspace
      rw [hmult μ, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']
    apply isDiagonalizable_iff_iSup_eigenspace_eq_top.mpr
    simpa only [heq] using Module.End.iSup_maxGenEigenspace_eq_top A.toLin'

/-! ### Geometric multiplicity under principal compression -/

/-- Removing coordinates from any matrix decreases the geometric multiplicity of each scalar
by at most the number removed. For the retained set $s$ and any scalar $\mu$,
$$\lvert s\rvert+\dim E_\mu(\mathbf{A})\le
\lvert n\rvert+\dim E_\mu(\mathbf{A}_{s,s})\,.$$
No diagonalizability is required; empty sets and scalars outside the spectrum are included.
This strengthens the survival conclusion in [HornJohnson2013, Theorem 1.4.10].
Formal source: `tchen-research/NLAlib`, commit `77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib.mem_spectrum_principal_submatrix_of_finrank_eigenspace_gt`; strengthened from survival
to a dimension bound using the same coordinate restriction. -/
theorem card_add_finrank_eigenspace_le (A : Matrix n n K) (μ : K) (s : Finset n) :
    s.card + Module.finrank K (Module.End.eigenspace A.toLin' μ) ≤
      Fintype.card n + Module.finrank K
        (Module.End.eigenspace
          (A.submatrix (fun j : s => j.val) (fun j : s => j.val)).toLin' μ) := by
  classical
  let E := Module.End.eigenspace A.toLin' μ
  let T : E →ₗ[K] ({j : n // j ∉ s} → K) :=
    { toFun x := fun j => x.val j.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let E' := Module.End.eigenspace
    (A.submatrix (fun j : s => j.val) (fun j : s => j.val)).toLin' μ
  let R : T.ker →ₗ[K] E' :=
    { toFun v := ⟨fun j => v.val.val j.val, by
        apply Module.End.mem_eigenspace_iff.mpr
        have heig : A *ᵥ v.val.val = μ • v.val.val :=
          Module.End.mem_eigenspace_iff.mp v.val.property
        funext i
        have hsum := Fintype.sum_subtype_add_sum_subtype (fun j : n => j ∈ s)
          (fun j => A i.val j * v.val.val j)
        have hzero : (∑ j : {j : n // j ∉ s}, A i.val j.val * v.val.val j.val) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          have hj : v.val.val j.val = 0 := congrFun v.property j
          rw [hj, mul_zero]
        rw [hzero, add_zero] at hsum
        change (∑ j : s, A i.val j.val * v.val.val j.val) = μ * v.val.val i.val
        convert! hsum.trans (congrFun heig i.val) using 1
        congr 1
        ext j
        simp only [Finset.mem_univ]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hR : Function.Injective R := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ s
    · exact congrArg (fun z : E' => z.val ⟨j, hj⟩) hxy
    · have hx : x.val.val j = 0 := congrFun x.property ⟨j, hj⟩
      have hy : y.val.val j = 0 := congrFun y.property ⟨j, hj⟩
      exact hx.trans hy.symm
  have hdimR := LinearMap.finrank_le_finrank_of_injective hR
  have hdimT := T.finrank_range_add_finrank_ker
  have hdimRange := (T.range).finrank_le
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_coe] at hdimRange
  have hcard := s.card_le_univ
  change s.card + Module.finrank K E ≤ Fintype.card n + Module.finrank K E'
  omega

/-- **Principal-submatrix eigenvalue survival.** Over any field, if the geometric multiplicity
of $\mu$ for $\mathbf{A}$ exceeds the number of deleted coordinates, then $\mu$ remains an
eigenvalue of $\mathbf{A}_{s,s}$. The matrix need not be diagonalisable.
[HornJohnson2013, Theorem 1.4.10]; generalized to arbitrary fields and finite index types.
Formal source: `tchen-research/NLAlib`, commit `77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib.mem_spectrum_principal_submatrix_of_finrank_eigenspace_gt`; the additive dimension
condition avoids truncated subtraction.
Result: principal-submatrix-eigenvalue-survival -/
theorem mem_spectrum_submatrix_of_card_lt_add_finrank_eigenspace
    (A : Matrix n n K) (μ : K) (s : Finset n)
    (h : Fintype.card n < s.card + Module.finrank K (Module.End.eigenspace A.toLin' μ)) :
    μ ∈ spectrum K (A.submatrix (fun j : s => j.val) (fun j : s => j.val)) := by
  have hdim := card_add_finrank_eigenspace_le A μ s
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum,
    Module.End.hasEigenvalue_iff]
  apply Submodule.one_le_finrank_iff.mp
  omega

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

/-- A block diagonal matrix
$\begin{bmatrix} \mathbf{A} & \mathbf{0} \\ \mathbf{0} & \mathbf{B} \end{bmatrix}$ is
diagonalisable exactly when its blocks $\mathbf{A}$ and $\mathbf{B}$ are. -/
theorem isDiagonalizable_fromBlocks_zero₁₂_zero₂₁_iff {A : Matrix m m K} {B : Matrix n n K} :
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

/-- A Hermitian matrix is diagonalisable. -/
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

/-- **A commuting family of diagonalisable matrices is simultaneously diagonalisable**: if the
$\mathbf{A}_i$ are diagonalisable and commute pairwise, there is one invertible $\mathbf{V}$ with
$\mathbf{A}_i\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d}_i)$ for every $i$.
[HornJohnson2013, Theorem 1.3.21]. -/
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

/-- Simultaneously diagonalisable matrices commute: if $\mathbf{V}$ is invertible,
$\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{a})$ and
$\mathbf{B}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{b})$, then
$\mathbf{A}\mathbf{B} = \mathbf{B}\mathbf{A}$. -/
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

/-! ### Coordinates in an eigenvector basis -/

/-- Expressing an eigenvector family in an eigenvector basis intertwines the two diagonal
eigenvalue matrices: if $\mathbf{A}\mathbf{V}=\mathbf{V}\operatorname{diag}(\mathbf{d})$,
$\mathbf{A}\mathbf{W}=\mathbf{W}\operatorname{diag}(\mathbf{e})$, and $\mathbf{V}$ is invertible,
then $\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}\mathbf{W}=
\mathbf{V}^{-1}\mathbf{W}\operatorname{diag}(\mathbf{e})$. The family $\mathbf{W}$ may be
rectangular or dependent, and its listing need not agree with $\mathbf{d}$.
[HornJohnson2013, Theorem 1.3.27]; generalized from two aligned eigenvector bases.
Formal source: `tchen-research/NLAlib`, commit `77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib.diagonal_mul_change_eigenbasis_eq_change_eigenbasis_mul_diagonal`. -/
theorem diagonal_mul_inv_mul_eq_inv_mul_diagonal
    {A V : Matrix n n K} {W : Matrix n m K} {d : n → K} {e : m → K}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    (hAW : A * W = W * Matrix.diagonal e) :
    Matrix.diagonal d * (V⁻¹ * W) = (V⁻¹ * W) * Matrix.diagonal e := by
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  apply Matrix.mul_right_injective_of_inv V⁻¹ V (Matrix.nonsing_inv_mul V hdet)
  change V * (Matrix.diagonal d * (V⁻¹ * W)) = V * ((V⁻¹ * W) * Matrix.diagonal e)
  rw [← Matrix.mul_assoc V (Matrix.diagonal d), ← hAV,
    Matrix.mul_assoc A V, ← Matrix.mul_assoc V V⁻¹,
    Matrix.mul_nonsing_inv V hdet, Matrix.one_mul,
    ← Matrix.mul_assoc V, ← Matrix.mul_assoc V V⁻¹,
    Matrix.mul_nonsing_inv V hdet, Matrix.one_mul]
  exact hAW

/-- Coordinates of an eigenvector in an eigenvector basis vanish at different eigenvalues.
If $\mathbf{A}\mathbf{V}=\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
$\mathbf{A}\mathbf{W}=\mathbf{W}\operatorname{diag}(\mathbf{e})$, and $d_i\ne e_j$, then
$(\mathbf{V}^{-1}\mathbf{W})_{i,j}=0$. The matrix $\mathbf{W}$ may be rectangular or dependent.
[HornJohnson2013, Theorem 1.3.27]; generalized from two aligned eigenvector bases.
Formal source: `tchen-research/NLAlib`, commit `77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib.change_eigenbasis_apply_eq_zero_of_eigenvalues_ne`. -/
theorem inv_mul_apply_eq_zero_of_ne
    {A V : Matrix n n K} {W : Matrix n m K} {d : n → K} {e : m → K}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    (hAW : A * W = W * Matrix.diagonal e) {i : n} {j : m} (hij : d i ≠ e j) :
    (V⁻¹ * W) i j = 0 := by
  have h := congrArg (fun M : Matrix n m K => M i j)
    (diagonal_mul_inv_mul_eq_inv_mul_diagonal hV hAV hAW)
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  exact (mul_eq_zero.mp (by linear_combination h : (d i - e j) * (V⁻¹ * W) i j = 0)).resolve_left
    (sub_ne_zero.mpr hij)

/-! ### Polynomials of a diagonalised matrix -/

section Polynomial

variable {H V : Matrix n n ℂ} {d : n → ℂ}

/-- Powers of a diagonalised matrix: for invertible $\mathbf{V}$,
$(\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1})^e =
\mathbf{V}\operatorname{diag}(\mathbf{g}^e)\mathbf{V}^{-1}$. -/
theorem mul_diagonal_mul_inv_pow (hV : IsUnit V) (g : n → ℂ) (e : ℕ) :
    (V * Matrix.diagonal g * V⁻¹) ^ e = V * Matrix.diagonal (g ^ e) * V⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  induction e with
  | zero => rw [pow_zero, pow_zero, Pi.one_def, Matrix.diagonal_one, mul_one,
      Matrix.mul_nonsing_inv V hdet]
  | succ e ih =>
    rw [pow_succ, ih]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
    rw [← Matrix.mul_assoc (Matrix.diagonal (g ^ e)), Matrix.diagonal_mul_diagonal, pow_succ]
    rfl

/-- A polynomial of a diagonalised matrix: if $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible, then for every
polynomial $p$, $p(\mathbf{H}) = \mathbf{V}\operatorname{diag}(p(\mathbf{d}_i))\mathbf{V}^{-1}$. -/
theorem aeval_eq_mul_diagonal_mul_inv (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (p : Polynomial ℂ) :
    Polynomial.aeval H p = V * Matrix.diagonal (fun i => p.eval (d i)) * V⁻¹ := by
  have hH : H = V * Matrix.diagonal d * V⁻¹ := by
    rw [← hHV, Matrix.mul_assoc, Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hV),
      Matrix.mul_one]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq, Polynomial.eval_add, ← Matrix.diagonal_add, Matrix.mul_add,
      Matrix.add_mul]
  | monomial e a =>
    have hf : (fun i => (Polynomial.monomial e a).eval (d i)) = a • (d ^ e) := by
      funext i; simp [Polynomial.eval_monomial]
    rw [Polynomial.aeval_monomial, hH, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul,
      mul_diagonal_mul_inv_pow hV, hf, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The inverse of a polynomial of a diagonalised matrix: if $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and $p(\mathbf{d}_i) \ne
0$ for all $i$, then $p(\mathbf{H})^{-1} = \mathbf{V}\operatorname{diag}(p(\mathbf{d}_i)^{-1})
\mathbf{V}^{-1}$. -/
theorem inv_aeval_eq_mul_diagonal_mul_inv (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    {p : Polynomial ℂ} (hp : ∀ i, p.eval (d i) ≠ 0) :
    (Polynomial.aeval H p)⁻¹ = V * Matrix.diagonal (fun i => (p.eval (d i))⁻¹) * V⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  rw [aeval_eq_mul_diagonal_mul_inv hV hHV p]
  apply Matrix.inv_eq_left_inv
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
  rw [← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal,
    show (fun i => (p.eval (d i))⁻¹ * p.eval (d i)) = 1 from funext fun i => inv_mul_cancel₀ (hp i),
    Pi.one_def, Matrix.diagonal_one, Matrix.one_mul, Matrix.mul_nonsing_inv V hdet]

/-- A polynomial of a diagonalised matrix that vanishes at no eigenvalue is invertible. -/
theorem isUnit_aeval_of_forall_eval_ne_zero (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    {p : Polynomial ℂ} (hp : ∀ i, p.eval (d i) ≠ 0) : IsUnit (Polynomial.aeval H p) := by
  rw [aeval_eq_mul_diagonal_mul_inv hV hHV p]
  exact (hV.mul (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i =>
    isUnit_iff_ne_zero.mpr (hp i)))).mul (Matrix.isUnit_nonsing_inv_iff.mpr hV)

/-- The negative powers of a shifted diagonalised matrix: if $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and no $\mathbf{d}_i$
equals $s$, then $(\mathbf{H} - s\mathbf{I})^{-k} =
\mathbf{V}\operatorname{diag}((\mathbf{d}_i - s)^{-k})\mathbf{V}^{-1}$. -/
theorem inv_sub_smul_one_pow_eq_mul_diagonal_mul_inv (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) {s : ℂ} (hs : ∀ i, d i ≠ s) (k : ℕ) :
    (H - s • (1 : Matrix n n ℂ))⁻¹ ^ k = V * Matrix.diagonal (fun i => (d i - s)⁻¹ ^ k) * V⁻¹ := by
  have h := inv_aeval_eq_mul_diagonal_mul_inv hV hHV (p := Polynomial.X - Polynomial.C s)
    fun i => by simpa [sub_eq_zero] using hs i
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  rw [h, mul_diagonal_mul_inv_pow hV]
  rfl

/-- An eigenvalue of a diagonalised matrix: if $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible, then
$\det(\mathbf{H} - \mathbf{d}_i\mathbf{I}) = 0$. -/
theorem det_sub_smul_one_eq_zero_of_mul_eq_mul_diagonal (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (i : n) : (H - d i • (1 : Matrix n n ℂ)).det = 0 := by
  have h := aeval_eq_mul_diagonal_mul_inv hV hHV (Polynomial.X - Polynomial.C (d i))
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _), mul_zero, zero_mul]

/-- A shift that is no eigenvalue of a diagonalised matrix: if $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and no $\mathbf{d}_i$
equals $s$, then $\det(\mathbf{H} - s\mathbf{I}) \ne 0$. -/
theorem det_sub_smul_one_ne_zero_of_forall_ne (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) {s : ℂ} (hs : ∀ i, d i ≠ s) :
    (H - s • (1 : Matrix n n ℂ)).det ≠ 0 := by
  have h := isUnit_aeval_of_forall_eval_ne_zero hV hHV (p := Polynomial.X - Polynomial.C s)
    fun i => by simpa [sub_eq_zero] using hs i
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one] at h
  exact ((Matrix.isUnit_iff_isUnit_det _).mp h).ne_zero

/-- An eigenvalue of a diagonalised matrix is at most the norm: if $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible, then
$\lvert\mathbf{d}_i\rvert \le \|\mathbf{H}\|_2$. -/
theorem norm_le_specNorm_of_mul_eq_mul_diagonal (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (i : n) : ‖d i‖ ≤ specNorm H := by
  set x := V *ᵥ Pi.single i 1
  have hx : H *ᵥ x = d i • x := by
    rw [Matrix.mulVec_mulVec, hHV, ← Matrix.mulVec_mulVec, Matrix.mulVec_single,
      Matrix.mulVec_smul]
    simp [x]
  have hx0 : WithLp.toLp 2 x ≠ 0 := fun h0 => by
    have := congrFun (Matrix.mulVec_injective_iff_isUnit.mpr hV
      (show x = V *ᵥ 0 by rw [Matrix.mulVec_zero]; exact congrArg WithLp.ofLp h0)) i
    simp at this
  have h := norm_toLp_mulVec_le H x
  rw [hx, WithLp.toLp_smul, norm_smul] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hx0)

/-- **A normal matrix has a perfectly conditioned eigenvector matrix**: a normal complex matrix
$\mathbf{H}$, $n$ nonempty, has $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$
with $\mathbf{V}$ unitary, so $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 = 1$.
[HornJohnson2013, Theorem 2.5.3], the spectral theorem for normal matrices. -/
theorem _root_.IsStarNormal.exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_eq_one
    [Nonempty n] {H : Matrix n n ℂ} (hH : IsStarNormal H) :
    ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧ H * V = V * Matrix.diagonal d ∧
      pseudoConditionNumber V = 1 := by
  obtain ⟨U, d, hU, rfl⟩ := isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose.mp hH
  refine ⟨U, d, hU.isUnit, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
  · rw [pseudoConditionNumber_of_isUnit hU.isUnit,
      Matrix.inv_eq_left_inv hU.conjTranspose_mul_self, specNorm_conjTranspose,
      hU.specNorm_eq_one, mul_one]

end Polynomial

end NLAlib
