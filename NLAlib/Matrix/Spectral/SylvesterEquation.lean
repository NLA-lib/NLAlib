/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import NLAlib.Matrix.Spectral.EigenvectorPairing

/-!
# The Sylvester equation

The Sylvester equation $\mathbf{A}\mathbf{X} - \mathbf{X}\mathbf{B} = \mathbf{C}$, for square
$\mathbf{A}$ and $\mathbf{B}$ of possibly different sizes over a field, has exactly one solution
$\mathbf{X}$ when the characteristic polynomials of $\mathbf{A}$ and $\mathbf{B}$ are coprime;
over an algebraically closed field this says that $\mathbf{A}$ and $\mathbf{B}$ have no common
eigenvalue. A block upper triangular matrix whose diagonal blocks satisfy this condition is
therefore similar to its block diagonal part.

## Main results

* `NLAlib.eq_zero_of_mul_eq_mul_of_isCoprime_charpoly`: only $\mathbf{X} = \mathbf{0}$
  intertwines $\mathbf{A}$ and $\mathbf{B}$.
* `NLAlib.existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly`: the Sylvester equation.
* `NLAlib.isCoprime_charpoly_iff_disjoint_spectrum`: coprimality as disjoint spectra.
* `NLAlib.exists_fromBlocks_mul_eq_mul_fromBlocks`: block diagonalisation.
* `NLAlib.forall_existsUnique_mul_sub_mul_eq_iff_disjoint_spectrum`: the converse criterion.
* `NLAlib.isCoprime_charpoly_iff_disjoint_spectrum_complexify`: complex spectral separation
  for real or complex matrices.
* `NLAlib.blockDiagonal'_mul_eq_mul_blockDiagonal'_iff_of_isCoprime_charpoly`: intertwiners
  between block diagonal matrices.
* `NLAlib.commute_blockDiagonal'_iff_of_isCoprime_charpoly`: block commutants.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- An intertwining relation $\mathbf{A}\mathbf{Y} = \mathbf{Y}\mathbf{B}$ passes to polynomials
in $\mathbf{A}$ and $\mathbf{B}$: $p(\mathbf{A})\mathbf{Y} = \mathbf{Y}p(\mathbf{B})$. -/
private theorem aeval_mul_eq_mul_aeval {A : Matrix m m K} {B : Matrix n n K} {Y : Matrix m n K}
    (hY : A * Y = Y * B) (p : K[X]) : aeval A p * Y = Y * aeval B p := by
  have hpow : ∀ k : ℕ, A ^ k * Y = Y * B ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
    | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, hY, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
      Matrix.smul_mul, Matrix.mul_smul, hpow]

/-- If the characteristic polynomials of $\mathbf{A}$ and $\mathbf{B}$ are coprime, only
$\mathbf{X} = \mathbf{0}$ satisfies $\mathbf{A}\mathbf{X} = \mathbf{X}\mathbf{B}$. -/
theorem eq_zero_of_mul_eq_mul_of_isCoprime_charpoly {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) {X : Matrix m n K} (hX : A * X = X * B) : X = 0 := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (aeval A) huv
  rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, zero_add, map_one] at h1
  have h2 := aeval_mul_eq_mul_aeval hX B.charpoly
  rw [Matrix.aeval_self_charpoly, Matrix.mul_zero] at h2
  rw [← Matrix.one_mul X, ← h1, Matrix.mul_assoc, h2, Matrix.mul_zero]

/-- **The Sylvester equation $\mathbf{A}\mathbf{X} - \mathbf{X}\mathbf{B} = \mathbf{C}$ has a
unique solution** when the characteristic polynomials of $\mathbf{A}$ and $\mathbf{B}$ are
coprime. [HornJohnson2013, Theorem 2.4.4.1].
Result: sylvester-equation -/
theorem existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly (A : Matrix m m K) (B : Matrix n n K)
    (h : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C := by
  let T : Matrix m n K →ₗ[K] Matrix m n K :=
    { toFun Y := A * Y - Y * B
      map_add' Y Z := by rw [Matrix.mul_add, Matrix.add_mul, add_sub_add_comm]
      map_smul' c Y := by rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    exact eq_zero_of_mul_eq_mul_of_isCoprime_charpoly h (sub_eq_zero.mp hY)
  obtain ⟨Y, hY⟩ := LinearMap.injective_iff_surjective.mp hinj C
  exact ⟨Y, hY, fun Z hZ => hinj (hZ.trans hY.symm)⟩

/-- Over an algebraically closed field the characteristic polynomials are coprime exactly when
the spectra are disjoint. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum [IsAlgClosed K] (A : Matrix m m K)
    (B : Matrix n n K) :
    IsCoprime A.charpoly B.charpoly ↔ Disjoint (spectrum K A) (spectrum K B) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K A.charpoly B.charpoly,
    Set.disjoint_left]
  refine forall_congr' fun a => ?_
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    IsRoot.def, IsRoot.def, coe_aeval_eq_eval]
  tauto

/-- Over an algebraically closed field, $\mathbf{A}\mathbf{X}=\mathbf{X}\mathbf{B}$ has only
the zero solution exactly when the spectra of $\mathbf{A}$ and $\mathbf{B}$ are disjoint.
The row and column index types may be empty. [HornJohnson2013, Theorem 2.4.4.1].
Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`sylvesterLinearMap_injective_iff_disjoint_spectrum`, through the equation interface. -/
theorem forall_eq_zero_iff_disjoint_spectrum [IsAlgClosed K]
    (A : Matrix m m K) (B : Matrix n n K) :
    (∀ X : Matrix m n K, A * X = X * B → X = 0) ↔
      Disjoint (spectrum K A) (spectrum K B) := by
  constructor
  · intro h
    apply Set.disjoint_left.mpr
    intro μ hA hB
    obtain ⟨x, hx, hAx⟩ := exists_mulVec_eq_smul_of_mem_spectrum hA
    obtain ⟨y, hy, hyB⟩ := exists_vecMul_eq_smul_of_mem_spectrum hB
    have hXY : A * Matrix.vecMulVec x y = Matrix.vecMulVec x y * B := by
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hAx, hyB]
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
    have heq := congrArg (fun X : Matrix m n K => X i j) (h _ hXY)
    exact mul_ne_zero hi hj heq
  · intro h X hX
    exact eq_zero_of_mul_eq_mul_of_isCoprime_charpoly
      ((isCoprime_charpoly_iff_disjoint_spectrum A B).mpr h) hX

/-- **The Sylvester solvability criterion.** Over an algebraically closed field,
$\mathbf{A}\mathbf{X}-\mathbf{X}\mathbf{B}=\mathbf{C}$ has a unique solution for every
right-hand side $\mathbf{C}$ exactly when the spectra of $\mathbf{A}$ and $\mathbf{B}$ are
disjoint. The two matrix sizes may be different or zero.
[HornJohnson2013, Theorem 2.4.4.1].
Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`sylvesterLinearMap_bijective_iff_disjoint_spectrum`, through unique solvability.
Result: sylvester-equation -/
theorem forall_existsUnique_mul_sub_mul_eq_iff_disjoint_spectrum [IsAlgClosed K]
    (A : Matrix m m K) (B : Matrix n n K) :
    (∀ C : Matrix m n K, ∃! X : Matrix m n K, A * X - X * B = C) ↔
      Disjoint (spectrum K A) (spectrum K B) := by
  constructor
  · intro h
    apply (forall_eq_zero_iff_disjoint_spectrum A B).mp
    intro X hX
    obtain ⟨Y, _, hY⟩ := h 0
    have hzero : A * (0 : Matrix m n K) - (0 : Matrix m n K) * B = 0 := by
      rw [Matrix.mul_zero, Matrix.zero_mul, sub_self]
    exact (hY X (sub_eq_zero.mpr hX)).trans (hY 0 hzero).symm
  · intro h C
    exact existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly A B
      ((isCoprime_charpoly_iff_disjoint_spectrum A B).mpr h) C

/-- The characteristic polynomials of real or complex matrices are coprime exactly when
their complex spectra are disjoint. This transfers complex spectral separation to
`existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly` without duplicating the solver theorem.
Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`, the
transport step of `existsUnique_real_sylvester_of_disjoint_complex_spectrum`, over `RCLike`. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum_complexify
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    IsCoprime A.charpoly B.charpoly ↔
      Disjoint (spectrum ℂ (complexify A)) (spectrum ℂ (complexify B)) := by
  rw [← isCoprime_charpoly_iff_disjoint_spectrum, charpoly_complexify,
    charpoly_complexify, Polynomial.isCoprime_map]

/-- **A block upper triangular matrix whose diagonal blocks have coprime characteristic
polynomials is similar to its block diagonal part**: there is $\mathbf{X}$ with
$$\begin{bmatrix} \mathbf{A} & \mathbf{C} \\ \mathbf{0} & \mathbf{B} \end{bmatrix}
  \begin{bmatrix} \mathbf{I} & \mathbf{X} \\ \mathbf{0} & \mathbf{I} \end{bmatrix} =
  \begin{bmatrix} \mathbf{I} & \mathbf{X} \\ \mathbf{0} & \mathbf{I} \end{bmatrix}
  \begin{bmatrix} \mathbf{A} & \mathbf{0} \\ \mathbf{0} & \mathbf{B} \end{bmatrix}.$$
[HornJohnson2013, Theorem 2.4.6.1 context]. -/
theorem exists_fromBlocks_mul_eq_mul_fromBlocks (A : Matrix m m K) (B : Matrix n n K)
    (h : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃ X : Matrix m n K,
      Matrix.fromBlocks A C 0 B * Matrix.fromBlocks 1 X 0 1 =
        Matrix.fromBlocks 1 X 0 1 * Matrix.fromBlocks A 0 0 B := by
  obtain ⟨Y, hY, -⟩ := existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly A B h (-C)
  refine ⟨Y, ?_⟩
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    Matrix.one_mul]
  rw [show A * Y + C = Y * B from by rw [sub_eq_iff_eq_add.mp hY]; abel]

/-! ### Intertwiners of block diagonal matrices -/

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {p q : ι → Type*} [∀ i, Fintype (p i)] [∀ i, DecidableEq (p i)]
  [∀ i, Fintype (q i)] [∀ i, DecidableEq (q i)]

/-- **Block intertwiners.** Suppose the characteristic polynomials of $\mathbf{A}_i$ and
$\mathbf{B}_j$ are coprime whenever $i\ne j$. A matrix intertwines the block diagonal
matrices with blocks $\mathbf{A}_i$ and $\mathbf{B}_i$ exactly when it is block diagonal
with matching blocks $\mathbf{X}_i$ satisfying
$\mathbf{A}_i\mathbf{X}_i=\mathbf{X}_i\mathbf{B}_i$.
The blocks $\mathbf{X}_i$ may be rectangular or empty, over any field.
[HornJohnson2013, Corollary 2.4.4.2]; generalized from spectral disjointness to coprimality.
Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`eq_blockDiagonal'_of_intertwines_of_disjoint_spectrum`, strengthened to an equivalence.
Result: sylvester-equation -/
theorem blockDiagonal'_mul_eq_mul_blockDiagonal'_iff_of_isCoprime_charpoly
    (A : ∀ i, Matrix (p i) (p i) K) (B : ∀ i, Matrix (q i) (q i) K)
    (h : ∀ i j, i ≠ j → IsCoprime (A i).charpoly (B j).charpoly)
    (X : Matrix (Σ i, p i) (Σ i, q i) K) :
    Matrix.blockDiagonal' A * X = X * Matrix.blockDiagonal' B ↔
      X = Matrix.blockDiagonal' (Matrix.blockDiag' X) ∧
        ∀ i, A i * Matrix.blockDiag' X i = Matrix.blockDiag' X i * B i := by
  constructor
  · intro hX
    have hleft (i j : ι) :
        (Matrix.blockDiagonal' A * X).submatrix (Sigma.mk i) (Sigma.mk j) =
          A i * X.submatrix (Sigma.mk i) (Sigma.mk j) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, ← Finset.univ_sigma_univ,
        Finset.sum_sigma]
      rw [Fintype.sum_eq_single i]
      · simp only [Matrix.blockDiagonal'_apply_eq]
      · intro k hki
        exact Finset.sum_eq_zero fun c _ => by
          rw [Matrix.blockDiagonal'_apply_ne A a c hki.symm, zero_mul]
    have hright (i j : ι) :
        (X * Matrix.blockDiagonal' B).submatrix (Sigma.mk i) (Sigma.mk j) =
          X.submatrix (Sigma.mk i) (Sigma.mk j) * B j := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, ← Finset.univ_sigma_univ,
        Finset.sum_sigma]
      rw [Fintype.sum_eq_single j]
      · simp only [Matrix.blockDiagonal'_apply_eq]
      · intro k hkj
        exact Finset.sum_eq_zero fun c _ => by
          rw [Matrix.blockDiagonal'_apply_ne B c b hkj, mul_zero]
    have hblock (i j : ι) : A i * X.submatrix (Sigma.mk i) (Sigma.mk j) =
        X.submatrix (Sigma.mk i) (Sigma.mk j) * B j := by
      have hh := congrArg (fun M : Matrix (Σ i, p i) (Σ i, q i) K =>
        M.submatrix (Sigma.mk i) (Sigma.mk j)) hX
      simpa only [hleft, hright] using hh
    refine ⟨?_, fun i => hblock i i⟩
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ a b hij]
      exact congrArg (fun M : Matrix (p i) (q j) K => M a b)
        (eq_zero_of_mul_eq_mul_of_isCoprime_charpoly (h i j hij) (hblock i j))
  · rintro ⟨hX, hblock⟩
    rw [hX, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext hblock)

/-- A matrix commutes with a block diagonal matrix whose block characteristic polynomials
are pairwise coprime exactly when it is block diagonal and its matching blocks commute.
Empty blocks and any field are allowed. [HornJohnson2013, Corollary 2.4.4.2]; the coprimality
form removes the need for an algebraically closed field.
Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`commute_blockDiagonal'_iff`, as a consequence of the rectangular characterization. -/
theorem commute_blockDiagonal'_iff_of_isCoprime_charpoly
    (A : ∀ i, Matrix (p i) (p i) K)
    (h : Pairwise fun i j => IsCoprime (A i).charpoly (A j).charpoly)
    (X : Matrix (Σ i, p i) (Σ i, p i) K) :
    Commute (Matrix.blockDiagonal' A) X ↔
      ∃ Y : ∀ i, Matrix (p i) (p i) K,
        X = Matrix.blockDiagonal' Y ∧ ∀ i, Commute (A i) (Y i) := by
  constructor
  · intro hX
    obtain ⟨hdiag, hcomm⟩ :=
      (blockDiagonal'_mul_eq_mul_blockDiagonal'_iff_of_isCoprime_charpoly
        A A (fun _ _ hij => h hij) X).mp hX.eq
    exact ⟨Matrix.blockDiag' X, hdiag, hcomm⟩
  · rintro ⟨Y, rfl, hY⟩
    change Matrix.blockDiagonal' A * Matrix.blockDiagonal' Y =
      Matrix.blockDiagonal' Y * Matrix.blockDiagonal' A
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext fun i => (hY i).eq)

end Blocks

end NLAlib
