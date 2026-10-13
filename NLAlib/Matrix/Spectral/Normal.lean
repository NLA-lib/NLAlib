/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Schur
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import NLAlib.Matrix.Majorization.Schur

/-!
# Normal matrices

A square matrix is normal, Mathlib's `IsStarNormal A`, when it commutes with its conjugate
transpose. A complex matrix is normal exactly when it is unitarily diagonalisable. Normal upper
triangular matrices are diagonal; intertwining relations between normal matrices pass to the
conjugate transposes (Fuglede–Putnam); normal matrices with the same characteristic polynomial
are unitarily similar; and the eigenvalues of two normal matrices can be matched within the
Frobenius distance (Hoffman–Wielandt).

## Main results

* `NLAlib.isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose`: the spectral theorem.
* `IsStarNormal.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing`: with a prescribed
  order.
* `IsStarNormal.isDiag_of_isUpperTriangular`.
* `IsStarNormal.mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose`: Fuglede–Putnam.
* `IsStarNormal.exists_eq_mul_mul_conjTranspose_iff_charpoly_eq`: unitary similarity.
* `IsStarNormal.exists_perm_sum_norm_sub_sq_le_frobNorm_sq`: Hoffman–Wielandt.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### The spectral theorem -/

/-- Unitary similarity in both spellings: `A = U D Uᴴ` exactly when `Uᴴ A U = D`, for a unitary
`U`. -/
theorem HasOrthonormalCols.eq_mul_mul_conjTranspose_iff {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) {A D : Matrix n n 𝕜} : A = U * D * Uᴴ ↔ Uᴴ * A * U = D := by
  constructor
  · rintro rfl
    simp only [Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one,
      hU.conjTranspose_mul_cancel_left]
  · rintro rfl
    simp only [Matrix.mul_assoc, hU.mul_conjTranspose_self, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hU.mul_conjTranspose_self, Matrix.one_mul]

/-- A unitary similarity is injective. -/
private theorem mul_mul_conjTranspose_inj {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U)
    {D E : Matrix n n 𝕜} : U * D * Uᴴ = U * E * Uᴴ ↔ D = E := by
  rw [hU.eq_mul_mul_conjTranspose_iff, hU.eq_mul_mul_conjTranspose_iff.mp rfl]

/-- The conjugate transpose of a unitary diagonalisation. -/
private theorem conjTranspose_mul_diagonal_mul_conjTranspose (U : Matrix n n 𝕜) (d : n → 𝕜) :
    (U * Matrix.diagonal d * Uᴴ)ᴴ = U * Matrix.diagonal (star d) * Uᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]

/-- A unitarily diagonalisable matrix is normal.
Port of `NLAlib.mul_conjTranspose_eq_conjTranspose_mul_of_unitary_diagonalization`. -/
theorem isStarNormal_mul_diagonal_mul_conjTranspose {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) (d : n → 𝕜) : IsStarNormal (U * Matrix.diagonal d * Uᴴ) := by
  refine ⟨?_⟩
  rw [Commute, SemiconjBy, Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  rw [hU.conjTranspose_mul_cancel_left, hU.conjTranspose_mul_cancel_left,
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  simp only [mul_comm]

/-- A unitary similarity of a normal matrix is normal. -/
private theorem isStarNormal_conjTranspose_mul_mul {U A : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) (hA : IsStarNormal A) : IsStarNormal (Uᴴ * A * U) := by
  have h : Aᴴ * A = A * Aᴴ := hA.star_comm_self
  refine ⟨?_⟩
  rw [Commute, SemiconjBy, Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ, ← Matrix.mul_assoc U Uᴴ, hU.mul_conjTranspose_self,
    Matrix.one_mul, Matrix.one_mul, ← Matrix.mul_assoc Aᴴ, h, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- A normal upper triangular matrix is diagonal. [HornJohnson2013, Lemma 2.5.2].
Port of `NLAlib.upper_fromBlocks_eq_diagonal_of_normal`, for a triangular matrix. -/
theorem _root_.IsStarNormal.isDiag_of_isUpperTriangular [LinearOrder n] {T : Matrix n n 𝕜}
    (hT : IsStarNormal T) (h : T.IsUpperTriangular) : T.IsDiag := by
  classical
  have heq := h.isEigenvalueListing_diag.sum_norm_sq_eq_frobNorm_sq_iff.mpr hT
  rw [frobNorm_sq_eq_sum] at heq
  intro i j hij
  have hle : ∀ i ∈ Finset.univ, ‖T i i‖ ^ 2 ≤ ∑ j, ‖T i j‖ ^ 2 := fun i _ =>
    Finset.single_le_sum (f := fun j => ‖T i j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h1 := (Finset.sum_eq_sum_iff_of_le hle).mp heq i (Finset.mem_univ i)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), left_eq_add] at h1
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖T i j‖).mp h1 j
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)

/-- A unitary matrix that triangularises a normal matrix diagonalises it. -/
theorem _root_.IsStarNormal.eq_mul_diagonal_mul_conjTranspose_of_isUpperTriangular [LinearOrder n]
    {A U : Matrix n n 𝕜} (hA : IsStarNormal A) (hU : HasOrthonormalCols U)
    (hT : (Uᴴ * A * U).IsUpperTriangular) :
    A = U * Matrix.diagonal (fun i => (Uᴴ * A * U) i i) * Uᴴ := by
  have hD := (isStarNormal_conjTranspose_mul_mul hU hA).isDiag_of_isUpperTriangular hT
  refine hU.eq_mul_mul_conjTranspose_iff.mpr (Matrix.ext fun i j => ?_)
  by_cases hij : i = j
  · rw [hij, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, hD hij]

/-- **A normal matrix whose characteristic polynomial splits is unitarily diagonalisable**, with
its eigenvalues in any prescribed order. [HornJohnson2013, Theorem 2.5.3].
Port of `NLAlib.exists_unitary_diagonalization_of_normal_with_charpoly`, there over `ℂ`. -/
theorem _root_.IsStarNormal.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing
    {A : Matrix n n 𝕜} (hA : IsStarNormal A) {d : n → 𝕜}
    (hd : IsEigenvalueListing A d) :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ A = U * Matrix.diagonal d * Uᴴ := by
  classical
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨U, hU, hT, hdiag⟩ := hd.exists_hasOrthonormalCols_isUpperTriangular
  refine ⟨U, hU, ?_⟩
  have h := hA.eq_mul_diagonal_mul_conjTranspose_of_isUpperTriangular hU hT
  rwa [funext hdiag] at h

/-- **The spectral theorem for normal matrices**: a complex matrix is normal exactly when it is
unitarily diagonalisable. [HornJohnson2013, Theorem 2.5.3].
Port of `NLAlib.normal_iff_exists_unitary_diagonalization`.
Result: normal-spectral-theorem -/
theorem isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose {A : Matrix n n ℂ} :
    IsStarNormal A ↔
      ∃ (U : Matrix n n ℂ) (d : n → ℂ), HasOrthonormalCols U ∧
        A = U * Matrix.diagonal d * Uᴴ := by
  refine ⟨fun hA => ?_, ?_⟩
  · obtain ⟨d, hd⟩ := exists_isEigenvalueListing A
    obtain ⟨U, hU, h⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing hd
    exact ⟨U, d, hU, h⟩
  · rintro ⟨U, d, hU, rfl⟩
    exact isStarNormal_mul_diagonal_mul_conjTranspose hU d

omit [DecidableEq m] [DecidableEq n] in
open scoped ComplexOrder in
/-- A normal block upper triangular matrix is block diagonal.
Port of `NLAlib.eq_zero_of_normal_upper_fromBlocks`, there over `ℂ`. -/
theorem eq_zero_of_isStarNormal_fromBlocks {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    {C : Matrix m n 𝕜} (h : IsStarNormal (Matrix.fromBlocks A C 0 B)) : C = 0 := by
  have h1 := h.star_comm_self
  rw [Commute, SemiconjBy, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h1
  have h11 := congrArg Matrix.trace h1.1
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero, Matrix.trace_add] at h11
  rw [Matrix.trace_mul_comm Aᴴ A, left_eq_add] at h11
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp h11

/-- A normal matrix with listed eigenvalues `d` is Hermitian exactly when the `d i` are real. -/
theorem _root_.IsStarNormal.isHermitian_iff_forall_im_eq_zero {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) {d : n → 𝕜} (hd : IsEigenvalueListing A d) :
    A.IsHermitian ↔ ∀ i, RCLike.im (d i) = 0 := by
  obtain ⟨U, hU, rfl⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing hd
  rw [Matrix.IsHermitian, conjTranspose_mul_diagonal_mul_conjTranspose,
    mul_mul_conjTranspose_inj hU, Matrix.diagonal_eq_diagonal_iff]
  simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_eq_iff_im]

/-- A normal matrix with listed eigenvalues `d` is unitary exactly when the `d i` have modulus
one. -/
theorem _root_.IsStarNormal.hasOrthonormalCols_iff_forall_norm_eq_one {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) {d : n → 𝕜} (hd : IsEigenvalueListing A d) :
    HasOrthonormalCols A ↔ ∀ i, ‖d i‖ = 1 := by
  obtain ⟨U, hU, rfl⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing hd
  have h1 : (U * Matrix.diagonal d * Uᴴ)ᴴ * (U * Matrix.diagonal d * Uᴴ) =
      U * Matrix.diagonal (fun i => star (d i) * d i) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    rw [hU.conjTranspose_mul_cancel_left, ← Matrix.mul_assoc (Matrix.diagonal _)
      (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    rfl
  have h2 : (1 : Matrix n n 𝕜) = U * Matrix.diagonal (fun _ => 1) * Uᴴ := by
    rw [Matrix.diagonal_one, Matrix.mul_one, hU.mul_conjTranspose_self]
  rw [hasOrthonormalCols_iff, h1, h2, mul_mul_conjTranspose_inj hU, Matrix.diagonal_eq_diagonal_iff]
  refine forall_congr' fun i => ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_one,
    RCLike.ofReal_inj, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

/-- The squared Frobenius norm of a normal matrix is the sum of the squared moduli of its
eigenvalues. Port of `NLAlib.frobSq_eq_sum_norm_sq_of_normal`. -/
theorem _root_.IsStarNormal.frobNorm_sq_eq_sum {A : Matrix n n 𝕜} (hA : IsStarNormal A)
    {ι : Type*} [Fintype ι] {d : ι → 𝕜} (hd : IsEigenvalueListing A d) :
    frobNorm A ^ 2 = ∑ i, ‖d i‖ ^ 2 :=
  (hd.sum_norm_sq_eq_frobNorm_sq_iff.mpr hA).symm

/-- The spectral norm of a normal matrix is the largest modulus of an eigenvalue. -/
theorem _root_.IsStarNormal.specNorm_le_iff {A : Matrix n n 𝕜} (hA : IsStarNormal A)
    {d : n → 𝕜} (hd : IsEigenvalueListing A d) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ ∀ i, ‖d i‖ ≤ c := by
  obtain ⟨U, hU, rfl⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing hd
  rw [hU.specNorm_mul_conjTranspose_right, hU.specNorm_mul_left, specNorm_diagonal,
    pi_norm_le_iff_of_nonneg hc]

/-! ### Intertwining and similarity -/

/-- An intertwining relation between unitarily diagonalised matrices, in the coordinates of the
diagonalisations. -/
private theorem mul_eq_mul_iff_forall_apply {U : Matrix m m 𝕜} {V : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (a : m → 𝕜) (b : n → 𝕜)
    (X : Matrix m n 𝕜) :
    U * Matrix.diagonal a * Uᴴ * X = X * (V * Matrix.diagonal b * Vᴴ) ↔
      ∀ i j, a i * (Uᴴ * X * V) i j = (Uᴴ * X * V) i j * b j := by
  have h1 : Uᴴ * (U * Matrix.diagonal a * Uᴴ * X) * V = Matrix.diagonal a * (Uᴴ * X * V) := by
    simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
  have h2 : Uᴴ * (X * (V * Matrix.diagonal b * Vᴴ)) * V = Uᴴ * X * V * Matrix.diagonal b := by
    simp only [Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one]
  constructor
  · intro h i j
    have h3 := congrFun (congrFun (h1.symm.trans ((congrArg (Uᴴ * · * V) h).trans h2)) i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at h3
  · intro h
    have h3 : Matrix.diagonal a * (Uᴴ * X * V) = Uᴴ * X * V * Matrix.diagonal b :=
      Matrix.ext fun i j => by rw [Matrix.diagonal_mul, Matrix.mul_diagonal, h]
    rw [← h1, ← h2] at h3
    have h4 := congrArg (U * · * Vᴴ) h3
    simp only [Matrix.mul_assoc, hV.mul_conjTranspose_self, Matrix.mul_one] at h4
    simp only [← Matrix.mul_assoc, hU.mul_conjTranspose_self, Matrix.one_mul] at h4
    simpa only [Matrix.mul_assoc] using h4

omit [DecidableEq m] [DecidableEq n] in
/-- **The Fuglede–Putnam theorem**: for normal `A`, `B`, `A X = X B` exactly when
`Aᴴ X = X Bᴴ`. [HornJohnson2013, Theorem 2.5.16].
Port of `NLAlib.mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose_of_normal_rectangular`. -/
theorem _root_.IsStarNormal.mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : IsStarNormal A) (hB : IsStarNormal B)
    {X : Matrix m n ℂ} : A * X = X * B ↔ Aᴴ * X = X * Bᴴ := by
  classical
  obtain ⟨U, a, hU, rfl⟩ := isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose.mp hA
  obtain ⟨V, b, hV, rfl⟩ := isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose.mp hB
  rw [conjTranspose_mul_diagonal_mul_conjTranspose, conjTranspose_mul_diagonal_mul_conjTranspose,
    mul_eq_mul_iff_forall_apply hU hV, mul_eq_mul_iff_forall_apply hU hV]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  by_cases hY : (Uᴴ * X * V) i j = 0
  · rw [hY, mul_zero, zero_mul, mul_zero, zero_mul]
  · rw [mul_comm (a i), mul_comm (star a i), mul_right_inj' hY, mul_right_inj' hY,
      Pi.star_apply, Pi.star_apply, star_inj]

/-- **Normal matrices are unitarily similar exactly when they have the same characteristic
polynomial.** Port of `NLAlib.exists_unitary_similarity_iff_charpoly_eq_of_normal`. -/
theorem _root_.IsStarNormal.exists_eq_mul_mul_conjTranspose_iff_charpoly_eq {A B : Matrix n n ℂ}
    (hA : IsStarNormal A) (hB : IsStarNormal B) :
    (∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧ B = U * A * Uᴴ) ↔ A.charpoly = B.charpoly := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.one_mul]
  · intro h
    obtain ⟨d, hd⟩ := exists_isEigenvalueListing A
    have hd' : IsEigenvalueListing B d := by rw [isEigenvalueListing_iff, ← h, hd]
    obtain ⟨U, hU, rfl⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing hd
    obtain ⟨V, hV, rfl⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing hd'
    refine ⟨V * Uᴴ, hV.mul hU.conjTranspose, ?_⟩
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      hU.conjTranspose_mul_cancel_left]

/-! ### Eigenvalue variation -/

/-- The Frobenius distance between two unitarily diagonalised matrices, through the matrix of
squared moduli of `Uᴴ V`. -/
private theorem frobNorm_sub_sq_eq_sum {U V : Matrix n n 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (a b : n → 𝕜) :
    frobNorm (U * Matrix.diagonal a * Uᴴ - V * Matrix.diagonal b * Vᴴ) ^ 2 =
      ∑ i, ∑ j, ‖(Uᴴ * V) i j‖ ^ 2 * ‖a i - b j‖ ^ 2 := by
  have h : Uᴴ * (U * Matrix.diagonal a * Uᴴ - V * Matrix.diagonal b * Vᴴ) * V =
      Matrix.diagonal a * (Uᴴ * V) - Uᴴ * V * Matrix.diagonal b := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left, hV.conjTranspose_mul_self,
      Matrix.mul_one]
  rw [← hU.conjTranspose.frobNorm_mul_left, ← hV.frobNorm_mul_right, h, frobNorm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (a i), ← mul_sub,
    norm_mul, mul_pow]

/-- **The Hoffman–Wielandt theorem for normal matrices.** The eigenvalues of two normal matrices
can be matched so that the sum of squared distances is at most `‖A - B‖_F²`.
[HornJohnson2013, Theorem 6.3.5]; [Bhatia1997, Theorem VI.4.1].
Result: hoffman-wielandt-normal -/
theorem _root_.IsStarNormal.exists_perm_sum_norm_sub_sq_le_frobNorm_sq {A B : Matrix n n 𝕜}
    (hA : IsStarNormal A) (hB : IsStarNormal B) {ι : Type*} [Fintype ι] {a b : ι → 𝕜}
    (ha : IsEigenvalueListing A a) (hb : IsEigenvalueListing B b) :
    ∃ σ : Equiv.Perm ι, ∑ i, ‖a i - b (σ i)‖ ^ 2 ≤ frobNorm (A - B) ^ 2 := by
  obtain ⟨e⟩ : Nonempty (n ≃ ι) := ⟨(Fintype.equivOfCardEq ha.card_eq).symm⟩
  obtain ⟨U, hU, rfl⟩ :=
    hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing (ha.comp_equiv e)
  obtain ⟨V, hV, rfl⟩ :=
    hB.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing (hb.comp_equiv e)
  obtain ⟨σ, hσ⟩ := exists_perm_sum_le_sum_mul_of_mem_doublyStochastic
    (Matrix.of fun i j => ‖a (e i) - b (e j)‖ ^ 2)
    (hU.conjTranspose.mul hV).norm_sq_mem_doublyStochastic
  refine ⟨(e.symm.trans σ).trans e, ?_⟩
  rw [frobNorm_sub_sq_eq_sum hU hV, ← e.sum_comp]
  simpa only [Matrix.of_apply, Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    using hσ

end NLAlib
