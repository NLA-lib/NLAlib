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
* `IsStarNormal.apply_eq_zero_of_blockTriangular`: normal block triangular matrices are
  block diagonal.
* `IsStarNormal.conjTranspose_mul_mul`: normality is invariant under unitary similarity.
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

/-- Unitary similarity in both spellings:
$\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$ exactly when
$\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U} = \mathbf{D}$, for a unitary $\mathbf{U}$. -/
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

/-- The conjugate transpose of a unitary diagonalisation:
$(\mathbf{U} \operatorname{diag}(\mathbf{d}) \mathbf{U}^{\mathsf{H}})^{\mathsf{H}} =
\mathbf{U} \operatorname{diag}(\bar{\mathbf{d}}) \mathbf{U}^{\mathsf{H}}$. -/
private theorem conjTranspose_mul_diagonal_mul_conjTranspose (U : Matrix n n 𝕜) (d : n → 𝕜) :
    (U * Matrix.diagonal d * Uᴴ)ᴴ = U * Matrix.diagonal (star d) * Uᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]

/-- A unitarily diagonalisable matrix is normal: for unitary $\mathbf{U}$,
$\mathbf{U} \operatorname{diag}(\mathbf{d}) \mathbf{U}^{\mathsf{H}}$ is normal. -/
theorem HasOrthonormalCols.isStarNormal_mul_diagonal_mul_conjTranspose {U : Matrix n n 𝕜}
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

/-- Normality is invariant under unitary similarity: for normal $\mathbf{A}$ and unitary
$\mathbf{U}$, the matrix $\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U}$ is normal. -/
theorem _root_.IsStarNormal.conjTranspose_mul_mul {A : Matrix n n 𝕜} (hA : IsStarNormal A)
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : IsStarNormal (Uᴴ * A * U) := by
  have h : Aᴴ * A = A * Aᴴ := hA.star_comm_self
  refine ⟨?_⟩
  rw [Commute, SemiconjBy, Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ, ← Matrix.mul_assoc U Uᴴ, hU.mul_conjTranspose_self,
    Matrix.one_mul, Matrix.one_mul, ← Matrix.mul_assoc Aᴴ, h, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- A normal upper triangular matrix is diagonal. [HornJohnson2013, Lemma 2.5.2]. -/
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

/-- A unitary matrix that triangularises a normal matrix diagonalises it: if
$\mathbf{T} = \mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U}$ is upper triangular, then
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\mathbf{T}_{i,i}) \mathbf{U}^{\mathsf{H}}$. -/
theorem _root_.IsStarNormal.eq_mul_diagonal_mul_conjTranspose_of_isUpperTriangular [LinearOrder n]
    {A U : Matrix n n 𝕜} (hA : IsStarNormal A) (hU : HasOrthonormalCols U)
    (hT : (Uᴴ * A * U).IsUpperTriangular) :
    A = U * Matrix.diagonal (fun i => (Uᴴ * A * U) i i) * Uᴴ := by
  have hD := (hA.conjTranspose_mul_mul hU).isDiag_of_isUpperTriangular hT
  refine hU.eq_mul_mul_conjTranspose_iff.mpr (Matrix.ext fun i j => ?_)
  by_cases hij : i = j
  · rw [hij, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, hD hij]

/-- **A normal matrix whose characteristic polynomial splits is unitarily diagonalisable**, with
its eigenvalues in any prescribed order: if $\mathbf{d}$ lists the eigenvalues of the normal
$\mathbf{A}$, then $\mathbf{A} = \mathbf{U} \operatorname{diag}(\mathbf{d}) \mathbf{U}^{\mathsf{H}}$
for a unitary $\mathbf{U}$. [HornJohnson2013, Theorem 2.5.3]. -/
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
unitarily diagonalisable,
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\mathbf{d}) \mathbf{U}^{\mathsf{H}}$ for a unitary
$\mathbf{U}$ and a complex $\mathbf{d}$. [HornJohnson2013, Theorem 2.5.3].
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
    exact HasOrthonormalCols.isStarNormal_mul_diagonal_mul_conjTranspose hU d

omit [DecidableEq m] [DecidableEq n] in
open scoped ComplexOrder in
/-- A normal block upper triangular matrix is block diagonal: if
$\begin{bmatrix} \mathbf{A} & \mathbf{C} \\ \mathbf{0} & \mathbf{B} \end{bmatrix}$ is normal then
$\mathbf{C} = \mathbf{0}$. -/
theorem eq_zero_of_isStarNormal_fromBlocks {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    {C : Matrix m n 𝕜} (h : IsStarNormal (Matrix.fromBlocks A C 0 B)) : C = 0 := by
  have h1 := h.star_comm_self
  rw [Commute, SemiconjBy, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h1
  have h11 := congrArg Matrix.trace h1.1
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero, Matrix.trace_add] at h11
  rw [Matrix.trace_mul_comm Aᴴ A, left_eq_add] at h11
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp h11

/-- For a normal matrix, if the columns indexed by a finset `F` vanish outside `F`, then so do the
rows indexed by `F`: compare the diagonal entries of $\mathbf{N}^{\mathsf H}\mathbf{N} =
\mathbf{N}\mathbf{N}^{\mathsf H}$ summed over `F`. -/
private lemma rowSpill_eq_zero {m : Type*} [Fintype m] {N : Matrix m m 𝕜}
    (hN : IsStarNormal N) (F : Finset m) (hcol : ∀ x ∈ F, ∀ k ∉ F, N k x = 0) {x k : m}
    (hx : x ∈ F) (hk : k ∉ F) : N x k = 0 := by
  classical
  have hdiag : ∀ y, ∑ l, star (N l y) * N l y = ∑ l, N y l * star (N y l) := fun y => by
    have h := congrFun (congrFun hN.star_comm_self y) y
    simpa [Matrix.mul_apply, Matrix.star_apply] using h
  have hA : ∀ y ∈ F, ∑ l ∈ F, star (N l y) * N l y = ∑ l, star (N l y) * N l y := fun y hy =>
    Finset.sum_subset (Finset.subset_univ F) fun l _ hl => by simp [hcol y hy l hl]
  have key : ∑ y ∈ F, ∑ l ∈ Fᶜ, N y l * star (N y l) = 0 := by
    have h5 : ∀ y ∈ F, ∑ l ∈ Fᶜ, N y l * star (N y l) =
        (∑ l, N y l * star (N y l)) - ∑ l ∈ F, N y l * star (N y l) := fun y _ => by
      rw [eq_sub_iff_add_eq, add_comm]
      exact Finset.sum_add_sum_compl F _
    have h1 : ∑ y ∈ F, ∑ l ∈ F, N y l * star (N y l) =
        ∑ y ∈ F, ∑ l ∈ F, star (N l y) * N l y := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun l _ => mul_comm _ _
    have h2 : ∑ y ∈ F, ∑ l, N y l * star (N y l) = ∑ y ∈ F, ∑ l ∈ F, star (N l y) * N l y := by
      rw [Finset.sum_congr rfl fun y _ => (hdiag y).symm]
      exact Finset.sum_congr rfl fun y hy => (hA y hy).symm
    rw [Finset.sum_congr rfl h5, Finset.sum_sub_distrib, h2, h1, sub_self]
  have hnn : ∀ y l : m, N y l * star (N y l) = ((‖N y l‖ ^ 2 : ℝ) : 𝕜) :=
    fun y l => by rw [RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]
  simp only [hnn] at key
  have key2 : ∑ y ∈ F, ∑ l ∈ Fᶜ, ‖N y l‖ ^ 2 = 0 := by
    have h := congrArg RCLike.re key
    simpa only [map_sum, RCLike.ofReal_re, map_zero] using h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun y _ =>
    Finset.sum_nonneg fun l _ => sq_nonneg ‖N y l‖).mp key2 x hx
  have hz2 := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => sq_nonneg ‖N x l‖).mp hz k
    (Finset.mem_compl.mpr hk)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz2)

/-- A normal block triangular matrix is block diagonal: if $\mathbf{N}$ is normal and block
upper triangular for the labels $b$, its entries between different blocks vanish. Compare the
Frobenius norms of the first block row and the first block column of
$\mathbf{N}^{\mathsf H}\mathbf{N} = \mathbf{N}\mathbf{N}^{\mathsf H}$ and induct on the labels; the
block form of `IsStarNormal.isDiag_of_isUpperTriangular`. -/
theorem _root_.IsStarNormal.apply_eq_zero_of_blockTriangular {m α : Type*} [Fintype m]
    [LinearOrder α] {N : Matrix m m 𝕜} (hN : IsStarNormal N) {b : m → α}
    (hb : N.BlockTriangular b) {i j : m} (hij : b i ≠ b j) : N i j = 0 := by
  classical
  rcases lt_or_gt_of_ne hij with h | h
  · refine rowSpill_eq_zero hN (Finset.univ.filter fun k => b k ≤ b i) ?_
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩) ?_
    · intro x hx k hk
      have hk' : b i < b k :=
        not_le.mp fun h' => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
      exact hb ((Finset.mem_filter.mp hx).2.trans_lt hk')
    · exact fun hj => absurd (Finset.mem_filter.mp hj).2 (not_le.mpr h)
  · exact hb h

/-- A normal matrix with listed eigenvalues $\mathbf{d}$ is Hermitian exactly when the
$\mathbf{d}_i$ are real. -/
theorem _root_.IsStarNormal.isHermitian_iff_forall_im_eq_zero {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) {ι : Type*} [Fintype ι] {d : ι → 𝕜} (hd : IsEigenvalueListing A d) :
    A.IsHermitian ↔ ∀ i, RCLike.im (d i) = 0 := by
  obtain ⟨e⟩ : Nonempty (n ≃ ι) := ⟨Fintype.equivOfCardEq hd.card_eq.symm⟩
  obtain ⟨U, hU, rfl⟩ :=
    hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing (hd.comp_equiv e)
  rw [Matrix.IsHermitian, conjTranspose_mul_diagonal_mul_conjTranspose,
    mul_mul_conjTranspose_inj hU, Matrix.diagonal_eq_diagonal_iff]
  refine e.forall_congr fun i => ?_
  simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, RCLike.conj_eq_iff_im]

/-- A normal matrix with listed eigenvalues $\mathbf{d}$ is unitary exactly when the
$\mathbf{d}_i$ have modulus one. -/
theorem _root_.IsStarNormal.hasOrthonormalCols_iff_forall_norm_eq_one {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) {ι : Type*} [Fintype ι] {d : ι → 𝕜} (hd : IsEigenvalueListing A d) :
    HasOrthonormalCols A ↔ ∀ i, ‖d i‖ = 1 := by
  obtain ⟨e⟩ : Nonempty (n ≃ ι) := ⟨Fintype.equivOfCardEq hd.card_eq.symm⟩
  obtain ⟨U, hU, rfl⟩ :=
    hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing (hd.comp_equiv e)
  have h1 : (U * Matrix.diagonal (d ∘ e) * Uᴴ)ᴴ * (U * Matrix.diagonal (d ∘ e) * Uᴴ) =
      U * Matrix.diagonal (fun i => star (d (e i)) * d (e i)) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    rw [hU.conjTranspose_mul_cancel_left, ← Matrix.mul_assoc (Matrix.diagonal _)
      (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    rfl
  have h2 : (1 : Matrix n n 𝕜) = U * Matrix.diagonal (fun _ => 1) * Uᴴ := by
    rw [Matrix.diagonal_one, Matrix.mul_one, hU.mul_conjTranspose_self]
  rw [hasOrthonormalCols_iff, h1, h2, mul_mul_conjTranspose_inj hU, Matrix.diagonal_eq_diagonal_iff]
  refine e.forall_congr fun i => ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_one,
    RCLike.ofReal_inj, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

/-- The squared Frobenius norm of a normal matrix is the sum of the squared moduli of its
eigenvalues: $\|\mathbf{A}\|_{\mathsf{F}}^2 = \sum_i \lvert \mathbf{d}_i \rvert^2$ for a listing
$\mathbf{d}$. -/
theorem _root_.IsStarNormal.frobNorm_sq_eq_sum {A : Matrix n n 𝕜} (hA : IsStarNormal A)
    {ι : Type*} [Fintype ι] {d : ι → 𝕜} (hd : IsEigenvalueListing A d) :
    frobNorm A ^ 2 = ∑ i, ‖d i‖ ^ 2 :=
  (hd.sum_norm_sq_eq_frobNorm_sq_iff.mpr hA).symm

/-- The spectral norm of a normal matrix is the largest modulus of an eigenvalue: for a listing
$\mathbf{d}$ of the eigenvalues and $c \ge 0$, $\|\mathbf{A}\|_2 \le c$ exactly when
$\lvert \mathbf{d}_i \rvert \le c$ for every $i$. -/
theorem _root_.IsStarNormal.specNorm_le_iff {A : Matrix n n 𝕜} (hA : IsStarNormal A)
    {ι : Type*} [Fintype ι] {d : ι → 𝕜} (hd : IsEigenvalueListing A d) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ ∀ i, ‖d i‖ ≤ c := by
  obtain ⟨e⟩ : Nonempty (n ≃ ι) := ⟨Fintype.equivOfCardEq hd.card_eq.symm⟩
  obtain ⟨U, hU, rfl⟩ :=
    hA.exists_eq_mul_diagonal_mul_conjTranspose_of_isEigenvalueListing (hd.comp_equiv e)
  rw [hU.specNorm_mul_conjTranspose_right, hU.specNorm_mul_left, specNorm_diagonal,
    pi_norm_le_iff_of_nonneg hc]
  exact e.forall_congr fun i => Iff.rfl

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
/-- **The Fuglede–Putnam theorem**: for normal complex $\mathbf{A}$, $\mathbf{B}$,
$\mathbf{A}\mathbf{X} = \mathbf{X}\mathbf{B}$ exactly when
$\mathbf{A}^{\mathsf{H}}\mathbf{X} = \mathbf{X}\mathbf{B}^{\mathsf{H}}$.
[HornJohnson2013, Theorem 2.5.16]. -/
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

/-- Normal matrices are unitarily similar exactly when they have the same characteristic
polynomial: for normal complex $\mathbf{A}$, $\mathbf{B}$, there is a unitary $\mathbf{U}$ with
$\mathbf{B} = \mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}}$ if and only if
$\det(X\mathbf{I} - \mathbf{A}) = \det(X\mathbf{I} - \mathbf{B})$. -/
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
squared moduli of $\mathbf{U}^{\mathsf{H}}\mathbf{V}$. -/
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
can be matched so that the sum of squared distances is at most the squared Frobenius distance:
if $\mathbf{a}$ and $\mathbf{b}$ list the eigenvalues of $\mathbf{A}$ and $\mathbf{B}$, there is
a permutation $\pi$ with
$$\sum_i \lvert \mathbf{a}_i - \mathbf{b}_{\pi(i)} \rvert^2
  \le \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}^2.$$
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
