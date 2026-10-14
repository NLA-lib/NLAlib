/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import NLAlib.Matrix.Basic.Orthonormal

/-!
# Eigenvalues of Hermitian matrices

`NLAlib.eigenvalue A k` is the `k`-th largest eigenvalue of a Hermitian matrix `A`, counted with
multiplicity and indexed from `0`. It is a total function of the matrix and a natural number: it
is `0` when `k` is at least the size of `A`, and `0` when `A` is not Hermitian. The values are
sorted in non-increasing order on the valid range `k < Fintype.card n`.

This is the library's spelling of an eigenvalue. Mathlib's `Matrix.IsHermitian.eigenvalues₀`
(sorted, indexed by `Fin (Fintype.card n)`, taking the proof of Hermitian-ness as an argument) is
the definition underneath, and `Matrix.IsHermitian.eigenvalue_eq_eigenvalues₀` is the bridge.
Mathlib's `Matrix.IsHermitian.eigenvalues` is a different function: unsorted and indexed by `n`.

The largest eigenvalue is `eigenvalue A 0`. Statements never mention a chosen eigenvector
basis: a diagonalisation is an equation `A * U = U * Matrix.diagonal d` with
`HasOrthonormalCols U`.

## Reading and writing statements about `eigenvalue A k`

`eigenvalue` is a total function: it returns a number for every matrix and every natural number,
including inputs for which "the `k`-th eigenvalue" does not exist. There the value is `0`, a
*junk value*, in the way that `1 / 0 = 0` and `A⁻¹ = 0` for a singular `A` are in Mathlib. This
cannot make a false theorem provable, because Lean checks every proof against this definition.
What it does mean is that a statement is also a statement about the junk values, so the range of
the index has to be read, and written, with care.

**The example to remember.** `∃ k, -3 < eigenvalue A k` does not say that `A` has an eigenvalue
above `-3`. It holds for every matrix: take `k ≥ Fintype.card n`, where the value is `0`. The
statement that was meant is `∃ k < Fintype.card n, -3 < eigenvalue A k`.

* An index quantified by `∃` needs `k < Fintype.card n`, or the witness can be out of range.
* An index quantified by `∀` in a hypothesis needs it too. `∀ k, 0 < eigenvalue A k` is never
  satisfied, since the value is `0` out of range, so a theorem that assumes it says nothing.
* An index quantified by `∀` in a conclusion, or left free, makes a claim about the padding too.
  That is fine when the claim is true of `0`, and such statements are left unbounded on purpose.
  Compare `Matrix.IsHermitian.posSemidef_iff_eigenvalue_nonneg`,
  `A.PosSemidef ↔ ∀ k, 0 ≤ eigenvalue A k`, with `Matrix.IsHermitian.posDef_iff_eigenvalue_pos`,
  `A.PosDef ↔ ∀ k < Fintype.card n, 0 < eigenvalue A k`: the strict one must carry the bound.
* The same applies to a matrix that is not Hermitian, for which `eigenvalue A k = 0` for every
  `k`. Theorems carry `A.IsHermitian` where the value matters. Identities such as
  `NLAlib.eigenvalue_neg` hold for every matrix, because both sides are junk together.

`NLAlib.singularValues` is padded in the same way and is read by the same rules. The reasons for
this design, and what Mathlib does, are in `docs/design/Mathlib-deviations.md`, entry 1.

## Main definitions

* `NLAlib.eigenvalue`: the sorted, zero-padded eigenvalues of a Hermitian matrix.

## Main results

* `Matrix.IsHermitian.eigenvalue_eq_eigenvalues₀`: the bridge to Mathlib.
* `Matrix.IsHermitian.eigenvalue_le_eigenvalue`: the values are non-increasing.
* `Matrix.IsHermitian.exists_mul_eq_mul_diagonal`: a unitary diagonalisation with the eigenvalues
  in order.
* `Matrix.IsHermitian.exists_hasOrthonormalCols_eq_mul_diagonal_mul_conjTranspose`: a unitary
  diagonalisation indexed by the index type of the matrix.
* `NLAlib.eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose`: the eigenvalues are determined by
  any sorted unitary diagonalisation.
* `Matrix.IsHermitian.exists_norm_eq_one_and_mulVec_eq`: a unit eigenvector for each eigenvalue.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [Fintype r]

open Classical in
/-- The `k`-th largest **eigenvalue** of a Hermitian matrix, counted with multiplicity, indexed
from `0`. Non-increasing in `k` for `k < Fintype.card n`. The value is `0` for
`k ≥ Fintype.card n`, and `0` for every `k` when `A` is not Hermitian. Mathlib's
`Matrix.IsHermitian.eigenvalues₀` is the same sequence indexed by `Fin (Fintype.card n)`;
Mathlib's `Matrix.IsHermitian.eigenvalues` is unsorted.

The zeros are junk values: `∃ k, -3 < eigenvalue A k` is true of every matrix. Bound the index
(`k < Fintype.card n`) when quantifying over it; see the module docstring. -/
noncomputable def eigenvalue (A : Matrix n n 𝕜) (k : ℕ) : ℝ :=
  if h : A.IsHermitian ∧ k < Fintype.card n then h.1.eigenvalues₀ ⟨k, h.2⟩ else 0

/-- Beyond the size of the matrix the eigenvalue sequence is zero. -/
theorem eigenvalue_of_card_le (A : Matrix n n 𝕜) {k : ℕ} (hk : Fintype.card n ≤ k) :
    eigenvalue A k = 0 := by
  rw [eigenvalue, dif_neg fun h => absurd h.2 (Nat.not_lt.mpr hk)]

/-- The eigenvalue sequence of a matrix that is not Hermitian is zero. -/
theorem eigenvalue_of_not_isHermitian {A : Matrix n n 𝕜} (hA : ¬ A.IsHermitian) (k : ℕ) :
    eigenvalue A k = 0 := by
  rw [eigenvalue, dif_neg fun h => hA h.1]

/-- **Bridge to Mathlib.** On the valid range, `eigenvalue A` is Mathlib's sorted
`Matrix.IsHermitian.eigenvalues₀`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_eigenvalues₀ [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (i : Fin (Fintype.card n)) : eigenvalue A i = hA.eigenvalues₀ i := by
  rw [eigenvalue, dif_pos ⟨hA, i.isLt⟩]
  congr

/-- The eigenvalues of a Hermitian matrix are non-increasing on the valid range. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {i j : ℕ} (hij : i ≤ j) (hj : j < Fintype.card n) :
    eigenvalue A j ≤ eigenvalue A i := by
  classical
  have hj' : eigenvalue A j = hA.eigenvalues₀ ⟨j, hj⟩ := hA.eigenvalue_eq_eigenvalues₀ ⟨j, hj⟩
  have hi' : eigenvalue A i = hA.eigenvalues₀ ⟨i, hij.trans_lt hj⟩ :=
    hA.eigenvalue_eq_eigenvalues₀ ⟨i, hij.trans_lt hj⟩
  rw [hi', hj']
  exact hA.eigenvalues₀_antitone hij

/-- The eigenvalue sequence of a Hermitian matrix, restricted to the valid range
`Fin (Fintype.card n)`, is non-increasing. This is `Matrix.IsHermitian.eigenvalue_le_eigenvalue`
as an `Antitone` statement, the form `NLAlib.eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose`
and `NLAlib.eigenvalue_diagonal` take as a hypothesis. -/
theorem _root_.Matrix.IsHermitian.antitone_eigenvalue_coe {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : Antitone fun i : Fin (Fintype.card n) => eigenvalue A i :=
  fun _ b hab => hA.eigenvalue_le_eigenvalue hab b.isLt

/-- Mathlib's unsorted eigenvalues `hA.eigenvalues : n → ℝ` are a relabelling of the sorted
sequence. -/
theorem _root_.Matrix.IsHermitian.exists_equiv_eigenvalue_eq [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    ∃ e : n ≃ Fin (Fintype.card n), ∀ i, hA.eigenvalues i = eigenvalue A (e i) := by
  exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm,
    fun _ => (hA.eigenvalue_eq_eigenvalues₀ _).symm⟩

/-- Mathlib's eigenvector unitary of a Hermitian matrix has orthonormal columns. -/
theorem _root_.Matrix.IsHermitian.hasOrthonormalCols_eigenvectorUnitary [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    HasOrthonormalCols (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  exact hasOrthonormalCols_iff_mem_unitaryGroup.mpr hA.eigenvectorUnitary.2

/-! ### Diagonalisation -/

omit [Fintype n] in
/-- A matrix `U * diagonal d * Uᴴ` with real `d` is Hermitian. -/
private theorem isHermitian_mul_diagonal_mul_conjTranspose [DecidableEq r] (U : Matrix n r 𝕜)
    (d : r → ℝ) : (U * (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) * Uᴴ).IsHermitian := by
  refine Matrix.isHermitian_mul_mul_conjTranspose U ?_
  rw [Matrix.isHermitian_diagonal_iff]
  exact fun i => RCLike.conj_ofReal (d i)

/-- **Spectral theorem**, in the form of an invariance equation: a Hermitian matrix has a matrix
`U` of orthonormal eigenvectors, one column for each eigenvalue in order, with
`A * U = U * diagonal (eigenvalue A)`. The matrix `U` has as many columns as rows, so
`HasOrthonormalCols.mul_conjTranspose_self_of_card_eq` gives `U * Uᴴ = 1`.
[HornJohnson2013, Theorem 2.5.6]. Port of `NLAlib.mul_sortedEigenframe_eq_mul_diagonal`, there
for a chosen `sortedEigenframe`. -/
theorem _root_.Matrix.IsHermitian.exists_mul_eq_mul_diagonal {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    ∃ U : Matrix n (Fin (Fintype.card n)) 𝕜, HasOrthonormalCols U ∧
      A * U =
        U * Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜) := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hV := hA.hasOrthonormalCols_eigenvectorUnitary
  have hAV : A * (hA.eigenvectorUnitary : Matrix n n 𝕜) =
      (hA.eigenvectorUnitary : Matrix n n 𝕜) *
        Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    refine (congrArg (· * (hA.eigenvectorUnitary : Matrix n n 𝕜)) h).trans ?_
    rw [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  refine ⟨(hA.eigenvectorUnitary : Matrix n n 𝕜).submatrix id e,
    hV.submatrix (Equiv.refl n) e.injective, ?_⟩
  ext i j
  have h := congrFun (congrFun hAV i) (e j)
  rw [Matrix.mul_diagonal] at h ⊢
  rw [Matrix.submatrix_apply, hA.eigenvalue_eq_eigenvalues₀ j]
  refine Eq.trans h ?_
  simp only [Function.comp_apply, Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply, id]

/-- **Spectral theorem**: a Hermitian matrix is `U * diagonal (eigenvalue A) * Uᴴ` for a matrix
`U` with orthonormal columns indexed by `Fin (Fintype.card n)`.
[HornJohnson2013, Theorem 2.5.6].
Result: spectral-theorem-hermitian -/
theorem _root_.Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    ∃ U : Matrix n (Fin (Fintype.card n)) 𝕜, HasOrthonormalCols U ∧
      A = U * (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) *
        Uᴴ := by
  classical
  obtain ⟨U, hU, h⟩ := hA.exists_mul_eq_mul_diagonal
  refine ⟨U, hU, ?_⟩
  rw [← h, Matrix.mul_assoc, hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm,
    Matrix.mul_one]

/-- **Spectral theorem**, with the eigenvectors and the eigenvalues indexed by the index type of
the matrix: a Hermitian matrix is `U * diagonal d * Uᴴ` for a unitary `U` and a real `d`, in no
particular order. `Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose` is the form with
the sorted eigenvalues, indexed by `Fin (Fintype.card n)`. -/
theorem _root_.Matrix.IsHermitian.exists_hasOrthonormalCols_eq_mul_diagonal_mul_conjTranspose
    [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ (U : Matrix n n 𝕜) (d : n → ℝ), HasOrthonormalCols U ∧
      A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, hA.hasOrthonormalCols_eigenvectorUnitary, ?_⟩
  have h := hA.spectral_theorem
  rwa [Unitary.conjStarAlgAut_apply] at h

/-- For each valid index there is a unit eigenvector with that eigenvalue. -/
theorem _root_.Matrix.IsHermitian.exists_norm_eq_one_and_mulVec_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    ∃ u : n → 𝕜, ‖WithLp.toLp 2 u‖ = 1 ∧ A *ᵥ u = eigenvalue A k • u := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  refine ⟨hA.eigenvectorBasis (e ⟨k, hk⟩), ?_, ?_⟩
  · rw [WithLp.toLp_ofLp]
    exact hA.eigenvectorBasis.orthonormal.1 _
  · rw [hA.mulVec_eigenvectorBasis, hA.eigenvalue_eq_eigenvalues₀ ⟨k, hk⟩]
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]

/-- A real eigenvalue of a Hermitian matrix, witnessed by a nonzero eigenvector, occurs in the
eigenvalue sequence. -/
theorem _root_.Matrix.IsHermitian.exists_eigenvalue_eq_of_mulVec_eq_smul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {u : n → 𝕜} {c : ℝ} (hu : u ≠ 0) (h : A *ᵥ u = c • u) :
    ∃ k < Fintype.card n, eigenvalue A k = c := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hUU := hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  have hw : Uᴴ *ᵥ u ≠ 0 := by
    intro h0
    apply hu
    rw [← Matrix.one_mulVec u, ← hUU, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine ⟨i, i.isLt, ?_⟩
  have h1 : Uᴴ *ᵥ (A *ᵥ u) =
      (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) *ᵥ
        (Uᴴ *ᵥ u) := by
    conv_lhs => rw [hAU]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hU.conjTranspose_mul_self, Matrix.one_mul]
  rw [h, Matrix.mulVec_smul] at h1
  have h2 := congrFun h1 i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, RCLike.real_smul_eq_coe_mul] at h2
  exact (RCLike.ofReal_injective (mul_right_cancel₀ hi h2)).symm

/-- **The eigenvalues are determined by a sorted unitary diagonalisation.** If
`A = U * diagonal μ * Uᴴ` with `U` having orthonormal columns indexed by `Fin q`, `q` the size of
`A`, and `μ` non-increasing, then `μ` is the eigenvalue sequence of `A`.
Port of `NLAlib.eigenvalues₀_eq_of_eq_mul_diagonal_mul`. -/
theorem eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose {q : ℕ} {A : Matrix n n 𝕜}
    {U : Matrix n (Fin q) 𝕜} {μ : Fin q → ℝ} (hU : HasOrthonormalCols U)
    (hq : Fintype.card n = q) (hμ : Antitone μ)
    (hA : A = U * (Matrix.diagonal fun i => ((μ i : ℝ) : 𝕜)) * Uᴴ) (i : Fin q) :
    eigenvalue A i = μ i := by
  classical
  have hH : A.IsHermitian := hA ▸ isHermitian_mul_diagonal_mul_conjTranspose U μ
  have hc : A.charpoly = (Matrix.diagonal fun i => ((μ i : ℝ) : 𝕜)).charpoly := by
    rw [hA, Matrix.mul_assoc, Matrix.charpoly_mul_comm_of_le _ _
      (by rw [Fintype.card_fin, hq]), Fintype.card_fin, hq, Nat.sub_self, pow_zero, one_mul,
      Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
  have hsort := hH.sort_roots_charpoly_eq_eigenvalues₀
  rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hsort
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def, RCLike.ofReal_re] at hsort
  have hl : List.ofFn hH.eigenvalues₀ = List.ofFn μ := by
    rw [← hsort]
    simp_rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hμ.sortedGE_ofFn
  have hi : (i : ℕ) < Fintype.card n := hq ▸ i.isLt
  have h1 : eigenvalue A i = hH.eigenvalues₀ ⟨i, hi⟩ := hH.eigenvalue_eq_eigenvalues₀ ⟨i, hi⟩
  have h2 := congrArg (fun l : List ℝ => l.getD i 0) hl
  simp only [List.getD_eq_getElem?_getD, List.length_ofFn, hi, getElem?_pos, List.getElem_ofFn,
    Option.getD_some, Fin.is_lt, Fin.eta] at h2
  rw [h1]
  exact h2

/-- **The eigenvalues are determined by any unitary diagonalisation**, up to order. If
`A = U * diagonal d * Uᴴ` with `U` having orthonormal columns indexed by a type `r` with as many
elements as `A` has rows, then the entries of `d` are the eigenvalues of `A` in some order. -/
theorem exists_equiv_eq_eigenvalue_of_eq_mul_diagonal_mul_conjTranspose [DecidableEq r]
    {A : Matrix n n 𝕜} {U : Matrix n r 𝕜} {d : r → ℝ} (hU : HasOrthonormalCols U)
    (hr : Fintype.card n = Fintype.card r)
    (hA : A = U * (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) :
    ∃ e : r ≃ Fin (Fintype.card n), ∀ i, d i = eigenvalue A (e i) := by
  classical
  let e₀ : r ≃ Fin (Fintype.card n) := Fintype.equivFinOfCardEq hr.symm
  let f : Fin (Fintype.card n) → ℝ := fun i => -d (e₀.symm i)
  let g : Fin (Fintype.card n) ≃ r := (Tuple.sort f).trans e₀.symm
  have hμ : Antitone fun i => d (g i) := fun i j hij =>
    neg_le_neg_iff.mp (Tuple.monotone_sort f hij)
  have hU' : HasOrthonormalCols (U.submatrix id g) := hU.submatrix (Equiv.refl n) g.injective
  have hA' : A = U.submatrix id g * (Matrix.diagonal fun i => ((d (g i) : ℝ) : 𝕜)) *
      (U.submatrix id g)ᴴ := by
    have hd : (Matrix.diagonal fun i => ((d (g i) : ℝ) : 𝕜)) =
        (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)).submatrix g g :=
      (Matrix.submatrix_diagonal_equiv (fun i => ((d i : ℝ) : 𝕜)) g).symm
    rw [hA, Matrix.conjTranspose_submatrix, hd, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  refine ⟨g.symm, fun i => ?_⟩
  rw [eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU' rfl hμ hA' (g.symm i),
    Equiv.apply_symm_apply]

/-! ### Spectrum -/

/-- Each eigenvalue of a Hermitian matrix lies in its real spectrum. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_mem_spectrum [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue A k ∈ spectrum ℝ A := by
  obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact ⟨e.symm ⟨k, hk⟩, by rw [he, Equiv.apply_symm_apply]⟩

/-- The real spectrum of a Hermitian matrix is the set of its eigenvalues. -/
theorem _root_.Matrix.IsHermitian.spectrum_eq_image_eigenvalue [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectrum ℝ A = eigenvalue A '' Set.Iio (Fintype.card n) := by
  obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
  rw [hA.spectrum_real_eq_range_eigenvalues]
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, (e i).isLt, (he i).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e.symm ⟨k, hk⟩, by rw [he, Equiv.apply_symm_apply]⟩

end NLAlib
