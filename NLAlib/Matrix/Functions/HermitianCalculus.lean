/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import NLAlib.Matrix.Spectral.CourantFischer
public import NLAlib.Matrix.Norms.Loewner

/-!
# Functions of a Hermitian matrix

For a Hermitian matrix `A` and `f : ℝ → ℝ`, the matrix `f(A)` is Mathlib's continuous functional
calculus `cfc f A`. This file gives the working API in the vocabulary of this library: `cfc f A`
through any unitary diagonalisation, its trace, eigenvalues, quadratic form and spectral norm,
and its behaviour under unitary conjugation and block diagonal sums; the inverse and the inverse
square root of a positive definite matrix are functions of it.

No definition is introduced. `cfc f A` is the spelling of `f(A)`; the square root is
`CFC.sqrt A`, a real power of a positive semidefinite matrix is `A ^ r`, the absolute value is
`CFC.abs A` and the positive part is `A⁺`, all from Mathlib and all available with
`open scoped MatrixOrder`. They unfold to `cfc` by `CFC.sqrt_eq_real_sqrt`,
`CFC.rpow_eq_cfc_real`, `CFC.abs_eq_cfc_norm` and `CFC.posPart_def` (the first and the last to
the non-unital `cfcₙ`, which is `cfc` by `cfcₙ_eq_cfc`). General facts are Mathlib's:
`cfc_predicate` (`f(A)` is Hermitian), `cfc_commute_cfc`, `cfc_mono` (comparison on the
spectrum), `cfc_nonneg`, `cfc_pow_id`, `cfc_inv_id`, `cfc_polynomial`.

The location of the spectrum is the hypothesis `spectrum ℝ A ⊆ s`, or a Loewner sandwich
`a • 1 ≤ A`, `A ≤ b • 1` for an interval.

## Main results

* `NLAlib.cfc_eq_mul_diagonal_mul_conjTranspose`: `f(U D Uᴴ) = U f(D) Uᴴ`.
* `Matrix.IsHermitian.spectrum_subset_iff`: the spectrum through the sorted eigenvalues.
* `Matrix.IsHermitian.re_trace_cfc`: `tr f(A) = ∑ f(λ_i)`.
* `Matrix.IsHermitian.eigenvalue_cfc_of_monotoneOn`: eigenvalues of `f(A)` for monotone `f`.
* `Matrix.IsHermitian.specNorm_cfc_le`: `‖f(A)‖₂ ≤ max |f|` on the spectrum.
* `NLAlib.re_quadForm_cfc_eq_sum`: the quadratic form of `f(A)` as a weighted sum.
* `NLAlib.cfc_fromBlocks_diagonal`, `NLAlib.cfc_blockDiagonal`: block diagonal sums.
* `Matrix.PosDef.inv_eq_cfc`, `Matrix.PosDef.inv_sqrt_eq_cfc`: the inverse and the inverse
  square root.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Diagonalisation -/

/-- A matrix intertwining two real diagonal matrices intertwines their images under `f`. -/
private theorem diagonal_mul_eq_mul_diagonal_of_eq {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] {W : Matrix p q 𝕜} {d : p → ℝ} {e : q → ℝ}
    (h : Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * W =
      W * Matrix.diagonal fun j => ((e j : ℝ) : 𝕜)) (f : ℝ → ℝ) :
    Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * W =
      W * Matrix.diagonal fun j => ((f (e j) : ℝ) : 𝕜) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij ⊢
  by_cases hW : W i j = 0
  · rw [hW, mul_zero, zero_mul]
  · have hde : d i = e j := by
      rw [mul_comm] at hij
      exact RCLike.ofReal_injective (mul_left_cancel₀ hW hij)
    rw [hde, mul_comm]

/-- **`f(A)` through a unitary diagonalisation.** If `A = U * diagonal d * Uᴴ` with `d` real and
`U` unitary, that is, with orthonormal columns and as many columns as rows, on any column index
type, then `cfc f A = U * diagonal (f ∘ d) * Uᴴ`. The frame of the spectral theorem
`Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose` is such a `U`.
Port of `NLAlib.cfc_eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose`, there for the chosen
eigenvector matrix. -/
theorem cfc_eq_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n 𝕜} {U : Matrix n r 𝕜} {d : r → ℝ} (hU : HasOrthonormalCols U)
    (hr : Fintype.card r = Fintype.card n)
    (hA : A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) (f : ℝ → ℝ) :
    cfc f A = U * Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * Uᴴ := by
  have hH : A.IsHermitian := by
    rw [hA]
    refine Matrix.isHermitian_mul_mul_conjTranspose U ?_
    rw [Matrix.isHermitian_diagonal_iff]
    exact fun i => RCLike.conj_ofReal (d i)
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq hr.symm
  have hV := hH.hasOrthonormalCols_eigenvectorUnitary
  have hAV : A = (hH.eigenvectorUnitary : Matrix n n 𝕜) *
      Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : 𝕜)) *
        (hH.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
    have h := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hcfc : cfc f A = (hH.eigenvectorUnitary : Matrix n n 𝕜) *
      Matrix.diagonal (fun i => ((f (hH.eigenvalues i) : ℝ) : 𝕜)) *
        (hH.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
    rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  generalize (hH.eigenvectorUnitary : Matrix n n 𝕜) = V at hV hAV hcfc
  have hW : Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * (Uᴴ * V) =
      Uᴴ * V * Matrix.diagonal fun i => ((hH.eigenvalues i : ℝ) : 𝕜) := by
    calc Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * (Uᴴ * V)
        = Uᴴ * (U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) * V := by
          simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
      _ = Uᴴ * A * V := by rw [← hA]
      _ = Uᴴ * (V * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : 𝕜)) * Vᴴ) * V := by
          rw [← hAV]
      _ = Uᴴ * V * Matrix.diagonal fun i => ((hH.eigenvalues i : ℝ) : 𝕜) := by
          simp only [Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one]
  have hfW := diagonal_mul_eq_mul_diagonal_of_eq hW f
  rw [hcfc]
  calc V * Matrix.diagonal (fun i => ((f (hH.eigenvalues i) : ℝ) : 𝕜)) * Vᴴ
      = U * (Uᴴ * V * Matrix.diagonal fun i => ((f (hH.eigenvalues i) : ℝ) : 𝕜)) * Vᴴ := by
        simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    _ = U * Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * Uᴴ * (V * Vᴴ) := by
        rw [← hfW]
        simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * Uᴴ := by
        rw [hV.mul_conjTranspose_self, Matrix.mul_one]

/-- `f(A)` through the sorted spectral decomposition of a Hermitian matrix. -/
private theorem exists_cfc_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ U : Matrix n (Fin (Fintype.card n)) 𝕜, HasOrthonormalCols U ∧ U * Uᴴ = 1 ∧
      (A = U * (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) *
        Uᴴ) ∧
      ∀ f : ℝ → ℝ, cfc f A = U * (Matrix.diagonal fun i : Fin (Fintype.card n) =>
        ((f (eigenvalue A i) : ℝ) : 𝕜)) * Uᴴ := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  exact ⟨U, hU, hU.mul_conjTranspose_self_of_card_eq hr.symm, hAU,
    cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAU⟩

/-- `f` of a real diagonal matrix is the diagonal matrix of the values of `f`.
Port of `NLAlib.cfc_diagonal_real`. -/
theorem cfc_diagonal (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      Matrix.diagonal fun i => ((f (d i) : ℝ) : 𝕜) := by
  have h := cfc_eq_mul_diagonal_mul_conjTranspose (𝕜 := 𝕜) (U := (1 : Matrix n n 𝕜)) (d := d)
    hasOrthonormalCols_one rfl (by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]) f
  rwa [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h

/-- An eigenvector of `A` is an eigenvector of `f(A)`: if `A x = μ x` then `f(A) x = f(μ) x`. -/
theorem _root_.Matrix.IsHermitian.cfc_mulVec_of_mulVec_eq_smul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) {x : n → 𝕜} {μ : ℝ} (hx : A *ᵥ x = μ • x) :
    cfc f A *ᵥ x = f μ • x := by
  obtain ⟨U, hU, hUU, hAU, hcfc⟩ := exists_cfc_eq hA
  have hy : ∀ i : Fin (Fintype.card n),
      ((eigenvalue A i : ℝ) : 𝕜) * (Uᴴ *ᵥ x) i = (μ : 𝕜) * (Uᴴ *ᵥ x) i := by
    intro i
    have h := congrFun (congrArg (Uᴴ *ᵥ ·) hx) i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, RCLike.real_smul_eq_coe_mul] at h
    rw [← h]
    conv_rhs => rw [hAU]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU.conjTranspose_mul_self,
      Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  have hfy : (Matrix.diagonal fun i : Fin (Fintype.card n) => ((f (eigenvalue A i) : ℝ) : 𝕜)) *ᵥ
      (Uᴴ *ᵥ x) = f μ • (Uᴴ *ᵥ x) := by
    ext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, RCLike.real_smul_eq_coe_mul]
    by_cases h0 : (Uᴴ *ᵥ x) i = 0
    · rw [h0, mul_zero, mul_zero]
    · rw [RCLike.ofReal_injective (mul_right_cancel₀ h0 (hy i))]
  rw [hcfc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfy, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]

/-! ### Conjugation, relabelling and block sums -/

/-- **`f` commutes with unitary conjugation**: `f(U A Uᴴ) = U f(A) Uᴴ` for `U` unitary, that is,
with orthonormal columns and as many columns as rows, on any column index type.
Port of `NLAlib.cfc_unitary_conj`, there over `ℂ`. -/
theorem cfc_mul_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r] {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n) {A : Matrix r r 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) : cfc f (U * A * Uᴴ) = U * cfc f A * Uᴴ := by
  obtain ⟨V, hV, -, hAV, hcfc⟩ := exists_cfc_eq hA
  have hr' : Fintype.card (Fin (Fintype.card r)) = Fintype.card n := by
    rw [Fintype.card_fin, hr]
  have hUV : U * A * Uᴴ = U * V * (Matrix.diagonal fun i : Fin (Fintype.card r) =>
      ((eigenvalue A i : ℝ) : 𝕜)) * (U * V)ᴴ := by
    conv_lhs => rw [hAV]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [cfc_eq_mul_diagonal_mul_conjTranspose (hU.mul hV) hr' hUV f, hcfc f]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- `f` commutes with relabelling. Port of `NLAlib.cfc_reindex_of_isHermitian`. -/
theorem cfc_submatrix_equiv {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) (e : m ≃ n) :
    cfc f (A.submatrix e e) = (cfc f A).submatrix e e := by
  obtain ⟨V, hV, -, hAV, hcfc⟩ := exists_cfc_eq hA
  have hr : Fintype.card (Fin (Fintype.card n)) = Fintype.card m := by
    rw [Fintype.card_fin, Fintype.card_congr e]
  have hsub : ∀ D : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜,
      (V * D * Vᴴ).submatrix e e = V.submatrix e (Equiv.refl _) * D *
        (V.submatrix e (Equiv.refl _))ᴴ := by
    intro D
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul_equiv (V * D) Vᴴ e (Equiv.refl _) e,
      ← Matrix.submatrix_mul_equiv V D e (Equiv.refl _) (Equiv.refl _)]
    rfl
  have hA' : A.submatrix e e = V.submatrix e (Equiv.refl _) *
      (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) *
        (V.submatrix e (Equiv.refl _))ᴴ := by
    conv_lhs => rw [hAV]
    exact hsub _
  rw [cfc_eq_mul_diagonal_mul_conjTranspose (hV.submatrix e (Equiv.refl _).injective) hr hA' f,
    hcfc f, hsub]

/-- **`f` of a block diagonal matrix** is the block diagonal matrix of `f(A)` and `f(B)`.
Port of `NLAlib.cfc_fromBlocks`, there over `ℂ`. -/
theorem cfc_fromBlocks_diagonal {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (cfc f A) 0 0 (cfc f B) := by
  obtain ⟨V, hV, -, hAV, hcfcA⟩ := exists_cfc_eq hA
  obtain ⟨W, hW, -, hBW, hcfcB⟩ := exists_cfc_eq hB
  have hU : HasOrthonormalCols (Matrix.fromBlocks V 0 0 W) := by
    rw [HasOrthonormalCols, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      hV.conjTranspose_mul_self, hW.conjTranspose_mul_self, Matrix.fromBlocks_one]
  have hr : Fintype.card (Fin (Fintype.card m) ⊕ Fin (Fintype.card n)) =
      Fintype.card (m ⊕ n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
  have hblock : ∀ a : Fin (Fintype.card m) → ℝ, ∀ b : Fin (Fintype.card n) → ℝ,
      Matrix.fromBlocks (V * (Matrix.diagonal fun i => ((a i : ℝ) : 𝕜)) * Vᴴ) 0 0
        (W * (Matrix.diagonal fun i => ((b i : ℝ) : 𝕜)) * Wᴴ) =
      Matrix.fromBlocks V 0 0 W * (Matrix.diagonal fun i => ((Sum.elim a b i : ℝ) : 𝕜)) *
        (Matrix.fromBlocks V 0 0 W)ᴴ := by
    intro a b
    have hd : (Matrix.diagonal fun i => ((Sum.elim a b i : ℝ) : 𝕜)) =
        Matrix.fromBlocks (Matrix.diagonal fun i => ((a i : ℝ) : 𝕜)) 0 0
          (Matrix.diagonal fun i => ((b i : ℝ) : 𝕜)) := by
      rw [Matrix.fromBlocks_diagonal]
      congr 1
      funext i
      cases i <;> rfl
    rw [hd, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hAB : Matrix.fromBlocks A 0 0 B = Matrix.fromBlocks V 0 0 W *
      (Matrix.diagonal fun i => ((Sum.elim (fun i : Fin (Fintype.card m) => eigenvalue A i)
        (fun i : Fin (Fintype.card n) => eigenvalue B i) i : ℝ) : 𝕜)) *
        (Matrix.fromBlocks V 0 0 W)ᴴ := by
    rw [← hblock, ← hAV, ← hBW]
  rw [cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAB f, hcfcA f, hcfcB f, hblock]
  congr 3
  funext i
  cases i <;> rfl

/-- **`f` of a block diagonal matrix** with Hermitian blocks `A i` is the block diagonal matrix
of the `f (A i)`; the version of `cfc_fromBlocks_diagonal` for a family of blocks of one size. -/
theorem cfc_blockDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Matrix m m 𝕜} (hA : ∀ i, (A i).IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.blockDiagonal A) = Matrix.blockDiagonal fun i => cfc f (A i) := by
  choose U hU hAU using fun i => (hA i).exists_eq_mul_diagonal_mul_conjTranspose
  have hW : HasOrthonormalCols (Matrix.blockDiagonal U) := by
    rw [HasOrthonormalCols, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [(hU _).conjTranspose_mul_self]
    exact Matrix.blockDiagonal_one
  have hr : Fintype.card (Fin (Fintype.card m) × ι) = Fintype.card (m × ι) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  have hdiag : ∀ g : ℝ → ℝ, (Matrix.blockDiagonal fun i => U i *
      (Matrix.diagonal fun k : Fin (Fintype.card m) => ((g (eigenvalue (A i) k) : ℝ) : 𝕜)) *
        (U i)ᴴ) = Matrix.blockDiagonal U *
      (Matrix.diagonal fun p : Fin (Fintype.card m) × ι =>
        ((g (eigenvalue (A p.2) p.1) : ℝ) : 𝕜)) * (Matrix.blockDiagonal U)ᴴ := fun g => by
    rw [Matrix.blockDiagonal_mul, Matrix.blockDiagonal_mul, Matrix.blockDiagonal_conjTranspose,
      Matrix.blockDiagonal_diagonal]
  have hA' : Matrix.blockDiagonal A = Matrix.blockDiagonal U *
      (Matrix.diagonal fun p : Fin (Fintype.card m) × ι =>
        ((eigenvalue (A p.2) p.1 : ℝ) : 𝕜)) * (Matrix.blockDiagonal U)ᴴ := by
    exact (congrArg _ (funext hAU)).trans (hdiag id)
  rw [cfc_eq_mul_diagonal_mul_conjTranspose hW hr hA' f, ← hdiag f]
  exact congrArg _ (funext fun i =>
    (cfc_eq_mul_diagonal_mul_conjTranspose (hU i) (Fintype.card_fin _) (hAU i) f).symm)

/-! ### The spectrum -/

/-- The spectrum of a Hermitian matrix lies in `s` exactly when its eigenvalues do. -/
theorem _root_.Matrix.IsHermitian.spectrum_subset_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {s : Set ℝ} : spectrum ℝ A ⊆ s ↔ ∀ i, i < Fintype.card n → eigenvalue A i ∈ s := by
  classical
  rw [hA.spectrum_eq_image_eigenvalue, Set.image_subset_iff]
  exact Iff.rfl

/-- A matrix between `a • 1` and `b • 1` has its spectrum in `[a, b]`. -/
theorem spectrum_subset_Icc_of_le {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) :
    spectrum ℝ A ⊆ Set.Icc a b := by
  have hA := isHermitian_of_le_smul_one h₂
  rw [hA.spectrum_subset_iff]
  intro i hi
  have : Nonempty n := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hi)
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by omega⟩
  exact ⟨((hA.smul_one_le_iff hk).mp h₁).trans
      (hA.eigenvalue_le_eigenvalue (by omega) (by omega)),
    (hA.eigenvalue_le_eigenvalue (Nat.zero_le i) hi).trans (hA.le_smul_one_iff.mp h₂)⟩

/-- The spectrum of a positive semidefinite matrix is nonnegative. -/
theorem _root_.Matrix.PosSemidef.spectrum_subset_Ici {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    spectrum ℝ A ⊆ Set.Ici 0 := by
  rw [hA.isHermitian.spectrum_subset_iff]
  exact fun i _ => hA.eigenvalue_nonneg i

/-- The spectrum of a positive definite matrix is positive. -/
theorem _root_.Matrix.PosDef.spectrum_subset_Ioi {A : Matrix n n 𝕜} (hA : A.PosDef) :
    spectrum ℝ A ⊆ Set.Ioi 0 := by
  rw [hA.isHermitian.spectrum_subset_iff]
  exact hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA

/-! ### Trace, eigenvalues and quadratic forms -/

/-- **The trace of `f(A)`** is the sum of `f` over the eigenvalues.
Port of `NLAlib.re_trace_cfc_eq_sum_eigenvalues`.
Result: trace-of-matrix-function -/
theorem _root_.Matrix.IsHermitian.re_trace_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    RCLike.re (cfc f A).trace = ∑ i ∈ Finset.range (Fintype.card n), f (eigenvalue A i) := by
  obtain ⟨U, hU, -, -, hcfc⟩ := exists_cfc_eq hA
  rw [hcfc f, Matrix.trace_mul_cycle, hU.conjTranspose_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal, map_sum]
  simp only [RCLike.ofReal_re]
  exact Fin.sum_univ_eq_sum_range (fun i => f (eigenvalue A i)) _

/-- **Eigenvalues of `f(A)` for a non-decreasing `f`**: `λ_k(f(A)) = f(λ_k(A))`, when `f` is
monotone on a set containing the spectrum of `A`.
Port of `NLAlib.eigenvalues₀_cfc_of_antitone`, there with the hypothesis on the composite. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_cfc_of_monotoneOn {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s)
    (hs : spectrum ℝ A ⊆ s) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue (cfc f A) k = f (eigenvalue A k) := by
  obtain ⟨U, hU, -, -, hcfc⟩ := exists_cfc_eq hA
  have hanti : Antitone fun i : Fin (Fintype.card n) => f (eigenvalue A i) := fun i j hij =>
    hf (hs (hA.eigenvalue_mem_spectrum j.isLt)) (hs (hA.eigenvalue_mem_spectrum i.isLt))
      (hA.eigenvalue_le_eigenvalue hij j.isLt)
  exact eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU rfl hanti (hcfc f) ⟨k, hk⟩

/-- Eigenvalues of `f(A)` for a non-increasing `f`: `λ_k(f(A)) = f(λ_j(A))` with
`k + j + 1 = card n`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_cfc_of_antitoneOn {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {s : Set ℝ} (hf : AntitoneOn f s)
    (hs : spectrum ℝ A ⊆ s) {k j : ℕ} (hkj : k + j + 1 = Fintype.card n) :
    eigenvalue (cfc f A) k = f (eigenvalue A j) := by
  have hj : j < Fintype.card n := by omega
  have h := hA.eigenvalue_cfc_of_monotoneOn (f := fun x => -f x) hf.neg hs hj
  have hneg : cfc f A = -cfc (fun x => -f x) A := by rw [cfc_neg, neg_neg]
  rw [hneg, eigenvalue_neg _ hkj, h, neg_neg]

/-- **The quadratic form of `f(A)`** through a unitary diagonalisation `A = U D Uᴴ`, with `U`
having orthonormal columns and as many columns as rows, on any column index type:
`xᴴ f(A) x = ∑ f(d_i) |(Uᴴ x)_i|²`. This is the identity behind Gauss quadrature for `xᴴ f(A) x`.
Port of `NLAlib.dotProduct_cfc_mulVec_eq_sum`, there over `ℝ` with the chosen eigenbasis. -/
theorem re_quadForm_cfc_eq_sum {r : Type*} [Fintype r] [DecidableEq r] {A : Matrix n n 𝕜}
    {U : Matrix n r 𝕜} {d : r → ℝ} (hU : HasOrthonormalCols U)
    (hr : Fintype.card r = Fintype.card n)
    (hA : A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) (f : ℝ → ℝ) (x : n → 𝕜) :
    RCLike.re (quadForm (cfc f A) x) = ∑ i, f (d i) * ‖(Uᴴ *ᵥ x) i‖ ^ 2 := by
  have h := quadForm_conjTranspose_mul_mul (Matrix.diagonal fun i => ((f (d i) : ℝ) : 𝕜)) Uᴴ x
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [cfc_eq_mul_diagonal_mul_conjTranspose hU hr hA f, h, quadForm_diagonal, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- **A nonnegative trace function dominates its value at the largest eigenvalue**: if `φ ≥ 0`
on the spectrum of `A` then `φ(λ_0(A)) ≤ tr φ(A)`. With `φ = exp` this is the first step of the
matrix Laplace transform method; with `φ(t) = max (t - 1) 0` it is the first step of the
intrinsic-dimension bounds. [Tropp2015, Proposition 3.2.1 and §7.5]. -/
theorem _root_.Matrix.IsHermitian.apply_eigenvalue_zero_le_re_trace_cfc [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {φ : ℝ → ℝ} (hφ : ∀ x ∈ spectrum ℝ A, 0 ≤ φ x) :
    φ (eigenvalue A 0) ≤ RCLike.re (cfc φ A).trace := by
  rw [hA.re_trace_cfc]
  exact Finset.single_le_sum (f := fun i => φ (eigenvalue A i))
    (fun i hi => hφ _ (hA.eigenvalue_mem_spectrum (Finset.mem_range.mp hi)))
    (Finset.mem_range.mpr Fintype.card_pos)

/-! ### Order and norm bounds -/

/-- Comparison on an interval containing the spectrum: if `a • 1 ≤ A ≤ b • 1` and `f ≤ g` on
`[a, b]`, then `f(A) ≤ g(A)`. The comparison on the spectrum itself is Mathlib's `cfc_mono`. -/
theorem cfc_le_cfc_of_forall_mem_Icc {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc a b, f x ≤ g x) : cfc f A ≤ cfc g A := by
  have hs := spectrum_subset_Icc_of_le h₁ h₂
  exact cfc_mono (fun x hx => h x (hs hx)) (A.finite_real_spectrum.continuousOn f)
    (A.finite_real_spectrum.continuousOn g)

/-- The quadratic form of `f(A)` is bounded by the largest `|f|` on the spectrum. -/
private theorem abs_re_quadForm_cfc_le_aux {A : Matrix n n 𝕜} (hA : A.IsHermitian) {f : ℝ → ℝ}
    {c : ℝ} (h : ∀ x ∈ spectrum ℝ A, |f x| ≤ c) (x : n → 𝕜) :
    |RCLike.re (quadForm (cfc f A) x)| ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  obtain ⟨U, hU, -, hAU, -⟩ := exists_cfc_eq hA
  have hr := Fintype.card_fin (Fintype.card n)
  rw [re_quadForm_cfc_eq_sum hU hr hAU f x,
    ← (hU.conjTranspose_of_card_eq hr.symm).norm_toLp_mulVec x, EuclideanSpace.norm_sq_eq,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖(Uᴴ *ᵥ x) i‖ ^ 2)]
  exact mul_le_mul_of_nonneg_right (h _ (hA.eigenvalue_mem_spectrum i.isLt)) (by positivity)

/-- **The spectral norm of `f(A)`** is at most the largest `|f|` on the spectrum.
Port of `NLAlib.specNorm_aeval_le`, there for polynomials over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.specNorm_cfc_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ A, |f x| ≤ c) :
    specNorm (cfc f A) ≤ c := by
  have hH : (cfc f A).IsHermitian := cfc_predicate f A
  exact (hH.specNorm_le_iff_abs_re_quadForm_le hc).mpr (abs_re_quadForm_cfc_le_aux hA h)

/-- The quadratic form of `f(A)` is bounded by the largest `|f|` on the spectrum.
Port of `NLAlib.abs_dotProduct_cfc_mulVec_le`. -/
theorem _root_.Matrix.IsHermitian.abs_re_quadForm_cfc_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {c : ℝ} (h : ∀ x ∈ spectrum ℝ A, |f x| ≤ c) (x : n → 𝕜) :
    |RCLike.re (quadForm (cfc f A) x)| ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  exact abs_re_quadForm_cfc_le_aux hA h x

/-- A lower bound for the trace of `f(A)` from a lower bound of `f` on the spectrum.
Port of `NLAlib.mul_card_le_re_trace_cfc_of_le`. -/
theorem _root_.Matrix.IsHermitian.mul_card_le_re_trace_cfc {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {b : ℝ} (h : ∀ x ∈ spectrum ℝ A, b ≤ f x) :
    b * Fintype.card n ≤ RCLike.re (cfc f A).trace := by
  rw [hA.re_trace_cfc, mul_comm]
  have hsum := Finset.card_nsmul_le_sum (Finset.range (Fintype.card n))
    (fun i => f (eigenvalue A i)) b
    (fun i hi => h _ (hA.eigenvalue_mem_spectrum (Finset.mem_range.mp hi)))
  rwa [Finset.card_range, nsmul_eq_mul] at hsum

/-! ### The inverse and the inverse square root -/

/-- The inverse of a positive definite matrix through the functional calculus:
`A⁻¹ = cfc (fun x => x⁻¹) A`. -/
theorem _root_.Matrix.PosDef.inv_eq_cfc {A : Matrix n n 𝕜} (hA : A.PosDef) :
    A⁻¹ = cfc (fun x : ℝ => x⁻¹) A := by
  have hH : IsSelfAdjoint A := hA.isHermitian
  have h : cfc (fun x : ℝ => x⁻¹) A * cfc (fun x : ℝ => x) A = 1 := by
    rw [← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _), ← cfc_one ℝ A]
    refine cfc_congr fun x hx => ?_
    simp only [Pi.one_apply]
    exact inv_mul_cancel₀ (hA.spectrum_subset_Ioi hx).ne'
  rw [cfc_id' ℝ A hH] at h
  exact Matrix.inv_eq_left_inv h

/-- The functional calculus of `x ↦ (√x)⁻¹` is a left inverse of the square root of a positive
definite matrix. -/
private theorem cfc_inv_sqrt_mul_sqrt {A : Matrix n n 𝕜} (hA : A.PosDef) :
    cfc (fun x : ℝ => (√x)⁻¹) A * CFC.sqrt A = 1 := by
  have hH : IsSelfAdjoint A := hA.isHermitian
  rw [CFC.sqrt_eq_real_sqrt A (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef), cfcₙ_eq_cfc,
    ← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _), ← cfc_one ℝ A]
  refine cfc_congr fun x hx => ?_
  have hx0 : 0 < √x := Real.sqrt_pos.mpr (hA.spectrum_subset_Ioi hx)
  simp only [Pi.one_apply]
  exact inv_mul_cancel₀ hx0.ne'

/-- The inverse of the square root of a positive definite matrix through the functional
calculus. Port of `NLAlib.cfc_inv_sqrt_mul_sqrt`. -/
theorem _root_.Matrix.PosDef.inv_sqrt_eq_cfc {A : Matrix n n 𝕜} (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ = cfc (fun x : ℝ => (√x)⁻¹) A := by
  exact Matrix.inv_eq_left_inv (cfc_inv_sqrt_mul_sqrt hA)

/-- The square root of a positive definite matrix is invertible. -/
theorem _root_.Matrix.PosDef.isUnit_sqrt {A : Matrix n n 𝕜} (hA : A.PosDef) :
    IsUnit (CFC.sqrt A) := by
  exact IsUnit.of_mul_eq_one_right _ (cfc_inv_sqrt_mul_sqrt hA)

end NLAlib
