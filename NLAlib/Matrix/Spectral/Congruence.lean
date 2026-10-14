/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.ConjTranspose
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Spectral.Diagonalizable
public import NLAlib.Matrix.Spectral.Inertia
public import NLAlib.Matrix.Subspaces.Frames

/-!
# Simultaneous diagonalisation by congruence

A positive definite `A` and a Hermitian `B` are simultaneously diagonalised by congruence:
`A = S Sᴴ` and `B = S D Sᴴ` with `D` real diagonal. The entries of `D` are the generalized
eigenvalues of the pair, the eigenvalues of `A⁻¹ B`, so `A⁻¹ B` and `A B` are diagonalisable with
real spectrum. Two positive semidefinite matrices are simultaneously diagonalised by congruence
as well, and for an indefinite invertible `A` this happens exactly when `A⁻¹ B` is diagonalisable
with real eigenvalues. Over `ℂ` every pair of square matrices is simultaneously unitarily
triangularised (the generalized Schur, or QZ, decomposition).

## Main results

* `Matrix.PosDef.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose`: the definite
  pair.
* `NLAlib.isEigenvalueListing_inv_mul_of_eq_mul_diagonal_mul_conjTranspose`,
  `Matrix.PosDef.isDiagonalizable_inv_mul`.
* `Matrix.PosSemidef.exists_conjTranspose_mul_mul_eq_diagonal`: the semidefinite pair.
* `NLAlib.exists_hasOrthonormalCols_isUpperTriangular_isUpperTriangular`: the QZ decomposition.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Definite pairs -/

/-- The conjugate transpose of an invertible matrix is invertible. -/
private theorem isUnit_det_conjTranspose {S : Matrix n n 𝕜} (hS : IsUnit S.det) :
    IsUnit Sᴴ.det := by
  rw [Matrix.det_conjTranspose]
  exact hS.star

/-- For `A = S Sᴴ` and `B = S D Sᴴ`, the columns of `S⁻ᴴ` are eigenvectors of `A⁻¹ B` when `D` is
diagonal: `A⁻¹ B S⁻ᴴ = S⁻ᴴ D`. -/
private theorem inv_mul_mul_inv_conjTranspose {A B S D : Matrix n n 𝕜} (hS : IsUnit S.det)
    (hA : A = S * Sᴴ) (hB : B = S * D * Sᴴ) : A⁻¹ * B * (Sᴴ)⁻¹ = (Sᴴ)⁻¹ * D := by
  rw [hA, hB, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ (isUnit_det_conjTranspose hS), Matrix.mul_one,
    ← Matrix.mul_assoc S⁻¹, Matrix.nonsing_inv_mul _ hS, Matrix.one_mul]

/-- The middle factor of a congruence by an invertible matrix. -/
private theorem diagonal_eq_inv_mul_mul_conjTranspose {B S D : Matrix n n 𝕜} (hS : IsUnit S.det)
    (hB : B = S * D * Sᴴ) : D = S⁻¹ * B * (S⁻¹)ᴴ := by
  rw [hB, Matrix.conjTranspose_nonsing_inv]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ (isUnit_det_conjTranspose hS), Matrix.mul_one,
    ← Matrix.mul_assoc S⁻¹, Matrix.nonsing_inv_mul _ hS, Matrix.one_mul]

/-- **Simultaneous diagonalisation of a definite pair.** For `A` positive definite and `B`
Hermitian there are an invertible `S` and a real `d` with `A = S Sᴴ` and `B = S diag(d) Sᴴ`.
[HornJohnson2013, Theorem 7.6.4]; [GolubVanLoan2013, Theorem 8.7.1].
Port of `NLAlib.exists_definite_pair_congruence_diagonal`, there over `ℝ`.
Result: definite-pair -/
theorem _root_.Matrix.PosDef.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose
    {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (S : Matrix n n 𝕜) (d : n → ℝ), IsUnit S.det ∧ A = S * Sᴴ ∧
      B = S * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Sᴴ := by
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨L, hL⟩ := (exists_isCholesky_iff_posDef A).mpr hA
  have hLu : IsUnit L.det := hL.isUnit_det
  have hLL : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hLu
  have hLL' : (L⁻¹)ᴴ * Lᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hLL, Matrix.conjTranspose_one]
  obtain ⟨U, d, hU, hd⟩ := (Matrix.isHermitian_mul_mul_conjTranspose L⁻¹
    hB).exists_hasOrthonormalCols_eq_mul_diagonal_mul_conjTranspose
  refine ⟨L * U, d, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact hLu.mul ((Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit)
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U,
      hU.mul_conjTranspose_self, Matrix.one_mul]
    exact hL.eq_mul_conjTranspose
  · calc B = L * (L⁻¹ * B * (L⁻¹)ᴴ) * Lᴴ := by
          simp only [Matrix.mul_assoc]
          rw [hLL', Matrix.mul_one, ← Matrix.mul_assoc, hLL, Matrix.one_mul]
      _ = L * U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * (L * U)ᴴ := by
          rw [hd, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]

/-- **The generalized eigenvalues of a definite pair** are the eigenvalues of `A⁻¹ B`.
Port of `NLAlib.charpoly_inverse_mul_eq_prod_of_congruence`. -/
theorem isEigenvalueListing_inv_mul_of_eq_mul_diagonal_mul_conjTranspose {A B S : Matrix n n 𝕜}
    {d : n → ℝ} (hS : IsUnit S.det) (hA : A = S * Sᴴ)
    (hB : B = S * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Sᴴ) :
    IsEigenvalueListing (A⁻¹ * B) (fun i => ((d i : ℝ) : 𝕜)) := by
  exact isEigenvalueListing_of_mul_eq_mul_diagonal
    (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_conjTranspose hS))
    (inv_mul_mul_inv_conjTranspose hS hA hB)

/-- For `A` positive definite and `B` Hermitian, `A⁻¹ B` is diagonalisable.
[HornJohnson2013, Theorem 7.6.3]. Port of `NLAlib.isDiagonalizable_inverse_mul_of_posDef`. -/
theorem _root_.Matrix.PosDef.isDiagonalizable_inv_mul {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.IsHermitian) : IsDiagonalizable (A⁻¹ * B) := by
  obtain ⟨S, d, hS, hA', hB'⟩ :=
    hA.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose hB
  exact ⟨(Sᴴ)⁻¹, _, Matrix.isUnit_nonsing_inv_det _ (isUnit_det_conjTranspose hS),
    inv_mul_mul_inv_conjTranspose hS hA' hB'⟩

/-- For `A` positive definite and `B` Hermitian, `A B` is diagonalisable.
Port of `NLAlib.isDiagonalizable_mul_of_posDef`. -/
theorem _root_.Matrix.PosDef.isDiagonalizable_mul {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.IsHermitian) : IsDiagonalizable (A * B) := by
  have h := hA.inv.isDiagonalizable_inv_mul hB
  rwa [Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)] at h

/-- For `A` positive definite and `B` Hermitian, the eigenvalues of `A B` are real: its
characteristic polynomial splits with real roots. -/
theorem _root_.Matrix.PosDef.exists_isEigenvalueListing_mul {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.IsHermitian) : ∃ d : n → ℝ, IsEigenvalueListing (A * B) (fun i => ((d i : ℝ) : 𝕜)) := by
  obtain ⟨S, d, hS, hA', hB'⟩ :=
    hA.inv.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose hB
  have h := isEigenvalueListing_inv_mul_of_eq_mul_diagonal_mul_conjTranspose hS hA' hB'
  rw [Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)] at h
  exact ⟨d, h⟩

/-- For `A` positive definite and `B` positive semidefinite, the eigenvalues of `A B` are real
and nonnegative. Port of `NLAlib.spectrum_mul_subset_nonneg_of_posDef`. -/
theorem _root_.Matrix.PosDef.exists_isEigenvalueListing_mul_nonneg {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    ∃ d : n → ℝ, IsEigenvalueListing (A * B) (fun i => ((d i : ℝ) : 𝕜)) ∧ ∀ i, 0 ≤ d i := by
  obtain ⟨S, d, hS, hA', hB'⟩ :=
    hA.inv.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose hB.isHermitian
  have h := isEigenvalueListing_inv_mul_of_eq_mul_diagonal_mul_conjTranspose hS hA' hB'
  rw [Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)] at h
  refine ⟨d, h, fun i => ?_⟩
  have hD := hB.mul_mul_conjTranspose_same S⁻¹
  rw [← diagonal_eq_inv_mul_mul_conjTranspose hS hB', Matrix.posSemidef_diagonal_iff] at hD
  exact RCLike.ofReal_nonneg.mp (hD i)

/-- The inertia of `B` is read off the diagonal of a congruence.
Port of `NLAlib.inertia_diagonal_eq_of_congruence`. -/
theorem inertiaPos_eq_card_of_eq_mul_diagonal_mul_conjTranspose {B S : Matrix n n 𝕜} {d : n → ℝ}
    (hS : IsUnit S.det) (hB : B = S * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Sᴴ) :
    inertiaPos B = (Finset.univ.filter fun i => 0 < d i).card := by
  have hD : (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)).IsHermitian :=
    Matrix.conjTranspose_diagonal_ofReal d
  have h := hD.inertiaPos_conjTranspose_mul_mul (isUnit_det_conjTranspose hS)
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [hB, h, inertiaPos_diagonal]

/-! ### Semidefinite and indefinite pairs -/

omit [DecidableEq n] in
/-- The kernel of a sum of positive semidefinite matrices is the intersection of the kernels.
Port of `NLAlib.ker_add_eq_inf_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.ker_add {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    LinearMap.ker (A + B).mulVecLin = LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_inf, Matrix.add_mulVec]
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, add_zero]⟩
  have h1 : star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (B *ᵥ x) = 0 := by
    rw [← dotProduct_add, h, dotProduct_zero]
  have ha := hA.dotProduct_mulVec_nonneg x
  have hb := hB.dotProduct_mulVec_nonneg x
  have ha0 : star x ⬝ᵥ (A *ᵥ x) = 0 :=
    le_antisymm (h1 ▸ le_add_of_nonneg_right hb) ha
  have hb0 : star x ⬝ᵥ (B *ᵥ x) = 0 :=
    le_antisymm (h1 ▸ le_add_of_nonneg_left ha) hb
  exact ⟨(hA.dotProduct_mulVec_zero_iff x).mp ha0, (hB.dotProduct_mulVec_zero_iff x).mp hb0⟩

omit [DecidableEq n] in
/-- Positive semidefinite matrices whose sum is idempotent commute. -/
private theorem commute_of_add_eq_of_mul_self_eq {A B P : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hAB : A + B = P) (hP : P * P = P) : Commute A B := by
  classical
  have hker : ∀ y, A *ᵥ ((1 - P) *ᵥ y) = 0 := by
    intro y
    have h : (1 - P) *ᵥ y ∈ LinearMap.ker (A + B).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hAB, Matrix.mulVec_mulVec, Matrix.mul_sub,
        Matrix.mul_one, hP, sub_self, Matrix.zero_mulVec]
    rw [hA.ker_add hB] at h
    exact h.1
  have hAP : A * P = A := by
    have h : A * (1 - P) = 0 := Matrix.mulVec_injective (funext fun y => by
      rw [← Matrix.mulVec_mulVec, hker, Matrix.zero_mulVec])
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h.symm
  have hPA : P * A = A := by
    have h := congrArg Matrix.conjTranspose hAP
    rwa [Matrix.conjTranspose_mul, hA.isHermitian.eq, ← hAB,
      (hA.isHermitian.add hB.isHermitian).eq, hAB] at h
  rw [Commute, SemiconjBy, ← sub_eq_of_eq_add' hAB.symm, Matrix.mul_sub, Matrix.sub_mul, hAP, hPA]

/-- A positive semidefinite matrix is congruent to a diagonal matrix of zeros and ones. -/
private theorem exists_conjTranspose_mul_mul_eq_diagonal_indicator {C : Matrix n n 𝕜}
    (hC : C.PosSemidef) :
    ∃ (X : Matrix n n 𝕜) (e : n → ℝ), IsUnit X.det ∧
      Xᴴ * C * X = Matrix.diagonal (fun i => ((e i : ℝ) : 𝕜)) ∧ ∀ i, e i * e i = e i := by
  obtain ⟨U, c, hU, hCU⟩ :=
    hC.isHermitian.exists_hasOrthonormalCols_eq_mul_diagonal_mul_conjTranspose
  have hc : ∀ i, 0 ≤ c i := by
    have h := hC.conjTranspose_mul_mul_same U
    rw [hU.eq_mul_mul_conjTranspose_iff.mp hCU, Matrix.posSemidef_diagonal_iff] at h
    exact fun i => RCLike.ofReal_nonneg.mp (h i)
  have hs : ∀ i, (if c i = 0 then (1 : ℝ) else (√(c i))⁻¹) ≠ 0 := by
    intro i
    split_ifs with h
    · exact one_ne_zero
    · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr ((hc i).lt_of_ne' h))
  refine ⟨U * Matrix.diagonal (fun i => (((if c i = 0 then (1 : ℝ) else (√(c i))⁻¹ : ℝ)) : 𝕜)),
    fun i => if c i = 0 then 0 else 1, ?_, ?_, fun i => by beta_reduce; split_ifs <;> norm_num⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    refine ((Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit).mul (isUnit_iff_ne_zero.mpr ?_)
    exact Finset.prod_ne_zero_iff.mpr fun i _ => RCLike.ofReal_ne_zero.mpr (hs i)
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_diagonal_ofReal, hCU]
    simp only [Matrix.mul_assoc]
    rw [hU.conjTranspose_mul_cancel_left, ← Matrix.mul_assoc Uᴴ, hU.conjTranspose_mul_self,
      Matrix.one_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul]
    congr 1
    split_ifs with h
    · rw [h, zero_mul, mul_zero]
    · have h1 : √(c i) ≠ 0 := Real.sqrt_ne_zero'.mpr ((hc i).lt_of_ne' h)
      field_simp
      exact (Real.sq_sqrt (hc i)).symm

/-- **Two positive semidefinite matrices are simultaneously diagonalised by congruence**, with
nonnegative diagonals. [HornJohnson2013, Theorem 7.6.4 context].
Port of `NLAlib.exists_diagonal_congruence_of_posSemidef`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.exists_conjTranspose_mul_mul_eq_diagonal {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ (X : Matrix n n 𝕜) (a b : n → ℝ), IsUnit X.det ∧
      Xᴴ * A * X = Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) ∧
      Xᴴ * B * X = Matrix.diagonal (fun i => ((b i : ℝ) : 𝕜)) ∧
      (∀ i, 0 ≤ a i) ∧ ∀ i, 0 ≤ b i := by
  obtain ⟨X₁, e, hX₁, hsum, he⟩ := exists_conjTranspose_mul_mul_eq_diagonal_indicator
    (hA.add hB)
  have hA' := hA.conjTranspose_mul_mul_same X₁
  have hB' := hB.conjTranspose_mul_mul_same X₁
  rw [Matrix.mul_add, Matrix.add_mul] at hsum
  have hP : (Matrix.diagonal fun i => ((e i : ℝ) : 𝕜)) *
      Matrix.diagonal (fun i => ((e i : ℝ) : 𝕜)) = Matrix.diagonal fun i => ((e i : ℝ) : 𝕜) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← RCLike.ofReal_mul, he i]
  obtain ⟨V, a, b, hV, ha, hb⟩ :=
    (hA'.isHermitian.commute_iff_exists_eq_mul_diagonal_mul_conjTranspose hB'.isHermitian).mp
      (commute_of_add_eq_of_mul_self_eq hA' hB' hsum hP)
  have hXA : (X₁ * V)ᴴ * A * (X₁ * V) = Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) := by
    rw [Matrix.conjTranspose_mul, ← hV.eq_mul_mul_conjTranspose_iff.mp ha]
    simp only [Matrix.mul_assoc]
  have hXB : (X₁ * V)ᴴ * B * (X₁ * V) = Matrix.diagonal (fun i => ((b i : ℝ) : 𝕜)) := by
    rw [Matrix.conjTranspose_mul, ← hV.eq_mul_mul_conjTranspose_iff.mp hb]
    simp only [Matrix.mul_assoc]
  have ha0 := hA.conjTranspose_mul_mul_same (X₁ * V)
  have hb0 := hB.conjTranspose_mul_mul_same (X₁ * V)
  rw [hXA, Matrix.posSemidef_diagonal_iff] at ha0
  rw [hXB, Matrix.posSemidef_diagonal_iff] at hb0
  refine ⟨X₁ * V, a, b, ?_, hXA, hXB, fun i => RCLike.ofReal_nonneg.mp (ha0 i),
    fun i => RCLike.ofReal_nonneg.mp (hb0 i)⟩
  rw [Matrix.det_mul]
  exact hX₁.mul ((Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit)

/-- **A real symmetric pair with invertible `A` is simultaneously diagonalised by congruence
exactly when `A⁻¹ B` is diagonalisable over `ℝ`.** [HornJohnson2013, Theorem 4.5.17].
Port of `NLAlib.exists_diagonal_congruence_iff_isDiagonalizable_inverse_mul`. -/
theorem _root_.Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_diagonal_iff
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hAu : IsUnit A.det) (hB : B.IsHermitian) :
    (∃ (X : Matrix n n ℝ) (a b : n → ℝ), IsUnit X.det ∧ Xᴴ * A * X = Matrix.diagonal a ∧
      Xᴴ * B * X = Matrix.diagonal b) ↔ IsDiagonalizable (A⁻¹ * B) := by
  have hAu' : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hAu
  constructor
  · rintro ⟨X, a, b, hX, hXA, hXB⟩
    have hXAu : IsUnit (Xᴴ * A) :=
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_conjTranspose hX)).mul hAu'
    have ha : ∀ i, a i ≠ 0 := by
      have h : IsUnit (Matrix.diagonal a).det := by
        rw [← hXA, Matrix.det_mul]
        exact ((Matrix.isUnit_iff_isUnit_det _).mp hXAu).mul hX
      rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff] at h
      exact fun i => h i (Finset.mem_univ i)
    refine ⟨X, fun i => (a i)⁻¹ * b i, hX, hXAu.mul_left_cancel ?_⟩
    calc Xᴴ * A * (A⁻¹ * B * X) = Xᴴ * B * X := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc A A⁻¹, Matrix.mul_nonsing_inv A hAu, Matrix.one_mul]
      _ = Xᴴ * A * (X * Matrix.diagonal fun i => (a i)⁻¹ * b i) := by
          rw [← Matrix.mul_assoc, hXA, hXB, Matrix.diagonal_mul_diagonal]
          congr 1
          funext i
          rw [mul_inv_cancel_left₀ (ha i)]
  · rintro ⟨V, d, hV, hTV⟩
    have hC : (Vᴴ * A * V).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V hA
    have hD : (Matrix.diagonal d).IsHermitian := Matrix.isHermitian_diagonal d
    have hCD : Vᴴ * A * V * Matrix.diagonal d = Vᴴ * B * V := by
      rw [Matrix.mul_assoc, ← hTV]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc A A⁻¹, Matrix.mul_nonsing_inv A hAu, Matrix.one_mul]
    have hcomm : Commute (Vᴴ * A * V) (Matrix.diagonal d) :=
      (hC.commute_iff hD).mpr (hCD ▸ Matrix.isHermitian_conjTranspose_mul_mul V hB)
    obtain ⟨U, a, e, hU, hCU, hDU⟩ :=
      (hC.commute_iff_exists_eq_mul_diagonal_mul_conjTranspose hD).mp hcomm
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hCU hDU
    refine ⟨V * U, a, fun i => a i * e i, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul]
      exact hV.mul ((Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit)
    · rw [Matrix.conjTranspose_mul, ← hU.eq_mul_mul_conjTranspose_iff.mp hCU]
      simp only [Matrix.mul_assoc]
    · calc (V * U)ᴴ * B * (V * U) = Uᴴ * (Vᴴ * A * V * Matrix.diagonal d) * U := by
            rw [hCD, Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = Uᴴ * (Vᴴ * A * V) * U * (Uᴴ * Matrix.diagonal d * U) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc U Uᴴ, hU.mul_conjTranspose_self, Matrix.one_mul]
        _ = Matrix.diagonal fun i => a i * e i := by
            rw [hU.eq_mul_mul_conjTranspose_iff.mp hCU, hU.eq_mul_mul_conjTranspose_iff.mp hDU,
              Matrix.diagonal_mul_diagonal]

/-! ### The generalized Schur decomposition -/

/-- The QZ decomposition of a pencil with invertible `B`: a Schur form `Zᴴ (B⁻¹ A) Z` followed by a
QR factorization of `B Z`. -/
private theorem exists_isUpperTriangular_of_isUnit_det [LinearOrder n] (A : Matrix n n ℂ)
    {B : Matrix n n ℂ} (hB : IsUnit B.det) :
    ∃ Q Z : Matrix n n ℂ, HasOrthonormalCols Q ∧ HasOrthonormalCols Z ∧
      (Qᴴ * A * Z).IsUpperTriangular ∧ (Qᴴ * B * Z).IsUpperTriangular := by
  obtain ⟨Z, hZ, hT⟩ := exists_hasOrthonormalCols_isUpperTriangular (B⁻¹ * A)
  obtain ⟨Q, R, hQR, -⟩ := exists_isQR (B * Z) le_rfl
  have hR : Qᴴ * B * Z = R := by
    rw [Matrix.mul_assoc]
    exact hQR.conjTranspose_mul_eq
  have h : Qᴴ * A * Z = R * (Zᴴ * (B⁻¹ * A) * Z) := by
    rw [← hR]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Z Zᴴ, hZ.mul_conjTranspose_self, Matrix.one_mul,
      ← Matrix.mul_assoc B B⁻¹, Matrix.mul_nonsing_inv B hB, Matrix.one_mul]
  refine ⟨Q, Z, hQR.hasOrthonormalCols, hZ, ?_, ?_⟩
  · rw [h]
    exact Matrix.BlockTriangular.mul hQR.isUpperTriangular hT
  · rw [hR]
    exact hQR.isUpperTriangular

omit [Fintype n] [DecidableEq n] in
/-- The upper triangular matrices form a closed set. -/
private theorem isClosed_setOf_isUpperTriangular [LinearOrder n] :
    IsClosed {M : Matrix n n ℂ | M.IsUpperTriangular} := by
  have h : {M : Matrix n n ℂ | M.IsUpperTriangular} =
      ⋂ (i : n) (j : n) (_ : j < i), {M : Matrix n n ℂ | M i j = 0} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Iff.rfl
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const

/-- **The QZ decomposition.** Every pair of square complex matrices is simultaneously reduced to
upper triangular form by two unitary matrices.
[GolubVanLoan2013, Theorem 7.7.1]; [HornJohnson2013, Theorem 2.6.1].
Port of `NLAlib.exists_unitary_qz_triangularization`.
Result: qz -/
theorem exists_hasOrthonormalCols_isUpperTriangular_isUpperTriangular
    [LinearOrder n] (A B : Matrix n n ℂ) :
    ∃ Q Z : Matrix n n ℂ, HasOrthonormalCols Q ∧ HasOrthonormalCols Z ∧
      (Qᴴ * A * Z).IsUpperTriangular ∧ (Qᴴ * B * Z).IsUpperTriangular := by
  have hK : IsCompact ({Q : Matrix n n ℂ | HasOrthonormalCols Q} ×ˢ
      {Z : Matrix n n ℂ | HasOrthonormalCols Z}) :=
    isCompact_setOf_hasOrthonormalCols.prod isCompact_setOf_hasOrthonormalCols
  have := isCompact_iff_compactSpace.mp hK
  have hC : IsClosed {x : ℂ × ↥({Q : Matrix n n ℂ | HasOrthonormalCols Q} ×ˢ
      {Z : Matrix n n ℂ | HasOrthonormalCols Z}) |
      (x.2.1.1ᴴ * A * x.2.1.2).IsUpperTriangular ∧
        (x.2.1.1ᴴ * (B + x.1 • (1 : Matrix n n ℂ)) * x.2.1.2).IsUpperTriangular} := by
    refine (isClosed_setOf_isUpperTriangular.preimage ?_).inter
      (isClosed_setOf_isUpperTriangular.preimage ?_)
    · fun_prop
    · fun_prop
  have hev : ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, t ∈ Prod.fst '' {x : ℂ ×
      ↥({Q : Matrix n n ℂ | HasOrthonormalCols Q} ×ˢ {Z : Matrix n n ℂ | HasOrthonormalCols Z}) |
      (x.2.1.1ᴴ * A * x.2.1.2).IsUpperTriangular ∧
        (x.2.1.1ᴴ * (B + x.1 • (1 : Matrix n n ℂ)) * x.2.1.2).IsUpperTriangular} := by
    have hfin : {t : ℂ | -t ∈ spectrum ℂ B}.Finite :=
      (Matrix.finite_spectrum B).preimage neg_injective.injOn
    filter_upwards [nhdsNE_le_cofinite (0 : ℂ) hfin.compl_mem_cofinite] with t ht
    have h1 : IsUnit (algebraMap ℂ (Matrix n n ℂ) (-t) - B) := by
      by_contra h
      exact ht h
    have h2 : B + t • (1 : Matrix n n ℂ) = -(algebraMap ℂ (Matrix n n ℂ) (-t) - B) := by
      rw [Algebra.algebraMap_eq_smul_one, neg_smul]
      abel
    obtain ⟨Q, Z, hQ, hZ, hA', hB'⟩ := exists_isUpperTriangular_of_isUnit_det A
      (h2 ▸ (Matrix.isUnit_iff_isUnit_det _).mp h1.neg)
    exact ⟨(t, ⟨(Q, Z), hQ, hZ⟩), ⟨hA', hB'⟩, rfl⟩
  obtain ⟨⟨t, ⟨⟨Q, Z⟩, hQ, hZ⟩⟩, ⟨hA', hB'⟩, ht⟩ :=
    (isClosedMap_fst_of_compactSpace _ hC).mem_of_tendsto
      (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id) hev
  simp only at ht hA' hB'
  rw [ht, zero_smul, add_zero] at hB'
  exact ⟨Q, Z, hQ, hZ, hA', hB'⟩

end NLAlib
