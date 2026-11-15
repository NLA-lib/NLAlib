/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.FindRitzSolve
public import NLAlib.Matrix.QRIteration.ShiftedQRConjugation

/-!
# Mathematical states of the exact Givens row solve

The row solve factors an upper Hessenberg matrix, solves the triangular row system in
increasing column order, then applies its saved Givens rotations in reverse order. Nonzero
diagonal pivots follow from invertibility of the original matrix.

## Main results

* `NLAlib.ShiftedQR.stepCoefs`: the coefficients saved by each factorization round.
* `NLAlib.ShiftedQR.solvePrefix`: the in-place state of forward substitution.
* `NLAlib.ShiftedQR.reverseRotations_solve`: the exact row solve is multiplication by the inverse.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open scoped Matrix

/-- Coefficients of the actual adjacent-row rotation at factorization step $k$. -/
noncomputable def stepCoefs {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ × ℂ :=
  if h : k + 1 < n then
    givensCoeffs ((givensHessenbergState D k).2 ⟨k, by omega⟩ ⟨k, by omega⟩)
      ((givensHessenbergState D k).2 ⟨k + 1, h⟩ ⟨k, by omega⟩)
  else (1, 0)

/-- A factorization step is the Givens matrix with the saved coefficients. -/
theorem stepCoefs_givens {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (hk : k + 1 < n) :
    givensHessenbergStep (givensHessenbergState D k).2 k =
      givens (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ (stepCoefs D k).1 (stepCoefs D k).2 := by
  rw [givensHessenbergStep_of_lt _ (by omega) hk (by omega), stepCoefs, dif_pos hk]

/-- Multiplication by the saved rotation advances the triangular factorization state. -/
theorem stepCoefs_mul_state {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (hk : k + 1 < n) :
    givens (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ (stepCoefs D k).1 (stepCoefs D k).2 *
      (givensHessenbergState D k).2 = (givensHessenbergState D (k + 1)).2 := by
  rw [← stepCoefs_givens D hk, givensHessenbergState_succ_snd]

/-- The last adjacent-row rotation completes the triangular factor. -/
theorem factorState_last {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (givensHessenbergState D n).2 = givensHessenbergR D := by
  rw [givensHessenbergR, givensHessenbergState_succ_snd, givensHessenbergStep_last,
    Matrix.one_mul]

/-- Invertibility of the original Hessenberg matrix supplies every nonzero division pivot.
[GolubVanLoan2013, §5.2.5]. -/
theorem factor_diagonal_ne_zero {n : ℕ} {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hD : IsUpperHessenberg D) (hdet : D.det ≠ 0) : ∀ i, givensHessenbergR D i i ≠ 0 := by
  have hinj : Function.Injective D.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det D).mpr (isUnit_iff_ne_zero.mpr hdet))
  exact (forall_givensHessenbergR_apply_self_ne_zero_iff hD le_rfl).mpr hinj

/-- The in-place row vector has solved entries before $k$ and its original entries from $k$
onwards. The triangular solve itself is the existing mathematical forward substitution. -/
noncomputable def solvePrefix {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (k : ℕ) (i : Fin n) : ℂ :=
  if i < k then rowForwardSubstState R v k i else v i

/-- Before the first column, the in-place vector is the supplied row. -/
@[simp] theorem solvePrefix_zero {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    solvePrefix R v 0 = v := by
  funext i
  simp [solvePrefix]

/-- At a column not yet processed, the original right-hand side is still present. -/
theorem solvePrefix_current {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (j : Fin n) : solvePrefix R v j j = v j := by
  simp [solvePrefix]

/-- Solving one column is one mathematical entry update. -/
theorem solvePrefix_succ {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (j : Fin n) :
    solvePrefix R v (j + 1) = Function.update (solvePrefix R v j) j
      ((v j - ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j),
        solvePrefix R v j i * R i j) / R j j) := by
  funext i
  by_cases hij : i = j
  · subst i
    simp only [Function.update_self, solvePrefix, Nat.lt_succ_self, ↓reduceIte,
      rowForwardSubstState]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    have hij := (Finset.mem_filter.mp hi).2
    simp only [hij, if_pos]
  · have hval : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rw [Function.update_of_ne hij]
    by_cases hi : (i : ℕ) < j
    · simp [solvePrefix, hi, show (i : ℕ) < j + 1 by omega,
        rowForwardSubstState, hval]
    · simp [solvePrefix, hi, show ¬(i : ℕ) < j + 1 by omega]

/-- Completing every column gives the established triangular row solve. -/
theorem solvePrefix_last {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    solvePrefix R v n = rowForwardSubst R v := by
  funext i
  simp [solvePrefix, rowForwardSubst, i.isLt]

/-- The complex column sum used by forward substitution after $t$ products. -/
noncomputable def columnProductSum {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (j : Fin n) (t : ℕ) : ℂ :=
  ∑ i : Fin n, if (i : ℕ) < t then v i * R i j else 0

/-- There are no products before the first residual update. -/
@[simp] theorem columnProductSum_zero {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (j : Fin n) : columnProductSum R v j 0 = 0 := by
  simp [columnProductSum]

/-- One more scalar product extends the mathematical column sum. -/
theorem columnProductSum_succ {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (j : Fin n) {t : ℕ} (ht : t < n) :
    columnProductSum R v j (t + 1) = columnProductSum R v j t + v ⟨t, ht⟩ * R ⟨t, ht⟩ j := by
  unfold columnProductSum
  have hterm (i : Fin n) : (if (i : ℕ) < t + 1 then v i * R i j else 0) =
      (if (i : ℕ) < t then v i * R i j else 0) +
        if i = ⟨t, ht⟩ then v i * R i j else 0 := by
    by_cases hi : (i : ℕ) < t
    · have hne : i ≠ ⟨t, ht⟩ := fun h => by rw [h] at hi; simp at hi
      simp [hi, hne, show (i : ℕ) < t + 1 by omega]
    · by_cases he : i = ⟨t, ht⟩
      · subst i
        simp
      · have hn : ¬(i : ℕ) < t + 1 := fun h => he (Fin.ext (show (i : ℕ) = t by omega))
        simp [hi, he, hn]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
  simp

/-- The accumulator after the first $t$ products of column $j$. -/
noncomputable def residualPrefix {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (j : Fin n) (t : ℕ) : ℂ := v j - columnProductSum R v j t

/-- Subtracting one complex product advances the residual accumulator. -/
theorem residualPrefix_succ {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (j : Fin n) {t : ℕ} (ht : t < n) :
    residualPrefix R v j (t + 1) = residualPrefix R v j t - v ⟨t, ht⟩ * R ⟨t, ht⟩ j := by
  rw [residualPrefix, columnProductSum_succ R v j ht, residualPrefix]
  ring

/-- Dividing the completed residual is the next forward-substitution coordinate. -/
theorem solvePrefix_residual {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (j : Fin n) :
    solvePrefix R v (j + 1) = Function.update (solvePrefix R v j) j
      (residualPrefix R (solvePrefix R v j) j j / R j j) := by
  rw [solvePrefix_succ]
  congr 1
  rw [residualPrefix, solvePrefix_current]
  simp only [columnProductSum, Finset.sum_filter]

/-- One saved factorization rotation acting on a row vector. -/
noncomputable def reverseRotationStep {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (k : ℕ) : Fin n → ℂ :=
  v ᵥ* givensHessenbergStep (givensHessenbergState D k).2 k

/-- After $t$ reverse rotations, the next index is $k-1-t$. -/
noncomputable def reverseRotations {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (v : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0 => v
  | t + 1 => reverseRotationStep D (reverseRotations D k v t) (k - 1 - t)

/-- Completed reverse rotations and the remaining suffix are the same reverse fold. -/
theorem reverseRotations_foldl {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (v : Fin n → ℂ) : ∀ t ≤ k,
    (List.range (k - t)).reverse.foldl (reverseRotationStep D) (reverseRotations D k v t) =
      (List.range k).reverse.foldl (reverseRotationStep D) v := by
  intro t
  induction t with
  | zero => intro _; simp [reverseRotations]
  | succ t ih =>
    intro ht
    rw [← ih (by omega), show k - t = (k - (t + 1)) + 1 by omega, List.range_succ,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons]
    simp only [reverseRotations]
    rw [show k - (t + 1) = k - 1 - t by omega]

/-- A zero diagonal of the computed triangular factor certifies a singular original matrix. -/
theorem factor_singular_of_zero_diagonal {n : ℕ}
    {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hD : IsUpperHessenberg D)
    (i : Fin (n + 1)) (hi : givensHessenbergR D i i = 0) : D.det = 0 := by
  have htri : (givensHessenbergR D).IsUpperTriangular :=
    isUpperTrapezoidal_iff_isUpperTriangular.mp (isUpperTrapezoidal_givensHessenbergR hD)
  have hz : (givensHessenbergR D).det = 0 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hfac : givensHessenbergQ D * givensHessenbergR D = D :=
    givensHessenbergState_fst_mul_snd D _
  rw [← hfac, Matrix.det_mul, hz, mul_zero]

/-- Nonzero computed triangular pivots suffice for the reverse-rotation inverse identity.
These pivots are established by the actual checks in the program. -/
theorem reverseRotations_solve_of_diagonal {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hD : IsUpperHessenberg D)
    (hdiag : ∀ i, givensHessenbergR D i i ≠ 0) (v : Fin (n + 1) → ℂ) :
    reverseRotations D n (rowForwardSubst (givensHessenbergR D) v) n = v ᵥ* D⁻¹ := by
  rw [rowForwardSubst_eq
    (isUpperTrapezoidal_iff_isUpperTriangular.mp (isUpperTrapezoidal_givensHessenbergR hD))
    hdiag, vecMul_inv_eq_givens D v,
    vecMul_conjTranspose_givensHessenbergQ_eq_foldl D (v ᵥ* (givensHessenbergR D)⁻¹)]
  have h := reverseRotations_foldl D n (v ᵥ* (givensHessenbergR D)⁻¹) n le_rfl
  rw [Nat.sub_self, List.range_zero, List.reverse_nil, List.foldl_nil] at h
  rw [h, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.foldl_cons]
  simp only [givensHessenbergStep_last, Matrix.vecMul_one]
  rfl

/-- Under the Hessenberg and invertibility hypotheses, forward substitution followed by all
saved reverse rotations computes the row multiplied by the original inverse.
[GolubVanLoan2013, §5.2.5]. -/
theorem reverseRotations_solve {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hD : IsUpperHessenberg D) (hdet : D.det ≠ 0) (v : Fin (n + 1) → ℂ) :
    reverseRotations D n (rowForwardSubst (givensHessenbergR D) v) n = v ᵥ* D⁻¹ := by
  exact reverseRotations_solve_of_diagonal D hD (factor_diagonal_ne_zero hD hdet) v

end NLAlib.ShiftedQR
