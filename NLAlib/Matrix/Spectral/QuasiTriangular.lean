/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Hessenberg

/-!
# Upper quasi-triangular matrices

A matrix indexed by `Fin k` is upper quasi-triangular if it is upper Hessenberg and no two
consecutive subdiagonal entries are nonzero: it is block upper triangular with diagonal blocks of
size one and two. This is the shape of the real Schur form and of the first factor of the real QZ
decomposition. The predicate is preserved by multiplication on the left by an upper triangular
matrix and by assembling blocks.

## Main definitions

* `NLAlib.IsUpperQuasiTriangular`: upper Hessenberg with no two consecutive nonzero subdiagonal
  entries.

## Main results

* `Matrix.IsUpperTriangular.isUpperQuasiTriangular`,
  `Matrix.IsUpperTriangular.mul_isUpperQuasiTriangular`.
* `NLAlib.IsUpperQuasiTriangular.submatrix_fromBlocks`,
  `Matrix.IsUpperTriangular.submatrix_fromBlocks`: a block upper triangular matrix with
  quasi-triangular (respectively triangular) diagonal blocks.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {R : Type*} {k : ℕ}

/-- A matrix indexed by `Fin k` is **upper quasi-triangular** if it is upper Hessenberg and no
two consecutive subdiagonal entries are nonzero: it is block upper triangular with diagonal
blocks of size at most two. [HornJohnson2013, §2.3].
Port of `NLAlib.IsUpperQuasiTriangular`. -/
def IsUpperQuasiTriangular [Zero R] (T : Matrix (Fin k) (Fin k) R) : Prop :=
  IsUpperHessenberg T ∧
    ∀ i j l : Fin k, (j : ℕ) + 1 = (i : ℕ) → (l : ℕ) + 1 = (j : ℕ) → T i j = 0 ∨ T j l = 0

/-- An upper triangular matrix is upper quasi-triangular.
Port of `NLAlib.isUpperQuasiTriangular_of_isUpperTriangular`. -/
theorem _root_.Matrix.IsUpperTriangular.isUpperQuasiTriangular [Zero R]
    {T : Matrix (Fin k) (Fin k) R} (hT : T.IsUpperTriangular) : IsUpperQuasiTriangular T :=
  ⟨hT.isUpperHessenberg, fun i j _ hij _ => Or.inl (hT (show j < i from Fin.lt_def.mpr (by omega)))⟩

private theorem mul_apply_of_succ_eq [Semiring R] {U T : Matrix (Fin k) (Fin k) R}
    (hU : U.IsUpperTriangular) (hT : IsUpperQuasiTriangular T) {i j : Fin k}
    (hij : (j : ℕ) + 1 = (i : ℕ)) : (U * T) i j = U i i * T i j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hli => ?_) (fun h => absurd (Finset.mem_univ i) h)
  by_cases hlt : l < i
  · rw [hU hlt, zero_mul]
  · rw [hT.1 l j (by have := Fin.val_ne_of_ne hli; have := Fin.lt_def.not.mp hlt; omega),
      mul_zero]

/-- An upper triangular matrix times an upper quasi-triangular one is upper quasi-triangular.
Port of `NLAlib.IsUpperQuasiTriangular.upperTriangular_mul`. -/
theorem _root_.Matrix.IsUpperTriangular.mul_isUpperQuasiTriangular [Semiring R]
    {U T : Matrix (Fin k) (Fin k) R} (hU : U.IsUpperTriangular)
    (hT : IsUpperQuasiTriangular T) : IsUpperQuasiTriangular (U * T) := by
  refine ⟨IsUpperHessenberg.isUpperTriangular_mul hU hT.1, fun i j l hij hjl => ?_⟩
  rw [mul_apply_of_succ_eq hU hT hij, mul_apply_of_succ_eq hU hT hjl]
  rcases hT.2 i j l hij hjl with h | h
  · exact Or.inl (by rw [h, mul_zero])
  · exact Or.inr (by rw [h, mul_zero])

/-- A matrix of size at most two is upper quasi-triangular. -/
theorem isUpperQuasiTriangular_of_le_two [Zero R] (hk : k ≤ 2)
    (T : Matrix (Fin k) (Fin k) R) : IsUpperQuasiTriangular T :=
  ⟨fun i j h => by have := i.isLt; omega, fun i j l h₁ h₂ => by have := i.isLt; omega⟩

/-! ### Block triangular matrices -/

/-- The matrix with blocks `S`, `C`, `D`, `T`, indexed by `Fin (p + q)`. -/
private def finBlocks {p q : ℕ} (S : Matrix (Fin p) (Fin p) R) (C : Matrix (Fin p) (Fin q) R)
    (D : Matrix (Fin q) (Fin p) R) (T : Matrix (Fin q) (Fin q) R) :
    Matrix (Fin (p + q)) (Fin (p + q)) R :=
  (Matrix.fromBlocks S C D T).submatrix finSumFinEquiv.symm finSumFinEquiv.symm


section finBlocks

variable {p q : ℕ} {S : Matrix (Fin p) (Fin p) R} {C : Matrix (Fin p) (Fin q) R}
  {D : Matrix (Fin q) (Fin p) R} {T : Matrix (Fin q) (Fin q) R}

private theorem finBlocks_castAdd_castAdd (i j : Fin p) :
    finBlocks S C D T (Fin.castAdd q i) (Fin.castAdd q j) = S i j := by
  simp [finBlocks]

private theorem finBlocks_castAdd_natAdd (i : Fin p) (j : Fin q) :
    finBlocks S C D T (Fin.castAdd q i) (Fin.natAdd p j) = C i j := by
  simp [finBlocks]

private theorem finBlocks_natAdd_castAdd (i : Fin q) (j : Fin p) :
    finBlocks S C D T (Fin.natAdd p i) (Fin.castAdd q j) = D i j := by
  simp [finBlocks]

private theorem finBlocks_natAdd_natAdd (i j : Fin q) :
    finBlocks S C D T (Fin.natAdd p i) (Fin.natAdd p j) = T i j := by
  simp [finBlocks]

/-- **A block upper triangular matrix with upper quasi-triangular diagonal blocks is upper
quasi-triangular**, the blocks being placed in order along `Fin (p + q)`.
Port of `NLAlib.isUpperQuasiTriangular_of_small_leading_block`, there for a leading block of size
at most two. -/
theorem IsUpperQuasiTriangular.submatrix_fromBlocks [Zero R] (hS : IsUpperQuasiTriangular S)
    (hT : IsUpperQuasiTriangular T) (C : Matrix (Fin p) (Fin q) R) :
    IsUpperQuasiTriangular
      ((Matrix.fromBlocks S C 0 T).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  change IsUpperQuasiTriangular (finBlocks S C 0 T)
  constructor
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro h
    · rw [finBlocks_castAdd_castAdd]
      exact hS.1 i j (by simpa only [Fin.val_castAdd] using h)
    · have := i.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h
      omega
    · rw [finBlocks_natAdd_castAdd, Matrix.zero_apply]
    · rw [finBlocks_natAdd_natAdd]
      exact hT.1 i j (by simp only [Fin.val_natAdd] at h; omega)
  · intro i j l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;> intro h₁ h₂
    · rw [finBlocks_castAdd_castAdd, finBlocks_castAdd_castAdd]
      exact hS.2 i j l (by simpa only [Fin.val_castAdd] using h₁)
        (by simpa only [Fin.val_castAdd] using h₂)
    · have := j.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h₂
      omega
    · have := i.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h₁
      omega
    · have := i.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h₁
      omega
    · exact Or.inl (by rw [finBlocks_natAdd_castAdd, Matrix.zero_apply])
    · exact Or.inl (by rw [finBlocks_natAdd_castAdd, Matrix.zero_apply])
    · exact Or.inr (by rw [finBlocks_natAdd_castAdd, Matrix.zero_apply])
    · rw [finBlocks_natAdd_natAdd, finBlocks_natAdd_natAdd]
      exact hT.2 i j l (by simp only [Fin.val_natAdd] at h₁; omega)
        (by simp only [Fin.val_natAdd] at h₂; omega)

/-- A block upper triangular matrix with upper triangular diagonal blocks is upper triangular,
the blocks being placed in order along `Fin (p + q)`. -/
theorem _root_.Matrix.IsUpperTriangular.submatrix_fromBlocks [Zero R] (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (C : Matrix (Fin p) (Fin q) R) :
    ((Matrix.fromBlocks S C 0 T).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm).IsUpperTriangular := by
  change (finBlocks S C 0 T).IsUpperTriangular
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro h
  · rw [finBlocks_castAdd_castAdd]
    exact hS (show j < i from h)
  · have := i.isLt
    have h' := Fin.lt_def.mp (show Fin.natAdd p j < Fin.castAdd q i from h)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · rw [finBlocks_natAdd_castAdd, Matrix.zero_apply]
  · rw [finBlocks_natAdd_natAdd]
    have h' := Fin.lt_def.mp (show Fin.natAdd p j < Fin.natAdd p i from h)
    simp only [Fin.val_natAdd] at h'
    exact hT (show j < i from Fin.lt_def.mpr (by omega))

end finBlocks

end NLAlib
