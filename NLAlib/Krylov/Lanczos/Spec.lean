/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlib.Ops.Catalog.Operator

/-!
# Packed outputs of Lanczos over operations

Basis columns and coefficients are compared directly with the existing pure Lanczos
recurrence. The coefficient prefix is shared by ordinary and fully reorthogonalized programs;
additional coefficient storage is allowed. For Hermitian matrices the basis is canonical.

## Main results

* `NLAlib.Krylov.Lanczos.Output` specifies the stored basis, coefficients and input norm.
* `NLAlib.Krylov.Lanczos.Output.basisMatrix_succ_eq_arnoldiMatrix` identifies the canonical basis.
* `NLAlib.Krylov.Lanczos.basisMatrix` and `NLAlib.Krylov.Lanczos.tridiagonalMatrix` decode
  physically stored prefixes.
* `NLAlib.Krylov.Lanczos.Output.hasOrthonormalCols_basisMatrix_iff` handles the active grade.
* `NLAlib.Krylov.Lanczos.Output.tridiagonalMatrix_eq` identifies the stored compression.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

/-- Decode the first `q` columns of a column-major stored Lanczos basis with vector length `n`.
This is a packing view of the actual words, with the existing total `Ops.vec` convention for
missing entries. Output contracts identify every admitted prefix with the canonical basis. -/
def basisMatrix {K : Type} [Inhabited K] (dec : K → ℝ) (n : ℕ) (vs : List K) (q : ℕ) :
    Matrix (Fin n) (Fin q) ℝ :=
  Matrix.of fun i j => dec (vec vs (j * n + i))

/-- Decode a symmetric tridiagonal prefix from the actual stored coefficient words. Alpha
starts at zero and beta at `cap`; $q \le \mathrm{cap}$ admits every referenced coefficient. The same
prefix layout is used by ordinary and fully reorthogonalized Lanczos. -/
def tridiagonalMatrix {K : Type} [Inhabited K] (dec : K → ℝ) (cap : ℕ) (cs : List K)
    (q : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i j =>
    if i = j then dec (vec cs i)
    else if (i : ℕ) = j + 1 then dec (vec cs (cap + i))
    else if (j : ℕ) = i + 1 then dec (vec cs (cap + j))
    else 0

/-- Packed Lanczos output: column-major basis through the final state, alpha coefficients,
beta coefficients starting at `cap`, and input norm at `2*cap+1`.
[Paige1972, §2]; [Saad2011, §6.6]. -/
structure Output {K : Type} [Inhabited K] (dec : K → ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (cap : ℕ) (vs cs : List K) : Prop where
  /-- Every requested basis column, including zero columns after breakdown. -/
  basis : ∀ j ≤ cap, ∀ i : Fin n,
    dec (vec vs (j * n + i)) = (lanczosState A b j).cur i
  /-- Every diagonal coefficient. -/
  alpha : ∀ j < cap, dec (vec cs j) = lanczosAlpha A (lanczosState A b j)
  /-- Every coupling coefficient, including the initial zero. -/
  beta : ∀ j ≤ cap, dec (vec cs (cap + j)) = (lanczosState A b j).beta
  /-- The norm used to normalize the initial input. -/
  inputNorm : dec (vec cs (2 * cap + 1)) = ‖WithLp.toLp 2 b‖

/-- For a Hermitian matrix, the decoded stored basis is the canonical Arnoldi/Lanczos basis,
including zero columns after exact breakdown. [Saad2011, §6.6]. -/
theorem Output.basisMatrix_succ_eq_arnoldiMatrix {K : Type} [Inhabited K] {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.IsHermitian) :
    basisMatrix dec n vs (cap + 1) = arnoldiMatrix A b (cap + 1) := by
  rw [← hA.lanczosMatrix_eq_arnoldiMatrix]
  funext i j
  exact h.basis j (by omega) i

/-- Every stored prefix is the corresponding canonical basis, including prefixes that
contain initialized zero columns after breakdown. [Saad2011, §6.6]. -/
theorem Output.basisMatrix_eq_arnoldiMatrix {K : Type} [Inhabited K] {dec : K → ℝ}
    {n cap q : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.IsHermitian) (hq : q ≤ cap + 1) :
    basisMatrix dec n vs q = arnoldiMatrix A b q := by
  have he := h.basisMatrix_succ_eq_arnoldiMatrix hA
  ext i j
  calc
    basisMatrix dec n vs q i j =
        arnoldiMatrix A b (cap + 1) i (Fin.castLE hq j) :=
      congrFun (congrFun he i) (Fin.castLE hq j)
    _ = arnoldiMatrix A b q i j :=
      congrFun (congrFun (arnoldiMatrix_submatrix_castLE A b hq) i) j

/-- A stored prefix has orthonormal columns exactly up to the input Krylov grade. Zero tails
past breakdown are excluded by this equivalence. [Saad2003, Proposition 6.4]. -/
theorem Output.hasOrthonormalCols_basisMatrix_iff {K : Type} [Inhabited K] {dec : K → ℝ}
    {n cap q : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.IsHermitian) (hq : q ≤ cap + 1) :
    HasOrthonormalCols (basisMatrix dec n vs q) ↔ q ≤ krylovGrade A b := by
  rw [h.basisMatrix_eq_arnoldiMatrix hA hq]
  exact hasOrthonormalCols_arnoldiMatrix_iff

/-- Every stored basis prefix spans its Krylov space, even after exact breakdown and for
zero input. [Saad2003, Proposition 6.4]. -/
theorem Output.range_basisMatrix {K : Type} [Inhabited K] {dec : K → ℝ}
    {n cap q : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.IsHermitian) (hq : q ≤ cap + 1) :
    LinearMap.range (basisMatrix dec n vs q).mulVecLin = krylovSpace A b q := by
  rw [h.basisMatrix_eq_arnoldiMatrix hA hq]
  exact range_arnoldiMatrix A b q

/-- The tridiagonal reconstructed from actual coefficient words is the pure recurrence's
tridiagonal, for every stored prefix and without a nonbreakdown assumption. -/
theorem Output.tridiagonalMatrix_eq_lanczosTridiagonal {K : Type} [Inhabited K]
    {dec : K → ℝ} {n cap q : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    {vs cs : List K} (h : Output dec A b cap vs cs) (hq : q ≤ cap) :
    tridiagonalMatrix dec cap cs q = lanczosTridiagonal A b q := by
  ext i j
  simp only [tridiagonalMatrix, lanczosTridiagonal, Matrix.of_apply,
    RCLike.ofReal_real_eq_id, id]
  split_ifs
  · exact h.alpha i (lt_of_lt_of_le i.isLt hq)
  · exact h.beta i (Nat.le_of_lt (lt_of_lt_of_le i.isLt hq))
  · exact h.beta j (Nat.le_of_lt (lt_of_lt_of_le j.isLt hq))
  · rfl

/-- The actual stored coefficients form the compression of the input Hermitian matrix to
the actual stored basis prefix. The identity holds for zero input and after exact breakdown;
orthonormality is a separate grade-bounded fact. [Saad2003, Theorem 6.19]. -/
theorem Output.tridiagonalMatrix_eq {K : Type} [Inhabited K] {dec : K → ℝ}
    {n cap q : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.IsHermitian) (hq : q ≤ cap) :
    tridiagonalMatrix dec cap cs q =
      (basisMatrix dec n vs q)ᴴ * A * basisMatrix dec n vs q := by
  rw [h.tridiagonalMatrix_eq_lanczosTridiagonal hq, hA.lanczosTridiagonal_eq,
    h.basisMatrix_eq_arnoldiMatrix hA (hq.trans (Nat.le_succ cap))]

end NLAlib.Krylov.Lanczos
