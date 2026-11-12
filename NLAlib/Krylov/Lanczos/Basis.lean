/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Exact
public import NLAlib.Krylov.Eigenvalues.Ritz

/-!
# The computed Lanczos basis

The output contract identifies every stored column with the existing Lanczos recurrence,
including initialized zero columns after breakdown. Hermitian symmetry then identifies those
same stored words with the canonical Arnoldi basis, by the pure mathematical bridge.

## Main results

* `NLAlib.Krylov.Lanczos.Output.eigenvalue_sub_eigenvalue_tridiagonalMatrix_le` transfers
  Kaniel–Paige–Saad convergence to actual stored coefficients.
* `NLAlib.Krylov.Lanczos.runs_solve_ritz` includes total program success and that bound.

* `NLAlib.Krylov.Lanczos.runs_solve_basis` identifies the actual stored basis, preserving the
  total solver's operation and workspace budgets without replaying its program proof.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

/-- The largest eigenvalue of an active stored tridiagonal prefix satisfies the classical
Kaniel–Paige–Saad bound. The Hermitian input has all other spectral values in `[a,c]` below
the largest eigenvalue, and the start has positive spectral mass at that largest value.
The prefix contains `q+1` columns, fits the stored cap, and does not exceed the Krylov grade.
[Saad2011, Theorem 6.4]. -/
theorem Output.eigenvalue_sub_eigenvalue_tridiagonalMatrix_le
    {K : Type} [Inhabited K] {dec : K → ℝ} {n cap q : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.IsHermitian)
    (hq : q + 1 ≤ cap) (hgrade : q + 1 ≤ krylovGrade A b)
    {a c : ℝ} (hac : a < c) (hc : c < eigenvalue A 0)
    (hs : spectrum ℝ A ⊆ Set.Icc a c ∪ {eigenvalue A 0})
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) :
    eigenvalue A 0 - eigenvalue (tridiagonalMatrix dec cap cs (q + 1)) 0 ≤
      4 * (eigenvalue A 0 - a) * spectralTangentSq A b (eigenvalue A 0) *
        ((Real.sqrt (eigenvalue A 0 - a) - Real.sqrt (eigenvalue A 0 - c)) /
          (Real.sqrt (eigenvalue A 0 - a) + Real.sqrt (eigenvalue A 0 - c))) ^ (2 * q) := by
  rw [h.tridiagonalMatrix_eq hA hq]
  exact hA.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le hac hc hs hb
    ((h.hasOrthonormalCols_basisMatrix_iff hA (hq.trans (Nat.le_succ cap))).mpr hgrade)
    (h.range_basisMatrix hA (hq.trans (Nat.le_succ cap)))

/-- For a positive semidefinite input and a start with positive mass in its top eigenspace,
the largest eigenvalue of an active stored tridiagonal prefix has a gap-free bound for every
accuracy parameter strictly between zero and one. The prefix has `q+1` columns and lies
within both the cap and the Krylov grade. [MuscoMusco2015, Theorem 1]. -/
theorem Output.eigenvalue_sub_eigenvalue_tridiagonalMatrix_le_add
    {K : Type} [Inhabited K] {dec : K → ℝ} {n cap q : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.PosSemidef)
    (hq : q + 1 ≤ cap) (hgrade : q + 1 ≤ krylovGrade A b)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) :
    eigenvalue A 0 - eigenvalue (tridiagonalMatrix dec cap cs (q + 1)) 0 ≤
      ε * eigenvalue A 0 + 4 * Real.exp (-4 * q * Real.sqrt ε) * eigenvalue A 0 *
        spectralTangentSq A b (eigenvalue A 0) := by
  rw [h.tridiagonalMatrix_eq hA.isHermitian hq]
  exact hA.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_add hε₀ hε₁ hb
    ((h.hasOrthonormalCols_basisMatrix_iff hA.isHermitian
      (hq.trans (Nat.le_succ cap))).mpr hgrade)
    (h.range_basisMatrix hA.isHermitian (hq.trans (Nat.le_succ cap)))

/-- For a positive semidefinite input and a start with positive top spectral mass, an active
stored prefix of `q+1` columns with $q \ge 1$ has the deterministic squared-logarithmic
Kuczyński–Woźniakowski bound. The prefix fits both the cap and the input Krylov grade.
[KuczynskiWozniakowski1992, Theorem 4.2]. -/
theorem Output.eigenvalue_sub_eigenvalue_tridiagonalMatrix_le_div_sq
    {K : Type} [Inhabited K] {dec : K → ℝ} {n cap q : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.PosSemidef)
    (hq : q + 1 ≤ cap) (hgrade : q + 1 ≤ krylovGrade A b) (hqpos : 1 ≤ q)
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) :
    eigenvalue A 0 - eigenvalue (tridiagonalMatrix dec cap cs (q + 1)) 0 ≤
      4 * eigenvalue A 0 *
        (1 + Real.log (1 + spectralTangentSq A b (eigenvalue A 0)) / Real.log 2) ^ 2 / q ^ 2 := by
  rw [h.tridiagonalMatrix_eq hA.isHermitian hq]
  exact hA.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq hb
    ((h.hasOrthonormalCols_basisMatrix_iff hA.isHermitian
      (hq.trans (Nat.le_succ cap))).mpr hgrade) hqpos
    (h.range_basisMatrix hA.isHermitian (hq.trans (Nat.le_succ cap)))

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- For a Hermitian matrix, the concrete capped Lanczos program stores its canonical Arnoldi
basis through the final requested column, including zero tails after breakdown.
[Saad2011, §6.6]. -/
theorem runs_solve_basis {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hHerm : A.IsHermitian)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2]) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [B, V, C]) μ
      (solveCount n cap) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        (fun i : Fin n => fun j : Fin (cap + 1) => dec (vec vs (j * n + i))) =
          arnoldiMatrix A (decv dec n bs) (cap + 1)) := by
  refine (runs_solve hS hM hB hok hA hCmp W hBV hBC hVC hl hb hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, vs, cs, hv, hc, hout⟩
  exact ⟨hpos, vs, cs, hv, hc, hout.basisMatrix_succ_eq_arnoldiMatrix hHerm⟩

/-- Exact scalar, BLAS, matvec and comparison contracts imply total successful Lanczos
execution and the Kaniel–Paige–Saad convergence bound for the largest eigenvalue of an actual
stored tridiagonal prefix. The Hermitian input has its other spectral values in `[a,c]` below
the largest eigenvalue, the start has positive mass in its top eigenspace, and the prefix of
`q+1` columns fits the cap and Krylov grade. The program returns basis and coefficients; this
conclusion concerns the mathematical eigenvalue of those coefficients, not an executed
eigensolver. The original operation and scratch budgets are retained.
[Saad2011, Theorem 6.4]. -/
theorem runs_solve_ritz {M : Machine K} {dec : K → ℝ} {n cap q : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hHerm : A.IsHermitian)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2])
    (hq : q + 1 ≤ cap) (hgrade : q + 1 ≤ krylovGrade A (decv dec n bs))
    {a c : ℝ} (hac : a < c) (hc : c < eigenvalue A 0)
    (hs : spectrum ℝ A ⊆ Set.Icc a c ∪ {eigenvalue A 0})
    (hstart : 0 < (spectralMeasure A (decv dec n bs)).real {eigenvalue A 0}) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [B, V, C]) μ
      (solveCount n cap) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) cap vs cs ∧
        eigenvalue A 0 - eigenvalue (tridiagonalMatrix dec cap cs (q + 1)) 0 ≤
          4 * (eigenvalue A 0 - a) * spectralTangentSq A (decv dec n bs) (eigenvalue A 0) *
            ((Real.sqrt (eigenvalue A 0 - a) - Real.sqrt (eigenvalue A 0 - c)) /
              (Real.sqrt (eigenvalue A 0 - a) + Real.sqrt (eigenvalue A 0 - c))) ^ (2 * q)) := by
  refine (runs_solve hS hM hB hok hA hCmp W hBV hBC hVC hl hb hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, vs, cs, hv, hcs, hout⟩
  exact ⟨hpos, vs, cs, hv, hcs, hout,
    hout.eigenvalue_sub_eigenvalue_tridiagonalMatrix_le hHerm hq hgrade hac hc hs hstart⟩

end NLAlib.Krylov.Lanczos
