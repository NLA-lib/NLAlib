/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Basis
public import NLAlib.Krylov.Lanczos.Reorth.Exact

/-!
# Spectral consequences of stored fully reorthogonalized Lanczos output

The exact reorthogonalized solver returns the ordinary canonical Lanczos basis and
tridiagonal coefficient prefix. The shared packed-output compression API transfers pure
Ritz convergence to those actual words. Extra preorthogonalization norm coefficients remain
part of the original output contract and resource accounting.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.runs_solve_basis`: canonical stored basis including zero tails.
* `NLAlib.Krylov.Lanczos.Reorth.runs_solve_ritz`: total execution and explicit Ritz convergence.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- For a Hermitian matrix, the capped fully reorthogonalized Lanczos program stores its
canonical Arnoldi basis through the final requested column, including zero tails after breakdown.
[Saad2011, §6.6]. -/
theorem runs_solve_basis {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hHerm : A.IsHermitian)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2]) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [B, V, C]) μ
      (solveCount n cap) (solvePeak W n cap)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        (fun i : Fin n => fun j : Fin (cap + 1) => dec (vec vs (j * n + i))) =
          arnoldiMatrix A (decv dec n bs) (cap + 1)) := by
  refine (runs_solve hS hM hB hok hA hCmp hHerm W hBV hBC hVC hl hb hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, vs, cs, hv, hc, hout⟩
  exact ⟨hpos, vs, cs, hv, hc, (hout.toOrdinary hHerm).basisMatrix_succ_eq_arnoldiMatrix hHerm⟩

/-- Exact scalar, BLAS, matvec and comparison contracts imply total successful execution
of fully reorthogonalized Lanczos and the Kaniel–Paige–Saad convergence bound for the
largest eigenvalue of an actual
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
    (hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2])
    (hq : q + 1 ≤ cap) (hgrade : q + 1 ≤ krylovGrade A (decv dec n bs))
    {a c : ℝ} (hac : a < c) (hc : c < eigenvalue A 0)
    (hs : spectrum ℝ A ⊆ Set.Icc a c ∪ {eigenvalue A 0})
    (hstart : 0 < (spectralMeasure A (decv dec n bs)).real {eigenvalue A 0}) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [B, V, C]) μ
      (solveCount n cap) (solvePeak W n cap)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) cap vs cs ∧
        eigenvalue A 0 - eigenvalue (tridiagonalMatrix dec cap cs (q + 1)) 0 ≤
          4 * (eigenvalue A 0 - a) * spectralTangentSq A (decv dec n bs) (eigenvalue A 0) *
            ((Real.sqrt (eigenvalue A 0 - a) - Real.sqrt (eigenvalue A 0 - c)) /
              (Real.sqrt (eigenvalue A 0 - a) + Real.sqrt (eigenvalue A 0 - c))) ^ (2 * q)) := by
  refine (runs_solve hS hM hB hok hA hCmp hHerm W hBV hBC hVC hl hb hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, vs, cs, hv, hcs, hout⟩
  exact ⟨hpos, vs, cs, hv, hcs, hout,
    (hout.toOrdinary hHerm).eigenvalue_sub_eigenvalue_tridiagonalMatrix_le
      hHerm hq hgrade hac hc hs hstart⟩

end NLAlib.Krylov.Lanczos.Reorth
