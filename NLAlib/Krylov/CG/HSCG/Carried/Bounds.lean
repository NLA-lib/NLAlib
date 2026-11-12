/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Solve

/-!
# Chebyshev convergence of the stored early-exit CG output

The exact carried-rho solver accepts every cap and stops at exact convergence. Its stored
output inherits the pure CG energy-error bound at the smaller of the cap and Krylov grade.
The original total conditional run budgets are retained; this is not a new canonical
Algorithm certificate or a rounded-arithmetic result.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.runs_solve_chebyshev`: spectral-interval convergence of
  the stored output for every cap, including zero and caps exceeding the Krylov grade.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Under exact scalar, BLAS, matvec and comparison contracts, SPD CG successfully returns
a stored iterate for every cap. If the spectrum lies in a positive interval `[a, a']` and
`solution` solves the input system, its squared energy error is at most
`4 * rho ^ (2 * q)` times the initial squared energy error, where
`rho = (sqrt (a' / a) - 1) / (sqrt (a' / a) + 1)` and `q` is the smaller of cap and
initial residual Krylov grade. The original operation and scratch bounds are retained.
[Saad2003, Theorem 6.29]. -/
theorem runs_solve_chebyshev {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) (W : Op → List ℕ → ℕ)
    {τ : Tape K} {μ : Mem K} {cap : ℕ} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1])
    {a a' : ℝ} (ha : 0 < a) (hspectrum : spectrum ℝ A ⊆ Set.Icc a a')
    {solution : Fin n → ℝ} (hsolution : A *ᵥ solution = decv dec n bs) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [b, x, x, r, p, v]) μ
      (solveCount n cap) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        RCLike.re (quadForm A (solution - decv dec n ys)) ≤
          4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^
            (2 * min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))) *
              RCLike.re (quadForm A (solution - decv dec n xs))) := by
  refine (runs_solve hS hM hB hA hCmp hPos W (τ := τ) (cap := cap)
    hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hys, he⟩
  refine ⟨hpos, ys, hys, ?_⟩
  rw [he]
  exact hPos.isHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow
    ha hspectrum hsolution _ _

end NLAlib.Krylov.CG.HSCG.Carried
