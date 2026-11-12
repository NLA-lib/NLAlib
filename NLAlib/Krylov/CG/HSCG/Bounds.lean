/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Solve

/-!
# Polynomial error bounds for the stored CG output

The program already implements the pure CG recurrence. Its energy-error theorem is obtained
by applying the existing pure polynomial bound to the decoded output, without unfolding an
instruction, replaying a loop, or reproducing the mathematical convergence argument.

The operation hypotheses remain explicit and the fixed-horizon domain remains unchanged:
the horizon is at most the initial residual's Krylov grade. These are
conditional program results, not new canonical Algorithm certificates or registered targets.

## Main results

* `NLAlib.Krylov.CG.HSCG.runs_solve_chebyshev`: explicit spectral-interval convergence
  of the stored iterate, with the original operation and scratch bounds.

* `NLAlib.Krylov.CG.HSCG.runs_solve_polynomial`: the actual stored iterate has the
  classical polynomial energy-error bound and retains its existing resource budget.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Transfer the pure CG polynomial energy-error bound to the decoded program output.
The exact contracts and nonbreaking horizon are those of the total solver theorem;
`solution` solves the decoded input system and the polynomial is bounded on the spectrum.
[Saad2003, §6.11.3]. -/
theorem runs_solve_polynomial {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hPos : A.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p])
    (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))
    (hz : μ.Room [x, r, p] [n, n, n])
    {spectral : Set ℝ} (hspectrum : spectrum ℝ A ⊆ spectral)
    {solution : Fin n → ℝ} (hsolution : A *ᵥ solution = decv dec n bs)
    {poly : Polynomial ℝ} (hp : poly.degree ≤ k) (hpzero : poly.eval 0 = 1)
    {η : ℝ} (hη : ∀ ξ ∈ spectral, |poly.eval ξ| ≤ η) :
    ConditionalRuns I W τ solve (Env.frame [n, k] [b, x, x, r, p]) μ
      (solveCount n k) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        RCLike.re (quadForm A (solution - decv dec n ys)) ≤
          η ^ 2 * RCLike.re (quadForm A (solution - decv dec n xs))) := by
  refine (runs_solve hS hM hB hA hPos W (τ := τ)
    hbx hbr hbp hxr hxp hrp hl hbs hxs hk hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hys, he⟩
  refine ⟨hpos, ys, hys, ?_⟩
  rw [he]
  exact hPos.re_quadForm_sub_cgIterate_le hspectrum hsolution _ hp hpzero hη

/-- The exact SPD solver returns a stored iterate satisfying the classical Chebyshev
energy-error bound. The spectrum lies in a positive interval `[a, a']`, `solution` solves the
input system, and the horizon is at most the initial residual's Krylov grade. With
`rho = (sqrt (a' / a) - 1) / (sqrt (a' / a) + 1)`, the squared energy error is at most
`4 * rho ^ (2 * k)` times the initial squared energy error. Execution succeeds under the
exact scalar, BLAS and matvec contracts, with the existing operation and scratch bounds.
[Saad2003, Theorem 6.29]. -/
theorem runs_solve_chebyshev {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hPos : A.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p])
    (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))
    (hz : μ.Room [x, r, p] [n, n, n])
    {a a' : ℝ} (ha : 0 < a) (hspectrum : spectrum ℝ A ⊆ Set.Icc a a')
    {solution : Fin n → ℝ} (hsolution : A *ᵥ solution = decv dec n bs) :
    ConditionalRuns I W τ solve (Env.frame [n, k] [b, x, x, r, p]) μ
      (solveCount n k) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        RCLike.re (quadForm A (solution - decv dec n ys)) ≤
          4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * k) *
            RCLike.re (quadForm A (solution - decv dec n xs))) := by
  refine (runs_solve hS hM hB hA hPos W (τ := τ)
    hbx hbr hbp hxr hxp hrp hl hbs hxs hk hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hys, he⟩
  refine ⟨hpos, ys, hys, ?_⟩
  rw [he]
  exact hPos.isHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow
    ha hspectrum hsolution _ _

end NLAlib.Krylov.CG.HSCG
