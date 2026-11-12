/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Solve

/-!
# Polynomial error bounds for the stored PCG output

The program already implements the pure PCG recurrence. Its energy-error theorem is obtained
by applying the existing pure polynomial bound to the decoded output, without unfolding an
instruction, replaying a loop, or reproducing the mathematical convergence argument.

The operation hypotheses remain explicit and the fixed-horizon domain remains unchanged:
the horizon is at most the initial residual's preconditioned Krylov grade. These are
conditional program results, not new canonical Algorithm certificates or registered targets.

## Main results

* `NLAlib.Krylov.CG.HSPCG.runs_solve_polynomial`: the actual stored iterate has the
  classical polynomial energy-error bound and retains its existing resource budget.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- Transfer the pure PCG polynomial energy-error bound to the decoded program output.
The exact contracts and nonbreaking horizon are those of the total solver theorem;
`solution` solves the decoded input system and the polynomial is bounded on the
preconditioned spectrum.
[Saad2003, §9.2]. -/
theorem runs_solve_polynomial {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) (hPos : A.PosDef) (hPPos : P.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p])
    (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs)))
    (hz : μ.Room [x, r, z, p] [n, n, n, n])
    {spectral : Set ℝ} (hspectrum : spectrum ℝ (P * A) ⊆ spectral)
    {solution : Fin n → ℝ} (hsolution : A *ᵥ solution = decv dec n bs)
    {poly : Polynomial ℝ} (hp : poly.degree ≤ k) (hpzero : poly.eval 0 = 1)
    {η : ℝ} (hη : ∀ ξ ∈ spectral, |poly.eval ξ| ≤ η) :
    ConditionalRuns I W τ solve (Env.frame [n, k] [b, x, x, r, z, p]) μ
      (solveCount n k) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        RCLike.re (quadForm A (solution - decv dec n ys)) ≤
          η ^ 2 * RCLike.re (quadForm A (solution - decv dec n xs))) := by
  refine (runs_solve hS hM hB hA hP hPos hPPos W (τ := τ)
    hbx hbr hbz hbp hxr hxz hxp hrz hrp hzp hl hbs hxs hk hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hys, he⟩
  refine ⟨hpos, ys, hys, ?_⟩
  rw [he]
  exact hPos.re_quadForm_sub_pcgIterate_le hPPos hspectrum hsolution _ hp hpzero hη

end NLAlib.Krylov.CG.HSPCG
