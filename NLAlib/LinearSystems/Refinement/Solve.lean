/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.RefinementRun
public import NLAlib.Ops.Catalog.Refinement
public import NLAlib.Ops.Routine
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# Iterative refinement over three vector operations

`NLAlib.LinearSystems.Refinement.solve` is $k$ steps of iterative refinement for
$\mathbf{A}\mathbf{x} = \mathbf{b}$ as one routine over the operations of
`NLAlib.Ops.RefinementOp`: the residual, the correction solve and the update. No matrix data
enters the tree; the caller supplies the right-hand side, the starting iterate and two vectors
of scratch.

Each operation has its own accuracy, so each can run in its own precision
[CarsonHigham2018]: the residual in the residual precision, the correction from factors in the
factorization precision, the update in the working precision. The judgment holds under the
three contracts and gives a `NLAlib.RefinementRun` whose last iterate is the stored output, so
every bound on the run is a bound on the stored output.

## Main results

* `NLAlib.LinearSystems.Refinement.solve`: the routine.
* `NLAlib.LinearSystems.Refinement.solveSpec`: the stored iterates are a refinement run.
* `NLAlib.LinearSystems.Refinement.solve_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.LinearSystems.Refinement

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has RefinementOp Op]

/-- **Iterative refinement**: $k$ rounds of residual, correction solve and update in place,
with the residual in `r` and the correction in `d`, scratch supplied by the caller.
[CarsonHigham2018, Algorithm 1.1]; the factorization there is the implementation of the
correction solve.
Algorithm: iterative-refinement -/
def solve : Routine Op Tst :=
  routine% [n, k] (b : n, x : n) → (x, unreported r : n, unreported d : n) {
    for j < k {
      call (Has.inj RefinementOp.residual) [n] (b, x) → (r);
      call (Has.inj RefinementOp.solve) [n] (r) → (d);
      call (Has.inj RefinementOp.update) [n] (d, x) → (x)
    }
  }

variable [Inhabited K]

/-- At the order of the matrix, the iterate written is the last iterate of a refinement run of
$k$ steps for the decoded right-hand side, from the decoded start, with the accuracies
$\theta$ (correction), $\eta$, $\zeta$ (residual) and $\varepsilon$ (update). -/
def solveSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (θ η ζ ε : ℝ) :
    Routine.Spec K :=
  spec% [m, k] (bs, xs) → (xs')
    requires m = n
    ensures ∃ R : RefinementRun A (decv dec n bs) θ η ζ ε k,
      R.x 0 = decv dec n xs ∧ R.x k = decv dec n xs'

/-- Iterative refinement meets its specification for every interpretation that satisfies the
three contracts for an invertible $\mathbf{A}$, with nonnegative accuracies and the spectral
norm as the matrix-norm allowance of the residual: each round extends the run by the three
local bounds of its three calls. -/
theorem solve_meets {dec : K → ℝ} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {θ η ζ ε : ℝ}
    {I : Interp Op Tst K} (hI : IsRefinement dec A θ η ζ ε (specNorm A) I) (hA : IsUnit A)
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hε : 0 ≤ ε) :
    (solve (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A θ η ζ ε) := by
  routine_intro [n', k] (b, x, r, d) reads (bs, xs)
  obtain rfl : n = n' := Eq.symm hpre
  loop_inv (fun _ => Fp.blocks [x, r, d] [n, n, n])
    (fun j m' => m'.pos = m.pos ∧ ∃ (xs' : List K)
      (R : RefinementRun A (decv dec n bs) θ η ζ ε j),
      m'.store.readBlock x.1 x.2 n = some xs' ∧ R.x 0 = decv dec n xs ∧
        R.x j = decv dec n xs')
    with j hj m₁ hfr hP
  case initial => exact ⟨rfl, xs, .start hA hθ hη hζ hε _, hxs, rfl, rfl⟩
  case round =>
    obtain ⟨hpos₁, xs', R, hxs', h0, hxj⟩ := hP
    have hbs₁ : m₁.store.readBlock b.1 b.2 n = some bs := by keep
    step hI.residual as m₂ hfr₂ ⟨hpos₂, rs, hrs, hres⟩
    step hI.solve as m₃ hfr₃ ⟨hpos₃, ds, hds, hsol⟩
    step hI.update as m₄ hfr₄ ⟨hpos₄, xs'', hxs'', hupd⟩
    rw [← hxj] at hres hupd
    exact ⟨by rw [hpos₄, hpos₃, hpos₂, hpos₁], xs'',
      R.extend (decv dec n rs) (decv dec n ds) (decv dec n xs'') hres hsol hupd, hxs'',
      (R.extend_x_of_le _ _ _ hres hsol hupd (Nat.zero_le j)).trans h0,
      R.extend_x_succ _ _ _ hres hsol hupd⟩
  case exit =>
    rintro m₁ - ⟨hpos₁, xs', R, hx, h0, hk⟩
    exact ⟨hpos₁, [xs'], Mem.readBlocks_of_cons hx rfl, R, h0, hk⟩

end NLAlib.LinearSystems.Refinement
