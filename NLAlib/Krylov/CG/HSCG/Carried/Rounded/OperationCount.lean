/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.StoredCertification
public import NLAlib.Ops.OperationCount

/-!
# The operation count of scalar conjugate gradient

The scalar-only stored conjugate gradient program
(`NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification.scalarProgram`) executes, on a matrix
of order
`n` with iteration cap `k`, at most

`33 n² k + 157 n k + 242 k + 50 n + 127`

instructions: scalar operations, comparisons, and every structural instruction (index
arithmetic, operand addressing, loop rounds, allocation). Every weight of the scalar model is
one, so this is its work. The polynomial is computed from the fixed instrumented tree
(`NLAlib.Ops.Program.countPoly`) and checked by the kernel; it is an upper bound, in which a
branch counts both sides.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification.countPoly_scalarProgram`: the
  polynomial of the
  program.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification.scalarCountedAlgorithm`: the
  certificate with
  this explicit work and span.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification

open Ops

/-- The number of instructions of scalar CG at order `d 0` and cap `d 1`, at most. -/
def operationCount (d : Fin 2 → ℕ) : ℕ :=
  33 * d 0 ^ 2 * d 1 + 157 * d 0 * d 1 + 242 * d 1 + 50 * d 0 + 127

/-- The instruction polynomial of the scalar CG program, evaluated by the kernel. -/
theorem countPoly_scalarProgram : scalarProgram.countPoly =
    [(242, [1]), (33, [0, 0, 1]), (157, [0, 1]), (127, []), (50, [0])] := by
  kernel_rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_scalarProgram (d : Fin 2 → ℕ) :
    CountPoly.eval (List.ofFn d) scalarProgram.countPoly = operationCount d := by
  rw [countPoly_scalarProgram]
  poly_eval [operationCount]

variable (lower upper : (Fin 2 → ℕ) → ℝ)
variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
    raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts lower upper d raw rhs)

/-- The scalar CG specification with the explicit operation count as work and span. -/
noncomputable def scalarCountedSpecification (E : (Fin 2 → ℕ) → ℝ) :
    Specification ScalarOp CmpTst (problem lower upper domain admitted supply) :=
  { scalarSpecification lower upper domain admitted supply E with
    work := operationCount
    span := operationCount }

/-- Scalar conjugate gradient on a stored matrix of order `n` with cap `k` runs within
`33 n² k + 157 n k + 242 k + 50 n + 127` instructions of the scalar model, with the output
stability of `scalarAlgorithm`. The program, model and hypotheses are those of
`scalarAlgorithm`. -/
noncomputable def scalarCountedAlgorithm (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (em E : (Fin 2 → ℕ) → ℝ)
    (hMatvec : ∀ d, domain d → ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0) ≤ em d)
    (hAccuracy : ∀ d, domain d → Standard.Accuracy (em d) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lower d)
    (hprec : ∀ d, domain d → 3 * E d * upper d ≤ lower d)
    (hwindow : ∀ d, domain d → (d 1 : ℝ) ^ 2 * Real.sqrt (d 1) * E d *
      (upper d / lower d) ^ 2 ≤ 1 / 10 ^ 5) :
    Algorithm (RoundedScalarBlas.model (problem lower upper domain admitted supply) M)
      (scalarCountedSpecification lower upper domain admitted supply E) :=
  (scalarAlgorithm lower upper domain admitted supply M u hM hu em E hMatvec hAccuracy ha hprec
    hwindow).withCountPoly (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    operationCount (fun d _ => (eval_countPoly_scalarProgram d).le)

end NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification
