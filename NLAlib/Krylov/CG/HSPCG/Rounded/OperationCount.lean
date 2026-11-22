/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Rounded.StoredCertification
public import NLAlib.Ops.OperationCount

/-!
# The operation count of scalar preconditioned conjugate gradient

The scalar-only stored preconditioned conjugate gradient program
(`NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification.program`) executes, on a
matrix of order `n` with iteration cap `k`, at most

`66 n² k + 33 n² + 228 n k + 390 k + 73 n + 181`

instructions: scalar operations, comparisons, and every structural instruction (index
arithmetic, operand addressing, loop rounds, allocation). Every weight of the scalar model is
one, so this is its work. The polynomial is computed from the fixed instrumented tree
(`NLAlib.Ops.Program.countPoly`) and checked by the kernel; it is an upper bound, in which a
branch counts both sides.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification.countPoly_program`: the polynomial of the
  program.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification.countedAlgorithm`: the certificate with this
  explicit work
  and span.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification

open Ops

/-- The number of instructions of scalar preconditioned conjugate gradient at order `d 0` and cap
`d 1`, at most. -/
def operationCount (d : Fin 2 → ℕ) : ℕ :=
  66 * d 0 ^ 2 * d 1 + 33 * d 0 ^ 2 + 228 * d 0 * d 1 + 390 * d 1 + 73 * d 0 + 181

/-- The instruction polynomial of the scalar preconditioned conjugate gradient program, evaluated
by the kernel. -/
theorem countPoly_program : program.countPoly =
    [(73, [0]), (390, [1]), (228, [0, 1]), (66, [0, 0, 1]), (181, []), (33, [0, 0])] := by
  kernel_rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_program (d : Fin 2 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = operationCount d := by
  rw [countPoly_program]
  poly_eval [operationCount]

variable (lowerA upperA lowerP upperP : (Fin 2 → ℕ) → ℝ)
  (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ x : Inputs d, accepts lowerA upperA lowerP upperP d x)

/-- The scalar PCG specification with the explicit operation count as work and span. -/
noncomputable def countedSpecification (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ) :
    Specification ScalarOp CmpTst
      (problem lowerA upperA lowerP upperP domain admitted supply) :=
  { specification lowerA upperA lowerP upperP domain admitted supply M u hM hu E with
    work := operationCount
    span := operationCount }

/-- Scalar preconditioned conjugate gradient on stored matrices of order `n` with cap `k` runs
within `66 n² k + 33 n² + 228 n k + 390 k + 73 n + 181` instructions of the scalar model, with
the output of `algorithm`. The program, model and hypotheses are those of `algorithm`. -/
noncomputable def countedAlgorithm (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ)
    (hAccuracy : ∀ d, domain d →
      Standard.Accuracy (StoredContext.relativeError u (d 0)) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lowerA d) (hp : ∀ d, domain d → 0 < lowerP d)
    (hAp : ∀ d, domain d → 6 * E d * upperA d ≤ lowerA d)
    (hPp : ∀ d, domain d → 6 * E d * upperP d ≤ lowerP d)
    (hwindow : ∀ d, domain d → E d *
      (1024 * (upperA d / lowerA d) * (upperP d / lowerP d)) ^ (d 1 + 1) ≤ 1 / 2) :
    Algorithm (RoundedScalarBlas.model
      (problem lowerA upperA lowerP upperP domain admitted supply) M)
      (countedSpecification lowerA upperA lowerP upperP domain admitted supply M u hM hu E) :=
  (algorithm lowerA upperA lowerP upperP domain admitted supply M u hM hu E hAccuracy ha hp hAp
    hPp hwindow).withCountPoly (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    operationCount (fun d _ => (eval_countPoly_program d).le)

end NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification
