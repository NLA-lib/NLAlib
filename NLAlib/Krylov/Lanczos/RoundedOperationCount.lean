/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedStoredCertificate
public import NLAlib.Ops.OperationCount

/-!
# The operation count of scalar Lanczos

The scalar-only stored Lanczos program (`NLAlib.Krylov.Lanczos.Stored.Rounded.scalarProgram`)
executes, on a
matrix of order `n` with iteration cap `k`, at most

`33 n² k + 153 n k + 302 k + 58 n + 179`

instructions: scalar operations, comparisons, and every structural instruction (index
arithmetic, operand addressing, loop rounds, allocation). Every weight of the scalar model is
one, so this is its work. The polynomial is computed from the fixed instrumented tree
(`NLAlib.Ops.Program.countPoly`) and checked by the kernel; it is an upper bound, in which a
branch counts both sides.

## Main results

* `NLAlib.Krylov.Lanczos.Stored.Rounded.countPoly_scalarProgram`: the polynomial of the program.
* `NLAlib.Krylov.Lanczos.Stored.Rounded.scalarCountedAlgorithm`: the certificate with this
  explicit work
  and span.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Stored.Rounded

open Ops

/-- The number of instructions of scalar Lanczos at order `d 0` and cap `d 1`, at most. -/
def operationCount (d : Fin 2 → ℕ) : ℕ :=
  33 * d 0 ^ 2 * d 1 + 153 * d 0 * d 1 + 302 * d 1 + 58 * d 0 + 179

-- Kernel reduction of the instrumented tree exceeds the default recursion depth.
set_option maxRecDepth 100000 in
/-- The instruction polynomial of the scalar Lanczos program, evaluated by the kernel. -/
theorem countPoly_scalarProgram : scalarProgram.countPoly =
    [(179, []), (33, [0, 0, 1]), (302, [1]), (153, [0, 1]), (58, [0])] := by
  rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_scalarProgram (d : Fin 2 → ℕ) :
    CountPoly.eval (List.ofFn d) scalarProgram.countPoly = operationCount d := by
  rw [countPoly_scalarProgram]
  simp only [CountPoly.eval, CountPoly.monoEval, operationCount, List.ofFn_succ, List.ofFn_zero,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil,
    List.getD_cons_zero, List.getD_cons_succ, Fin.succ_zero_eq_one]
  ring

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The scalar specification with the explicit operation count as work and span. -/
noncomputable def scalarCountedSpecification (M : Machine ℝ) (E : (Fin 2 → ℕ) → ℝ) :
    Specification ScalarOp CmpTst (problem domain admitted) :=
  { scalarSpecification (domain := domain) (admitted := admitted) M E with
    work := operationCount
    span := operationCount }

/-- Scalar Lanczos on a stored matrix of order `n` with cap `k` runs within
`33 n² k + 153 n k + 302 k + 58 n + 179` instructions of the
scalar model, with the output of `scalarAlgorithm`. The program, model and hypotheses are those
of `scalarAlgorithm`. -/
noncomputable def scalarCountedAlgorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M)
    (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ)
    (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d) (Blas.seq.err u) (d 0)) :
    Algorithm (RoundedScalarBlas.model (problem domain admitted) M)
      (scalarCountedSpecification M E) :=
  (scalarAlgorithm M u hM hu E hprec).withCountPoly (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) operationCount (fun d _ => (eval_countPoly_scalarProgram d).le)

end NLAlib.Krylov.Lanczos.Stored.Rounded
