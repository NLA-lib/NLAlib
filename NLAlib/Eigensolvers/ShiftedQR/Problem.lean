/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.ComplexCodec
public import NLAlib.Eigensolvers.ShiftedQR.StepRoutine
public import NLAlib.Ops.Certification

/-!
# The inputs of a single shifted QR step

The inputs are a complex matrix and a complex shift; the problem holds the interleaved matrix
words and the two shift words. The third supplied buffer is uninitialized output capacity.
Dimension `n` denotes a matrix of order `n+1`, including the scalar case. The program, rather
than the input interface, initializes its working matrix and output. No preprocessing computes
a factorization or a shifted matrix.

## Main results

* `NLAlib.ShiftedQR.stepInputs`, `NLAlib.ShiftedQR.stepProblem`: the admitted inputs and their
  problem.
* `NLAlib.ShiftedQR.initialBytes_stepProblem`: the supplied payload.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The admitted inputs of one shifted QR step: every complex matrix of order `n + 1` and every
complex shift. The first operand holds the interleaved words of the matrix, the second the real
and imaginary parts of the shift; the output matrix is blank. Every natural size is admitted;
the exact scalar step has a mathematical value even for singular shifts. -/
noncomputable def stepInputs :
    (stepRoutine (Op := ScalarOp) (Tst := CmpTst)).Domain ℝ 1 3 where
  valid _ := True
  In d := Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ × ℂ
  accepts _ _ := True
  slot d := ![.stored (Codec.complexMatrix (d 0 + 1)) Prod.fst, .stored Codec.complex Prod.snd,
    .blank (2 * ((d 0 + 1) * (d 0 + 1)))]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Access.readable, Codec.complexMatrix, Codec.complex,
          List.ofFn_succ])
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq]
      at h0 h1
    exact Prod.ext ((Codec.complexMatrix (d 0 + 1)).encode_injective h0)
      (Codec.complex.encode_injective h1)
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨(0, 0), trivial⟩

/-- The matrix words, the two shift words and uninitialized output capacity: the problem of
one shifted QR step. -/
noncomputable abbrev stepProblem : Problem ℝ 1 3 := stepInputs.problem

/-- The matrix of an input of the problem. -/
abbrev stepInputMatrix (d : Fin 1 → ℕ) (x : stepProblem.Input d) :
    Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ := x.val.1.1

/-- The shift of an input of the problem. -/
abbrev stepInputShift (d : Fin 1 → ℕ) (x : stepProblem.Input d) : ℂ := x.val.1.2

/-- Resident payload counts both raw input blocks and the full uninitialized output capacity. -/
theorem initialBytes_stepProblem (d : Fin 1 → ℕ) (x : stepProblem.Input d) :
    stepProblem.initialBytes d x = 4 * ((d 0 + 1) * (d 0 + 1)) + 2 := by
  refine (stepInputs.initialBytes_eq x).trans ?_
  simp [stepInputs, Slot.len, Codec.complexMatrix, Codec.complex, List.ofFn_succ]
  ring

end NLAlib.ShiftedQR
