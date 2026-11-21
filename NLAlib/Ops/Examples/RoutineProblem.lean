/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.RoutineSyntax

/-!
# Example: the kinds of buffers a problem supplies

A routine reads a vector, raw words, a pair of parameters and a threshold, and writes a cell.
Its problem (`NLAlib.Ops.Examples.RoutineProblems.thresholdDomain`) shows every kind of slot:

* the vector, the words and the parameters are inputs, each `stored` with its codec;
* the threshold is `derived`: its buffer holds the sum of the two parameters, a quantity
  computed from the inputs, and the problem lists it as such;
* the cell is `blank`.

The admitted inputs are those with a nonnegative first parameter, and every such tuple is the
data of exactly one input of the problem.

## Main definitions

* `NLAlib.Ops.Examples.RoutineProblems.thresholdDomain`: the admitted inputs.

## Main results

* `NLAlib.Ops.Examples.RoutineProblems.derived_thresholdDomain`: the one derived operand.
* `NLAlib.Ops.Examples.RoutineProblems.thresholdDomain_covers`: coverage.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.RoutineProblems

/-- A routine with four operands read and one written; its tree does not matter here. -/
def thresholdRoutine : Routine Empty Empty :=
  routine% [n] (x : n, w : n, par : 2, t : 1) → (z : 1) := .skip

/-- The admitted inputs: a real vector, `n` raw words and two parameters, the first
nonnegative. The threshold operand holds the sum of the parameters. -/
def thresholdDomain : thresholdRoutine.Domain ℝ 1 5 where
  valid _ := True
  In d := (Fin (d 0) → ℝ) × { ws : List ℝ // ws.length = d 0 } × (ℝ × ℝ)
  accepts _ x := 0 ≤ x.2.2.1
  slot d := ![.stored (Codec.vector (d 0)) Prod.fst,
    .stored (Codec.words (d 0)) fun x => x.2.1,
    .stored (Codec.scalar.prod Codec.scalar) fun x => x.2.2,
    .derived 1 (fun x => [x.2.2.1 + x.2.2.2]) fun _ => rfl,
    .blank 1]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Option.some.injEq] at h0 h1 h2
    exact Prod.ext ((Codec.vector (d 0)).encode_injective h0)
      (Prod.ext ((Codec.words (d 0)).encode_injective h1)
        ((Codec.scalar.prod Codec.scalar).encode_injective h2))
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited d _ := ⟨(fun _ => 0, ⟨List.replicate (d 0) 0, by simp⟩, (0, 0)), le_rfl⟩

/-- The problem names its derived operands: here the fourth one only. -/
theorem derived_thresholdDomain (d : Fin 1 → ℕ) : thresholdDomain.derived d = [3] := rfl

/-- The threshold buffer holds the sum of the parameters. -/
theorem buffer_threshold (d : Fin 1 → ℕ) (x : thresholdDomain.In d) :
    thresholdDomain.buffers d x 3 = [some (x.2.2.1 + x.2.2.2)] := rfl

/-- Every tuple of inputs with a nonnegative first parameter is admitted, by one input. -/
theorem thresholdDomain_covers (d : Fin 1 → ℕ) (x : thresholdDomain.In d) (hx : 0 ≤ x.2.2.1) :
    ∃! X : thresholdDomain.problem.Input d, X.val.1 = x :=
  thresholdDomain.covers d x hx

end NLAlib.Ops.Examples.RoutineProblems
