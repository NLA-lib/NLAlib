/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Solve
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Certification

/-!
# Supplied buffers and resource declarations for spectral bisection

The problem supplies its raw matrix, three scalar parameters, and uninitialized output
capacity. Initial memory does no numerical preprocessing. The same fixed program has an
independent full syntactic manifest, including primitive calls, queries and structural work.
Format checking and a manifest alone are not a total numerical/resource certificate.

## Main results

* `NLAlib.SpectralBisection.problem`: explicit raw input and output buffers.
* `NLAlib.SpectralBisection.initialBytes_problem`: all supplied resident word capacity.
* `NLAlib.SpectralBisection.wellTyped_bisectionProgram`: every primitive uses its declared
  storage format.
* `NLAlib.SpectralBisection.staticBudget`: the complete instrumented syntactic manifest.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K : Type} [Inhabited K]

/-- The admitted inputs of spectral bisection: at the sizes of `domain`, every square matrix of
complex pairs and every triple of parameters (radius, tolerance, sign accuracy, in that order).
The first operand holds the packed matrix, the second the three parameter words; the basis and
the values are blank. -/
def inputs (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d) :
    (bisectionRoutine (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).Domain K 3 4 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) (K × K) × (Fin 3 → K)
  accepts _ _ := True
  slot d := ![.stored (Codec.matrix (EntryCodec.pair K) (d 0) (d 0)) Prod.fst,
    .stored (Codec.vector 3) Prod.snd, .blank (2 * (d 0 * d 0)), .blank (d 0)]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Access.readable, Codec.matrix, Codec.vector,
          EntryCodec.pair, List.ofFn_succ, Nat.mul_comm])
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq]
      at h0 h1
    exact Prod.ext ((Codec.matrix (EntryCodec.pair K) (d 0) (d 0)).encode_injective h0)
      ((Codec.vector 3).encode_injective h1)
  admitted := admitted
  inhabited _ _ := ⟨(fun _ _ => default, fun _ => default), trivial⟩

/-- A packed square matrix, three stored parameters, and empty output slots for a basis and
values: the problem of spectral bisection. -/
abbrev problem (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 3 4 :=
  (inputs (K := K) domain admitted).problem

variable {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The matrix of an input of the problem. -/
abbrev inputMatrix (d : Fin 3 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) (K × K) := x.val.1.1

/-- Resident capacity includes both the supplied matrix and output basis, the output values,
and all three supplied scalar parameters, including every initially empty output slot. -/
theorem initialBytes_problem (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x =
      4 * (d 0 * d 0) + d 0 + 3 := by
  refine ((inputs (K := K) domain admitted).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.matrix, Codec.vector, EntryCodec.pair, List.ofFn_succ]
  ring

/-- The blocks the routine reads at an input: the packed matrix and the three parameters. -/
theorem blocks_inputs (d : Fin 3 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    (inputs (K := K) domain admitted).blocks d x.val.1 =
      [(EntryCodec.pair K).packFinMatrix (inputMatrix d x),
        [x.val.1.2 0, x.val.1.2 1, x.val.1.2 2]] := by
  simp [Routine.Domain.blocks, inputs, bisectionRoutine, Routine.sel, Access.readable,
    Slot.words, Codec.matrix, Codec.vector, List.ofFn_succ, routineNF]

/-- The two supplied input buffers read as the packed matrix and the three parameters. -/
theorem initial_reads (d : Fin 3 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 0 0 (2 * (d 0 * d 0)) =
        some ((EntryCodec.pair K).packFinMatrix (inputMatrix d x)) ∧
      ((problem (K := K) domain admitted).initial d x).store.readBlock 1 0 3 =
        some [x.val.1.2 0, x.val.1.2 1, x.val.1.2 2] := by
  have h : ((problem (K := K) domain admitted).initial d x).readBlocks [(0, 0), (1, 0)]
      [2 * (d 0 * d 0), 3] = some [(EntryCodec.pair K).packFinMatrix (inputMatrix d x),
        [x.val.1.2 0, x.val.1.2 1, x.val.1.2 2]] := by
    have h := (inputs (K := K) domain admitted).readBlocks_initial x
    rw [blocks_inputs] at h
    exact h
  obtain ⟨a, b, as, bs, hab, ha, hb, hx⟩ := Mem.readBlocks_two h
  obtain ⟨rfl, rfl⟩ : (0, 0) = a ∧ (1, 0) = b := by simpa using hab
  obtain ⟨rfl, rfl⟩ : _ = as ∧ _ = bs := by simpa using hx
  exact ⟨ha, hb⟩

/-- The supplied matrix reads as the packing of the input matrix. -/
theorem initial_readBlock_inputMatrix (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 0 0 (2 * (d 0 * d 0)) =
      some ((EntryCodec.pair K).packFinMatrix (inputMatrix d x)) := (initial_reads d x).1

/-- The supplied parameter buffer holds the three parameters of the input. -/
theorem initial_parameter_words (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 1 0 3 =
      some [x.val.1.2 0, x.val.1.2 1, x.val.1.2 2] := (initial_reads d x).2

/-- The full budget is computed from the fixed instrumented tree before any input executes.
It contains all scalar/matrix/sample calls, queries and core addressing/control instructions. -/
noncomputable def staticBudget (d : Fin 3 → ℕ) :
    Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst) :=
  staticCost (bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d

/-- The entire fixed program respects the standard dense signature's storage formats,
independently of the chosen matrix work and scratch functions. This is format checking;
execution, numerical output and sharp resource bounds require their own proofs. -/
theorem wellTyped_bisectionProgram (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    (bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).wellTyped
      (Dense.resources matrixWork matrixWorkspace) (fun _ => .cell) = true := by
  rfl

end NLAlib.SpectralBisection
