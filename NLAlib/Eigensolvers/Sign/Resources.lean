/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Alg
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Certification

/-!
# Supplied buffers for capped matrix sign iteration

The inputs are a square matrix of complex pairs and two parameters (tolerance and scale); the
problem holds the packed matrix, the two parameter words and uninitialized output capacity.
The fixed program computes the capped sign iteration using its own scoped workspace.
Resources include the complete instrumented tree and all supplied capacity.

## Main results

* `NLAlib.Sign.inputs`, `NLAlib.Sign.problem`: the admitted inputs and their problem.
* `NLAlib.Sign.signProgram` fixes one tree before sizes or input values.
* `NLAlib.Sign.initialBytes_problem` counts all supplied capacity.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K : Type} [Inhabited K]

/-- The admitted inputs of the sign iteration: at the sizes of `domain`, every square matrix
of complex pairs and every pair of parameters (tolerance, scale). The first operand holds the
packed matrix, the second the two parameter words; the output matrix is blank. -/
def inputs (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) :
    (signRoutine (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst) (Has.inj MatrixOp.mul)).Domain K 2 3
    where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) (K × K) × (K × K)
  accepts _ _ := True
  slot d := ![.stored (Codec.matrix (EntryCodec.pair K) (d 0) (d 0)) Prod.fst,
    .stored (Codec.scalar.prod Codec.scalar) Prod.snd, .blank (2 * (d 0 * d 0))]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Access.readable, Codec.matrix, Codec.prod, Codec.scalar,
          EntryCodec.pair, List.ofFn_succ, Nat.mul_comm])
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq]
      at h0 h1
    exact Prod.ext ((Codec.matrix (EntryCodec.pair K) (d 0) (d 0)).encode_injective h0)
      ((Codec.scalar.prod Codec.scalar).encode_injective h1)
  admitted := admitted
  inhabited _ _ := ⟨(fun _ _ => default, default), trivial⟩

/-- A packed square matrix, tolerance and scale, and an empty packed matrix output: the
problem of the sign iteration. -/
abbrev problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 3 :=
  (inputs (K := K) domain admitted).problem

/-- The complete sign tree uses the standard dense operation signature. Parameters are
matrix dimension and cap; the three handles are input matrix, parameters and output. -/
def signProgram : Program DenseOp (CmpTst ⊕ IdxTst) 2 3 :=
  (signRoutine (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst) (Has.inj MatrixOp.mul)).close 2 3

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The matrix of an input of the problem. -/
abbrev inputMatrix (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) (K × K) := x.val.1.1

/-- The tolerance of an input of the problem: its first parameter. -/
abbrev tolerance (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) : K :=
  x.val.1.2.1

/-- The scale of an input of the problem: its second parameter. -/
abbrev scale (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) : K :=
  x.val.1.2.2

/-- Input and output capacity both count as supplied resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x = 4 * (d 0 * d 0) + 2 := by
  refine ((inputs (K := K) domain admitted).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.matrix, Codec.prod, Codec.scalar, EntryCodec.pair,
    List.ofFn_succ]
  ring

/-- Every primitive and structural instruction in the fixed instrumented sign tree. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst) := staticCost signProgram d

/-- Every sign call uses the storage formats of the standard dense resource profile. -/
theorem wellTyped_signProgram (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    signProgram.wellTyped (Dense.resources matrixWork matrixWorkspace) (fun _ => .cell) = true :=
  rfl

end NLAlib.Sign
