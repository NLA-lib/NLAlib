/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import NLAlib.Ops.Certification

/-!
# Supplied packed Lanczos input and output buffers

Ordinary and reorthogonalized Lanczos share the same right-hand-side and packed basis layout.
Their coefficient lengths differ. This common problem declares all supplied output capacity
and derives the initial reads, room, liveness and resident payload without preprocessing.

## Main results

* `NLAlib.Krylov.Lanczos.PackedProblem.problem`: the supplied packed-buffer problem.
* `NLAlib.Krylov.Lanczos.PackedProblem.initialBytes_problem`: full supplied resident payload.
* `NLAlib.Krylov.Lanczos.PackedProblem.initial_readBlock`: the declared raw input words.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.PackedProblem

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K]

/-- The matrix-free Lanczos problem has an initialized right-hand side and explicitly supplied
uninitialized basis/coefficient slots. The nonempty size-only domain can express reduction
applicability and precision caps without imposing a restriction on the right-hand-side words. -/
def problem (coefficientLength : ℕ → ℕ) (domain : (Fin 2 → ℕ) → Prop)
    (admitted : ∃ d, domain d) : Problem K 2 3 where
  formats _ := .cell
  valid := domain
  Data _ := List K
  admissible d bs buffers :=
    buffers = ![bs.map some, List.replicate ((d 1 + 1) * d 0) none,
      List.replicate (coefficientLength (d 1)) none] ∧ bs.length = d 0
  admitted := admitted
  supply d _ := ⟨List.replicate (d 0) default,
    ![(List.replicate (d 0) default).map some,
      List.replicate ((d 1 + 1) * d 0) none, List.replicate (coefficientLength (d 1)) none],
    rfl, List.length_replicate ..⟩

variable {coefficientLength : ℕ → ℕ}
variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- Admissibility identifies the three actual supplied buffers. -/
theorem input_buffers (d : Fin 2 → ℕ)
    (x : (problem (K := K) coefficientLength domain admitted).Input d) :
    x.val.2 = ![x.val.1.map some, List.replicate ((d 1 + 1) * d 0) none,
      List.replicate (coefficientLength (d 1)) none] := x.property.1

/-- Every supplied word list has the declared dimension. -/
theorem length_input (d : Fin 2 → ℕ)
    (x : (problem (K := K) coefficientLength domain admitted).Input d) :
    x.val.1.length = d 0 := x.property.2

/-- The input and all output capacity count toward resident modeled payload, regardless of
whether early breakdown leaves some output slots zero. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) coefficientLength domain admitted).Input d) :
    (problem (K := K) coefficientLength domain admitted).initialBytes d x =
      d 0 + (d 1 + 1) * d 0 + coefficientLength (d 1) := by
  rw [Problem.initialBytes, input_buffers]
  simp [problem, List.ofFn_succ, length_input, Nat.add_assoc]

/-- The supplied right-hand-side buffer reads back the declared raw word list. -/
theorem initial_readBlock (d : Fin 2 → ℕ)
    (x : (problem (K := K) coefficientLength domain admitted).Input d) :
    ((problem (K := K) coefficientLength domain admitted).initial d x).store.readBlock 0 0 (d 0) =
      some x.val.1 := by
  have h := Problem.initial_readBlock
    (P := problem (K := K) coefficientLength domain admitted) d x (0 : Fin 3)
    (show x.val.2 0 = x.val.1.map some by rw [input_buffers]; rfl)
  rw [length_input d x] at h
  exact h

/-- All three supplied handles are live in the canonical initial memory. -/
theorem initial_live (d : Fin 2 → ℕ)
    (x : (problem (K := K) coefficientLength domain admitted).Input d) :
    ((problem (K := K) coefficientLength domain admitted).initial d x).Live
      [(0, 0), (1, 0), (2, 0)] := by
  simp [Mem.live_cons, Mem.live_nil]

/-- The public output capacities are supplied before execution; they are not hidden scratch. -/
theorem initial_room (d : Fin 2 → ℕ)
    (x : (problem (K := K) coefficientLength domain admitted).Input d) :
    ((problem (K := K) coefficientLength domain admitted).initial d x).Room [(1, 0), (2, 0)]
      [(d 1 + 1) * d 0, coefficientLength (d 1)] := by
  have hv := Problem.initial_len d x (1 : Fin 3)
  have hc := Problem.initial_len d x (2 : Fin 3)
  simp only [input_buffers, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, List.length_replicate] at hv hc
  simp only [Mem.room_cons, Mem.room_nil, Nat.zero_add, and_true]
  exact ⟨hv.ge, hc.ge⟩

end NLAlib.Krylov.Lanczos.PackedProblem
