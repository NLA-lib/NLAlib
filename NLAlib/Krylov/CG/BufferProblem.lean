/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Certification

/-!
# Raw vector buffers for conjugate-gradient solvers

The right-hand side is supplied as raw words. Every other buffer is an explicitly supplied
uninitialized capacity. Initialization therefore belongs to the actual program.

## Main results

* `NLAlib.Krylov.CG.RawProblem.problem`: the capacity-parametric input interface.
* `NLAlib.Krylov.CG.RawProblem.initial_readBlock`: the supplied right-hand side.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.RawProblem

open Ops

variable {K : Type} [Inhabited K] {b : ℕ}

/-- Raw right-hand-side words and uninitialized output buffers of the declared capacities. -/
def problem (outputs : (Fin 2 → ℕ) → Fin (b + 1) → ℕ)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 (b + 1) where
  formats _ := .cell
  valid := domain
  Data _ := List K
  admissible d rhs buffers :=
    buffers = (fun i => if i = 0 then rhs.map some else List.replicate (outputs d i) none) ∧
      rhs.length = d 0
  admitted := admitted
  supply d _ := ⟨List.replicate (d 0) default,
    (fun i => if i = 0 then (List.replicate (d 0) default).map some
      else List.replicate (outputs d i) none), rfl, List.length_replicate ..⟩

variable {outputs : (Fin 2 → ℕ) → Fin (b + 1) → ℕ}
  {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The actual supplied buffer array is exactly the raw declared interface. -/
theorem input_buffers (d : Fin 2 → ℕ)
    (x : (problem (K := K) outputs domain admitted).Input d) :
    x.val.2 = (fun i => if i = 0 then x.val.1.map some
      else List.replicate (outputs d i) none) := x.property.1

/-- The raw right-hand-side list has the supplied dimension. -/
theorem length_input (d : Fin 2 → ℕ)
    (x : (problem (K := K) outputs domain admitted).Input d) : x.val.1.length = d 0 :=
  x.property.2

/-- Canonical execution starts with the supplied right-hand-side words readable. -/
theorem initial_readBlock (d : Fin 2 → ℕ)
    (x : (problem (K := K) outputs domain admitted).Input d) :
    ((problem outputs domain admitted).initial d x).store.readBlock 0 0 (d 0) =
      some x.val.1 := by
  have h := Problem.initial_readBlock (P := problem outputs domain admitted) d x (0 : Fin (b + 1))
    (show x.val.2 0 = x.val.1.map some by rw [input_buffers]; simp)
  rw [length_input d x] at h
  exact h

/-- Every supplied handle has its declared raw capacity, including uninitialized outputs. -/
theorem initial_len (d : Fin 2 → ℕ)
    (x : (problem (K := K) outputs domain admitted).Input d) (i : Fin (b + 1)) :
    ((problem outputs domain admitted).initial d x).store.len i =
      if i = 0 then d 0 else outputs d i := by
  rw [Problem.initial_len, input_buffers]
  by_cases hi : i = 0
  · simp only [if_pos hi]
    exact (List.length_map ..).trans (length_input d x)
  · simp only [if_neg hi, List.length_replicate]

/-- Resident payload is the sum of the actual raw capacities, including uninitialized slots. -/
theorem initialBytes_eq (d : Fin 2 → ℕ)
    (x : (problem (K := K) outputs domain admitted).Input d) :
    (problem (K := K) outputs domain admitted).initialBytes d x =
      (List.ofFn fun i => if i = 0 then d 0 else outputs d i).sum := by
  unfold Problem.initialBytes
  apply congrArg List.sum
  apply congrArg (fun f : Fin (b + 1) → ℕ => List.ofFn f)
  funext i
  change StorageFormat.cell.bytes * (x.val.2 i).length = _
  rw [StorageFormat.bytes_cell, one_mul]
  simpa only [Problem.initial_len] using initial_len d x i

end NLAlib.Krylov.CG.RawProblem
