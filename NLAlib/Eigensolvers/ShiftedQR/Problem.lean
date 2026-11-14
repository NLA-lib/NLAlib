/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Ops.Certification

/-!
# Raw input buffers for a single shifted QR step

The input consists of the actual interleaved matrix words and two shift words. The third
supplied buffer is uninitialized output capacity. Dimension `n` denotes a matrix of order
`n+1`, including the scalar case. The program, rather than the input interface, initializes
its working matrix and output. No preprocessing computes a factorization or a shifted matrix.

## Main results

* `NLAlib.ShiftedQR.stepProblem`: the raw three-buffer interface.
* `NLAlib.ShiftedQR.initial_step_matrix`: the actual input matrix representation.
* `NLAlib.ShiftedQR.initial_step_geometry`: capacities and separation of supplied views.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- A raw matrix, two raw shift words, and uninitialized matrix output capacity. Every natural
size is admitted; the exact scalar step has a mathematical value even for singular shifts. -/
def stepProblem : Problem ℝ 1 3 where
  formats _ := .cell
  valid _ := True
  Data _ := List ℝ × List ℝ
  admissible d data buffers :=
    buffers = ![data.1.map some, data.2.map some,
      List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none] ∧
    data.1.length = 2 * ((d 0 + 1) * (d 0 + 1)) ∧ data.2.length = 2
  admitted := ⟨fun _ => 0, trivial⟩
  supply d _ := ⟨(List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) 0, [0, 0]),
    _, rfl, List.length_replicate .., rfl⟩

/-- The supplied buffers have exactly their declared raw contents and uninitialized capacity. -/
theorem step_input_buffers (d : Fin 1 → ℕ) (x : stepProblem.Input d) :
    x.val.2 = ![x.val.1.1.map some, x.val.1.2.map some,
      List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none] := x.property.1

/-- The input matrix is decoded from the supplied words using the pair codec. -/
def stepInputMatrix (d : Fin 1 → ℕ) (x : stepProblem.Input d) :
    Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ :=
  matrixOfWords (d 0 + 1) x.val.1.1

/-- The complex shift has precisely the two supplied real components. -/
def stepInputShift (d : Fin 1 → ℕ) (x : stepProblem.Input d) : ℂ :=
  ⟨vec x.val.1.2 0, vec x.val.1.2 1⟩

/-- Initial matrix storage represents the matrix decoded from the actual supplied word list. -/
theorem initial_step_matrix (d : Fin 1 → ℕ) (x : stepProblem.Input d) :
    HoldsMatrix (0, 0) (stepInputMatrix d x) (stepProblem.initial d x).store := by
  have h := Problem.initial_readBlock (P := stepProblem) d x (0 : Fin 3)
    (show x.val.2 0 = x.val.1.1.map some by rw [step_input_buffers]; rfl)
  rw [x.property.2.1] at h
  simpa only [HoldsMatrix, stepInputMatrix,
    matrixWords_matrixOfWords _ x.property.2.1, Fin.val_zero] using h

/-- Initial shift storage contains exactly its two actual supplied components. -/
theorem initial_step_shift (d : Fin 1 → ℕ) (x : stepProblem.Input d) :
    (stepProblem.initial d x).store.readBlock 1 0 2 =
      some [(stepInputShift d x).re, (stepInputShift d x).im] := by
  have h := Problem.initial_readBlock (P := stepProblem) d x (1 : Fin 3)
    (show x.val.2 1 = x.val.1.2.map some by rw [step_input_buffers]; rfl)
  have hx : x.val.1.2 = [vec x.val.1.2 0, vec x.val.1.2 1] := by
    rcases hxs : x.val.1.2 with _ | ⟨a, xs⟩
    · simpa [hxs] using x.property.2.2
    rcases xs with _ | ⟨b, xs⟩
    · simpa [hxs] using x.property.2.2
    have hn : xs = [] := List.length_eq_zero_iff.mp (by simpa [hxs] using x.property.2.2)
    subst xs
    simp [vec]
  rw [x.property.2.2, hx] at h
  exact h

/-- All three supplied handles are live; the output has its full declared capacity and is
separate from both inputs. These are consequences of the raw interface, not extra premises. -/
theorem initial_step_geometry (d : Fin 1 → ℕ) (x : stepProblem.Input d) :
    let m := stepProblem.initial d x
    m.Live [(0, 0), (1, 0), (2, 0)] ∧
      m.store.len 2 = 2 * ((d 0 + 1) * (d 0 + 1)) ∧
      m.store.length = 3 ∧ m.pos = 0 := by
  have hs : (stepProblem.initial d x).store =
      [x.val.1.1.map some, x.val.1.2.map some,
        List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none] := by
    change List.ofFn x.val.2 = _
    rw [step_input_buffers]
    rfl
  refine ⟨?_, ?_, by simp [Problem.initial], rfl⟩
  · simp [Mem.Live, Problem.initial]
  · rw [hs]
    simp [Store.len]

/-- Resident payload counts both raw input blocks and the full uninitialized output capacity. -/
theorem initialBytes_stepProblem (d : Fin 1 → ℕ) (x : stepProblem.Input d) :
    stepProblem.initialBytes d x = 4 * ((d 0 + 1) * (d 0 + 1)) + 2 := by
  unfold Problem.initialBytes
  rw [step_input_buffers]
  simp [stepProblem, List.ofFn_succ, x.property.2.1, x.property.2.2]
  omega

end NLAlib.ShiftedQR
