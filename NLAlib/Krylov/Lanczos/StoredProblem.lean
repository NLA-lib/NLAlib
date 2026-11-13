/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.BufferProblem
public import NLAlib.Ops.ContextProblem
public import NLAlib.Ops.Catalog.StoredOperator
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Raw dense inputs for stored Lanczos

A matrix word buffer precedes the ordinary supplied right-hand side, basis and coefficient
buffers. Symmetry is an explicit admission condition for the reorthogonalized endpoint.
An actual zero matrix witnesses nonempty raw inputs at every admitted size.

## Main results

* `NLAlib.Krylov.Lanczos.StoredProblem.problem`: the shared four-buffer problem.
* `NLAlib.Krylov.Lanczos.StoredProblem.initial_matrix`: actual raw matrix readback.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.StoredProblem

open Ops

/-- A zero raw matrix decodes to the zero linear operator, including empty dimensions. -/
theorem denseMatrix_replicate_zero (n : ℕ) :
    StoredOperator.denseMatrix n n (List.replicate (n * n) (0 : ℝ)) = 0 := by
  ext i j
  simp [StoredOperator.denseMatrix]

/-- The additional raw-input condition imposes symmetry precisely when requested. -/
def extra (symmetric : Bool) (d : Fin 2 → ℕ) (context : Fin 1 → List ℝ)
    (_ : List ℝ) : Prop :=
  symmetric = true → (StoredOperator.denseMatrix (d 0) (d 0) (context 0)).IsHermitian

/-- Zero raw entries and an existing supplied-buffer input jointly witness admissibility. -/
theorem supply (coefficientLength : ℕ → ℕ) (domain : (Fin 2 → ℕ) → Prop)
    (admitted : ∃ d, domain d) (symmetric : Bool) (d : Fin 2 → ℕ) (hd : domain d) :
    ∃ context : Fin 1 → List ℝ,
      ∃ x : (PackedProblem.problem coefficientLength domain admitted).Input d,
        (∀ i, (context i).length = d 0 * d 0) ∧ extra symmetric d context x.val.1 := by
  obtain ⟨words, buffers, h⟩ :=
    (PackedProblem.problem (K := ℝ) coefficientLength domain admitted).supply d hd
  refine ⟨fun _ => List.replicate (d 0 * d 0) 0, ⟨⟨words, buffers⟩, h⟩, ?_, ?_⟩
  · intro i
    simp
  · intro _
    rw [denseMatrix_replicate_zero]
    exact Matrix.isHermitian_zero

/-- One raw matrix buffer followed by the existing packed Lanczos buffer problem. -/
def problem (coefficientLength : ℕ → ℕ) (domain : (Fin 2 → ℕ) → Prop)
    (admitted : ∃ d, domain d) (symmetric : Bool) : Problem ℝ 2 4 :=
  (PackedProblem.problem coefficientLength domain admitted).withContext 1
    (fun d _ => d 0 * d 0) (extra symmetric) (supply coefficientLength domain admitted symmetric)

variable {coefficientLength : ℕ → ℕ} {domain : (Fin 2 → ℕ) → Prop}
  {admitted : ∃ d, domain d} {symmetric : Bool}

/-- The mathematical matrix is the decoder of the supplied raw words, without preprocessing. -/
def matrix {d : Fin 2 → ℕ} (x : (problem coefficientLength domain admitted symmetric).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) ℝ :=
  StoredOperator.denseMatrix (d 0) (d 0) (x.val.1.1 0)

/-- Actual initialized matrix words read back from buffer zero. -/
theorem initial_matrix (d : Fin 2 → ℕ)
    (x : (problem coefficientLength domain admitted symmetric).Input d) :
    ((problem coefficientLength domain admitted symmetric).initial d x).store.readBlock
      0 0 (d 0 * d 0) = some (x.val.1.1 0) :=
  Problem.withContext.initial_readBlock_context d x 0

/-- The right-hand side is the actual supplied word list in shifted buffer one. -/
theorem initial_rhs (d : Fin 2 → ℕ)
    (x : (problem coefficientLength domain admitted symmetric).Input d) :
    ((problem coefficientLength domain admitted symmetric).initial d x).store.readBlock
      1 0 (d 0) = some x.val.1.2 := by
  have hlen := PackedProblem.length_input d (Problem.withContext.originalInput x)
  have hr := Problem.withContext.initial_readBlock_original d x (0 : Fin 3)
    (show (Problem.withContext.originalInput x).val.2 0 = x.val.1.2.map some by
      rw [PackedProblem.input_buffers]; rfl)
  change x.val.1.2.length = d 0 at hlen
  change ((problem coefficientLength domain admitted symmetric).initial d x).store.readBlock
    1 0 x.val.1.2.length = some x.val.1.2 at hr
  rw [hlen] at hr
  exact hr

/-- Every supplied source capability is live above the protected matrix prefix. -/
theorem initial_live (d : Fin 2 → ℕ)
    (x : (problem coefficientLength domain admitted symmetric).Input d) :
    ((problem coefficientLength domain admitted symmetric).initial d x).Live
      [(1, 0), (2, 0), (3, 0)] := by
  simp [Mem.live_cons, Mem.live_nil]

/-- The supplied basis and coefficient capacities retain their original declared lengths. -/
theorem initial_room (d : Fin 2 → ℕ)
    (x : (problem coefficientLength domain admitted symmetric).Input d) :
    ((problem coefficientLength domain admitted symmetric).initial d x).Room [(2, 0), (3, 0)]
      [(d 1 + 1) * d 0, coefficientLength (d 1)] := by
  have hv := Problem.withContext.initial_len_original d x (1 : Fin 3)
  have hc := Problem.withContext.initial_len_original d x (2 : Fin 3)
  have hz := PackedProblem.initial_room d (Problem.withContext.originalInput x)
  change ((problem coefficientLength domain admitted symmetric).initial d x).store.len 2 =
    _ at hv
  change ((problem coefficientLength domain admitted symmetric).initial d x).store.len 3 =
    _ at hc
  simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add] at hz ⊢
  rw [hv, hc]
  exact hz

/-- Symmetry admission is a property of the actual decoded raw matrix. -/
theorem matrix_isHermitian {d : Fin 2 → ℕ}
    (x : (problem coefficientLength domain admitted true).Input d) :
    (matrix x).IsHermitian := x.property.2.2.2 rfl

/-- The raw matrix prefix contributes its full payload above the original buffer capacities. -/
theorem initialBytes_eq (d : Fin 2 → ℕ)
    (x : (problem coefficientLength domain admitted symmetric).Input d) :
    (problem coefficientLength domain admitted symmetric).initialBytes d x =
      d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + coefficientLength (d 1)) := by
  have h := Problem.withContext.initialBytes_eq
    (P := PackedProblem.problem coefficientLength domain admitted)
    (count := 1) (lengths := fun d _ => d 0 * d 0) (extra := extra symmetric)
    (supply := supply coefficientLength domain admitted symmetric) d x
  rw [PackedProblem.initialBytes_problem] at h
  simpa [problem] using h

end NLAlib.Krylov.Lanczos.StoredProblem
