/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.MatrixStorage

/-!
# Declared input buffers

The existing `NLAlib.Computation.inputState` stores its declared buffers at consecutive handles.
These lemmas expose their reads, shapes and writable capacities without evaluating a program.
The matrix readback lemma uses the existing column-major layout, including empty rectangles.

## Main results

* `NLAlib.Computation.read_inputState`: a declared-buffer read.
* `NLAlib.Computation.shape_inputState`: a declared-buffer extent.
* `NLAlib.Computation.writable_inputState`: output capacity before initialization.
* `NLAlib.Computation.holds_inputState`: a packed initialized matrix satisfies `Holds`.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K C : Type} [DecidableEq P] [Zero C]

/-- A read from a declared buffer sees its initialized word. -/
theorem read_inputState {b : ℕ} (p : P) (bufs : Fin b → Array (Option K))
    (j : Fin b) (i : ℕ) :
    (inputState (C := C) p (List.ofFn bufs)).store.read p j.val i = (bufs j)[i]?.join := by
  simp [inputState, Store.read, j.isLt]

/-- A declared buffer has its original tag and extent. -/
theorem shape_inputState {b : ℕ} (p : P) (bufs : Fin b → Array (Option K)) (j : Fin b) :
    (inputState (C := C) p (List.ofFn bufs)).store.shape[j.val]? =
      some (p, (bufs j).size) := by
  simp [inputState, Store.shape, j.isLt]

/-- Any prefix within a declared buffer is writable, even when uninitialized. -/
theorem writable_inputState {b : ℕ} (p : P) (bufs : Fin b → Array (Option K))
    (j : Fin b) (len : ℕ) (hlen : len ≤ (bufs j).size) :
    Writable (inputState (C := C) p (List.ofFn bufs)).store p j.val 0 len := by
  intro i hi
  exact ⟨(bufs j).size, shape_inputState p bufs j, by omega⟩

/-- A packed initialized rectangular matrix satisfies the column-major storage contract. -/
theorem holds_inputState {𝕜 : Type} [RCLike 𝕜] {b N k : ℕ} (p : P)
    (bufs : Fin b → Array (Option 𝕜)) (j : Fin b) (A : Matrix (Fin N) (Fin k) 𝕜)
    (hbuf : bufs j = (flatten A).map some) :
    Holds (inputState (C := C) p (List.ofFn bufs)).store p j.val 0 A := by
  intro i t
  rw [Nat.zero_add, read_inputState, hbuf, Array.getElem?_map, getElem?_flatten]
  rfl

end NLAlib.Computation
