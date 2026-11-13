/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# The tape of draws

The memory of a run has one position on the tape; an operation with a window of `k` entries
reads `k` positions, in the streams it names, and advances the position by `k`. Which law a
stream has is fixed by the access model (`NLAlib.Ops.IsTapeLaw`).

## Main results

* `NLAlib.Ops.Tape`: a tape holds, at each position, one entry of each stream; a stream is a
  source of independent draws of one distribution (`NLAlib.Ops.Stream.unif`,
  `NLAlib.Ops.Stream.gauss`, `NLAlib.Ops.Stream.sign`).
* `NLAlib.Ops.Tape.window`: the window of `k` entries of a stream from a position.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type}

/-- **The tape of draws**: the entry at each position of each stream, `τ i s`. A stream is a
source of independent draws of one distribution; a position holds one entry of every stream. -/
abbrev Tape (K : Type) := ℕ → ℕ → K

/-- The stream of uniform draws. Which law a stream has is fixed by the access model
(`NLAlib.Ops.IsTapeLaw`); the names only keep the streams apart. -/
abbrev Stream.unif : ℕ := 0

/-- The stream of standard Gaussian draws. -/
abbrev Stream.gauss : ℕ := 1

/-- The stream of random signs. -/
abbrev Stream.sign : ℕ := 2

/-- View a tape from a fixed initial position. All streams share the same offset. -/
def Tape.shift (τ : Tape K) (base : ℕ) : Tape K := fun p s => τ (base + p) s

@[simp] theorem Tape.shift_apply (τ : Tape K) (base p s : ℕ) :
    τ.shift base p s = τ (base + p) s := rfl

/-- The window of `k` entries of the stream `s` from the position `p`. -/
def Tape.window (τ : Tape K) (s p k : ℕ) : List K := (List.range k).map fun j => τ (p + j) s

/-- Place a finite list on one named stream. Other streams and positions beyond that list
contain the default word. This specifies tape values, without asserting a probability law. -/
def Tape.ofStream [Inhabited K] (stream : ℕ) (words : List K) : Tape K :=
  fun p s => if s = stream then words.getD p default else default

/-- Reading the supplied stream from position zero returns exactly the supplied list. -/
theorem Tape.window_ofStream [Inhabited K] (stream : ℕ) (words : List K) :
    (Tape.ofStream stream words).window stream 0 words.length = words := by
  apply List.ext_getElem
  · simp [Tape.window]
  · intro i hi hi'
    simp [Tape.window, Tape.ofStream, List.getD_eq_getElem?_getD, hi']

/-- The first adjacent supplied list occupies exactly the initial stream window. -/
theorem Tape.window_ofStream_append_left [Inhabited K] (stream : ℕ) (xs ys : List K) :
    (Tape.ofStream stream (xs ++ ys)).window stream 0 xs.length = xs := by
  apply List.ext_getElem
  · simp [Tape.window]
  · intro i hi hi'
    simp [Tape.window, Tape.ofStream, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hi', hi']

/-- The second adjacent supplied list begins immediately after the first one. -/
theorem Tape.window_ofStream_append_right [Inhabited K] (stream : ℕ) (xs ys : List K) :
    (Tape.ofStream stream (xs ++ ys)).window stream xs.length ys.length = ys := by
  apply List.ext_getElem
  · simp [Tape.window]
  · intro i hi hi'
    simp [Tape.window, Tape.ofStream, List.getD_eq_getElem?_getD,
      List.getElem?_append_right, hi']

/-- A window of the shifted tape is the corresponding window of the original tape. -/
theorem Tape.window_shift (τ : Tape K) (base s p k : ℕ) :
    (τ.shift base).window s p k = τ.window s (base + p) k := by
  simp only [Tape.window, Tape.shift, Nat.add_assoc]

@[simp] theorem Tape.length_window (τ : Tape K) (s p k : ℕ) : (τ.window s p k).length = k := by
  simp [Tape.window]

theorem Tape.window_one (τ : Tape K) (s p : ℕ) : τ.window s p 1 = [τ p s] := by
  simp [Tape.window]

/-- Tapes that agree on the positions of a window have the same window. -/
theorem Tape.window_congr {τ τ' : Tape K} {p k : ℕ} (h : ∀ j < k, τ (p + j) = τ' (p + j))
    (s : ℕ) : τ.window s p k = τ'.window s p k :=
  List.map_congr_left fun j hj => congrFun (h j (List.mem_range.mp hj)) s

end NLAlib.Ops
