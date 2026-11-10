/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# The tape of draws

A tape `NLAlib.Ops.Tape K` holds, at each position, one entry of each stream; a stream is a
source of independent draws of one distribution (`NLAlib.Ops.Stream.unif`,
`NLAlib.Ops.Stream.gauss`, `NLAlib.Ops.Stream.sign`). The memory of a run has one position; an
operation with a window of `k` entries reads `k` positions, in the streams it names, and
advances the position by `k`. Which law a stream has is fixed by the access model
(`NLAlib.Ops.IsTapeLaw`).
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

/-- The window of `k` entries of the stream `s` from the position `p`. -/
def Tape.window (τ : Tape K) (s p k : ℕ) : List K := (List.range k).map fun j => τ (p + j) s

@[simp] theorem Tape.length_window (τ : Tape K) (s p k : ℕ) : (τ.window s p k).length = k := by
  simp [Tape.window]

theorem Tape.window_one (τ : Tape K) (s p : ℕ) : τ.window s p 1 = [τ p s] := by
  simp [Tape.window]

/-- Tapes that agree on the positions of a window have the same window. -/
theorem Tape.window_congr {τ τ' : Tape K} {p k : ℕ} (h : ∀ j < k, τ (p + j) = τ' (p + j))
    (s : ℕ) : τ.window s p k = τ'.window s p k :=
  List.map_congr_left fun j hj => congrFun (h j (List.mem_range.mp hj)) s

end NLAlib.Ops
