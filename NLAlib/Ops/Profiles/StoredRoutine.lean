/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.StoredOperator
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.RoutineLink
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# Stored matrix-vector leaves as routines

A tree that applies a stored matrix to a vector is a routine
`[m, n] (data : read, x : read n) → (y : write m)` separated by block: the output block is
disjoint from the data and the vector, which may be views of one buffer. Every such routine
implements the stored-operator contract of its data length, so a leaf is proved once, as a
routine, and its operation contract follows.

## Main definitions

* `NLAlib.Ops.StoredOperator.matvecRoutine`: the routine of a matrix-vector tree.

## Main results

* `NLAlib.Ops.StoredOperator.matvecRoutine_disj`: the separation of its operands.
* `NLAlib.Ops.StoredOperator.matvecRoutine_implements`: it implements the stored-operator
  contract.
-/

@[expose] public section

namespace NLAlib.Ops.StoredOperator

variable {K Op Tst : Type} [Semiring K]

/-- A matrix-vector tree as a routine: `[m, n] (data : read, x : read n) → (y : write m)`,
separated by block. -/
def matvecRoutine (dataLength : ℕ → ℕ → ℕ) (body : Stmt Op Tst) : Routine Op Tst :=
  routine% [m, n] (data : ↑(dataLength m n), x : n) → (y : m) by blocks := body

/-- Separated operands of a matrix-vector routine: the output block is disjoint from the data
and from the vector. -/
theorem matvecRoutine_disj {dataLength : ℕ → ℕ → ℕ} {body : Stmt Op Tst} {m n : ℕ}
    {data x y : ℕ × ℕ}
    (h : (matvecRoutine dataLength body).SeparatedAt [m, n] [data, x, y]) :
    Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock data.1 data.2 (dataLength m n)) ∧
      Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock x.1 x.2 n) := by
  have h' : Fp.Disj (Fp.blocks [y] [m]) (Fp.blocks [data, x] [dataLength m n, n]) := h.2.1
  have h'' : Fp.Disj (Store.inBlock y.1 y.2 m)
      (Store.inBlock data.1 data.2 (dataLength m n) ⊔ Store.inBlock x.1 x.2 n) := by
    simpa [Fp.blocks] using h'
  exact Fp.disj_sup_right.mp h''

/-- A matrix-vector routine implements the stored-operator contract of its data length, the
operands of the routine being the inputs followed by the output. -/
theorem matvecRoutine_implements (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List K → Matrix (Fin m) (Fin n) K) (body : Stmt Op Tst) :
    (matvecRoutine dataLength body).Implements (functions dataLength matrix .matvec).rel
      (OutApart dataLength) (fun ins outs => ins ++ outs) := by
  implements [m, n] (data, x) → (y) with hadm
  have hdisj := hadm
  refine Routine.separatedAt_of_blocks rfl ⟨?_, hdisj, ?_, ?_⟩
  · change Fp.Disj (Store.inBlock y.1 y.2 m) (Fp.blocks [] []) ∧ True
    exact ⟨by simp [Fp.Disj], trivial⟩
  · trivial
  · change Fp.Disj (Fp.blocks [] []) _
    simp [Fp.Disj]

end NLAlib.Ops.StoredOperator
