/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Rounded.Linked
public import NLAlib.Krylov.Lanczos.Rounded.Solve

/-!
# Sequentially lowered rounded Lanczos

`NLAlib.Krylov.Lanczos.Rounded.seqSolveRoutine` has the interface of
`NLAlib.Krylov.Lanczos.solveRoutine` and the tree of the solver with every level-one
vector operation replaced by its sequential scalar implementation. It meets the same
specification, with the reduction errors of the sequential profile.

## Main definitions

* `NLAlib.Krylov.Lanczos.Rounded.seqSolveRoutine`.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.seqSolveRoutine_meets`: the lowered routine meets the
  specification of the solver.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- The solver with sequential scalar vector operations:
`[n, cap] (b : read n) → (V, C : write)`. -/
def seqSolveRoutine : Routine Op Tst :=
  solveRoutine.link (Table.comp Blas.level1Table Blas.sumSeqTable)

/-- The lowered solver meets the specification of the solver, for every interpretation of
scalar arithmetic satisfying the standard model and of the rounded product, with the reduction
errors of the sequential profile. -/
theorem seqSolveRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ} {em u E : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hAT : Aᵀ = A) (hprec : Precision em u E (Blas.seq.err u) n) :
    (seqSolveRoutine (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A E) := by
  have hc := Blas.seq_certifies (Op := Op) (Tst := Tst) hM hu (fun _ => True)
  obtain ⟨hS', hB⟩ := hc.satisfies I hS
  have hA' := Interp.link_satisfies_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  exact Routine.Meets.of_link (T := (Blas.seq (Op := Op) (Tst := Tst)).table)
    (solveRoutine_meets hS' hM hB trivial hA' hCmp hAT hprec)

end NLAlib.Krylov.Lanczos.Rounded
