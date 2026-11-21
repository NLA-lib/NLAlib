/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.StoredProgram
public import NLAlib.Ops.Profiles.ContextLinearGuarded
public import NLAlib.Ops.RoutineData
public import NLAlib.Ops.Routine
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# Lanczos with reorthogonalization on a stored dense matrix

The routine `[n, cap] (A, b) → (V, C)` runs the two-pass reorthogonalized Lanczos recurrence on
the Hermitian matrix whose words are in the input block `A`. It is the matrix-free routine on
stored data (`NLAlib.Ops.Routine.withData`): the matrix is an isolated operand, in any buffer
different from those of the other operands, forwarded to every product.

## Main definitions

* `NLAlib.Krylov.Lanczos.Reorth.Stored.solveRoutine`,
  `NLAlib.Krylov.Lanczos.Reorth.Stored.solveSpec`: the routine and its specification.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Stored.solveRoutine_meets`: the routine meets its
  specification.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Stored

open Ops

variable {I : Interp RCLikeBlas.Operation CmpTst ℝ}

/-- The specification of reorthogonalized Lanczos on a stored matrix of order `n`: for a Hermitian
matrix decoded from the stored words, that of the matrix-free routine at that matrix. -/
noncomputable def solveSpec (n : ℕ) : Routine.Spec ℝ :=
  .onData 1
    (fun d raws => d.headD 0 = n ∧ (StoredOperator.denseMatrix n n (raws.headD [])).IsHermitian)
    (fun _ raws => Lanczos.Reorth.solveSpec id (StoredOperator.denseMatrix n n (raws.headD [])))

/-- Reorthogonalized Lanczos on a stored dense matrix meets its specification for every exact scalar
and vector interpretation, at every dimension and cap: it is the matrix-free routine on stored data
(`NLAlib.Ops.Routine.Meets.withData`). -/
theorem solveRoutine_meets (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I)
    (hCmp : IsCmp id I) {n : ℕ} : solveRoutine.Meets I (solveSpec n) :=
  Routine.Meets.withData _ _
    (fun _ raws => ContextLinear.relation (StoredOperator.denseMatrix n n (raws.headD [])))
    (fun _ => ContextLinear.admissible n)
    (fun _ raws => ContextLinear.fallback (StoredOperator.denseMatrix n n (raws.headD [])))
    rfl rfl
    (fun d ctx m raws hc hr hP => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hc
      split_reads hr as (raw)
      have hraw' : m.store.readBlock a.1 a.2 (n * n) = some raw := by
        rw [← hP.1]
        exact hraw
      exact ContextLinear.guarded_satisfies hS hB [a] ⟨0, by simp⟩ m.store raw
        (fun z hz => List.mem_map_of_mem hz) hraw')
    (fun d ctx m raws hc hr hP => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hc
      split_reads hr as (raw)
      have hraw' : m.store.readBlock a.1 a.2 (n * n) = some raw := by
        rw [← hP.1]
        exact hraw
      obtain ⟨hs, hb', hA, hc⟩ := ContextLinear.guarded_laws hS hB hCmp [a] ⟨0, by simp⟩
        m.store raw (fun z hz => List.mem_map_of_mem hz) hraw'
      exact Lanczos.Reorth.solveRoutine_meets hs RCLikeBlas.exactModel_real hb' trivial hA hc hP.2)

end NLAlib.Krylov.Lanczos.Reorth.Stored
