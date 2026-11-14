/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Model
public import NLAlib.Ops.Confined

/-!
# The matrix-free conjugate gradient model is confined

The exact model of matrix-free CG and PCG (`NLAlib.Krylov.CG.HSPCG.Model.exactModel`) has two
declared oracles, the system operator and the preconditioner of the input. Every contract is in
operand form, so the model is confined (`NLAlib.Ops.AccessModel.Confined`): an oracle call reads
one vector and writes one vector. It is not uniform, and its operator weights are parameters.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Model.confined_exactModel`: the model is confined.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Model

open Ops

/-- The exact vector contracts are in operand form. -/
theorem confined_blasContract (a : Blas1Op) : (blasContract a).Confined := by
  cases a <;> exact BlockRel.confined_spec _ _

/-- **The matrix-free CG and PCG model is confined.** -/
instance confined_exactModel {r b : ℕ} (P : Problem ℝ r b) (n : (Fin r → ℕ) → ℕ)
    (A B : (d : Fin r → ℕ) → P.Input d → Matrix (Fin (n d)) (Fin (n d)) ℝ)
    (R : ResourceModel Signature Empty) : (exactModel P n A B R).Confined :=
  ⟨fun d x o => by
    cases o with
    | scalar a => exact BlockRel.confined_spec _ _
    | blas a => exact confined_blasContract a
    | operator => exact BlockRel.confined_spec _ _
    | preconditioner => exact BlockRel.confined_spec _ _,
    fun _ _ q => nomatch q⟩

end NLAlib.Krylov.CG.HSPCG.Model
