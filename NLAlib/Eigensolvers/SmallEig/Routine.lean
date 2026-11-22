/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.Program
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# The routine of the small-eigenvalue solver

`NLAlib.SmallEig.smallEigRoutine` is
`[n, nq, T] (M : update 2 (n + 1)², q : read nq) → (U : write 2 (n + 1)²)`: the program
`NLAlib.SmallEig.smallEigProg` at the order `n + 1`, in Schur mode. It overwrites the matrix by
the computed triangular factor and writes the accumulator. It draws from two streams, and the
number of tape positions it consumes depends on the data and on the tape, so it declares none.

The specification holds on every tape: the run terminates, writes only the matrix and the
accumulator and leaves both stored. The accuracy of the output is a statement in probability
(`NLAlib.Eigensolvers.SmallEig.Theorems`), not a postcondition.

## Main definitions

* `NLAlib.SmallEig.smallEigRoutine`, `NLAlib.SmallEig.smallEigSpec`.

## Main results

* `NLAlib.SmallEig.smallEigRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Ops ShiftedQR
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- The small-eigenvalue solver at the order `n + 1`. The dimension `n` is one less than the
order, so that every dimension is the order of a nonempty matrix; the tree is `smallEigProg` at
`n + 1`, whose two variables for the matrix are the one operand `M`. The number of draws depends
on the data. -/
def smallEigRoutine (sG : ℕ) : Routine O Q :=
  routine% [n, nq, T] (M : 2 * ((n + 1) * (n + 1)), q : nq) →
      (M, U : 2 * ((n + 1) * (n + 1)))
    draws unspecified one variable {
    run (smallEigProg (O := O) (Q := Q) sG) [n + 1, nq, T] (M, q, M, U)
  }

/-- The input is the words of a matrix of order `n + 1` and `nq` parameter words holding caps
for the cap `T`, with the natural literals up to `n + 1` exact on the machine. The matrix and
the accumulator end up holding the words of two matrices; nothing is claimed of their values. -/
def smallEigSpec (M : Machine ℝ) : Routine.Spec ℝ where
  pre d _ X := IsExactNatLit id M (d.headD 0 + 1) ∧ ∃ qs : List ℝ,
    SmallEigCaps (d.getD 2 0) qs ∧ 12 ≤ qs.length ∧ qs.length = d.getD 1 0 ∧
      ∃ B : Matrix (Fin (d.headD 0 + 1)) (Fin (d.headD 0 + 1)) ℂ, X = [matrixWords B, qs]
  post d _ _ Y := ∃ Tb Ub : Matrix (Fin (d.headD 0 + 1)) (Fin (d.headD 0 + 1)) ℂ,
    Y = [matrixWords Tb, matrixWords Ub]

/-- The small-eigenvalue solver terminates on every tape, writes only the matrix and the
accumulator and leaves both stored. -/
theorem smallEigRoutine_meets {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I)
    {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I) :
    (smallEigRoutine (O := O) (Q := Q) sG).Meets I (smallEigSpec M) := by
  routine_intro [n, nq, T] (w, q, ub) reads (ws, qs')
  obtain ⟨hNat, qs, hcaps, h12, hq, B, heq⟩ := hpre
  obtain rfl : qs.length = nq := hq
  obtain ⟨rfl, rfl⟩ : matrixWords B = ws ∧ qs = qs' := by simpa using heq.symm
  have hT := smallEigProg_completes (O := O) (Q := Q) (sG := sG) hS hL hNat hC hQ hSmp hDisk
    hcaps h12 (tape := τ) B le_rfl hws hqs' (by room) hroom.2
    (Fp.disj_inBlock_of_ne hwub) (Fp.disj_sup_right.mpr
      ⟨Fp.disj_inBlock_of_ne hwq.symm, Fp.disj_inBlock_of_ne hqub⟩)
  refine ((hT.in_frame (ρ := Env.frame [n, qs.length, T] [w, q, ub]) rfl rfl (by room)).mono
    (by fp_sub) ?_)
  rintro m' - ⟨Tb, Ub, hTb, hUb⟩
  exact ⟨trivial, [_, _], Mem.readBlocks_of_cons hTb (Mem.readBlocks_of_cons hUb rfl),
    Tb, Ub, rfl⟩

end NLAlib.SmallEig
