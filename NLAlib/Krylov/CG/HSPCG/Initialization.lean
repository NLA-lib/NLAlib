/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Exact

/-!
# Initialization of the Hestenes–Stiefel state

The initial iterate is retained while the residual and search direction are initialized to
the right-hand side minus its matrix-vector product. All arithmetic is performed through
the shared operations. The exact certificate identifies the stored state with the existing
PCG recurrence at index zero.

## Main results

* `NLAlib.Krylov.CG.HSPCG.initializeRoutine_meets`: the routine establishes the initial state.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- At the dimension of the matrix, the written state is the initial state of the
preconditioned recurrence for the right-hand side and the iterate read. -/
noncomputable def initializeSpec (dec : K → ℝ) {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m] (bs, xs) → (xs', rs, zs, ps)
    requires m = n
    ensures decodedState dec n xs' rs zs ps = pcgState A P (decv dec n bs) (decv dec n xs) 0

/-- Initialization meets its specification under exact scalar, vector and operator contracts:
it establishes the initial state of the preconditioned recurrence. -/
theorem initializeRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) :
    (initializeRoutine (Op := Op) (Tst := Tst)).Meets I (initializeSpec dec A P) := by
  routine_intro [n'] (b, x, r, z, p) reads (bs, xs)
  obtain rfl : n = n' := hpre.symm
  refine writes_allocs (lens := [.var 0, .const 1]) (ns := [n, 1]) rfl
    fun s₁ hs₁ hlen hB₁ => ?_
  have hq : s₁.len m.store.length = n := by simpa using hlen 0 (by simp)
  have ht : s₁.len (m.store.length + 1) = 1 := by simpa using hlen 1 (by simp)
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  step hB.copy as m₁ hfr₁ ⟨hpos₁, rs₀, hrs₀, hcopy₀⟩
  subst rs₀
  step hA as m₂ hfr₂ ⟨hpos₂, qs, hqs, heq⟩
  step (hS (.lit (-1))) as m₃ hfr₃ ⟨hpos₃, a, ha, hea⟩
  step hB.axpy as m₄ hfr₄ ⟨hpos₄, rs, hrs, her⟩
  step hP as m₅ hfr₅ ⟨hpos₅, zs, hzs, hez⟩
  step hB.copy as m₆ hfr₆ ⟨hpos₆, ps, hps, hcopy⟩
  subst ps
  have had : dec a = -1 := by rw [← hea, hM.lit]; norm_num
  have hrd : decv dec n rs = decv dec n bs - A *ᵥ decv dec n xs := by
    simpa [had, heq, sub_eq_add_neg] using
      (axpyExactRel_decoded (dec := dec) (n := n) her)
  intro s₂ hs₂ hB₂
  routine_exit
  change decodedState dec n xs rs zs zs = pcgState A P (decv dec n bs) (decv dec n xs) 0
  simp only [decodedState, pcgState]
  rw [hrd, hez, hrd]

end NLAlib.Krylov.CG.HSPCG
