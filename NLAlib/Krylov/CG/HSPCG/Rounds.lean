/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Exact
public import NLAlib.Krylov.CG.Math.Preconditioned

/-!
# Composition of exact conjugate-gradient rounds

Each round of the loop is a call of the routine of one round, used by its judgment. The
invariant states that the buffers hold the iterated mathematical PCG state. Nonbreakdown is
required only at the rounds that the loop executes.

## Main results

* `NLAlib.Krylov.CG.HSPCG.roundsRoutine_meets`: the loop iterates the recurrence.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- At the dimension of the matrix, a state whose first `k` iterates do not break down is
advanced by `k` rounds. -/
noncomputable def roundsSpec (dec : K → ℝ) {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m, k] (xs, rs, zs, ps) → (xs', rs', zs', ps')
    requires m = n ∧
      ∀ j < k, Nonbreakdown A ((pcgStep A P)^[j] (decodedState dec n xs rs zs ps))
    ensures decodedState dec n xs' rs' zs' ps' =
      (pcgStep A P)^[k] (decodedState dec n xs rs zs ps)

/-- The round loop meets its specification: each iteration uses the judgment of the round. -/
theorem roundsRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) :
    (roundsRoutine (Op := Op) (Tst := Tst)).Meets I (roundsSpec dec A P) := by
  routine_intro [n', k] (x, r, z, p) reads (xs, rs, zs, ps)
  obtain ⟨hn, hdom⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hstep := stepRoutine_meets (Op := Op) (Tst := Tst) hS hM hB hA hP
  refine (writes_loop_frame_iterate (F := Fp.blocks [x, r, z, p] [n, n, n, n])
    (StoresState dec n x r z p) (pcgStep A P) (Nonbreakdown A) rfl rfl rfl
    (by simp only [Mem.live_cons, Mem.live_nil, and_true]; tauto) ⟨xs, rs, zs, ps, hr, rfl⟩ hdom
    ?_).mono le_rfl ?_
  · rintro s' m' hfr hl' ⟨xs', rs', zs', ps', hread, rfl⟩ hnb
    refine (hstep [n] [x, r, z, p] τ m' _ rfl rfl ?_ (by routine_sep) hread ⟨rfl, hnb⟩ ?_).mono
      le_rfl ?_
    · exact fun w hw => hl' w (List.mem_append_left _ hw)
    · change m'.Room [x, r, z, p] [n, n, n, n]
      simp only [Mem.room_cons, Mem.room_nil, and_true, hfr.len_eq]
      exact hroom
    · rintro m'' - ⟨hpos, ys, hys, hrel⟩
      routine_nf at hys
      split_reads hys as (xs'', rs'', zs'', ps'')
      exact ⟨hpos, xs'', rs'', zs'', ps'', hys, hrel⟩
  · rintro m' - ⟨hpos, xs', rs', zs', ps', hread, hstate⟩
    exact ⟨hpos, [xs', rs', zs', ps'], hread, hstate⟩

end NLAlib.Krylov.CG.HSPCG
