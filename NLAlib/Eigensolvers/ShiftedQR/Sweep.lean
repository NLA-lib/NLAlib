/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Round
public import NLAlib.Matrix.QRIteration.ShiftedQRConjugation
public import NLAlib.Ops.Logic.Loop

/-!
# Exact sweep of the scalar Givens QR state

The loop invariant is the existing mathematical Givens state and its conjugation of the
original output matrix. Each round invokes the proved scalar transition. No upper Hessenberg
premise is needed to identify this computation with the defined Givens sequence.

## Main results

* `NLAlib.ShiftedQR.sweep_writes`: the total loop computes the mathematical Givens state.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- The initialized scalar sweep computes the existing Givens state and conjugates the output
by its accumulated unitary factor. This covers zero-size sweeps and zero coefficient pairs. -/
theorem sweep_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {w z cf : ℕ × ℕ}
    {W H : Matrix (Fin n) (Fin n) ℂ}
    (hW : HoldsMatrix w W m.store) (hH : HoldsMatrix z H m.store)
    (hc : cf.2 + 4 ≤ m.store.len cf.1)
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * (n * n)))
      (Store.inBlock z.1 z.2 (2 * (n * n))))
    (hwc : Fp.Disj (Store.inBlock w.1 w.2 (2 * (n * n)))
      (Store.inBlock cf.1 cf.2 4))
    (hzc : Fp.Disj (Store.inBlock z.1 z.2 (2 * (n * n)))
      (Store.inBlock cf.1 cf.2 4))
    (hl : m.Live [w, z, cf, w, z]) :
    Writes .total I τ sweep.body (Env.frame [n] [w, z, cf, w, z])
      (Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
        Store.inBlock z.1 z.2 (2 * (n * n)) ⊔ Store.inBlock cf.1 cf.2 4)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix w (givensHessenbergState W (n - 1)).2 m'.store ∧
        HoldsMatrix z ((givensHessenbergState W (n - 1)).1ᴴ * H *
          (givensHessenbergState W (n - 1)).1) m'.store) m := by
  let F := Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
    Store.inBlock z.1 z.2 (2 * (n * n)) ⊔ Store.inBlock cf.1 cf.2 4
  unfold sweep
  refine writes_loop rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧
      HoldsMatrix w (givensHessenbergState W k).2 m'.store ∧
      HoldsMatrix z ((givensHessenbergState W k).1ᴴ * H *
        (givensHessenbergState W k).1) m'.store) ?_ ?_
  · simpa only [givensHessenbergState, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one] using And.intro (rfl : m.pos = m.pos) (And.intro hW hH)
  · intro k hk m' hfr ⟨hp, hW', hH'⟩
    have hround := round_writes (τ := τ) (m := m') (n := n) (k := k) hS hE hCmp (by omega) hW' hH'
      (by rw [hfr.len_eq]; exact hc) hwz hwc hzc
    refine (hround.in_frame rfl rfl ?_).mono le_rfl ?_
    · exact hl.congr hfr.length_eq
    · intro m'' _ ⟨hp', hW'', hH''⟩
      exact ⟨hp'.trans hp, hW'', by
        rw [conj_givensHessenbergState_succ]
        exact hH''⟩

end NLAlib.ShiftedQR
