/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedIteration

/-!
# The actual clipped LU panel loop

The loop commits one factor column and row per actual pivot and performs the two saved-word
rectangle updates. Its trailing square stays at panel entry until the later scalar GEMM
correction. Nonzero pivots are hypotheses on the original matrix, not on a supplied run.

## Main results

* `NLAlib.LU.panel_writes`: actual success and the complete stored panel exit prefix.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst] [Inhabited K]

/-- Execute one actual scalar panel iteration per pivot in the supplied clipped width. -/
def panel : Stmt Op Tst := ops% [n, start, width] (R, L, U) → () {
  for t < width {
    run panelIteration [n, start + t, start + width] (R, L, U)
  }
}

/-- Original nonzero Gaussian pivots give actual success of the complete panel, including a
zero-width panel. Every factor prefix and deferred residual entry has an actual stored word. -/
theorem panel_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (start width : ℕ) (hsw : start + width ≤ N)
    (hp : ∀ i : Fin N, gaussState A i.val i i ≠ 0) {τ : Tape K} {m : Mem K}
    {R L U : ℕ × ℕ} (hlive : m.Live [R, L, U])
    (hRL : R.1 ≠ L.1) (hRU : R.1 ≠ U.1) (hLU : L.1 ≠ U.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) (hUroom : U.2 + N * N ≤ m.store.len U.1)
    (hstate : IsFactorPrefix dec A start R L U m.store) :
    Writes .total I τ (panel (Op := Op) (Tst := Tst))
      (Env.frame [N, start, width] [R, L, U])
      (Store.inBuf R.1 ⊔ Store.inBlock L.1 L.2 (N * N) ⊔ Store.inBlock U.1 U.2 (N * N))
      (fun m' => m'.pos = m.pos ∧
        IsPanelPrefix dec A start (start + width) (start + width) R L U m'.store) m := by
  unfold panel
  refine (writes_loop rfl
    (fun _ => Store.inBuf R.1 ⊔ Store.inBlock L.1 L.2 (N * N) ⊔
      Store.inBlock U.1 U.2 (N * N)) (fun _ _ => le_rfl)
    (fun t μ => μ.pos = m.pos ∧ IsPanelPrefix dec A start (start + width) (start + t)
      R L U μ.store) ⟨rfl, by simpa only [Nat.add_zero] using hstate.toPanelPrefix (start + width)⟩
    ?_).mono le_rfl (fun _ _ h => h)
  intro t ht μ hfr ⟨hpos, hpref⟩
  let k : Fin N := ⟨start + t, by omega⟩
  have hl' := hlive.congr hfr.length_eq
  refine ((panelIteration_writes hI hcmp hM A start (start + width) k (by dsimp [k]; omega)
    hsw hp hl' hRL hRU hLU (by simpa only [hfr.len_eq] using hLroom)
    (by simpa only [hfr.len_eq] using hUroom) hpref).in_frame rfl rfl hl').mono le_rfl ?_
  intro μ' hfr' ⟨hp', hpref'⟩
  refine ⟨hp'.trans hpos, ?_⟩
  simpa only [k, Nat.add_assoc] using hpref'

end NLAlib.LU
