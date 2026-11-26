/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedRectangleExecution

/-!
# Two actual saved-operand panel rectangles

Both scalar rectangle updates read the same saved pivot vectors and coefficient. Their
precise frames reconstruct the intermediate matrix, while the aggregate fragment owns only
its private residual and packed workspace buffers. The deferred bottom-right square is not
updated by either rectangle.

## Main results

* `NLAlib.LU.panelRectangles_writes`: the two actual scalar updates realize `luPanelStep`.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- The two disjoint panel rectangles, reusing the same packed workspace and original saved
pivot operands. This is the fragment called after preparation in one panel pivot. -/
def panelRectangles : Stmt Op Tst := ops% [n, k, stop] (a, c, r, R, P) → () {
  run rankOneStridedWithScratch [n - k, stop - k, n]
    (a, c[k], r[k], R[k * n + k], P);
  run rankOneStridedWithScratch [stop - k, n - stop, n]
    (a, c[k], r[stop], R[stop * n + k], P)
}

private theorem rectangle_footprint_le (rows cols ld : ℕ) (a x y R P : ℕ × ℕ) :
    (rankOneStridedWithScratch (Op := Op) (Tst := Tst)).footprint [rows, cols, ld]
      ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).operands [rows, cols, ld]
        [a, x, y, R, P]) ≤ Store.inBuf R.1 ⊔ Store.inBuf P.1 := by
  change Fp.views [R, P] [⟨rows, some (cols, ld)⟩, View.block (rows * cols)] ≤ _
  simp only [Fp.views, Fp.inView_block, sup_bot_eq]
  exact sup_le (le_trans (Fp.inView_le_inBuf _ _ _) le_sup_left)
    (le_trans (Fp.inBlock_le_inBuf _ _ _) le_sup_right)

variable {K : Type} [Inhabited K]

/-- Two actual scalar rectangle updates give the panel step and retain a complete stored
residual witness. The coefficient and vectors are original saved operands; no division or
factorization result is assumed about the execution. -/
theorem panelRectangles_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℝ) (rk : Fin N) (stop : ℕ)
    (hks : rk.val ≤ stop) (hstop : stop ≤ N) {τ : Tape K} {m : Mem K}
    {a c r R P : ℕ × ℕ} {av : K} {cs rs : List K} {old : ℕ → ℕ → K}
    (hStore : m.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ old)
    (hcur : ∀ i j : Fin N, dec (old i j) = B i j)
    (haRead : m.store.readBlock a.1 a.2 1 = some [av])
    (hcRead : m.store.readBlock c.1 c.2 N = some cs)
    (hrRead : m.store.readBlock r.1 r.2 N = some rs)
    (hLive : m.Live [a, c, r, R, P])
    (haR : a.1 ≠ R.1) (haP : a.1 ≠ P.1) (hcR : c.1 ≠ R.1) (hcP : c.1 ≠ P.1)
    (hrR : r.1 ≠ R.1) (hrP : r.1 ≠ P.1) (hRP : R.1 ≠ P.1)
    (hP : P.2 + N * N ≤ m.store.len P.1) (hcoef : dec av = -1 / B rk rk)
    (hC : ∀ i : Fin N, dec (vec cs i.val) = B i rk)
    (hR : ∀ j : Fin N, dec (vec rs j.val) = B rk j) :
    Writes .total I τ (panelRectangles (Op := Op) (Tst := Tst))
      (Env.frame [N, rk.val, stop] [a, c, r, R, P]) (Store.inBuf R.1 ⊔ Store.inBuf P.1)
      (fun m' => m'.pos = m.pos ∧ ∃ W : ℕ → ℕ → K,
        m'.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ W ∧
          (fun i j : Fin N => dec (W i j)) = luPanelStep B rk stop) m := by
  let k := rk.val
  have hrows : k + (N - k) ≤ N := by dsimp [k]; omega
  have hcols : k + (stop - k) ≤ N := by dsimp [k]; omega
  have htail : stop + (N - stop) ≤ N := by omega
  have hx₁ : m.store.readBlock c.1 (c.2 + k) (N - k) =
      some ((cs.drop k).take (N - k)) := Store.readBlock_sub hcRead hrows
  have hy₁ : m.store.readBlock r.1 (r.2 + k) (stop - k) =
      some ((rs.drop k).take (stop - k)) := Store.readBlock_sub hrRead hcols
  have hl₁ : m.Live [a, (c.1, c.2 + k), (r.1, r.2 + k), R, P] := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using hLive
  have hfirst := rankOneStridedWithScratch_writes_rectangle_of_apart (τ := τ) hI hM B B rk
    k k (N - k) (stop - k) hrows hcols hStore hcur haRead hx₁ hy₁ hl₁
    haR haP hcR hcP hrR hrP hRP hP hcoef
    (by
      intro i
      simpa only [vec_drop_take i.isLt, Fin.val_castLE, Fin.val_natAdd] using
        hC (Fin.castLE hrows (Fin.natAdd k i)))
    (by
      intro j
      simpa only [vec_drop_take j.isLt, Fin.val_castLE, Fin.val_natAdd] using
        hR (Fin.castLE hcols (Fin.natAdd k j)))
  unfold panelRectangles
  refine (hfirst.in_frame rfl rfl (Routine.live_env (Routine.live_operands (by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using hl₁)))).seq_le
    (rectangle_footprint_le _ _ _ _ _ _ _ _) ?_
  intro m₁ hfr₁ ⟨hp₁, W₁, hW₁, hdec₁⟩
  have hglobal := hfr₁.mono (rectangle_footprint_le _ _ _ _ _ _ _ _)
  have ha₁ : m₁.store.readBlock a.1 a.2 1 = some [av] := by keep
  have hc₁ : m₁.store.readBlock c.1 c.2 N = some cs := by keep
  have hr₁ : m₁.store.readBlock r.1 r.2 N = some rs := by keep
  have hx₂ : m₁.store.readBlock c.1 (c.2 + k) (stop - k) =
      some ((cs.drop k).take (stop - k)) := Store.readBlock_sub hc₁ hcols
  have hy₂ : m₁.store.readBlock r.1 (r.2 + stop) (N - stop) =
      some ((rs.drop stop).take (N - stop)) := Store.readBlock_sub hr₁ htail
  have hl₂ : m₁.Live [a, (c.1, c.2 + k), (r.1, r.2 + stop), R, P] := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using hLive.congr hfr₁.length_eq
  have hpRoom : P.2 + N * N ≤ m₁.store.len P.1 := by rw [hfr₁.len_eq]; exact hP
  have hsecond := rankOneStridedWithScratch_writes_rectangle_of_apart (τ := τ) hI hM B
    (luPanelRectangle B B rk k k (N - k) (stop - k)) rk k stop (stop - k) (N - stop)
    hcols htail hW₁ (fun i j => congrFun (congrFun hdec₁ i) j) ha₁ hx₂ hy₂ hl₂
    haR haP hcR hcP hrR hrP hRP hpRoom hcoef
    (by
      intro i
      simpa only [vec_drop_take i.isLt, Fin.val_castLE, Fin.val_natAdd] using
        hC (Fin.castLE hcols (Fin.natAdd k i)))
    (by
      intro j
      simpa only [vec_drop_take j.isLt, Fin.val_castLE, Fin.val_natAdd] using
        hR (Fin.castLE htail (Fin.natAdd stop j)))
  refine (hsecond.in_frame rfl rfl (Routine.live_env (Routine.live_operands (by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using hl₂)))).mono
    (rectangle_footprint_le _ _ _ _ _ _ _ _) ?_
  intro m₂ hfr₂ ⟨hp₂, W₂, hW₂, hdec₂⟩
  exact ⟨hp₂.trans hp₁, W₂, hW₂, hdec₂.trans (luPanelRectangle_twice B rk stop hks hstop)⟩

end NLAlib.LU
