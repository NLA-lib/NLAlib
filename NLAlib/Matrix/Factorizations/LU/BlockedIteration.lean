/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedPanel
public import NLAlib.Matrix.Factorizations.LU.BlockedPrefix

/-!
# Actual LU iteration inside one deferred panel

Materialize a lower column and upper row from the active pivot coordinates, then execute the
saved-operand scalar panel step. Pivot row and column agreement suffice even though the
bottom-right square still contains the panel-entry residual.

## Main results

* `NLAlib.LU.panelIteration_writes`: advance the actual stored panel prefix by one pivot.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst] [Inhabited K]

/-- Commit the current factor column/row and update the two saved-operand panel rectangles. -/
def panelIteration : Stmt Op Tst := ops% [n, k, stop] (R, L, U) → () {
  run materializeColumn [n, k] (R, L, U);
  run panelSchurStep [n, k, stop] (R)
}

/-- Original nonzero Gaussian pivots suffice to advance a stored panel state. The conclusion
contains actual words for every residual and factor entry, with canonical committed prefixes.
Only the private residual and the two factor blocks may change. -/
theorem panelIteration_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (start stop : ℕ) (k : Fin N)
    (hk : k.val < stop) (hstop : stop ≤ N)
    (hp : ∀ i : Fin N, gaussState A i.val i i ≠ 0)
    {τ : Tape K} {m : Mem K} {R L U : ℕ × ℕ}
    (hlive : m.Live [R, L, U]) (hRL : R.1 ≠ L.1) (hRU : R.1 ≠ U.1) (hLU : L.1 ≠ U.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) (hUroom : U.2 + N * N ≤ m.store.len U.1)
    (hstate : IsPanelPrefix dec A start stop k.val R L U m.store) :
    Writes .total I τ (panelIteration (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val, stop] [R, L, U])
      (Store.inBuf R.1 ⊔ Store.inBlock L.1 L.2 (N * N) ⊔ Store.inBlock U.1 U.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ IsPanelPrefix dec A start stop (k.val + 1) R L U m'.store) m := by
  obtain ⟨hlR, hlL, hlU⟩ : R.1 < m.store.length ∧ L.1 < m.store.length ∧
      U.1 < m.store.length := by simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlive
  obtain ⟨rw, lw, uw, hR, hL, hU, hres, hlo, hup⟩ := hstate
  obtain ⟨rs, hrs, hrlen, hrdata⟩ := hR.readBlock rfl
  obtain ⟨ls, hls, hllen, hldata⟩ := hL.readBlock rfl
  obtain ⟨us, hus, hulen, hudata⟩ := hU.readBlock rfl
  have hcol (i : Fin N) : decodeMatrix dec N N rs i k = gaussState A k.val i k := by
    rw [decodeMatrix_apply, hrdata i i.isLt k k.isLt, hres i k]
    exact luPanelState_apply_column A start stop k i hk
  have hrow (j : Fin N) : decodeMatrix dec N N rs k j = gaussState A k.val k j := by
    rw [decodeMatrix_apply, hrdata k k.isLt j j.isLt, hres k j]
    exact luPanelState_apply_row A start stop k j hk
  have hB : decodeMatrix dec N N rs = luPanelState A start stop k.val := by
    ext i j
    rw [decodeMatrix_apply, hrdata i i.isLt j j.isLt]
    exact hres i j
  call (materializeColumn_meets hI hcmp) [N, k.val] (R, L, U) (pre := k.isLt)
    as m₁ hfr₁ hpos₁ (ls', us') hpost
  have hnew := materializeColumnSpec_prefix_of_column_row hM A k hpost hcol hrow
    (by intro i j; rw [decodeMatrix_apply, hldata i i.isLt j j.isLt]; exact hlo i j)
    (by intro i j; rw [decodeMatrix_apply, hudata i i.isLt j j.isLt]; exact hup i j)
  have hrs₁ : m₁.store.readBlock R.1 R.2 (N * N) = some rs := by keep
  have hpivot : decodeMatrix dec N N rs k k ≠ 0 := hcol k ▸ hp k
  have hstep := panelSchurStep_writes (τ := τ) hI hM k stop hk hstop
    (by rw [hfr₁.length_eq]; exact hlR) hrs₁ hpivot
  refine (hstep.in_frame rfl rfl (by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using
      (show R.1 < m₁.store.length from by rw [hfr₁.length_eq]; exact hlR))).mono
    (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, W, hW, hdec⟩
  have hls₂ : m₂.store.readBlock L.1 L.2 (N * N) = some ls' := by keep
  have hus₂ : m₂.store.readBlock U.1 U.2 (N * N) = some us' := by keep
  rw [hB, luPanelStep_luPanelState A start stop k hk hp] at hdec
  refine ⟨hp₂.trans hpos₁, W, (fun i j => vec ls' (j * N + i)),
    (fun i j => vec us' (j * N + i)), hW, Store.holdsMat_of_readBlock rfl hls₂,
    Store.holdsMat_of_readBlock rfl hus₂, ?_, ?_, ?_⟩
  · intro i j
    exact congrFun (congrFun hdec i) j
  · intro i j
    simpa only [decodeMatrix_apply] using hnew.1 i j
  · intro i j
    simpa only [decodeMatrix_apply] using hnew.2 i j

end NLAlib.LU
