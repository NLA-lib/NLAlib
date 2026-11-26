/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedPanelLoop
public import NLAlib.Matrix.Factorizations.LU.BlockedTrailing

/-!
# One complete LU panel and scalar trailing product

The actual panel loop is followed by a packed scalar GEMM correction using the stored lower
and upper factor rectangles. Its precise destination frame restores the complete Gaussian
residual, so the next block starts from the ordinary stored factor-prefix invariant.

## Main results

* `NLAlib.LU.blockedStep_writes`: actual panel and scalar product restore a Gaussian boundary.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst] [Inhabited K]

/-- One completed panel is followed by a genuine scalar matrix-product trailing update.
The stored lower and upper rectangles are packed before multiplication. -/
def blockedStep : Stmt Op Tst :=
  ops% [n, start, width] (R, L, U) → () {
    run panel [n, start, width] (R, L, U);
    run ScalarMatrix.update [n - (start + width), width, n - (start + width), n, n, n]
      (L[start * n + (start + width)], U[(start + width) * n + start],
        R[(start + width) * n + (start + width)])
  }

/-- A whole actual panel and scalar trailing product advance the canonical stored prefix.
The mathematical precondition is nonzero original Gaussian pivots; every claimed store and
matrix result is derived from these actual instruction trees. -/
theorem blockedStep_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (start width : ℕ) (hsw : start + width ≤ N)
    (hp : ∀ i : Fin N, gaussState A i.val i i ≠ 0) {τ : Tape K} {m : Mem K}
    {R L U : ℕ × ℕ} (hlive : m.Live [R, L, U])
    (hRL : R.1 ≠ L.1) (hRU : R.1 ≠ U.1) (hLU : L.1 ≠ U.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) (hUroom : U.2 + N * N ≤ m.store.len U.1)
    (hstate : IsFactorPrefix dec A start R L U m.store) :
    Writes .total I τ (blockedStep (Op := Op) (Tst := Tst))
      (Env.frame [N, start, width] [R, L, U])
      (Store.inBuf R.1 ⊔ Store.inBlock L.1 L.2 (N * N) ⊔ Store.inBlock U.1 U.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ IsFactorPrefix dec A (start + width) R L U m'.store) m := by
  unfold blockedStep
  refine ((panel_writes hI hcmp hM A start width hsw hp hlive hRL hRU hLU hLroom hUroom
    hstate).in_frame rfl rfl hlive).seq_le le_rfl ?_
  intro μ hfr ⟨hpos, hpref⟩
  obtain ⟨rw, lw, uw, hR, hL, hU, hres, hlo, hup⟩ := hpref
  let stop := start + width
  have htail : stop + (N - stop) ≤ N := by dsimp [stop]; omega
  have hLs := hL.readView_rectangle stop start (N - stop) width htail hsw
  have hUs := hU.readView_rectangle start stop width (N - stop) hsw htail
  have hRs := hR.readView_rectangle stop stop (N - stop) (N - stop) htail htail
  obtain ⟨hlR, hlL, hlU⟩ : R.1 < μ.store.length ∧ L.1 < μ.store.length ∧
      U.1 < μ.store.length := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlive.congr hfr.length_eq
  call (ScalarMatrix.update_meets hI) [N - stop, width, N - stop, N, N, N]
    ((L.1, L.2 + start * N + stop), (U.1, U.2 + stop * N + start),
      (R.1, R.2 + stop * N + stop)) (pre := fun _ => Nat.sub_le _ _)
    as ν hfr' hpos' (ts) hpost
  case' hcall =>
    exact [(EntryCodec.scalar K).packMatrix (N - stop) width
      (fun i j => lw (stop + i) (start + j)),
      (EntryCodec.scalar K).packMatrix width (N - stop)
        (fun i j => uw (start + i) (stop + j)),
      (EntryCodec.scalar K).packMatrix (N - stop) (N - stop)
        (fun i j => rw (stop + i) (stop + j))]
  case' hr =>
    change μ.readViews [(L.1, L.2 + start * N + stop), (U.1, U.2 + stop * N + start),
      (R.1, R.2 + stop * N + stop)] [⟨N - stop, some (width, N)⟩,
        ⟨width, some (N - stop, N)⟩, ⟨N - stop, some (N - stop, N)⟩] = some _
    exact Mem.readViews_of_cons hLs (Mem.readViews_of_cons hUs (Mem.readViews_of_cons hRs rfl))
  case' hle =>
    change Fp.views [(R.1, R.2 + stop * N + stop)]
      [⟨N - stop, some (N - stop, N)⟩] ≤ _
    simp only [Fp.views, sup_bot_eq]
    exact le_trans (Fp.inView_le_inBuf _ _ _) (by fp_sub)
  case' hpre => exact fun _ => Nat.sub_le _ _
  case' hroom =>
    change (⟨N - stop, some (N - stop, N)⟩ : View).Fits (R.2 + stop * N + stop)
      (μ.store.len R.1) ∧ True
    refine ⟨?_, trivial⟩
    by_cases hz : 0 < (N - stop) * (N - stop)
    · exact Store.fits_of_readView hRs hz
    · intro q hq
      change q < (N - stop) * (N - stop) at hq
      omega
  let F : Matrix (Fin N) (Fin N) ℝ := fun i j => dec (lw i j)
  let G : Matrix (Fin N) (Fin N) ℝ := fun i j => dec (uw i j)
  have hfrect : μ.store.EqOff (Fp.inView R.1 (R.2 + stop * N + stop)
      ⟨N - stop, some (N - stop, N)⟩) ν.store := by
    simpa only [Fp.views, sup_bot_eq] using hfr'
  obtain ⟨W, hW, hdec⟩ := trailingUpdateSpec_gaussState hM A F G start width hsw htail
    (fun i j hj => by simpa only [if_pos hj] using hlo i j)
    (fun i j hi => by simpa only [if_pos hi] using hup i j) hR hres hfrect hpost hts
    (by intro i t; rw [decodeMatrix, EntryCodec.matrix_packMatrix]; rfl)
    (by intro t j; rw [decodeMatrix, EntryCodec.matrix_packMatrix]; rfl)
    (by
      intro i j
      rw [decodeMatrix, EntryCodec.matrix_packMatrix]
      exact hres (Fin.castLE htail (Fin.natAdd stop i))
        (Fin.castLE htail (Fin.natAdd stop j)))
  have hL' : ν.store.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw :=
    hfrect.keep (Store.readsOnly_holdsMat _ _) (by
      intro b i hr hl
      exact hRL ((Fp.inView_apply.mp hr).1.symm.trans hl.1)) hL
  have hU' : ν.store.HoldsMat ⟨U.1, U.2, N, N, N⟩ uw :=
    hfrect.keep (Store.readsOnly_holdsMat _ _) (by
      intro b i hr hu
      exact hRU ((Fp.inView_apply.mp hr).1.symm.trans hu.1)) hU
  refine ⟨hpos'.trans hpos, W, lw, uw, hW, hL', hU', ?_, hlo, hup⟩
  intro i j
  exact congrFun (congrFun hdec i) j

end NLAlib.LU
