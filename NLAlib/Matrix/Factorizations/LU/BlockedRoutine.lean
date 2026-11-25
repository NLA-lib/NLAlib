/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedExecution
public import NLAlib.Ops.Logic.Allocation

/-!
# Complete blocked scalar LU success and frame

The actual positive-order body copies its source before any factor write, executes every
clipped panel and packed scalar GEMM correction, and releases the residual workspace.
The dimension-only guard makes the empty body independent of handles and arithmetic laws.

## Main results

* `NLAlib.LU.factorBlocked_writes`: full actual success with source/output overlap.
* `NLAlib.LU.factorBlocked_meets`: the ordinary exact blocked LU routine judgment.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst] [Inhabited K]

/-- Complete exact blocked LU from the original Gaussian-pivot condition, with only the two
factor blocks written. Source and factors may overlap because copying occurs first. All
handle, capacity and factor-separation requirements are guarded by positive matrix order. -/
theorem factorBlocked_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) {N : ℕ}
    (B Q : ℕ) (hB : 0 < B) (hQ : Q = (N + B - 1) / B)
    {τ : Tape K} {m : Mem K} {A L U : ℕ × ℕ} {As : List K}
    (hp : ∀ i : Fin N, gaussState (decodeMatrix dec N N As) i.val i i ≠ 0)
    (hlive : 0 < N → m.Live [A, L, U]) (hLU : 0 < N → L.1 ≠ U.1)
    (hAs : m.store.readBlock A.1 A.2 (N * N) = some As)
    (hLroom : 0 < N → L.2 + N * N ≤ m.store.len L.1)
    (hUroom : 0 < N → U.2 + N * N ≤ m.store.len U.1) :
    Writes .total I τ (factorBlocked (Op := Op) (Tst := Tst)).body
      (Env.frame [N, B, Q] [A, L, U]) (Fp.blocks [L, U] [N * N, N * N])
      (fun m' => m'.pos = m.pos ∧ ∃ ls us : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some ls ∧
        m'.store.readBlock U.1 U.2 (N * N) = some us ∧
        decodeMatrix dec N N ls = luLower (decodeMatrix dec N N As) ∧
        decodeMatrix dec N N us = luUpper (decodeMatrix dec N N As) ∧
        IsLU (decodeMatrix dec N N As) (decodeMatrix dec N N ls) (decodeMatrix dec N N us)) m := by
  refine writes_ifPos (n := N) rfl ?_
  by_cases hn : 0 < N
  · rw [if_pos hn]
    obtain ⟨hlA, hlL, hlU⟩ : A.1 < m.store.length ∧ L.1 < m.store.length ∧
        U.1 < m.store.length := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlive hn
    apply writes_allocs_preserving_post (lens := [.var 0 * .var 0]) (ns := [N * N]) rfl
    · intro s s' p hBelow hpost
      obtain ⟨hpos, ls, us, hls, hus, hlo, hup, hlu⟩ := hpost
      exact ⟨hpos, ls, us, (hBelow.readBlock hlL L.2 (N * N)).trans hls,
        (hBelow.readBlock hlU U.2 (N * N)).trans hus, hlo, hup, hlu⟩
    · intro store hlength hlens hBelow
      have hRlen : store.len m.store.length = N * N := by simpa using hlens 0 (by simp)
      have hRlive : m.store.length < store.length := by
        simp only [List.length_singleton] at hlength
        omega
      have hLive : (Mem.mk store m.pos).Live [A, (m.store.length, 0), L, U] := by
        simp only [Mem.live_cons, Mem.live_nil, and_true]
        exact ⟨by omega, hRlive, by omega, by omega⟩
      refine ((blockedWithScratch_writes hI hcmp hM B Q hB hQ hp hLive
        (by omega) (by omega) (by omega) (hLU hn)
        (Store.Below.readBlock_of hBelow hlA hAs) (by simpa using hRlen.ge)
        (by simpa only [(hBelow L.1 hlL).1] using hLroom hn)
        (by simpa only [(hBelow U.1 hlU).1] using hUroom hn)).in_frame
          rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
  · rw [if_neg hn]
    have hz : N = 0 := by omega
    subst N
    have hlo : decodeMatrix dec 0 0 [] = luLower (decodeMatrix dec 0 0 As) := Subsingleton.elim _ _
    have hup : decodeMatrix dec 0 0 [] = luUpper (decodeMatrix dec 0 0 As) := Subsingleton.elim _ _
    refine ⟨rfl, [], [], rfl, rfl, hlo, hup, ?_⟩
    have hcanon : IsLU (decodeMatrix dec 0 0 As) (luLower (decodeMatrix dec 0 0 As))
        (luUpper (decodeMatrix dec 0 0 As)) := isLU_luLower_luUpper (fun i hi => i.elim0)
    exact (congrArg₂ (IsLU (decodeMatrix dec 0 0 As)) hlo hup).mpr hcanon

/-- The actual fixed blocked program meets its exact factor specification at every admitted
order and positive symbolic block size, with its exact ceiling count and final clipped panel.
The hypothesis concerns original Gaussian pivots, never a supplied successful trace. -/
theorem factorBlocked_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) :
    (factorBlocked (Op := Op) (Tst := Tst)).Meets I (factorBlockedSpec dec) := by
  routine_intro [N, B, Q] (A, L, U) reads (As)
  obtain ⟨hB, hQ, hp⟩ := hpre
  refine (factorBlocked_writes hI hcmp hM B Q hB hQ hp (fun _ => hlive) (fun _ => hLU)
    hAs (fun _ => hroom.1) (fun _ => hroom.2)).mono le_rfl ?_
  rintro μ hfr ⟨hpos, ls, us, hls, hus, hlo, hup, hlu⟩
  exact ⟨hpos, [ls, us], Mem.readBlocks_of_cons hls (Mem.readBlocks_of_cons hus rfl), hlo, hup, hlu⟩

end NLAlib.LU
