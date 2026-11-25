/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.PivotedLoop

/-!
# Full stored diagonal-pivoted semidefinite Cholesky

The complete actual scalar routine returns a lower factor and the stored absolute pivot log.
That log determines the symmetric source permutation and records each first-maximum diagonal
choice. Singular semidefinite inputs need no nonzero-pivot assumption. The same copy-first
body supports a genuine in-place interface. All caller handles remain live at order zero.

## Main results

* `NLAlib.Cholesky.pivotedRightLooking_meets`: full exact scalar success and Gram guarantee.
* `NLAlib.Cholesky.pivotedRightLookingInPlace_meets`: the same guarantee in place.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- The full scoped body admits source/output overlap because copying precedes the first
output write. Only the factor and log buffers must differ. The actual output blocks satisfy
the ordinary numerical specification; no execution or chosen-pivot hypothesis is used. -/
theorem pivotedRightLooking_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hlit : IsIndexLit M I) (hcmp : IsCmp dec I) (hQ : IsToNat dec I)
    (hM : ExactModel dec M) {N : ℕ} {τ : Tape K} {m : Mem K} {A L H : ℕ × ℕ}
    {as : List K} (hlive : m.Live [A, L, H]) (hLH : L.1 ≠ H.1)
    (has : m.store.readBlock A.1 A.2 (N * N) = some as)
    (hA : (decodeMatrix dec N N as).PosSemidef)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hHroom : H.2 + N ≤ m.store.len H.1) :
    Writes .total I τ (pivotedRightLooking (Op := Op) (Tst := Tst)).body
      (Env.frame [N] [A, L, H])
      (Store.inBlock L.1 L.2 (N * N) ⊔ Store.inBlock H.1 H.2 N)
      (fun m' => m'.pos = m.pos ∧ ∃ ls hs : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some ls ∧
        m'.store.readBlock H.1 H.2 N = some hs ∧
        (pivotedRightLookingSpec M dec).post [N] (τ.shift m.pos) [as] [ls, hs]) m := by
  refine writes_ifPos (n := N) rfl ?_
  by_cases hn : 0 < N
  · rw [if_pos hn]
    have hlA : A.1 < m.store.length := hlive A (by simp)
    have hlL : L.1 < m.store.length := hlive L (by simp)
    have hlH : H.1 < m.store.length := hlive H (by simp)
    apply writes_allocs_preserving_post (lens := [.var 0 * .var 0]) (ns := [N * N]) rfl
    · intro s s' pos hBelow ⟨hpos, ls, hs, hls, hhs, hpost⟩
      exact ⟨hpos, ls, hs, (hBelow.readBlock hlL L.2 (N * N)).trans hls,
        (hBelow.readBlock hlH H.2 N).trans hhs, hpost⟩
    · intro store hlength hlens hBelow
      have hRlen : store.len m.store.length = N * N := by simpa using hlens 0 (by simp)
      have hRlive : m.store.length < store.length := by
        simp only [List.length_singleton] at hlength
        omega
      have hLive : (Mem.mk store m.pos).Live [A, L, H, (m.store.length, 0)] := by
        simp only [Mem.live_cons, Mem.live_nil]
        exact ⟨by omega, by omega, by omega, hRlive, trivial⟩
      refine ((pivotedWithScratch_writes hI hlit hcmp hQ hM hLive
        (by omega) (by omega) (by omega) hLH (by kept) hA
        (by simpa using hRlen.ge)
        (by rw [(hBelow L.1 hlL).1]; exact hLroom)
        (by rw [(hBelow H.1 hlH).1]; exact hHroom)).in_frame
          rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
  · rw [if_neg hn]
    have hn0 : N = 0 := by omega
    subst N
    exact ⟨rfl, [], [], rfl, rfl, pivotedRightLookingSpec_empty M dec as (τ.shift m.pos)⟩

/-- The complete scalar routine succeeds on every admitted semidefinite matrix and returns
the actual absolute log and its corresponding canonical Gram factor. Only its output blocks
can change; the source, buffer shapes, tape position and scoped scratch are retained. -/
theorem pivotedRightLooking_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hlit : IsIndexLit M I) (hcmp : IsCmp dec I) (hQ : IsToNat dec I)
    (hM : ExactModel dec M) :
    (pivotedRightLooking (Op := Op) (Tst := Tst)).Meets I (pivotedRightLookingSpec M dec) := by
  routine_intro [n] (A, L, H) reads (as)
  obtain ⟨hLroom, hHroom⟩ := hroom
  refine (pivotedRightLooking_writes hI hlit hcmp hQ hM hlive hLH has hpre hLroom hHroom).mono
    (by fp_sub) ?_
  rintro m' hfr ⟨hpos, ls, hs, hls, hhs, hpost⟩
  exact ⟨by omega, [ls, hs], Mem.readBlocks_of_cons hls (Mem.readBlocks_of_cons hhs rfl), hpost⟩

/-- Overwrite a semidefinite matrix by its pivoted factor, returning its actual absolute log
in a separate buffer. The copy-first scalar body is shared with the ordinary interface. -/
def pivotedRightLookingInPlace : Routine Op Tst :=
  routine% [n] (A : n * n) → (A, H : n) {
    ifPos n {
      run pivotedRightLooking [n] (A, A, H)
    }
  }

omit [Inhabited K] in
/-- At order zero the raw scalar body reads no operands and leaves the complete memory
unchanged, for arbitrary handles, offsets, aliases and even an empty caller store. -/
theorem eval_pivotedRightLookingInPlace_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (pivotedRightLookingInPlace (Op := Op) (Tst := Tst)).body
      (Env.frame [0] args) m = some m := by
  rfl

/-- The genuine in-place interface has the same first-maximum log and semidefinite Gram
postcondition, with restored scratch and no source/output admission predicate. -/
theorem pivotedRightLookingInPlace_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hlit : IsIndexLit M I) (hcmp : IsCmp dec I) (hQ : IsToNat dec I)
    (hM : ExactModel dec M) :
    (pivotedRightLookingInPlace (Op := Op) (Tst := Tst)).Meets I
      (pivotedRightLookingSpec M dec) := by
  routine_intro [n] (A, H) reads (as)
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    obtain ⟨hAroom, hHroom⟩ := hroom
    have hlAAH : m.Live [A, A, H] := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true, and_self_left] using hlive
    refine ((pivotedRightLooking_writes hI hlit hcmp hQ hM hlAAH hAH has hpre
      hAroom hHroom).in_frame
      rfl rfl hlAAH).mono (by fp_sub) ?_
    rintro m' hfr ⟨hpos, ls, hs, hls, hhs, hpost⟩
    exact ⟨by omega, [ls, hs], Mem.readBlocks_of_cons hls (Mem.readBlocks_of_cons hhs rfl), hpost⟩
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    exact ⟨rfl, [[], []],
      Mem.readBlocks_of_cons rfl (Mem.readBlocks_of_cons rfl rfl),
      pivotedRightLookingSpec_empty M dec as (τ.shift m.pos)⟩


end NLAlib.Cholesky
