/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedRoutine
public import NLAlib.Matrix.Factorizations.Cholesky.BlockedScale
public import NLAlib.Ops.Logic.Allocation

/-!
# Actual blocked Cholesky through scalar LU and column scaling

The complete blocked scalar LU routine supplies canonical unit lower entries and upper
pivots. Actual square-root column scaling gives the canonical Cholesky factor and literal
upper zeros. The source is copied before output initialization, so it may overlap the output.
The upper workspace is scoped; a dimension-only guard bypasses every frame at order zero.

## Main results

* `NLAlib.Cholesky.factorBlocked_writes`: full success, exact factor and source-overlap frame.
* `NLAlib.Cholesky.factorBlocked_meets`: the ordinary exact blocked Cholesky judgment.
* `NLAlib.Cholesky.eval_factorBlocked_zero`: arbitrary-handle empty execution.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Blocked Cholesky computation on caller-owned upper scratch: actual blocked LU,
then actual scalar square-root scaling of its unit lower columns. -/
def blockedWithScratch : Stmt Op Tst := ops% [n, b, q] (A, L, U) → () {
  run LU.factorBlocked [n, b, q] (A, L, U);
  run scaleLuColumns [n] (L, U)
}

/-- Complete blocked Cholesky with positive symbolic block size and exact ceiling count.
The empty dimension performs no scalar operation, allocation or operand frame. -/
def factorBlocked : Routine Op Tst := routine% [n, b, q] (A : n * n) → (L : n * n) {
  ifPos n {
    let U ← alloc (n * n);
    run blockedWithScratch [n, b, q] (A, L, U)
  }
}

/-- Raw empty execution needs no live handles, capacities, separation or arithmetic laws. -/
theorem eval_factorBlocked_zero (I : Interp Op Tst K) (τ : Tape K) (B Q : ℕ)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (factorBlocked (Op := Op) (Tst := Tst)).body
      (Env.frame [0, B, Q] args) m = some m := by
  rfl

variable [Inhabited K]

/-- Original positive definiteness and valid block controls give the canonical Cholesky
factor, the strict positive-diagonal Gram predicate, and actual upper zero-literal words. -/
def factorBlockedSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n, b, q] (As) → (Ls) requires
    0 < b ∧ q = (n + b - 1) / b ∧ (decodeMatrix dec n n As).PosDef ensures
    decodeMatrix dec n n Ls = choleskyLower (decodeMatrix dec n n As) ∧
      IsCholesky (decodeMatrix dec n n As) (decodeMatrix dec n n Ls) ∧
      (∀ i j : Fin n, i < j → vec Ls (j.val * n + i.val) = M.lit 0)

/-- Actual blocked LU and scalar column scaling compose on the original source words.
Source/factor overlap is permitted; only the lower and upper workspace blocks can change. -/
theorem blockedWithScratch_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) {N : ℕ}
    (B Q : ℕ) (hB : 0 < B) (hQ : Q = (N + B - 1) / B)
    {τ : Tape K} {m : Mem K} {A L U : ℕ × ℕ} {As : List K}
    (hA : (decodeMatrix dec N N As).PosDef) (hlive : m.Live [A, L, U]) (hLU : L.1 ≠ U.1)
    (hAs : m.store.readBlock A.1 A.2 (N * N) = some As)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) (hUroom : U.2 + N * N ≤ m.store.len U.1) :
    Writes .total I τ (blockedWithScratch (Op := Op) (Tst := Tst))
      (Env.frame [N, B, Q] [A, L, U]) (Fp.blocks [L, U] [N * N, N * N])
      (fun m' => m'.pos = m.pos ∧ ∃ Bs : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some Bs ∧
        decodeMatrix dec N N Bs = choleskyLower (decodeMatrix dec N N As) ∧
        IsCholesky (decodeMatrix dec N N As) (decodeMatrix dec N N Bs) ∧
        (∀ i j : Fin N, i < j → vec Bs (j.val * N + i.val) = M.lit 0)) m := by
  have hp : ∀ i : Fin N, gaussState (decodeMatrix dec N N As) i.val i i ≠ 0 :=
    fun i => (hA.gaussState_apply_self_pos i).ne'
  unfold blockedWithScratch
  refine ((LU.factorBlocked_writes hI hcmp hM B Q hB hQ hp (fun _ => hlive) (fun _ => hLU)
    hAs (fun _ => hLroom) (fun _ => hUroom)).in_frame rfl rfl hlive).seq_le le_rfl ?_
  intro μ hfr ⟨hpos, ls, us, hls, hus, hlo, hup, hlu⟩
  obtain ⟨hlA, hlL, hlU⟩ : A.1 < μ.store.length ∧ L.1 < μ.store.length ∧
      U.1 < μ.store.length := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlive.congr hfr.length_eq
  have hlroom : L.2 + N * N ≤ μ.store.len L.1 := by rw [hfr.len_eq]; exact hLroom
  call (scaleLuColumns_meets hI) [N] (L, U) as ν hfr' hpos' (Bs) hpost
  have hnum := decodeMatrix_eq_choleskyLower_of_scaleLuColumnsSpec hM hA hpost hlo hup
  refine ⟨hpos'.trans hpos, Bs, hBs, hnum, ?_, vec_eq_lit_zero_of_scaleLuColumnsSpec hpost⟩
  rw [hnum]
  exact hA.isCholesky_choleskyLower

/-- Complete blocked Cholesky from the original positive-definite matrix, with one net factor
write and all scratch released. Source/output overlap is safe. Empty order imposes no handle
or capacity requirement, even when an invalid output equals the fresh upper handle. -/
theorem factorBlocked_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) {N : ℕ}
    (B Q : ℕ) (hB : 0 < B) (hQ : Q = (N + B - 1) / B)
    {τ : Tape K} {m : Mem K} {A L : ℕ × ℕ} {As : List K}
    (hA : (decodeMatrix dec N N As).PosDef) (hlive : 0 < N → m.Live [A, L])
    (hAs : m.store.readBlock A.1 A.2 (N * N) = some As)
    (hLroom : 0 < N → L.2 + N * N ≤ m.store.len L.1) :
    Writes .total I τ (factorBlocked (Op := Op) (Tst := Tst)).body
      (Env.frame [N, B, Q] [A, L]) (Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ ∃ Bs : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some Bs ∧
        decodeMatrix dec N N Bs = choleskyLower (decodeMatrix dec N N As) ∧
        IsCholesky (decodeMatrix dec N N As) (decodeMatrix dec N N Bs) ∧
        (∀ i j : Fin N, i < j → vec Bs (j.val * N + i.val) = M.lit 0)) m := by
  refine writes_ifPos (n := N) rfl ?_
  by_cases hn : 0 < N
  · rw [if_pos hn]
    have hlA : A.1 < m.store.length := hlive hn A (by simp)
    have hlL : L.1 < m.store.length := hlive hn L (by simp)
    apply writes_allocs_preserving_post (lens := [.var 0 * .var 0]) (ns := [N * N]) rfl
    · intro s s' p hBelow hpost
      obtain ⟨hpos, Bs, hBs, hnum, hchol, hupper⟩ := hpost
      exact ⟨hpos, Bs, (hBelow.readBlock hlL L.2 (N * N)).trans hBs, hnum, hchol, hupper⟩
    · intro store hlength hlens hBelow
      have hUlen : store.len m.store.length = N * N := by simpa using hlens 0 (by simp)
      have hUlive : m.store.length < store.length := by
        simp only [List.length_singleton] at hlength
        omega
      have hLive : (Mem.mk store m.pos).Live [A, L, (m.store.length, 0)] := by
        simp only [Mem.live_cons, Mem.live_nil, and_true]
        exact ⟨by omega, by omega, hUlive⟩
      refine ((blockedWithScratch_writes hI hcmp hM B Q hB hQ hA hLive (by omega)
        (Store.Below.readBlock_of hBelow hlA hAs)
        (by simpa only [(hBelow L.1 hlL).1] using hLroom hn)
        (by simpa using hUlen.ge)).in_frame rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
  · rw [if_neg hn]
    have hz : N = 0 := by omega
    subst N
    have hnum : decodeMatrix dec 0 0 [] = choleskyLower (decodeMatrix dec 0 0 As) :=
      Subsingleton.elim _ _
    refine ⟨rfl, [], rfl, hnum, ?_, fun i => i.elim0⟩
    rw [hnum]
    exact hA.isCholesky_choleskyLower

/-- The actual blocked scalar tree meets the original SPD Cholesky specification at every
order and valid positive block size, including a nondividing final clipped panel. -/
theorem factorBlocked_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) :
    (factorBlocked (Op := Op) (Tst := Tst)).Meets I (factorBlockedSpec M dec) := by
  routine_intro [N, B, Q] (A, L) reads (As)
  obtain ⟨hB, hQ, hA⟩ := hpre
  refine (factorBlocked_writes hI hcmp hM B Q hB hQ hA (fun _ => hlive) hAs
    (fun _ => hroom)).mono (by fp_sub) ?_
  rintro μ hfr ⟨hpos, Bs, hBs, hnum, hchol, hupper⟩
  exact ⟨hpos, [Bs], Mem.readBlocks_of_cons hBs rfl, hnum, hchol, hupper⟩

end NLAlib.Cholesky
