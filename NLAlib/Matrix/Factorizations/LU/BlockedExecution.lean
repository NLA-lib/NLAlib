/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Blocked
public import NLAlib.Matrix.Factorizations.LU.BlockedInitialize
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Actual execution of all clipped LU blocks

The outer loop uses the positive symbolic block size and its exact ceiling quotient.
Every active block has an in-range start and its natural clipped width ends at the next
boundary. The actual panel and packed scalar trailing update restore the canonical Gaussian
state at each boundary, including a final partial block.

## Main results

* `NLAlib.LU.blockedLoop_writes`: actual complete factor prefixes at the last boundary.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst] [Inhabited K]

/-- All actual clipped panels and scalar trailing products execute from the initial stored
Gaussian prefix. The block count is the exact ceiling quotient, not a supplied execution
trace, and no divisibility of the matrix order by the block size is required. -/
theorem blockedLoop_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (B Q : ℕ) (hB : 0 < B) (hQ : Q = (N + B - 1) / B)
    (hp : ∀ i : Fin N, gaussState A i.val i i ≠ 0) {τ : Tape K} {m : Mem K}
    {R L U : ℕ × ℕ} (hlive : m.Live [R, L, U])
    (hRL : R.1 ≠ L.1) (hRU : R.1 ≠ U.1) (hLU : L.1 ≠ U.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) (hUroom : U.2 + N * N ≤ m.store.len U.1)
    (hstate : IsFactorPrefix dec A 0 R L U m.store) :
    Writes .total I τ (blockedLoop (Op := Op) (Tst := Tst))
      (Env.frame [N, B, Q] [R, L, U])
      (Store.inBuf R.1 ⊔ Store.inBlock L.1 L.2 (N * N) ⊔ Store.inBlock U.1 U.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ IsFactorPrefix dec A N R L U m'.store) m := by
  have hceil : N ⌈/⌉ B = Q := by rw [Nat.ceilDiv_eq_add_pred_div, hQ]
  have hterminal : N ≤ B * Q := (ceilDiv_le_iff_le_mul hB).mp hceil.le
  unfold blockedLoop
  refine (writes_loop rfl
    (fun _ => Store.inBuf R.1 ⊔ Store.inBlock L.1 L.2 (N * N) ⊔
      Store.inBlock U.1 U.2 (N * N)) (fun _ _ => le_rfl)
    (fun t μ => μ.pos = m.pos ∧ IsFactorPrefix dec A (min (B * t) N) R L U μ.store)
    ⟨rfl, by simpa only [Nat.mul_zero, zero_min] using hstate⟩ ?_).mono le_rfl ?_
  · intro t ht μ hfr ⟨hpos, hpref⟩
    have hstart : B * t < N := by
      by_contra hn
      have hle : N ≤ B * t := Nat.le_of_not_gt hn
      have hqt : N ⌈/⌉ B ≤ t := (ceilDiv_le_iff_le_mul hB).mpr hle
      rw [hceil] at hqt
      omega
    have hend : B * t + (B - (B - (N - B * t))) = min (B * (t + 1)) N := by
      rw [Nat.mul_succ]
      omega
    have hsw : B * t + (B - (B - (N - B * t))) ≤ N := by
      rw [hend]
      exact min_le_right _ _
    have hpref' : IsFactorPrefix dec A (B * t) R L U μ.store := by
      simpa only [min_eq_left hstart.le] using hpref
    have hl' := hlive.congr hfr.length_eq
    refine ((blockedStep_writes hI hcmp hM A (B * t) (B - (B - (N - B * t))) hsw hp
      hl' hRL hRU hLU (by simpa only [hfr.len_eq] using hLroom)
      (by simpa only [hfr.len_eq] using hUroom) hpref').in_frame rfl rfl hl').mono le_rfl ?_
    intro μ' hfr' ⟨hp', hpref''⟩
    exact ⟨hp'.trans hpos, hend ▸ hpref''⟩
  · intro μ hfr ⟨hpos, hpref⟩
    exact ⟨hpos, by simpa only [min_eq_right hterminal] using hpref⟩

/-- The unchanged initializer copies the source before factor writes, so the complete blocked
body permits source/factor overlap. Only residual scratch must be apart, and factors are
separate from each other. All numerical outputs come from the original source words. -/
theorem blockedWithScratch_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) {N : ℕ}
    (B Q : ℕ) (hB : 0 < B) (hQ : Q = (N + B - 1) / B)
    {τ : Tape K} {m : Mem K} {A R L U : ℕ × ℕ} {As : List K}
    (hp : ∀ i : Fin N, gaussState (decodeMatrix dec N N As) i.val i i ≠ 0)
    (hlive : m.Live [A, R, L, U]) (hRA : R.1 ≠ A.1)
    (hRL : R.1 ≠ L.1) (hRU : R.1 ≠ U.1) (hLU : L.1 ≠ U.1)
    (hAs : m.store.readBlock A.1 A.2 (N * N) = some As)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) (hUroom : U.2 + N * N ≤ m.store.len U.1) :
    Writes .total I τ (blockedWithScratch (Op := Op) (Tst := Tst))
      (Env.frame [N, B, Q] [A, R, L, U])
      (Store.inBuf R.1 ⊔ Store.inBlock L.1 L.2 (N * N) ⊔ Store.inBlock U.1 U.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ ∃ ls us : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some ls ∧
        m'.store.readBlock U.1 U.2 (N * N) = some us ∧
        decodeMatrix dec N N ls = luLower (decodeMatrix dec N N As) ∧
        decodeMatrix dec N N us = luUpper (decodeMatrix dec N N As) ∧
        IsLU (decodeMatrix dec N N As) (decodeMatrix dec N N ls) (decodeMatrix dec N N us)) m := by
  unfold blockedWithScratch
  refine ((initializeFactors_writes_of_scratch_apart hI hlive hRA hRL hRU hLU hAs hRroom
    hLroom hUroom).in_frame rfl rfl hlive).seq_le (by fp_sub) ?_
  intro μ hfr ⟨hpos, hR, hL, hU⟩
  have hprefix := IsFactorPrefix.initial hM hR hL hU
  have hl' : μ.Live [R, L, U] := by
    have h := hlive.congr hfr.length_eq
    simp only [Mem.live_cons, Mem.live_nil, and_true] at h ⊢
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  refine ((blockedLoop_writes hI hcmp hM (decodeMatrix dec N N As) B Q hB hQ hp hl'
    hRL hRU hLU (by simpa only [hfr.len_eq] using hLroom)
    (by simpa only [hfr.len_eq] using hUroom) hprefix).in_frame rfl rfl hl').mono le_rfl ?_
  intro ν hfr' ⟨hp', hpref'⟩
  obtain ⟨ls, us, hls, hus, hlo, hup⟩ := hpref'.read_factors
  refine ⟨hp'.trans hpos, ls, us, hls, hus, hlo, hup, ?_⟩
  rw [hlo, hup]
  exact isLU_luLower_luUpper (fun i hi => by rw [luUpper_apply_self]; exact hp i)

end NLAlib.LU
