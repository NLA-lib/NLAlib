/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedAlg

/-!
# Correctness of scalar pivoted LU drivers

The fixed policy wrapper supplies the internal column-storage flag. Initialization copies
actual input words, and the policy loop constructs canonical factors and actual histories.
No nonsingularity or successful-execution premise is part of the public judgment.

## Main results

* `NLAlib.LU.factorPivoted_meets`: the actual fixed policy driver and canonical factor output.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

omit [Inhabited K] in
/-- Fresh residual and selector buffers give the common pivot loop its live operands and
output capacities after initialization. The proof uses only allocation shapes and frames. -/
theorem pivotedLoop_allocated {choose : Stmt Op Tst} {n columns : ℕ}
    {m m' : Mem K} {s : Store K} {F : Fp} {L U H Q : ℕ × ℕ}
    (hlive : m.Live [L, U, H, Q])
    (hroom : m.Room [L, U, H, Q]
      [n * n, n * n, n, columns * n + (1 - columns) * (n - (n - 1))])
    (hlen : s.length = m.store.length + 2)
    (hbelow : Store.Below m.store.length m.store s)
    (hR : s.len m.store.length = n * n) (hselected : s.len (m.store.length + 1) = 2)
    (hfr : s.EqOff F m'.store) :
    m'.Live [(m.store.length, 0), L, U, H, Q, (m.store.length + 1, 0)] ∧
      (pivotedLoop choose).RoomAt m' [n, columns]
        ((pivotedLoop choose).operands [n, columns]
          [(m.store.length, 0), L, U, H, Q, (m.store.length + 1, 0)]) := by
  obtain ⟨hL, hU, hH, hQ⟩ : L.1 < m.store.length ∧ U.1 < m.store.length ∧
      H.1 < m.store.length ∧ Q.1 < m.store.length := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlive
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hroom
  constructor
  · simp only [Mem.live_cons, Mem.live_nil, and_true]
    have he := hfr.length_eq
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · change (0 + n * n ≤ m'.store.len m.store.length) ∧
      (L.2 + n * n ≤ m'.store.len L.1) ∧ (U.2 + n * n ≤ m'.store.len U.1) ∧
      (H.2 + n ≤ m'.store.len H.1) ∧
      (Q.2 + (columns * n + (1 - columns) * (n - (n - 1))) ≤ m'.store.len Q.1) ∧
      (0 + 2 ≤ m'.store.len (m.store.length + 1)) ∧ True
    simp only [hfr.len_eq]
    exact ⟨by simpa only [Nat.zero_add] using hR.ge,
      by rw [(hbelow L.1 hL).1]; exact hroom.1,
      by rw [(hbelow U.1 hU).1]; exact hroom.2.1,
      by rw [(hbelow H.1 hH).1]; exact hroom.2.2.1,
      by rw [(hbelow Q.1 hQ).1]; exact hroom.2.2.2,
      by simpa only [Nat.zero_add] using hselected.ge, trivial⟩

/-- The common internal driver executes initialization and the actual pivoted loop. Its only
flag premise is discharged literally by the fixed-policy wrappers. -/
theorem factorPivotedCore_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {choose : Stmt Op Tst} {quality : ℝ} {fixedColumns : Bool}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) (hα : 0 < quality) (hα₁ : quality ≤ 1)
    (hchoice : ∀ bound : ℕ,
      (choiceRoutine choose).Meets I (choiceSpec dec quality bound fixedColumns)) :
    (factorPivotedCore choose).Meets I (factorPivotedCoreSpec dec quality fixedColumns) := by
  routine_intro [n, columns] (A, L, U, H, Q) reads (as)
  have hcolumns := hpre
  refine writes_ifPos rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    alloc as R selected
    have hAR : A.1 ≠ R := by change A.1 ≠ m.store.length + 0; omega
    have hRL : R ≠ L.1 := by change m.store.length + 0 ≠ L.1; omega
    have hRU : R ≠ U.1 := by change m.store.length + 0 ≠ U.1; omega
    have hRH : R ≠ H.1 := by change m.store.length + 0 ≠ H.1; omega
    have hRQ : R ≠ Q.1 := by change m.store.length + 0 ≠ Q.1; omega
    have hRs : R ≠ selected := by change m.store.length + 0 ≠ m.store.length + 1; omega
    have hLs : L.1 ≠ selected := by change L.1 ≠ m.store.length + 1; omega
    have hUs : U.1 ≠ selected := by change U.1 ≠ m.store.length + 1; omega
    have hHs : H.1 ≠ selected := by change H.1 ≠ m.store.length + 1; omega
    have hQs : Q.1 ≠ selected := by change Q.1 ≠ m.store.length + 1; omega
    call (initializeFactors_meets hI) [n] (A, (R, 0), L, U)
      as m₁ hfr₁ hpos₁ (rs, ls, us) hinit
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change A.1 < s_R.length ∧ m.store.length < s_R.length ∧
        L.1 < s_R.length ∧ U.1 < s_R.length
      simp only [List.length_cons, List.length_nil] at hlen_R
      omega
    case' hroom =>
      change (0 + n * n ≤ s_R.len R) ∧ (L.2 + n * n ≤ s_R.len L.1) ∧
        (U.2 + n * n ≤ s_R.len U.1) ∧ True
      exact ⟨by simpa only [Nat.zero_add] using hR.ge,
        by rw [(hbelow_R L.1 hl.2.1).1]; exact hroom.1,
        by rw [(hbelow_R U.1 hl.2.2.1).1]; exact hroom.2.1, trivial⟩
    obtain ⟨rfl, rfl, rfl⟩ := hinit
    call (pivotedLoop_meets hI hcmp hlit hQ hM hα hα₁ hchoice) [n, columns]
      ((R, 0), L, U, H, Q, (selected, 0)) (pre := ⟨hcolumns, rfl, rfl⟩)
      as m₂ hfr₂ hpos₂ (rr, ls', us', hs, qs) hout
    case' hlive =>
      exact (pivotedLoop_allocated (Op := Op) (Tst := Tst) (choose := choose)
        (by simpa using hl.2) hrooms
        (by simpa using hlen_R) hbelow_R hR hselected hfr₁).1
    case' hroom =>
      exact (pivotedLoop_allocated (Op := Op) (Tst := Tst) (choose := choose)
        (by simpa using hl.2) hrooms
        (by simpa using hlen_R) hbelow_R hR hselected hfr₁).2
    intro s₂ hs₂ hB
    refine ⟨hpos₂.trans hpos₁, [ls', us', hs, qs], Mem.readBlocks_of_cons ?_
      (Mem.readBlocks_of_cons ?_ (Mem.readBlocks_of_cons ?_
        (Mem.readBlocks_of_cons ?_ rfl))), hout⟩
    · exact Store.Below.readBlock_of hB hl.2.1 hls'
    · exact Store.Below.readBlock_of hB hl.2.2.1 hus'
    · exact Store.Below.readBlock_of hB hl.2.2.2.1 hhs
    · exact Store.Below.readBlock_of hB hl.2.2.2.2 hqs
  · rw [if_neg hn]
    have he : n = 0 := by omega
    subst n
    have has : as = [] := List.eq_nil_of_length_eq_zero (Store.length_of_readBlock has)
    subst as
    exact ⟨rfl, [[], [], [], []], by simp [Mem.readBlocks, Store.readBlock_zero],
      factorPivotedSpec_zero dec quality fixedColumns (τ.shift m.pos)⟩

/-- A fixed selector tree gives a full canonical LU factorization for every matrix, including
singular and empty matrices. Concrete policy theorems supply the selector judgment. -/
theorem factorPivoted_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {choose : Stmt Op Tst} {quality : ℝ} {fixedColumns : Bool}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) (hα : 0 < quality) (hα₁ : quality ≤ 1)
    (hchoice : ∀ bound : ℕ,
      (choiceRoutine choose).Meets I (choiceSpec dec quality bound fixedColumns)) :
    (factorPivoted choose fixedColumns).Meets I (factorPivotedSpec dec quality fixedColumns) := by
  cases fixedColumns with
  | false =>
    routine_intro [n] (A, L, U, H, Q) reads (as)
    call (factorPivotedCore_meets hI hcmp hlit hQ hM hα hα₁ hchoice) [n, 1] (A, L, U, H, Q)
      (pre := rfl) as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hout
    have hqs' : m₁.store.readBlock Q.1 Q.2 n = some qs := by simpa using hqs
    have hout' : (factorPivotedSpec dec quality false).post [n] (τ.shift m.pos)
        [as] [ls, us, hs, qs] := hout
    routine_exit
    exact hout'
  | true =>
    routine_intro [n] (A, L, U, H, Q) reads (as)
    call (factorPivotedCore_meets hI hcmp hlit hQ hM hα hα₁ hchoice) [n, 0] (A, L, U, H, Q)
      (pre := rfl) as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hout
    have hqs' : m₁.store.readBlock Q.1 Q.2 (n - (n - 1)) = some qs := by simpa using hqs
    have hout' : (factorPivotedSpec dec quality true).post [n] (τ.shift m.pos)
        [as] [ls, us, hs, qs] := hout
    routine_exit
    exact hout'

end NLAlib.LU
