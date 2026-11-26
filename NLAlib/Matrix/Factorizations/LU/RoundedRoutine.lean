/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedRoutine
public import NLAlib.Matrix.Factorizations.LU.RoundedLoop

/-!
# Full rounded scalar pivoted LU

The unchanged scoped driver copies the original matrix, initializes both factors and runs
the actual policy loop. Its original-matrix domain includes singular and empty inputs within
the exact integer range. Actual pivot logs identify the permuted input in the componentwise
backward-error bound, with shapes and multiplier bounds retained at every nonnegative roundoff.

## Main results

* `NLAlib.LU.Rounded.factorPivotedCore_meets`: the full scoped actual driver.
* `NLAlib.LU.Rounded.factorPivoted_meets`: a fixed-policy interface of that driver.
-/

@[expose] public section

namespace NLAlib.LU.Rounded

open Ops Computation

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- The literal column-storage flag matches the concrete policy, and the original dimension
is representable by the exact bounded-index interface. No matrix values are excluded. -/
def factorPivotedCoreSpec (dec : K → ℝ) (u quality : ℝ) (fixedColumns : Bool) (literalBound : ℕ) :
    Routine.Spec K :=
  spec% [n, columns] tape t (as) → (ls, us, hs, qs) requires
    n ≤ literalBound ∧ columns = (if fixedColumns then 0 else 1) ensures
    (factorPivotedSpec dec u quality fixedColumns literalBound).post [n] t [as] [ls, us, hs, qs]

/-- The common internal driver executes initialization and the actual pivoted loop. Its only
flag premise is discharged literally by the fixed-policy wrappers. -/
theorem factorPivotedCore_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {choose : Stmt Op Tst} {u quality : ℝ} {fixedColumns : Bool} {literalBound : ℕ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hNat : IsExactNatLit dec M literalBound) (hα : 0 < quality) (hα₁ : quality ≤ 1)
    (hchoice : (choiceRoutine choose).Meets I (choiceSpec dec quality literalBound fixedColumns)) :
    (LU.factorPivotedCore choose).Meets I
      (factorPivotedCoreSpec dec u quality fixedColumns literalBound) := by
  routine_intro [n, columns] (A, L, U, H, Q) reads (as)
  obtain ⟨hbound, hcolumns⟩ := hpre
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
    call (pivotedLoop_meets hI hcmp hlit hQ hM hu hNat hα hα₁ hchoice) [n, columns]
      ((R, 0), L, U, H, Q, (selected, 0)) (pre := ⟨hbound, hcolumns, rfl, rfl⟩)
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
      factorPivotedSpec_zero dec u quality fixedColumns literalBound (τ.shift m.pos)⟩

/-- A fixed selector tree gives a full rounded pivoted LU factorization for every matrix, including
singular and empty matrices. Concrete policy theorems supply the selector judgment. -/
theorem factorPivoted_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {choose : Stmt Op Tst} {u quality : ℝ} {fixedColumns : Bool} {literalBound : ℕ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hNat : IsExactNatLit dec M literalBound) (hα : 0 < quality) (hα₁ : quality ≤ 1)
    (hchoice : (choiceRoutine choose).Meets I (choiceSpec dec quality literalBound fixedColumns)) :
    (LU.factorPivoted choose fixedColumns).Meets I
      (factorPivotedSpec dec u quality fixedColumns literalBound) := by
  cases fixedColumns with
  | false =>
    routine_intro [n] (A, L, U, H, Q) reads (as)
    call (factorPivotedCore_meets hI hcmp hlit hQ hM hu hNat hα hα₁ hchoice) [n, 1] (A, L, U, H, Q)
      (pre := ⟨hpre, rfl⟩) as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hout
    have hqs' : m₁.store.readBlock Q.1 Q.2 n = some qs := by simpa using hqs
    have hout' : (factorPivotedSpec dec u quality false literalBound).post [n] (τ.shift m.pos)
        [as] [ls, us, hs, qs] := hout
    routine_exit
    exact hout'
  | true =>
    routine_intro [n] (A, L, U, H, Q) reads (as)
    call (factorPivotedCore_meets hI hcmp hlit hQ hM hu hNat hα hα₁ hchoice) [n, 0] (A, L, U, H, Q)
      (pre := ⟨hpre, rfl⟩) as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hout
    have hqs' : m₁.store.readBlock Q.1 Q.2 (n - (n - 1)) = some qs := by simpa using hqs
    have hout' : (factorPivotedSpec dec u quality true literalBound).post [n] (τ.shift m.pos)
        [as] [ls, us, hs, qs] := hout
    routine_exit
    exact hout'

end NLAlib.LU.Rounded
