/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RookChoice
public import NLAlib.Matrix.Factorizations.LU.PivotedRoutine

/-!
# Scalar rook-pivot LU

The actual bounded alternating rook search drives the common total elimination loop. Both
current-position histories are reported and determine independent permutations. All matrices,
including singular and empty ones, are admitted. The shared pivoted specification expresses
canonical factors and unit column quality; the selector separately proves both rook maxima.

## Main results

* `NLAlib.LU.factorRook_meets`: canonical PLUQ and both actual recorded histories.
* `NLAlib.LU.eval_factorRook_zero`: actual empty execution without caller-handle premises.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Stored rook-pivot LU with separate row and column histories. The dimension guard skips
all framed calls at zero; nonempty orders use actual rook search and zero-safe elimination. -/
def factorRook : Routine Op Tst :=
  routine% [n] (A : n * n) → (L : n * n, U : n * n, H : n, Q : n) {
    ifPos n {
      run (factorPivoted (rookChoice (Op := Op) (Tst := Tst)).body false)
        [n] (A, L, U, H, Q)
    }
  }

/-- The actual empty tree returns the original memory without reading handles, entering a
frame, allocating scratch or requiring a scalar/index model. -/
theorem eval_factorRook_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (factorRook (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- Actual rook column maximality supplies unit quality to the common pivoted driver. Its
stronger row maximum and first maximum row remain in the concrete selector specification. -/
theorem rookChoice_meets_choice {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (rookChoice (Op := Op) (Tst := Tst)).Meets I (choiceSpec dec 1 bound false) := by
  routine_intro [n, k] (R, p) reads (rs)
  have hraw := (rookChoice_meets hI hcmp hlit hQ hM hNat)
    [n, k] [R, p] τ m [rs] rfl rfl hlive hsep hr hpre hrooms
  refine hraw.mono le_rfl ?_
  rintro m' hfr ⟨hp, ys, hys, hpost⟩
  change m'.readBlocks [p] [2] = some ys at hys
  obtain ⟨ws, rest, hws, hrest, rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys
  have he : rest = [] := by simpa only [Mem.readBlocks_nil, Option.some.injEq] using hrest.symm
  subst rest
  obtain ⟨r, c, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hws)
  exact ⟨hp, [[r, c]], Mem.readBlocks_of_cons hws rfl, rookChoiceSpec_choiceSpec hpost⟩

/-- The actual rook policy factors every matrix and reports both current-position logs.
Their independent permutations give canonical lower/upper factors and exact LU, with lower
multipliers bounded by one. The total step admits singular pivots; no run is assumed. -/
theorem factorRook_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (factorRook (Op := Op) (Tst := Tst)).Meets I (factorPivotedSpec dec 1 false) := by
  routine_intro [n] (A, L, U, H, Q) reads (as)
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    call (factorPivoted_meets (quality := 1) (fixedColumns := false)
      hI hcmp hlit hQ hM (by norm_num) le_rfl
      (fun bound => rookChoice_meets_choice hI hcmp hlit hQ hM.toStdModel_zero
        (hM.isExactNatLit bound))) [n] (A, L, U, H, Q)
      as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hout
    routine_exit
    exact hout
  · rw [if_neg hn]
    have he : n = 0 := by omega
    subst n
    have heas : as = [] := List.eq_nil_of_length_eq_zero (Store.length_of_readBlock has)
    subst as
    exact ⟨rfl, [[], [], [], []], by simp [Mem.readBlocks, Store.readBlock_zero],
      factorPivotedSpec_zero dec 1 false (τ.shift m.pos)⟩

end NLAlib.LU
