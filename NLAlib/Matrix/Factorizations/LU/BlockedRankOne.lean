/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RankOne
public import NLAlib.Ops.Blas.MatrixCopy
public import NLAlib.Ops.Logic.MatrixView
public import NLAlib.Ops.Catalog.Orth

/-!
# Scalar rank-one updates of strided panel rectangles

Panel elimination uses two disjoint rectangles of one square residual. This adapter packs
one rectangle, calls the shared scalar rank-one routine, and scatters the result to the same
logical entries. Padding is retained. Saved source vectors are read only; a caller-owned
packed workspace may be reused for successive rectangles.

## Main results

* `NLAlib.LU.rankOneStridedWithScratch_meets`: actual packing, scalar update and scattering.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Pack a strided rectangle, update it through the shared scalar column loops, and scatter
it back. The packed workspace is caller-owned and not a reported numerical output. -/
def rankOneStridedWithScratch : Routine Op Tst :=
  routine% [rows, cols, ld]
      (a : 1, x : rows, y : cols, R : rows × cols every ld) →
      (R, unreported P : rows * cols) {
    run copyMatrixRoutine [rows, cols, ld, rows] (R, P);
    run rankOne [rows, cols] (a, x, y, P);
    run copyMatrixRoutine [rows, cols, rows, ld] (P, R)
  }

variable [Inhabited K]

/-- The logical output words are exactly the packed shared rank-one word update. Nonempty
columns must not overlap; empty rectangles impose no leading-dimension condition. -/
def rankOneStridedSpec (M : Machine K) : Routine.Spec K :=
  spec% [rows, cols, ld] ([a], xs, ys, rs) → (ts)
    requires (0 < cols * rows → rows ≤ ld) ensures
    ts = (EntryCodec.scalar K).packMatrix rows cols
      (rankOneValues M a (vec xs) (vec ys) (fun i j => vec rs (j * rows + i)))

/-- Every scalar machine executes the actual pack/update/scatter tree and retains all gaps
outside the logical rectangle. This word statement assumes no numerical accuracy law. -/
theorem rankOneStridedWithScratch_meets {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (rankOneStridedWithScratch (Op := Op) (Tst := Tst)).Meets I
      (rankOneStridedSpec M) := by
  routine_intro [rows, cols, ld] (a, x, y, R, P) reads (as, xs, ys, rs)
  obtain ⟨av, ha, rfl⟩ := Store.readBlock_one_eq_some.mp has
  have has := Store.readBlock_one_of_get ha
  call (copyMatrixRoutine_meets hI) [rows, cols, ld, rows] (R, P)
    as m₁ hfr₁ hpos₁ (ps) hcopy
  case' hcall => exact [rs]
  case' hr => exact Mem.readViews_of_cons hrs rfl
  case' hpre => exact fun _ => le_rfl
  case' hroom =>
    change (⟨rows, some (cols, rows)⟩ : View).Fits P.2 (m.store.len P.1) ∧ True
    refine ⟨?_, trivial⟩
    intro q hq
    simp only [View.offset_packedMatrix]
    have hq' : q < cols * rows := hq
    nlinarith [hroom.2]
  have hwords : ps = rs := hcopy
  subst ps
  simp only [Store.readView_packedMatrix] at hps
  simp only [Fp.views, Fp.inView_packedMatrix, sup_bot_eq] at hfr₁
  have ha₁ : m₁.store.readBlock a.1 a.2 1 = some [av] := by keep
  have hx₁ : m₁.store.readBlock x.1 x.2 rows = some xs := by keep
  have hy₁ : m₁.store.readBlock y.1 y.2 cols = some ys := by keep
  call (rankOne_meets hI) [rows, cols] (a, x, y, P)
    as m₂ hfr₂ hpos₂ (ps) hupdate
  call (copyMatrixRoutine_meets hI) [rows, cols, rows, ld] (P, R)
    (pre := hpre) as m₃ hfr₃ hpos₃ (ts) hscatter
  case' hcall => exact [ps]
  case' hr =>
    change m₂.readViews [P] [⟨rows, some (cols, rows)⟩] = some [ps]
    exact Mem.readViews_of_cons (by simpa only [Store.readView_packedMatrix] using hps) rfl
  case' hpre => exact hpre
  refine ⟨by omega, [ts], Mem.readViews_of_cons hts rfl, ?_⟩
  have hts' : ts = ps := hscatter
  rw [hts']
  exact hupdate

omit [Has ScalarOp Op] in
/-- Exact decoded arithmetic reads the saved-operand rank-one correction from the actual
word postcondition, without any factorization or successful-run hypothesis. -/
theorem rankOneStridedSpec_decode {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {rows cols ld : ℕ} {a : K} {xs ys rs ts : List K}
    {τ : Tape K}
    (hpost : (rankOneStridedSpec M).post [rows, cols, ld] τ [[a], xs, ys, rs] [ts]) :
    decodeMatrix dec rows cols ts = fun i j =>
      dec (vec rs (j.val * rows + i.val)) +
        (dec a * dec (vec ys j.val)) * dec (vec xs i.val) := by
  obtain rfl : ts = (EntryCodec.scalar K).packMatrix rows cols
      (rankOneValues M a (vec xs) (vec ys) (fun i j => vec rs (j * rows + i))) := hpost
  rw [decodeMatrix, EntryCodec.matrix_packMatrix]
  ext i j
  change dec (M.add (vec rs (j.val * rows + i.val))
    (M.mul (M.mul a (vec ys j.val)) (vec xs i.val))) = _
  rw [hM.add, hM.mul, hM.mul]

end NLAlib.LU
