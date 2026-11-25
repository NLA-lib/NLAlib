/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedRectangle
public import NLAlib.Ops.Blas.Dot

/-!
# Actual execution of a saved-operand panel rectangle

The shared scalar pack/update/scatter routine is applied to a rectangular view of a larger
matrix. Its actual word postcondition and frame yield the full decoded saved-operand panel
update. The hypotheses are arithmetic laws, readable operands, geometry and capacity.

## Main results

* `NLAlib.LU.rankOneStridedWithScratch_writes_rectangle`: actual exact rectangle execution.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} [Inhabited K]

section Execution

variable {Op Tst : Type} [Has ScalarOp Op]

/-- The actual strided scalar routine updates one rectangle of a larger stored matrix.
The standard routine geometry hypotheses concern only operands and capacities. Its decoded
whole-matrix conclusion is derived from the actual word run and its precise frame. -/
theorem rankOneStridedWithScratch_writes_rectangle {M : Machine K} {dec : K → ℝ}
    {I : Interp Op Tst K} (hI : IsScalar M I) (hM : ExactModel dec M) {N : ℕ}
    (source current : Matrix (Fin N) (Fin N) ℝ) (r : Fin N)
    (row col rows cols : ℕ) (hr : row + rows ≤ N) (hc : col + cols ≤ N)
    {τ : Tape K} {m : Mem K} {a x y R P : ℕ × ℕ} {av : K} {xs ys : List K}
    {old : ℕ → ℕ → K} (h : m.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ old)
    (hcur : ∀ i j : Fin N, dec (old i j) = current i j)
    (haRead : m.store.readBlock a.1 a.2 1 = some [av])
    (hxRead : m.store.readBlock x.1 x.2 rows = some xs)
    (hyRead : m.store.readBlock y.1 y.2 cols = some ys)
    (hPR : P.1 ≠ R.1)
    (hlive : m.Live [a, x, y, (R.1, R.2 + col * N + row), P])
    (hsep : (rankOneStridedWithScratch (Op := Op) (Tst := Tst)).SeparatedAt [rows, cols, N]
      [a, x, y, (R.1, R.2 + col * N + row), P])
    (hroom : (rankOneStridedWithScratch (Op := Op) (Tst := Tst)).RoomAt m [rows, cols, N]
      ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).operands [rows, cols, N]
        [a, x, y, (R.1, R.2 + col * N + row), P]))
    (ha : dec av = -1 / source r r)
    (hx : ∀ i : Fin rows, dec (vec xs i.val) = source (Fin.castLE hr (Fin.natAdd row i)) r)
    (hy : ∀ j : Fin cols, dec (vec ys j.val) = source r (Fin.castLE hc (Fin.natAdd col j))) :
    Writes .total I τ (rankOneStridedWithScratch (Op := Op) (Tst := Tst)).body
      (Env.frame [rows, cols, N]
        ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).env
          ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).operands [rows, cols, N]
            [a, x, y, (R.1, R.2 + col * N + row), P])))
      ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).footprint [rows, cols, N]
        ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).operands [rows, cols, N]
          [a, x, y, (R.1, R.2 + col * N + row), P]))
      (fun m' => m'.pos = m.pos ∧ ∃ W : ℕ → ℕ → K,
        m'.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ W ∧
          (fun i j : Fin N => dec (W i j)) =
            luPanelRectangle source current r row col rows cols) m := by
  let rs := (EntryCodec.scalar K).packMatrix rows cols (fun i j => old (row + i) (col + j))
  have hRs : m.store.readView R.1 (R.2 + col * N + row) ⟨rows, some (cols, N)⟩ = some rs :=
    h.readView_rectangle row col rows cols hr hc
  have hrun := rankOneStridedWithScratch_meets hI [rows, cols, N]
    [a, x, y, (R.1, R.2 + col * N + row), P] τ m [[av], xs, ys, rs]
    rfl rfl hlive hsep
    (by
      change m.readViews [a, x, y, (R.1, R.2 + col * N + row)]
        [View.block 1, View.block rows, View.block cols, ⟨rows, some (cols, N)⟩] =
        some [[av], xs, ys, rs]
      exact Mem.readViews_of_cons (by simpa using haRead)
        (Mem.readViews_of_cons (by simpa using hxRead)
          (Mem.readViews_of_cons (by simpa using hyRead) (Mem.readViews_of_cons hRs rfl))))
    (by change 0 < cols * rows → rows ≤ N; omega) hroom
  refine hrun.mono le_rfl ?_
  intro m' hfr ⟨hpos, ts, hts, hpost⟩
  obtain ⟨ts', rfl⟩ : ∃ ts' : List K, ts = [ts'] := by
    cases ts with
    | nil => change False at hpost; contradiction
    | cons ts' tail =>
      cases tail with
      | nil => exact ⟨ts', rfl⟩
      | cons bad tail => change False at hpost; contradiction
  have hts' : m'.store.readView R.1 (R.2 + col * N + row) ⟨rows, some (cols, N)⟩ =
      some ts' := by
    change m'.readViews [(R.1, R.2 + col * N + row)] [⟨rows, some (cols, N)⟩] =
      some [ts'] at hts
    obtain ⟨out, rest, hread, hrest, he⟩ := Mem.readViews_cons_eq_some.mp hts
    have hn : rest = [] := (Option.some.inj hrest).symm
    subst rest
    have he' : ts' = out := (List.cons.inj he).1
    simpa only [← he'] using hread
  have hfr' : m.store.EqOff (Fp.inView R.1 (R.2 + col * N + row)
      ⟨rows, some (cols, N)⟩ ⊔ Store.inBlock P.1 P.2 (rows * cols)) m'.store := by
    change m.store.EqOff (Fp.views [(R.1, R.2 + col * N + row), P]
      [⟨rows, some (cols, N)⟩, View.block (rows * cols)]) m'.store at hfr
    simpa only [Fp.views, Fp.inView_block, sup_bot_eq] using hfr
  obtain ⟨W, hW, hdec⟩ := rankOneStridedSpec_rectangle hM source current r row col rows cols
    hr hc h hcur (Store.inBlock P.1 P.2 (rows * cols)) (Fp.disj_inBlock_of_ne hPR) hfr'
    hpost hts' ha hx hy (by
      intro i j
      rw [decodeMatrix, EntryCodec.matrix_packMatrix]
      exact hcur (Fin.castLE hr (Fin.natAdd row i)) (Fin.castLE hc (Fin.natAdd col j)))
  exact ⟨hpos, W, hW, hdec⟩

/-- Operand geometry for the rectangle execution theorem follows from separate buffers and
one reusable square workspace. The larger residual is supplied by its actual stored entries. -/
theorem rankOneStridedWithScratch_writes_rectangle_of_apart
    {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hI : IsScalar M I) (hM : ExactModel dec M) {N : ℕ}
    (source current : Matrix (Fin N) (Fin N) ℝ) (r : Fin N)
    (row col rows cols : ℕ) (hr : row + rows ≤ N) (hc : col + cols ≤ N)
    {τ : Tape K} {m : Mem K} {a x y R P : ℕ × ℕ} {av : K} {xs ys : List K}
    {old : ℕ → ℕ → K} (h : m.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ old)
    (hcur : ∀ i j : Fin N, dec (old i j) = current i j)
    (haRead : m.store.readBlock a.1 a.2 1 = some [av])
    (hxRead : m.store.readBlock x.1 x.2 rows = some xs)
    (hyRead : m.store.readBlock y.1 y.2 cols = some ys)
    (hlive : m.Live [a, x, y, R, P])
    (haR : a.1 ≠ R.1) (haP : a.1 ≠ P.1) (hxR : x.1 ≠ R.1) (hxP : x.1 ≠ P.1)
    (hyR : y.1 ≠ R.1) (hyP : y.1 ≠ P.1) (hRP : R.1 ≠ P.1)
    (hP : P.2 + N * N ≤ m.store.len P.1) (ha : dec av = -1 / source r r)
    (hx : ∀ i : Fin rows, dec (vec xs i.val) = source (Fin.castLE hr (Fin.natAdd row i)) r)
    (hy : ∀ j : Fin cols, dec (vec ys j.val) = source r (Fin.castLE hc (Fin.natAdd col j))) :
    Writes .total I τ (rankOneStridedWithScratch (Op := Op) (Tst := Tst)).body
      (Env.frame [rows, cols, N]
        ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).env
          ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).operands [rows, cols, N]
            [a, x, y, (R.1, R.2 + col * N + row), P])))
      ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).footprint [rows, cols, N]
        ((rankOneStridedWithScratch (Op := Op) (Tst := Tst)).operands [rows, cols, N]
          [a, x, y, (R.1, R.2 + col * N + row), P]))
      (fun m' => m'.pos = m.pos ∧ ∃ W : ℕ → ℕ → K,
        m'.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ W ∧
          (fun i j : Fin N => dec (W i j)) =
            luPanelRectangle source current r row col rows cols) m := by
  apply rankOneStridedWithScratch_writes_rectangle hI hM source current r row col rows cols
    hr hc h hcur haRead hxRead hyRead hRP.symm
  · simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlive
  · routine_sep
  · change (⟨rows, some (cols, N)⟩ : View).Fits (R.2 + col * N + row)
      (m.store.len R.1) ∧ P.2 + rows * cols ≤ m.store.len P.1 ∧ True
    refine ⟨?_, ?_, trivial⟩
    · have hv := h.readView_rectangle row col rows cols hr hc
      by_cases hp : 0 < cols * rows
      · exact Store.fits_of_readView hv hp
      · intro q hq
        change q < cols * rows at hq
        omega
    · have hm : rows * cols ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
      omega
  · exact ha
  · exact hx
  · exact hy

end Execution

end NLAlib.LU
