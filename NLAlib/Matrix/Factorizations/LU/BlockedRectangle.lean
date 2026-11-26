/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedRankOne
public import NLAlib.Matrix.Factorizations.LUBlocked
public import NLAlib.Ops.Logic.MatrixViewUpdate

/-!
# Stored rectangle updates and deferred LU panel mathematics

The actual rank-one word postcondition and precise rectangle frame reconstruct the whole
stored residual. Exact arithmetic then identifies it with the existing saved-operand panel
rectangle, including its unchanged exterior. Scratch is allowed in the actual frame provided
it is apart from the residual matrix.

## Main results

* `NLAlib.LU.rankOneStridedSpec_rectangle`: reconstruct and identify one actual panel rectangle.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} [Inhabited K]

/-- Actual output words and their frame give the saved-operand rectangle update. The input
word meanings concern only the supplied coefficient, vectors and old rectangle; no completed
factorization or execution is assumed. -/
theorem rankOneStridedSpec_rectangle {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {N : ℕ} (source current : Matrix (Fin N) (Fin N) ℝ)
    (r : Fin N) (row col rows cols : ℕ) (hr : row + rows ≤ N) (hc : col + cols ≤ N)
    {s s' : Store K} {b off : ℕ} {old : ℕ → ℕ → K}
    (h : s.HoldsMat ⟨b, off, N, N, N⟩ old)
    (hcur : ∀ i j : Fin N, dec (old i j) = current i j)
    (scratch : Fp) (hdis : Fp.Disj scratch (Store.inBlock b off (N * N)))
    (hfr : s.EqOff (Fp.inView b (off + col * N + row)
      ⟨rows, some (cols, N)⟩ ⊔ scratch) s')
    {a : K} {xs ys rs ts : List K} {τ : Tape K}
    (hpost : (rankOneStridedSpec M).post [rows, cols, N] τ [[a], xs, ys, rs] [ts])
    (hts : s'.readView b (off + col * N + row) ⟨rows, some (cols, N)⟩ = some ts)
    (ha : dec a = -1 / source r r)
    (hx : ∀ i : Fin rows, dec (vec xs i.val) = source (Fin.castLE hr (Fin.natAdd row i)) r)
    (hy : ∀ j : Fin cols, dec (vec ys j.val) = source r (Fin.castLE hc (Fin.natAdd col j)))
    (hrs : ∀ i : Fin rows, ∀ j : Fin cols, decodeMatrix dec rows cols rs i j =
      current (Fin.castLE hr (Fin.natAdd row i)) (Fin.castLE hc (Fin.natAdd col j))) :
    ∃ W : ℕ → ℕ → K, s'.HoldsMat ⟨b, off, N, N, N⟩ W ∧
      (fun i j : Fin N => dec (W i j)) = luPanelRectangle source current r row col rows cols := by
  let W : ℕ → ℕ → K := fun i j =>
    if row ≤ i ∧ i < row + rows ∧ col ≤ j ∧ j < col + cols then
      vec ts ((j - col) * rows + (i - row)) else old i j
  have hstore : s'.HoldsMat ⟨b, off, N, N, N⟩ W :=
    h.update_rectangle_of_frame_with_scratch (by exact le_rfl) row col rows cols hr
      scratch hdis hfr hts
  refine ⟨W, hstore, eq_luPanelRectangle_of_coordinates source current _ r row col rows cols
    hr hc ?_ ?_⟩
  · intro i j
    have hi : row ≤ row + i.val ∧ row + i.val < row + rows := by omega
    have hj : col ≤ col + j.val ∧ col + j.val < col + cols := by omega
    change dec (W (row + i.val) (col + j.val)) = _
    simp only [W, hi.1, hi.2, hj.1, hj.2, and_self, if_true, Nat.add_sub_cancel_left]
    have ht := congrFun (congrFun (rankOneStridedSpec_decode hM hpost) i) j
    rw [decodeMatrix_apply] at ht
    rw [ht, hx i, hy j, ha, ← decodeMatrix_apply dec rows cols rs i j, hrs i j]
    ring
  · intro i j hout
    have hn : ¬(row ≤ i.val ∧ i.val < row + rows ∧ col ≤ j.val ∧ j.val < col + cols) := by
      omega
    change dec (W i.val j.val) = _
    simp only [W, if_neg hn]
    exact hcur i j

end NLAlib.LU
