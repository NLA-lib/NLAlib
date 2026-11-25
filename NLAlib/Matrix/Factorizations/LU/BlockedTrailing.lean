/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LUBlocked
public import NLAlib.Ops.Blas.MatrixUpdate
public import NLAlib.Ops.Logic.MatrixViewUpdate

/-!
# Actual scalar trailing products restore Gaussian residuals

The actual packed scalar matrix-product postcondition and its precise destination frame
restore the complete exit residual after a panel. Only the committed columns and rows of
the stored factors enter the product. No matrix-product primitive or whole-run hypothesis is
introduced: the numerical window identity comes from the shared scalar update routine.

## Main results

* `NLAlib.LU.trailingUpdateSpec_gaussState`: actual trailing words and frame restore the
  canonical Gaussian residual and a full stored-matrix witness.
-/

@[expose] public section

namespace NLAlib.LU

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K]

/-- The scalar matrix-product correction restores the full Gaussian residual from a completed
panel. All source-window meanings and factor prefixes are explicit; they are supplied by the
stored loop invariant rather than assumed for the complete algorithm. -/
theorem trailingUpdateSpec_gaussState {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {N : ℕ} (A F G : Matrix (Fin N) (Fin N) ℝ)
    (start width : ℕ) (hr : start + width ≤ N)
    (htail : start + width + (N - (start + width)) ≤ N)
    (hF : ∀ i j : Fin N, j.val < start + width → F i j = luLower A i j)
    (hG : ∀ i j : Fin N, i.val < start + width → G i j = luUpper A i j)
    {s s' : Store K} {b off : ℕ} {old : ℕ → ℕ → K}
    (h : s.HoldsMat ⟨b, off, N, N, N⟩ old)
    (hcur : ∀ i j : Fin N, dec (old i j) =
      luPanelState A start (start + width) (start + width) i j)
    (hfr : s.EqOff (Fp.inView b (off + (start + width) * N + (start + width))
      ⟨N - (start + width), some (N - (start + width), N)⟩) s')
    {as bs rs ts : List K} {τ : Tape K}
    (hpost : (ScalarMatrix.updateSpec M).post
      [N - (start + width), width, N - (start + width), N, N, N] τ [as, bs, rs] [ts])
    (hts : s'.readView b (off + (start + width) * N + (start + width))
      ⟨N - (start + width), some (N - (start + width), N)⟩ = some ts)
    (hAs : ∀ i : Fin (N - (start + width)), ∀ t : Fin width,
      decodeMatrix dec (N - (start + width)) width as i t =
        F (Fin.castLE htail (Fin.natAdd (start + width) i))
          (Fin.castLE hr (Fin.natAdd start t)))
    (hBs : ∀ t : Fin width, ∀ j : Fin (N - (start + width)),
      decodeMatrix dec width (N - (start + width)) bs t j =
        G (Fin.castLE hr (Fin.natAdd start t))
          (Fin.castLE htail (Fin.natAdd (start + width) j)))
    (hRs : ∀ i j : Fin (N - (start + width)),
      decodeMatrix dec (N - (start + width)) (N - (start + width)) rs i j =
        luPanelState A start (start + width) (start + width)
          (Fin.castLE htail (Fin.natAdd (start + width) i))
          (Fin.castLE htail (Fin.natAdd (start + width) j))) :
    ∃ W : ℕ → ℕ → K, s'.HoldsMat ⟨b, off, N, N, N⟩ W ∧
      (fun i j : Fin N => dec (W i j)) = gaussState A (start + width) := by
  let stop := start + width
  let W : ℕ → ℕ → K := fun i j =>
    if stop ≤ i ∧ i < stop + (N - stop) ∧ stop ≤ j ∧ j < stop + (N - stop) then
      vec ts ((j - stop) * (N - stop) + (i - stop)) else old i j
  have hstore : s'.HoldsMat ⟨b, off, N, N, N⟩ W :=
    h.update_rectangle_of_frame (by exact le_rfl) stop stop (N - stop) (N - stop)
      htail hfr hts
  refine ⟨W, hstore, eq_gaussState_of_panel_products A F G _ start width hr hF hG ?_ ?_⟩
  · intro i j hi hj
    let ii : Fin (N - stop) := ⟨i.val - stop, by dsimp [stop]; omega⟩
    let jj : Fin (N - stop) := ⟨j.val - stop, by dsimp [stop]; omega⟩
    have hei : Fin.castLE htail (Fin.natAdd stop ii) = i := Fin.ext (by dsimp [ii, stop]; omega)
    have hej : Fin.castLE htail (Fin.natAdd stop jj) = j := Fin.ext (by dsimp [jj, stop]; omega)
    have hin : stop ≤ i.val ∧ i.val < stop + (N - stop) ∧
        stop ≤ j.val ∧ j.val < stop + (N - stop) := by dsimp [stop]; omega
    change dec (W i.val j.val) = _
    rw [show W i.val j.val = vec ts ((j.val - stop) * (N - stop) + (i.val - stop)) by
      simp only [W, if_pos hin]]
    have he := congrFun (congrFun (ScalarMatrix.updateSpec_decode hM hpost) ii) jj
    rw [decodeMatrix_apply, Matrix.sub_apply, Matrix.mul_apply, hRs ii jj, hei, hej] at he
    change dec (vec ts ((j.val - stop) * (N - stop) + (i.val - stop))) = _ at he
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [hAs ii t, hBs t jj, hei, hej]
  · intro i j hout
    have hn : ¬(stop ≤ i.val ∧ i.val < stop + (N - stop) ∧
        stop ≤ j.val ∧ j.val < stop + (N - stop)) := by dsimp [stop]; omega
    change dec (W i.val j.val) = _
    simp only [W, if_neg hn]
    exact hcur i j

end NLAlib.LU
