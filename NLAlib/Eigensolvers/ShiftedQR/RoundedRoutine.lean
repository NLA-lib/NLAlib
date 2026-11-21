/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheorems
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# The routine of rounded shifted QR

`NLAlib.ShiftedQR.shqrRoutine` is
`[n, k, np, F] (A : update 2 (n + 1)², t : read 1, p : read np) →
(out : write 2 (n + 1), f : write 1)`: the program `NLAlib.ShiftedQR.roundedShQR` at the order
`n + 1`. The parameter words are in a buffer of their own.

On every tape the run terminates and changes only the matrix, the output and the failure word.
Nothing is claimed of their contents on every tape (on a bad window the kernel may return any
words), nor of the number of tape positions consumed, so the routine meets its specification in
the sense of `NLAlib.Ops.Routine.Spec.terminates`: no written operand is reported.
The accuracy of the output is a statement in probability.

## Main definitions

* `NLAlib.ShiftedQR.shqrRoutine`, `NLAlib.ShiftedQR.shqrSpec`.

## Main results

* `NLAlib.ShiftedQR.shqrRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops MeasureTheory
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- Rounded shifted QR at the order `n + 1`: `[n, k, np, F] (A : update 2 (n + 1)², t : read 1,
p : read np) → (out : write 2 (n + 1), f : write 1)`. The number of draws depends on the data,
so the routine declares none. Its written operands are unreported: the statement it rests on,
`NLAlib.ShiftedQR.roundedShQR_terminates`, gives termination and the footprint on every tape,
not that the written blocks are defined; with no blocks reported, its specification is a
`NLAlib.Ops.Routine.Spec.terminates`, and its accuracy is the probability theorems'.
The dimension `n` is one less than the order, so that every dimension is the order of a nonempty
matrix; the tree is `roundedShQR` at `n + 1`. The threshold and the parameter words are only
read, so they may overlap (`NLAlib.ShiftedQR.ShQRViewsApart`). The tree has one buffer variable
for each operand (the matrix is updated through one variable), which the clause `one variable`
states; the routine then has no layout, and its program is this tree with no frame around it. -/
def shqrRoutine : Routine O Q :=
  routine% [n, k, np, F] (unreported A : 2 * ((n + 1) * (n + 1)), t : 1, p : np) →
      (A, unreported out : 2 * (n + 1), unreported f : 1)
    draws unspecified one variable {
    run (roundedShQR (O := O) (Q := Q)) [n + 1, k, np, F] (A, t, p, out, f)
  }

/-- The input is the words of a matrix of order `n + 1`, the deflation threshold word and the
parameter words of the reals $B, \Gamma, \Sigma, \delta, \varphi$, at the shift degree, word
count and cap they determine, with the natural literals up to `n + 1` exact on the machine.
Nothing is claimed of the written blocks. -/
noncomputable def shqrSpec (Mch : Machine ℝ) (B Γ S δ φ : ℝ) : Routine.Spec ℝ :=
  .terminates fun d _ X => IsExactNatLit id Mch (d.headD 0 + 1) ∧ d.getD 1 0 = shqrDegree (4 * B) ∧
    d.getD 2 0 = (shqrParams (d.headD 0) (d.getD 1 0) B Γ S δ φ).length ∧
    d.getD 3 0 = shqrCap (d.headD 0) B Γ S δ ∧
    ∃ H : Matrix (Fin (d.headD 0 + 1)) (Fin (d.headD 0 + 1)) ℂ,
      X = [matrixWords H, [shqrDeflationThreshold (d.headD 0) (d.getD 1 0) B Γ S δ φ],
        shqrParams (d.headD 0) (d.getD 1 0) B Γ S δ φ]

/-- Rounded shifted QR terminates on every tape and changes only the matrix, the output and the
failure word. -/
theorem shqrRoutine_meets {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) (hQ : IsToNat id I) (hC : IsCmp id I)
    {law : ℕ → Measure ℝ} {sU : ℕ} {βse φse : ℝ} (hSE : IsRandomSmallEig law sU βse φse I)
    (hDisk : IsPolarDiskSampler sU I) {B Γ S δ φ : ℝ} :
    (shqrRoutine (O := O) (Q := Q)).Meets I
      (shqrSpec Mch B Γ S δ φ) := by
  routine_intro [n, k, np, F] (a, t, p, out, f) reads (ws, ts, ps)
  obtain ⟨hNat, hk, hnp, hF, H, heq⟩ := hpre
  change k = shqrDegree (4 * B) at hk
  obtain rfl : np = (shqrParams n k B Γ S δ φ).length := hnp
  obtain rfl : F = shqrCap n B Γ S δ := hF
  obtain ⟨rfl, rfl, rfl⟩ : ws = matrixWords H ∧
      ts = [shqrDeflationThreshold n k B Γ S δ φ] ∧ ps = shqrParams n k B Γ S δ φ := by
    simpa using heq
  have hA := hws
  have ht := hts
  have hp := hps
  have hpos : 0 < (shqrParams n k B Γ S δ φ).length := by
    simp [shqrParams, roundedDecoupleParams]
  have hin : ShQRInput k B Γ S δ φ a t p out f H m := by
    refine ⟨by room, ?_, ⟨by disjoint, by disjoint⟩, hA, ?_, hp⟩
    · simp only [Mem.room_cons, Mem.room_nil, and_true]
      exact ⟨hroom.1, Store.le_len_of_readBlock ht Nat.one_pos,
        Store.le_len_of_readBlock hp hpos, hroom.2.1, hroom.2.2⟩
    · simpa [vec] using Store.get_of_readBlock ht (j := 0) Nat.one_pos default
  have hT := roundedShQR_terminates (O := O) (Q := Q) hS hL hNat hQ hC hSE hDisk hk hin τ
  refine (hT.in_frame (ρ := Env.frame [n, k, (shqrParams n k B Γ S δ φ).length,
    shqrCap n B Γ S δ] [a, t, p, out, f]) rfl rfl (by room)).mono ?_ ?_
  · unfold shqrFp
    fp_sub
  · rintro m' - -
    exact ⟨trivial, [], rfl, trivial⟩

end NLAlib.ShiftedQR
