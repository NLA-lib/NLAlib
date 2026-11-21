/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedRoutine
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEig

/-!
# The routine of rounded shifted QR with the small-eigenvalue program

`NLAlib.ShiftedQR.shqrSmallEigRoutine` is
`[n, k, np, F, T] (A : update 2 (n + 1)², t : read 1, p : read np) →
(out : write 2 (n + 1), f : write 1)`: the program `NLAlib.ShiftedQR.roundedShQRSmallEig` at the
order `n + 1`, with no eigenvalue oracle. As for `NLAlib.ShiftedQR.shqrRoutine`, on every tape
the run terminates and changes only the matrix, the output and the failure word; nothing is
claimed of their contents or of the number of tape positions consumed.

## Main definitions

* `NLAlib.ShiftedQR.shqrSmallEigRoutine`, `NLAlib.ShiftedQR.shqrSmallEigSpec`.

## Main results

* `NLAlib.ShiftedQR.shqrSmallEigRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops SmallEig
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has SampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- Rounded shifted QR with the small-eigenvalue program at the order `n + 1`:
`[n, k, np, F, T] (A : update 2 (n + 1)², t : read 1, p : read np) →
(out : write 2 (n + 1), f : write 1)`. The number of draws depends on the data, so the
routine declares none. The unreported written operands and the termination specification, the
dimension, the `isolated` parameter words and the single buffer variable of the matrix are as
for `NLAlib.ShiftedQR.shqrRoutine`. -/
def shqrSmallEigRoutine (sG : ℕ) : Routine O Q :=
  routine% [n, k, np, F, T] (unreported A : 2 * ((n + 1) * (n + 1)), t : 1, p : np) →
      (A, unreported out : 2 * (n + 1), unreported f : 1)
    draws unspecified one variable {
    run (roundedShQRSmallEig (O := O) (Q := Q) sG) [n + 1, k, np, F, T] (A, t, p, out, f)
  }

/-- The input is the words of a matrix of order `n + 1`, the deflation threshold word and the
parameter words of the reals $B, \Gamma, \Sigma, \delta, \varphi$ at the tail records, at the
shift degree, word count and two caps they determine, with the natural literals up to `n + 1`
exact on the machine. Nothing is claimed of the written blocks. -/
noncomputable def shqrSmallEigSpec (Mch : Machine ℝ) (B Γ S δ φ : ℝ)
    (c₁ c₂ : PolyLogTail) : Routine.Spec ℝ :=
  .terminates fun d _ X => IsExactNatLit id Mch (d.headD 0 + 1) ∧ d.getD 1 0 = shqrDegree (4 * B) ∧
    d.getD 2 0 = (shqrSmallEigParams (d.headD 0) (d.getD 1 0) B Γ S δ φ c₁ c₂).length ∧
    d.getD 3 0 = shqrCap (d.headD 0) B Γ S δ ∧
    d.getD 4 0 = shqrSmallEigCap (d.headD 0) (d.getD 1 0) B Γ S δ φ c₁ c₂ ∧
    ∃ H : Matrix (Fin (d.headD 0 + 1)) (Fin (d.headD 0 + 1)) ℂ,
      X = [matrixWords H, [shqrDeflationThreshold (d.headD 0) (d.getD 1 0) B Γ S δ φ],
        shqrSmallEigParams (d.headD 0) (d.getD 1 0) B Γ S δ φ c₁ c₂]

/-- Rounded shifted QR with the small-eigenvalue program terminates on every tape and changes
only the matrix, the output and the failure word. -/
theorem shqrSmallEigRoutine_meets {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I)
    {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I) {B Γ S δ φ : ℝ} {c₁ c₂ : PolyLogTail} :
    (shqrSmallEigRoutine (O := O) (Q := Q) sG).Meets I
      (shqrSmallEigSpec Mch B Γ S δ φ c₁ c₂) := by
  routine_intro [n, k, np, F, T] (a, t, p, out, f) reads (ws, ts, ps)
  obtain ⟨hNat, hk, hnp, hF, hT, H, heq⟩ := hpre
  change k = shqrDegree (4 * B) at hk
  obtain rfl : np = (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length := hnp
  obtain rfl : F = shqrCap n B Γ S δ := hF
  obtain rfl : T = shqrSmallEigCap n k B Γ S δ φ c₁ c₂ := hT
  obtain ⟨rfl, rfl, rfl⟩ : ws = matrixWords H ∧
      ts = [shqrDeflationThreshold n k B Γ S δ φ] ∧
        ps = shqrSmallEigParams n k B Γ S δ φ c₁ c₂ := by
    simpa using heq
  have hA := hws
  have ht := hts
  have hp := hps
  have hpos : 0 < (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length := by
    simp [shqrSmallEigParams, shqrParams, roundedDecoupleParams]
  have hin : ShQRSmallEigInput k B Γ S δ φ c₁ c₂ a t p out f H m := by
    refine ⟨by room, ?_, ⟨by disjoint, by disjoint⟩, hA, ?_, hp⟩
    · simp only [Mem.room_cons, Mem.room_nil, and_true]
      exact ⟨hroom.1, Store.le_len_of_readBlock ht Nat.one_pos,
        Store.le_len_of_readBlock hp hpos, hroom.2.1, hroom.2.2⟩
    · simpa [vec] using Store.get_of_readBlock ht (j := 0) Nat.one_pos default
  have hT := roundedShQRSmallEig_terminates (O := O) (Q := Q) (sG := sG) hS hL hNat hQ hC hSmp
    hDisk hk hin τ
  refine (hT.in_frame (ρ := Env.frame [n, k, (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length,
    shqrCap n B Γ S δ, shqrSmallEigCap n k B Γ S δ φ c₁ c₂] [a, t, p, out, f]) rfl rfl
    (by room)).mono ?_ ?_
  · unfold shqrFp
    fp_sub
  · rintro m' - -
    exact ⟨trivial, [], rfl, trivial⟩

end NLAlib.ShiftedQR
