/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEig
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# The routine of rounded shifted QR with the small-eigenvalue program

`NLAlib.ShiftedQR.shqrSmallEigRoutine` is
`[n, k, np, F, T] (A : update 2 (n + 1)², t : read 1, p : read np, U : update 2 (n + 1)²) →
(f : write 1)`: the program `NLAlib.ShiftedQR.roundedShQRSmallEig` at the order `n + 1`, in
Schur mode, with no eigenvalue oracle. On every tape the run terminates and changes only the
matrix, the accumulator and the failure word; nothing is claimed of their contents or of the
number of tape positions consumed. The accuracy of the output is a statement in probability
(`NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEig`), not a postcondition.

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

/-- Rounded shifted QR with the small-eigenvalue program at the order `n + 1`. The dimension `n`
is one less than the order, so that every dimension is the order of a nonempty matrix; the log
shape `F (k + 1 + np)`, `k (n + 1)` of the program is computed from the dimensions. The number
of draws depends on the data, so the routine declares none. The written operands are unreported:
the termination theorem (`NLAlib.ShiftedQR.roundedShQRSmallEig_terminates`) states the footprint
of the run, not the contents left. The threshold word and the parameter words are read only and
may overlap: the input condition `NLAlib.ShiftedQR.ShQRSmallEigInput` takes each of them apart
from the written operands, not from the other. The tree has one variable for each of the matrix
and the accumulator, named in both positions of the call. -/
def shqrSmallEigRoutine (sG : ℕ) : Routine O Q :=
  routine% [n, k, np, F, T] (unreported A : 2 * ((n + 1) * (n + 1)), t : 1, p : np,
      unreported U : 2 * ((n + 1) * (n + 1))) → (A, U, unreported f : 1)
    draws unspecified one variable {
    run (roundedShQRSmallEig (O := O) (Q := Q) sG)
      [n + 1, k, np, F, T, F * (k + 1 + np), k * (n + 1)] (A, t, p, U, A, U, f)
  }

/-- The input is the words of a matrix of order `n + 1`, the deflation threshold word, the
parameter words of the reals $B, \Gamma, \Sigma, \delta, \varphi$ at the tail records and the
words of an accumulator, at the shift degree, word count and two caps they determine, with the
natural literals up to `n + 1` exact on the machine. Nothing is claimed of the written blocks. -/
noncomputable def shqrSmallEigSpec (Mch : Machine ℝ) (B Γ S δ φ : ℝ)
    (c₁ c₂ : PolyLogTail) : Routine.Spec ℝ :=
  .terminates fun d _ X => IsExactNatLit id Mch (d.headD 0 + 1) ∧ d.getD 1 0 = shqrDegree (4 * B) ∧
    d.getD 2 0 = (shqrSmallEigParams (d.headD 0) (d.getD 1 0) B Γ S δ φ c₁ c₂).length ∧
    d.getD 3 0 = shqrCap (d.headD 0) B Γ S δ ∧
    d.getD 4 0 = shqrSmallEigCap (d.headD 0) (d.getD 1 0) B Γ S δ φ c₁ c₂ ∧
    ∃ H U₀ : Matrix (Fin (d.headD 0 + 1)) (Fin (d.headD 0 + 1)) ℂ,
      X = [matrixWords H, [shqrDeflationThreshold (d.headD 0) (d.getD 1 0) B Γ S δ φ],
        shqrSmallEigParams (d.headD 0) (d.getD 1 0) B Γ S δ φ c₁ c₂, matrixWords U₀]

/-- Rounded shifted QR with the small-eigenvalue program terminates on every tape and changes
only the matrix, the accumulator and the failure word. -/
theorem shqrSmallEigRoutine_meets {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I)
    {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I) {B Γ S δ φ : ℝ} {c₁ c₂ : PolyLogTail} :
    (shqrSmallEigRoutine (O := O) (Q := Q) sG).Meets I
      (shqrSmallEigSpec Mch B Γ S δ φ c₁ c₂) := by
  routine_intro [n, k, np, F, T] (a, t, p, out, f) reads (ws, ts, ps, us)
  obtain ⟨hNat, hk, hnp, hF, hT, H, U₀, heq⟩ := hpre
  change k = shqrDegree (4 * B) at hk
  obtain rfl : np = (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length := hnp
  obtain rfl : F = shqrCap n B Γ S δ := hF
  obtain rfl : T = shqrSmallEigCap n k B Γ S δ φ c₁ c₂ := hT
  obtain ⟨rfl, rfl, rfl, rfl⟩ : ws = matrixWords H ∧
      ts = [shqrDeflationThreshold n k B Γ S δ φ] ∧
        ps = shqrSmallEigParams n k B Γ S δ φ c₁ c₂ ∧ us = matrixWords U₀ := by
    simpa using heq
  have hpos : 0 < (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length := by
    simp [shqrSmallEigParams, shqrParams, roundedDecoupleParams]
  have hin : ShQRSmallEigInput k B Γ S δ φ c₁ c₂ a t p out f H m := by
    refine ⟨by room, ?_, ?_, ⟨U₀, hus⟩, hws, ?_, hps⟩
    · simp only [Mem.room_cons, Mem.room_nil, and_true]
      exact ⟨hroom.1, Store.le_len_of_readBlock hts Nat.one_pos,
        Store.le_len_of_readBlock hps hpos, hroom.2.1, hroom.2.2⟩
    · unfold ShQRViewsApart
      exact ⟨by disjoint, by disjoint⟩
    · simpa [vec] using Store.get_of_readBlock hts (j := 0) Nat.one_pos default
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
