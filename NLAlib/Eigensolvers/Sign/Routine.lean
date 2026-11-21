/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Initialized
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.Step
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# The capped sign iteration meets its specification

`NLAlib.Sign.signRoutine` reads a packed square matrix and two parameters (a tolerance and a
scale), runs the capped Newton–Schulz sign iteration with scoped workspace, and writes the packed
result. Its judgment is total: there is no convergence or successful-run premise; convergence and
numerical accuracy are separate results about the written matrix.

## Main definitions

* `NLAlib.Sign.signSpec`: the written block is the capped sign iteration of the blocks read.

## Main results

* `NLAlib.Sign.signRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has IndexOp Op] [Has CmpTst Tst]

/-- The written block packs the capped sign iteration of the matrix that the first block read
packs, with the two parameters of the second block read. -/
noncomputable def signSpec (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K))
    (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K) : Routine.Spec K :=
  spec% [n, cap] (aw, pw) → (zw) ensures
    zw = (EntryCodec.pair K).packFinMatrix
      (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal) (vec pw 0) (vec pw 1)
        cap ((EntryCodec.pair K).matrix n n aw))

/-- A two-word block is its two entries. -/
theorem eq_vec_two {pw : List K} (h : pw.length = 2) : pw = [vec pw 0, vec pw 1] := by
  rcases pw with _ | ⟨p, _ | ⟨q, _ | ⟨_, _⟩⟩⟩
  · cases h
  · cases h
  · rfl
  · simp at h

/-- The capped sign routine meets its specification for every functional interpretation of the
scalar, index, multiplication and comparison operations with distinct decoded zero and one, at
every order and cap. The workspace (five scalar cells and two square matrices) is allocated and
freed inside; only the written matrix changes. There is no convergence or successful-run
premise. -/
theorem signRoutine_meets {M : Machine K} (dec : K → ℝ) (mm : MatMulMap (K × K))
    (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K) {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hIndex : IsIndexLit M I)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) :
    (signRoutine (Op := Op) (Tst := Tst) (Has.inj MatrixOp.mul)).Meets I
      (signSpec M dec mm qr unif normal) := by
  routine_intro [n, cap] (a, par, x) reads (aw, pw)
  have hlen' : aw.length = n * n * (EntryCodec.pair K).width := by
    have h := Store.length_of_readBlock haw
    simpa only [EntryCodec.pair, Nat.mul_comm] using h
  set A := (EntryCodec.pair K).matrix n n aw
  have hA : m.store.readBlock a.1 a.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A) := by
    rw [(EntryCodec.pair K).packFinMatrix_matrix _ _ _ hlen']
    exact haw
  have hPar : m.store.readBlock par.1 par.2 2 = some [vec pw 0, vec pw 1] := by
    rw [← eq_vec_two (Store.length_of_readBlock hpw)]
    exact hpw
  have hxs : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n))) (Store.inBlock a.1 a.2 (2 * (n * n))) ∧
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n))) (Store.inBlock par.1 par.2 2) := by
    simpa using hblocks.2.1
  have hxa := hxs.1.symm
  have hxp := hxs.2.symm
  have hw : Writes .total I τ (program (Has.inj MatrixOp.mul))
      (Env.frame [n, cap] [a, par, x]) (Store.inBlock x.1 x.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock x.1 x.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal) (vec pw 0) (vec pw 1)
            cap A))) m := by
    apply writes_allocs_readBlock
      (lens := [.const 5, .const 2 * (.var 0 * .var 0), .const 2 * (.var 0 * .var 0)])
      (ns := [5, 2 * (n * n), 2 * (n * n)]) rfl (hlive x (by simp))
    intro store hlength hlens hBelow
    have ha : a.1 < m.store.length := hlive a (by simp)
    have hp : par.1 < m.store.length := hlive par (by simp)
    have ho : x.1 < m.store.length := hlive x (by simp)
    have ht : store.len m.store.length = 5 := by simpa using hlens 0 (by simp)
    have hw : store.len (m.store.length + 1) = 2 * (n * n) := by
      simpa using hlens 1 (by simp)
    have hv : store.len (m.store.length + 2) = 2 * (n * n) := by
      simpa using hlens 2 (by simp)
    refine (writes_frame rfl rfl ?_ (writes_initialized (dec := dec) (mm := mm) (qr := qr)
      (unif := unif) (normal := normal) hS hC hMM hIndex A (vec pw 0) (vec pw 1) h01
      (by room) (by disjoint) ?_ (by kept) (by kept) (by room) (by room) (by room)
      (by room))).mono (by fp_sub) (fun _ _ h => h)
    · room
    · refine Fp.disj_sup_left.mpr ⟨?_, ?_⟩ <;>
        refine Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨?_, ?_⟩,
          ?_⟩, ?_⟩
      all_goals first | assumption | disjoint
  refine hw.mono (by fp_sub) ?_
  rintro μ' - ⟨hpos, hread⟩
  routine_exit
  exact rfl

end NLAlib.Sign
