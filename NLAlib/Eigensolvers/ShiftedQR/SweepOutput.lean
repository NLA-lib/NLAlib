/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Sweep
public import NLAlib.Ops.Blas.MapCorrect

/-!
# Stored last diagonal entry of a QR sweep

The sweep leaves its working matrix in supplied storage. A scalar copy extracts its final
complex diagonal entry into a separate two-word output before a caller releases that working
storage. The wrapper composes with an exact or rounded sweep proof, without repeating its
memory invariant or imposing a numerical accuracy assumption.

## Main results

* `NLAlib.ShiftedQR.copyLastDiagonal_writes`: the actual last diagonal word pair is copied.
* `NLAlib.ShiftedQR.sweepWithDiag_writes_of_sweep`: export the pair from any proved sweep.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Copy the final diagonal entry of an interleaved matrix into a two-word output. The
interface is `[n] (W) -> (D)`; the stored correctness theorem requires positive matrix order.
For order zero the index expression is total, but no diagonal-entry guarantee is asserted. -/
def copyLastDiagonal : Impl Op Tst where
  nd := 1
  nin := 1
  nout := 1
  body := .frame [.const 2]
    [⟨0, .var 1 + .const 2 * ((.var 0 - .const 1) * .var 0 + (.var 0 - .const 1))⟩,
      ⟨1, .var 2⟩] (unaryMap (Has.inj ScalarOp.copy)).body

/-- On any scalar machine, copying a positive-order matrix's last diagonal entry writes its
real and imaginary words exactly and preserves every other cell and the tape position.
The output has capacity for two words and is disjoint from the complete input matrix. -/
theorem copyLastDiagonal_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {w d : ℕ × ℕ}
    {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hW : HoldsMatrix w W m.store) (hd : d.2 + 2 ≤ m.store.len d.1)
    (hwd : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock d.1 d.2 2)) :
    Writes .total I τ copyLastDiagonal.body (Env.frame [n + 1] [w, d])
      (Store.inBlock d.1 d.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock d.1 d.2 2 =
        some [(W (Fin.last n) (Fin.last n)).re, (W (Fin.last n) (Fin.last n)).im]) m := by
  have hi : n * (n + 1) + n < (n + 1) * (n + 1) :=
    Idx.add_lt_mul (by omega) (by omega)
  have hsub : Store.inBlock w.1 (w.2 + 2 * (n * (n + 1) + n)) 2 ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) := by
    intro c j hj
    exact ⟨hj.1, by have := hj.2.1; omega, by have := hj.2.2; omega⟩
  have hr := hW.read_entry (Fin.last n) (Fin.last n)
  have hw := writes_unaryMap_of_disj_or_eq (md := .total) (τ := τ)
    (x := (w.1, w.2 + 2 * (n * (n + 1) + n))) (y := d) (f := id) (hS .copy)
    (Or.inl (hwd.mono hsub le_rfl)) hr hd
  unfold copyLastDiagonal
  simpa only [List.map_id] using hw.in_frame rfl rfl
    (by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using
        (And.intro (Store.lt_length_of_get (hW.get_re (Fin.last n) (Fin.last n)))
          (Store.lt_length_of_lt_len (by omega : d.2 < m.store.len d.1))))

variable [Has CmpTst Tst]

/-- Run the existing sweep and then copy the final working diagonal entry into a separate
pair. The interface is `[n] (W,Z,Cf) -> (W,Z,D)`; W and Z are exact in-place views, and D is
disjoint from both matrices and the four coefficient words. -/
def sweepWithDiag : Impl Op Tst where
  nd := 1
  nin := 3
  nout := 3
  body := .seq (.frame [.var 0]
    [⟨0, .var 1⟩, ⟨1, .var 2⟩, ⟨2, .var 3⟩, ⟨3, .var 4⟩, ⟨4, .var 5⟩] sweep.body)
    (.frame [.var 0] [⟨3, .var 4⟩, ⟨5, .var 6⟩] copyLastDiagonal.body)

/-- Any total sweep proof that identifies its final stored working and output matrices
extends to the wrapper with their last working diagonal entry copied into D. The output pair
has supplied capacity and is disjoint from the sweep's entire write footprint. All numerical
information remains in P, so exact and rounded sweep analyses use the same memory proof. -/
theorem sweepWithDiag_writes_of_sweep {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {w z cf d : ℕ × ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop}
    (hl : m.Live [w, z, cf, w, z, d]) (hd : d.2 + 2 ≤ m.store.len d.1)
    (hfd : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
      (Store.inBlock d.1 d.2 2))
    (hsweep : Writes .total I τ sweep.body (Env.frame [n + 1] [w, z, cf, w, z])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
      (fun m' => m'.pos = m.pos ∧ ∃ W Z, P W Z ∧
        HoldsMatrix w W m'.store ∧ HoldsMatrix z Z m'.store) m) :
    Writes .total I τ sweepWithDiag.body (Env.frame [n + 1] [w, z, cf, w, z, d])
      ((Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4) ⊔
          Store.inBlock d.1 d.2 2)
      (fun m' => m'.pos = m.pos ∧ ∃ W Z, P W Z ∧
        HoldsMatrix w W m'.store ∧ HoldsMatrix z Z m'.store ∧
        m'.store.readBlock d.1 d.2 2 =
          some [(W (Fin.last n) (Fin.last n)).re, (W (Fin.last n) (Fin.last n)).im]) m := by
  unfold sweepWithDiag
  refine hsweep.frame_seq_le rfl rfl ?_ le_sup_left ?_
  · exact hl.mono (by simp)
  intro m₁ hfr₁ ⟨hp₁, W, Z, hP, hW, hZ⟩
  have hwd := hfd.mono (le_sup_left.trans le_sup_left) le_rfl
  have hzd := hfd.mono (le_sup_right.trans le_sup_left) le_rfl
  have hc := copyLastDiagonal_writes (τ := τ) hS hW
    (by rw [hfr₁.len_eq]; exact hd) hwd
  refine (hc.in_frame rfl rfl ?_).mono le_sup_right ?_
  · exact (hl.congr hfr₁.length_eq).mono (by simp)
  intro m₂ hfr₂ ⟨hp₂, hD⟩
  exact ⟨hp₂.trans hp₁, W, Z, hP, hW.of_eqOff hfr₂ hwd.symm,
    hZ.of_eqOff hfr₂ hzd.symm, hD⟩

end NLAlib.ShiftedQR
