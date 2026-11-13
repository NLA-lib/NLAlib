/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Loop

/-!
# The first stopping test and capped sign loop

The initial square cache and flag are computed from the actual stored matrix. The loop then
returns its stopped mathematical iterate, including the unchanged input when the first test
passes or the cap is zero.

## Main results

* `NLAlib.Sign.writes_start` computes the capped sign loop from a stored matrix and bounds.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has CmpTst Tst] {M : Ops.Machine K} {dec : K → ℝ}
  {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- Execute the initial test and the capped iteration on the same actual matrix. -/
theorem writes_start {I : Interp Op Tst K} (hS : IsScalar M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {n cap : ℕ}
    (B : Matrix (Fin n) (Fin n) (K × K)) (η : K) {x w v t : ℕ × ℕ} {m : Mem K}
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) (hl : m.Live [x, w, v, t])
    (hAP : Fp.Apart [x, w, v, t] [2 * (n * n), 2 * (n * n), 2 * (n * n), 5])
    (hX : m.store.readBlock x.1 x.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix B))
    (hη : m.store.get t.1 t.2 = some η)
    (hlo : m.store.get t.1 (t.2 + 4) = some (M.neg η))
    (hone : m.store.get t.1 (t.2 + 3) = some (M.lit 1))
    (hx : x.2 + 2 * (n * n) ≤ m.store.len x.1)
    (hw : w.2 + 2 * (n * n) ≤ m.store.len w.1)
    (hv : v.2 + 2 * (n * n) ≤ m.store.len v.1) (ht : t.2 + 5 ≤ m.store.len t.1) :
    Writes .total I τ (start (Has.inj MatrixOp.mul)).body
      (Env.frame [n, cap] [x, w, v, t, x, w, v, t]) (loopFootprint n x w v t)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock x.1 x.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          (newtonSchulzLoop (M.toFloatMachine dec mm qr unif normal) η cap B))) m := by
  have hn : n * n * 2 = 2 * (n * n) := Nat.mul_comm _ _
  have hdis (i j : Fin 4) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have hTX : Fp.Disj (Store.inBlock t.1 t.2 5)
      (Store.inBlock x.1 x.2 (2 * (n * n))) := by simpa using hdis 3 0 (by simp)
  have hlTest : m.Live [x, (t.1, t.2 + 3), (t.1, t.2 + 4), t, w, v, (t.1, t.2 + 1)] := by
    simpa [Mem.Live, and_assoc, and_left_comm, and_comm] using hl
  have htest := writes_test (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS hC hMM B η hlTest (apart_test hAP)
    hX hone hlo hη hw hv (by dsimp; omega)
  have hsub : Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
      Store.inBlock v.1 v.2 (2 * (n * n)) ⊔ Store.inBlock t.1 (t.2 + 1) 1 ≤
      loopFootprint n x w v t := by
    exact sup_le (sup_le ((le_sup_right.trans le_sup_left).trans le_sup_left)
      (le_sup_right.trans le_sup_left))
      ((Fp.inBlock_le_inBlock (by omega) (by omega)).trans le_sup_right)
  refine (writes_frame rfl rfl hlTest htest).seq_le hsub fun ψ hfr htested => ?_
  have hX' := hfr.keep (Store.readsOnly_readBlock x.1 x.2 (2 * (n * n)) _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hdis 1 0 (by simp),
      hdis 2 0 (by simp)⟩, hTX.mono
        (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl⟩) hX
  have hconst := hfr.keep
    ((Store.readsOnly_get t.1 t.2 η).and
      ((Store.readsOnly_get t.1 (t.2 + 3) (M.lit 1)).and
        (Store.readsOnly_get t.1 (t.2 + 4) (M.neg η))))
    ((disj_loopFootprint_constantsFootprint hAP).mono hsub le_rfl) ⟨hη, hone, hlo⟩
  have hState : LoopState (M.toFloatMachine dec mm qr unif normal) x w t η B ψ.store :=
    ⟨by simpa only [hn] using hX',
      by simpa only [hn, Machine.toFloatMachine] using htested.2.1,
      hconst.1, hconst.2.1, hconst.2.2, htested.2.2⟩
  have hlψ : ψ.Live [x, w, v, t] := by simpa [Mem.Live, hfr.length_eq] using hl
  have hlFrame : ψ.Live [x, w, v, t, x, w, v, t] :=
    (Mem.live_append ψ _ _).mpr ⟨hlψ, hlψ⟩
  have hloop := writes_loop (cap := cap) (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS hC hMM B η hState h01 hlψ hAP
    (by rw [hfr.len_eq]; exact hx) (by rw [hfr.len_eq]; exact hw)
    (by rw [hfr.len_eq]; exact hv) (by rw [hfr.len_eq]; exact ht)
  exact (writes_frame rfl rfl hlFrame hloop).mono le_rfl fun _ _ h =>
    ⟨h.2.trans htested.1, by simpa only [hn] using h.1.matrix⟩

end NLAlib.Sign
