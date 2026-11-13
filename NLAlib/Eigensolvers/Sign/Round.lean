/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Step
public import NLAlib.Eigensolvers.Sign.Layout

/-!
# One executed Newton–Schulz round preserves the mathematical state relation

The matrix step and the refreshed stopping test are composed on their actual outputs.
Workspace subviews and kept constants come from shared spatial rules; the mathematical
transition is exactly the existing rounded matrix step.

## Main results

* `NLAlib.Sign.writes_round`: one total round returns the next matrix, cache and actual flag.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has CmpTst Tst] {M : Ops.Machine K} {dec : K → ℝ}
  {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- A complete round returns the actual next iterate, its actual cached square and its actual
stopping flag. The three control constants are outside the written footprint. The temporary
literal and unused matrix scratch require capacity but no initial contents. -/
theorem writes_round {I : Interp Op Tst K} (hS : IsScalar M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) (η : K) {x w v t : ℕ × ℕ} {m : Mem K}
    (hState : LoopState (M.toFloatMachine dec mm qr unif normal) x w t η A m.store)
    (hl : m.Live [x, w, v, t])
    (hAP : Fp.Apart [x, w, v, t] [2 * (n * n), 2 * (n * n), 2 * (n * n), 5])
    (hx : x.2 + 2 * (n * n) ≤ m.store.len x.1)
    (hw : w.2 + 2 * (n * n) ≤ m.store.len w.1)
    (hv : v.2 + 2 * (n * n) ≤ m.store.len v.1) (ht : t.2 + 5 ≤ m.store.len t.1) :
    Writes .total I τ (round (Has.inj MatrixOp.mul)).body
      (Env.frame [n] [x, w, v, t, x, w, v, t]) (loopFootprint n x w v t)
      (fun μ => LoopState (M.toFloatMachine dec mm qr unif normal) x w t η
        (newtonSchulzRounded (M.toFloatMachine dec mm qr unif normal) A) μ.store ∧
        μ.pos = m.pos) m := by
  generalize hB : newtonSchulzRounded (M.toFloatMachine dec mm qr unif normal) A = B
  have hn : n * n * 2 = 2 * (n * n) := Nat.mul_comm _ _
  have hLS : m.Live [x, w, v, (t.1, t.2 + 2)] := by simpa [Mem.Live] using hl
  have hs := writes_step (dec := dec) (mm := mm) (qr := qr) (unif := unif) (normal := normal)
    (τ := τ) hS hMM A hLS (apart_step hAP)
    (by simpa only [hn] using hState.matrix)
    (by simpa only [hn, Machine.toFloatMachine] using hState.square)
    hx hw hv (by dsimp; omega)
  rw [hB] at hs
  have hlStep : m.Live [x, w, v, (t.1, t.2 + 2), x, w, v, (t.1, t.2 + 2)] :=
    (Mem.live_append m _ _).mpr ⟨hLS, hLS⟩
  have hsubStep : Store.inBlock x.1 x.2 (2 * (n * n)) ⊔
      Store.inBlock w.1 w.2 (2 * (n * n)) ⊔ Store.inBlock v.1 v.2 (2 * (n * n)) ⊔
      Store.inBlock t.1 (t.2 + 2) 1 ≤ loopFootprint n x w v t := by fp_sub [loopFootprint]
  refine ((writes_frame rfl rfl hlStep hs).mono hsubStep (fun _ _ h => h)).seq_le le_rfl
    fun μ hfr hp => ?_
  have hread := (Store.readsOnly_get t.1 t.2 η).and
    ((Store.readsOnly_get t.1 (t.2 + 3) (M.lit 1)).and
      (Store.readsOnly_get t.1 (t.2 + 4) (M.neg η)))
  have hconst := hfr.keep hread (disj_loopFootprint_constantsFootprint hAP)
    ⟨hState.threshold, hState.one, hState.lower⟩
  have hAPtest := apart_test hAP
  have hlTest : μ.Live [x, (t.1, t.2 + 3), (t.1, t.2 + 4), t, w, v, (t.1, t.2 + 1)] := by
    simpa [Mem.Live, hfr.length_eq, and_assoc, and_left_comm, and_comm] using hl
  have hw' : w.2 + 2 * (n * n) ≤ μ.store.len w.1 := by rw [hfr.len_eq]; exact hw
  have hv' : v.2 + 2 * (n * n) ≤ μ.store.len v.1 := by rw [hfr.len_eq]; exact hv
  have hz' : t.2 + 1 < μ.store.len t.1 := by rw [hfr.len_eq]; omega
  have hsubTest : Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
      Store.inBlock v.1 v.2 (2 * (n * n)) ⊔ Store.inBlock t.1 (t.2 + 1) 1 ≤
      loopFootprint n x w v t := by
    exact sup_le (sup_le ((le_sup_right.trans le_sup_left).trans le_sup_left)
      (le_sup_right.trans le_sup_left))
      ((Fp.inBlock_le_inBlock (by simp) (by simp)).trans le_sup_right)
  have hdis (i j : Fin 4) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have hTX : Fp.Disj (Store.inBlock t.1 t.2 5)
      (Store.inBlock x.1 x.2 (2 * (n * n))) := by simpa using hdis 3 0 (by simp)
  have hkeepX : Fp.Disj (Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
      Store.inBlock v.1 v.2 (2 * (n * n)) ⊔ Store.inBlock t.1 (t.2 + 1) 1)
      (Store.inBlock x.1 x.2 (2 * (n * n))) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hdis 1 0 (by simp),
      hdis 2 0 (by simp)⟩, hTX.mono
        (Fp.inBlock_le_inBlock (by simp) (by simp)) le_rfl⟩
  have htest := (writes_test (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS hC hMM _ η hlTest hAPtest hp.2
    hconst.2.1 hconst.2.2 hconst.1 hw' hv' hz').keep
      ((Store.readsOnly_readBlock x.1 x.2 (2 * (n * n)) _).and hread)
      (Fp.disj_sup_right.mpr ⟨hkeepX,
        (disj_loopFootprint_constantsFootprint hAP).mono hsubTest le_rfl⟩) ⟨hp.2, hconst⟩
  refine (writes_frame rfl rfl hlTest htest).mono hsubTest ?_
  intro ν _ h
  refine ⟨⟨?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h.1.2.2⟩, h.1.1.trans hp.1⟩
  · simpa only [hn] using h.2.1
  · simpa only [hn, Machine.toFloatMachine] using h.1.2.1

end NLAlib.Sign
