/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Math
public import NLAlib.Matrix.FinitePrecision.OpsHermitian
public import NLAlib.Ops.Blas.HermitianTest
public import NLAlib.Ops.Logic.MatrixPacked

/-!
# The executed Newton–Schulz stopping test

The program computes its square, shifts it using the same scalar machine, and scans the
actual packed output. The cache and the failure flag belong to this same execution.

## Main results

* `NLAlib.Sign.writes_test` returns the actual cached square and the mathematical stopping flag.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has CmpTst Tst] {M : Ops.Machine K} {dec : K → ℝ}
  {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- The complete stopping-test program computes the actual square and a zero/one word for the
existing matrix stopping predicate. All seven supplied word regions are pairwise disjoint,
including scalar endpoints that may share one buffer; no output initialization is required. -/
theorem writes_test {I : Interp Op Tst K} (hS : IsScalar M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) (η : K)
    {x one lo hi w v z : ℕ × ℕ} {m : Mem K}
    (hl : m.Live [x, one, lo, hi, w, v, z])
    (hAP : Fp.Apart [x, one, lo, hi, w, v, z]
      [2 * (n * n), 1, 1, 1, 2 * (n * n), 2 * (n * n), 1])
    (hX : m.store.readBlock x.1 x.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hOne : m.store.get one.1 one.2 = some (M.lit 1))
    (hLo : m.store.get lo.1 lo.2 = some (M.neg η))
    (hHi : m.store.get hi.1 hi.2 = some η)
    (hW : w.2 + 2 * (n * n) ≤ m.store.len w.1)
    (hV : v.2 + 2 * (n * n) ≤ m.store.len v.1) (hz : z.2 < m.store.len z.1) :
    Writes .total I τ (test (Has.inj MatrixOp.mul)).body
      (Env.frame [n] [x, one, lo, hi, w, v, z])
      (Store.inBlock w.1 w.2 (2 * (n * n)) ⊔ Store.inBlock v.1 v.2 (2 * (n * n)) ⊔
        Store.inBlock z.1 z.2 1)
      (fun μ => μ.pos = m.pos ∧
        μ.store.readBlock w.1 w.2 (2 * (n * n)) =
          some ((EntryCodec.pair K).packFinMatrix (mm A A)) ∧
        μ.store.get z.1 z.2 = some
          (if newtonSchulzTest (M.toFloatMachine dec mm qr unif normal) η A
            then M.lit 0 else M.lit 1)) m := by
  have hn : n * n * 2 = 2 * (n * n) := Nat.mul_comm _ _
  have hdis (i j : Fin 7) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have hw := writes_matrixMul_packFinMatrix (md := .total) (I := I) (τ := τ)
    (ρ := Env.frame [n] [x, one, lo, hi, w, v, z])
    (ds := [.var 0, .var 0, .var 0]) (ins := [⟨0, .var 1⟩, ⟨0, .var 1⟩])
    (outs := [⟨4, .var 5⟩]) (EntryCodec.pair K) mm hMM A A rfl rfl rfl
    (by simpa [Mem.Live] using ⟨hl x (by simp), hl w (by simp)⟩)
    (by simpa only [hn] using hX) (by simpa only [hn] using hX)
    (by simpa only [hn] using hW)
  rw [hn] at hw
  refine hw.seq_le (le_sup_left.trans le_sup_left) fun μ hfr hp => ?_
  have hOne' := hfr.keep (Store.readsOnly_get one.1 one.2 (M.lit 1)) (hdis 4 1 (by decide)) hOne
  have hLo' := hfr.keep (Store.readsOnly_get lo.1 lo.2 (M.neg η)) (hdis 4 2 (by decide)) hLo
  have hHi' := hfr.keep (Store.readsOnly_get hi.1 hi.2 η) (hdis 4 3 (by decide)) hHi
  have hv : v.2 + 2 * (n * n) ≤ μ.store.len v.1 := by rw [hfr.len_eq]; exact hV
  have hl1 : μ.Live [w, one, v] := by
    simpa [Mem.Live, hfr.length_eq] using ⟨hl w (by simp), hl one (by simp), hl v (by simp)⟩
  have hs := Hermitian.writes_shift_packed (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS (mm A A) (M.lit 1)
    (hdis 4 5 (by decide)) (hdis 1 5 (by decide)) hp.2 hOne' hv hl1
  refine (writes_frame rfl rfl hl1 hs).seq_le (le_sup_right.trans le_sup_left)
    fun ν hfr' hshift => ?_
  have hLo'' := hfr'.keep (Store.readsOnly_get lo.1 lo.2 (M.neg η))
    (hdis 5 2 (by decide)) hLo'
  have hHi'' := hfr'.keep (Store.readsOnly_get hi.1 hi.2 η) (hdis 5 3 (by decide)) hHi'
  have hW' := hfr'.keep (Store.readsOnly_readBlock w.1 w.2 (2 * (n * n))
    ((EntryCodec.pair K).packFinMatrix (mm A A))) (hdis 5 4 (by decide)) hp.2
  have hz' : z.2 < ν.store.len z.1 := by rw [hfr'.len_eq, hfr.len_eq]; exact hz
  have hl2 : ν.Live [v, lo, hi, z] := by
    simpa [Mem.Live, hfr'.length_eq, hfr.length_eq] using
      ⟨hl v (by simp), hl lo (by simp), hl hi (by simp), hl z (by simp)⟩
  have hb := (Hermitian.writes_boxTest (md := .total) (τ := τ) hS hC hl2 hshift.2
    hLo'' hHi'' hz' (hdis 5 6 (by decide)) (hdis 2 6 (by decide)) (hdis 3 6 (by decide))).keep
      (Store.readsOnly_readBlock w.1 w.2 (2 * (n * n))
        ((EntryCodec.pair K).packFinMatrix (mm A A))) (hdis 6 4 (by decide)) hW'
  refine (writes_frame rfl rfl hl2 hb).mono le_sup_right ?_
  intro ω _ hbox
  refine ⟨hbox.1.1.trans (hshift.1.trans hp.1), hbox.2, ?_⟩
  have ht := newtonSchulzTest_eq_true_iff_inInterval M dec mm qr unif normal η A
  rw [← ht] at hbox
  cases hc : newtonSchulzTest (M.toFloatMachine dec mm qr unif normal) η A <;>
    simpa [hc] using hbox.1.2

end NLAlib.Sign
