/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Test
public import NLAlib.Matrix.FinitePrecision.OpsHermitianShiftNegate

/-!
# The actual rounded Newton–Schulz matrix step

The step uses the square cached by the previous executed test, forms the negated shifted
matrix, multiplies it by the same iterate, and stores its Hermitian average. All scalar and
matrix operations come from the same interpretation and mathematical machine.

## Main results

* `NLAlib.Sign.writes_step` returns the existing mathematical rounded step on the actual iterate.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  {M : Ops.Machine K} {dec : K → ℝ}
  {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- One step writes exactly the existing rounded Newton–Schulz matrix. Its cached square is
of this same actual input matrix. All four supplied regions are disjoint; the temporary scalar
need not be initialized. Numerical accuracy is a separate property of the machine and product. -/
theorem writes_step {I : Interp Op Tst K} (hS : IsScalar M I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) {x w v c : ℕ × ℕ} {m : Mem K}
    (hl : m.Live [x, w, v, c])
    (hAP : Fp.Apart [x, w, v, c] [2 * (n * n), 2 * (n * n), 2 * (n * n), 1])
    (hX : m.store.readBlock x.1 x.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hW : m.store.readBlock w.1 w.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix (mm A A)))
    (hx : x.2 + 2 * (n * n) ≤ m.store.len x.1)
    (hw : w.2 + 2 * (n * n) ≤ m.store.len w.1)
    (hv : v.2 + 2 * (n * n) ≤ m.store.len v.1) (hc : c.2 < m.store.len c.1) :
    Writes .total I τ (step (Has.inj MatrixOp.mul)).body
      (Env.frame [n] [x, w, v, c, x, w, v, c])
      (Store.inBlock x.1 x.2 (2 * (n * n)) ⊔ Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
        Store.inBlock v.1 v.2 (2 * (n * n)) ⊔ Store.inBlock c.1 c.2 1)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock x.1 x.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          (newtonSchulzRounded (M.toFloatMachine dec mm qr unif normal) A))) m := by
  have hn : n * n * 2 = 2 * (n * n) := Nat.mul_comm _ _
  have hdis (i j : Fin 4) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have h3 := writes_call_const (md := .total) (τ := τ)
    (ρ := Env.frame [n] [x, w, v, c, x, w, v, c]) (hS (.lit 3))
    (out := ⟨3, .var 4⟩) rfl trivial hc
  refine h3.seq_le le_sup_right fun μ hfr0 hthree => ?_
  have hW' := hfr0.keep (Store.readsOnly_readBlock w.1 w.2 (2 * (n * n))
    ((EntryCodec.pair K).packFinMatrix (mm A A))) (hdis 3 1 (by decide)) hW
  have hv' : v.2 + 2 * (n * n) ≤ μ.store.len v.1 := by rw [hfr0.len_eq]; exact hv
  have hl1 : μ.Live [w, c, v] := by
    simpa [Mem.Live, hfr0.length_eq] using ⟨hl w (by simp), hl c (by simp), hl v (by simp)⟩
  have hp := Hermitian.writes_shiftNegate_packed (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS (mm A A) (M.lit 3)
    (hdis 1 2 (by decide)) (hdis 3 2 (by decide)) hW' hthree.2 hv' hl1
  refine (writes_frame rfl rfl hl1 hp).seq_le (le_sup_right.trans le_sup_left)
    fun ν hfr1 hprep => ?_
  have hfr01 := hfr0.trans' hfr1
  have hX' := hfr01.keep (Store.readsOnly_readBlock x.1 x.2 (2 * (n * n))
    ((EntryCodec.pair K).packFinMatrix A))
    ((Fp.disj_sup_left).mpr ⟨hdis 3 0 (by decide), hdis 2 0 (by decide)⟩) hX
  have hw' : w.2 + 2 * (n * n) ≤ ν.store.len w.1 := by rw [hfr01.len_eq]; exact hw
  have hl2 : ν.Live [x, v, w] := by
    simpa [Mem.Live, hfr01.length_eq] using ⟨hl x (by simp), hl v (by simp), hl w (by simp)⟩
  have hm := writes_matrixMul_packFinMatrix (md := .total) (I := I) (τ := τ)
    (ρ := Env.frame [n] [x, w, v, c, x, w, v, c])
    (ds := [.var 0, .var 0, .var 0]) (ins := [⟨0, .var 1⟩, ⟨2, .var 3⟩])
    (outs := [⟨1, .var 2⟩]) (EntryCodec.pair K) mm hMM A _ rfl rfl rfl hl2
    (by simpa only [hn] using hX') (by simpa [hn] using hprep.2)
    (by simpa only [hn] using hw')
  rw [hn] at hm
  refine hm.seq_le ((le_sup_right.trans le_sup_left).trans le_sup_left) fun ω hfr2 hprod => ?_
  have hfr012 := hfr01.trans' hfr2
  have hc' : c.2 < ω.store.len c.1 := by rw [hfr012.len_eq]; exact hc
  have h4 := (writes_call_const (md := .total) (τ := τ)
    (ρ := Env.frame [n] [x, w, v, c, x, w, v, c]) (hS (.lit 4))
    (out := ⟨3, .var 4⟩) rfl trivial hc').keep
      (Store.readsOnly_readBlock w.1 w.2 (2 * (n * n)) _) (hdis 3 1 (by decide)) hprod.2
  refine h4.seq_le le_sup_right fun χ hfr3 hfour => ?_
  have hfr0123 := hfr012.trans' hfr3
  have hx' : x.2 + 2 * (n * n) ≤ χ.store.len x.1 := by rw [hfr0123.len_eq]; exact hx
  have hl3 : χ.Live [w, c, x] := by
    simpa [Mem.Live, hfr0123.length_eq] using ⟨hl w (by simp), hl c (by simp), hl x (by simp)⟩
  have ha := Hermitian.writes_average_packed (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS _ (M.lit 4)
    (hdis 1 0 (by decide)) (hdis 3 0 (by decide)) hfour.2 hfour.1.2 hx' hl3
  refine (writes_frame rfl rfl hl3 ha).mono ((le_sup_left.trans le_sup_left).trans le_sup_left) ?_
  intro μ' _ hlast
  exact ⟨hlast.1.trans (hfour.1.1.trans (hprod.1.trans (hprep.1.trans hthree.1))), by
    simpa [newtonSchulzRounded, Machine.toFloatMachine] using hlast.2⟩

end NLAlib.Sign
