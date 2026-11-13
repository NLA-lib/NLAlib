/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.InitialScalars
public import NLAlib.Eigensolvers.Sign.Start
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Initialization and total capped sign execution on caller-owned workspace

The threshold is computed from the actual stored tolerance and dimension literal. Scaling,
stopping tests, and each matrix transition then use the same word machine. The resulting
matrix is the existing mathematical capped sign algorithm on the supplied words.

## Main results

* `NLAlib.Sign.writes_initialized` refines the complete initialized sign implementation.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has IndexOp Op] [Has CmpTst Tst] {M : Ops.Machine K} {dec : K → ℝ}
  {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- The explicit initializer and capped loop compute the mathematical sign algorithm on the
actual stored input and parameters. Workspace requires capacity and separation, with no initial
contents. The theorem is total and does not assume numerical convergence or successful execution. -/
theorem writes_initialized {I : Interp Op Tst K} (hS : IsScalar M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hIndex : IsIndexLit M I)
    {τ : Tape K} {n cap : ℕ} (A : Matrix (Fin n) (Fin n) (K × K)) (eps b : K)
    {a par x w v t : ℕ × ℕ} {m : Mem K}
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) (hl : m.Live [a, par, x, w, v, t])
    (hAP : Fp.Apart [a, par, x, w, v, t]
      [2 * (n * n), 2, 2 * (n * n), 2 * (n * n), 2 * (n * n), 5])
    (hA : m.store.readBlock a.1 a.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hPar : m.store.readBlock par.1 par.2 2 = some [eps, b])
    (hx : x.2 + 2 * (n * n) ≤ m.store.len x.1)
    (hw : w.2 + 2 * (n * n) ≤ m.store.len w.1)
    (hv : v.2 + 2 * (n * n) ≤ m.store.len v.1) (ht : t.2 + 5 ≤ m.store.len t.1) :
    Writes .total I τ (initialized (Has.inj MatrixOp.mul)).body
      (Env.frame [n, cap] [a, par, x, w, v, t, x, w, v, t])
      (Store.inBlock x.1 x.2 (2 * (n * n)) ⊔ Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
        Store.inBlock v.1 v.2 (2 * (n * n)) ⊔ Store.inBlock t.1 t.2 5)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock x.1 x.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal) eps b cap A))) m := by
  let N := M.toFloatMachine dec mm qr unif normal
  let η := M.div eps (M.lit (4 * n : ℕ))
  let B := N.hermScale A b
  have hn : n * n * 2 = 2 * (n * n) := Nat.mul_comm _ _
  have hdis (i j : Fin 6) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have hsmall : Store.inBlock t.1 (t.2 + 2) 1 ≤ Store.inBlock t.1 t.2 5 :=
    Fp.inBlock_le_inBlock (by simp) (by simp)
  have hSource := (Store.readsOnly_readBlock a.1 a.2 (2 * (n * n))
    ((EntryCodec.pair K).packFinMatrix A)).and
    (Store.readsOnly_readBlock par.1 par.2 2 [eps, b])
  have hTSource : Fp.Disj (Store.inBlock t.1 t.2 5)
      (Store.inBlock a.1 a.2 (2 * (n * n)) ⊔ Store.inBlock par.1 par.2 2) :=
    Fp.disj_sup_right.mpr ⟨hdis 5 0 (by simp), hdis 5 1 (by simp)⟩
  have hi := writes_indexLit (m := m) (τ := τ)
    (ρ := Env.frame [n, cap] [a, par, x, w, v, t, x, w, v, t]) hIndex
    (e := .const 4 * .var 0) (out := ⟨5, .add (.var 7) (.const 2)⟩)
    rfl rfl (by dsimp; omega)
  refine hi.seq_le (hsmall.trans le_sup_right) fun μ hfr0 hden => ?_
  have hsrc := hfr0.keep hSource (hTSource.mono hsmall le_rfl) ⟨hA, hPar⟩
  have heps : μ.store.get par.1 par.2 = some eps := by
    simpa using Store.get_of_readBlock hsrc.2 (j := 0) (by simp) eps
  have ht' : t.2 + 5 ≤ μ.store.len t.1 := by rw [hfr0.len_eq]; exact ht
  have hs := writes_initialScalars (τ := τ) hS heps hden.2 ht'
  have hls : μ.Live [par, (t.1, t.2 + 2), t] := by
    simpa [Mem.Live, hfr0.length_eq] using
      (show par.1 < m.store.length ∧ t.1 < m.store.length from
        ⟨hl par (by simp), hl t (by simp)⟩)
  refine (writes_frame rfl rfl hls hs).seq_le le_sup_right fun ν hfr1 hsc => ?_
  have hfrT := (hfr0.trans' hfr1).mono (sup_le hsmall le_rfl)
  have hsrc' := hfrT.keep hSource hTSource ⟨hA, hPar⟩
  have hb : ν.store.get par.1 (par.2 + 1) = some b := by
    simpa using Store.get_of_readBlock hsrc'.2 (j := 1) (by simp) b
  have hx' : x.2 + 2 * (n * n) ≤ ν.store.len x.1 := by rw [hfrT.len_eq]; exact hx
  have hlsScale : ν.Live [a, (par.1, par.2 + 1), x] := by
    simpa [Mem.Live, hfrT.length_eq] using ⟨hl a (by simp), hl par (by simp), hl x (by simp)⟩
  have hpx : Fp.Disj (Store.inBlock par.1 (par.2 + 1) 1)
      (Store.inBlock x.1 x.2 (2 * (n * n))) :=
    (hdis 1 2 (by simp)).mono
      (Fp.inBlock_le_inBlock (by simp) (by simp)) le_rfl
  have hscale := Hermitian.writes_scale_packed (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS A b
    (hdis 0 2 (by simp)) hpx hsrc'.1 hb hx' hlsScale
  refine (writes_frame rfl rfl hlsScale hscale).seq_le
    ((le_sup_left.trans le_sup_left).trans le_sup_left) fun χ hfr2 hscaled => ?_
  have hfrAll := hfrT.trans' hfr2
  have htχ : t.2 + 5 ≤ χ.store.len t.1 := by rw [hfrAll.len_eq]; exact ht
  have hwχ : w.2 + 2 * (n * n) ≤ χ.store.len w.1 := by rw [hfrAll.len_eq]; exact hw
  have hvχ : v.2 + 2 * (n * n) ≤ χ.store.len v.1 := by rw [hfrAll.len_eq]; exact hv
  have hxT : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock t.1 t.2 5) := by simpa using hdis 2 5 (by simp)
  have hconstants := hfr2.keep
    ((Store.readsOnly_get t.1 t.2 η).and
      ((Store.readsOnly_get t.1 (t.2 + 4) (M.neg η)).and
        (Store.readsOnly_get t.1 (t.2 + 3) (M.lit 1))))
    (hxT.mono le_rfl (by fp_sub)) ⟨hsc.2.1, hsc.2.2⟩
  have hLoopAP : Fp.Apart [x, w, v, t]
      [2 * (n * n), 2 * (n * n), 2 * (n * n), 5] := hAP.2.2
  have hlχ : χ.Live [x, w, v, t] := by
    simpa [Mem.Live, hfrAll.length_eq] using
      ⟨hl x (by simp), hl w (by simp), hl v (by simp), hl t (by simp)⟩
  have hlFrame : χ.Live [x, w, v, t, x, w, v, t] :=
    (Mem.live_append χ _ _).mpr ⟨hlχ, hlχ⟩
  have hs := writes_start (cap := cap) (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS hC hMM B η h01 hlχ hLoopAP
    hscaled.2 hconstants.1 hconstants.2.1 hconstants.2.2
    (by rw [hfrAll.len_eq]; exact hx) hwχ hvχ htχ
  refine (writes_frame rfl rfl hlFrame hs).mono (by fp_sub [loopFootprint]) ?_
  intro ω _ h
  refine ⟨h.1.trans (hscaled.1.trans (hsc.1.trans hden.1)), ?_⟩
  simpa [newtonSchulzSign, N, η, B, Machine.toFloatMachine, hn] using h.2

end NLAlib.Sign
