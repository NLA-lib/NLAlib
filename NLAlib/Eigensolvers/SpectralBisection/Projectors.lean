/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Node
public import NLAlib.Eigensolvers.Sign.Solve
public import NLAlib.Matrix.FinitePrecision.OpsHermitianShiftNegate
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Actual sign iterates and stored bisection projectors

The projectors use the actual capped sign result and the actual stored arithmetic constants.
Their shifts, negation and divisions are scalar subprograms. The total refinement does not
assume convergence of the sign loop; numerical projector estimates apply to its returned matrix
under the separate numerical hypotheses.

## Main results

* `NLAlib.SpectralBisection.writes_nodeProjectors` stores both mathematical rounded projectors.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has IndexOp Op] [Has CmpTst Tst] {M : Machine K} {dec : K → ℝ}
  {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

private def projectorTail : Impl Op Tst := opsImpl% [k, F] (W, sp, c) → (B, T, Pp, Pm) {
  run Hermitian.shift.body [k] (B, c[3], T);
  run Hermitian.scale.body [k] (T, c[1], Pp);
  run Hermitian.shiftNegate.body [k] (B, c, T);
  run Hermitian.scale.body [k] (T, c[1], Pm)
}

omit [Has MatrixOp Op] [Has IndexOp Op] [Has CmpTst Tst] in
private theorem writes_projectorTail {I : Interp Op Tst K} (hS : IsScalar M I)
    {τ : Tape K} {k fuel : ℕ} (B : Matrix (Fin k) (Fin k) (K × K))
    {w sp c b t pp pm : ℕ × ℕ} {m : Mem K} (hl : m.Live [w, sp, c, b, t, pp, pm])
    (hAP : Fp.Apart [c, b, t, pp, pm] [4, 2 * (k * k), 2 * (k * k),
      2 * (k * k), 2 * (k * k)])
    (hB : m.store.readBlock b.1 b.2 (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix B))
    (hc : m.store.readBlock c.1 c.2 4 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1)])
    (ht : t.2 + 2 * (k * k) ≤ m.store.len t.1)
    (hp : pp.2 + 2 * (k * k) ≤ m.store.len pp.1)
    (hm : pm.2 + 2 * (k * k) ≤ m.store.len pm.1) :
    Writes .total I τ projectorTail.body (Env.frame [k, fuel] [w, sp, c, b, t, pp, pm])
      (Store.inBlock t.1 t.2 (2 * (k * k)) ⊔ Store.inBlock pp.1 pp.2 (2 * (k * k)) ⊔
        Store.inBlock pm.1 pm.2 (2 * (k * k)))
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [pp, pm] [2 * (k * k), 2 * (k * k)] =
        some [(EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).hermScale
            ((M.toFloatMachine dec mm qr unif normal).hermShift B (M.neg (M.lit 1)))
            (M.lit 2)),
          (EntryCodec.pair K).packFinMatrix
            ((M.toFloatMachine dec mm qr unif normal).hermScale
              ((M.toFloatMachine dec mm qr unif normal).negMat
                ((M.toFloatMachine dec mm qr unif normal).hermShift B (M.lit 1)))
              (M.lit 2))]) m := by
  have hLive : w.1 < m.store.length ∧ sp.1 < m.store.length ∧ c.1 < m.store.length ∧
      b.1 < m.store.length ∧ t.1 < m.store.length ∧ pp.1 < m.store.length ∧
      pm.1 < m.store.length := by simpa [Mem.Live] using hl
  rcases hLive with ⟨hlw, hlsp, hlc, hlb, hlt, hlpp, hlpm⟩
  have hd (i j : Fin 5) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have hct : Fp.Disj (Store.inBlock c.1 c.2 4)
      (Store.inBlock t.1 t.2 (2 * (k * k))) := by simpa using hd 0 2 (by simp)
  have hcp : Fp.Disj (Store.inBlock c.1 c.2 4)
      (Store.inBlock pp.1 pp.2 (2 * (k * k))) := by simpa using hd 0 3 (by simp)
  have hcm : Fp.Disj (Store.inBlock c.1 c.2 4)
      (Store.inBlock pm.1 pm.2 (2 * (k * k))) := by simpa using hd 0 4 (by simp)
  have hc3 : m.store.get c.1 (c.2 + 3) = some (M.neg (M.lit 1)) := by
    simpa using Store.get_of_readBlock hc (j := 3) (by simp) (M.lit 1)
  have hRead := (Store.readsOnly_readBlock b.1 b.2 (2 * (k * k))
    ((EntryCodec.pair K).packFinMatrix B)).and
      (Store.readsOnly_readBlock c.1 c.2 4
        [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1)])
  have h1 := Hermitian.writes_shift_packed (x := b) (y := t)
    (c := (c.1, c.2 + 3)) (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS B (M.neg (M.lit 1))
    (hd 1 2 (by simp)) (hct.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl)
    hB hc3 ht (by room)
  refine (writes_frame rfl rfl (by room) h1).seq_le (le_sup_left.trans le_sup_left)
    fun μ hfr1 hshift => ?_
  have hSrc := hfr1.keep hRead (Fp.disj_sup_right.mpr ⟨hd 2 1 (by simp), hct.symm⟩) ⟨hB, hc⟩
  have hc1 : μ.store.get c.1 (c.2 + 1) = some (M.lit 2) := by
    simpa using Store.get_of_readBlock hSrc.2 (j := 1) (by simp) (M.lit 1)
  have h2 := Hermitian.writes_scale_packed (x := t) (y := pp)
    (c := (c.1, c.2 + 1)) (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS _ (M.lit 2)
    (hd 2 3 (by simp)) (hcp.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl)
    hshift.2 hc1 (by rw [hfr1.len_eq]; exact hp) (by room)
  refine (writes_frame rfl rfl (by room) h2).seq_le (le_sup_right.trans le_sup_left)
    fun ν hfr2 hplus => ?_
  have hfr12 := hfr1.trans' hfr2
  have hSrc' := hfr12.keep hRead (Fp.disj_sup_left.mpr
    ⟨Fp.disj_sup_right.mpr ⟨hd 2 1 (by simp), hct.symm⟩,
      Fp.disj_sup_right.mpr ⟨hd 3 1 (by simp), hcp.symm⟩⟩) ⟨hB, hc⟩
  have hc0 : ν.store.get c.1 c.2 = some (M.lit 1) := by
    simpa using Store.get_of_readBlock hSrc'.2 (j := 0) (by simp) (M.lit 1)
  have h3 := Hermitian.writes_shiftNegate_packed (x := b) (y := t) (c := c)
    (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS B (M.lit 1)
    (hd 1 2 (by simp)) (hct.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl)
    hSrc'.1 hc0 (by rw [hfr12.len_eq]; exact ht) (by room)
  refine (writes_frame rfl rfl (by room) h3).seq_le (le_sup_left.trans le_sup_left)
    fun χ hfr3 hminus => ?_
  have hfr123 := hfr12.trans' hfr3
  have hPp := hfr3.keep (Store.readsOnly_readBlock pp.1 pp.2 (2 * (k * k)) _)
    (hd 2 3 (by simp)) hplus.2
  have hc1' := hfr123.keep (Store.readsOnly_readBlock c.1 c.2 4 _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hct.symm, hcp.symm⟩, hct.symm⟩) hc
  have hc1χ : χ.store.get c.1 (c.2 + 1) = some (M.lit 2) := by
    simpa using Store.get_of_readBlock hc1' (j := 1) (by simp) (M.lit 1)
  have h4 := (Hermitian.writes_scale_packed (x := t) (y := pm)
    (c := (c.1, c.2 + 1)) (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hS _ (M.lit 2)
    (hd 2 4 (by simp)) (hcm.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl)
    hminus.2 hc1χ (by rw [hfr123.len_eq]; exact hm) (by room)).keep
      (Store.readsOnly_readBlock pp.1 pp.2 (2 * (k * k)) _) (hd 4 3 (by simp)) hPp
  refine (writes_frame rfl rfl (by room) h4).mono le_sup_right ?_
  intro ψ _ h
  refine ⟨h.1.1.trans (hminus.1.trans (hplus.1.trans hshift.1)), ?_⟩
  simp only [Mem.readBlocks_cons, Mem.readBlocks_nil, h.2, h.1.2, Option.bind_some,
    Option.map_some]

/-- The sign call uses the input matrix, parameters and result views of the node workspace. -/
private theorem apart_sign {k : ℕ} {w sp c b t pp pm : ℕ × ℕ}
    (h : Fp.Apart [w, sp, c, b, t, pp, pm]
      [2 * (k * k), 2, 4, 2 * (k * k), 2 * (k * k), 2 * (k * k), 2 * (k * k)]) :
    Fp.Apart [w, sp, b] [2 * (k * k), 2, 2 * (k * k)] := by
  have hv := h.subviews (fun i : Fin 3 => (![0, 1, 3] : Fin 3 → Fin 7) i)
    (fun _ => 0) ![2 * (k * k), 2, 2 * (k * k)]
    (by intro i; fin_cases i <;> simp)
    (by intro i j hij hp; fin_cases i <;> fin_cases j <;> simp at hp hij ⊢)
  simpa using hv

/-- The actual capped sign matrix yields both actual rounded projector matrices. Functional
operation contracts, readable inputs, writable separated regions and distinguishable zero/one
flags suffice for total execution; convergence assumptions are reserved for numerical bounds. -/
theorem writes_nodeProjectors {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hIndex : IsIndexLit M I)
    {τ : Tape K} {k fuel : ℕ} (A : Matrix (Fin k) (Fin k) (K × K)) (eps scale : K)
    {w sp c b t pp pm : ℕ × ℕ} {m : Mem K}
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) (hl : m.Live [w, sp, c, b, t, pp, pm])
    (hAP : Fp.Apart [w, sp, c, b, t, pp, pm]
      [2 * (k * k), 2, 4, 2 * (k * k), 2 * (k * k), 2 * (k * k), 2 * (k * k)])
    (hA : m.store.readBlock w.1 w.2 (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hSp : m.store.readBlock sp.1 sp.2 2 = some [eps, scale])
    (hc : m.store.readBlock c.1 c.2 4 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1)])
    (hb : b.2 + 2 * (k * k) ≤ m.store.len b.1)
    (ht : t.2 + 2 * (k * k) ≤ m.store.len t.1)
    (hp : pp.2 + 2 * (k * k) ≤ m.store.len pp.1)
    (hm : pm.2 + 2 * (k * k) ≤ m.store.len pm.1) :
    Writes .total I τ nodeProjectors.body (Env.frame [k, fuel] [w, sp, c, b, t, pp, pm])
      (Fp.blocks [b, t, pp, pm]
        [2 * (k * k), 2 * (k * k), 2 * (k * k), 2 * (k * k)])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [pp, pm] [2 * (k * k), 2 * (k * k)] =
        some [(EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).hermScale
            ((M.toFloatMachine dec mm qr unif normal).hermShift
              (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal) eps scale fuel A)
              (M.neg (M.lit 1))) (M.lit 2)),
          (EntryCodec.pair K).packFinMatrix
            ((M.toFloatMachine dec mm qr unif normal).hermScale
              ((M.toFloatMachine dec mm qr unif normal).negMat
                ((M.toFloatMachine dec mm qr unif normal).hermShift
                  (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal) eps scale fuel A)
                  (M.lit 1))) (M.lit 2))]) m := by
  have hLive : w.1 < m.store.length ∧ sp.1 < m.store.length ∧ c.1 < m.store.length ∧
      b.1 < m.store.length ∧ t.1 < m.store.length ∧ pp.1 < m.store.length ∧
      pm.1 < m.store.length := by simpa [Mem.Live] using hl
  rcases hLive with ⟨hlw, hlsp, hlc, hlb, hlt, hlpp, hlpm⟩
  have hs := Sign.writes_program dec mm qr unif normal (cap := fuel) (τ := τ)
    hS hC hMM hIndex A eps scale h01 (by room) (apart_sign hAP) hA hSp hb
  refine (writes_frame rfl rfl (by room) hs).seq_le (by fp_sub) fun μ hfr hsign => ?_
  have hcb : Fp.Disj (Store.inBlock b.1 b.2 (2 * (k * k))) (Store.inBlock c.1 c.2 4) := by
    simpa using (hAP.disj_getD (i := 3) (j := 2) (by simp) (by simp) (by simp))
  have hc' := hfr.keep (Store.readsOnly_readBlock c.1 c.2 4 _) hcb hc
  have htail := writes_projectorTail (w := w) (sp := sp) (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (fuel := fuel) (τ := τ) hS _
    (by room) hAP.2.2 hsign.2 hc'
    (by rw [hfr.len_eq]; exact ht) (by rw [hfr.len_eq]; exact hp)
    (by rw [hfr.len_eq]; exact hm)
  exact htail.mono (by fp_sub) fun _ _ h => ⟨h.1.trans hsign.1, h.2⟩

end NLAlib.SpectralBisection
