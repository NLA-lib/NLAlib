/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.OpsHermitian

/-!
# Negated Hermitian shifts as one shared matrix transition

Matrix-sign steps and negative spectral projectors use the same two explicit scalar
subprograms: Hermitian shift followed by in-place negation. Their shared functional theorem
returns the existing mathematical machine's exact word matrix.

## Main results

* `NLAlib.Ops.Hermitian.writes_shiftNegate_packed`: actual packed negated-shift output.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op]
  {M : Machine K} {dec : K → ℝ} {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- The two explicit matrix subprograms return the actual machine negation of its rounded
Hermitian shift. Disjoint input/output word regions may belong to the same arena. -/
theorem writes_shiftNegate_packed {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K)) (d : K)
    {x c y : ℕ × ℕ} {μ : Mem K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : μ.store.readBlock x.1 x.2 (2 * (n * n)) = some ((EntryCodec.pair K).packFinMatrix A))
    (hc : μ.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ μ.store.len y.1) (hl : μ.Live [x, c, y]) :
    Writes .total I τ (shiftNegate (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock y.1 y.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).negMat
            ((M.toFloatMachine dec mm qr unif normal).hermShift A d)))) μ := by
  have hs := writes_shift_packed (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hI A d hxy hcy hX hc hY hl
  refine hs.seq_le le_rfl fun ν hfr hp => ?_
  have hy' : y.1 < ν.store.length := by rw [hfr.length_eq]; exact hl y (by simp)
  have hl' : ν.Live [y, y] := by simp [Mem.Live, hy']
  have hY' : y.2 + 2 * (n * n) ≤ ν.store.len y.1 := by rw [hfr.len_eq]; exact hY
  have hn := writes_negate_packed (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) (τ := τ) hI
    ((M.toFloatMachine dec mm qr unif normal).hermShift A d) (Or.inr rfl) hp.2 hY' hl'
  exact (writes_frame rfl rfl hl' hn).mono le_rfl fun _ _ h => ⟨h.1.trans hp.1, h.2⟩

end NLAlib.Ops.Hermitian
