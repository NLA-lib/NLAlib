/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Node
public import NLAlib.Matrix.FinitePrecision.OpsMatrix
public import NLAlib.Matrix.FinitePrecision.OpsHermitian
public import NLAlib.Ops.Logic.MatrixPacked
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.Step

/-!
# Total stored-output refinement of a bisection compression

The actual allocated compression program transposes the supplied basis, performs two matrix
products, takes the rounded Hermitian average, and subtracts the stored shift. The proof
composes packed matrix contracts and one shared scratch-cleanup rule. Scalar rounding accuracy
is separate from this exact functional statement on actual machine words.

## Main results

* `NLAlib.SpectralBisection.writes_compress`: the stored compression is the existing
  mathematical machine's nested product, Hermitian average and shift.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Compression succeeds on the actual readable basis, matrix and scalar words, with writable
output capacity disjoint from the shift cell. Source matrices may overlap the output because
all source reads finish before the final write. No numerical model or successful-run premise
is assumed; the four scratch allocations are discharged together. -/
theorem writes_compress {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
    {M : Machine K} (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K) {I : Interp Op Tst K}
    (hS : IsScalar M I) (hmm : IsMatrixMul (EntryCodec.pair K) mm I)
    {τ : Tape K} {μ : Mem K} {k r : ℕ} {q a two sigma y : ℕ × ℕ}
    (Q : Matrix (Fin k) (Fin r) (K × K)) (A : Matrix (Fin k) (Fin k) (K × K)) (t s : K)
    (hl : μ.Live [q, a, two, sigma, y])
    (hQ : μ.store.readBlock q.1 q.2 (2 * (k * r)) = some ((EntryCodec.pair K).packFinMatrix Q))
    (hA : μ.store.readBlock a.1 a.2 (2 * (k * k)) = some ((EntryCodec.pair K).packFinMatrix A))
    (ht : μ.store.get two.1 two.2 = some t) (hs : μ.store.get sigma.1 sigma.2 = some s)
    (hy : y.2 + 2 * (r * r) ≤ μ.store.len y.1)
    (hsy : Fp.Disj (Store.inBlock sigma.1 sigma.2 1) (Store.inBlock y.1 y.2 (2 * (r * r)))) :
    Writes .total I τ (compress (Op := Op) (Tst := Tst)).body
      (Env.frame [k, r] [q, a, two, sigma, y]) (Store.inBlock y.1 y.2 (2 * (r * r)))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock y.1 y.2 (2 * (r * r)) =
        some ((EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).hermShift
            ((M.toFloatMachine dec mm qr unif normal).hermAvg
              (mm (mm ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat Q) A) Q)
              t) s))) μ := by
  have hQcall : μ.store.readBlock q.1 q.2 (r * k * 2) =
      some ((EntryCodec.pair K).packFinMatrix Q) := by simpa only [Nat.mul_comm] using hQ
  have hAcall : μ.store.readBlock a.1 a.2 (k * k * 2) =
      some ((EntryCodec.pair K).packFinMatrix A) := by simpa only [Nat.mul_comm] using hA
  apply writes_allocs_readBlock
    (lens := [.const 2 * (.var 0 * .var 1), .const 2 * (.var 1 * .var 0),
      .const 2 * (.var 1 * .var 1), .const 2 * (.var 1 * .var 1)])
    (ns := [2 * (k * r), 2 * (r * k), 2 * (r * r), 2 * (r * r)]) rfl (hl y (by simp))
  intro store hlength hlens hBelow
  have hq : q.1 < μ.store.length := hl q (by simp)
  have ha : a.1 < μ.store.length := hl a (by simp)
  have htwo : two.1 < μ.store.length := hl two (by simp)
  have hsigma : sigma.1 < μ.store.length := hl sigma (by simp)
  have hout : y.1 < μ.store.length := hl y (by simp)
  have hlen0 : store.len μ.store.length = 2 * (k * r) := by simpa using hlens 0 (by simp)
  have hlen1 : store.len (μ.store.length + 1) = 2 * (r * k) := by simpa using hlens 1 (by simp)
  have hlen2 : store.len (μ.store.length + 2) = 2 * (r * r) := by simpa using hlens 2 (by simp)
  have hlen3 : store.len (μ.store.length + 3) = 2 * (r * r) := by simpa using hlens 3 (by simp)
  refine (writes_frame rfl rfl ?_ (PairMatrix.writes_conjTranspose_packed
    (dec := dec) (mm := mm) (qr := qr) (unif := unif) (normal := normal) hS Q
    (by disjoint) (by kept) (by room) (by room))).seq_le (by fp_sub) ?_
  · room
  intro μ₁ hfr₁ ⟨hp₁, hQh⟩
  have hQhcall : μ₁.store.readBlock μ.store.length 0 (k * r * 2) =
      some ((EntryCodec.pair K).packFinMatrix
        ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat Q)) := by
    simpa only [Nat.mul_comm, Nat.add_zero] using hQh
  refine (writes_matrixMul_packFinMatrix (EntryCodec.pair K) mm hmm
    ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat Q) A rfl rfl rfl
    (by room) (by kept [Nat.mul_comm]) (by kept [Nat.mul_comm]) (by room [Nat.mul_comm])).seq_le
    (by fp_sub) ?_
  intro μ₂ hfr₂ ⟨hp₂, hC₁⟩
  refine (writes_matrixMul_packFinMatrix (EntryCodec.pair K) mm hmm
    (mm ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat Q) A) Q rfl rfl rfl
    (by room) (by kept [Nat.mul_comm]) (by kept [Nat.mul_comm]) (by room [Nat.mul_comm])).seq_le
    (by fp_sub) ?_
  intro μ₃ hfr₃ ⟨hp₃, hC₂⟩
  have hC₂packed : μ₃.store.readBlock (μ.store.length + 2) 0 (2 * (r * r)) =
      some ((EntryCodec.pair K).packFinMatrix
        (mm (mm ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat Q) A) Q)) := by
    simpa only [Nat.mul_comm, List.length_cons, List.length_nil] using hC₂
  refine (writes_frame rfl rfl ?_ (Hermitian.writes_average_packed
    (dec := dec) (mm := mm) (qr := qr) (unif := unif) (normal := normal) hS
    (mm (mm ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat Q) A) Q) t
    (by disjoint) (by disjoint) (by kept) (by kept) (by room) (by room))).seq_le
    (by fp_sub) ?_
  · room
  intro μ₄ hfr₄ ⟨hp₄, hC₃⟩
  refine (writes_frame rfl rfl ?_ (Hermitian.writes_shift_packed
    (dec := dec) (mm := mm) (qr := qr) (unif := unif) (normal := normal) hS
    ((M.toFloatMachine dec mm qr unif normal).hermAvg
      (mm (mm ((M.toFloatMachine dec mm qr unif normal).conjTransposeMat Q) A) Q) t) s
    (by disjoint) hsy (by kept) (by kept) (by room) (by room))).mono le_sup_left ?_
  · room
  intro μ₅ _ ⟨hp₅, hC⟩
  exact ⟨hp₅.trans (hp₄.trans (hp₃.trans (hp₂.trans hp₁))), hC⟩

end NLAlib.SpectralBisection
