/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Deflation.Alg
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.MatrixPacked
public import NLAlib.Ops.Blas.MatrixCorrect
public import NLAlib.Matrix.FinitePrecision.Machine

/-!
# Total execution of standalone randomized deflation

Functional primitive contracts identify the actual sample words, product and QR factors.
No numerical rank, conditioning or successful-run premise is needed. The requested column
count is bounded by the matrix dimension.

## Main results

* `NLAlib.Deflation.sampleMatrix` decodes precisely the consumed sample words.
* `NLAlib.Deflation.apply_writes` computes deflation in the routine's scratch buffers.
-/

@[expose] public section

namespace NLAlib.Deflation

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has SampleOp Op] {M : Machine K} {I : Interp Op Tst K}

/-- The square matrix decoded from the exact contiguous Gaussian-stream words used by
the program. Distribution and independence are separate assumptions on the tape law. -/
def sampleMatrix (n pos : ℕ) (tape : Tape K) : Matrix (Fin n) (Fin n) (K × K) :=
  (EntryCodec.pair K).matrix n n (tape.window Stream.gauss pos (2 * (n * n)))

/-- Sample, multiply, factor and select columns in explicit workspace: a fragment of
`NLAlib.Deflation.deflateRoutine`, run on the four square scratch buffers that the routine
allocates. Every input is read before its output is written. Scratch and output geometry is
explicit; the Gaussian distribution is unnecessary for this total word-level computation. -/
theorem apply_writes (hS : IsScalar M I) (hSample : IsSample I)
    {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    {tape : Tape K} {m : Mem K} {n rank : ℕ} {p g y q r z : ℕ × ℕ}
    (P : Matrix (Fin n) (Fin n) (K × K)) (hrank : rank ≤ n)
    (hl : m.Live [p, g, y, q, r, z]) (hpg : p.1 ≠ g.1)
    (hqr : q.1 ≠ r.1) (hqz : q.1 ≠ z.1)
    (hP : m.store.readBlock p.1 p.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix P))
    (hG : g.2 + 2 * (n * n) ≤ m.store.len g.1)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1)
    (hQ : q.2 + 2 * (n * n) ≤ m.store.len q.1)
    (hR : r.2 + 2 * (n * n) ≤ m.store.len r.1)
    (hZ : z.2 + 2 * (n * rank) ≤ m.store.len z.1) :
    Writes .total I tape (apply (Op := Op) (Tst := Tst))
      (Env.frame [n, rank] [p, g, y, q, r, z])
      (Store.inBlock g.1 g.2 (2 * (n * n)) ⊔
        (Store.inBlock y.1 y.2 (2 * (n * n)) ⊔
          ((Store.inBlock q.1 q.2 (2 * (n * n)) ⊔
            Store.inBlock r.1 r.2 (2 * (n * n))) ⊔
              Store.inBlock z.1 z.2 (2 * (n * rank)))))
      (fun m' => m'.pos = m.pos + 2 * (n * n) ∧
        m'.store.readBlock z.1 z.2 (2 * (n * rank)) =
          some ((EntryCodec.pair K).packFinMatrix
            ((qr (mm P (sampleMatrix n m.pos tape))).1.submatrix id (Fin.castLE hrank)))) m := by
  let C := EntryCodec.pair K
  let G := sampleMatrix n m.pos tape
  obtain ⟨hp, hg, hy, hq, hr, hz⟩ : p.1 < m.store.length ∧ g.1 < m.store.length ∧
      y.1 < m.store.length ∧ q.1 < m.store.length ∧ r.1 < m.store.length ∧
      z.1 < m.store.length := by simpa [Mem.Live] using hl
  have hroomG : m.Room [g] [2 * (n * n)] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hG
  call (sampleRoutine_meets hSample Stream.gauss) [2 * (n * n)] (g) as m₁ hf₁ hpos₁ (ws) hpost
  have hf₁ : m.store.EqOff (Store.inBlock g.1 g.2 (2 * (n * n))) m₁.store :=
    hf₁.mono (by fp_sub)
  have hDraw : m₁.store.readBlock g.1 g.2 (2 * (n * n)) =
      some (tape.window Stream.gauss m.pos (2 * (n * n))) := by
    have h : ws = (tape.shift m.pos).window Stream.gauss 0 (2 * (n * n)) := hpost
    rw [h, Tape.window_shift] at hws
    exact hws
  refine Writes.mono (F := Store.inBlock y.1 y.2 (2 * (n * n)) ⊔
    ((Store.inBlock q.1 q.2 (2 * (n * n)) ⊔ Store.inBlock r.1 r.2 (2 * (n * n))) ⊔
      Store.inBlock z.1 z.2 (2 * (n * rank)))) ?_ le_sup_right fun _ _ h => h
  have hlen : (tape.window Stream.gauss m.pos (2 * (n * n))).length = n * n * C.width := by
    simp [C, Tape.window, Nat.mul_comm]
  have hG₁ : m₁.store.readBlock g.1 g.2 (n * n * C.width) = some (C.packFinMatrix G) := by
    change m₁.store.readBlock g.1 g.2 (n * n * C.width) =
      some (C.packFinMatrix (C.matrix n n (tape.window Stream.gauss m.pos (2 * (n * n)))))
    rw [C.packFinMatrix_matrix _ _ _ hlen]
    simpa [C, Nat.mul_comm] using hDraw
  have hP₁ := hf₁.readBlock_of hP (by intro j hj hin; exact hpg hin.1)
  refine ((writes_matrixMul_packFinMatrix C mm hMM P G (x := p) (y := g) (z := y)
    (ρ := Env.frame [n, rank] [p, g, y, q, r, z])
    (ds := [.var 0, .var 0, .var 0])
    (ins := [⟨0, .var 2⟩, ⟨1, .var 3⟩]) (outs := [⟨2, .var 4⟩]) rfl rfl rfl
    (by simp [Mem.Live, hf₁.length_eq]; omega) (by simpa [C, Nat.mul_comm] using hP₁)
    hG₁ (by simpa [C, hf₁.len_eq, Nat.mul_comm] using hY)).mono
      (G := Store.inBlock y.1 y.2 (2 * (n * n)))
      (by simp [C, Nat.mul_comm]) (fun _ _ h => h)).seq ?_
  intro m₂ hf₂ ⟨hpos₂, hY₂⟩
  refine ((writes_matrixQR_packFinMatrix C qr hQR (mm P G) (x := y) (q := q) (z := r)
    (ρ := Env.frame [n, rank] [p, g, y, q, r, z])
    (ds := [.var 0, .var 0]) (ins := [⟨2, .var 4⟩])
    (outs := [⟨3, .var 5⟩, ⟨4, .var 6⟩]) rfl rfl rfl
    (by simp [Mem.Live, hf₂.length_eq, hf₁.length_eq]; omega) hY₂
    (Fp.disj_inBlock_of_ne hqr)
    (by simpa [C, hf₂.len_eq, hf₁.len_eq, Nat.mul_comm] using hQ)
    (by simpa [C, hf₂.len_eq, hf₁.len_eq, Nat.mul_comm] using hR)).mono
      (G := Store.inBlock q.1 q.2 (2 * (n * n)) ⊔ Store.inBlock r.1 r.2 (2 * (n * n)))
      (by simp [C, Nat.mul_comm]) (fun _ _ h => h)).seq ?_
  intro m₃ hf₃ ⟨hpos₃, hQ₃, _⟩
  have hread : m₃.store.readBlock q.1 q.2 (2 * (n * rank)) =
      some (C.packFinMatrix ((qr (mm P G)).1.submatrix id (Fin.castLE hrank))) := by
    simpa [C, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Store.readBlock_packFinMatrix_columns C hQ₃ hrank
  have hlive₃ : m₃.Live [q, z] := by
    simp [Mem.Live, hf₃.length_eq, hf₂.length_eq, hf₁.length_eq]; omega
  have hroom₃ : m₃.Room [z] [2 * (n * rank)] := by
    simp only [Mem.room_cons, Mem.room_nil, and_true]
    rw [hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]
    exact hZ
  have hdqz : Fp.Disj (Store.inBlock q.1 q.2 (2 * (n * rank)))
      (Store.inBlock z.1 z.2 (2 * (n * rank))) := Fp.disj_inBlock_of_ne hqz
  call (PairMatrix.copyRoutine_meets hS) [n, rank] (q, z) as m₄ hf₄ hpos₄ (zs) hpost
  obtain rfl : zs = _ := hpost
  exact ⟨hpos₄.trans (hpos₃.trans (hpos₂.trans hpos₁)), hzs⟩

end NLAlib.Deflation
