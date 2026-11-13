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
* `NLAlib.Deflation.writes_apply` computes deflation in caller-owned workspace.
* `NLAlib.Deflation.writes_program` computes deflation with scoped scratch.
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

/-- Sample, multiply, factor and select columns using explicit caller-owned workspace.
Every input is read before its output is written. Scratch and output geometry is explicit;
the Gaussian distribution is unnecessary for this total word-level computation. -/
theorem writes_apply (hS : IsScalar M I) (hSample : IsSample I)
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
    Writes .total I tape (apply (Op := Op) (Tst := Tst)).body
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
  refine (writes_frame rfl rfl (by simp [Mem.Live]; omega)
    (writes_sampleVector hSample Stream.gauss hG)).seq ?_
  intro m₁ hf₁ ⟨hDraw, hpos₁⟩
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
  refine (writes_frame rfl rfl (by
    simp [Mem.Live, hf₃.length_eq, hf₂.length_eq, hf₁.length_eq]; omega)
    (PairMatrix.writes_copy hS (by
      simp [Mem.Live, hf₃.length_eq, hf₂.length_eq, hf₁.length_eq]; omega)
      (Or.inl (Fp.disj_inBlock_of_ne hqz)) hread
      (by rw [hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; exact hZ))).mono le_rfl ?_
  exact fun _ _ h => ⟨h.1.trans (hpos₃.trans (hpos₂.trans hpos₁)), h.2⟩

/-- The standalone program terminates and returns its actual sampled QR columns. All
four square scratch buffers are scoped and freed; only the output block is modified.
There is no successful-run, rank or numerical-accuracy premise. -/
theorem writes_program (hS : IsScalar M I) (hSample : IsSample I)
    {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    {tape : Tape K} {m : Mem K} {n rank : ℕ} {p z : ℕ × ℕ}
    (P : Matrix (Fin n) (Fin n) (K × K)) (hrank : rank ≤ n)
    (hl : m.Live [p, z])
    (hP : m.store.readBlock p.1 p.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix P))
    (hZ : z.2 + 2 * (n * rank) ≤ m.store.len z.1) :
    Writes .total I tape (program (Op := Op) (Tst := Tst)).body
      (Env.frame [n, rank] [p, z]) (Store.inBlock z.1 z.2 (2 * (n * rank)))
      (fun m' => m'.pos = m.pos + 2 * (n * n) ∧
        m'.store.readBlock z.1 z.2 (2 * (n * rank)) =
          some ((EntryCodec.pair K).packFinMatrix
            ((qr (mm P (sampleMatrix n m.pos tape))).1.submatrix id (Fin.castLE hrank)))) m := by
  obtain ⟨hp, hz⟩ : p.1 < m.store.length ∧ z.1 < m.store.length := by
    simpa [Mem.Live] using hl
  refine writes_allocs_readBlock_at (ρ := Env.frame [n, rank] [p, z]) (m := m)
    (lens := List.replicate 4 (.const 2 * (.var 0 * .var 0)))
    (ns := List.replicate 4 (2 * (n * n))) rfl hz fun s hs hlen hBelow => ?_
  have hGlen := hlen 0 (by simp)
  have hYlen := hlen 1 (by simp)
  have hQlen := hlen 2 (by simp)
  have hRlen := hlen 3 (by simp)
  simp only [List.length_replicate, List.getElem_replicate, Nat.add_zero] at *
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    Nat.add_zero] at ⊢
  have hP₀ := (hBelow.readBlock hp p.2 (2 * (n * n))).trans hP
  have hz₀ : z.2 + 2 * (n * rank) ≤ s.len z.1 := by
    rw [(hBelow z.1 hz).1]
    exact hZ
  refine (writes_frame rfl rfl (by simp [Mem.Live, hs]; omega)
    (writes_apply hS hSample hMM hQR P hrank (by simp [Mem.Live, hs]; omega)
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
      hP₀ (by simpa using hGlen.ge) (by simpa using hYlen.ge)
      (by simpa using hQlen.ge) (by simpa using hRlen.ge) hz₀)).mono ?_ ?_
  · exact sup_le (Fp.inBlock_le_sup_above (by dsimp only; omega))
      (sup_le (Fp.inBlock_le_sup_above (by dsimp only; omega))
        (sup_le (sup_le (Fp.inBlock_le_sup_above (by dsimp only; omega))
          (Fp.inBlock_le_sup_above (by dsimp only; omega))) le_sup_left))
  · exact fun _ _ h => h

end NLAlib.Deflation
