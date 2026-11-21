/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Deflation.Execution
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# Randomized deflation as a routine with declared draws

`NLAlib.Deflation.deflateRoutine` is `[n, rank] (P : read 2 n²) → (Q : write 2 n rank)`, drawing
`2 n²` tape positions: it reads a packed square matrix, draws a square sample matrix from the
Gaussian stream, multiplies, factors, and writes the first `rank` columns of the orthogonal
factor. Numerical accuracy and the law of the tape are separate assumptions about the result.

## Main definitions

* `NLAlib.Deflation.deflateRoutine`, `NLAlib.Deflation.deflateSpec`.

## Main results

* `NLAlib.Deflation.deflateRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.Deflation

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has SampleOp Op] {M : Machine K} {I : Interp Op Tst K}

/-- Randomized deflation: `[n, rank] (P : read 2 n²) → (Q : write 2 n rank)`, drawing `2 n²`
tape positions. -/
def deflateRoutine : Routine Op Tst :=
  routine% [n, r] (P : 2 * (n * n)) → (Q : 2 * (n * r))
    draws 2 * (n * n) := program

/-- For a requested rank at most the order, the written block packs the first `rank` columns of
the orthogonal factor of the product of the matrix that the block read packs with the sample
matrix packed in the first `2 n²` words drawn from the Gaussian stream. -/
def deflateSpec (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) : Routine.Spec K :=
  spec% [n, rank] tape ω (pw) → (zw) requires rank ≤ n ensures
    ∃ hrank : rank ≤ n, zw = (EntryCodec.pair K).packFinMatrix
      ((qr (mm ((EntryCodec.pair K).matrix n n pw)
        (sampleMatrix n 0 ω))).1.submatrix id (Fin.castLE hrank))

/-- The sample matrix of a tape seen from a position. -/
theorem sampleMatrix_shift (n pos : ℕ) (tape : Tape K) :
    sampleMatrix n 0 (tape.shift pos) = sampleMatrix n pos tape := by
  simp only [sampleMatrix, Tape.window_shift, Nat.add_zero]

/-- Randomized deflation meets its specification for every functional interpretation of the
scalar, sampling, multiplication and QR operations, at every order and every rank at most the
order. There is no successful-run or numerical-accuracy premise. -/
theorem deflateRoutine_meets (hS : IsScalar M I) (hSample : IsSample I)
    {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I) :
    (deflateRoutine (Op := Op) (Tst := Tst)).Meets I (deflateSpec mm qr) := by
  routine_intro [n, rank] (p, z) reads (pw)
  have hrank : rank ≤ n := hpre
  have hlen' : pw.length = n * n * (EntryCodec.pair K).width := by
    have h := Store.length_of_readBlock hpw
    simpa only [EntryCodec.pair, Nat.mul_comm] using h
  have hP : m.store.readBlock p.1 p.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix ((EntryCodec.pair K).matrix n n pw)) := by
    rw [(EntryCodec.pair K).packFinMatrix_matrix _ _ _ hlen']
    exact hpw
  set P := (EntryCodec.pair K).matrix n n pw
  have hw : Writes .total I τ (program (Op := Op) (Tst := Tst))
      (Env.frame [n, rank] [p, z]) (Store.inBlock z.1 z.2 (2 * (n * rank)))
      (fun m' => m'.pos = m.pos + 2 * (n * n) ∧
        m'.store.readBlock z.1 z.2 (2 * (n * rank)) =
          some ((EntryCodec.pair K).packFinMatrix
            ((qr (mm P (sampleMatrix n m.pos τ))).1.submatrix id (Fin.castLE hrank)))) m := by
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
        exact hroom
      refine (writes_frame rfl rfl (by simp [Mem.Live, hs]; omega)
        (apply_writes hS hSample hMM hQR P hrank (by simp [Mem.Live, hs]; omega)
          (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
          hP₀ (by simpa using hGlen.ge) (by simpa using hYlen.ge)
          (by simpa using hQlen.ge) (by simpa using hRlen.ge) hz₀)).mono ?_ ?_
      · exact sup_le (Fp.inBlock_le_sup_above (by dsimp only; omega))
          (sup_le (Fp.inBlock_le_sup_above (by dsimp only; omega))
            (sup_le (sup_le (Fp.inBlock_le_sup_above (by dsimp only; omega))
              (Fp.inBlock_le_sup_above (by dsimp only; omega))) le_sup_left))
      · exact fun _ _ h => h
  refine hw.mono (by fp_sub) ?_
  rintro μ' - ⟨hpos, hread⟩
  routine_exit
  exact ⟨hrank, by rw [sampleMatrix_shift]⟩

end NLAlib.Deflation
