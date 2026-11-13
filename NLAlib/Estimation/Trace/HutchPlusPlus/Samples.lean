/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryLayout
public import NLAlib.Ops.Stream

/-!
# The actual adjacent sample windows of Hutch++

A sketch matrix and a probe matrix occupy adjacent column-major windows on one stream. Their
finite word packing specifies the consumed tape explicitly; unused positions and streams carry
the default value. Gaussian laws and independence are separate hypotheses, not properties of
an arbitrary supplied matrix or unused tape position.

## Main results

* `NLAlib.HutchPlusPlus.sampleMatrices`: the actual sketch and probe windows from position zero.
* `NLAlib.HutchPlusPlus.packedSampleTape`: place the two matrices on the sampled stream.
* `NLAlib.HutchPlusPlus.sampleMatrices_packedSampleTape`: exact sample coupling.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {K : Type} [Inhabited K]

/-- The actual sketch and probe matrices drawn in that order, with no transformation of
sample words. Both matrices use the library's scalar column-major codec. -/
def sampleMatrices (stream n k ell : ℕ) (tape : Tape K) :
    Matrix (Fin n) (Fin k) K × Matrix (Fin n) (Fin ell) K :=
  ((EntryCodec.scalar K).matrix n k (tape.window stream 0 (n * k)),
    (EntryCodec.scalar K).matrix n ell (tape.window stream (n * k) (n * ell)))

/-- Pack two supplied matrices on adjacent windows of the named stream. This is a tape
constructor for mathematical sample coupling, not an initialization of any program buffer. -/
def packedSampleTape {n k ell : ℕ} (stream : ℕ) (S : Matrix (Fin n) (Fin k) K)
    (G : Matrix (Fin n) (Fin ell) K) : Tape K :=
  Tape.ofStream stream
    ((EntryCodec.scalar K).packFinMatrix S ++ (EntryCodec.scalar K).packFinMatrix G)

/-- The initial draw returns exactly the supplied sketch matrix. -/
theorem sampleMatrices_packedSampleTape_fst {n k ell : ℕ} (stream : ℕ)
    (S : Matrix (Fin n) (Fin k) K) (G : Matrix (Fin n) (Fin ell) K) :
    (sampleMatrices stream n k ell (packedSampleTape stream S G)).1 = S := by
  simp only [sampleMatrices, packedSampleTape]
  have hlen : n * k = ((EntryCodec.scalar K).packFinMatrix S).length := by
    simp [EntryCodec.scalar, Nat.mul_comm]
  rw [hlen, Tape.window_ofStream_append_left, EntryCodec.matrix_packFinMatrix]

/-- The second draw begins at the exact end of the sketch and returns the probe matrix. -/
theorem sampleMatrices_packedSampleTape_snd {n k ell : ℕ} (stream : ℕ)
    (S : Matrix (Fin n) (Fin k) K) (G : Matrix (Fin n) (Fin ell) K) :
    (sampleMatrices stream n k ell (packedSampleTape stream S G)).2 = G := by
  simp only [sampleMatrices, packedSampleTape]
  have hS : n * k = ((EntryCodec.scalar K).packFinMatrix S).length := by
    simp [EntryCodec.scalar, Nat.mul_comm]
  have hG : n * ell = ((EntryCodec.scalar K).packFinMatrix G).length := by
    simp [EntryCodec.scalar, Nat.mul_comm]
  rw [hS, hG, Tape.window_ofStream_append_right, EntryCodec.matrix_packFinMatrix]

/-- Both actual sample windows coincide with the supplied mathematical matrices. -/
theorem sampleMatrices_packedSampleTape {n k ell : ℕ} (stream : ℕ)
    (S : Matrix (Fin n) (Fin k) K) (G : Matrix (Fin n) (Fin ell) K) :
    sampleMatrices stream n k ell (packedSampleTape stream S G) = (S, G) :=
  Prod.ext (sampleMatrices_packedSampleTape_fst stream S G)
    (sampleMatrices_packedSampleTape_snd stream S G)

end NLAlib.HutchPlusPlus
