/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.GolubKahan.Band.Certification
public import NLAlib.LowRank.BlockKrylov.Factored

/-!
# The sample window of the block Golub–Kahan program

The program `NLAlib.Krylov.GolubKahan.Band.program` draws its $n \times b$ start block
$\mathbf{\Omega}$ from one window of $nb$ words of a stream, column by column. This file names
the block decoded from that window, places a given matrix on the tape, and shows that the two
are inverse: on the tape of $\mathbf{X}$ the start block is $\mathbf{X}$, and the stored factors
of a certified run multiply to $\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)$ (`NLAlib.rbki`). No
law of the tape is assumed here; laws are hypotheses of
`NLAlib/LowRank/BlockKrylov/Probability.lean`.

## Main definitions

* `NLAlib.BlockKrylov.sampleMatrix`: the start block decoded from the window of a tape.
* `NLAlib.BlockKrylov.packedSampleTape`: the tape that carries a given start block.

## Main results

* `NLAlib.BlockKrylov.sampleMatrix_packedSampleTape`,
  `NLAlib.BlockKrylov.decodeMatrix_window_packedSampleTape`: the window of the tape of a matrix
  decodes to that matrix.
* `NLAlib.BlockKrylov.storedProduct_eq_rbki`,
  `NLAlib.BlockKrylov.storedProduct_eq_rbki_of_packedSampleTape`: the stored factors of a
  certified run are randomized block Krylov iteration at the start block of the tape.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.BlockKrylov

open Ops Krylov.GolubKahan.Band Krylov.GolubKahan.Band.Certification

section Tape

variable {K : Type} [Inhabited K]

/-- The $n \times b$ start block drawn by the program: the window of $nb$ words of the stream at
the position zero, read column by column with the scalar codec and no transformation of the
words. -/
def sampleMatrix (stream n b : ℕ) (tape : Tape K) : Matrix (Fin n) (Fin b) K :=
  (EntryCodec.scalar K).matrix n b (tape.window stream 0 (n * b))

/-- The tape that carries the matrix $\mathbf{X}$ as start block: its entries, column by column,
at the first $nb$ positions of the named stream, and the default word elsewhere. It is a
constructor of tapes for the coupling with a random matrix, not an initialization of a buffer. -/
def packedSampleTape {n b : ℕ} (stream : ℕ) (X : Matrix (Fin n) (Fin b) K) : Tape K :=
  Tape.ofStream stream ((EntryCodec.scalar K).packFinMatrix X)

/-- The start block drawn from the tape of $\mathbf{X}$ is $\mathbf{X}$, for every matrix,
including matrices with no rows or no columns. -/
theorem sampleMatrix_packedSampleTape {n b : ℕ} (stream : ℕ) (X : Matrix (Fin n) (Fin b) K) :
    sampleMatrix stream n b (packedSampleTape stream X) = X := by
  simp only [sampleMatrix, packedSampleTape]
  have hlen : n * b = ((EntryCodec.scalar K).packFinMatrix X).length := by
    simp [EntryCodec.scalar, Nat.mul_comm]
  rw [hlen, Tape.window_ofStream, EntryCodec.matrix_packFinMatrix]

end Tape

/-- The window of $nb$ words of the tape of a real matrix $\mathbf{X}$ decodes, with the identity
decoding of real words, to $\mathbf{X}$. This is the start block in the postcondition of the
program. -/
theorem decodeMatrix_window_packedSampleTape {n b : ℕ} (stream : ℕ)
    (X : Matrix (Fin n) (Fin b) ℝ) :
    decodeMatrix id n b ((packedSampleTape stream X).window stream 0 (n * b)) = X := by
  have h := sampleMatrix_packedSampleTape stream X
  rw [sampleMatrix] at h
  rw [decodeMatrix, h]
  exact Matrix.map_id X

/-- The stored factors of a certified run are randomized block Krylov iteration: if a final
memory satisfies the postcondition of a run for $\mathbf{A}$ at the sizes $(m, n, b, q)$ on the
tape `τ`, and $\mathbf{\Omega}$ is the $n \times b$ block decoded from the window of the tape,
then the stored product is
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} =
\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\,,$$
for every matrix, every tape and every exact orthogonalization scheme. -/
theorem storedProduct_eq_rbki {stream : ℕ} {d : Fin 4 → ℕ}
    {A : Matrix (Fin (d 0)) (Fin (d 1)) ℝ} {τ : Tape ℝ} {μ : Mem ℝ} (h : Good stream d A τ μ) :
    storedProduct (d 0) (d 1) (d 2) (d 3) μ =
      rbki A (decodeMatrix id (d 1) (d 2) (τ.window stream 0 (d 1 * d 2))) (d 3) := by
  rw [rbki_def]
  exact h.storedProduct_eq_rsvd

/-- On the tape of a start block $\mathbf{X}$ the stored factors of a certified run are
randomized block Krylov iteration from $\mathbf{X}$: if a final memory satisfies the
postcondition of a run for $\mathbf{A}$ at the sizes $(m, n, b, q)$ on the tape that carries the
real $n \times b$ matrix $\mathbf{X}$, then the stored product is
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} =
\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\,.$$ -/
theorem storedProduct_eq_rbki_of_packedSampleTape {stream : ℕ} {d : Fin 4 → ℕ}
    {A : Matrix (Fin (d 0)) (Fin (d 1)) ℝ} {X : Matrix (Fin (d 1)) (Fin (d 2)) ℝ} {μ : Mem ℝ}
    (h : Good stream d A (packedSampleTape stream X) μ) :
    storedProduct (d 0) (d 1) (d 2) (d 3) μ = rbki A X (d 3) := by
  rw [storedProduct_eq_rbki h, decodeMatrix_window_packedSampleTape]

end NLAlib.BlockKrylov
