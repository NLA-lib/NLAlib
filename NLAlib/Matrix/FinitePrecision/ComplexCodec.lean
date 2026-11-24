/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.StoredMatrix
public import NLAlib.Ops.RoutineProblem

/-!
# Complex numbers and complex matrices as blocks of real words

The operand of a routine that holds a complex number is the block of its real and imaginary
parts; one that holds a square complex matrix is the block `NLAlib.matrixWords`. Both are
bijective at their length, so a problem may take the complex value as its input.

## Main definitions

* `NLAlib.Ops.Codec.complex`: a complex number as two real words.
* `NLAlib.Ops.Codec.complexMatrix`: a square complex matrix as its interleaved words.
-/

@[expose] public section

namespace NLAlib.Ops.Codec

/-- A complex number: its real part, then its imaginary part. -/
def complex : Codec ℝ ℂ where
  len := 2
  encode z := [z.re, z.im]
  decode ws := ⟨vec ws 0, vec ws 1⟩
  length_encode _ := rfl
  decode_encode _ := rfl
  encode_decode ws h := by
    rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
    · cases h
    · cases h
    · rfl
    · simp at h

/-- A square complex matrix of order `N`: its interleaved words, column by column. -/
noncomputable def complexMatrix (N : ℕ) : Codec ℝ (Matrix (Fin N) (Fin N) ℂ) where
  len := 2 * (N * N)
  encode A := matrixWords A
  decode ws := matrixOfWords N ws
  length_encode A := length_matrixWords A
  decode_encode A := matrixOfWords_matrixWords A
  encode_decode ws h := matrixWords_matrixOfWords ws h

end NLAlib.Ops.Codec
