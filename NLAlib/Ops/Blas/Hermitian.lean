/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Blas.Map
public import NLAlib.Ops.Blas.HermitianEntry
public import NLAlib.Ops.Blas.Interval

/-!
# Hermitian matrix kernels over scalar operations

Complex entries occupy two consecutive scalar words, with the real part first and columns
stored consecutively. These implementations expose every scalar operation. They retain the
upper triangle and mirror it, so rounding cannot make the stored lower triangle independent
of the upper triangle. No operation performing an entire Hermitian transformation is assumed.

## Main results

* `NLAlib.Ops.Hermitian.mirror` copies the conjugate upper triangle to the lower triangle.
* `NLAlib.Ops.Hermitian.shift`, `scale`, and `average` implement Hermitian entrywise operations.
* `NLAlib.Ops.Hermitian.boxTest` checks every scalar word against stored lower and upper bounds.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Copy the strict upper triangle to the strict lower triangle, negating imaginary words.
The input and output are the same column-major interleaved square matrix. -/
def mirror : Stmt Op Tst :=
  .loop (.var 0) (.loop (.var 3)
    (.frame [] [⟨0, .var 1 + .const 2 * (.var 3 * .var 0 + .var 4)⟩,
      ⟨0, .var 1 + .const 2 * (.var 4 * .var 0 + .var 3)⟩] conjugatePair))

/-- Negate both words of every entry of an interleaved rectangular matrix.
Exact in-place operation is supported by scalar calls. -/
def negate : Stmt Op Tst :=
  .frame [.const 2 * (.var 0 * .var 1)] [⟨0, .var 2⟩, ⟨1, .var 3⟩]
    (unaryMap (Has.inj ScalarOp.neg))

/-- Negation writes the machine-negated words of the complete interleaved matrix.
The operands are live and either in distinct buffers or exactly coincident; output has room. -/
theorem negate_wp {K : Type} [Inhabited K] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {md : Mode} {τ : Tape K} {rows cols : ℕ} {x y : ℕ × ℕ}
    {m : Mem K} {xs : List K} (hxy : x.1 ≠ y.1 ∨ x = y)
    (hx : m.store.readBlock x.1 x.2 (2 * (rows * cols)) = some xs)
    (hy : y.2 + 2 * (rows * cols) ≤ m.store.len y.1) (hl : m.Live [x, y])
    {Q : Mem K → Prop} (hQ : Q (m.updBlock y (xs.map M.neg))) :
    Wp md I τ (negate (Op := Op) (Tst := Tst))
      (Env.frame [rows, cols] [x, y]) Q m :=
  wp_frame rfl rfl hl (unaryMap_wp (hI .neg) hxy hx hy hQ)

/-- Copy the strict upper triangle of an interleaved square matrix into another buffer. -/
def copyTriangle : Stmt Op Tst :=
  .loop (.var 0) (.loop (.var 3)
    (.frame [] [⟨0, .var 1 + .const 2 * (.var 3 * .var 0 + .var 4)⟩,
      ⟨1, .var 2 + .const 2 * (.var 3 * .var 0 + .var 4)⟩] copyPair))

/-- Apply an entry procedure to the strict upper triangle. Each entry procedure receives
its entry, its transposed entry, the scalar parameter, and its output word pair. -/
def triangle (entry : Stmt Op Tst) : Stmt Op Tst :=
  .loop (.var 0) (.loop (.var 4)
    (.frame [] [⟨0, .var 1 + .const 2 * (.var 4 * .var 0 + .var 5)⟩,
      ⟨0, .var 1 + .const 2 * (.var 5 * .var 0 + .var 4)⟩, ⟨1, .var 2⟩,
      ⟨2, .var 3 + .const 2 * (.var 4 * .var 0 + .var 5)⟩] entry))

/-- Apply a diagonal-entry procedure to a square matrix. The size-one inner loop permits
reuse of the same injective entry-region fill rule as the strict-upper loop. -/
def diagonal (entry : Stmt Op Tst) : Stmt Op Tst :=
  .loop (.var 0) (.loop (.const 1)
    (.frame [] [⟨0, .var 1 + .const 2 * (.var 4 * .var 0 + .var 4)⟩,
      ⟨1, .var 2⟩, ⟨2, .var 3 + .const 2 * (.var 4 * .var 0 + .var 4)⟩] entry))

/-- Transform the strict upper triangle, then transform the diagonal. Each procedure is
inlined as a first-order scalar program; neither is a new primitive operation. -/
def upper (offDiagonal diagonalEntry : Stmt Op Tst) : Stmt Op Tst :=
  .seq (triangle offDiagonal) (diagonal diagonalEntry)

/-- Adapt the pair copy to the entry/transpose/scalar interface; unused operands cause no
scalar operation and no hidden computation. -/
def copyEntry : Stmt Op Tst :=
  .frame [] [⟨0, .var 0⟩, ⟨3, .var 3⟩] copyPair

/-- Adapt pair scaling to the entry/transpose/scalar interface. -/
def scaleEntry : Stmt Op Tst :=
  .frame [] [⟨0, .var 0⟩, ⟨2, .var 2⟩, ⟨3, .var 3⟩] scalePair

/-- Write the upper triangle shifted by a stored real scalar. Diagonal imaginary words are
literal zero; lower words remain uninitialized until completion. -/
def shiftUpper : Stmt Op Tst := upper copyEntry shiftDiagonal

/-- Divide the upper triangle by a stored real scalar. Diagonal imaginary words are literal
zero; numerical accuracy requires a nonzero decoded divisor. -/
def scaleUpper : Stmt Op Tst := upper scaleEntry scaleDiagonal

/-- Write the upper triangle of the rounded Hermitian sum divided by a stored scalar.
Real words add transposed entries; imaginary words subtract them. -/
def averageUpper : Stmt Op Tst := upper averagePair averageDiagonal

/-- Complete an upper-triangle transformation by mirroring its computed output.
The scalar parameter uses one cell; the matrix output is the third operand. -/
def complete (upper : Stmt Op Tst) : Stmt Op Tst :=
  .seq upper (.frame [.var 0] [⟨2, .var 3⟩, ⟨2, .var 3⟩] mirror)

/-- Subtract a stored scalar times the identity and store the Hermitian completion. -/
def shift : Stmt Op Tst := complete shiftUpper

/-- Subtract the stored scalar times the identity, complete the Hermitian matrix, then negate
both words of every entry in place. Matrix-sign steps and negative projectors share this
explicit scalar subprogram. -/
def shiftNegate : Stmt Op Tst :=
  .seq shift (.frame [.var 0, .var 0] [⟨2, .var 3⟩, ⟨2, .var 3⟩] negate)

/-- Divide by a stored real scalar and store the Hermitian completion.
Numerical use requires a nonzero decoded divisor. -/
def scale : Stmt Op Tst := complete scaleUpper

/-- Add the conjugate transpose, divide by a stored real scalar, and store Hermitian completion.
Numerical use requires a nonzero decoded divisor and nonoverlapping input/output matrices. -/
def average : Stmt Op Tst := complete averageUpper

variable [Has CmpTst Tst]

/-- Write zero if every word of a rectangular interleaved matrix is between stored bounds,
and one otherwise. Every comparison is a counted primitive query on scalar words. -/
def boxTest : Stmt Op Tst :=
  .frame [.const 2 * (.var 0 * .var 1)]
    [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩] intervalScan

end NLAlib.Ops.Hermitian
