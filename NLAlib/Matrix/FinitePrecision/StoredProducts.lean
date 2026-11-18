/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Pair

/-!
# Products of stored complex matrices on strided views

A product $\mathbf{Z} = \mathbf{X}\mathbf{Y}$, or $\mathbf{Z} = \mathbf{X}^{\mathsf H}\mathbf{Y}$,
of complex matrices stored as word pairs in column-major order on strided views (leading dimensions
of their own), accumulated by rounded complex multiply–adds (`NLAlib.Ops.Pair.linearCombination`).
The output is a separate view. The error bounds are not in this file.

## Main definitions

* `NLAlib.matMulOn`: the strided product, with the left factor optionally conjugate-transposed.
-/

@[expose] public section

namespace NLAlib

open Ops

variable {O Q : Type} [Has ScalarOp O]

/-- **The product of two stored complex matrices on strided views**: for $c = 0$,
$\mathbf{Z} = \mathbf{X}\mathbf{Y}$ with $\mathbf{X}$ of size $m \times p$ (leading dimension
`ldx`), $\mathbf{Y}$ of size $p \times q$ (`ldy`) and $\mathbf{Z}$ of size $m \times q$ (`ldz`);
for $c \ge 1$, $\mathbf{Z} = \mathbf{X}^{\mathsf H}\mathbf{Y}$ with $\mathbf{X}$ of size
$p \times m$. Entry $(i, j)$ is accumulated from $0$ by $p$ rounded complex multiply–adds. The
interface is `[m, p, q, ldx, ldy, ldz, c] (X, Y) → (Z)`; the output is apart from the inputs, and
the four scratch pairs are scoped. -/
def matMulOn : Impl O Q := opsImpl% [m, p, q, ldx, ldy, ldz, c] (X, Y) → (Z) {
  let One ← alloc 2;
  let A ← alloc 2;
  let S ← alloc 2;
  let T ← alloc 2;
  let R ← alloc 2;
  call (Has.inj (ScalarOp.lit 1)) [] () → (One);
  call (Has.inj (ScalarOp.lit 0)) [] () → (One[1]);
  for j < q {
    for i < m {
      call (Has.inj (ScalarOp.lit 0)) [] () → (S);
      call (Has.inj (ScalarOp.lit 0)) [] () → (S[1]);
      for l < p {
        ifPos c {
          call (Has.inj ScalarOp.copy) [] (X[2 * (i * ldx + l)]) → (A);
          call (Has.inj ScalarOp.neg) [] (X[2 * (i * ldx + l) + 1]) → (A[1])
        };
        ifPos 1 - c {
          call (Has.inj ScalarOp.copy) [] (X[2 * (l * ldx + i)]) → (A);
          call (Has.inj ScalarOp.copy) [] (X[2 * (l * ldx + i) + 1]) → (A[1])
        };
        run Pair.linearCombination.body [] (A, One, Y[2 * (j * ldy + l)], S, T, R);
        call (Has.inj ScalarOp.copy) [] (R) → (S);
        call (Has.inj ScalarOp.copy) [] (R[1]) → (S[1])
      };
      call (Has.inj ScalarOp.copy) [] (S) → (Z[2 * (j * ldz + i)]);
      call (Has.inj ScalarOp.copy) [] (S[1]) → (Z[2 * (j * ldz + i) + 1])
    }
  }
}

end NLAlib
