/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Pair
public import NLAlib.Matrix.FinitePrecision.GivensRotation
public import NLAlib.Matrix.FinitePrecision.StoredMatrix
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Ops.Logic.Writes

/-!
# Products of stored complex matrices on strided views

A product $\mathbf{Z} = \mathbf{X}\mathbf{Y}$, or $\mathbf{Z} = \mathbf{X}^{\mathsf H}\mathbf{Y}$,
of complex matrices stored as word pairs in column-major order on strided views (leading dimensions
of their own), accumulated by rounded complex multiply–adds (`NLAlib.Ops.Pair.linearCombination`).
The output is a separate view. Under the standard model the stored product is within
$8(p + 1)\boldsymbol{u}\|\mathbf{X}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$ of the exact one, $p$
the inner dimension.

## Main definitions

* `NLAlib.matMulOn`: the strided product, with the left factor optionally conjugate-transposed.
* `NLAlib.matMulWord`: the product the program stores on a machine.

## Main results

* `NLAlib.matMulOn_writes_word`, `NLAlib.matMulOn_conjTranspose_writes_word`: the program stores
  `NLAlib.matMulWord` (contiguous views).
* `NLAlib.Ops.StdModel.specNorm_matMulWord_sub_le`: the error of the stored product.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

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

/-- **The product stored by `NLAlib.matMulOn`** on the machine `M`: entry $(i, j)$ is accumulated
from the pair of the literal $0$ by the rounded complex multiply–adds $s \mapsto
\mathrm{fl}(x_{il}y_{lj} + \hat 1 s)$, $l = 0, \dots, p - 1$, with $\hat 1$ the pair of the
literals $1$ and $0$ (`NLAlib.linearComplex`). -/
noncomputable def matMulWord (M : Machine ℝ) {m p q : ℕ} (X : Matrix (Fin m) (Fin p) ℂ)
    (Y : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin m) (Fin q) ℂ :=
  Matrix.of fun i j => (List.finRange p).foldl
    (fun s l => linearComplex M (X i l) ⟨M.lit 1, M.lit 0⟩ (Y l j) s) ⟨M.lit 0, M.lit 0⟩

section Theorems

variable [Inhabited ℝ]

/-- `NLAlib.matMulOn` with $c = 0$ on contiguous views (leading dimensions the row counts), on a
scalar machine and every tape: from $\mathbf{X}$ ($m \times p$) at `x` and $\mathbf{Y}$
($p \times q$) at `y`, with room for the output at `z` apart from both, it writes only the output
and stores `NLAlib.matMulWord`. -/
theorem matMulOn_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {m p q : ℕ} {x y z : ℕ × ℕ} {X : Matrix (Fin m) (Fin p) ℂ}
    {Y : Matrix (Fin p) (Fin q) ℂ} (hX : HoldsMatrix x X μ.store) (hY : HoldsMatrix y Y μ.store)
    (hl : μ.Live [x, y, z]) (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 (2 * (m * p))) (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 (2 * (p * q))) (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q)).body (Env.frame [m, p, q, m, p, m, 0] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M X Y) μ'.store) μ :=
  sorry

/-- `NLAlib.matMulOn` with $c = 1$ on contiguous views, under the standard model (negation is
exact): from $\mathbf{X}$ ($p \times m$) at `x` and $\mathbf{Y}$ ($p \times q$) at `y`, it writes
only the output and stores `NLAlib.matMulWord` of $\mathbf{X}^{\mathsf H}$ and $\mathbf{Y}$. -/
theorem matMulOn_conjTranspose_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : Ops.StdModel u id M) {τ : Tape ℝ} {μ : Mem ℝ} {m p q : ℕ}
    {x y z : ℕ × ℕ} {X : Matrix (Fin p) (Fin m) ℂ} {Y : Matrix (Fin p) (Fin q) ℂ}
    (hX : HoldsMatrix x X μ.store) (hY : HoldsMatrix y Y μ.store) (hl : μ.Live [x, y, z])
    (hz : z.2 + 2 * (m * q) ≤ μ.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 (2 * (p * m))) (Store.inBlock z.1 z.2 (2 * (m * q))))
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 (2 * (p * q))) (Store.inBlock z.1 z.2 (2 * (m * q)))) :
    Writes .total I τ (matMulOn (O := O) (Q := Q)).body (Env.frame [m, p, q, p, p, m, 1] [x, y, z])
      (Store.inBlock z.1 z.2 (2 * (m * q)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix z (matMulWord M Xᴴ Y) μ'.store) μ :=
  sorry

end Theorems

/-- **The error of a stored product** ([Higham2002, §3.5], complex, with the accumulation from a
rounded zero and a rounded unit): under the standard model at $\boldsymbol{u}$ with
$32(p + 1)\boldsymbol{u} \le 1$,
$\|\mathrm{fl}(\mathbf{X}\mathbf{Y}) - \mathbf{X}\mathbf{Y}\|_2 \le
8(p + 1)\boldsymbol{u}\|\mathbf{X}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$, $p$ the inner
dimension. Each multiply–add rounds the running sum four times (the product by the rounded unit,
the subtraction of the exact zero product, the sum), so a term passes through at most $4p$
roundings; the complex products contribute the factor $\sqrt 2$. -/
theorem Ops.StdModel.specNorm_matMulWord_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) {m p q : ℕ} (hu : 32 * ((p : ℝ) + 1) * u ≤ 1)
    (X : Matrix (Fin m) (Fin p) ℂ) (Y : Matrix (Fin p) (Fin q) ℂ) :
    specNorm (matMulWord M X Y - X * Y) ≤ 8 * (p + 1) * u * (frobNorm X * frobNorm Y) :=
  sorry

end NLAlib
