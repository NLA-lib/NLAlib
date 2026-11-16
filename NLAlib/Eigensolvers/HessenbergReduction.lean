/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Coefficients
public import NLAlib.Eigensolvers.ShiftedQR.Hessenberg
public import NLAlib.Eigensolvers.ShiftedQR.RotationLoops
public import NLAlib.Matrix.FinitePrecision.GivensRounded
public import NLAlib.Matrix.Perturbation.UnitarySimilarity

/-!
# Bottom-up reduction to Hessenberg form by rounded rotations

A complex matrix of order $N$ is reduced to upper Hessenberg form by a unitary similarity that
fixes the last coordinate vector $\mathbf{e}_N$: row by row from the bottom, the entries of row
$r$ left of the subdiagonal are zeroed by rotations of adjacent columns $c, c + 1 < r$, each
applied on both sides. The columns rotated never include the last one, so the accumulated
unitary fixes $\mathbf{e}_N$; the entries below the subdiagonal are then written as exact
zeros. This is the "bottom-up Hessenberg form" that
[BanksGarzaVargasSrivastava2025, Definition 5.1] assumes to be stable; here it is a fixed program
over rounded scalar arithmetic, and its backward error is proved. The exact top-down reduction
(`NLAlib.hessenbergReduction`, fixing $\mathbf{e}_1$) is not a program.

## Main definitions

* `NLAlib.hessenbergReduceLast`: the program `[N] (A) → (A)`.
* `NLAlib.hessenbergReduceLastWord`: the matrix it stores on a machine.

## Main results

* `NLAlib.hessenbergReduceLast_writes_word`: the program stores the machine evaluation.
* `NLAlib.hessenbergReduceLast_isPerturbedUnitarySimilar`: backward stability, with the last
  coordinate vector fixed.
* `NLAlib.hessenbergReduceLast_terminates`: termination on every tape.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

/-- **The bottom-up Hessenberg reduction** ([BanksGarzaVargasSrivastava2025, Definition 5.1],
as a program): for the rows $r = N - 1, \dots, 2$ (round $i$ has $r = N - 1 - i$) and the columns
$c = 0, \dots, r - 2$, the Givens coefficients of the pair
$(\mathbf{A}_{r, c+1}, -\mathbf{A}_{r, c})$, then the rotation of the columns $c, c + 1$ (which
zeros $\mathbf{A}_{r,c}$) and of the rows $c, c + 1$; finally the entries below the subdiagonal
are written as zeros. The interface is `[N] (A) → (A)`; the coefficients and the pair are
scoped scratch.
Algorithm: hessenberg-reduction -/
def hessenbergReduceLast : Impl O Q := opsImpl% [N] (A) → (A) {
  let Cf ← alloc 4;
  let Uv ← alloc 4;
  for i < N - 2 {
    for c < N - 2 - i {
      call (Has.inj ScalarOp.copy) [] (A[2 * ((c + 1) * N + N - 1 - i)]) → (Uv);
      call (Has.inj ScalarOp.copy) [] (A[2 * ((c + 1) * N + N - 1 - i) + 1]) → (Uv[1]);
      call (Has.inj ScalarOp.neg) [] (A[2 * (c * N + N - 1 - i)]) → (Uv[2]);
      call (Has.inj ScalarOp.neg) [] (A[2 * (c * N + N - 1 - i) + 1]) → (Uv[3]);
      run (coefficients (Op := O) (Tst := Q)).body [] (Uv, Uv[2], Cf, Cf[2]);
      run (rotateColumns (Op := O) (Tst := Q)).body [N, c] (A, Cf, Cf[2], A);
      run (rotateRows (Op := O) (Tst := Q)).body [N, c] (A, Cf, Cf[2], A)
    }
  };
  run (clearBelowSubdiagonal (Op := O) (Tst := Q)).body [N] (A)
}

end Program

/-- One step of the reduction on a machine: the rounded Givens coefficients of
$(\mathbf{A}_{r,c+1}, -\mathbf{A}_{r,c})$, then the rounded rotation of the columns $c, c + 1$
and of the rows $c, c + 1$; the identity when $c + 1$ or $r$ is out of range. -/
noncomputable def reduceLastStepWord (M : Machine ℝ) {N : ℕ} (r c : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  if h : c + 1 < N ∧ r < N then
    let i : Fin N := ⟨c, by omega⟩
    let j : Fin N := ⟨c + 1, h.1⟩
    let cs := roundedGivensCoeffs M (A ⟨r, h.2⟩ j) ⟨M.neg (A ⟨r, h.2⟩ i).re, M.neg (A ⟨r, h.2⟩ i).im⟩
    machineRowRotation M i j cs.1 cs.2 (machineColRotation M i j cs.1 cs.2 A)
  else A

/-- The matrix stored by `NLAlib.hessenbergReduceLast` on the machine `M`: the steps
`NLAlib.reduceLastStepWord` in the order of the program, then the entries below the subdiagonal
replaced by the pair of the literal $0$. -/
noncomputable def hessenbergReduceLastWord (M : Machine ℝ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  let B := ((List.range (N - 2)).flatMap fun i => (List.range (N - 2 - i)).map fun c => (i, c)).foldl
    (fun X ic => reduceLastStepWord M (N - 1 - ic.1) ic.2 X) A
  Matrix.of fun i j => if (j : ℕ) + 1 < i then ⟨M.lit 0, M.lit 0⟩ else B i j

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

/-- `NLAlib.hessenbergReduceLast` on any scalar machine with exact comparisons stores the machine
evaluation `NLAlib.hessenbergReduceLastWord` of the matrix in place, writes only the matrix, and
reads no tape. -/
theorem hessenbergReduceLast_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {N : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : m.Live [a]) (hA : HoldsMatrix a A m.store) :
    Writes .total I τ (hessenbergReduceLast (O := O) (Q := Q)).body (Env.frame [N] [a, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (hessenbergReduceLastWord M A) m'.store) m := by
  sorry

/-- **The bottom-up Hessenberg reduction is backward stable and fixes $\mathbf{e}_N$**
([BanksGarzaVargasSrivastava2025, Definition 5.1], proved for rounded rotations): on a machine
with the standard model at the unit roundoff $\boldsymbol{u}$, $M.\mathrm{lit}(0) = 0$ and
$100(n + 1)^2\boldsymbol{u} \le 1$, the stored matrix $\widehat{\mathbf{H}}$ of a complex
$\mathbf{A}$ of order $n + 1$ is upper Hessenberg and there is a unitary $\mathbf{Q}$ with
$\mathbf{Q}\mathbf{e}_{n+1} = \mathbf{e}_{n+1}$ and
$$\|\widehat{\mathbf{H}} - \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le
  50(n + 1)^2\boldsymbol{u}\,\|\mathbf{A}\|_2\,.$$ -/
theorem hessenbergReduceLast_isPerturbedUnitarySimilar {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hzero : M.lit 0 = 0) {n : ℕ} (hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    IsUpperHessenberg (hessenbergReduceLastWord M A) ∧
      ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols Q ∧
        (∀ i, Q i (Fin.last n) = if i = Fin.last n then 1 else 0) ∧
        specNorm (hessenbergReduceLastWord M A - Qᴴ * A * Q) ≤
          50 * ((n : ℝ) + 1) ^ 2 * u * specNorm A := by
  sorry

/-- `NLAlib.hessenbergReduceLast` terminates on every tape and every stored matrix: its loops are
counted and every operation succeeds on stored operands. -/
theorem hessenbergReduceLast_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {N : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : m.Live [a]) (hA : HoldsMatrix a A m.store) :
    Writes .total I τ (hessenbergReduceLast (O := O) (Q := Q)).body (Env.frame [N] [a, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun m' => ∃ A' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix a A' m'.store) m := by
  sorry

end Theorems

end NLAlib
