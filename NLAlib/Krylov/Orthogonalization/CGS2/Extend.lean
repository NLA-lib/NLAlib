/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.Sweep
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Catalog.Orth

/-!
# Extension of a stored basis by column-wise two-pass classical Gram–Schmidt

The first implementation of the operation `NLAlib.Ops.OrthOp.extend`. Each column of the block is
reduced twice against the stored basis followed by the new columns already written, which form
one contiguous stored block; the coefficients of the two passes are added into the coefficient
block. The reduced column is dropped (a zero column and a zero diagonal coefficient are written)
when its computed norm is at most the threshold $\tau$ times the computed norm of the input
column, and it is divided by its computed norm otherwise. The threshold is a rational literal of
the implementation; at $\tau = 0$ the test is the exact zero guard.
Design: `docs/design/LowRank-BlockLanczos.md` §3.5.

The program calls `NLAlib.Krylov.Lanczos.Reorth.cgsPass`, which is why this file is in the
Krylov layer; its intended home is `NLAlib/Matrix/Factorizations/CGS2/`, next to the pure
lemmas, once the classical pass is moved to the matrix layer.

## Main definitions

* `NLAlib.CGS2.cgs2Extend`, `NLAlib.CGS2.cgs2ExtendImpl`: the program and the implementation.
* `NLAlib.CGS2.cgs2ExtendColumnCount`, `NLAlib.CGS2.cgs2ExtendCount`: the operations of one
  column and of the block.
* `NLAlib.CGS2.cgs2ExtendPeak`: the workspace.

## Main results

* `NLAlib.CGS2.stmtCost_cgs2Extend`: the static count of the program.
* `NLAlib.CGS2.stmtPeak_cgs2Extend_le`: the static workspace of the program.
-/

@[expose] public section

namespace NLAlib.CGS2

open Ops Krylov.Lanczos.Reorth

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- **Column-wise two-pass classical Gram–Schmidt with threshold deflation**, at the dimensions
`[n, k, b]`. The stored basis `Q` has `k` columns of length `n`; the new block `Qn` is the `b`
columns stored directly after it, so that `Q` read with `k + c` columns is the basis followed by
the new columns before `c`. For each column `c` of the block `W`, in order: the norm of the
column is saved; the rows `k, …, k + b - 1` of column `c` of the coefficient block `C` are set
to zero; a first classical pass against the `k + c` stored columns writes its coefficients to
the rows before `k + c` of that column and a second pass writes its coefficients to scratch,
both reducing the column of `W` in place; the second coefficients are added to the first; the
norm of the reduced column is compared with the rounded product of the literal `τ` and the saved
norm. If it is at most that product the new column is set to zero, and otherwise the new column
is the reduced column divided by its norm, and the norm is the diagonal coefficient at row
`k + c`. The scratch is `k + b` coefficient cells and three scalar cells. -/
def cgs2Extend (τ : ℚ) : Stmt Op Tst := ops% [n, k, b] (Q, W) → (Qn, W, C) {
  let h ← alloc k + b;
  let t ← alloc 3;
  for c < b {
    call (Has.inj Blas1Op.nrm2) [n] (W[c * n]) → (t);
    for r < b {
      call (Has.inj (ScalarOp.lit 0)) [] () → (C[c * (k + b) + k + r])
    };
    run cgsPass [n, k + c] (Q, W[c * n], W[c * n], C[c * (k + b)]);
    run cgsPass [n, k + c] (Q, W[c * n], W[c * n], h);
    for r < k + c {
      call (Has.inj ScalarOp.add) [] (C[c * (k + b) + r], h[r]) → (C[c * (k + b) + r])
    };
    call (Has.inj Blas1Op.nrm2) [n] (W[c * n]) → (t[1]);
    call (Has.inj (ScalarOp.lit τ)) [] () → (t[2]);
    call (Has.inj ScalarOp.mul) [] (t[2], t) → (t[2]);
    if (Has.inj CmpTst.le) [] (t[1], t[2]) {
      for i < n {
        call (Has.inj (ScalarOp.lit 0)) [] () → (Qn[c * n + i])
      }
    } else {
      call (Has.inj Blas1Op.copy) [n] (W[c * n]) → (Qn[c * n]);
      call (Has.inj Blas1Op.scal) [n] (t[1], Qn[c * n]) → (Qn[c * n]);
      call (Has.inj ScalarOp.copy) [] (t[1]) → (C[c * (k + b) + k + c])
    }
  }
}

/-- The implementation of `NLAlib.Ops.OrthOp.extend` by column-wise two-pass classical
Gram–Schmidt with the deflation threshold `τ`: three dimensions `[n, k, b]`, the two inputs
`Q`, `W` and the three outputs `Qn`, `W`, `C`. -/
def cgs2ExtendImpl (τ : ℚ) : Impl Op Tst := ⟨3, 2, 3, cgs2Extend τ⟩

/-- The operations of column `c` of a block extension at the dimensions `[n, k, b]`: two norms,
`b` zero literals, two classical passes against `k + c` columns, `k + c` additions, the
threshold literal, one multiplication, one comparison, and the larger of the two branches (`n`
zero literals, or a copy, a scaling and a scalar copy). -/
noncomputable def cgs2ExtendColumnCount (τ : ℚ) (n k b c : ℕ) : Count Op Tst :=
  Count.one (Has.inj Blas1Op.nrm2) [n] + b • Count.one (Has.inj (ScalarOp.lit 0)) [] +
    cgsPassCount n (k + c) + cgsPassCount n (k + c) +
    (k + c) • Count.one (Has.inj ScalarOp.add) [] + Count.one (Has.inj Blas1Op.nrm2) [n] +
    Count.one (Has.inj (ScalarOp.lit τ)) [] + Count.one (Has.inj ScalarOp.mul) [] +
    Count.test (Has.inj CmpTst.le) [] +
    (n • Count.one (Has.inj (ScalarOp.lit 0)) [] ⊔
      (Count.one (Has.inj Blas1Op.copy) [n] + Count.one (Has.inj Blas1Op.scal) [n] +
        Count.one (Has.inj ScalarOp.copy) []))

/-- The operations of a block extension at the dimensions `[n, k, b]`: the sum over the `b`
columns of the operations of each column. -/
noncomputable def cgs2ExtendCount (τ : ℚ) (n k b : ℕ) : Count Op Tst :=
  ∑ c ∈ Finset.range b, cgs2ExtendColumnCount τ n k b c

/-- The workspace of a block extension at the dimensions `[n, k, b]`: `k + b` coefficient cells,
three scalar cells, and the largest workspace of a called operation, the scalar cell of a
classical pass included. -/
def cgs2ExtendPeak (W : Op → List ℕ → ℕ) (τ : ℚ) (n k b : ℕ) : ℕ :=
  k + b + 3 + max (W (Has.inj Blas1Op.nrm2) [n]) (max (cgsPassPeak W n)
    (max (W (Has.inj (ScalarOp.lit 0)) []) (max (W (Has.inj ScalarOp.add) [])
      (max (W (Has.inj (ScalarOp.lit τ)) []) (max (W (Has.inj ScalarOp.mul) [])
        (max (W (Has.inj Blas1Op.copy) [n]) (max (W (Has.inj Blas1Op.scal) [n])
          (W (Has.inj ScalarOp.copy) []))))))))

/-- The static count of the block extension is the sum over its columns: every pass, every
coefficient addition and the larger branch of every deflation test are charged. -/
theorem stmtCost_cgs2Extend (τ : ℚ) (n k b q w q' w' c : ℕ) :
    stmtCost (cgs2Extend (Op := Op) (Tst := Tst) τ) [n, k, b, q, w, q', w', c] =
      cgs2ExtendCount τ n k b := by
  -- Unfold `cgs2Extend` with `stmtCost`, `useCost`, `testCost` (the allocations cost nothing,
  -- `stmtCost_alloc`), evaluate the index expressions of round `c`, rewrite the two frames with
  -- `stmtCost_cgsPass` and the three inner loops with `Finset.sum_const`, `Finset.card_range`;
  -- then `Finset.sum_congr` over the columns, the summands agreeing up to associativity
  -- (`add_assoc`; the supremum of the two branches is kept as one term).
  sorry

/-- The static workspace of the block extension: the coefficient scratch and the three scalar
cells are held throughout, and the calls borrow at most the largest primitive workspace. -/
theorem stmtPeak_cgs2Extend_le (W : Op → List ℕ → ℕ) (τ : ℚ) (n k b q w q' w' c : ℕ) :
    stmtPeak W (cgs2Extend (Op := Op) (Tst := Tst) τ) [n, k, b, q, w, q', w', c] ≤
      cgs2ExtendPeak W τ n k b := by
  -- Unfold the two allocations (`stmtPeak_alloc`): the left side is `(k + b) + (3 + s)` with
  -- `s` the supremum over the columns `c < b` of the maximum of the workspaces of the calls of
  -- one column. Bound each call by its term of `cgs2ExtendPeak`: the two frames by
  -- `stmtPeak_cgsPass_le`, the three inner loops by `Finset.sup_le`.
  sorry

end NLAlib.CGS2
