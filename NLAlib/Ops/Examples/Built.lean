/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Examples.GramSchmidt
public import NLAlib.Ops.Examples.Gemm
public import NLAlib.Ops.Examples.CgsQR

/-!
# Test case: the builder gives the hand-written trees

`ops%` elaborates to a plain `NLAlib.Ops.Stmt`; each example below states that the tree built
with names is the hand-written positional tree of an example, by `rfl` (the two terms are equal
after elaboration, so the check is syntactic, not a computation).

## Main results

* `mgs`: equal as written.
* `gemm`: equal as written.
* `cgs` (classical Gram–Schmidt): the whole algorithm in one block, equal as written.
* The other constructs (`index`, `if`, `while`, `ifPos`) against a hand-written tree.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- Modified Gram–Schmidt with names. -/
def mgsB : Stmt Op Tst := ops% [n, k] (Q, w) → (w, R) {
  let t ← alloc 1;
  for j < k {
    call (Has.inj Blas1Op.dot) [n] (Q[j * n], w) → (R[j]);
    call (Has.inj ScalarOp.neg) [] (R[j]) → (t);
    call (Has.inj Blas1Op.axpy) [n] (t, Q[j * n], w) → (w)
  };
  call (Has.inj Blas1Op.nrm2) [n] (w) → (R[k])
}

example : (mgsB : Stmt Op Tst) = mgs := rfl

/-- The implementation, with its numbers of dimensions and operands. -/
example : (opsImpl% [n, k] (Q, w) → (w, R) {
    let t ← alloc 1;
    for j < k {
      call (Has.inj Blas1Op.dot) [n] (Q[j * n], w) → (R[j]);
      call (Has.inj ScalarOp.neg) [] (R[j]) → (t);
      call (Has.inj Blas1Op.axpy) [n] (t, Q[j * n], w) → (w)
    };
    call (Has.inj Blas1Op.nrm2) [n] (w) → (R[k])
  } : Impl Op Tst) = mgsImpl := rfl

/-- The matrix product with names. -/
example : (ops% [m, n, p] (A, B) → (C) {
    for i < m {
      for j < p {
        call (Has.inj Blas1Op.dot) [n] (A[i * n], B[j * n]) → (C[(i * p + j)])
      }
    }
  } : Stmt Op Tst) = gemm := rfl

/-- **Classical Gram–Schmidt with names**, the whole algorithm in one block: for each column `j`
of the `n × p` matrix `A` stored by columns, the coefficients `R[j p + i] := Q_iᵀ A_j` for
`i < j`, the work vector `v := A_j - Σ_i R[j p + i] Q_i`, the norm `R[j p + j] := ‖v‖`, and
`Q_j := v / R[j p + j]`. The operand `R` is updated in place; the input copy is named `R₀` and is
not used, so every use of `R` is the output copy (buffer variable 3, offset variable 5). -/
def cgsB : Stmt Op Tst := ops% [n, p] (A, R₀) → (Q, R) {
  let t ← alloc 1;
  let v ← alloc n;
  for j < p {
    for i < j {
      call (Has.inj Blas1Op.dot) [n] (Q[i * n], A[j * n]) → (R[j * p + i])
    };
    call (Has.inj Blas1Op.copy) [n] (A[j * n]) → (v);
    for i < j {
      call (Has.inj ScalarOp.neg) [] (R[j * p + i]) → (t);
      call (Has.inj Blas1Op.axpy) [n] (t, Q[i * n], v) → (v)
    };
    call (Has.inj Blas1Op.nrm2) [n] (v) → (R[j * p + j]);
    call (Has.inj Blas1Op.scal) [n] (R[j * p + j], v) → (v);
    call (Has.inj Blas1Op.copy) [n] (v) → (Q[j * n])
  }
}

example : (cgsB : Stmt Op Tst) = cgs := rfl

/-- The other constructs: an index read from the store, a branch, the loop with early exit and
a branch on a size. -/
example (q : Tst) (o : Op) : (ops% [n] (x) → (y) {
    let k ← index q (x) ≤ n;
    if q [k] (x[k]) { call o [k] (x) → (y[k]) } else { abort };
    while r < n, q [r] (y[r]) { call o [r, k] (x) → (y[r]) } then {
      ifPos r { call o [r] (x) → (y) }
    }
  } : Stmt Op Tst) =
    .bindIdx q [⟨0, .var 1⟩] (.var 0)
      (.seq (.ite q [.var 3] [⟨0, .var 1 + .var 3⟩]
          (.call o [.var 3] [⟨0, .var 1⟩] [⟨1, .var 2 + .var 3⟩]) .abort)
        (.whileFuel (.var 0) q [.var 4] [⟨1, .var 2 + .var 4⟩]
          (.call o [.var 4, .var 3] [⟨0, .var 1⟩] [⟨1, .var 2 + .var 4⟩])
          (.ifPos (.var 4) (.call o [.var 4] [⟨0, .var 1⟩] [⟨1, .var 2⟩])))) := rfl

-- Allocation chains expose one fresh store and named lengths, including zero-sized buffers.
example {K : Type} {I : Interp Op Tst K} {md : Mode} (τ : Tape K) (μ : Mem K) (n : ℕ) :
    Writes md I τ (.alloc (.var 0) (.alloc (.var 0 * .const 2) .skip))
      ⟨[n], []⟩ ⊥ (fun _ => True) μ := by
  fail_if_success alloc as t t
  fail_if_success alloc as t u v
  fail_if_success alloc as n
  alloc as t u
  have : s_t.len t = n := ht
  have : s_t.len u = n * 2 := hu
  exact wp_skip ⟨Store.EqOff.refl _ _, fun _ _ _ => True.intro⟩

-- The tactic also recognizes the allocation-chain helper.
example {K : Type} {I : Interp Op Tst K} (τ : Tape K) (μ : Mem K) :
    Writes .total I τ (Stmt.allocs [.const 0] .skip) ⟨[], []⟩ ⊥ (fun _ => True) μ := by
  alloc as t
  have : s_t.len t = 0 := ht
  exact wp_skip ⟨Store.EqOff.refl _ _, fun _ _ _ => True.intro⟩

-- A caller read crosses allocation, two named calls, and release of the scratch buffer.
example {K : Type} {M : Machine K} {J : Interp Op Tst K} (hS : IsScalar M J) :
    (opsImpl% [] (x) → (y) {
      let t ← alloc 1;
      call (Has.inj ScalarOp.copy) [] (x) → (t);
      call (Has.inj ScalarOp.copy) [] (t) → (y)
    }).Meets J .total ((BlockFn.un fun a : K => some a).rel.spec AnyOperands) := by
  cert_intro [] (x) → (y) reads (xs)
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hxs)
  alloc as t
  step (hS .copy) as m₁ hfr₁ ⟨hpos₁, a₁, ha₁, hcopy₁⟩
  step (hS .copy) as m₂ hfr₂ ⟨hpos₂, a₂, ha₂, hcopy₂⟩
  intro s₂ hs₂ hB₂
  exact ⟨by simp [hpos₂, hpos₁], [[a₂]],
    Mem.readBlocks_of_cons (Store.readBlock_one_of_get (by kept)) rfl,
    by simp [BlockFn.rel, BlockFn.un, hcopy₁, hcopy₂]⟩

end NLAlib.Ops.Examples
