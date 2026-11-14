/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Orthogonalization.CGS2.Extend
public import NLAlib.Matrix.Factorizations.BasisExtensionContract
public import NLAlib.Matrix.Factorizations.CGS2.BasisExtension

/-!
# The exact contract of the column-wise two-pass Gram–Schmidt extension

In exact arithmetic, the implementation `NLAlib.CGS2.cgs2ExtendImpl` with the threshold $0$
meets the exact contract `NLAlib.Ops.exactExtendRel` of a basis extension, for an arbitrary
stored basis: with the threshold $0$ the deflation test drops exactly the columns whose reduced
vector is zero, which is the zero guard of rank-revealing Gram–Schmidt. The mathematics is
`NLAlib.isBasisExtension_of_two_passes`. Design: `docs/design/LowRank-BlockLanczos.md` §3.5,
statement E4 of §5.

## Main results

* `NLAlib.CGS2.cgs2Extend_exact_spec`: the implementation with the threshold $0$ meets the exact
  contract of a basis extension in exact arithmetic.
-/

@[expose] public section

namespace NLAlib.CGS2

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- **Exact column-wise two-pass classical Gram–Schmidt meets the exact contract of a basis
extension.** Under exact scalar arithmetic, exact level-1 operations at every length and exact
comparisons, the implementation with the deflation threshold $0$ runs on all admitted operands
of `NLAlib.Ops.OrthOp.extend` and the decoded basis $\mathbf{Q}$, block $\mathbf{W}$, new block
$\mathbf{Q}'$ and coefficients $\mathbf{H}$, $\mathbf{R}$ satisfy `NLAlib.IsBasisExtension`. The
stored basis is arbitrary: it may have zero columns and need not be orthonormal on its
support. -/
theorem cgs2Extend_exact_spec {M : Machine K} {dec : K → ℝ} {okB : ℕ → Prop}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec okB I) (hok : ∀ n, okB n) (hCmp : IsCmp dec I) :
    (cgs2ExtendImpl (Op := Op) (Tst := Tst) 0).Triple I .total
      ((exactExtendRel dec).spec ExtendOperands) := by
  -- `cert_intro [n, k, b] (Q, W) → (Qn, W', C) reads (qs, ws)`, the two `writes_alloc`, then
  -- `writes_loop` over `c` with the invariant: the first `c` columns of the new block, of the
  -- coefficient block and of the reduced block decode to matrices satisfying the seven
  -- hypotheses of `isBasisExtension_of_two_passes` restricted to the columns before `c`, and
  -- the columns from `c` on of `W` are unchanged.
  -- One round: `hB.nrm2`; `writes_fill` for the zero rows (`hM.lit 0`); `cgsPass_writes` twice
  -- with `hB.dot_zero` and the exact axpy, read against the `(k + c) * n` stored words (the
  -- basis block followed by the `c` new columns, one block by `Store.readBlock` of adjacent
  -- blocks); `PassOut` at zero errors gives `h₁ = Vᵀ w`, `w₁ = w - V h₁` and the same for the
  -- second pass; `hM.add` for the sums; `hB.nrm2`, `hM.lit`, `hM.mul` give the test
  -- `‖w₂‖ ≤ 0` (`hCmp.test_le`); the zero branch writes `hM.lit 0`, the other `hB.copy`,
  -- `hB.scal` (`w₂ / ‖w₂‖`) and the scalar copy of the norm.
  -- At exit apply `isBasisExtension_of_two_passes` with `𝕜 := ℝ` to the decoded matrices
  -- (`decodeMatrix_apply`, `coefTop`, `coefBot`).
  sorry

end NLAlib.CGS2
