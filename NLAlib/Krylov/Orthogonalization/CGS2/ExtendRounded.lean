/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Orthogonalization.CGS2.Extend
public import NLAlib.Matrix.Factorizations.BasisExtensionContract
public import NLAlib.Matrix.Factorizations.CGS2.BasisExtensionErr
public import NLAlib.Ops.Catalog.Operator

/-!
# The rounded contract of the column-wise two-pass Gram–Schmidt extension

Under the standard model of rounded arithmetic and the level-1 contracts, the implementation
`NLAlib.CGS2.cgs2ExtendImpl` with a threshold $\tau > 0$ meets the rounded contract
`NLAlib.Ops.extendRel` of a basis extension with the parameters
`NLAlib.cgs2ExtendMu` and `NLAlib.cgs2ExtendEps` at the constants of two classical passes. The
stored basis has zero columns where earlier columns were dropped: a rounded dot product with a
stored zero column decodes to zero, and the update with a zero coefficient is one more link of
the chain of rounded updates, so the two passes meet the single-vector guarantee on the support
with the pass coefficient of the full number of stored columns. Design:
`docs/design/LowRank-BlockLanczos.md` §3.5, statement E3 of §5.

## Main results

* `NLAlib.CGS2.decv_eq_zero_of_passOut`: a classical pass maps a zero vector to a zero vector.
* `NLAlib.CGS2.isOrthErrOnSupport_of_passOut`: two rounded passes against a stored basis with
  zero columns meet the single-vector guarantee on the support.
* `NLAlib.CGS2.cgs2Extend_spec`: the implementation meets the rounded contract of a basis
  extension.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.CGS2

open Ops Krylov.Lanczos.Reorth

variable {K Op Tst : Type} [Inhabited K]

/-- A rounded classical pass maps a vector that decodes to zero to a vector that decodes to
zero, for any error parameters of the dot products and of the updates: every coefficient is a
rounded dot product with the zero vector, and every update adds a zero multiple to zero. -/
theorem decv_eq_zero_of_passOut {dec : K → ℝ} {ed ea : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hw : decv dec n ws = 0) :
    decv dec n ws' = 0 := by
  -- `h.dot j hj` with `hw` gives `dec (vec hs j) = 0` (both sums of `IsDotErr` vanish). Then
  -- induction on `h.update` (`AxpyChain`): if the current vector decodes to zero on `i < n`, the
  -- step `IsAxpyErr dec ea n t (q j) w w'` with `dec t = -dec (vec hs j) = 0` gives
  -- `|dec (w' i) - 0| ≤ ea * (0 + 0)`.
  sorry

/-- Two rounded classical passes against a stored basis with zero columns. Let two passes
against the $k$ stored columns $\mathbf{V}$ of length $n$ have dot errors $e_d \ge 0$ and update
errors $e_a \ge 0$, the first from $\mathbf{w}$ to $\mathbf{w}_1$ with coefficients
$\mathbf{h}_1$ and the second from $\mathbf{w}_1$ to $\mathbf{w}_2$ with coefficients
$\mathbf{h}_2$, and let $\mathbf{h}$ be their sum computed with relative error $u$,
$\lvert h_j - (h_{1,j} + h_{2,j})\rvert \le u\lvert h_{1,j} + h_{2,j}\rvert$. If
$0 \le \eta \le 1/100$, $c \le 1/100$, $u \ge 0$, $4u \le c$ and
$(k+1)e_d(1+\eta)^2 + ((1+e_a)^k - 1)(1 + k(1+e_d)(1+\eta)^2) \le c$, then
$(\mathbf{h}, \mathbf{w}_2)$ meets the single-vector guarantee on the support for $\mathbf{w}$
and $\mathbf{V}$ with parameters $(\eta, 2c, 3c, 2(\eta + c)^2)$. The stored columns may be
zero: the budget counts all $k$ columns. -/
theorem isOrthErrOnSupport_of_passOut {dec : K → ℝ} {ed ea η c u : ℝ} {n k : ℕ}
    {qs ws mid ws' h₁ h₂ : List K} {h : Fin k → ℝ}
    (hp₁ : PassOut dec ed ea n k qs ws mid h₁) (hp₂ : PassOut dec ed ea n k qs mid ws' h₂)
    (hd : 0 ≤ ed) (ha : 0 ≤ ea) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100) (hc : c ≤ 1 / 100)
    (hu : 0 ≤ u) (hu₁ : 4 * u ≤ c)
    (hbudget : (k + 1) * ed * (1 + η) ^ 2 +
      ((1 + ea) ^ k - 1) * (1 + k * (1 + ed) * (1 + η) ^ 2) ≤ c)
    (hsum : ∀ j : Fin k, |h j - (dec (vec h₁ j) + dec (vec h₂ j))| ≤
      u * |dec (vec h₁ j) + dec (vec h₂ j)|) :
    IsOrthErrOnSupport η (2 * c) (3 * c) (2 * (η + c) ^ 2) (decodeMatrix dec n k qs)
      (decv dec n ws) h (decv dec n ws') := by
  -- By `isOrthErrOnSupport_of_two_passes` it suffices to prove, for each pass, the three bounds
  -- of `PassOut.norm_bounds` under `specNorm (gramDefect V) ≤ η` in place of
  -- `specNorm (Vᵀ * V - 1) ≤ η`. Its proof goes through: `PassOut.abs_sub_dotProduct_le` and
  -- `PassOut.norm_sub_sub_sum_le` need no orthogonality; the only use of the antecedent is
  -- `‖column‖ ≤ 1 + η` and `specNorm V ≤ 1 + η`, which hold for a zero column trivially and for
  -- the others by `specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect` on the nonzero
  -- columns (`V *ᵥ x` and `Vᵀ *ᵥ y` see only those).
  sorry

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- **Column-wise two-pass classical Gram–Schmidt with threshold deflation meets the rounded
contract of a basis extension.** Assume the standard model of rounded arithmetic at the unit
roundoff $u$, the level-1 contracts with dot error $e_d(n)$, update error $e_a$, square-root
error $e_s$ and scaling error $e_c$, and exact comparisons. Let $0 \le \eta_0 \le 1/100$,
$c \le 1/100$, $u \ge 0$, $4u \le c$, $0 \le E \le 1/100$, and let $\tau > 0$ be the rational
threshold of the implementation. At every admitted dimension $(n, k, b)$ assume that the level-1
operations admit the length $n$, that $e_d(n) \ge 0$, that the pass budget of $k + b$ columns
holds,
$(k+b+1)e_d(n)(1+\eta_0)^2 + ((1+e_a)^{k+b} - 1)(1 + (k+b)(1+e_d(n))(1+\eta_0)^2) \le c$,
and that the computed norms are accurate to $E$, $e_d(n) + e_s(1 + e_d(n)) \le E$; assume also
$e_c \le E$. Then the implementation runs on all admitted operands and its decoded output is a
rounded extension with the window $\eta_0$ and the parameters
$\mu = 4c + 8(\eta_0 + c)^2/\tau + 5E$ and $\varepsilon = 3c + 2E + 2\tau$. -/
theorem cgs2Extend_spec {M : Machine K} {dec : K → ℝ} {u η₀ c E : ℝ} {τ : ℚ} {ε : Blas1Err}
    {okB : ℕ → Prop} {ok : ℕ → ℕ → ℕ → Prop} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε okB I) (hCmp : IsCmp dec I)
    (hu : 0 ≤ u) (hu₁ : 4 * u ≤ c) (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hc : c ≤ 1 / 100)
    (hE : 0 ≤ E) (hE' : E ≤ 1 / 100) (hτ : 0 < τ)
    (ha : 0 ≤ ε.axpy) (hs : 0 ≤ ε.sqrt) (hsc : 0 ≤ ε.scal) (hscal : ε.scal ≤ E)
    (hokB : ∀ n k b, ok n k b → okB n) (hdot : ∀ n k b, ok n k b → 0 ≤ ε.dot n)
    (hbudget : ∀ n k b, ok n k b → ((k + b : ℕ) + 1) * ε.dot n * (1 + η₀) ^ 2 +
      ((1 + ε.axpy) ^ (k + b) - 1) * (1 + (k + b : ℕ) * (1 + ε.dot n) * (1 + η₀) ^ 2) ≤ c)
    (hnorm : ∀ n k b, ok n k b → ε.dot n + ε.sqrt * (1 + ε.dot n) ≤ E) :
    (cgs2ExtendImpl (Op := Op) (Tst := Tst) τ).Triple I .total
      ((extendRel dec η₀ (cgs2ExtendMu (2 * c) (2 * (η₀ + c) ^ 2) E τ)
        (cgs2ExtendEps (3 * c) E τ) ok).spec ExtendOperands) := by
  -- Execution as in `cgs2Extend_exact_spec`, with `hB.nrm2`, `cgsPass_writes hS hB.dot hB.axpy
  -- hM.neg`, `hM.add`, `hM.lit`, `hM.mul`, `hCmp.test_le`, `hB.copy`, `hB.scal`; no branch needs
  -- a premise, since `nrm2` and `scal` are total. The loop invariant keeps, for the columns
  -- before `c`, the words of both passes (`PassOut` twice), of the two norms and of the branch.
  -- At exit apply `isBasisExtensionErr_of_columns` with `ε₁ = 2 * c`, `ε₂ = 3 * c`,
  -- `ε₃ = 2 * (η₀ + c) ^ 2`: `hR` and the zero column from `hM.zero`; `hO` from
  -- `isOrthErrOnSupport_of_passOut` (budget monotone in the number `k + c ≤ k + b` of columns,
  -- sums by `hM.add`) and `IsOrthErrOnSupport.of_submatrix` along the embedding of
  -- `Fin (k + c)` into `Fin k ⊕ Fin b`; `hzero` from `decv_eq_zero_of_passOut` twice; `hν`, `hβ`
  -- from `IsNrm2Err.norm_error_bounds` and `hnorm`; `hstep` from the test on
  -- `t = fl(fl(τ) * ν)`, with `τ * (1 - u) ^ 2 * ν ≤ t ≤ τ * (1 + u) ^ 2 * ν` (`hM.lit`,
  -- `hM.mul`, `u ≤ 1 / 400`), and from `IsScalErr` with `hscal` in the kept branch.
  sorry

end NLAlib.CGS2
