/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Rounded.OperationCount
public import NLAlib.Krylov.Lanczos.Rounded.Ritz

/-!
# Scalar Lanczos in rounded arithmetic: one statement

The certificate `NLAlib.Krylov.Lanczos.Rounded.Stored.Certification.scalarCountedAlgorithm` is
unfolded here
into one theorem about a run, joined with the Ritz residual bound
`NLAlib.Krylov.Lanczos.Rounded.Output.ritzResidual` for the output of that same run: the run
succeeds, executes at most an explicit number of instructions of the scalar model, and every
eigenpair of the tridiagonal matrix it stores has a bounded residual.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.Stored.Certification.exec_scalarProgram_work_le_and_ritzResidual`:
  the
  statement.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded.Stored.Certification

open Ops

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- **Scalar Lanczos in rounded arithmetic: termination, operation count and Ritz residuals.**
Let $\mathbf{A} \in \mathbb{R}^{n \times n}$ be symmetric, stored entry by entry, let
$\mathbf{b} \in \mathbb{R}^n$ and let $k$ be the iteration cap. The program is the Lanczos
recurrence in Paige's ordering started from $\mathbf{b}$, without reorthogonalization, with
every matrix-vector product and every vector operation written out as scalar loops. Its
arithmetic is any scalar machine in the standard model with unit roundoff $u$: each of
$+, -, \times, /, \sqrt{\cdot}$ returns the exact result times $1 + \delta$,
$\lvert \delta \rvert \le u$, with no overflow or underflow, and comparisons of stored numbers
are exact. Let $E \le 1/100$ be an allowance that dominates the rounding of one scalar
operation, of one dot product, vector update and scaling of length $n$, and of one row-by-row
matrix-vector product (`Lanczos.Rounded.Precision`).

Then for every such input, every interpretation of the scalar operations that meets the model,
and every tape, the run succeeds, and

* it executes at most $33 n^{2} k + 153 n k + 302 k + 58 n + 179$ instructions (scalar
  operations, comparisons, index arithmetic, operand addressing, loop control and allocation,
  each of unit cost);
* it performs some number $m \le k$ of steps and leaves in memory the vectors
  $\mathbf{v}_1, \dots, \mathbf{v}_{m+1}$ (zeros after them), the coefficients
  $\alpha_1, \dots, \alpha_m$ and $\beta_1, \dots, \beta_m$, and the computed norm of
  $\mathbf{b}$. They are the values of a Lanczos recurrence in which each operation is exact up
  to an error of at most $E$ times its operands and
  $\lvert \|\mathbf{v}_j\|^2 - 1 \rvert \le E$ (`Lanczos.Rounded.Output`). If $m < k$, the last
  computed $\beta_m$ (or, for $m = 0$, the computed norm of $\mathbf{b}$) is exactly zero;
* if $k > 0$, $\mathbf{b} \ne \mathbf{0}$ and $k E \le 1/100$, then there is a length
  $q$ with $1 \le q \le k$, whose stored $\beta_q$ is zero when $q < k$, such that, with
  $\mathbf{V}_q = [\mathbf{v}_1, \dots, \mathbf{v}_q]$ and $\mathbf{T}_q$ the leading $q \times q$
  stored tridiagonal matrix, every $\theta$ and unit vector $\mathbf{y}$ with
  $\mathbf{T}_q \mathbf{y} = \theta \mathbf{y}$ satisfy
  $$\|\mathbf{A} \mathbf{V}_q \mathbf{y} - \theta \mathbf{V}_q \mathbf{y}\|
  \le \sqrt{1 + E}\, \beta_q \lvert y_q \rvert +
  6 q \sqrt{q}\, E\, \|\mathbf{A}\|_2$$
  (`Lanczos.Rounded.RitzResidual`; in its proof $q$ is the number $m$ of steps performed).

No orthogonality of the stored vectors is claimed, so $\mathbf{V}_m \mathbf{y}$ need not be
close to a unit vector and the residual bound alone does not place $\theta$ near an eigenvalue
of $\mathbf{A}$. The count is an upper bound read off the fixed program
(`NLAlib.Ops.Program.countPoly`). No printed source for the combined statement; the residual
bound is `NLAlib.LanczosRun.norm_mulVec_basis_mulVec_sub_smul_le` for the run the program
executes.
Result: lanczos-scalar-rounded-operation-count-ritz-residual -/
theorem exec_scalarProgram_work_le_and_ritzResidual (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ)
    (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d) (Blas.seq.err u) (d 0))
    {d : Fin 2 → ℕ} (hd : domain d) (x : (problem domain admitted).Input d)
    (I : Interp ScalarOp CmpTst ℝ)
    (hI : (RoundedScalarBlas.model (problem domain admitted) M).contracts d x I) (τ : Tape ℝ) :
    ∃ st, exec scalarProgram I RoundedScalarBlas.resources (problem domain admitted).formats τ d
        ((problem domain admitted).initial d x) = some st ∧
      RoundedScalarBlas.resources.work st.cost ≤
        33 * d 0 ^ 2 * d 1 + 153 * d 0 * d 1 + 302 * d 1 + 58 * d 0 + 179 ∧
      ∃ vs cs, st.mem.store.readBlock 2 0 ((d 1 + 1) * d 0) = some vs ∧
        st.mem.store.readBlock 3 0 (2 * d 1 + 2) = some cs ∧
        Lanczos.Rounded.Output id x.val.1.1 x.val.1.2 (E d) (d 1)
          vs cs ∧
        (0 < d 1 → x.val.1.2 ≠ 0 → (d 1 : ℝ) * E d ≤ 1 / 100 →
          Lanczos.Rounded.RitzResidual id x.val.1.1 (E d) (d 1) vs cs) := by
  obtain ⟨st, hr, -, -, hw, -, -, hg⟩ :=
    (scalarCountedAlgorithm M u hM hu E hprec).correct d hd x I hI τ
  obtain ⟨-, -, vs, cs, hvs, hcs, hout⟩ := hg
  exact ⟨st, hr, hw, vs, cs, hvs, hcs, hout, fun hk hb hs => hout.ritzResidual hk hb hs⟩

end NLAlib.Krylov.Lanczos.Rounded.Stored.Certification
