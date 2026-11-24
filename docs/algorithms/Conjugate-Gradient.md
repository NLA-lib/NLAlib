# Conjugate gradient

Conjugate gradient solves a symmetric positive-definite system through matrix applications,
dot products and vector updates. NLAlib separates the algorithm's update order, the operation
model giving those operations meaning, and the implementations of individual operations.
The certificates describe the actual stored state and its counted execution.

## Headline statement: scalar conjugate gradient in rounded arithmetic

This is the strongest statement proved about a conjugate gradient program, as one theorem:
[`exec_scalarProgram_work_le_and_quadForm_le`](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/ScalarTheorem.lean).
The other certificates on this page are for other programs or other operation models, and are
listed under "Checked sources".

**Theorem.** Let A be a real symmetric n × n matrix with spectrum in [a, a′], a > 0, stored
entry by entry; let b be a real vector of length n; let k be the iteration cap; and write
κ = a′/a. Run carried Hestenes–Stiefel conjugate gradient from x₀ = 0, with every
matrix-vector product and vector operation written out as scalar loops, on any scalar machine
in the standard model with unit roundoff u. Let E ≤ 1/100 be an error allowance with

```text
((1+u)^(2n) − 1)·√n ≤ E      one row-by-row matrix-vector product
16·u ≤ E                      one scalar operation; one scaling
16·((1+u)^n − 1) ≤ E          one sequential dot product of length n
(1+u)² − 1 ≤ E                one vector update
3·E·a′ ≤ a
k²·√k·E·κ² ≤ 10⁻⁵
```

Then every run succeeds, and:

1. **Cost.** It executes at most `33·n²·k + 157·n·k + 242·k + 50·n + 127` instructions of the
   scalar model.
2. **Stopping.** It performs some m ≤ k rounds and leaves an iterate x̂, a residual vector r̂
   and a direction in memory. If m < k then r̂ = 0 exactly.
3. **Accuracy.** For every solution x of A x = b,

```text
(x − x̂)ᵀ A (x − x̂) ≤ 4·((√(2κ+1) − 1)/(√(2κ+1) + 1))^(2m) · xᵀ A x
                    + 12000·m²·√m·E·κ·a′·‖b‖² / a²
                    + 135·m²·E·κ·‖b‖² / a
```

**Scope.** What the statement does and does not say:

- *Every run* means: every admitted input, every interpretation of the seven scalar
  operations and the comparisons that satisfies the model's contracts, and every tape. The
  program is one fixed tree for all n and k.
- *Instructions* are scalar operations, comparisons, and every structural instruction (index
  arithmetic, operand addressing, loop control, allocation), each of unit cost. The count is
  an upper bound read off the program; a branch is charged for both sides.
- The standard model has no overflow or underflow, and comparisons of stored numbers are
  exact. It is not IEEE arithmetic. Stored numbers are real numbers; a cell is not 64 bits.
- The accuracy bound is in terms of the rounds m actually performed. Reaching the cap is not
  a convergence claim, and the program has no tolerance-based stopping test.
- The first term is the exact conjugate gradient rate at condition number 2κ + 1, not κ. The
  other two terms are accumulated rounding; at the edge of the window k²√k·E·κ² ≤ 10⁻⁵ they
  can exceed the initial error, so the bound is informative when E is well inside it.
- The window limits the cap. For n = 1000 and u ≈ 1.1·10⁻¹⁶ the smallest admissible E is
  about 7·10⁻¹², set by the matrix-vector condition, and the window then allows roughly
  k ≤ 45 at κ = 10 and k ≤ 7 at κ = 100. No instance with n > 1 is exhibited in the library.
- The spectral interval [a, a′] is part of the admitted input: the caller must know it.

**Lean.** The statement, verbatim:

```lean
theorem exec_scalarProgram_work_le_and_quadForm_le (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (em E : (Fin 2 → ℕ) → ℝ)
    (hMatvec : ∀ d, domain d → ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0) ≤ em d)
    (hAccuracy : ∀ d, domain d → Standard.Accuracy (em d) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lower d)
    (hprec : ∀ d, domain d → 3 * E d * upper d ≤ lower d)
    (hwindow : ∀ d, domain d → (d 1 : ℝ) ^ 2 * Real.sqrt (d 1) * E d *
      (upper d / lower d) ^ 2 ≤ 1 / 10 ^ 5)
    {d : Fin 2 → ℕ} (hd : domain d) (x : (problem lower upper domain admitted supply).Input d)
    (I : Interp ScalarOp CmpTst ℝ)
    (hI : (RoundedScalarBlas.model (problem lower upper domain admitted supply) M).contracts
      d x I) (τ : Tape ℝ) :
    ∃ st, exec scalarProgram I RoundedScalarBlas.resources
        (problem lower upper domain admitted supply).formats τ d
        ((problem lower upper domain admitted supply).initial d x) = some st ∧
      RoundedScalarBlas.resources.work st.cost ≤
        33 * d 0 ^ 2 * d 1 + 157 * d 0 * d 1 + 242 * d 1 + 50 * d 0 + 127 ∧
      ∃ m ≤ d 1, ∃ (s : CGState ℝ (Fin (d 0))) (rho : ℝ),
        StoresValues id (d 0) (2, 0) (3, 0) (4, 0) (5, 0) s rho st.mem ∧
        (m < d 1 → s.r = 0) ∧
        ∀ xs : Fin (d 0) → ℝ, inputMatrix x *ᵥ xs = inputRhs x →
          quadForm (inputMatrix x) (xs - s.x) ≤
            4 * ((Real.sqrt (2 * (upper d / lower d) + 1) - 1) /
              (Real.sqrt (2 * (upper d / lower d) + 1) + 1)) ^ (2 * m) *
                quadForm (inputMatrix x) xs +
            2 * ‖WithLp.toLp 2 (inputRhs x)‖ ^ 2 *
              (6000 * (m : ℝ) ^ 2 * Real.sqrt m * E d * (upper d / lower d) * upper d) /
                lower d ^ 2 +
            135 * (m : ℝ) ^ 2 * E d * (upper d / lower d) *
              (‖WithLp.toLp 2 (inputRhs x)‖ ^ 2 / lower d)
```

**Translation notes.**

| In the theorem | In the Lean | Where |
|---|---|---|
| n, k | `d 0`, `d 1`, the two sizes of the program | `d : Fin 2 → ℕ` |
| which (n, k) are covered | `domain d`, a parameter: the theorem holds for whatever set of sizes satisfies its hypotheses | `hd : domain d` |
| A, b | `inputMatrix x`, `inputRhs x`: the words of buffers 0 and 1, read as a matrix and a vector | [`ScalarTheorem.lean`](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/ScalarTheorem.lean) |
| A symmetric with spectrum in [a, a′] | part of being an input: `accepts lower upper d raw rhs` is `Aᵀ = A ∧ spectrum ℝ A ⊆ Set.Icc (lower d) (upper d)`; a, a′ are `lower d`, `upper d` | [`StoredCertification.lean`](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/StoredCertification.lean) |
| scalar machine in the standard model | `M : Machine ℝ` with `hM : StdModel u id M` | [`Catalog/Scalar.lean`](../../NLAlib/Ops/Catalog/Scalar.lean) |
| the first four conditions on E, and E ≤ 1/100 | `hMatvec` and `hAccuracy`; `em d` is the matrix-vector allowance, `Blas.seq.err u` the sequential dot, update and scaling errors | [`Profiles/Standard.lean`](../../NLAlib/Ops/Profiles/Standard.lean), [`Profiles/BlasCert.lean`](../../NLAlib/Ops/Profiles/BlasCert.lean) |
| E may depend on the sizes | `E d` | |
| every interpretation meeting the model | `I` with `hI : (RoundedScalarBlas.model …).contracts d x I` | [`Profiles/RoundedScalarBlas.lean`](../../NLAlib/Ops/Profiles/RoundedScalarBlas.lean) |
| the run succeeds | `exec scalarProgram … = some st` | [`Ops/Exec.lean`](../../NLAlib/Ops/Exec.lean) |
| number of instructions | `RoundedScalarBlas.resources.work st.cost`; every weight of these resources is 1 | [`OperationCount.lean`](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/OperationCount.lean) |
| x̂, r̂, the direction and the retained scalar are in memory | `StoresValues id n (2,0) (3,0) (4,0) (5,0) s rho st.mem`: buffers 2, 3, 4 hold `s.x`, `s.r`, `s.p` and buffer 5 holds `rho` | [`State.lean`](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/State.lean) |
| (x − x̂)ᵀ A (x − x̂) | `quadForm (inputMatrix x) (xs - s.x)` | |
| 12000·m²·√m·E·κ·a′·‖b‖²/a² | `2 * ‖b‖ ^ 2 * (6000 * m ^ 2 * √m * E d * κ * upper d) / lower d ^ 2` | |

The Lean statement says three things the theorem above leaves implicit: the tape `τ` is
arbitrary (the program draws nothing); the theorem is stated for a family `E`, `em`, `lower`,
`upper` indexed by the sizes; and the three conclusions are about one execution state `st`.
The proof only unfolds the certificate
[`scalarCountedAlgorithm`](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/OperationCount.lean);
the energy bound is `NLAlib.CGRun.quadForm_sub_x_le_four_mul_pow_add` for the run the program
executes.

## Algorithms and stopping rules

| Algorithm | Distinguishing choice | Exact total result |
|---|---|---|
| Fixed-horizon Hestenes–Stiefel CG | Recomputes the old residual self-product each round; executes the prescribed horizon | The CG state after k rounds, assuming k does not exceed the initial Krylov grade |
| Carried Hestenes–Stiefel CG | Retains the residual self-product between rounds and tests it before the next round | The CG state at the earlier of the cap and exact convergence |
| Full residual reorthogonalization | Sweeps each new residual against the archived nonzero residuals before forming the next direction | The same exact CG state at the earlier of the cap and exact convergence |
| Preconditioned CG (PCG) | Applies a separately declared inverse preconditioner B to each residual | The PCG state after k rounds under the corresponding grade bound |

These are different algorithm implementations even when their exact mathematical iterates
agree. Retaining a scalar, changing update order, adding projections or changing the stopping
rule changes the actual program and can change its rounded behavior. Choosing exact or
rounded arithmetic is a separate operation-model choice.

The **Krylov grade** is the dimension at which the initial residual's Krylov space stops
growing. For an SPD system, exact CG converges by that grade. A fixed-horizon theorem uses
`k ≤ grade` to justify all executed divisions. The carried and reorthogonalized solvers
instead test the computed residual self-product before another round; their exact theorems
allow any cap and stop at `min(cap, grade)`. A zero initial residual therefore needs no round.

## CG pseudocode

The following shows the carried variant. Operations are abstract; `axpy(a,u,v)` means
`v + a*u`. Canonical zero-start programs write the initial iterate themselves.

```text
x = 0
r = b - matvec(A, x)
p = r
rho = dot(r, r)

repeat at most cap times, while rho > 0:
    q = matvec(A, p)
    alpha = rho / dot(p, q)
    x = axpy(alpha, p, x)
    r = axpy(-alpha, q, r)
    rho_next = dot(r, r)
    beta = rho_next / rho
    p = r + beta*p
    rho = rho_next
return x, r, p, rho
```

The [fixed-horizon program](../../NLAlib/Krylov/CG/HSCG/Alg.lean) computes `dot(r,r)` at
the beginning of each round and uses a fixed loop. The
[carried program](../../NLAlib/Krylov/CG/HSCG/Carried/Alg.lean) stores `rho` and tests it.
The actual direction update uses a temporary vector and counted copies. Initialization
still executes its declared matrix application even when the canonical initial iterate is zero.

The rounded zero-start carried implementation has a separate initializer: after writing
`x = 0`, it copies the raw RHS into `r` and `p`, then computes `rho = dot(r,r)`. Its initial
residual is therefore the supplied RHS, with no rounded subtraction of a zero matvec. The
rounded stored certificate uses this copy initializer and its actual instruction count.

The [reorthogonalized program](../../NLAlib/Krylov/CG/Reorth/Solver.lean) saves the incoming
residual before a round. After the ordinary iterate and residual updates, it inserts:

```text
for each archived residual h:
    r = r - (dot(h, r) / dot(h, h))*h
rho_next = dot(r, r)
p = r + (rho_next/rho)*p
```

Each coefficient uses the currently updated residual: this is a sequential projection sweep.
The history contains nonzero residuals from executed rounds. Its denominators are justified
by the exact SPD analysis. This is distinct from the two classical passes used by
[reorthogonalized Lanczos](Lanczos.md).

## Preconditioning

The [PCG program](../../NLAlib/Krylov/CG/HSPCG/Alg.lean) treats the system A and applied
inverse preconditioner B as separate operators. B approximates the inverse; the program
applies B directly rather than solving a system with a stored preconditioner.

```text
x = 0
r = b - matvec(A, x)
z = matvec(B, r)
p = z
repeat k times:
    rho = dot(r, z)
    q = matvec(A, p)
    alpha = rho / dot(p, q)
    x = x + alpha*p
    r = r - alpha*q
    z = matvec(B, r)
    beta = dot(r, z) / rho
    p = z + beta*p
return x, r, z, p
```

Both matrices are SPD. For the zero-start fixed-horizon certificate, the explicit assumption
is `k ≤ krylovGrade(B*A, B*b)`. The two operator names have separate contracts and resource
charges in the matrix-free model. The stored implementation declares both raw matrices.

## Operation models and implementations

| Model or implementation | What is declared or executed |
|---|---|
| Exact matrix-free | Exact scalar arithmetic, exact BLAS1 and an exact mathematical operator action; PCG declares two actions |
| Exact stored dense | Raw column-major matrix words are supplied as buffers; every matrix application executes scalar multiply/add loops, while BLAS1 remains an explicit exact collection |
| Rounded matrix-free | Scalar relative-error contracts, selected BLAS error allowances and an independent normwise matrix-vector error allowance |
| Rounded stored scalar carried CG | Raw matrix and RHS words; dense matvec and sequential BLAS both execute scalar loops, and their errors follow from the supplied scalar model |
| Sequential or pairwise scalar BLAS profile | A fixed lowering proves the selected vector contracts from scalar operations; an actual linked-tree certificate accounts for that tree's instructions and workspace |

The exact stored target model has scalar and vector names, with no matrix-vector primitive.
A shared context transformation forwards the declared matrix buffer through every procedure.
Its proof reuses the numerical word theorem; the running program performs the dense arithmetic.
A proof-side reference interpretation does not add runtime guards or an alternate solver.

The [standard operation model](../../NLAlib/Ops/Profiles/Standard.lean) keeps scalar rounding,
BLAS reduction scheme and matrix-vector accuracy separate. Its dot allowance scales with the
sum of absolute products, rather than the possibly cancelling dot result. The scalar model
uses unbounded exponents. Storage formats and physical arithmetic require their own bridges;
these exact and standard-model certificates do not claim native IEEE execution.

## Output, assumptions and resources

The exact canonical programs start from supplied RHS words and uninitialized output capacity.
They return the stored iterate, residual and search direction; PCG also returns the
preconditioned residual, and the carried variant retains its self-product. Their output
relations identify the existing pure `cgState` or `pcgState`, rather than merely asserting
that some successful run has a good iterate.

For stored inputs, SPD and grade assumptions concern the decoder of the actual raw words.
The admitted size domain has a genuine joint raw-input witness. This witnesses nonemptiness;
it neither initializes the algorithm's output nor assumes a run succeeds. The fixed-horizon
and PCG grade restrictions differ from the unrestricted caps of carried and reorthogonalized CG.

| Stored endpoint | Supplied resident payload before scratch |
|---|---:|
| Fixed-horizon CG | `n² + 4n` |
| Carried CG | `n² + 4n + 1` |
| Reorthogonalized CG | `n² + 4n` |
| PCG with both dense matrices | `2n² + 5n` |

Scoped history and temporaries are additional scratch. Reorthogonalized CG reserves a residual
history of `cap*n` cells, and its projection budget includes the triangular sum
`cap*(cap+1)/2`. Early exit can execute fewer rounds. The canonical certificates use the
actual transformed tree's complete size-only manifest and peak, including scalar dense
leaves, queries, frames, addressing, allocations and releases. Work and sequential span use
the declared weights on that manifest; supplied matrix and output capacity remain part of
resident memory. These are conservative total bounds in abstract cells, not physical timing
or a sharp adaptive-work claim.

## Rounded guarantees

The [rounded carried certificate](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/Certification.lean)
uses the actual computed residual self-product and returned state. Under its explicit
symmetry, spectral interval, error-budget and precision-window assumptions, it gives residual-gap,
physical-energy and backward-model guarantees. Rounded stopping and the exact Krylov grade
are not interchangeable. A zero computed self-product stops the program; its numerical
meaning is supplied by the rounded theorem's hypotheses.

The [rounded stored certificate](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/StoredCertification.lean)
also provides `Rounded.Stored.scalarAlgorithm`. Its operation signature contains only scalar
operations: all dense matrix applications and sequential BLAS reductions are actual scalar
loops. The raw matrix is symmetric with spectrum in the admitted positive interval. The
matvec allowance is derived from the scalar roundoff and dimension, and the theorem states
the resulting common-error and accumulated-precision inequalities explicitly. Full instruction,
work, span, scratch and resident-memory bounds are recomputed after both lowerings.

The [rounded stored PCG certificate](../../NLAlib/Krylov/CG/HSPCG/Rounded/StoredCertification.lean)
executes a capped zero-start variant using both supplied raw matrices. Initialization copies
`b` into `r`, applies the actual rounded inverse preconditioner to form `z`, and copies `z`
into `p`. A scoped scalar stores `dot(r,z)`. Each round tests that scalar, executes the existing
PCG step, and refreshes the scalar. Repeated dots on identical operands agree because the
scalar implementation has a functional contract; a relative-error interval alone would not
establish this identity. The extra cache refresh is an executed, counted dot product.

For spectral intervals `[a,aUpper]` and `[p,pUpper]`, let `kappaA = aUpper/a` and
`kappaP = pUpper/p`. The common error allowance `E` bounds scalar division, sequential BLAS,
and both dense operator errors. The sufficient continuation conditions include

```text
6*E*aUpper <= a
6*E*pUpper <= p
E*(1024*kappaA*kappaP)^(cap+1) <= 1/2
```

Together with positive lower endpoints and `E <= 1/100`, these input assumptions justify all
divisions. They do not assume a successful run or a nonzero search direction along its
trajectory. Early exit implies a zero computed residual; reaching the cap returns the actual
prefix without asserting convergence. The zero RHS and zero cap are included. The geometric
precision window is conservative: it permits positive rounding error for every finite cap,
but is too restrictive to represent a practical long-run tolerance. The returned physical
vectors match the existing `PCGRun`, so its numerical analysis applies to the same output.

These scalar standard-model certificates describe arithmetic without finite-format overflow
or underflow; native IEEE execution requires a corresponding finite-format model. The
reorthogonalized CG canonical certificates currently cover exact arithmetic.

### Attainable accuracy of the stored iterate

[`exec_scalarProgram_norm_sub_mulVec_le`](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/Accuracy.lean)
bounds the true residual of the stored iterate by `(11k + 8)·E·a′·(‖x‖ + ‖x‖_A/√a)` for a cap
`k ≥ k★(κ, E, 1)`, whether the program reaches the cap or stops on a zero computed residual.
`RunAccuracy` in the same file transfers the residual gap, relative energy-decrement tracking,
the inverse-tridiagonal estimate and minimax convergence on a set containing the eigenvalue
intervals of the backward model.

The conditions `k ≥ k★` and `k²√k·E·κ² ≤ 10⁻⁵` together limit κ. For `u = 2⁻⁵³` and the
smallest admissible `E`, a floating-point evaluation of the two conditions gives:

| n | E | largest κ (to 0.05) | k★ there |
|---:|---:|---:|---:|
| 10 | 1.78·10⁻¹⁴ | 40.4 | 164 |
| 100 | 2.22·10⁻¹³ | 19.25 | 108 |
| 1000 | 7.02·10⁻¹² | 6.85 | 62 |
| 10000 | 2.22·10⁻¹⁰ | 2.3 | 37 |
| 100000 | 7.02·10⁻⁹ | none | |

## Checked sources

- Matrix-free exact certificates: [fixed horizon](../../NLAlib/Krylov/CG/HSCG/Certification.lean),
  [carried](../../NLAlib/Krylov/CG/HSCG/Carried/Certification.lean),
  [reorthogonalized](../../NLAlib/Krylov/CG/Reorth/Certification.lean),
  [PCG](../../NLAlib/Krylov/CG/HSPCG/Certification.lean).
- Exact stored certificates: [fixed horizon](../../NLAlib/Krylov/CG/HSCG/StoredCertification.lean),
  [carried](../../NLAlib/Krylov/CG/HSCG/Carried/StoredCertification.lean),
  [reorthogonalized](../../NLAlib/Krylov/CG/Reorth/StoredCertification.lean),
  [PCG](../../NLAlib/Krylov/CG/HSPCG/StoredCertification.lean).
- [Exact scalar/vector operation model](../../NLAlib/Ops/Profiles/ExactBlas.lean) and
  [scalar dense matrix application](../../NLAlib/Ops/Profiles/StoredDense.lean).

- Rounded stored scalar carried CG: [canonical certificate](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/StoredCertification.lean),
  [stored routine](../../NLAlib/Krylov/CG/HSCG/Carried/Rounded/StoredRoutine.lean).
- Rounded stored scalar PCG: [canonical certificate](../../NLAlib/Krylov/CG/HSPCG/Rounded/StoredCertification.lean),
  [total solver](../../NLAlib/Krylov/CG/HSPCG/Rounded/Solve.lean),
  [continuation from input precision](../../NLAlib/Krylov/FinitePrecision/PCGContinuationPrecision.lean),
  [functional dot evidence](../../NLAlib/Krylov/CG/HSPCG/Rounded/Pairing.lean).
