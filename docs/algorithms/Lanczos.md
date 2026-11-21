# Lanczos

Lanczos builds a basis for a Krylov space and a small symmetric tridiagonal representation
of a symmetric operator. NLAlib separates the algorithm variant, the operation contracts,
the implementation of those operations, and the mathematical conclusions about stored output.
An eigenvalue theorem interprets the stored tridiagonal mathematically; the Lanczos program
itself does not run an eigensolver.

## Headline statements: scalar Lanczos in rounded arithmetic

Two theorems, one per program, are the strongest statements proved about a Lanczos program.
The other certificates on this page are for other operation models and are listed under
"Canonical certificates".

Both are for a real symmetric n × n matrix A stored entry by entry, a real vector b of length
n and an iteration cap k, on any scalar machine in the standard model with unit roundoff u,
with every matrix-vector product and vector operation written out as scalar loops. Both use an
error allowance E ≤ 1/100 with

```text
((1+u)^(2n) − 1)·√n ≤ E      one row-by-row matrix-vector product
(1+u)^n − 1 ≤ E               one sequential dot product of length n
(1+u)² − 1 ≤ E                one vector update
u ≤ E                         one scaling
```

In both, *every run* means every admitted input, every interpretation of the scalar
operations and comparisons that satisfies the model's contracts, and every tape; the program
is one fixed tree for all n and k; *instructions* are scalar operations, comparisons and every
structural instruction, each of unit cost, counted by an upper bound read off the program; and
the standard model has no overflow or underflow and exact comparisons, so it is not IEEE
arithmetic.

### Lanczos without reorthogonalization

[`exec_scalarProgram_work_le_and_ritzResidual`](../../NLAlib/Krylov/Lanczos/Rounded/ScalarTheorem.lean).

**Theorem.** Every run of the Lanczos recurrence (Paige's ordering) started from b succeeds,
and:

1. **Cost.** It executes at most `33·n²·k + 153·n·k + 302·k + 58·n + 179` instructions.
2. **Output.** It performs some m ≤ k steps and leaves in memory v₁, …, v₍m+1₎ (zeros after
   them), α₁, …, αₘ, β₁, …, βₘ and the computed norm of b. These are the values of a Lanczos
   recurrence in which each operation is exact up to an error of at most E times its operands
   and |‖vⱼ‖² − 1| ≤ E. If m < k, the last computed βₘ (for m = 0, the computed norm of b) is
   exactly zero.
3. **Ritz residuals.** If k > 0, b ≠ 0 and k·E ≤ 1/100, there is a length q, 1 ≤ q ≤ k, with
   stored β_q = 0 when q < k, such that every θ and unit vector y with T_q y = θ y satisfy

```text
‖A V_q y − θ V_q y‖ ≤ √(1+E)·β_q·|y_q| + 6·q·√q·E·‖A‖₂
```

**Scope.** No orthogonality of the stored vectors is claimed. V_q y need not be close to a
unit vector, so the residual bound alone does not place θ near an eigenvalue of A. In the
proof q is the number m of steps performed; the statement does not record that.

**Lean.** The conclusion, verbatim (hypotheses `hM : StdModel u id M`, `hu : 0 ≤ u`,
`hprec : ∀ d, domain d → Lanczos.Rounded.Precision … (E d) (Blas.seq.err u) (d 0)`, an input
`x`, an interpretation `I` meeting `RoundedScalarBlas.model`, a tape `τ`):

```lean
    ∃ st, exec scalarProgram I RoundedScalarBlas.resources (problem domain admitted).formats τ d
        ((problem domain admitted).initial d x) = some st ∧
      RoundedScalarBlas.resources.work st.cost ≤
        33 * d 0 ^ 2 * d 1 + 153 * d 0 * d 1 + 302 * d 1 + 58 * d 0 + 179 ∧
      ∃ vs cs, st.mem.store.readBlock 2 0 ((d 1 + 1) * d 0) = some vs ∧
        st.mem.store.readBlock 3 0 (2 * d 1 + 2) = some cs ∧
        Lanczos.Rounded.Output id (StoredProblem.matrix x) (decv id (d 0) x.val.1.2) (E d) (d 1)
          vs cs ∧
        (0 < d 1 → decv id (d 0) x.val.1.2 ≠ 0 → (d 1 : ℝ) * E d ≤ 1 / 100 →
          Lanczos.Rounded.RitzResidual id (StoredProblem.matrix x) (E d) (d 1) vs cs)
```

**Translation notes.**

| In the theorem | In the Lean | Where |
|---|---|---|
| n, k | `d 0`, `d 1`; the covered sizes are the parameter `domain` | |
| A, b | `StoredProblem.matrix x` (buffer 0), `decv id (d 0) x.val.1.2` (buffer 1) | [`StoredProblem.lean`](../../NLAlib/Krylov/Lanczos/StoredProblem.lean) |
| A symmetric | part of being an input (`StoredProblem.extra true`) | same file |
| the conditions on E | `Lanczos.Rounded.Precision em u E e n` with `em = ScalarProducts.roundoff u n * √n` and `e = Blas.seq.err u`; it also asks `e.dot n + u * (1 + e.dot n) < 1` | [`Rounded/Precision.lean`](../../NLAlib/Krylov/Lanczos/Rounded/Precision.lean) |
| the stored vectors and coefficients | `vs` is buffer 2, (k+1)·n words, vector j at offset (j−1)·n; `cs` is buffer 3, 2k+2 words: α at 0…k−1, β₀…β_k at k…2k, the norm of b at 2k+1 (`PackedOutput`) | [`Rounded/Output.lean`](../../NLAlib/Krylov/Lanczos/Rounded/Output.lean) |
| item 2 | `Lanczos.Rounded.Output`: `∃ done ≤ cap, ∃ z, Outcome A rhs E done z ∧ PackedOutput … ∧ (done < cap → … = 0)`; `Outcome` holds the `LanczosRun` | [`Rounded/State.lean`](../../NLAlib/Krylov/Lanczos/Rounded/State.lean), [`LanczosRun.lean`](../../NLAlib/Krylov/FinitePrecision/LanczosRun.lean) |
| item 3 | `Lanczos.Rounded.RitzResidual`; `6·q·√q` is `lanczosResidualFactor q` | [`Rounded/Ritz.lean`](../../NLAlib/Krylov/Lanczos/Rounded/Ritz.lean) |
| V_q, T_q | `basisMatrix id n vs q`, `tridiagonalMatrix id k cs q` | [`Spec.lean`](../../NLAlib/Krylov/Lanczos/Spec.lean) |

The theorem joins the certificate
[`scalarCountedAlgorithm`](../../NLAlib/Krylov/Lanczos/Rounded/OperationCount.lean) with
`Lanczos.Rounded.Output.ritzResidual` applied to the output of the same run.

### Lanczos with full reorthogonalization

[`exec_scalarProgram_work_le_and_spectral`](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/ScalarTheorem.lean).

**Theorem.** Every run of the Lanczos recurrence started from b, in which each new vector is
orthogonalized twice against all stored vectors before it is normalized, succeeds, and:

1. **Cost.** It executes at most
   `33·n²·k + 92·n·k² + 152·k² + 269·n·k + 581·k + 58·n + 179` instructions.
2. **Output.** It performs some m ≤ k steps and leaves in memory v₁, …, v₍m+1₎, the
   coefficients αⱼ, βⱼ and, for each step, the norm νⱼ of the new vector before
   reorthogonalization. If m < k, the last computed βₘ (or the computed norm of b) is exactly
   zero.
3. **Orthogonality and Ritz values.** Take any threshold 0 < τ ≤ 1 and tolerances
   0 ≤ η, c ≤ 1/100 that satisfy the three conditions below. Let r ≤ m be the number of
   leading steps with βⱼ > τ·νⱼ, let δ = 2(2c + 2(η+c)²/τ + E) + E + 3c and
   e = 100·(r+1)·δ·‖A‖₂. If r ≥ 1, then with θ₀ ≥ … ≥ θ₍r−1₎ the eigenvalues of T_r,

```text
‖V_rᵀ V_r − I‖₂ ≤ η
λ₍i+n−r₎(A) − e ≤ θᵢ ≤ λᵢ(A) + e        for i < r
```

The three conditions involve only n, k, u and E:

```text
for j < k:  (j+2)·ε_dot·(1+η)² + ((1+ε_axpy)^(j+1) − 1)·(1 + (j+1)·(1+ε_dot)·(1+η)²) ≤ c
√(3(k+1)) · 2(2c + 2(η+c)²/τ + E) ≤ η
δ ≤ 1/100
```

with ε_dot = (1+u)^n − 1 and ε_axpy = (1+u)² − 1.

**Scope.** The bounds hold on the prefix of r steps without severe cancellation in the
reorthogonalization (βⱼ > τ·νⱼ), which is read off the stored output. The prefix can be
shorter than the run, and is empty when β₁ ≤ τ·ν₁; nothing is claimed beyond it. τ, η and c
are parameters of the analysis, not of the program: the statement holds for every admissible
choice, and it does not say which choices are admissible at a given n, k and u. The
eigenvalues are indexed from 0 in non-increasing order.

**Lean.** After the same first two conjuncts as above (with cost
`33 * d 0 ^ 2 * d 1 + 92 * d 0 * d 1 ^ 2 + 152 * d 1 ^ 2 + 269 * d 0 * d 1 + 581 * d 1 + 58 * d 0 + 179`
and coefficient block `3 * d 1 + 2`), the conclusion is, verbatim:

```lean
        ∀ thr η c : ℝ, 0 < thr → thr ≤ 1 → 0 ≤ η → η ≤ 1 / 100 → 0 ≤ c → c ≤ 1 / 100 →
          (∀ j < d 1, (j + 1 + 1 : ℝ) * (Blas.seq.err u).dot (d 0) * (1 + η) ^ 2 +
            ((1 + (Blas.seq.err u).axpy) ^ (j + 1) - 1) *
              (1 + (j + 1 : ℝ) * (1 + (Blas.seq.err u).dot (d 0)) * (1 + η) ^ 2) ≤ c) →
          Real.sqrt (3 * ((d 1 : ℝ) + 1)) * (2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d)) ≤ η →
          2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d) + E d + 3 * c ≤ 1 / 100 →
          ∃ done ≤ d 1, ∃ z : Lanczos.Rounded.Values (d 0), ∃ nus : ℕ → ℝ,
            Lanczos.Reorth.Rounded.History id (StoredProblem.matrix x)
              (decv id (d 0) x.val.1.2) (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u
              (E d) (Blas.seq.err u) done z nus ∧
            Lanczos.Reorth.Rounded.PackedOutput id (d 1) done z nus vs cs ∧
            (done < d 1 → (if done = 0 then z.initialNorm else z.beta done) = 0) ∧
            ∃ r ≤ done, (∀ j < r, thr * nus (j + 1) < z.beta (j + 1)) ∧
              (r < done → z.beta (r + 1) ≤ thr * nus (r + 1)) ∧
              (r = 0 ∨
                (specNorm ((Lanczos.basisMatrix id (d 0) vs r)ᵀ *
                    Lanczos.basisMatrix id (d 0) vs r - 1) ≤ η ∧
                  ∀ i < r,
                    eigenvalue (StoredProblem.matrix x) (i + (d 0 - r)) -
                        100 * ((r : ℝ) + 1) *
                          (2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d) + E d + 3 * c) *
                          specNorm (StoredProblem.matrix x) ≤
                      eigenvalue (Lanczos.tridiagonalMatrix id (d 1) cs r) i ∧
                    eigenvalue (Lanczos.tridiagonalMatrix id (d 1) cs r) i ≤
                      eigenvalue (StoredProblem.matrix x) i +
                        100 * ((r : ℝ) + 1) *
                          (2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d) + E d + 3 * c) *
                          specNorm (StoredProblem.matrix x)))
```

**Translation notes.** As for the first theorem, and:

| In the theorem | In the Lean | Where |
|---|---|---|
| m, the steps performed | `done` | |
| τ | `thr` (the tape is `τ` in the Lean) | |
| αⱼ, βⱼ, νⱼ, vⱼ | `z.alpha j`, `z.beta j`, `nus j`, `z.v j`, tied to the stored words `vs`, `cs` by `PackedOutput` | [`Reorth/Rounded/Output.lean`](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/Output.lean) |
| item 2 | `History`: the initialization followed by `done` executed steps, each with its local rounding witnesses | [`Reorth/Rounded/State.lean`](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/State.lean) |
| r is the longest admissible prefix | the two clauses `∀ j < r, thr * nus (j+1) < z.beta (j+1)` and `r < done → z.beta (r+1) ≤ thr * nus (r+1)` | |
| the three conditions | the three implications before `∃ done`; `(Blas.seq.err u).dot n` is ε_dot and `.axpy` is ε_axpy | [`Profiles/BlasCert.lean`](../../NLAlib/Ops/Profiles/BlasCert.lean) |
| λᵢ(A), θᵢ | `eigenvalue A i`, `eigenvalue (tridiagonalMatrix id k cs r) i` | |

The theorem joins the certificate
[`scalarCountedAlgorithm`](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/OperationCount.lean)
with `Lanczos.Reorth.Rounded.Output.exists_spectral_prefix` and, for the run it exhibits,
`NLAlib.LanczosReorthRun.specNorm_transpose_mul_self_sub_one_le` and
`NLAlib.LanczosReorthRun.eigenvalue_sub_le_eigenvalue_tridiagonal`.

## Algorithm variants

| Variant | Order of an active round | Additional stored output |
|---|---|---|
| Ordinary Lanczos | Paige's three-term update, then normalization | Basis and tridiagonal coefficients |
| Full reorthogonalization | The same update, two classical Gram–Schmidt passes, then normalization | The norm of each residual before the passes |

Both variants initialize output tails to zero, accept an iteration cap, and stop when the
computed self-dot used for normalization is no longer positive. In exact arithmetic this
means a zero residual. Successful execution follows from the
operation and input hypotheses of their total-correctness theorems. The theorem statements
do not assume that an execution has already succeeded.

In exact arithmetic, the two variants produce the same ordinary basis and tridiagonal prefix
for symmetric matrices. Their programs and rounded computations remain distinct.

## Ordinary Lanczos pseudocode

The operations below are abstract. `dot`, `axpy`, `matvec`, square root and normalization have
the contracts selected by the operation model. Here `axpy(a,x,y)` means `y + a*x`.

```text
zero the requested basis and coefficient arrays
previous = 0
sigma = dot(b, b)
if sigma > 0:
    input_norm = sqrt(sigma)
    current = b / input_norm
else:
    return initialized zero outputs
beta = 0

for j = 1, ..., cap, while sigma > 0:
    work = matvec(current)
    work = axpy(-beta, previous, work)
    alpha[j] = dot(current, work)
    work = axpy(-alpha[j], current, work)
    sigma = dot(work, work)
    previous = current
    if sigma > 0:
        beta[j] = sqrt(sigma)
        next = work / beta[j]
    else:
        beta[j] = 0
        next = 0
    store next as the next basis column
    current = next
    beta = beta[j]
```

The implementation guards square roots and division with the positive self-dot branch.
Zero input, zero cap and early breakdown have explicit output meanings. A zero cap still
initializes and, for nonzero input, normalizes the initial basis column.

## Reorthogonalization pseudocode

The full-reorthogonalized variant inserts the following after the raw three-term residual and
before the final self-dot and normalization:

```text
save sqrt(dot(work, work)) if its self-dot is positive; otherwise save zero
repeat twice:
    for every current basis column i:
        coefficient[i] = dot(basis[i], work)
    for every current basis column i:
        work = axpy(-coefficient[i], basis[i], work)
```

Each classical pass forms all coefficients before applying its updates. The second pass uses
the vector produced by the first pass. Coefficient scratch is reused between the passes and
released on return. Local rounded pass results retain the actual coefficient witnesses even
though the program discards their words.

## Operation models and stored implementations

The [ordinary](../../NLAlib/Krylov/Lanczos/StoredCertification.lean) and
[reorthogonalized](../../NLAlib/Krylov/Lanczos/Reorth/StoredCertification.lean) exact stored
certificates declare four raw buffers: the dense matrix, right-hand side, basis capacity and
coefficient capacity. A fixed context transformation forwards the matrix capability through
every procedure. Each matrix application executes scalar multiply/add loops; the target
operation model retains exact scalar and BLAS1 names and has no matrix-vector primitive.
The supplied matrix words are decoded directly, without preprocessing or an implicit oracle.

Ordinary stored Lanczos returns the exact pure recurrence for every raw square matrix and
right-hand side. Identifying that recurrence with symmetric Lanczos and its spectral results
uses the additional symmetry hypotheses of those results. The reorthogonalized stored
certificate explicitly admits Hermitian raw matrices. Both allow any cap, empty dimension,
zero input and early breakdown, retain the packed zero tails, and return with only the four
supplied buffers. They do not assume a successful run.

Choosing the three-term or two-pass algorithm is separate from choosing a matrix-free
operator, a stored dense implementation, or a scalar implementation of BLAS. Exact agreement
of outputs does not identify the rounded computations of these different programs.


| Choice | Meaning |
|---|---|
| Exact matrix-free operations | Exact scalar arithmetic, BLAS1 and matvec contracts |
| Exact stored dense implementation | Declared raw matrix data, scalar dense matvec loops and exact BLAS1 |
| Rounded stored scalar implementation | Raw matrix data and sequential vector operations execute scalar loops; matvec and BLAS errors follow from the scalar model |
| Abstract rounded BLAS and matvec | Scalar relative-error model, explicit BLAS error allowances, and an independent normwise matvec allowance |
| Sequential standard scheme | The BLAS allowances are proved from sequential reductions in the scalar standard model |
| Pairwise standard scheme | The allowances are proved from pairwise reductions, with the declared recursion-depth applicability condition |

The scalar standard model has unbounded exponents. In a matrix-free model, matvec accuracy is a separate assumption:
`norm(A*v - computed) ≤ em * specNorm(A) * norm(v)`. The dot-product contract scales its error
by `sum(abs(x[i]*y[i]))`; it is not a relative-error promise with respect to a possibly
cancelling dot-product result. Copy is exact. Storage format, arithmetic behavior and matvec
accuracy are separate choices. These models do not assert a native IEEE implementation.

## Operation counts and storage

For vector dimension `n` and cap `k`, the following are upper bounds on abstract calls.
Early termination can use fewer calls. Initialization is included.

| Operation | Ordinary | Full reorthogonalization |
|---|---:|---:|
| Matvec | `k` | `k` |
| Dot product of length n | `1 + 2k` | `1 + 3k + k(k+1)` |
| AXPY of length n | `2k` | `2k + k(k+1)` |
| Vector copy | `1 + 2k` | `1 + 2k` |
| Vector normalization by a scalar | `1 + k` | `1 + k` |
| Square root | `1 + k` | `1 + 2k` |
| Scalar negation | `2k` | `2k + k(k+1)` |
| Literal zero | `(k+2)n + 2k + 2` | `(k+2)n + 3k + 2` |
| Positivity query | `1 + 2k` | `1 + 3k` |

The basis output contains `(k+1)n` words. The coefficient output contains `2k+2` words for
ordinary Lanczos and `3k+2` words with reorthogonalization. The input contains `n` words.
Ordinary scoped scratch contains `2n+2` words plus the maximum declared primitive workspace.
The reorthogonalized workspace bound is `2n+k+3` words plus its declared primitive workspace
envelope. These quantities distinguish resident inputs and outputs from additional scratch.
The displayed workspace formulas concern the matrix-free source trees and their declared
primitive workspace. Stored dense programs additionally supply `n²` matrix cells and use
their own transformed tree's full peak, including the scalar matvec temporary.

The closed call budgets are `solveCount` in each variant's `Alg.lean`; `stmtCost_solve`
proves that each is the corresponding static call budget. Primitive costs depend on the
chosen operation model. Counting one matvec does not declare a dense matrix multiplication
unit-cost, and a matrix captured by an oracle is not certified as free physical storage.
Canonical certificates additionally account for structural instructions, query workspace,
work, span and total modeled memory in the same execution. Their total instruction manifests
are conservative syntactic bounds; a registered closed-form total-work target is a separate
statement. The original operation counts and resident/scratch formulas are explicit. Abstract `.cell` words need a
representation bridge before their charges describe physical machine storage.

## Reading the guarantees

Exact stored basis prefixes equal the canonical Arnoldi basis. Orthonormality applies only
through the Krylov grade; initialized zero padding is not an orthonormal extension.
Stored tridiagonal prefixes give the projected operator and support Ritz-value bounds with
the stated spectral and starting-vector hypotheses.

The ordinary rounded output identifies one actual active run, including every stored vector
and coefficient. Its bounds include matvec rounding and the actual initial-normalization
defect. A rounded Ritz residual bound controls the physical vector formed from the stored
basis and a unit tridiagonal eigenvector. The physical vector is not automatically unit;
turning its residual into an eigenvalue-error estimate requires the corresponding norm
information. Backward-error bounds use their explicit accumulated-precision conditions.

The rounded reorthogonalized total solver retains the actual two-pass intermediate vectors,
coefficient witnesses, local error bounds and saved preorthogonalization norms. Its complete
output uses exactly the executed rounds and initialized zero tails. The proved two-pass
orthogonalization interface derives its numerical allowance from the actual dot and AXPY
chains, with an explicit small-error budget. A small residual-representation defect alone
does not prove strong mutual orthogonality or justify substituting a different matrix-update
implementation's constants. Stronger numerical conclusions use their proved hypotheses.

## Source map

- [Ordinary program](../../NLAlib/Krylov/Lanczos/Alg.lean)
- [Reorthogonalized program](../../NLAlib/Krylov/Lanczos/Reorth/Alg.lean)
- [Packed exact outputs](../../NLAlib/Krylov/Lanczos/Spec.lean)
- [Exact total solver](../../NLAlib/Krylov/Lanczos/Exact.lean)
- [Exact reorthogonalized total solver](../../NLAlib/Krylov/Lanczos/Reorth/Exact.lean)
- [Rounded ordinary total solver](../../NLAlib/Krylov/Lanczos/Rounded/Solve.lean)
- [Standard operation model](../../NLAlib/Krylov/Lanczos/Rounded/Models.lean)
- [Rounded backward error](../../NLAlib/Krylov/Lanczos/Rounded/Stability.lean)

- [Exact stored-output Ritz bounds](../../NLAlib/Krylov/Lanczos/Basis.lean)
- [Exact reorthogonalized stored-output bounds](../../NLAlib/Krylov/Lanczos/Reorth/Basis.lean)
- [Rounded physical Ritz residual](../../NLAlib/Krylov/Lanczos/Rounded/Ritz.lean)
- [Rounded reorthogonalized total solver](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/Solve.lean)
- [Reorthogonalized standard models](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/Models.lean)
- [Actual two-pass error bound](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/Orthogonality.lean)

## Canonical certificates

The exact stored endpoints are `Lanczos.Stored.algorithm` and
`Lanczos.Stored.Reorth.algorithm`. Their specifications identify the actual packed outputs
with the existing exact `Output` relations, preserve tape position, and assert cleanup back
to four buffers. Their complete count, work, sequential-span and scratch budgets are computed
from the actual transformed syntax. Resident bounds include matrix data, RHS, every basis
slot and every coefficient slot. These full manifests are conservative size-only accounting;
they are not a sharp adaptive-work bound.

The rounded stored endpoints are `Lanczos.Stored.Rounded.scalarAlgorithm` and
`Lanczos.Stored.Reorth.Rounded.scalarAlgorithm`. Both target a signature containing only scalar
operations. Matrix words remain explicit inputs; every matvec and sequential BLAS operation
executes its scalar implementation. The matvec allowance follows from the actual streamed
multiply/add recurrence and the scalar roundoff, rather than a separate accuracy callback.
Their precision conditions apply to admitted dimensions, while raw matrix admission carries
symmetry. They retain the actual packed rounded output, early breakdown and complete resource
bounds on the final lowered tree. These standard-model certificates do not claim native IEEE behavior.


Both ordinary and fully reorthogonalized Lanczos have `Certification.algorithm` constructors.
They use a fixed program and a jointly realized standard operation model. Their specifications
combine the actual rounded output with an independently computed, size-only instrumented
manifest. Work and sequential span apply the declared weights to that complete manifest.
Resident memory includes every supplied input and output slot, including uninitialized slots;
scoped scratch and the core query reservation are added separately.

The ordinary `Certification.ritzAlgorithm` strengthens the numerical postcondition with the
physical Ritz residual result using `Algorithm.mapPost`. It retains the same program and every
resource bound. Zero cap and zero input have their explicit original outcomes.

- [Exact stored ordinary certificate](../../NLAlib/Krylov/Lanczos/StoredCertification.lean)
- [Exact stored reorthogonalized certificate](../../NLAlib/Krylov/Lanczos/Reorth/StoredCertification.lean)
- [Ordinary canonical certificate](../../NLAlib/Krylov/Lanczos/Certification.lean)
- [Reorthogonalized canonical certificate](../../NLAlib/Krylov/Lanczos/Reorth/Certification.lean)
- [Canonical Ritz consequence](../../NLAlib/Krylov/Lanczos/RitzCertification.lean)

These base certificates describe the abstract BLAS trees. Proved BLAS implementations derive
the model's accuracy contracts, while a canonical certificate for a scalar lowering separately
checks the fully lowered tree and recomputes its full instruction/workspace manifest.

The [actual sequential scalar certificate](../../NLAlib/Krylov/Lanczos/LinkedCertification.lean)
checks the precise tree produced by the sequential implementation table. Its reduction error
budgets come from the scalar unit roundoff, independently of the high-level BLAS scheme. Its
Ritz postcondition is strengthened by `SequentialCertification.ritzAlgorithm`, preserving that
lowered tree's own full resource specification. Pairwise profile transfer retains its explicit
applicability and conditional budgets; this sequential certificate does not certify a different
pairwise scalar tree.

For rounded full reorthogonalization, the strongest run interface applies to the longest
leading prefix satisfying the selected strict test `tau * saved_raw_norm < beta`. This is an
analysis of the returned data; the program still uses its original self-dot stopping rule.
The prefix may be empty or shorter than the executed history. The next excluded step has
`beta <= tau * saved_raw_norm`. Every retained numerical-run parameter and vector/coefficient
sequence refers to the same archived data. Size-only fixed-point and recurrence precision
windows support spectral bounds for the nonempty selected tridiagonal.

- [Actual admissible-prefix run](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/Stability.lean)
- [Actual rounded prefix spectral bound](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/Spectral.lean)

- [Rounded stored scalar ordinary certificate](../../NLAlib/Krylov/Lanczos/Rounded/StoredCertification.lean)
- [Rounded stored scalar reorthogonalized certificate](../../NLAlib/Krylov/Lanczos/Reorth/Rounded/StoredCertification.lean)
