# Exact shifted QR over Ops

The library represents shifted QR as a fixed scalar/index program, certifies its execution
from raw matrix hypotheses, and gives numerical and resource guarantees for that same run.
The [curated algorithm page](../algorithms/Shifted-QR.md) gives the pseudocode.

## Input hypotheses

Let H be a complex N×N matrix, with N positive. Complex entries occupy adjacent real and
imaginary words in column-major order. The raw buffers contain H, the five parameters
`[B,theta,alpha,gamma,delta]`, and uninitialized capacity for N complex outputs.
The dimensions are `[N-1,m,k,F,M]`. The program computes `tau = delta*frobNorm H` before
changing H. The spectral gap g is a mathematical promise; it supplies no computed data.

[DeflationAdmissible](../../NLAlib/Eigensolvers/ShiftedQR/DeflationInput.lean) and
[ShiftedQRHyps](../../NLAlib/Matrix/QRIteration/DeflationHypotheses.lean) state the domain:

| Hypothesis | Exact condition | Purpose |
| --- | --- | --- |
| Representation | Matrix length `2*N*N`; parameter length 5; output capacity `2*N` | Relates the theorem to the supplied words |
| Matrix structure | `IsUpperHessenberg H` | Givens steps and deflation preserve Hessenberg structure |
| Diagonalization | `IsUnit V`, `H*V = V*diagonal d`, `2*pseudoConditionNumber V <= B` | Starts with conditioning at most B/2, leaving room for deflation perturbations |
| Separation | `g > 0`, `g <= norm(d i-d j)` whenever `i != j` | Controls conditioning after accumulated deflation error |
| Degree | `1 <= m`, `k = 2^m` | Specifies the multishift degree and leaf-kernel cutoff |
| Ritz/strategy factors | `1 <= theta`, `1 <= alpha`, `B^(4*m) <= alpha^(2^m)` | Promising-shift and exceptional-grid analysis |
| Contraction | `0 < gamma < 1` | Quantitative potential reduction |
| Tolerance | `0 < delta` | Defines the absolute decoupling threshold |
| Perturbation smallness | `(N-1)*tau <= g/(8*N*B)` | Keeps every active block's eigenvector condition number at most B |
| Norm control | `(N-1)*tau <= specNorm H` | Bounds active-block norms by twice the initial norm |
| Fuel | `ceil(log(2/delta)/log(1/(1-gamma))) <= F` | Forces a decoupled block before the iteration budget is exhausted |
| Grid resolution | `M = ceil(sqrt(2)/exceptionalSpacing k B theta alpha ((1-gamma)^2))` | Supplies the grid used by the exceptional-shift theorem |

The theorem covers scalar matrices as well. The separate single-step certificate admits
every raw matrix and shift; it computes the mathematical `shiftedQRStep` without requiring
the full solver's conditioning and separation assumptions.

## Program, operation model and oracle boundary

The operation collection is `ScalarOp + (IndexOp + EigenvalueKernelOp)` and queries are
`CmpTst + IdxTst`. Exact real scalar functions, literals, comparisons and bounded natural-index
conversion have jointly realized contracts. The two spectral kernels are declared in
[Kernels.lean](../../NLAlib/Eigensolvers/ShiftedQR/Kernels.lean):

| Primitive | Input and output | Local obligation |
| --- | --- | --- |
| `ritz` | Decoded N×N matrix, requested degree k; k complex values | Length k and theta-optimal Ritz values for Hessenberg inputs with `0 < k < N` |
| `smallEig` | Decoded block; one complex value per row | All characteristic-polynomial roots with algebraic multiplicity |

The reference `exactRoutines` uses exact trailing-block Ritz values and an exact root listing.
`exactRoutinesFor` proves that these same functions satisfy every theta at least one; it
changes the proof, preserving the functions and their root ordering. Calls receive only their
declared matrix words. In the full driver these spectral problems have order at most k.
Kernel work and workspace are explicit model parameters.

Givens formation, rotations, shifted steps, inverse-row solves, shift search, scans, stack
operations and the deflation worklist expand into scalar/index syntax. The local
`RitzSearchContract`, `IterationContract` and `DecouplingContract` are composition theorems for
fixed implementations. [Exact.lean](../../NLAlib/Eigensolvers/ShiftedQR/Exact.lean) substitutes
the concrete implementations into all three layers. `exactAlgorithm` has no remaining
implementation parameter or successful-execution premise.

Choosing the spectral kernels, scalar abstraction level, shift order and storage layout is a
contributor's design decision. The `Ops.Algorithm` definition binds one fixed program to its
raw problem, jointly realized operation model and total output/resource specification. It
also requires the numerical and resource guarantees to concern the same instrumented run.

## Numerical statements and stopping

The backward certificate returns N stored complex values whose multiset is exactly the
characteristic-polynomial roots of H+E, with

```text
specNorm E <= (N-1)*delta*frobNorm H.
```

Splitting a range logically discards a small coupling while retaining its physical words in
the matrix arena. The perturbation witness accounts for these discarded couplings. Output
order follows the worklist; the characteristic-polynomial equality retains multiplicity.

The forward certificate adds a directed nearest-spectrum guarantee: for every stored output,
some eigenvalue lambda of H satisfies

```text
norm(lambda-output[i]) <= (B/2)*(N-1)*delta*frobNorm H.
```

This is the Bauer–Fike consequence underlying HD9,
`DeflationInv.exists_norm_sub_le`. The factor B/2 comes from the raw conditioning hypothesis.
The certificate retains the backward guarantee and the same program and resource bounds.
It makes no bijective matching or reverse-coverage assertion about the original spectrum.

The mathematical rapid-decoupling theorem supplies potential contraction and an iteration cap.
The program proof also establishes the following bridges:

| Required bridge | Checked implementation layer |
| --- | --- |
| Compute derived thresholds from supplied data | `StorageNorm`, `Constants`, `PrepareIteration` |
| Implement the mathematical shift order | `SearchState`, `Search`, `FindRitz`, `GridSearch`, `CompleteSearch` |
| Prove total scalar operations, including singular cases | `Coefficients`, `Pivot`, `RowSolve`, `HalfNorm` |
| Retain convergence hypotheses after deflation | `DeflationConditioning`, `DeflationRanges`, `RangeLarge` |
| Turn progress into a stored final result | `DecoupleState`, `DecoupleLoop`, `WorklistLoop`, `DeflationProgram` |

`RapidDecouplingHyps.iteration_lt` says that an undecoupled state still leaves fuel.
`DecoupleInv.decoupled_at_cap` therefore proves that the capped loop exits decoupled. The
worklist's range invariant proves that its bounded traversal processes every range.
The active-block norm bound lets the local rapid-decoupling proof use relative tolerance
delta/2 against the global absolute threshold. This accounts for `log(2/delta)` in the
full solver's fuel condition.

## File and dependency map

Paths in the following table are relative to `NLAlib/`. Pure matrix mathematics is independent
of the execution layer. Shared memory and scalar rules live in Ops; solver files consume them.

| Layer | Files or file families | Public entry points |
| --- | --- | --- |
| Shared scalar and memory APIs | `Ops/Blas/{Pair,Map,Power,NormSq,BlockCopy}`, `Ops/Logic/{Footprint,Scalar,Functional,EntryRows}` | Pair linear combinations, scalar powers/norms, strided copies, selected-footprint separation |
| QR mathematics | `Matrix/QRIteration/{ShiftedQRConjugation,FindRitzSolve,ShiftSearch}` | Similarity, inverse-row identities, accepted-shift progress and cap |
| Deflation mathematics | `Matrix/QRIteration/{HessenbergDeflation,DeflationConditioning,DeflationHypotheses,DeflationRanges}` | Deflation invariant, roots, forward error, conditioning and quantitative hypotheses |
| Representation and primitives | `Eigensolvers/ShiftedQR/{Storage,Kernels,Problem,DeflationInput}` | Existing pair codec, local spectral contracts and raw problems |
| Scalar shifted step | `Coefficients`, `Rotation`, `RotationLoops`, `Shift`, `Round`, `Sweep`, `Step`, `MultiStep` | `shiftedStep_writes`, repeated/list-shift theorems |
| Guarded inverse-row computations | `Pivot`, `RowSolve*`, `HalfNorm`, `FindRitz*` | Total singular-or-inverse results and promising Ritz search |
| Candidate strategy | `Potential`, `Radius`, `Acceptance`, `Trial`, `Search*`, `Grid*`, `FinishSearch`, `CompleteSearch` | First accepted candidate, streamed grid and defined fallback |
| One strategy iteration | `Iteration*`, `PrepareIteration`, `Constants` | Concrete `iteration` and `iteration_contract` |
| Decoupling and deflation | `Decouple*`, `Scan`, `BlockCopy`, `Worklist*`, `Range*`, `Deflation*`, `Output` | Capped progress, range ownership, complete solver and backward certificate |
| Closed numerical certificates | `Exact`, `ForwardError` | `exactAlgorithm`, `exactForwardAlgorithm` |
| Resources | `StepProgram`, `Workspace`, `SearchWorkspace`, `Cost`, canonical specification | Same-tree manifest, component scratch bounds and an explicit full-work majorant |

Existing support changes belong in `Matrix/Norms/Frobenius` (norm bounds),
`Matrix/Perturbation/Inverse` (small perturbations), `Matrix/Pseudoinverse/ConditionNumber`
(products), `Matrix/Spectral/Gershgorin` (isolated eigenpairs), `Matrix/Spectral/Normal`
(normal block-triangular matrices), and `Matrix/Spectral/Diagonalizable` (diagonalization API).

## Shared proof rules and initialization discipline

`ScalarIns` and `ScalarOutput` describe straight-line word computations. Spatial footprints
permit separate views of one arena and proven exact aliases. Entry/layout rules and
`copyStrided` use the visited entries, including diagonal blocks without trailing padding.
`Fp.Apart.disj_select` separates selected subcollections of an apart footprint list, including
reordered selections; `fp_sub` handles containment in unions. Consumers use these rules in
place of nested disjunction injections.

Three initialization decisions are part of the implementation:

- Candidate state requires only flag zero until a trial is accepted. The output matrix may
  remain uninitialized before then; subsequent trials preserve the first accepted matrix.
- Pivot tests read initialized factor words before division. `RowSolve` returns either the
  inverse-row product or a flag witnessing singularity; `HalfNorm` returns an initialized norm
  and the corresponding singularity witness when needed.
- Half-norm proofs use the selected shift segment. Empty segments and zero exponents perform
  no unused solves. Padded storage outside that segment supplies no additional denominator
  assumptions.

These choices avoid requiring readability of output words before they have been written, or
nonsingularity of shifts the algorithm never uses. The enclosing shift analysis derives the
nonsingularity needed after failed candidate tests.

## G15: conditioning of a deflated block

The proof of Banks–Garza-Vargas–Srivastava, Shifted QR II, Lemma 6.2, claims that every
eigenvector matrix of a block upper-triangular matrix has the same block form. Shared
eigenvalues invalidate that step. For example, the two-by-two identity is diagonalized by
the coordinate-swap matrix, whose leading one-by-one block is zero.

The conditioning statement is valid. The library proves it with a Cholesky argument:
for `M*V = V*D`, factor `(V^-1)ᴴ*V^-1 = Rᴴ*R` with R upper triangular. Then W=RV is unitary,
and `R*M*R^-1 = W*D*Wᴴ` is normal and block upper triangular. A normal block upper-triangular
matrix is block diagonal. Each block is therefore unitarily diagonalizable, and
`V_r = R_rr^-1*U_r` diagonalizes the original block with
`kappa(V_r) <= kappa(R) = kappa(V)`.

[Matrix.BlockTriangular.exists_pseudoConditionNumber_subBlock_le](../../NLAlib/Matrix/QRIteration/DeflationConditioning.lean)
proves this general block result, including shared eigenvalues.
[IsStarNormal.apply_eq_zero_of_blockTriangular](../../NLAlib/Matrix/Spectral/Normal.lean)
supplies the normal-matrix step. Both are machine-checked.

Positive separation is still needed for the perturbation theorem that precedes the block
argument. A small perturbation of a repeated-eigenvalue matrix can be defective: adding a
nonzero strictly upper-triangular entry to the two-by-two identity gives an example.
`exists_pseudoConditionNumber_add_le` keeps conditioning within a factor two when
`norm(E) <= g/(16*N*C)` and the starting condition bound is C. Taking C=B/2 gives the full
solver's threshold `g/(8*N*B)`. This proves the active-block bound B used by decoupling.
G15 is a repaired proof step; the end-to-end theorem retains its explicit gap assumption.

## Resource scope

The canonical specification evaluates the full instrumented program: original scalar/index/
spectral calls, comparisons, bounded queries, address/index expressions, control, frames and
allocation. Kernel work and workspace are charged explicitly. Resident capacity includes
`2*N*N + 5 + 2*N` supplied real-word cells plus scoped scratch.

Independent stored-scratch bounds are `2*N*N + 14` for one shifted step and `4*N*N + 14` for
repeated/list shifts and streamed grid trials. These exclude caller-owned inputs/outputs and
primitive-internal workspace. Complete program scratch includes every allocation and the
chosen kernel workspace. [Cost.lean](../../NLAlib/Eigensolvers/ShiftedQR/Cost.lean) exposes a full-work expression.
Set `b = N+m+k+F+M+1`. Let K(L) be the finite maximum of both supplied spectral costs over
all dimension lists of length at most two with entries at most L. The complete program has

```text
modeled work, sequential span <= 17109 * b^14 * (1 + K(b^5)).
```

The coefficient 17109, work degree 14, call-dimension degree 5 and maximum call arity 2 come
from the fixed instrumented tree. The generic analysis preserves separate index-slot bounds;
sequential code adds coefficients, loops add iteration degrees, and frames substitute each
slot separately. The finite kernel maximum admits arbitrary nonmonotone costs, includes
malformed shapes conservatively, and imposes no unbounded global ceiling.

This is a conservative full-program bound, not an optimized NLA complexity. The overhead
`17109*b^14` is polynomial in the five explicit natural input values; the whole expression
need not be polynomial when the supplied kernel costs are not. Since `k = 2^m`, this is no
assertion of polynomial dependence on m alone, bit length or accuracy. F and M remain explicit
inputs.

`exactAlgorithmWithPolynomialWork` retains the original full count budget, scratch, resident
memory, backward guarantee and HD9 forward guarantee, and exposes this expression in its
work/span fields. Its run is identified with the original run by deterministic execution.
The shared machinery is in [Ops-PolynomialWork.md](Ops-PolynomialWork.md).

## What is not certified

- Hessenberg reduction from a general dense input.
- Rounded arithmetic, finite-exponent range safety, overflow/underflow or physical IEEE execution.
- An implementation or physical elapsed-time bound for the two local spectral primitives.
- Eigenvectors, sorted output, or a bijective perturbation matching of individual eigenvalues.
- A gap-free full-solver theorem or convergence for inputs outside the admitted hypotheses.
- A tight end-to-end asymptotic complexity or a simplified full-worklist storage polynomial.

## Validation and review

The solver and shared Ops rules are validated together by the full stage check: strict
builds, axiom audit, environment linters, kernel replay, fixed-program inventory,
import/freshness checks, references, constants, LaTeX and contribution rules.
The review description states the hypotheses, conclusions, primitive boundaries and resource
scope. Checks, baselines, allowlists, CI and build pins remain unchanged.
