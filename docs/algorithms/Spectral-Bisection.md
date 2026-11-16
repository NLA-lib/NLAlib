# Randomized spectral bisection

Spectral bisection approximates the diagonalization of a Hermitian matrix by repeatedly
splitting its spectrum. The implementation stores node matrices, bases and outputs in arenas,
processes one depth at a time, and assembles the children on the way back up.

The fixed [Ops program](../../NLAlib/Eigensolvers/SpectralBisection/Alg.lean) has a checked
[total execution theorem](../../NLAlib/Eigensolvers/SpectralBisection/Solve.lean) and
[output/resource certificate](../../NLAlib/Eigensolvers/SpectralBisection/WorkCertification.lean).
Its returned words equal the existing
[mathematical eigensolver](../../NLAlib/Matrix/FinitePrecision/SpectralBisection.lean)
using the same arithmetic,
matrix routines and tape. Numerical accuracy follows separately from the numerical reference
bound and its [transfer to the counted execution](../../NLAlib/Eigensolvers/SpectralBisection/ProbabilityTransfer.lean).

## Headline statement: cost and accuracy on one event

The strongest statement proved about the spectral bisection program, as one theorem:
[`measureReal_not_accepts_countedSpecification_le`](../../NLAlib/Eigensolvers/SpectralBisection/RunTheorem.lean).

**Theorem.** Let A be a Hermitian n × n complex matrix with ‖A‖₂ ≤ R, n ≥ 2, stored as n²
pairs of words, together with three parameter words: the radius R > 0, a tolerance
0 < ε ≤ 2⁻¹⁵ and a sign accuracy β > 0. Let the depth be L ≥ ⌈log₂(1/ε)⌉ + 5 and the
sign-iteration cap be c. Run randomized spectral bisection on a floating-point machine that is
accurate with unit roundoff u, calling matrix multiplication and QR as primitives whose
declared cost at order j is at most T(j), T monotone and superadditive, on a tape of
independent uniform and standard Gaussian draws rounded to machine words. Fix a failure
probability 0 < θ ≤ 1 and assume the numerical conditions listed below.

Then for every interpretation of the primitives that meets the model, with probability at
least 1 − θ over the tape, all of the following hold for the same run:

1. **Success.** The run completes.
2. **Cost.** Its work and its span are at most

```text
(L+1)·c·(362n³ + 146n² + 222n) + L·(1587n³ + 760n² + 2429n + 305)
  + 1599n³ + 818n² + 2509n + 680 + (L+1)·(2c+11)·T(n)
```

3. **Storage.** Its scratch is at most `6n²L + 32n² + 4nL + 7n + 2L + 24 + W(n)` cells and
   its resident memory at most `4n² + n + 3` more, W(n) the largest declared workspace of a
   matrix primitive at order at most n.
4. **Accuracy.** It leaves in memory a matrix U and a real vector d with

```text
‖A − U·diag(d)·Uᴴ‖₂ ≤ 2·ε·R        (1 − ε/3)²·I ⪯ Uᴴ U ⪯ (1 + ε/3)²·I
```

**Numerical conditions.** With s = `newtonSchulzSteps(θ/(12nL(L+1)), β/(16n))`, the cap must
satisfy c ≥ s, and

```text
β ≤ (L−1)²·ε·√θ / (52·L²·(2L−1)·√(n·min(n,L+1)·min(n,e))·(2√2·√n + √(log(96·n·min(n,L+1)/θ))))
146·n·L·(L+1)·(4μ_M(n) + 10 + 10√n)·u ≤ θ·β
2048·(n + s + 1)·(4μ_M(n) + 10 + 10√n)·u ≤ β
16·(4μ_Q(n) + 4√n·(c_N + 1) + 2μ_M(n) + 1)·u ≤ β
```

where μ_M, μ_Q and c_N are the accuracy constants of the machine's matrix multiplication, QR
and normal sampler. Two further conditions bound the machine's absolute-error floor and its
range bound (`hFloor`, `hBound` in the Lean).

**Scope.** What the statement does and does not say:

- Items 1 to 3 hold on every tape; only item 4 is probabilistic. The event of the theorem is
  the failure of any of the four, so the probability 1 − θ covers them jointly.
- The first four terms of the cost count every instruction that is not a matrix operation,
  each at unit cost, by an upper bound read off the fixed program. A loop over the blocks of a
  level is charged as if every block had order n, so the n³ there overestimates the scalar
  overhead. The last term is the matrix work and uses the actual block sizes.
- T is supplied by the caller; the statement is a bound in terms of it. No fast matrix
  multiplication exponent is asserted.
- The radius R is an input the caller must supply with ‖A‖₂ ≤ R.
- "Accurate floating-point machine" is the hypothesis `FloatMachine.IsAccurate`. It is not IEEE
  arithmetic; a word holds a number of the abstract machine, and a cell is not 64 bits.
- U is nearly unitary, not unitary. Nothing is said about the order of the entries of d.
- The program is one fixed tree for all n, L and c; the covered sizes are a parameter.

**Lean.** The conclusion, verbatim (the hypotheses are those of `countedAlgorithm` and of
`measureReal_not_isApproxDiagonalization_tapeMachine_le`, specialized to the input):

```lean
    P.real {omega | ¬ (countedSpecification M dec mm qr domain admitted matrixWorkspace T).Accepts
      (Dense.resources matrixWork matrixWorkspace) d x
        (exec (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) I
          (Dense.resources matrixWork matrixWorkspace)
          (problem (K := K) domain admitted).formats
          (roundTape roundUnif roundGaussian (ideal omega)) d
          ((problem (K := K) domain admitted).initial d x))
        (fun _ m => StoresApproxDiagonalization dec (inputMatrix d x)
          (2 * inputTolerance dec x * inputRadius dec x) (inputTolerance dec x / 3)
          (2, 0) (3, 0) m)} ≤ theta
```

and the cost of the specification it refers to:

```lean
def operationCount (d : Fin 3 → ℕ) : ℕ :=
  (d 1 + 1) * d 2 * (362 * d 0 ^ 3 + 146 * d 0 ^ 2 + 222 * d 0) +
    d 1 * (1587 * d 0 ^ 3 + 760 * d 0 ^ 2 + 2429 * d 0 + 305) +
    1599 * d 0 ^ 3 + 818 * d 0 ^ 2 + 2509 * d 0 + 680

noncomputable def countedSpecification … :=
  { workSpecification M dec mm qr domain admitted matrixWorkspace T with
    work := fun d => operationCount d + (d 1 + 1) * (2 * d 2 + 11) * T (d 0)
    span := fun d => operationCount d + (d 1 + 1) * (2 * d 2 + 11) * T (d 0) }
```

**Translation notes.**

| In the theorem | In the Lean | Where |
|---|---|---|
| n, L, c | `d 0`, `d 1`, `d 2`; the covered sizes are the parameter `domain`, with `hN : 2 ≤ d 0` | |
| A | `decodeMatrix dec (inputMatrix d x)`: buffer 0, 2n² words | [`Resources.lean`](../../NLAlib/Eigensolvers/SpectralBisection/Resources.lean) |
| R, ε, β | `inputRadius dec x`, `inputTolerance dec x`, `inputBeta dec x`: the three words of buffer 1, decoded | [`RunTheorem.lean`](../../NLAlib/Eigensolvers/SpectralBisection/RunTheorem.lean) |
| probability at least 1 − θ | `P.real {omega \| ¬ … } ≤ theta`: the measure of the failure set is at most θ | |
| all of items 1 to 4 hold | `Specification.Accepts`: the run returned a state, its scratch, count, work, span and memory are within the specification, and the postcondition holds | [`Ops/Probability.lean`](../../NLAlib/Ops/Probability.lean) |
| the cost bound | the `work` and `span` fields of `countedSpecification` | [`OperationCount.lean`](../../NLAlib/Eigensolvers/SpectralBisection/OperationCount.lean) |
| the storage bounds | the `scratch` and `memory` fields of `workSpecification` | [`WorkSpecification.lean`](../../NLAlib/Eigensolvers/SpectralBisection/WorkSpecification.lean) |
| item 4 | `StoresApproxDiagonalization dec A (2εR) (ε/3) (2,0) (3,0) m`: buffers 2 and 3 hold U and d with `IsApproxDiagonalization` | [`ProbabilityTransfer.lean`](../../NLAlib/Eigensolvers/SpectralBisection/ProbabilityTransfer.lean), [`SpectralBisection.lean`](../../NLAlib/Matrix/FinitePrecision/SpectralBisection.lean) |
| the random tape | `roundTape roundUnif roundGaussian (ideal omega)` with `hTape : IsTapeLaw law P ideal` and `hStream`: the ideal tape has independent entries with the uniform and Gaussian laws on their streams, and the program reads their rounded words | [`TapeRounding.lean`](../../NLAlib/Eigensolvers/SpectralBisection/TapeRounding.lean), [`Ops/TapeLaw.lean`](../../NLAlib/Ops/TapeLaw.lean) |
| accurate floating-point machine | `hAcc : FloatMachine.IsAccurate … u floor bound muM muQ cN` | [`Machine.lean`](../../NLAlib/Matrix/FinitePrecision/Machine.lean) |
| T dominates matrix costs | `hMatrix`, `hT`, `hadd` | |
| the numerical conditions | `hDepth`, `hFuel`, `hSteps`, `hBetaMax`, `hSign`, `hStop`, `hDeflate`, `hFloor`, `hBound` | |

The theorem joins three results:
[`countedAlgorithm`](../../NLAlib/Eigensolvers/SpectralBisection/OperationCount.lean) (total
execution with the explicit work), `measureReal_not_accepts_le_of_wordSpecification` (a
reference failure bound controls the failure of the run) and
`measureReal_not_isApproxDiagonalization_tapeMachine_le` (the failure bound of the rounded
reference computation, the setting of Shah's Theorem 4.2). On every tape the stored output
equals that reference computation; this is the postcondition of `countedAlgorithm` itself.

## Algorithm and implementation

At an active node with matrix A, radius R, tolerance ε and depth counter ℓ:

```text
if the node has size one:
    return an identity basis and the real diagonal values
if its window is sufficiently small:
    return an identity basis and zero values
choose a shift using the stored uniform sample and radius R/ℓ
B = sign(A - shift I), using capped Newton–Schulz iteration
P+ = (B + I)/2; P- = -(B - I)/2
k+ = clamp(floor(rounded_trace(P+) + rounded_half), 0, size(A))
if k+ is zero or size(A):
    continue with the corresponding shifted child
otherwise:
    form bases Q+ and Q- by sampled projection and QR
    compress A onto each basis and shift the two child matrices
process the children
assemble their computed bases and shifted values
```

Each scalar operation uses the supplied word function, including the computation of one-half
and accumulation of the trace. Matrix multiplication and full QR are matrix-level primitives.
Hermitian shifts, averages, scaling, conjugate transposes, traces, copies, sampling, metadata
writes and bounded conversions remain visible in the tree. Sign and node procedures expand
through frames; neither is an opaque primitive asserting the algorithm's conclusion.

Complex entries use adjacent real and imaginary words, stored by columns. For root size n,
a size-k node owns k slots in its level, each reserving 2n words. Its square matrix uses
2k² words within that reservation. Mathematical slot intervals supply memory separation and
the checked superadditive kernel-cost lemma.

## Total execution and the operation model

[DenseOp](../../NLAlib/Ops/Catalog/Dense.lean) combines scalar arithmetic, dimension literals,
multiplication/QR and explicit draws. Queries compare decoded scalar words or take their
natural floor. A bounded conversion checks its declared bound.

The generated dense functional model gives one jointly realized collection of local contracts.
`writes_solve` assumes these primitive contracts, readable matrix/parameter blocks, live handles,
separate source blocks, writable separate outputs, and exact decoding of natural literals
through `max n 4`. Outputs may overlap the source regions because the final copies follow all
source reads. Under those premises it guarantees total execution, the mathematical word result,
exact tape advancement and release of scoped scratch. It assumes no successful run.

The canonical problem supplies four separate buffers: raw matrix words, three parameter words,
and empty basis/value output capacity. Its initial memory performs no numerical preprocessing.
`workCertifiedAlgorithm` certifies this same fixed program for every admitted raw input and tape,
with the word result, full instruction count, independent storage bound and matrix-work estimate
below. The admitted root dimensions are at least two; bounded literal exactness and the stated
matrix-cost assumptions are explicit. No premise assumes a WP or successful execution.
The general `certifiedAlgorithm` adapter also supports other supplied resource bounds.

## Resources and their scope

Let n be the root dimension, L the depth parameter and cap the sign-iteration cap.
The certificate uses a monotone superadditive cost T that dominates each matrix primitive's
work at its largest dimension. Each nonleaf node of size k contributes at most
`(2cap + 9)T(k)` matrix-kernel work; reconstruction contributes at most `2T(k)`.
The actual nodes occupy disjoint slot intervals, so their costs sum to at most one root-size
cost per level. The complete bound is

```text
work, sequential span ≤ H(n,L,cap) + (L + 1)(2cap + 11)T(n)
```

Here H is the zero-matrix-work profile applied to `staticBudget`: it retains the conservative
charges for scalar arithmetic, samples, literals, queries, addressing, control flow, frames
and allocation. Matrix work is taken from the actual original-operation count of that same
instrumented execution. The full instruction budget remains conservative. This is a complete
certificate with a partition-sensitive matrix term; it does not assert an optimal total
complexity for fast matrix multiplication.

The matrix-cost domination is global over dimension lists, including empty and all-zero
lists. Superadditivity forces `T(0) = 0`, so matrix costs at those lists must vanish for this
certificate. `manifestAlgorithm` remains available for the full static manifest without
these additional cost assumptions.

The [independent storage bound](../../NLAlib/Eigensolvers/SpectralBisection/StoragePolynomial.lean)
for n ≥ 2 is

```text
scratch  ≤ 6n²L + 32n² + 4nL + 7n + 2L + 24 + E(n)
resident ≤ 6n²L + 36n² + 4nL + 8n + 2L + 27 + E(n)
```

`E(n) = MatrixOp.workspaceEnvelope W n` is one finite maximum of the chosen matrix-workspace
function W over multiplication triples and QR pairs with dimensions at most n. The fixed
program's static-support proof covers every such call, including all bounded query choices.
W needs neither monotonicity nor a global ceiling. Supplied buffers contribute `4n² + n + 3`
abstract cells to resident capacity. Neither storage polynomial grows with cap.

## Randomness, stopping and numerical accuracy

Every downward level draws n uniform words followed by 4n² Gaussian words, including levels
with no active nodes. The complete solver consumes exactly `(L + 1)(n + 4n²)` words. The
coordinate correspondence accounts for any fixed initial tape position. Independence and
distribution belong to the tape law and are separate from functional execution.

The sign iteration returns its current iterate at its cap. At the depth boundary, the program
writes identity bases and zero values. Both cases produce defined outputs; neither alone
establishes numerical accuracy. The numerical reference theorem requires its stated positive
dimension, Hermitian input, radius, precision, depth, sign-cap, sampler and tape-law assumptions.
The probability transfer retains the same actual output and all resource bounds, and includes
execution or resource failure in its failure event without assuming success.

The numerical bridge retains the original analysis's explicit nonnegative absolute-error floor
and its smallness bound. The standard relative-error specialization uses floor zero. A
bounded-exponent model must separately establish its primitive accuracy and range assumptions.
The resource profile counts abstract scalar cells and operation units. A physical IEEE
implementation additionally needs finite encodings, exceptional-value/comparison semantics
and an interpretation/resource proof; this certificate makes no such hardware claim.
