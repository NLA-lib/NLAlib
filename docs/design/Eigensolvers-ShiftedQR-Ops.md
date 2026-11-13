# Exact shifted QR over Ops

## Scope and operation model

The program receives an actual interleaved column-major complex upper Hessenberg matrix.
Its real scalar arithmetic and comparisons are exact. A single shifted QR step computes
`shiftedQRStep H s`, including zero coefficient pairs and singular shifts. The complete
algorithm implements shift selection, decoupling and the deflation worklist. Ritz extraction
and the eigenvalues of a small block are explicit local kernels, as explicit boundaries in the operation model; a whole shifted QR iteration is not a primitive.

The final output of the deflation algorithm is the spectrum of a nearby matrix. Deflation
logically discards small couplings at block boundaries while retaining their physical words;
the backward-error witness accounts for those discarded couplings even in exact arithmetic. The
statement gives the bound `(N-1)*delta*frobNorm H` and its raw spectral separation,
eigenvector conditioning and iteration-budget assumptions. It does not assume execution
succeeds. The finite-precision analysis is outside this development.

## Existing mathematics and representation

The implementation reuses `givensCoeffs`, `givens`, `givensHessenbergState`, `shiftedQRStep`,
`multiShiftedQRStep`, the exact shift-strategy analysis and its explicit iteration cap.
The supporting pure mathematics lives in its subject files:
`Matrix/QRIteration/{ShiftedQRConjugation,FindRitzSolve,ShiftSearch,HessenbergDeflation,
DeflationConditioning,DeflationHypotheses,DeflationRanges}.lean`. Supporting dependencies live in `Matrix/Norms/Frobenius.lean`,
`Matrix/Spectral/{Gershgorin,Normal,Diagonalizable}.lean` and
`Matrix/Perturbation/Inverse.lean` and `Matrix/Pseudoinverse/ConditionNumber.lean`,
with their mathematical statements preserved. No old executor
module is imported.

Storage uses the existing `Ops.EntryCodec.pair`, `MatLayout`, `decodeComplex` and
`decodeMatrix`; there is no competing complex codec. Real/imaginary pairs have width two.
The coefficient blocks encode `c.re,c.im` and `s.re,s.im`, permitting adjacent disjoint views
of one coefficient arena. Arithmetic consumes `Ops.IsScalar M I` and `ExactModel id M`;
queries consume `Ops.IsCmp id I`. All primitive meanings are local and jointly realized in
the final access model.

## Scalar kernels and theorem shapes

`Eigensolvers/ShiftedQR/Coefficients.lean` defines

```lean
coefficientsWithScratch : Ops.Impl Op Tst -- nd=0, inputs U,V,T; outputs C,S
coefficients : Ops.Impl Op Tst            -- nd=0, inputs U,V; outputs C,S
```

The former takes seven caller-owned scratch words; the latter allocates and frees them.
Its total `Writes` theorem, under the scalar model and spatial separation/capacity facts,
returns `givensCoeffs u v` in C/S for the actual input words. The radius-zero branch is
executed before division; nonzero denominators are proved from the chosen branch.

`Eigensolvers/ShiftedQR/Rotation.lean` supplies actual scalar left/right pair rotations,
with inputs C,S,X,Y and outputs X,Y exactly aliased. Both pair outputs are computed in
scratch before either source is overwritten. The mathematical outputs are

```text
left:  (c*x+s*y, -conj(s)*x+conj(c)*y)
right: (x*conj(c)+y*conj(s), -x*s+y*c)
```

`RotationLoops.lean` lifts these kernels to two rows or columns of an interleaved square
matrix. The interface has dimensions `[n,k]`, inputs A,C,S and output A, with `k+1<n`.
Their total `Writes` theorems return the corresponding existing mathematical Givens actions.

`Alg.lean`, `Shift.lean`, `Round.lean`, `Sweep.lean`, `Step.lean` and `Certification.lean` compose these kernels into
one fixed single-shift program. Its headline shape is

```lean
-- Actual input/read/capacity and separation arguments are explicit in the word theorem.
-- No premise asserts that execution succeeds.
shiftedStep_writes ... :
  Ops.Writes .total I tape shiftedStep.body (Ops.Env.frame [n+1] [A,S,Z])
    outputFootprint
    (fun mem => mem.pos = initial.pos ∧
      HoldsMatrix Z (shiftedQRStep H s) mem.store) initial
```

`HoldsMatrix` above denotes the existing pair-codec storage predicate applied to
complex components, not a new mathematical representation. The canonical certificate is
an `Ops.Algorithm` for a raw-matrix/shift problem, with full counts, modeled work/span,
scratch and initial-plus-scratch payload taken from the same actual scalar syntax.

`Problem.lean` supplies the actual matrix and shift word lists plus uninitialized output
capacity. `StepProgram.lean` fixes the scalar tree and full syntactic resource manifest.
The single-step statement admits every raw matrix and shift, including a scalar matrix.
The full deflation theorem additionally uses the upper Hessenberg and spectral assumptions.

`RowSolve` accepts an actual upper Hessenberg matrix and row vector. It returns either the
row-vector inverse product with flag zero, or flag one certifying that the matrix is singular.
Scalar Givens factorization, guarded forward substitution and reverse saved rotations are
actual code. Every division follows a successful nonzero-pivot test. `HalfNorm` composes these
row solves and returns either the exact inverse-polynomial squared norm or an initialized
zero norm with a witnessed singular candidate. Unused shifts are not tested when the exponent
or selected segment is empty. Neither routine is a primitive.

`Search` retains the first accepted candidate. Its partial state requires only flag zero
before any candidate passes, so matrix output can start uninitialized. `GridSearch` streams
the standard square grid through one reusable shift pair. `FinishSearch` computes the defined
promising-shift fallback even if every candidate is rejected. The complete deflation theorem
uses raw conditioning and spectral assumptions to prove progress; it never assumes that a
runtime acceptance flag was set.

`Constants` initializes `[tau,B,theta,alpha,gamma]` from actual raw parameter words
`[B,theta,alpha,gamma,delta]`, computing `tau=delta*frobNorm H` by the proved scalar norm
lowering before the matrix is modified. The enclosing decoupling loop initializes its squared
threshold and contraction power once. No host initializer supplies these derived words.

Further modules implement shift search, capped decoupling and the deflation
worklist, consuming the same local kernels and pure mathematical invariants. Their public
statement retains the actual Ritz/small-eigenvalue kernel boundaries and input assumptions.
There is no legacy registry, compiled-tree approval file, or NumPy emitter.

## Closed certificate and resources

[`exactAlgorithm`](../../NLAlib/Eigensolvers/ShiftedQR/Exact.lean) (in the `NLAlib.ShiftedQR` namespace) closes every implementation
parameter in `deflationAlgorithm`. The program accepts the matrix, five raw parameter words
`[B,theta,alpha,gamma,delta]`, and empty output capacity. The gap promise is mathematical
input to admissibility; it supplies no runtime result. Its assumptions concern the original
Hessenberg matrix, diagonalization and conditioning, spectral separation, positive tolerance,
and the explicit degree, grid resolution and iteration cap. The certificate proves total
execution and the stored output guarantee from those assumptions.

The canonical resource manifest counts this same program's actual scalar, index and spectral
calls, modeled work/span, scratch and resident-plus-scratch payload. Local spectral-kernel
work and workspace charges are explicit operation-model parameters. The initial resident
payload is `2*N*N + 5 + 2*N` real-word cells, including empty output slots.
`Workspace.lean` also proves dimensional bounds directly from the implemented syntax:
a shifted step uses at most `2*N*N + 14` scratch cells, and repeated/list shifts use at most
`4*N*N + 14`, independently of the number of shifts. These component bounds exclude input
and caller-owned output storage and primitive-internal workspace. They are distinct from
the complete program's canonical resource manifest.

## Shared proof machinery

The proofs use `Ops.Logic.Scalar` and `ScalarOutput` for straight-line word blocks, evaluating each
output separately rather than hand-composing dozens of calls. Spatial footprints support separated views and exact in-place aliases. Existing `EntryRows`, `EntryFill`,
`EntryLayout`, `BlockSequence` and `Allocation` rules handle matrix loops, input preservation
and scoped cleanup. Spectral bisection's range/partition mathematics supplies the precedent
for worklist ownership. `Ops.Blas.Map.binaryMap` adds the shared pointwise binary-vector rule;
`Ops.Blas.Pair.linearCombination` adds shared pair arithmetic.
`Ops.EntryCodec.disj_entryBlock_matrix` handles finite matrix-entry separation, and the
`Ops.copyStrided` handles arbitrary leading dimensions using the actual visited entries,
so a diagonal block at the end of a matrix needs no fictitious trailing padding.
`Ops.PairScalar.normSq` shares the three actual calls for component squares and their sum.
The `ScalarIns.applyWrites` append/frame/last-write lemmas keep scalar traces opaque between
short computations. Any repeated
non-mathematical argument is generalized before a
second use; missing shared APIs are placed in the corresponding Ops topic.

The implementation combines the existing mathematical Givens/QR definitions with the
shared memory/scalar APIs above. Legacy executor modules are not import dependencies.

## Validation and review

Review the scalar-kernel interfaces before consumers. Use targeted gated Lean builds and
source checks while integrating. Regenerate `NLAlib.lean` only for complete modules, then
run the full stage check including kernel replay and canonical program inventories before
calling the implementation finished. Do not change checks, baselines, allowlists, CI or pins.
