# Exact shifted QR

Shifted QR computes the spectrum of a nearby matrix from a complex upper Hessenberg input.
The implementation forms Givens rotations, applies shifted QR steps, selects shifts, decouples
blocks and processes a deflation worklist. Complex entries use adjacent real and imaginary
words, stored by columns.

The [closed exact certificate](../../NLAlib/Eigensolvers/ShiftedQR/Exact.lean),
`NLAlib.ShiftedQR.exactAlgorithm`, proves total execution, actual stored output and all five
resource bounds for one fixed Ops program. The
[single-step certificate](../../NLAlib/Eigensolvers/ShiftedQR/Certification.lean),
`exactStepAlgorithm`, separately certifies the mathematical `shiftedQRStep H s` for every raw
matrix and shift, including singular shifts. The
[design page](../design/Eigensolvers-ShiftedQR-Ops.md) describes the implementation interfaces.

## Algorithm and implementation

For positive matrix order, the full solver computes its absolute threshold from the original input, then processes blocks:

```text
tau = delta * frobenius_norm(H)
put the full matrix block on the worklist
while a block remains:
    if it is small enough for the local eigenvalue kernel:
        store its eigenvalues, with multiplicity
    otherwise:
        scan for a coupling of magnitude at most tau
        while no such coupling exists and the iteration cap is not reached:
            obtain trailing-block Ritz candidates
            try repeated shifted QR steps with each candidate, in order
            if none passes the decoupling or contraction test:
                choose a promising Ritz value by inverse-row norm comparisons
                try that value, then stream the exceptional-shift grid
            replace the block by the selected shifted QR result
            scan its couplings again
        split the block at the detected coupling and enqueue its children
```

The input hypotheses ensure that capped decoupling finds a split when a block requires one.
A split logically discards its small coupling; the physical matrix words retain that entry.
The backward-error witness accounts for these discarded couplings.

[Givens coefficients](../../NLAlib/Eigensolvers/ShiftedQR/Coefficients.lean) and
[row/column rotations](../../NLAlib/Eigensolvers/ShiftedQR/RotationLoops.lean) expand into scalar
operations. A zero input pair produces the identity rotation before any division occurs.
[RowSolve](../../NLAlib/Eigensolvers/ShiftedQR/RowSolve.lean) tests pivots and returns either
an exact inverse-row product or a flag certifying singularity.
[HalfNorm](../../NLAlib/Eigensolvers/ShiftedQR/HalfNorm.lean) composes these solves for the
[promising-Ritz search](../../NLAlib/Eigensolvers/ShiftedQR/FindRitz.lean). The enclosing strategy
derives the needed nonsingularity from failed candidate tests; it does not assume every
candidate shift is safe in advance. The
[grid search](../../NLAlib/Eigensolvers/ShiftedQR/GridSearch.lean) stores one candidate at a time.

## Operation model and input hypotheses

The [joint exact operation model](../../NLAlib/Eigensolvers/ShiftedQR/Kernels.lean) contains
real scalar arithmetic, square root, copies, dimension literals, comparisons and bounded
natural-index conversion. Its two spectral primitives are explicit local boundaries:

- `ritz` reads one matrix and returns the requested trailing-block Ritz values, with the
  stated local optimality guarantee.
- `smallEig` reads one small block and returns all its eigenvalues with algebraic multiplicity.

The reference model jointly realizes these contracts using exact roots. Neither a QR step,
shift search, decoupling loop nor worklist is a primitive. Their scalar arithmetic, branching,
addressing, copies and allocation remain visible in the fixed tree.

The [raw problem](../../NLAlib/Eigensolvers/ShiftedQR/DeflationInput.lean) supplies matrix words,
parameter words `[B,theta,alpha,gamma,delta]` and uninitialized root-output capacity. It assumes
an upper Hessenberg matrix with a diagonalization satisfying the eigenvector-conditioning
bound and a positive eigenvalue-separation promise. Its quantitative hypotheses also specify
positive tolerance, admissible Ritz depth and factors, contraction parameter, iteration cap
and grid size. The precise inequalities are
[`ShiftedQRHyps`](../../NLAlib/Matrix/QRIteration/DeflationHypotheses.lean) and
`DeflationAdmissible`. The program computes `tau` itself from the raw tolerance and matrix.

Under these mathematical input assumptions, execution is total and all output slots are
initialized. No premise assumes a successful run, an accepted candidate or an already
computed factorization. Initial Hessenberg reduction is outside this program: the caller
supplies a matrix already in that form.

## Output and resources

For input order N, the returned N complex values represent roots of `H + E`, with algebraic
multiplicity, where

```text
spectral_norm(E) <= (N - 1) * delta * frobenius_norm(H).
```

The [forward certificate](../../NLAlib/Eigensolvers/ShiftedQR/ForwardError.lean),
`exactForwardAlgorithm`, also proves that every stored output lies within
`(B/2)*(N-1)*delta*frobenius_norm(H)` of some eigenvalue of H. This is the directed
Bauer–Fike bound (HD9), using the raw input condition `2*kappa(V) <= B`.
It retains the complete backward guarantee and the same resource bounds. It does not assert
a bijective matching of individual eigenvalues or reverse coverage of the original spectrum.

The [canonical specification](../../NLAlib/Eigensolvers/ShiftedQR/DeflationCertificate.lean)
uses the full instruction manifest `staticCost` of the actual program. Modeled work and
sequential span evaluate that same manifest with the declared kernel charges. Scratch uses
`staticPeak`, including local primitive workspace; resident payload adds the supplied
`2N² + 5 + 2N` real-word cells. Scoped buffers are released and the tape position is unchanged.

Independent [component workspace bounds](../../NLAlib/Eigensolvers/ShiftedQR/Workspace.lean)
count stored real-word scratch, excluding caller-owned inputs and outputs:

| Component | Stored scratch bound |
| --- | ---: |
| One `shiftedStep` | `2N² + 14` |
| Repeated identical shifts or a stored shift list | `4N² + 14` |
| Streaming `searchGridWithScratch` | `4N² + 14` |

The [streaming-grid bound](../../NLAlib/Eigensolvers/ShiftedQR/SearchWorkspace.lean) excludes its
caller-owned candidate and output views. These bounds reuse arenas across iterations, shifts
and grid points; they do not grow with the number of trials. They are component bounds, not a
storage polynomial for the complete worklist. Primitive workspace is charged separately by
the operation model and included in the full certificate.

All arithmetic here is exact. The certificate makes no rounded QR accuracy or IEEE execution
claim; those require their own operation models and numerical analysis.
