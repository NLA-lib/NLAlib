# Second-wave independent review

2026-11-24, sprint worktree based on `7cbea9d1`. Review was read-only, separate from the
implementation owners. This record summarizes the mathematical and storage findings;
build/audit/kernel results are recorded in the delivery report.

## Shared update and full factorizations

The LU worker reviewed the final shared Schur step, full Cholesky driver and both factorization
certificates. No material defect was found. The coefficient `(-1)/pivot` correctly turns the
rank-one kernel's addition into elimination subtraction; both pivot operands are saved before
updating the matrix. The final block frame accounts for all workspace pops.

The Cholesky driver copies its input before writing the output, so original source/factor
overlap is admissible. SPD is used on the exact `gaussState` pivots; the result is the existing
canonical `choleskyLower`, with no assumed local execution trace. Empty dimensions require
no matrix or factor handle. Its exact implementation uses Gaussian saved-pivot residual
updates, so future numerical analysis must use that instruction order.

The LU driver assumes every exact elimination pivot is nonzero. Output factor handles are
distinct; retained-source separation is guarded by positive dimension. This lets an empty
matrix use absent source handles without pretending an allocation already exists. The
decoded LU certificate requires disjoint factor windows so the second write cannot invalidate
the first factor. Both exact instances have zero error, with arithmetic assumptions outside
the generic certificate.

## Upper/adjoint adapters and full system solves

The Cholesky worker reviewed all three triangular adapters and both full solve consumers.
No material numerical or footprint defect was found. Reverse/transposed addresses solve the
claimed systems; the finite-equivalence transport maps the RHS and solution in inverse
directions. Conjugation accuracy is explicitly through real decoding, not an unproved complex
floating-point model. Fully initialized operand blocks are packed before output copy-back,
so overlapping original matrix/RHS operands are safe. Packed workspace is an explicit cost.

Both complete system solvers execute the factorization, preserve the original RHS while writing
fresh factors, run the two triangular solves, collapse the two RHS writes and release factor
storage. Their statements conclude the original system `A *ᵥ x = b`, not merely two supplied
factor systems. Empty cases use guarded handle bounds. The LU worker separately reviewed the
final `exec_luSolve` and zero-error certificate, finding no material issue.

## Partial pivot operation

The LU worker reviewed the final generic `partialPivot`. It actually scans the active suffix,
converts the stored relative index through the bounded binder, swaps full rows and records
the absolute row. The exact-index bound through the matrix dimension covers both conversion
and the absolute literal. All-zero suffixes select the first active row without dividing.
Preliminary and final index writes are commuted/collapsed into the stated matrix-then-index
frame. First ties, the final active row and self swaps are included.

This is correctly labeled a pivot operation. A full PLU driver still needs accumulated
permutation and previous lower-factor-row invariants, plus either a proved nonbreakdown
argument or total zero-pivot branches. No full PLU, global rounded factorization stability,
finite-range safety or registered cost theorem is inferred from this review.
