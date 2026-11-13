# Canonical conjugate-gradient certification

CG certificates fix one Ops `Program`, a raw-buffer `Problem`, a jointly realized operation
model, and a separately stated output/resource specification. Primitive contracts supply
scalar arithmetic, BLAS, matrix-vector application, and comparisons. Matrix positivity,
precision windows, and any fixed-horizon grade condition are mathematical assumptions in the
certificate constructor; successful execution is a conclusion.

The zero-start programs receive the right-hand side and uninitialized output capacities.
An explicit literal-zero loop initializes the iterate before invoking the existing solver.
No decoded vector or initialized zero buffer is inserted by preprocessing. Stored guesses are
a separate interface when an implementation supports them.

The exact carried HSCG and fully reorthogonalized solvers stop at the earlier of the cap and
exact convergence. Fixed-horizon HSCG and PCG state the grade restriction in raw-input
admissibility, together with a raw-buffer witness at every admitted size. The rounded carried solver retains its
actual stored `CGRun`, computed residual product, residual-gap and energy/backward stability
claims, under the existing spectral and precision assumptions.

Full budgets count the instrumented fixed tree. Scratch, initial-plus-scratch payload, work,
and sequential span belong to the same execution and supplied resource configuration. Scalar
and BLAS linkage can replace operation-level costs only through a checked implementation table.

Shared infrastructure consists of a capacity-parametric raw vector interface, actual zero-fill
initialization, standard zero-error-to-exact model bridges, and the existing total word proofs.
Certificates reuse these pieces rather than replaying initialization or numerical recurrences.
Finite-format adapters keep range/underflow conditions explicit and establish numerical laws
for the actual word operations; a storage-format tag alone does not establish IEEE behavior.

The exact certificates cover positive-definite systems. Their stopping rules and output state
do not assert the legacy non-positive-curvature status interface. The guarded carried and
reorthogonalized implementations admit arbitrary right-hand sides and caps; the prescribed
horizon of fixed HSCG and PCG must not exceed the corresponding Krylov grade.

The sequential cache kernel is the actual dot-over-sum tree linked with sequential scalar
summation. Its mixed error and zero-cache threshold use only the supplied residual and an
explicit safe-radius inequality. The concrete binary64 adapter uses actual logical finite
Float operations; the bounded fixed-point adapter uses nearest-grid rounding and explicit
saturation. The general binary-format adapter uses represented real values and makes no
physical word-encoding claim. These cache guarantees concern the recursive residual; the
rounded carried certificate separately supplies the residual-gap and backward-error results.

Matrix-free certificates count supplied vector payload and declared operator workspace.
An external operator's stored matrix is part of its backend accounting rather than an
unmentioned matrix allocation in the CG program. The complete instrumented budgets retain
index/address expressions, branches, allocation, frame and query costs. Their original-operation
projection also records the explicit literal-zero initialization before the solver's budget.

The stored dense interfaces additionally declare matrix words as the first input buffer.
PCG declares both the system matrix and the inverse-preconditioner matrix. Their mathematical
operators are decoded from those exact words. The fixed context transform forwards these
operands through every nested procedure and replaces matrix applications by actual scalar
dense loops. The program receives raw RHS words and uninitialized state capacity, executes
zero initialization, and returns the same exact recurrence as the matrix-free interface.

Stored carried CG and reorthogonalized CG admit arbitrary RHS words and caps for raw SPD
matrices. The fixed-horizon CG and PCG interfaces include their initial Krylov-grade condition
in raw-input admission. Each size has an explicit joint raw matrix/RHS witness; this is a
nonemptiness proof and supplies no desired output or successful execution. Resident payload
includes every supplied matrix word and output slot. Canonical instrumentation is applied to
the translated tree, so context offsets and frames, dense scalar arithmetic and all remaining
vector operations are charged. Proof-side contract guards and mathematical reference functions
are absent from the executed tree. See [context linking](Ops-Context-Linking.md).
