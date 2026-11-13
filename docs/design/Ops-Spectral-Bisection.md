# Spectral bisection in Ops

The fixed Ops solver executes scalar arithmetic, matrix kernels, samples, decisions and
bounded index conversions. Its checked total theorem returns the existing mathematical
spectral-bisection result on the same word functions and tape, including scoped scratch
cleanup. The dense canonical certificate adds full counted execution, independent storage
and partition-sensitive matrix-work guarantees.
A whole bisection node is not introduced as an opaque primitive.

The implementation and numerical interfaces are summarized on the
[curated algorithm page](../algorithms/Spectral-Bisection.md).

## Algorithms, models and guarantees

The program is fixed before runtime dimensions, input words and the tape are supplied.
Multiplication and full QR are the matrix primitives; entry arithmetic, copies, trace sums,
sampling, conversions and control flow remain visible in the tree. The scalar machine,
entry codec and matrix routines determine the primitive word functions.

The generated dense access model provides local functional contracts and a joint reference
interpreter. `Dense.laws_functionalModel` supplies exactly the scalar, dimension-literal,
multiplication, QR, sampling and query interfaces used by the proofs. It does not assume a
whole-program postcondition or an execution-success predicate.

[`writes_solve`](../../NLAlib/Eigensolvers/SpectralBisection/Solve.lean)
is total under explicit primitive, readable-input, live-handle, output capacity and separation
premises. Exact decoding of natural literals through `max n 4` is
also explicit. Source blocks must be separate and output blocks must be separate; outputs
may overlap sources because their final copies occur after the source reads. The result
includes the exact tape position and preservation of the caller's storage shape.

[`workCertifiedAlgorithm`](../../NLAlib/Eigensolvers/SpectralBisection/WorkCertification.lean)
uses the raw four-buffer problem: matrix words, three scalar parameters, and initially empty
output capacity. `Problem.initial` supplies raw buffers without numerical preprocessing.
The certificate covers every admitted input and tape under the generated model, with exact
word output, tape use, cleanup and the resource bounds below. Its admitted root dimensions
are at least two. No public premise assumes a WP or successful execution.
The general `certifiedAlgorithm` and conservative `manifestAlgorithm` remain separate entrypoints.

These choices remain visible: contributors specify the problem's admissibility relation,
primitive meanings, numerical assumptions and resource profile. The core `Algorithm`
definition enforces one fixed program, joint model realization and successful counted
execution meeting the declared bounds. Functional realization by itself supplies neither
numerical accuracy nor exact integer decoding.

## Mathematical states and shared proof rules

`StoresLevel` connects the existing mathematical tree to packed matrices, actual size words
and level parameters. `StoresRecords` connects reached positive nodes to their stored outcomes.
`nodeAtSlot` is mathematical specification data; executable node dimensions come from the
actual bounded size queries. Exact occupied-child footprints preserve initialized zeros at
absent slots. No execution-phase record replaces the mathematical tree.

Block contracts return their computed matrices or ordinary output tuples. Shared rules retain
readable inputs across disjoint writes, collect outputs, traverse matrix entries, compose
loops and remove scoped scratch. Arena geometry is proved once from the canonical eleven
operand/capacity spans. Disjoint subviews of one buffer are supported.

The complete checked chain includes:

- initialization of constants, root data and all size slots;
- capped Newton–Schulz sign, including actual stopping tests and cap exhaustion;
- projector construction, bounded split conversion, deflation, compression and both branches;
- the entire downward pass, retaining all mathematical levels and node records;
- bottom initialization and the reverse-depth reconstruction pass;
- final output copies and release of all eleven arenas;
- canonical total certification of this same fixed program.

Useful shared interfaces are:

| Interface | Role |
| --- | --- |
| `Ops/Catalog/Index.lean` | Actual dimension literals and separate bounded literal exactness |
| `Ops/Logic/EntryLayout.lean` | Invertible fixed-width packing and matrix/storage correspondence |
| `Ops/Logic/EntryFill.lean`, `EntryRows.lean` | Rectangular, triangular and indexed-region writes |
| `Ops/Logic/Scalar.lean` | Straight-line scalar blocks evaluated with the actual machine functions |
| `Ops/Logic/While.lean` | Capped iteration whose transition is the identity after stopping |
| `Ops/Logic/BlockSequence.lean` | Stored output tuples and retained input reads |
| `Ops/Logic/BlockPartition.lean` | Capacity and separation inherited by arena subviews |
| `Ops/Logic/Allocation.lean` | Word-level cleanup and actual counted allocation-prefix inversion |
| `Ops/CallSupport.lean` | Primitive support properties and the structural `allOps` checker |
| `Ops/WeightedCost.lean` | Actual weighted counts, with scalar maxima over alternative query answers |
| `Ops/Logic/WeightedLoop.lean` | Count increments using the existing word invariant and prefix frame |
| `Ops/Profiles/DenseWork.lean` | Full-work decomposition retaining nonmatrix and structural charges |
| `SpectralBisection/ArenaLayout.lean` | The actual eleven arena operands and capacities |

Word-level execution is proved directly in Ops. The existing `Matrix/Computation` and sampling
developments supply the shared pure algorithms, tape functions and numerical facts.

## Full counts, independent storage and matrix work

`manifestAlgorithm` certifies the conservative `staticBudget` and `staticPeak` of the complete
instrumented tree. The specialized `workCertifiedAlgorithm` keeps that full instruction budget
and refines storage and work using proofs about the same program and actual counted outcome.
`Algorithm.ofWpActual` supports a work bound independently of weighting the count budget.

The matrix-work proof applies weights before combining alternative query answers. The actual
stored size selects the local cost. Sign contributes at most `(2cap + 1)T(k)`, and a node's
possible split adds eight multiplication/QR charges. Upward assembly adds at most two.
`sum_slotWork_le` bounds the sum over the actual disjoint node slots by `T(n)` at each depth.
There are L + 1 downward and L + 1 upward levels, giving the matrix term
`(L + 1)(2cap + 11)T(n)`.

The complete work and sequential-span bound adds
`(Dense.resources (fun _ _ => 0) W).work (staticBudget d)` to that term. This retains every
scalar, sample, literal, query and structural charge. The nonmatrix overhead remains a
conservative static estimate; no optimal total fast-matrix-multiplication bound is asserted.
`exec_original_count` connects the actual canonical counter to the raw source execution,
and `Dense.work_eq_nonmatrix_add_matrix` combines their resource contributions without
substituting a different run or dropping structural instructions.

The certificate requires T to be monotone and superadditive and the chosen matrix work
function to be bounded by T of the largest dimension, globally over dimension lists.
In particular, superadditivity forces `T(0) = 0`, and matrix costs on empty or all-zero lists
must be zero. These are cost-model assumptions, independent of numerical accuracy.

For n ≥ 2, the [storage theorem](../../NLAlib/Eigensolvers/SpectralBisection/StoragePolynomial.lean)
gives scratch at most
`6n²L + 32n² + 4nL + 7n + 2L + 24 + E(n)` abstract cells and resident memory at most
`6n²L + 36n² + 4nL + 8n + 2L + 27 + E(n)`.
The supplied matrix, parameter and output capacities are included in resident memory.
Neither polynomial is defined from the instruction manifest, and neither grows with cap.

Here `E(n) = MatrixOp.workspaceEnvelope W n` is the finite maximum over root-bounded
multiplication triples and QR pairs. `program_matrixShapes` covers every matrix call in the
actual static support, including every bounded query choice. W requires neither monotonicity
nor a global ceiling. The shared `stmtPeak_le_zero_add_on_support` rule turns that shape
coverage into one workspace reservation; `Stmt.allOps` certifies matrix-free fragments.

## Numerical probability and model scope

The tape correspondence uses the actual uniform and Gaussian word windows at each depth,
including an arbitrary fixed starting position. `eigh_tapeMachine_roundTape` identifies that
word reference with the existing ideal-sample recursion using the supplied rounding and
matrix routines. The numerical theorem
`measureReal_not_isApproxDiagonalization_tapeMachine_le` bounds its approximate-diagonalization
failure under the explicit input, precision, range, depth, iteration-cap and tape-law premises.
Rounding measurability and countable sampler ranges are proved separately for the actual
normalization and rounding maps.

[`measureReal_not_accepts_le_of_wordSpecification`](../../NLAlib/Eigensolvers/SpectralBisection/ProbabilityTransfer.lean)
transfers a mathematical
reference bound to the actual counted solver. It retains the word specification, tape advance,
cleanup, peak scratch, full count, work, span and resident-memory conditions on the same
execution. Execution failure and resource violations belong to the failure event; successful
execution is supplied by the certificate, not assumed. The real-valued transfer has an explicit
finite-measure premise.

The underlying scalar and matrix word functions are total in this abstract model. Their
functional output guarantees do not themselves establish numerical accuracy.

The numerical bridge accepts `IsAccurate` with an explicit nonnegative absolute-error floor
and the original analysis's bound on that floor, for a positive root dimension. The standard
relative-error specialization sets the floor to zero. A bounded-exponent model must establish
the corresponding primitive accuracy, range and floor assumptions; the bridge supplies no
automatic realization of that model. Exact arithmetic is likewise a model choice requiring
the declared primitive and decoder contracts.

Cells and operation units are abstract. No physical IEEE encoding, exceptional-value behavior,
native implementation or byte-level hardware resource bound is certified here. In particular,
real-decoding comparisons require a separate treatment of values such as NaNs. A physical
implementation must establish its own interpretation and resource correspondence.

## Validation

The complete solver, canonical work certificate and numerical probability transfer have focused
warnings-fatal Lean builds. The final certificate, solver, counted projection and numerical
probability/transfer axiom audits use only Lean's standard `propext`, `Classical.choice` and
`Quot.sound`. Executable rational regressions cover empty, scalar, tolerance-stop and nonleaf
split paths, output words, exact sample consumption and scratch cleanup. The simple QR routine in the nonleaf regression carries no accuracy claim.

No registered target, check, pin, baseline or allowance is changed to make this port pass.
Broader validation reports existing unrelated policy failures separately; a functional or
resource certificate does not extend its own numerical or hardware assumptions.
