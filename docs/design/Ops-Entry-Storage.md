# Fixed-width matrix entries in Ops

Spectral bisection stores a complex entry as two real words. The reusable object is a
fixed-width codec, not a second program semantics: `EntryCodec K E` gives a positive word
width and an equivalence between entries and vectors of that many words. The equivalence
ensures arbitrary raw words decode without hidden validity or preprocessing assumptions.

`EntryCodec.pack` flattens an entry vector. `EntryCodec.matrix` decodes a flat word list to
Mathlib `Matrix`; `Store.HoldsEntries` states the actual component reads in a logical
`MatLayout`, with word address `off + width * (column * ld + row) + component`.
The pair codec has width two, real part first. This is storage only; arithmetic contracts
and resource accounting still belong to the existing Ops operation model.

The API includes exact packing/decoding, dense block conversion, and a generic `ReadsOnly`
frame lemma. Sign, deflation, bisection compression and upward assembly consume the same
layout facts rather than re-proving component reads and frames. Existing Ops `MatLayout`,
`Store.HoldsVec`, read-block and footprint rules are reused. Mathlib `Equiv`, `Matrix`, `Fin`
and finite vector extensionality supply the mathematical objects; no second evaluator is
introduced. The codec API lives in `NLAlib/Ops/Logic/EntryLayout.lean` and remains independent
of numerical assumptions. Spectral bisection combines it with the execution and resource
proofs described below.

## Shared fill and operation rules

`EntryCodec.packFinMatrix` packs an actual Mathlib matrix without padded entries or an
inhabited entry carrier. `matrix_packFinMatrix` is the decoding retraction; zero rows and
zero columns are included. Raw decoding uses the existing opaque-word list accessor, and
operation contracts separately establish readable input blocks of the declared lengths.

`Logic/Functional.lean` supplies `writes_call_fn`, `writes_call_fn1` and `writes_call_fn2`.
A functional primitive produces its known mathematical output blocks, frame and tape position
in one rule. Input/output aliasing is admitted because reads precede writes. Multiple outputs
must be disjoint to read every result back. No algorithm success or numerical result is a
primitive contract.

`Logic/EntryFill.lean` expands logical entries to scalar word layouts and supplies a rectangular
entry fill rule. `Logic/EntryRows.lean` supplies variable inner-loop bounds and a more general
entry-region fill: its target is a pure index function injective on the visited coordinates.
The implementation tree, scalar operations and allocations are unchanged by these proof rules.
Column-major upper triangles and transposed lower triangles use the same theorem; their exact
footprints are unions of the word blocks actually written. Existing `Store.EqOff.keep`
preserves region facts across disjoint writes.

In `Blas/HermitianMirror.lean`, `writes_mirror_lower` applies the region fill rule to the
scalar conjugation entry kernel; `writes_mirror` joins the computed lower
triangle with the unchanged stored upper triangle. Its assumptions are readable upper words,
actual square output capacity and a live buffer handle. It does not require initialized lower
words, a pre-existing successful execution, or any floating-point numerical accuracy hypothesis.
The returned matrix preserves the stored diagonal, including its imaginary words. Interpreting
that matrix as Hermitian additionally uses the numerical scalar/diagonal properties.

## Scalar scans and matrix permutations

`Blas/MatrixCorrect.lean` uses the same injective region fill for conjugate transpose.
Input and output spatial spans are disjoint, permitting a shared buffer with separated
regions. Each visited entry applies the scalar conjugation WP once; the generic capacity,
footprint containment and frame rules handle layout bookkeeping.

`Blas/Interval.lean` contains one vector word scan, used by the framed matrix box test in
`Blas/HermitianTest.lean`. Its flag is the actual machine literal selected by the all-words
interval predicate. No exactness or distinguishability of literals is required at this
functional layer. The word span and endpoint cells are spatially disjoint from the flag,
so shared-arena inputs are allowed. `Functional.Writes.wp_eq_upd` turns its scalar result
and frame into one exact mathematical memory update; the box-test WP is a corollary.

`Logic/MatrixPacked.lean` specializes the generic raw-block matrix multiplication and QR
rules to actual `packFinMatrix` inputs. Each proof is a decoding rewrite of the existing
rule. The routines remain arbitrary word-level mathematical functions, with accuracy
assumptions supplied separately by numerical theorems.

## Deflation composition

`Logic/Allocation.lean` transports an exact output block through a whole scratch-allocation
chain. Its callback receives arbitrary newly allocated scratch stores with their lengths and
agreement on existing buffers; no initialized scratch contents are assumed. The shared rule
removes the scopes and returns the caller's output block. Fresh scratch blocks are included
in the declared scratch footprint by one common inclusion lemma.

`EntryCodec.take_packFinMatrix` identifies a packed column prefix with the corresponding
Mathlib submatrix. `HoldsEntries.readBlock_packFinMatrix` connects component storage directly
to matrix primitive operands, using `Matrix.of` explicitly for stable rewriting. These
bridges introduce neither padding entry requirements nor hidden matrix transformations.

The actual `SpectralBisection.writes_deflate` theorem composes sample scaling, multiplication,
QR and copy from these rules. Its output is exactly the packed first requested columns of
the QR factor of the supplied multiplication routine on the stored projector and actual
scaled sample matrix. Bounds on side, slot and requested rank justify every memory access.
All four scratch matrices are scoped, and the tape position is unchanged. The final copy may
overwrite any original input because all input-dependent computations finish before it.
This is a word-level functional refinement; it does not itself assert a numerical subspace
quality bound, probability bound or canonical resource certificate.

The split theorem composes these operations into eight stored results: two computed bases,
two shifted compressed matrices, the two child sizes, the parent kind and the split size.
`Writes.seq_readBlock` collects each mathematical block result while preserving earlier
results across spatially disjoint writes. `Stmt.indexBlock` provides the corresponding
straight-line rule for dimension literals, returning actual machine words without assuming
that their decoding is exact. The split assumes explicit interior-rank, slot, capacity,
readable-input and spatial-separation conditions. Numerical subspace and spectral guarantees
come from the mathematical analysis above this functional execution theorem.

Whole-tree storage uses the same slot invariant. `Fp.split_strided` places two disjoint
payloads inside consecutive slot reservations; their actual lengths may be smaller than their
reserved lengths, and either child may be empty. `Mem.room_split_strided` transfers the parent
capacity to both children. The spectral-bisection specializations prove that child square
matrices fit the parent's root-stride slots, while its two rectangular bases exactly fill the
parent square payload. The existing disjoint-interval sum rule bounds the total of any
monotone superadditive node cost over a level from the same mathematical slot partition.

The final traversal level is also an executable theorem. `BottomOutput` states the ordinary
stored identity and zero eigenvalue vector, and exposes both packed output blocks.
`writes_bottomLevel` initializes that result for every bounded decoded size word, including
empty slots, and preserves the tape position. The shared `writes_loop_disjoint` rule retains
all completed outputs from their local read footprints and pairwise spatial separation. The
bottom proof requires only scalar arithmetic and the bounded natural-index query it executes.

Upward reconstruction uses an ordinary mathematical output pair. `EighStep.assemble` factors
the exact matrix-column concatenation and eigenvalue shifts of the existing recursive
algorithm, with a checked equality to `eighAux`. `StoresResult` represents that pair by two
packed reads. The actual kind and split-size queries select checked copy/shift or
multiply/shift implementations, and `writes_upNode` returns exactly the mathematical
assembly from the occupied child results. `writes_upNodes` proves the entire slot loop.
Its shared prefix-sensitive loop rule preserves the original outputs of future leaves;
keeping an already-computed leaf introduces no arithmetic calls or initializations.

`writes_upLevel` includes the actual scalar half-radius and negation calls, the complete
upward slot iteration, and removal of its two-word workspace. Agreement below the original
handle boundary transports the input representations across scratch initialization and the
output representations across cleanup. Thus the level theorem returns the pure mathematical
assembly without exposing allocation/update chains in its result statement.

The whole upward pass uses `StoresLevelResults`, a family of ordinary represented matrix and
eigenvalue pairs indexed by depth and remaining recursion budget. The bottom identity/zero
outputs represent budget zero. Each executed upward level adds one unit of the existing
`eighAux` recursion, using its exact `eighSlotTree` samples, and reverse-depth iteration
returns the root result with budget `L + 1`.

Completed deeper levels have explicit write footprints. Initial level inputs and recorded
outcomes remain available because their coarse read footprints are spatially separate from
those writes. `readsOnly_storesLevel` and `readsOnly_storesRecords` derive this preservation
from ordinary field-block inclusions. The pass requires actual capacity, arena separation,
and exact bounded size decoding, and asserts no numerical quality or successful-execution
premise.

`writes_upwardPass_of_arenas` packages these conditions for the solver's actual eleven arena
allocations. Their complete capacities and spatial apartness imply the local node workspace,
result slots, metadata protection and cross-depth child protection. The theorem starts from
the original represented levels and outcomes and returns the exact root `eighAux` output;
callers do not supply per-iteration execution or geometry certificates.

The mathematical reference machine reads the same tape as the program. `tapeMachine` uses
the existing uniform and Gaussian stream coordinates with an explicit starting position,
and normalizes each Gaussian component with the actual scalar multiplication.
`eighStep_tapeMachine` identifies an indexed mathematical sample with the stored level words
at every requested matrix entry. A node's slot bound justifies the addresses; this equality
requires no probabilistic or numerical assumption.

`StoresLevel` ties the pure path traversal to actual packed input matrices, size words and
level parameters. `StoresRecords` ties its reached positive nodes to stored mathematical
outcomes. `nodeAtSlot` supplies a typed mathematical node at a slot, with an empty fallback
for absent slots, and proves bounded, disjoint slot intervals. The lookup is specification
data: the executable traversal obtains its dimensions from the actual stored size queries.

An outcome's occupied children supply their next-level packed matrices and literal sizes.
Its exact footprint separates these size cells from matrix and parent-metadata payloads.
The pure path-extension rule identifies every written size slot with a reached child. This
lets the level frame preserve initialized zero size words at absent slots, even when arenas
share a buffer in disjoint word intervals.

Numerical probability bounds use that same word computation. `eigh_tapeMachine_roundTape`
identifies its output, at any fixed starting tape position, with the ideal-sample recursion
using the actual uniform rounding, Gaussian rounding, normalization and matrix routines.
`measureReal_not_isApproxDiagonalization_tapeMachine_le` transfers the existing spectral-bisection
bound: numerical failure has probability at most the supplied tolerance under the explicit
input, precision, range and tape-law conditions. The numerical sampler contract follows from
the standard scalar model, explicit seed-rounding bounds/ranges, multiplication's radius
preservation, and the supplied multiplication/QR error contracts; measurability uses the
rounding maps' countable ranges. The probability theorem retains an explicit nonnegative
absolute-error floor and its original smallness bound, requires positive root dimension,
and assumes no successful execution. The standard relative-error specialization uses floor zero.

The core `Algorithm` definition fixes one program before dimensions and inputs, requires
jointly realized declared contracts, and certifies successful execution with every modeled
resource bound. Contributors choose the problem's admissibility relation, primitive contracts
and resource configuration. Those choices determine what the algorithm claim means. For this
port, the concrete raw-buffer relation supplies empty outputs, and the generated dense model
uses local functional block contracts for one fixed scalar machine and deterministic matrix
routines. These properties are visible choices of this problem and standardized model.

The dense profile counts opaque scalar cells and abstract operation units, with supplied
matrix work/workspace functions and sequential span. A physical IEEE implementation needs its
own finite encoding, resource units and interpretation proof. Real-decoding comparison
contracts also require an explicit treatment of exceptional values such as NaNs. Exact
natural literals over the admitted dimension range remain a separate model obligation;
functional realization alone supplies neither literal exactness nor numerical accuracy.

`Ops.Specification.Accepts` keeps execution success, peak scratch, the full instruction count,
work, span, resident-memory capacity and the output postcondition on one actual counted
outcome. The shared certificate probability rule places failure of any of these conditions
inside the mathematical reference failure event. Spectral bisection specializes this rule to
its stored approximate diagonalization while retaining the word specification's tape advance
and cleanup conditions. The numerical reference bound and the total certificate supply the
two independent proofs; no successful-run assumption is added.

The complete solver also has an independent storage polynomial. For root dimension
`n ≥ 2` and depth parameter `L`, its scratch reservation is at most
`6n²L + 32n² + 4nL + 7n + 2L + 24` abstract cells when primitive workspace is zero.
Adding the supplied input and output capacities gives
`6n²L + 36n² + 4nL + 8n + 2L + 27`. These estimates follow the eleven actual arena
allocations and the largest nested node buffers; neither expression is defined using the
operation-count manifest, and neither grows with the sign iteration cap.

`staticPeak_workspace_le` adds one global ceiling on matrix primitive workspace to the
scratch polynomial. The stronger `staticPeak_workspaceEnvelope_le` instead uses the finite
`MatrixOp.workspaceEnvelope` over multiplication and QR shapes bounded by the root dimension.
The whole-program static support theorem proves that every matrix call has a valid arity
and lies within that envelope, including every bounded query result. This corollary covers
arbitrary workspace functions without monotonicity or a global ceiling. Its resident-memory
version adds the supplied capacities to the same scratch bound.

The [complete work certificate](../../NLAlib/Eigensolvers/SpectralBisection/WorkCertification.lean)
uses those same stored levels, outcomes and mathematical slot partitions. The actual downward
node contributes at most `(2cap + 9)T(k)` at size k, and upward assembly contributes at most
`2T(k)`. Summing over each disjoint level and all L + 1 levels yields matrix work at most
`(L + 1)(2cap + 11)T(n)`.

`stmtWeightedCost` takes branch maxima after weighting, avoiding a charge for mutually
exclusive dimension keys in a pointwise count supremum. `evalCounted_loop_weight_of_writes`
accumulates actual counts using the existing word invariant and prefix frame.
`sum_slotWork_le` then bounds a monotone superadditive cost over the canonical slot partition
by one root-size cost per level. `exec_original_count` identifies the original-operation count
inside the same fully instrumented execution; structural accounting remains present.

`Dense.work_eq_nonmatrix_add_matrix` combines that actual matrix work with the scalar,
sampling, literal, query and structural charges. The complete work and sequential-span bound
is the matrix term above plus the zero-matrix-work profile applied to `staticBudget`.
Nonmatrix overhead remains a conservative static estimate. The result does not assert an
optimal total complexity with fast matrix multiplication.

`workCertifiedAlgorithm` and `certifies_work` guarantee total execution of the fixed program,
the exact mathematical word output, tape advance, cleanup and all declared resource bounds
on one outcome. Their domain has n ≥ 2. The matrix-cost majorant T is monotone and
superadditive and must dominate the model's matrix work globally over dimension lists.
This forces `T(0) = 0` and zero matrix costs on empty or all-zero lists. Matrix workspace
still uses the arbitrary finite-envelope function above; it has no global-ceiling or
monotonicity premise. Numerical accuracy, the explicit absolute-error floor and physical
IEEE realization remain separate from this total word/resource certificate.
