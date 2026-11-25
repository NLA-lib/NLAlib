# Dense resource and block-interface review

Read-only review of the four frozen modules in `/tmp/nlalib-next-semidefinite/NLAlib/Matrix/Computation/`. No sources, protected targets, caches or build artifacts changed; no shared build launched. Parent reports all four modules strict checked and 24 actual DenseBlockSmoke guards passing. This review checked source statements and proof structure independently.

## Findings

No material mathematical soundness, public-type, P9 or frame defect found in these four modules.

The remaining delivery boundary is target registration. `DenseFactorizationResources` proves ordinary conditional successful-run resource lemmas for seven actual routines. It supplies neither a registered cost target nor an access target. Under Computation E3 and design F15, these lemmas must not be described as completed registered/published cost results. The design explicitly requires maintainer-reviewed proposals and forbids evading registration by renaming a top-level program. This is a visible remaining work item, not a reason to edit protected target files automatically.

## What the resource theorems establish

Each symbolic tree is compiled from the actual builder, and its private `*_toStmt` theorem is `rfl` for arbitrary buffer numbers and arbitrary index expressions. Thus the proof is not restricted to the illustrative buffer numbering or zero offsets used to construct the symbolic tree. Aliases between external handles are allowed in the conditional resource statement; numerical-success and valid-frame hypotheses remain the execution theorem's responsibility.

`bounds_*` takes an actual `exec ... = some out` premise, arbitrary carrier K, arbitrary scalar interpretation, widths and instruction charges. It applies the existing sound static analysis rather than assuming numeric success. It proves count growth, restoration of current cell/bit counters, and peak bounds relative to initial current memory and any historical peak. It does not establish successful execution, matrix correctness, initialized accesses, or disjointness.

Closed bounds are additional simultaneously live words at the routine's tag, excluding caller-owned input/output storage: LU and positive-definite Cholesky N²+2N+3; semidefinite Cholesky N²+2N+4; LDL 2N²+2N+3; PLU and PLUQ N²+2N+7; fixed-scale PLU N²+3N+7. They are upper bounds, not equalities or total process memory. Space formulas impose no carrier Zero/Inhabited assumption. Counts and bits remain the existing finite static summaries; the new file does not provide closed polynomial operation-count or bit formulas, and it covers neither all policy drivers nor blocked variants.

Suggested next maintainer-review packet: explicit targets for the stable LU/PLU/PLUQ/Cholesky/semidefinite/LDL/scaled trees with declared order and offsets, conventional charges/widths, the relevant success domain, and stated count/memory quantities. Separate access targets would require their own actual access guarantees; a successful-run resource upper bound alone does not supply them. Existing ordinary lemmas can discharge resource portions after approval. No target registration was performed here.

## Copy and block-update limits

`copyMatrixBlock` uses two actual copy loops, arbitrary carrier and charge monoid, independent source/destination leading dimensions and offsets. Its proof requires destination row count <= destination leading dimension and distinct source/destination buffers for positive area. It deliberately does not claim a general in-place memmove guarantee, even for nonoverlapping same-buffer views. Source columns may overlap provided the stated source reads hold; destination columns are injective. Every destination gap and outside cell retains its original word. Gather supplies one full packed-block frame; scatter retains the strided gap frame.

Empty rectangles impose no valid-handle or separation requirement. No Zero/Inhabited carrier is introduced to fabricate empty words: the positive-row helper's fallback indexes an actual row, while the empty-row proof performs no reads. For zero column count the source/capacity conditions are vacuous. The destination-leading-dimension inequality remains explicit even when column count is zero; this is an applicability limit, not an incorrect no-valid-handle claim.

`blockSchurUpdate` performs one actual library GEMM into scoped m*n product storage, then m*n subtractions. Consequently either factor may overlap C, and the only net store write is C's full packed block. Exact success requires RCLike words, exactSem and standard OpCount charges; it is not a generic rounded kernel theorem. Zero panel width skips the whole body and proves the unchanged store by the generic Holds self-write bridge. Empty output dimensions still retain any nonempty factor readability premises actually needed by the existing GEMM builder; there is no blanket no-read promise.

The GEMM builder is the existing reference scalar-IR kernel (one GEMV per output column). Calling it establishes a genuine GEMM-shaped computation and supports blocked factorization semantics. It does not establish optimized native BLAS dispatch, cache locality, hardware speedup, or wall-clock performance. No such claim appears in these modules.
