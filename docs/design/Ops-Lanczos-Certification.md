# Canonical Lanczos certification

The concrete ordinary Lanczos tree already has total exact and standard-model output proofs.
This addition places the same fixed tree behind `Ops.Algorithm`, using the existing realized
standard operation model and mandatory canonical instruction accounting.

## Objects and interfaces

`Lanczos.Certification.problem domain admitted` has two sizes (dimension and cap), three
explicitly supplied cell buffers (right-hand side, basis, coefficients), and a raw word-list
right-hand side. Admissibility identifies that list with the supplied initialized input cells,
requires its dimension, and supplies initially uninitialized output slots of the exact public
lengths. No preprocessing callback computes input values. Every admitted size has actual buffers.
The optional domain is a size-only predicate with an inhabitant; this supports pairwise length
limits and rounded precision caps without removing ordinary input vectors.

`Lanczos.Certification.program : Program Standard.Operation CmpTst 2 3` is the existing
`Lanczos.solve`, fixed independently of sizes and inputs. `specification model E` records its
full syntactic instrumented static count, primitive/query projection, declared model work/span,
scratch plus query reservation, and initial resident payload. The budget is a size-only static
analysis of the fixed tree, never the observed execution count. It includes every structural
instruction; the existing explicit `solveCount` remains the readable primitive projection.

The algorithm constructor takes the standard model, equality of its resource configuration to
`Standard.resources`, and per-admitted-input numerical hypotheses: symmetric matrix, scheme
applicability, common `Accuracy`, and the declared matvec error budget. These are mathematical
primitive/data hypotheses; no successful execution or correctness statement is assumed.
The output is the existing `Rounded.Output` relation on the actual readback words, retaining
zero cap/input, early breakdown and all vector/coefficient ties.

## Statement shape and consumers

The main definition returns
`Algorithm model.access (specification model E)`
for a model on the declared problem. The constructor quantifies over all admitted sizes, every
supplied raw input and every interpreter satisfying exactly the primitive contracts. It proves
format typing and total WP, then uses `Algorithm.ofWp`. Consumers obtain full same-run counts,
work, span and modeled payload from `.correct` and may use `.mapPost` for mathematical results.
There is no registered target or native hardware/IEEE claim.

## Shared machinery and file placement

`Ops/Certification.lean` supplies generic initial-buffer read/capacity facts, the conversion
`ConditionalRuns.wp`, and the original-operation projection of full instrumented static counts.
These facts concern the core problem/evaluator interfaces and are not copied into solvers.
`Krylov/Lanczos/BufferProblem.lean` shares the explicit input/output layout with reorthogonalized
Lanczos, parameterized by coefficient length. `Krylov/Lanczos/Certificate.lean` specializes it
to the ordinary coefficient length and defines the solver certificate.
No existing algorithm is changed. Existing `Rounded.runs_solve_of_model`, `stmtCost_solve`,
`stmtPeak_solve_le`, `staticPeak_eq`, `Algorithm.ofWp` provide the program mathematics and
resources. Mathlib's finite lists, sums and finitely-supported maps provide all collection API;
searched Mathlib for the operation-core interfaces, none (they are NLAlib-specific).

## Scope and validation

The resident formula counts the supplied right-hand side and all allocated output capacity;
scratch has the existing two vectors and two scalar cells plus declared primitive/query space.
The matrix is accessed as a declared operator primitive, so hidden backend matrix storage is
not certified as absent or free. Cell payload is abstract and is not an IEEE byte encoding.
Syntactic complete counts are deliberately exposed before a handwritten closed structural-work
formula; the static manifest is conservative even after early exit. Full build, scoped rules,
axiom/kernel validation and the unchanged stage script are coordinated by the parent agent.
No open design question blocks implementation.

## Canonical scalar lowering

`Lanczos/LinkedCertificate.lean` certifies the actual fixed sequential scalar lowering, rather
than relabeling the abstract-BLAS certificate. Its computable `sequentialTable` is the table
composition underlying `Blas.seq`, and `program` is the existing ordinary tree linked with that
table. The canonical complete static manifest, work/span and scratch are recomputed on this
lowered tree, including all of the scalar loops, reduction scratch and structural instructions.
The same initial-buffer problem and resident payload are reused unchanged.

The standard model's scalar law, exact comparisons and rounded matvec contract supply total
lowered execution through the already checked sequential solver theorem. Its accuracy envelope
uses `Blas.seq.err (model.scheme.roundoff model.unit)` explicitly; a pairwise error guarantee
is not silently used for sequential reductions. The declared resource configuration is checked
again for this actual tree. `specification` records all static instructions and its mathematical
output is the existing rounded packed-output relation. Matvec remains primitive; this is a
scalar-plus-matvec model, not dense-matrix source certification. Closed structural scalar cost
simplification is separate from the complete syntactic manifest and is not assumed.
