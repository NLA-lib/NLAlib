# Operation core

The canonical API lives in the existing syntax, evaluator, contracts, static analysis and
certification files. Lint is optional prover guidance; none of these guarantees depends on it.

## Execution and operation models

`Program Op Tst r b` contains one first-order statement tree, fixed before runtime sizes or
inputs. Sizes enter `Program.environment`; raw buffers enter a separately specified `Problem`.
There is no runtime tree-building, preprocessing or environment-building callback.
`Op` and `Tst` are the closed signatures of permitted operations and queries. Each source call
names one of those operations. Index expressions have only the arithmetic constructors in
`IExp`; statements have only the constructors in `Stmt`.

`AccessModel` declares a `Contract` for every operation and a `QueryContract` for every query.
`AccessModel.contracts` is defined to be exactly satisfaction of those contracts. There is no
field for arbitrary additional interpreter assumptions or whole-program success. The contracts
themselves are unconstrained by this type: see "What the model must also satisfy" below.
The model must provide a joint realization of those exact contracts at every admitted input.
`Problem` requires an admitted size and an input at every admitted size. The model supplies an
actual word, so universal tape quantification cannot be vacuous.

Canonical `exec p I resources formats tape sizes memory` always elaborates index arithmetic,
operand addressing, control and allocations into explicit structural counters. Original operations,
structural instructions and queries have distinct keys. Allocation and release carry
`[format.bytes, elementCount]`, so weights can account for both width and capacity.
The interpretation cannot turn accounting off. `exec_mem` proves exact agreement with the memory
semantics `run`, including failures. Structural elaboration is an internal part of the evaluator,
not an optional wrapper around a different certification API.

The counters have abstract operation meaning. `Count.totalWeight` requires explicit weights for
operations, queries and structural instructions. `Count.original` explicitly projects only the
original-operation/query coordinates; it does not replace a full canonical budget.
Storage is format-aware. `allocAs format n` charges `format.bytes*n` modeled payload bytes;
`alloc n` means abstract `.cell` width1. `Problem.formats` declares the initial layout.
`ResourceModel` fixes permitted formats and primitive/query operand signatures, and canonical
execution checks the entire lexical format discipline, including aliases and frames. Explicit
conversion uses a declared operation with distinct input/output formats. No implicit retyping
or smaller forged representation can satisfy a different signature.

Certificates separately bound scratch, initial-plus-scratch payload, work, span and full counts.
Primitive workspace is in the same modeled byte units; queries reserve the largest workspace
among actual executed query keys, conservatively added to the allocation/primitive peak.
`stmtPeak_instrument` proves the allocation/primitive part is unchanged by elaboration.
`ResourceModel.work` and `span` weight the full count. Work and span use the same cost units;
FLOPs and seconds cannot be mixed in the span<=work comparison. Span permits internal primitive
parallelism but adds across sequential calls; no fork/scheduler/work-P speedup is inferred.
The per-key span<=work laws imply `ResourceModel.span_le_work` for the entire execution.

Format widths are model declarations, not a proof that arbitrary K values fit those bits.
Tagging exact real-valued words fp64 does not establish a physical 64-bit representation.
Physical byte/time claims require faithful storage encodings and justified primitive resource
models. Payload accounting excludes metadata, allocator headers/alignment, code and tape.
Oracle or backend storage included in a memory claim is declared as input payload or covered
by its resource model; an opaque matvec does not automatically account for a stored matrix.
See [resource design](../../docs/design/Ops-Resources.md) and `Examples/Resources.lean`.

## Certification

`Runs p model specification`, also written `p.Certifies model specification`, requires successful
canonical execution at every admitted size and input, under every interpretation satisfying
exactly the declared contracts and every tape. The budget, peak workspace and postcondition refer
to that same execution. `Specification` has no program argument, but nothing prevents its
budgets from being defined as the static count of the certified program (a manifest); such a
bound says only that the program runs. `Algorithm model specification` packages one fixed
program and this total proof.

## What the model must also satisfy

The types accept a contract that depends on the whole input, reads cells that are not operands,
or has zero work; a unit-cost primitive can then write the answer (`Examples/Oracles.lean`).
`Confined.lean` names the properties that exclude this, as classes on the model:

* `AccessModel.Confined`: every primitive contract is in operand form (`BlockRel.spec`) and
  every query reads its operand blocks only. `Contract.Confined.frame`: a confined call changes
  no buffer that is not an output operand.
* `AccessModel.Uniform`: the contracts do not depend on the sizes or the input. A model with a
  declared oracle (the matrix-free operator) is confined and not uniform.
* `AccessModel.Charged`: every primitive, query and structural instruction has positive work.
  `AccessModel.Charged.size_le_work`: work is then at least the number of instructions.

`Profiles/Confined.lean` proves these for the standard collections. `scripts/OpsPrograms.lean`
reports them for every certificate, with its number of hypotheses and whether its count
budget, its work and span, and its scratch are closed forms or manifests, and compares the report with
`scripts/ops_certificates.txt`: a recorded certificate may not get weaker, and a new one must be
confined with closed-form work or be added to that file. A family of certificates indexed
by a parameter that fixes the admitted size is not one certificate; the check lists
parametrised programs.

`OperationCount.lean` gives the closed forms. `Program.countPoly` computes from the fixed
instrumented tree a polynomial in the sizes, one variable per size, that bounds the number of
instructions of every run (`Program.exec_work_le_countPoly`); the kernel evaluates it to an
explicit list of terms. Under a model whose weights are at most one it bounds the work, and
`Algorithm.withCountPoly` restates a certificate with it. The scalar conjugate gradient, PCG
and Lanczos certificates are stated this way, e.g. `33 n² k + 157 n k + 242 k + 50 n + 127`
instructions for conjugate gradient of order `n` with cap `k`.

`Algorithm.ofWp` uses the total statement logic and full structural bounds to construct the
certificate. `Algorithm.link` takes a fixed implementation table and verifies the entire lower
program against a separately realized lower model and specification, including introduced frames
and allocations. `Algorithm.runsLaw` observes the output of the same certified execution.

## Writing a routine and certifying it

A routine (`Routine.lean`) is a fixed tree with an interface, and is the unit that is written,
called, linked and certified. It is written with `routine%` (`RoutineSyntax.lean`), whose header
is the interface:

```lean
/-- Sum two vectors by two calls of `sum` and one addition. -/
def sum2 : Routine Op Tst := routine% [n] (x : n, y : n) → (z : 1, unreported w : 1) {
  run sum [n] (x, z);
  run sum [n] (y, w);
  call (Has.inj ScalarOp.add) [] (z, w) → (z)
}

def sum2Spec (dec : K → ℝ) (u : ℝ) : Routine.Spec K :=
  spec% [n] (xs, ys) → ([v]) ensures |dec v - …| ≤ …

theorem sum2_meets … : sum2.Meets I (sum2Spec dec u) := by
  routine_intro [n] (x, y, z, w) reads (xs, ys)
  have hsum := sum_meets hI hM hu
  call hsum [n] (x, z) as ν hfr hpos (zs) hpost
  obtain ⟨v₁, hv₁, rfl⟩ := Store.readBlock_one_eq_some.mp hzs
  call hsum [n] (y, w) as ν₂ hfr₂ hpos₂ (ws) hpost₂
  obtain ⟨v₂, hv₂, rfl⟩ := Store.readBlock_one_eq_some.mp hws
  step (hI .add) as ν₃ hfr₃ ⟨hpos₃, v, hv, rfl⟩
  routine_exit
  exact sum2_error hM hu hpost hpost₂
```

(`Examples/Routine.lean`.) In the header an operand named only on the left of `→` is read, only
on the right written, on both sides updated in place; each is declared once with its length, an
index expression in the dimensions or a Lean term `↑(…)`. An operand named again on the left,
without its length, is one more buffer variable of the tree on the same operand, as when a tree
written for distinct operands runs with two of them equal. Marks (`isolated`, `unreported`)
and clauses (`draws e`, `draws unspecified`, `by blocks`, `one variable`) state
what the header cannot infer. The body is a block of the builder, or `:= t` for a tree defined
elsewhere.

**Routines and fragments.** A tree is a routine when it has operands of its own and something
calls it through its interface: a `run` in another tree, a linking table, or a certificate. It is
then written with `routine%` and has one judgment. A tree that is a piece of one routine's tree,
working on buffers that routine allocates or at offsets computed inside that routine's operands,
is a fragment: a plain `Stmt` written with `ops%`, with one statement of its run in operand form
(`X_writes`), used only inside the proof of the routine that contains it. Its docstring names
that routine.

The library does not yet follow this rule everywhere. Kernels that several routines run, each on
operands of its own, are by the rule routines, but some are still plain trees with operand-form
statements, from before routines existed: the rotation and coefficient kernels of shifted QR,
the small-eigenvalue solver and Hessenberg reduction (`rotateRows` and the trees their docstrings
describe as "shared by the trees of …"), and the matrix kernels of `Blas/` (`Hermitian`,
`Matrix`, `Pair`, `ColumnProducts`, `Clamp`, …). Some of them have a word-level and a decoded
statement. They are to become routines with one judgment each; until then their docstrings say
which trees share them. The Krylov families, Hutch++, MGS and the level-1 leaves follow the rule.

**One statement per routine.** A routine has one correctness statement, `XRoutine_meets`. A
caller uses it with `call`; it is not restated in operand form, and no lemma lists which
operands are apart (`routine_intro` puts those facts in the context, `routine_sep` proves them at
a call). Two derived statements exist where another consumer needs them: the contract of an
operation the routine implements (`Routine.Meets.satisfies_ofRel`, with `implements`), and the
counted run used to account a linked operation (`Routine.Meets.runs_ofRel`). A routine with
either states its specification as `Routine.Spec.ofRel` of the block relation of that contract;
every other routine states it with `spec%`.

Three situations keep an operand-form lemma beside a judgment, each for a stated reason at the
lemma:

- **One tree, several routines or table entries.** An operation whose contract admits several
  operand layouts (an output apart from an input, or that input itself) is implemented by one
  routine per layout, all with the same tree; the tree's lemma, stated for every layout, is the
  common proof of those routines (`RCLikeScalar.writes_copy`, `writes_scal`, `writes_axpy`). A
  tree that is the body of two table entries is proved once for both
  (`StoredDense.writes_impl_word`, used by `implRoutine` and the context-forwarded
  `ContextDense.impl`).
- **A judgment read on a loop invariant.** A loop over a routine keeps an invariant stated on
  the memory (the state of a recurrence held in the operands). The judgment of the body, read on
  that invariant, is a corollary used by the loop rule and by nothing else
  (`Carried.Rounded.step_writes`, `HSPCG.Rounded.step_writes_function`, `MGS.writes_sweep`).
- **An empty block past the end of a buffer.** A judgment requires room for every written
  block; a statement that must also hold for a block of length zero placed anywhere stays in
  operand form (`hessenbergReduceLast_writes_word`).

A routine may have several judgments, for several specifications. A leaf whose result is a
definite list of words states it once, for any machine, as an exact-output judgment
(`axpyLoopRoutine_meets_exact`, `scalLoopRoutine_meets_exact`, `sumSeqRoutine_meets_exact`), and
each error model's judgment applies that one at its operands and reads its bound off the words
(`axpyLoopRoutine_meets` under the standard model, `axpyLoopRoutine_meets_mixed` under a mixed
relative/absolute model, the fixed-point example).

There are two proof styles for a judgment. The default opens the goal with `routine_intro` and
proves the `Writes` statement of the tree. `Routine.meets_ofRel_of_post` is for a run computed as
an exact final memory (a `Wp` ending in the `BlockRel.Post` of the relation): it supplies the
frame and the blocks read back, so the proof states only the memory. The draw examples (`Noisy`,
`Hutch`, `NoisyLinked`) and `Split` use it.

The tactics (`Logic/RoutineIntro.lean`):

- `routine_intro [n, k] (b, x, r, p) reads (bs, xs)` opens a goal `R.Meets I S`: the
  dimensions, the operands and the blocks read are named, and the context holds liveness
  (`hlive : m.Live [b, x, r, p]`, and `hl`, the same fact one operand at a time), room for the
  written blocks (`hrooms` as lists, `hroom` one block at a time), the precondition `hpre`, and
  the separation: for a routine separated by buffer one fact `hxr : x.1 ≠ r.1` for each pair the
  interface requires apart (operands that continue another are part of its region and have no
  name of their own), for a routine separated by block the disjointness `hblocks` of the blocks
  at the named operands. The goal is the `Writes` statement of the tree. `memory μ` names the
  memory `μ` instead of `m`, for a routine with a dimension called `m`.
- `call h [n] (x, z) as ν hfr hpos (zs) hpost` uses the judgment `h` of a routine at a frame of
  its tree, proves the side conditions from the context, and names the memory after the call,
  its frame, the tape position, the blocks written (`hzs`) and the postcondition at those
  blocks. `(pre := t)` supplies the precondition when it is not in the context.
- `routine_exit` closes the proof at the final memory and leaves the postcondition.
- `implements [n] (x) → (z) with hadm` proves `R.Implements B adm port`: it names the operands
  of the contract, splits the admission, substitutes an output that the admission makes equal to
  an input (`implements [n] (a, x, y) → (y) with hadm` for an operation in place), checks the
  interface by computation and proves separation from the inequalities of buffers the admission
  gives. Separation by block, or an admission that does not state it buffer by buffer, is left
  as a goal.
- Inside a rule that wants the body of a loop in operand form, the judgment is applied to the
  named operands directly: `hstep [n] [x, r, p] τ m' _ rfl rfl …` (`Krylov/CG/HSCG/Rounds.lean`).

The interface in detail:

- **Operands.** `Routine.ports` lists the operands, each with its mode and its length in the
  dimensions: `Port.read len` (left unchanged), `Port.write len` (initial contents not read),
  `Port.update len` (read and written in place), `Port.isolated len` (read-only and apart from
  every other operand, as stored data forwarded to a linked operation must be). `routine%`
  produces them from the header; the value is a plain structure
  `{ nd := …, ports := […], body := … }` whose other fields have defaults (no draws, no layout,
  separation by buffer).
- **Unreported operands.** `(Port.write len).unreported` is a written operand whose final
  contents the judgment does not report: caller-supplied scratch, or a matrix destroyed by a
  factorization. Nothing outside it changes; nothing is claimed of what it holds.
- **Separation.** `Routine.sep` names one of two fixed rules, and `Routine.SeparatedAt` is what
  the judgment requires. Under `.buffers` (`Routine.Separated`) two operands are in different
  buffers unless both are merely read (`Access.apart`, `Routine.separated_iff_pairwise`); an
  `isolated` operand is therefore in a buffer of its own. Under `.blocks`
  (`Routine.SeparatedBlocks`) the same holds of the blocks instead of the buffers, so operands
  may be disjoint blocks of one buffer. Operands separated by buffer satisfy both
  (`Routine.separatedAt_of_separated`). An author chooses between the two rules and cannot state
  another admission of operands.
- **Continuation.** `(Port.write len).continuing` continues the operand before it: its
  block is in the same buffer and starts where that block ends at the dimensions of the call.
  It is written in an explicit list of operands, not in a `routine%` header, because it must
  directly follow the operand it continues, which is not the order of a header.
  A basis of `k` columns read and the next `b` columns written is two operands, the second
  continuing the first (`Catalog/OrthRoutine.lean`, `extendRoutine`). The position is fixed by
  the interface, so a call supplies one operand per region (`Port.regions`, `Routine.arity`),
  and `Routine.operands` gives the positions of all operands. Separation is stated on the
  regions: an operand and those that continue it are one block, written if any of them is.
- **Layout.** By default buffer variable `i` of the tree is operand `i`. `binds := some l` makes
  buffer variable `i` operand `l[i]`; the tree is not changed. The buffer variables of a tree
  are its inputs and then its outputs, the form of the contract of an operation, so a block
  updated in place is two buffer variables and one operand: `routine%` generates that layout
  from the header. A tree written for its operands directly, with one buffer variable for an
  operand it updates, takes the clause `one variable` and has no layout; its program is then the
  tree with no frame around it, which is why the top-level routines of shifted QR are written so. A tree that is correct
  on several aliasing patterns of its operands is one routine per pattern, each written with
  `routine%` by naming the shared operand in several positions (`Profiles/RCLikeScalar.lean`:
  `(a : 1, x : n, x) → (x)` runs `axpy` with one vector). A layout is written by hand in two
  places, each documented at the definition: where the written blocks must follow the output
  order of an operation contract rather than the macro's order (`Examples/CgsQR.lean`), and
  where a continuation must directly follow the operand it continues (`extendRoutine`). A third
  is not yet converted: the zero start of rounded preconditioned CG
  (`Krylov/CG/HSPCG/Rounded/ZeroStart.lean`) runs its solver on its own variables without a
  frame, unlike its exact sibling, so its routine has a hand layout and its solver is a
  fragment; it is to be written like the exact one.
- **Draws.** `Routine.draws d` is `some k` when the routine consumes exactly `k` tape positions at
  the dimensions `d`, and `none` when that number depends on the data (a rejection loop, an
  early stop); the judgment then makes no claim on the final tape position.
- **Specification.** `Routine.Spec` is a precondition on the dimensions, the draws and the blocks
  read, and a postcondition relating them to the blocks written. The draws are the tape seen
  from the position of the call, on any stream. It mentions no memory, operand or tree.
  `spec% [n, k] (bs) → (xs, rs, ps) requires P ensures Q` writes one on named dimensions and
  blocks; `Routine.Spec.ofRel` reads one off the block relation of an operation contract.
- **Judgment.** `Routine.Meets R I S`: at every memory, on live separated operands with the read
  blocks in the precondition and room for the written blocks, the tree terminates, changes only
  the written blocks, advances the tape by the declared draws, and the written blocks satisfy
  the postcondition. It is the only judgment of routines, and it holds on every tape.
- **Probability.** A guarantee that holds only with high probability over the draws is not a
  `Meets`. Its statement is `PWrites` (`Logic/Probabilistic.lean`): in operand form, the run
  writes only its footprint and ends in the postcondition on a good set of tapes, and the good
  set fails with probability at most $\varphi$ under the stream laws. Its rules mirror those of
  `Writes`, with failure probabilities that add; a deterministic step enters with
  `PWrites.of_writes`, inside which `call` applies as usual. A routine with such a guarantee
  states `Routine.Spec.terminates` as its judgment (termination and footprint on every tape) and
  its accuracy as a `PWrites` statement or a probability theorem about the same run (the
  small-eigenvalue solver, rounded shifted QR). There is no routine-level form of `PWrites`
  yet: its statements name operands.
- **Calling.** A caller runs a routine by its interface, `run R [dims] (operands)`, one operand
  per operand of the routine (an operand updated in place is named once; the layout is applied
  by the builder). A fragment's tree is run by its buffer variables, `run t [dims] (vars)`. The
  caller uses the routine's judgment with the tactic `call` (the rule is `Routine.Meets.call`); it learns the
  footprint and the postcondition, and nothing of the tree. The cost of the caller includes the
  callee because the callee's tree is in the caller's tree.
- **Linking.** A routine implements an operation contract of a model when the admitted operands
  of the contract are separated operands of the routine (`Routine.Implements`,
  `RoutineLink.lean`); the contract of the operation is then a corollary of the judgment
  (`Routine.Meets.satisfies_ofRel`), and linking grounds it under the induced interpretation
  (`Interp.link_satisfies`). `Routine.link` is a routine with its tree linked through a table, and
  `Routine.Meets.of_link` transfers the judgment. The level-1 loops (`Blas/Sum.lean`, `Dot.lean`, `Level1.lean`), the stored
  matrix-vector leaves (`Profiles/StoredRoutine.lean`, `StoredDense.lean`, `StoredCOO.lean`),
  the exact reductions of `Profiles/RCLikeScalar.lean`, the vector draw (`Profiles/Random.lean`)
  and the examples `Gemm`, `GramSchmidt`, `CgsQR`, `Bilinear`, `Hutch`, `Noisy`, `NoisyLinked`
  are proved this way. An operation contract that admits several layouts of its operands (an
  output apart from a vector input or exactly that input: `copy`, `scal`, `axpy`, the real
  conjugation) is implemented by one routine for each layout, all with the same tree: separate
  operands, or the vector updated in place with its buffer variables bound to one operand. The
  contract follows by cases on the admission (`Routine.Meets.writes_ofRel`;
  `Profiles/RCLikeScalar.lean`, `Profiles/RealStar.lean`).
- **Certifying.** `Routine.close` is the program of a routine on a problem: the tree, with the
  sizes as dimensions and the supplied buffers as operands. The initial environment of a
  program has one buffer variable per supplied buffer, at its start. The program of a routine
  without a layout is its tree; the program of a routine with a layout is one frame of its tree
  on the supplied buffers in the layout, and that frame is counted like any other. A routine
  with an operand that continues another has no program (the position of the continuation is
  not the start of a buffer); it is called by a frame.
  `Routine.algorithm` is the one constructor: it certifies the program against any
  `Specification`, for any weights, from `Meets` under every interpretation of the model.
  Liveness and separation of the supplied buffers are not hypotheses; they hold for every
  problem. A counted certificate is a corollary of it: `(algorithm …).withCountPoly …` replaces
  the work by a bound on `Program.countPoly`, the instruction polynomial the kernel computes
  from the fixed instrumented tree (`countedAlgorithm` in each family). The closed form of the
  polynomial is checked by `kernel_rfl` (`Logic/KernelRfl.lean`), which leaves the reduction to
  the kernel (the elaborator's `rfl` can be slow when the tree has a free parameter), and
  evaluated at the sizes by `poly_eval`. It needs every weight of the model to be at most one,
  because a count of instructions bounds the work only then. `Routine.certify` is the same
  construction for a routine whose certificate states exactly its specification. No statement
  about cost is taken from the author of the routine.

A reviewer of a certified routine reads its `Routine.Spec`, the problem (what is supplied), the
model (which operations exist and what each costs) and the stated work. `Examples/Routine.lean`
and `Examples/RoutineCertification.lean` are a complete small case, ending in a statement in
terms of the evaluator alone.

The names of routines, specifications, judgments, certificates and their files follow one
convention in every family, stated in
[Programs and certificates](../../docs/contributing/programs.md) ("Names of routines, files and
certificates").

### Three statements

Three statements have three roles. `Routine.Meets` is what an author states about a routine.
`Interp.Satisfies` says that an interpretation satisfies the contract of a primitive operation;
operation models are made of it. `Impl.Satisfies` says that an implementation of an operation
satisfies that contract; it is derived from the judgments of the routines that share the
entry's tree and consumed by linking.

An `Impl` is an implementation of an operation: the entry of a linking table, a tree with the
arity of the operation. It is the tree of a routine (`Routine.impl`). It is a separate type from
`Routine` because one tree may implement an operation whose contract
admits several layouts of the operands, which are several routines sharing that tree: the
`axpy` entry of `RCLikeScalar.table` is one tree, and its contract admits the output apart from
both vectors, on either vector in place and on both at once. `Impl.Satisfies` is then proved by
cases on the layout from the judgments of those routines (`Routine.Meets.satisfies_ofRel` when
there is one layout). An entry is written directly only where no routine can describe it: the
entry of a context table, whose first inputs are the context forwarded to every call
(`ContextDense.impl`); an implementation that does not always terminate, for liberal mode
(`Examples/Liberal.lean`); and the examples that prove a contract from the run of the entry
itself, the layer under routine judgments (`Examples/Dot.lean`, `MatMul.lean`, `Bits.lean`,
`StochRound.lean`). A tree that is not an implementation of an operation is a plain `Stmt`
(`ops%`), or a routine (`routine%`) when it has an interface of its own.

Operation meanings and primitive costs, the declared input representation, and the relevance of
the specified postcondition remain properties of the chosen problem and operation model.

## Proof construction

The statement interpreters `eval` and `evalCounted`, judgments `ConditionalRuns`,
`ConditionalRunsW`, `ConditionalRunsL`, and conditional implementation relation `Impl.Satisfies`
form the proof calculus. `Wp` and its constructor rules can express total or liberal correctness.
`Profile.Refines` transfers conditional contracts and resource bounds through a fixed table.
These constructions do not assert model realizability or uniformity of a runtime tree family.
They are useful ingredients for a canonical certificate, not substitutes for one.

`ConditionalRuns` is a total execution theorem under its explicit input and interpretation
hypotheses. It does not assume that execution succeeds. The liberal form `ConditionalRunsL`
is partial correctness and is useful only as an internal proof step toward a total result.

The named builder in `Logic/Builder.lean` elaborates to the same statement trees. Use
`let t ← alloc n` for scratch of `n` cells of one byte each (`StorageFormat.cell`), the format of
every model that does not distinguish storage widths, and `let t ← allocAs format n` when the
model charges memory by a storage format (a floating-point width, say).
`Logic/Writes.lean` provides format-aware single and chained allocation rules, and
`Logic/Tactic.lean` supplies `alloc as`, `loop_inv`, `keep`, and `checkpoint` for block proofs.

The catalog supplies exact and standard-error scalar contracts, exact and error-bounded BLAS1,
and matrix-vector and comparison contracts. Sequential and pairwise BLAS profiles prove their
contracts through `Profile.Refines`. The CG, PCG, and Lanczos developments use this conditional
proof layer; a canonical certificate additionally fixes the problem, realized model, and full
resource specification.
The existing BLAS profiles allocate abstract `.cell` scratch. A format-specific specialization
uses explicitly formatted allocation and workspace measured in the same modeled byte units.

## Standard collections and stored implementations

`Profiles/Standard.lean` supplies exact, sequential-rounded and pairwise-rounded numerical
models for Krylov analysis. `Profiles/ExactBlas.lean` generates the exact scalar/vector
collection for real or complex words. `ExactLinear` adds explicitly stored operators,
sampling and dimension literals; `ExactScalarLinear` replaces BLAS by scalar conjugation;
`ScalarOnly` contains no vector or matrix-operation names. `Catalog/Functional.lean`
generates exhaustive local contracts and a joint realization from the declared functions
and spatial admissions. Primitive meanings, admissions, weights and word encodings remain
explicit model choices.

`Profiles/RCLikeScalar.lean` implements the six BLAS operations using scalar arithmetic and
conjugation (the trees, routines and table are in `Profiles/RCLikeScalarTrees.lean`).
`StoredDense` and `StoredCOO` implement matrix application from declared matrix words;
`StoredScalar` composes their tables into the scalar-only signature, taking the leaf as a
routine. Linking retains
the complete lower instruction tree and its temporaries.

`RoundedBlas` supplies the sequential standard-error scalar/vector collection.
`RoundedScalarBlas` lowers that collection to `ScalarOp` alone and derives its contracts
from the supplied scalar machine. `StoredDense.rowWord` identifies the exact word recurrence
of streamed matrix products for that same machine; rowwise error follows from `StdModel`.
The Matrix layer converts the row bounds to a normwise allowance for the actual raw matrix.
Carried CG and both Lanczos variants combine these bridges into rounded stored scalar-only
certificates, with resources recomputed after lowering. Finite-format mixed-error models
remain separate from the unbounded-exponent standard relative model.

`Context.lean` forwards fixed extra input capabilities through procedure frames.
A routine written against an operation that only an oracle provides (a product with a matrix)
becomes a routine on stored data with `Routine.withData` (`RoutineData.lean`): the data blocks are
new leading `isolated` operands, forwarded to every call of the operation. Its specification is
`Spec.onData c P S₀`, the matrix-free specification `S₀` at the decoded data, for data that
satisfy `P`; `Routine.Meets.withData` gives its judgment from the judgment of the matrix-free
routine under the interpretation in which the operation reads the stored words, with no other
proof about the tree. Underneath, `Logic/IsolatedLink.lean` transfers a word proof through the
forwarding, the isolated buffers keeping their words (`Logic/Isolated.lean`).
`ContextProblem.lean` prefixes supplied raw buffers and proves their reads, capacities and
resident payload. Stored CG/PCG and Lanczos are built this way. The proof-side
source guard never becomes an omitted runtime operation. See the
[current program guide](../../docs/contributing/programs.md) and
[context design](../../docs/design/Ops-Context-Linking.md).

## Files

| File | Role |
| --- | --- |
| `Syntax.lean` | Index/operand/control syntax, fixed `Program`, structural elaboration |
| `Exec.lean` | Canonical `run`/`exec`, statement interpreters, memory projection |
| `Contract.lean` | Contracts, `Problem`, declared query contracts, closed `AccessModel` |
| `Static.lean` | Full `staticCost`/`staticPeak`, `Runs`, static soundness |
| `Cert.lean` | `Algorithm`, `Impl.Satisfies` (a tree implements an operation contract), constructors |
| `RoutineInterface.lean` | The interface of a routine: access modes, ports, regions, the two separation rules |
| `Routine.lean` | Routines: specifications, the judgment `Meets`, calls, programs and certificates |
| `RoutineSyntax.lean` | `routine%` and `spec%`: a routine and a specification on named dimensions and operands |
| `Logic/RoutineIntro.lean` | The tactics of routine proofs: `routine_intro`, `call`, `routine_exit`, `read_outputs`, `implements`, `routine_sep` |
| `Logic/KernelRfl.lean` | `kernel_rfl`: closed computations (instruction polynomials) checked by the kernel |
| `Certification.lean` | Adapters for certificates: reading supplied buffers, counts without structural instructions |
| `RoutineLink.lean` | A routine as the implementation of an operation contract; specifications read off a contract |
| `RoutineData.lean` | A routine on stored data (`Routine.withData`), its specification (`Spec.onData`) and judgment (`Meets.withData`) |
| `Link.lean`, `Transfer.lean` | Fixed implementation tables, count projections and explicit weights |
| `Logic.lean`, `Rules.lean`, `Counted.lean` | Conditional proof rules |
| `Store.lean`, `Frame.lean` | Buffer memory, liveness, shape preservation and frames |
| `Tape.lean`, `TapeLaw.lean`, `Law.lean` | Tape locality, laws and output observations |
| `Catalog/`, `Blas/`, `Profiles/` | Operation contracts and conditional implementations |
| `Examples/Certification.lean` | Repeated-addition certificate and adversarial regressions |
| `Examples/Resources.lean` | Mixed-format storage, workspace, and work/span certificates |
| `Confined.lean`, `Profiles/Confined.lean` | Confined, uniform and charged models |
| `Examples/Oracles.lean` | Misleading certificates the types accept and these properties reject |
| `Examples/Integrator.lean`, `IntegratorLink.lean` | The integrator of the *Programs, models and certificates* page: routines, model, certificate, linking |

The regressions address the canonical interfaces directly: impossible joint models, vacuous
inputs/tapes, runtime tree factories, failed execution, undeclared calls, omitted structural work,
and index arithmetic in a zero-round loop. No test invokes a linter to establish rejection.

This file is the current design of the layer. An earlier design, with a different vocabulary, is
recorded in [Ops-Certification](../../docs/design/Ops-Certification.md) (history only).
Breaking API changes: [rename map](../../docs/renames/Ops-certification.md) and the JSON maps in
`docs/renames/`.
