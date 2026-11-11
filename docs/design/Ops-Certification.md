# Structural certification of operation programs

Requested by the maintainer in the 2026-11-11 adversarial-audit conversation.
The general relational contracts remain unchanged. Lint is guidance, never evidence.

## Boundary

`Stmt`, `Wp`, `ConditionalRuns`, `ConditionalRunsL`, and `Impl.Triple` are proof infrastructure. A published
algorithm is one fixed symbolic tree, certified for every admitted size and input.
Its operation and query signatures, input layout, contracts, postcondition, and cost model
are specified independently of the prover. Their mathematical relevance remains reviewed.

No constructor of a certification object takes a function from concrete sizes or inputs
to a tree. Linking takes a fixed table and produces one fixed tree. Rational literals and
operation identities in the tree are consequently independent of the runtime sizes.
Sizes enter the environment; inputs enter declared buffers. An external family of
certificates for separately specialized specifications is not one certificate for the
original specification.

## Objects and interfaces

* `Program Op Tst r b`: one `Stmt Op Tst`, with `r` runtime size arguments and `b`
  initial buffers. The execution environment is fixed: sizes followed by zero offsets,
  and handles `0, ..., b - 1`. There is no host environment callback.
* `Problem K r b`: semantic data indexed by sizes, admitted sizes, raw-buffer admissibility,
  an input at some admitted size, and inhabited input types at every admitted size. An `Input`
  contains semantic data, supplied raw buffers and an admissibility proof. Initial memory
  lists those buffers directly; there is no word-computing initializer callback.
* `AccessModel Op Tst P`: an actual stored word (so tapes are inhabited), declared operation/query contracts at each admitted problem instance, fixed operation workspaces,
  and a proof that the exact joint contracts can
  be realized at every admitted instance. Shared parameters remain in the proposition;
  no predicate names are inspected or matched.
* `Specification Op Tst P`: joint operation/query/structural budget, scratch budget,
  and postcondition. All budgets depend on sizes alone. The postcondition may depend
  on the actual inputs and tape, and may inspect the actual counts.
* `Algorithm M S`: one `Program` and a total counted correctness proof over every
  size, input, interpretation satisfying `M`, and tape, with the index/control bound.
  A liberal theorem or a theorem of `True` cannot inhabit the correctness field.
  `Program.Certifies p M S` is the corresponding proposition for a target whose tree
  is fixed in advance: `theorem result : p.Certifies M S`.

These are specific to NLAlib's syntax and evaluator. Searched Mathlib's computability
interfaces and the existing Ops contracts; there is no equivalent object. Existing
`ConditionalRunsW`, `Count`, `staticCost`, `staticPeak`, and the execution/linking theorems are reused.

## Accounting

Operation and query counts retain the specified abstract-operation meaning. Index
expression evaluation, operand addressing, control, and allocation initialization are
recorded as distinct operation names by instrumenting the tree for the existing counted
evaluator, with a proved projection to the source run. This is
an explicit unit-operation accounting, not a bit-complexity or wall-clock claim.
The runtime evaluation has only the index operations in `IExp`; it cannot invoke an
arbitrary Lean callback. A different primitive cost model still needs a realization.

## Statement shapes

The essential quantifier order is:

```lean
structure Algorithm (M : AccessModel Op Tst P) (S : Specification Op Tst P) where
  program : Program Op Tst r b
  correct : forall d, P.valid d -> forall x : P.Input d,
    forall I, M.contracts d x I -> forall tape,
      -- successful execution of this same program, within S's budgets,
      -- with S's postcondition on this same execution
```

The model includes `forall d, P.valid d -> forall x, exists I, M.contracts d x I`.
The specification contains no program argument. Linking takes its fixed table before
the runtime arguments, transfers correctness, and requires the resulting bounds to
fit the independently supplied lower specification. Its bookkeeping is recomputed for
the entire linked tree, including frames and introduced scratch.

## Canonical integration

The 2026-11-11 follow-up replaces the additive prototype. There are no optional
`Program.lean`, `Algorithm.lean` or `Overhead.lean` modules.

* `Syntax.lean` owns `Program`, its fixed initial environment, `Bookkeeping`, and the
  fixed structural elaborator. The operation and query types are the closed model signature.
  Syntax cannot invoke any other operation or execute host callbacks on runtime data.
* `Exec.lean` owns canonical `run p I tape d mem` and `exec p I W tape d mem`.
  `exec` always elaborates structural accounting; there is no bypass flag. `exec_mem`
  proves that it has precisely the same results and failures as `run`.
  The statement interpreters are explicitly called `eval` and `evalCounted`.
* `Contract.lean` owns `Problem`, `QueryContract` and `AccessModel`. Every operation
  has a declared `Contract`, and every query a declared `QueryContract`. The interpretation assumptions are defined to be exactly satisfaction of those contracts,
  and must have a joint realization. There is no arbitrary stronger assumption field.
* `Static.lean` owns `Specification`, canonical `Runs p M S`, and full `staticCost`
  and `staticPeak`. `Program.Certifies` is the method spelling of `Runs`.
  Raw statement budget functions are `stmtCost` and `stmtPeak`; raw judgments are
  `ConditionalRuns`, `ConditionalRunsW`, and `ConditionalRunsL`.
* `Cert.lean` owns `Algorithm`, constructors from total program logic, and fixed linking.
  Canonical `Impl.Meets R ins outs M S` certifies a fixed `Impl.program` frame with fixed
  operand syntax. Conditional implementation contracts are named `Impl.Triple`.
* `Link.lean` owns `Impl.program` (preserves operand aliases) and fixed `Program.link`.
* `Law.lean` owns `Algorithm.runsLaw`; the conditional law judgment is
  `ConditionalRunsLaw`, and observes the same successful execution.
* `Transfer.lean` provides `Count.original`, explicitly a projection, and
  `Count.totalWeight` with mandatory operation, query and structural weights.
* `Examples/Certification.lean` proves a real repeated-addition certificate and attacks
  the canonical interfaces directly: failed execution, impossible joint models, vacuous
  domains, runtime tree factories, omitted structural work, and undeclared calls.

Existing BLAS, profile, logic and example consumers migrate to explicitly conditional
interfaces. They remain construction lemmas, not promoted canonical certificates. No target,
registered approval, check implementation or rule waiver is changed. Downstream numerical
agents must supply independently realized models when turning those lemmas into canonical
algorithm claims.

## Format-aware resource follow-up

The canonical interfaces were extended in the subsequent requested implementation:
[Ops-Resources](Ops-Resources.md). Problem fixes input storage formats; AccessModel fixes a
ResourceModel; canonical exec/run check lexical buffer signatures and input arity. Allocation
charges positive format width times capacity. Specification additionally requires full modeled
work/span and total initial-plus-scratch payload bounds. Query workspace is conservatively
reserved from actual executed query keys. Physical encoding and timing remain model-justification
obligations; opaque K and nominal format tags alone do not prove representability in bits.
