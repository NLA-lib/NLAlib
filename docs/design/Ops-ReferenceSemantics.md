# A reference semantics for Ops certificates

Status: implemented, and the rules are the definition. A certificate
(`Program.Certifies`, through `Specification.Accepts` in `NLAlib/Ops/Specification.lean`) is
stated with `Reference.Execution`. The evaluator `exec` has a kernel-checked two-way
equivalence with the rules and is proof machinery; the theorems named `_exec` restate each
statement with it. The rules do not validate the definitions they share with the evaluator.
The reviewer-facing list is [Ops-ReferenceReview.md](Ops-ReferenceReview.md).

## Purpose and review boundary

A recipient should be able to read mathematical rules for execution and accounting,
then rely on kernel-checked equivalence to connect those rules to `exec`. Merely
defining a relation by equality with `exec` would not achieve this.

The reference relation runs the original `Stmt`. It does not run `Stmt.instrument`,
call `eval` or `evalCounted`, or use a static cost/peak calculation. Primitive calls
are described by `Interp.call`, operand liveness, and preservation of store shape.
Index/address evaluation, branches, rounds, frames, allocation and release have
explicit charges in the rules. Counts are finite-support functions, as in Mathlib.

The shared definitions a semantic reviewer must also read are `Store`, `Mem`, `St`,
`Count`, the finite-support count constructors and `ResourceModel.queryReserve`,
`IExp.eval` and `Operand.evalList`, the syntax types, `Program.environment`, the
format predicate `Program.wellTyped`, and the primitive contracts and resource
model. In particular this first stage does not independently specify the lexical
format checker or the input codecs. Reusing their definitions is an explicit
boundary, not a claim to have independently verified them.

## Objects and vocabulary

| Concept | Lean name | Existing object / bridge |
|---|---|---|
| Accounting state | `Reference.State` | Abbreviation of `St`; no new state representation |
| Structural charge | `Reference.core`, `Reference.index`, `Reference.dimensions`, `Reference.operands` | `Count`, Mathlib `Finsupp`; independent of instrumentation |
| State after a charge | `Reference.charge` | Adds a count, preserving memory and scratch |
| Successful source execution | `Reference.Derives` | Inductively generated inference rules; `Reference.execution_iff_exec` bridges to canonical `exec` |
| Counted-loop execution | `Reference.Repeats` | Auxiliary indexed judgment, including one round charge per body execution |
| Early-exit execution | `Reference.While` | Auxiliary fuel/index judgment, including the actual queries |
| Checked program execution | `Reference.Execution` | Source derivation, format/arity checks, final query reservation |

These are definitions about NLAlib syntax, not replacement notions for a Mathlib
object. A search of the existing Ops modules and Mathlib's computability modules
found no existing judgment for this statement language. Existing evaluator bridge
lemmas in `Exec.lean` are material for the equivalence proofs, not definitions of
the reference relation.

## Statement shapes and consumers

The main bridge has this shape, with no admission, success, cost or numerical
assumptions (the actual parameters `I`, `R`, `tau` precede `p`):

```lean
theorem execution_iff_exec {r b : ℕ} (p : Program Op Tst r b)
    (I : Interp Op Tst K) (R : ResourceModel Op Tst)
    (formats : Fin b → StorageFormat) (τ : Tape K) (d : Fin r → ℕ)
    (m : Mem K) (out : St (Op ⊕ Bookkeeping) Tst K) :
    Reference.Execution p I R formats τ d m out ↔
      exec p I R formats τ d m = some out
```

This is equality of the entire outcome, including memory, tape position, count,
live scratch and peak. Its two directions provide completeness as well as
soundness. Failure is the absence of any derivation:

```lean
theorem exec_eq_none_iff ... :
    exec p I R formats τ d m = none ↔
      ¬ ∃ out, Reference.Execution p I R formats τ d m out
```

`Specification.Accepts S p I R τ d x Q` says that the rules derive an outcome of `p` from the
buffers of `x`, within the five resource bounds, whose count and memory satisfy `Q`. `Runs`
(`Program.Certifies`) says that every run is accepted with the output condition of the
specification, and `Algorithm.FailsAtMost` bounds the measure of the tapes at which a run is
not accepted with the accuracy event. `Inputs.Checked` and the readable `_checked` statements
are stated the same way.

### Evaluator forms

Proofs compute with the evaluator. `Specification.accepts_iff_exec` and
`Program.certifies_iff_exec` (`Reference/Equivalence.lean`) restate acceptance and
certification with `exec = some`, with all five resource inequalities and `good`;
`Algorithm.correct_exec` is the evaluator form of a certificate's field `correct`.
`Algorithm.failsAtMost_iff_exec` and `RandomizedClaim.holds_exec`
(`Reference/Probability.lean`) do the same for a randomized claim, under the same law,
`admits`, `interprets`, event and bound. The equivalence is pointwise in the tape, so no
measurability premise or second probability calculus is needed. Realizability remains the
claim's existing field.

`Examples/Reference.lean` also includes nested 2-byte and 8-byte allocations, a
7-byte primitive workspace, and a 5-byte query workspace after the inner buffer
has been released. The expected payloads are stated independently: 29 bytes at
the primitive peak, 34 after the conservative query reservation, and 42 including
an 8-byte initial buffer. Primitive/query/core weights differ, giving work 22
and span 13. Derivations use the reference rules before transfer to `exec`.

`Ops-ReferenceReview.md` is the reviewer-facing declaration map. It distinguishes
the semantic definitions, the standard arithmetic models, the claim-specific
assumptions and the kernel-checked bridge infrastructure. Its paths are relative
to the document, so they work in a checkout or on the repository host.

## Accounting choices that need independent review

* Counts include original calls, actual queries, and structural instructions.
* Scratch state excludes supplied buffers; the certificate adds their payload.
* A call reserves live allocation bytes plus the primitive workspace. Allocation
  reserves width times capacity; its body is evaluated before release.
* Query workspace follows the current public convention: the maximum declared
  workspace among executed query keys is added to the allocation/primitive peak.
  This is a conservative reservation, not an exact simultaneous-live-byte claim.
* An early-exit loop reserves one final dimension/address charge with `exit`,
  even when fuel is exhausted without a final query. This intentional allowance
  must be visible, rather than described as an actual query execution.
* Notes have no semantic or resource effect. Abort has no successful derivation.
* Primitive execution time and word encoding remain assumptions of the named
  model, in the library's abstract computational scope.

## Files and proof machinery

1. `NLAlib/Ops/Reference/Semantics.lean`: the small review surface, with charge
   definitions, inference rules, checked program execution and elementary rules.
2. `NLAlib/Ops/Reference/Accounting.lean`: tally bridges, the live-scratch/peak
   invariant, and equations for instrumented execution at source constructs.
3. `NLAlib/Ops/Reference/Equivalence.lean`: soundness/completeness, failure,
   determinism and the evaluator forms of acceptance and certification. Proofs belong here so that proof
   engineering does not enlarge the reference-rule file.
4. `NLAlib/Ops/Examples/Reference.lean`: the zero/one-fuel boundary with a refusing
   query and an aborting body, derived under the reference rules and transferred
   to canonical execution. Zero fuel performs no query and reserves four charges;
   one fuel unit fails at the query. The payload examples independently state
   nested allocation peaks, unequal widths/weights, query maxima and resident
   payload, then derive them under the reference rules.
5. `NLAlib/Ops/Reference/Probability.lean`: the evaluator form of the failure
   bound and of an existing `RandomizedClaim`.
6. `NLAlib/Ops/Specification.lean`: `Specification`, acceptance of one run and
   certification, stated with the rules.

The Ops README and the routine guide link the reviewer map, and the vocabulary
guide has the declarative execution and randomized read-back rows.

The loop bridges use shared induction lemmas for `iter` and `whileIter`, followed
by a statement induction. Structural charge equality is proved separately. The
existing `exec` wrappers and query-reservation equations are used only after the
source bridge. The general source bridge assumes live scratch does not exceed
its recorded peak; `consistent_of_evalCounted` preserves this invariant. Canonical
execution starts with zero live scratch and zero peak, so its equivalence theorem
has no additional hypothesis.

The evaluator and the contracts are unchanged. The certificate definitions are restated
with the rules; by `Program.certifies_iff_exec` each certificate states exactly what it stated
before, and no certified program, count or bound changes.

## Review questions

1. Are the shared memory/index/format definitions an acceptably small semantic
   boundary? Recommendation: retain them initially and document them explicitly.
2. Does the final early-exit allowance match the intended resource statement?
   Recommendation: state the current convention honestly; any accounting change
   should be separate from the equivalence work.
3. Should failures carry partial traces? Recommendation: not for this first bridge.
   Certificates require success, and exact absence of a derivation characterizes
   failure. Trace diagnostics can remain a separate tool.
