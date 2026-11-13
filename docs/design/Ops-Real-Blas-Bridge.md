# Exact real vector contracts across operation collections

The Hermitian `RCLikeBlas` collection and ordinary decoded `IsExactBlas1` collection share
operation names but expose different local contracts. Over real words conjugation is the
identity. Their vector formulas therefore agree, including division-based scaling and empty
vectors. The bridge derives all six ordinary decoded contracts from the Hermitian functional
contracts without adding an algorithm predicate or another operation implementation.

The admission implication must use the actual precondition. `OutApart` and `InPlace` describe
buffer relationships without constraining list arity. A bare implication from those predicates
to a shape-matching functional admission is false on malformed operands. Successful block reads
and output capacity supply the missing arities. The generic `Interp.IsFn.meets_rel_of_pre` rule
therefore exposes those two facts when proving admission, while retaining the existing local
functional-call semantics and relational output proof.

`RCLikeBlas.IsExact.toExactBlas1` specializes that rule. Reductions derive spatial separation
from distinct buffers; in-place updates derive exact alias for the last input and separation
for earlier inputs. No stored value is preprocessed or numerically altered by this proof.
