# Local contracts for CG flag initialization

CG's stored and oracle pre-dot setup performs only literal loading, exact negation, copies,
zero filling and, for the stored tree, ROM loading. Its global scalar relative-error contract
is stronger than these operations require. The subsequent self-dot and rounded recurrence
still need their numerical arithmetic hypotheses.

Generalize `CGImplementation.exists_cg_flag_words` to local zero-literal success and exact
decoding, one-literal success with the existing `RelErr` predicate, and defined exact negation.
The unit-roundoff bound below one still proves the positive flag sign, and the relative
literal error still yields the existing absolute distance from one.

Generalize both existing `exec_rounded_setup` declarations to the actual flag words and
their literal, negation and decoding facts. The stored setup additionally loads the supplied
ROM words; the oracle setup preserves the same input words without matrix storage. Their
full-initializer callers obtain these local facts from their existing relative model before
executing setup, and retain that model for the dot kernel and later numerical work.

The separate `CGInitializationIEEE` module proves successful zero and one literals with
actual checked binary64 words, derives exact negation from its existing arithmetic
certificate, and instantiates both generalized setup APIs in every dimension. The stored
result retains the actual ROM condition. Neither finite endpoint assumes initialized flag
words, a successful future trajectory, an all-range relative model, or dot-kernel success.

These are three public signature changes with unchanged names, recorded in the rename log.
No new predicate, program, target or arithmetic semantics is introduced.
