# Literal-only Lanczos initialization

The existing Lanczos zero prefix used its global relative-error arithmetic contract only
to obtain one successful literal zero. Extract its execution and frame proof into
`LanczosImplementation.exec_initialize_zeros_of_lit_eq_some` in the existing exact initialization
module, parametrized by the actual literal word and
its execution equation. Preserve `exec_rounded_initialize_zeros` and its statement as the
existing relative-model wrapper, implemented by the new weaker theorem.

The zero-norm initialization branch similarly requires only the successful zero literal,
the actual norm and zero-cell reads, and the successful true comparison. It fills the first
basis column without calling copy or division. A separate theorem retains execution,
the frame, shape and exact operation charges under just these local hypotheses.

Concrete binary64 specializations use `finiteFloatSem` to prove the required literal and
comparison properties, rather than assume them. They apply to arbitrary dimensions, budgets
and stored input words, subject only to the actual writable workspace shape. This certifies
the prefix and the zero continuation, not the preceding norm computation, a nonzero
normalization branch, the full Lanczos loop or a backward-error theorem.

No new program tree, target, algorithm or mathematical vocabulary is introduced. Existing
relative-model callers retain their public theorem type and application order.

The exact workspace theorem also uses this shared primitive, preserving its public statement,
compressed exact literal count and all frame postconditions. The existing exact
`exec_initialize_zeros` remains unchanged and distinct from the new local-literal API.
The rounded and finite modules import the shared implementation rather than redeclare it.
