# Exact semidefinite routine contract review

Independent read-only review of `SemidefiniteCholeskyRoutine.lean` found no material issue.
The generic-word certificate requires actual execution, the original exact-sized output write,
and lower triangularity, nonnegative diagonal and the decoded Gram identity. It imposes no
scalar zero/encoding instance on the word carrier. Its block-routine projection retains
composability and the exact singleton write. The actual real/exact-semantics instance consumes
the existing zero-safe PSD execution theorem, including source/output overlap and empty invalid
handles. It makes no indefinite or rounded success claim.

Both existing `IsCholesky` and `IsCholeskyErr` require strictly positive diagonal. The PSD
certificate uses the direct nonnegative triple and changes neither predicate. The cost-target
proposal was corrected to use that triple too; its initial independent review had missed this
difference and recorded the correction explicitly.

The new module passed strict private Lean and source checks before integration. Fresh canonical
build, lint and kernel replay remain the authoritative integration checks.
