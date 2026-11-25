# Closed-form cost-target review packet

Seven exact cost-target candidates, seven nonvacuity obligations and seven comparisons of the
actual static counts with independent cubic budgets have checked proofs. This packet preserves the prepublication review artifacts. The maintainer approved
publication and commit/push on 2026-11-25; see the
[delivery report](../../Matrix-DenseFactorizationDelivery.md) for the published modules and checks. The [proposal](../../Matrix-DenseFactorizationTargetProposal.md) specifies the domains,
model and budgets. The approval satisfies AGENTS.md rule 2 for these seven statements.

`ClosedCountBudget` explicitly lists the 23 operation kinds possible with Unit tags and Empty
oracle/kernel names. Each coordinate gets `1024*(N+1)^3`, independent of every program tree.
`DraftCountSupport` supplies ordinary pointwise count lemmas. `CountBoundTactic` constructs
ordinary proof terms compositionally; its recursion is structurally bounded by explicit fuel
4096, with failure at zero. It has focused imports, no `partial` definition and no native
proof oracle. Each concrete count comparison is checked by Lean's kernel.

`DraftSupport` connects actual numerical success and the independent count/space comparisons
to the proposed closed budget. The LU, pivoted and Cholesky proof modules prove exactly the
seven candidates and their nonvacuity conditions. Input-only domains, actual factor/log reads,
source retention, shapes and the closed memory envelopes are preserved. Singular PSD uses
lower triangularity, nonnegative diagonal and the Gram identity, without weakening either
strict-positive Cholesky predicate.

All eleven modules were compiled again in a fresh directory against the integrated library
with all project options and warnings as errors. The combined `AllAxioms` audit reports only
`propext`, `Classical.choice` and `Quot.sound` for all 21 obligations. See [axioms.txt](axioms.txt)
and the source hashes in [manifest.json](manifest.json). Only the scaled count comparison uses
a documented local proof-checking allowance of 800000 heartbeats; this changes neither the
algorithm's runtime nor its stated budget. There are no admissions or additional axioms.

The actual registry H4 `costErrors` check accepts all seven statements. Its witness and
decoding checks also accept all seven; explicit matrix/None-capacity initializers produce no
precomputed-input flags. Nonvacuity aliases are transparent, preserving the exact proposition
while exposing the required witness shape. See [companion-check.txt](companion-check.txt). The test concatenated
the budget and candidate definitions into its current file, ensuring helper definitions were
fully traversed; imported draft-module opacity could not conceal a static-cost reference.
The earlier tree-derived count draft was rejected by the same check and is superseded.
[h4-check.txt](h4-check.txt) records the passing result. Static analysis is used inside proofs,
not in the target count, memory or postcondition.

The `.lean.txt` extension keeps this review packet outside the published library. To reproduce
its proof checks from the implementation checkout, first build `NLAlib`, then run:

```bash
review_dir=/tmp/nlalib-dense-target-review
mkdir -p "$review_dir"
for name in ClosedCountBudget DenseFactorizationTargetDraft DraftCountSupport CountBoundTactic DraftSupport DraftLUCounts DraftPivotedCounts DraftCholeskyCounts DraftLUProofs DraftPivotedProofs DraftCholeskyProofs AllAxioms; do
  cp "docs/design/dense-factorization-audits/target-proof-review/$name.lean.txt" "$review_dir/$name.lean"
done
lake env bash -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for name in ClosedCountBudget DenseFactorizationTargetDraft DraftCountSupport CountBoundTactic DraftSupport DraftLUCounts DraftPivotedCounts DraftCholeskyCounts DraftLUProofs DraftPivotedProofs DraftCholeskyProofs; do
    lean --root="$1" -DautoImplicit=false -DmaxSynthPendingDepth=3 \
      -Dlinter.missingDocs=true -Dlinter.mathlibStandardSet=true \
      -Dlinter.style.header=true -DwarningAsError=true \
      "$1/$name.lean" -o "$1/$name.olean" || exit
  done
  lean --root="$1" "$1/AllAxioms.lean"
' _ "$review_dir"
```

These are conservative exact real-word, standard-charge, declared-input bounds with zero ROM
length and zero bit width. They do not assert native IEEE accuracy, physical RAM usage,
ROM-loading cost, sharp flop constants or costs for every additional policy/blocked variant.
