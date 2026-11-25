> Subsequent verification: all seven unchanged candidate propositions and all seven
> nonvacuity obligations now have privately checked proofs. See
> [the proof packet](target-proof-review/README.md). They remain unregistered pending approval.

# Independent seven-target draft review

Reviewed the canonical `DenseFactorizationTargetDraft.lean.txt` and
`Matrix-DenseFactorizationTargetProposal.md` against Model, Exact, FirstOrder, StaticCost,
the seven actual resource trees, Space/ResourceTags, and corresponding numerical interfaces.
Read-only: no source, protected registry, cache or build changes; no independent compilation
was run. The author reports strict compilation of the statement draft.

**Conclusion: no material blocker found.** This is a concrete reviewable AGENTS rule 2
maintainer packet, not approval, registration, or a proof of a published cost target.

- Every target is closed at Unit tags, Empty oracle names and real words. StoredEntries
  receives the fixed symbolic tree before N, offsets, matrix input, ROM values and tape.
  No tree, budget or supplied factor is selected from matrix values or an observed run.
- LU and scalar LDL domains use only original-matrix canonical nonzero pivots; LDL also
  requires Hermitian input. SPD/PSD domains use only their respective input predicates.
  PLU, PLUQ and fixed-original-scale PLU quantify over every real square matrix, including
  singular matrices. There is no assumed-success/run premise or output-dependent domain.
- Buffer and extra-size counts match the trees: LU/LDL 3/3, PLU/scaled 4/4, PLUQ 5/5,
  SPD/PSD 2/2. Prog adds the leading order variable to those offset vectors. The actual
  tree-to-builder rfl equations have the matching source/factor/log handle and offset order.
- Input arrays use the existing column-major flattening mapped to some. Every matrix
  output has N² None cells; each actual history/LDL diagonal has N None cells. Zero offsets
  are explicit in valid, rather than being silently assumed. All N, including zero, remain
  admitted. The proposal appropriately leaves capacity-initializer precomputed-policy
  classification to registry review.
- len=0 means no ROM, not missing declared matrix data: StoredEntries starts from
  inputState of the declared arrays. ROM values/tapes remain universally quantified and
  unused, and Empty provides no oracle escape. No counted ROM-loading claim is made.
- Posts assert actual output reads. Pivot logs contain absolute current-position indices,
  j≤p(j), and decode through the actual swap fold. PLU uses A.submatrix σ id and PLUQ
  independently uses A.submatrix σ τ, with current-to-original orientation. Fixed-scale
  PLU shares the row-log post but deliberately has no unweighted multiplier≤1 assertion.
- SPD uses strict IsCholesky; PSD uses lower triangularity, nonnegative diagonal and exact
  Gram identity directly, correctly including singular/zero matrices without weakening
  existing predicates. LDL reads the actual canonical pivot diagonal and asserts IsLDL.
- Source retention and complete original shape are explicit. Because these targets fix
  offsets to zero and every declared output extent is fully described, source/output
  reads plus unchanged shape determine the complete final declared-buffer contents. They
  are not arbitrary-offset or overlapping-external-buffer targets; the prose says so.
- Caller counts are respectively 3N², 3N²+N, 3N²+2N, 3N²+N, 2N², 2N², 2N²+N.
  The additional-word bounds agree with the proved Space formulas, including scaled
  scales and LDL's scoped upper factor plus residual. inputState counts every declared
  capacity at initial cur/peak; adding scratch is the right total RunsWithin budget.
  The sole Unit tag has no omitted off-tag case; ResourceTags also supplies the more
  general off-tag fact for future instantiations.
- treeCost uses the standard-charge static summary at the declared sizes, not observed
  counts. It is a conservative finite structural bound, not a closed polynomial flop
  count. Width zero/ROM zero introduce no native bit-memory, IEEE or optimized BLAS claim.
- All seven standard NonVacuous obligations are explicit and remain unproved. At every
  lower bound choose that order, zero offsets, and the identity matrix; its canonical
  pivots are unit and it is SPD/PSD/Hermitian. This supplies declared-input witnesses for
  every domain at arbitrarily large orders, rather than merely at N=0. Witnessing identity
  does not restrict the universally quantified input domains. The PSD target also admits
  singular zero input by its definition.

Remaining obligations are clearly stated: maintainer approval of exact statements, access
choice, initialization policy, charges and budgets; protected target registration and closure
hashes by the maintainer; one proof of each approved target; seven nonvacuity proofs; and
registered fixed-tree/access audits. The packet explicitly excludes rook/threshold, blocked,
pivoted-PSD, polynomial-count and rounded-native-budget targets. No completed registration or
cost publication should be claimed from this draft or the existing ordinary resource lemmas.
