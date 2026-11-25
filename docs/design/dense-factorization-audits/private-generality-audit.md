> Integration note: all seven findings below are corrected in the final source set. Shared
> pure results live in ForMathlib; the address, scalar positivity and suffix arguments reuse
> existing facts directly in the actual algorithm proofs. No exemptions were added.

# Private generality and placement audit

Read-only review of git-untracked new `NLAlib/**/*.lean` sources in the dense-factorization
worktree. The initial snapshot contained 130 new Lean files and 271 private declarations;
newly integrated pivoted-PSD private helpers were checked separately and all have actual
interpreter/store vocabulary. Tracked preexisting unrelated sources were excluded. No shared
source, cache, protected target or check changes were made by this audit.

The declaration inventory is `/tmp/nlalib-next-review/private-new-declarations.json`.
Private declarations were inspected because the normal public extraction omits them. General
scalar facts containing NLAlib predicates such as RelErr, AbsRelErr, IsRoundingProduct or
roundingFactor are legitimate NLAlib statements and were not falsely classified as P9.
Algorithm-specific matrix prefix definitions, store frames, actual-run lemmas and actual
builder AST equalities likewise remain in their topics.

## Seven true P9 declarations found

Locations refer to the audited source snapshot, before assigned corrective integrations.

| File | Private declaration | Recommendation / owner |
|---|---|---|
| Matrix/Factorizations/LUPivoting.lean:35 | lt_perm_apply_iff | Generic finite-permutation order fact; LU worker moves/generalizes to proper ForMathlib topic. |
| Matrix/Computation/RowSwap.lean:53 | address_eq_iff | Directly reuse existing Nat.add_mul_eq_add_mul_iff_of_lt and Fin.ext_iff at the two matrix-address goals; root owns. |
| Matrix/Perturbation/LURoundingPrefix.lean:150 | one_add_ne_zero | Directly derive positivity/nonzero using abs_lt and neg_lt_iff_pos_add'; root owns. |
| Matrix/Computation/PivotScan.lean:178 | scan_choice | Generic stable score scan; LU worker supplies one general ForMathlib score theorem shared with the scaled scan. |
| Matrix/Computation/ScaledPivot.lean:74 | scaled_comparison | Scalar ordered-field ratio comparison; LU worker replaces with standard positive-denominator division facts in actual branches. |
| Matrix/Computation/ScaledPivot.lean:88 | scaled_choice | Same generic stable score scan at ratio-valued scores; consumes shared theorem. |
| Matrix/Computation/RookPivot.lean:78 | suffix_le | Remove generic declaration; reuse Fin.range_natAdd_castLEEmb directly at both actual matrix bounds. Routines worker owns private corrective source. |

No further true private P9 theorem was found in the reviewed new sources. The already
identified scalar quotient/square-root and blocked Nat placement fixes are absent from this
snapshot after their corrections; they do not require new exemptions.

## Strict-checked direct reuse examples

`/tmp/nlalib-next-review/PrivateReuseExamples.lean` checks both replacements below with all
project options and warnings as errors, without generating shared artifacts:

```lean
simpa only [Fin.ext_iff] using
  (Nat.add_mul_eq_add_mul_iff_of_lt i.isLt i'.isLt :
    i.val + m * j.val = i'.val + m * j'.val ↔
      i.val = i'.val ∧ j.val = j'.val)
```

```lean
ne_of_gt (neg_lt_iff_pos_add'.mp (abs_lt.mp (hδ.trans_lt hu1)).1)
```

The primed addition-order lemma is required for the expression `1 + δ`.

## Rook corrective packet

Only staged source `NLAlib/Matrix/Computation/RookPivot.lean` changes in
`/tmp/nlalib-next-rook-placement`. It removes suffix_le and applies the existing range theorem
at the actual column/row magnitude bounds. The remaining private state_after_search signature
now takes an explicit htail : N-k≤N binder, avoiding hidden nonlocal proof terms in embedding
arguments; its caller supplies Nat.sub_le in its proof body. Public APIs and every runtime
definition are preserved. Final strict/source outcome is reported in the parent handoff.
