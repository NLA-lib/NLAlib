# Approved dense factorization cost targets

The maintainer approved these seven concrete targets and requested commit/push on 2026-11-25.
The statements preserve the reviewed declared-input model, input domains, output reads,
independent cubic counts and closed memory envelopes. Publication follows
[the program guide](../contributing/programs.md) and AGENTS.md rule 2.

The [review packet](dense-factorization-audits/target-proof-review/README.md) preserves the
approved Lean statements, checked proofs and prepublication audits. The published definitions,
proofs, registry hashes and final repository checks are linked in the
[delivery report](Matrix-DenseFactorizationDelivery.md).

The first structural-count draft was a true bound but did not meet H4, because it defined the
budget through the tree's own static cost. That version is superseded. The current statements
use explicit size-only polynomials; no tree or static analysis occurs in a declared budget,
memory bound or postcondition.

## Fixed programs and domains

Use the seven actual symbolic trees in `DenseFactorizationResources.lean`, bound before sizes,
matrices, tapes and declared inputs. Each is already compiled once with a kernel-checked `rfl`
instantiation equation for arbitrary handles and offsets. The following first batch fixes all
external offsets to zero by its size predicate; no tree is selected from matrix values.

| Approved target | Existing fixed tree | Extra sizes / buffers | Declared matrix domain | Postcondition |
|---|---|---|---|---|
| `StoredEntriesDenseLU` | `luResourceTree p` | 3 / 3 | All canonical elimination pivots nonzero | `A.IsLU L U` |
| `StoredEntriesDensePLU` | `pluResourceTree p` | 4 / 4 | Every real square matrix | `A.submatrix σ id` has factors `L,U` |
| `StoredEntriesDensePLUQ` | `pluqResourceTree p` | 5 / 5 | Every real square matrix | `A.submatrix σ τ` has factors `L,U` |
| `StoredEntriesDenseScaledPLU` | `scaledPluResourceTree p` | 4 / 4 | Every real square matrix | Row-permuted exact LU with original row scales |
| `StoredEntriesDenseCholesky` | `choleskyResourceTree p` | 2 / 2 | Positive definite | `A.IsCholesky L` |
| `StoredEntriesDenseSemidefiniteCholesky` | `semidefiniteCholeskyResourceTree p` | 2 / 2 | Positive semidefinite | Lower triangular `L`, nonnegative diagonal, `A = L*Lᴴ` |
| `StoredEntriesDenseLDL` | `ldlResourceTree p` | 3 / 3 | Hermitian, nonzero canonical scalar pivots | `A.IsLDL L d` |

The tree with `r+1` index variables is a `Prog P ι r b`; variable zero is the order N and
remaining variables are offsets. Require `valid N n := ∀ j, n j = 0`, including N=0.
Instantiate `P := Unit`, `ι := Empty`, `p := ()`, and real words. Thus each approved target
is a closed proposition, rather than a family choosing a tag or an oracle from data.
Choose `X N n` to contain the real input matrix
and exactly the domain proof listed above, with no supplied factors or execution witness.
Domain predicates must reference the input alone. For example the LU predicate is
`∀ k : Fin N, gaussState A k k k ≠ 0`, not successful execution of the builder.

All matrices enter through declared buffers, not hidden read-only data: set `len N n := 0`.
Buffer zero is the fully initialized column-major input `(flatten A).map some`
under the existing packed indexing. Each output matrix buffer is `N*N` uninitialized words;
each permutation log or LDL diagonal buffer is N uninitialized words. Include the input and
all output buffer sizes in the memory budget. No entry is computed from a factorization in
`inputs`. Matrix data are not precomputed from sizes; output-capacity arrays are determined by sizes.
The initializers are explicit in the target statements. The actual registry checker classifies
all seven as non-precomputed: matrix words come from declared data and output arrays contain
only uninitialized capacity. Tapes and the unused read-only `vals` remain
universally quantified. This is a declared-input stored-entries result; it must not be advertised
as a counted ROM-loading algorithm. A separate `read`-based ROM wrapper would need its own tree,
load costs, and review. In particular, a successful-run implication for arbitrary ROM contents
cannot establish success of SPD Cholesky on indefinite inputs.

For each row, the approved full statement is

```text
StoredEntries p FIXED_TREE valid X inputs (fun _ _ => 0) cost mem post
```

where the identifiers above have the explicitly specified definitions. The postcondition must
assert the actual output buffer reads, the displayed factorization, the exact decoded log
interpretation where present, source retention, and unchanged buffer extents. The PSD row deliberately uses the three
nonnegative-diagonal properties directly: the existing `IsCholesky` predicate requires a
strictly positive diagonal and cannot describe singular PSD factors. It must not take
successful execution as a hypothesis. Singular PLU/PLUQ/scaled cases and N=0 are included.
For nonvacuity, choose all offsets zero and the identity input at every order N.
Identity is SPD, PSD and Hermitian with unit canonical pivots, so it supplies the declared
input witness for every row at arbitrarily large orders. The PSD row additionally includes
the zero matrix as a singular example; it is not limited to positive definite inputs.
The checked candidate proofs establish the standard model nonvacuity obligation explicitly.

The existing execution theorems supply success; the existing `bounds_*` lemmas supply resources.
Each approved target should have one proof theorem with exactly the target constant as type.

## Concrete resource budgets

For each of the 23 operation kinds possible with one Unit tag and no oracle/kernel names,
set the count allowance to `1024*(N+1)^3`. `ClosedCountBudget.lean.txt` explicitly lists those
kinds and defines their finitely supported count vector. The target count is exactly that
independent vector, a function of N alone. It does not unfold to a program or `StaticCost`.

The seven concrete comparison proofs establish that each actual tree's static count is below
this declared vector. Together with the numerical execution theorem, this bounds the actual
successful run. Comparisons, copies, literals, divisions and index conversions are included.
The cubic constants are conservative uniform allowances, not sharp classical flop counts.

Let `c` denote the actual static summary only within these comparison proofs, for the
standard charge, width zero and sizes `[N,0,...,0]`.

Set `mem N n q := if q = p then callerCells N + scratchCells N else 0` with:

| Routine | Caller cells | Additional live words upper bound |
|---|---|---|
| LU | `3*N*N` | `N*N + 2*N + 3` |
| PLU | `3*N*N + N` | `N*N + 2*N + 7` |
| PLUQ | `3*N*N + 2*N` | `N*N + 2*N + 7` |
| Fixed-scale PLU | `3*N*N + N` | `N*N + 3*N + 7` |
| SPD Cholesky | `2*N*N` | `N*N + 2*N + 3` |
| PSD Cholesky | `2*N*N` | `N*N + 2*N + 4` |
| LDL | `2*N*N + N` | `2*N*N + 2*N + 3` |

The tag-p scratch bounds are proved in `DenseFactorizationSpace.lean`.
`DenseFactorizationResourceTags.lean` additionally proves `c.cells q = 0` for `q ≠ p`
for all seven actual trees, supplying the off-tag part of these approved budgets. These are conservative peaks
in the interpreter's memory model, excluding allocator overhead and memory hidden in scalar
operations. The access model uses width zero; it makes no native RAM or IEEE bit-memory claim.
An explicit finite-width bit budget should be a separate reviewed statement under a semantics
that justifies the arithmetic, rather than silently assigning IEEE widths to exact real words.

## Review and follow-up

The approval covers the declared-input access choice, each domain and postcondition, standard
charges, and conservative budgets specified above. The publication registers the fixed trees,
closure hashes and nonvacuity witnesses and reruns the full repository checks.

This batch does not cover the additional rook/threshold drivers, blocked algorithms,
pivoted PSD Cholesky, sharp operation-specific constants, or rounded native-backend budgets.
Those require their own concrete tree/domain/budget proposals.
