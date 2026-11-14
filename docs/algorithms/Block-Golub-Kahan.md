# Block Golub–Kahan bidiagonalization

Block Golub–Kahan bidiagonalization with full reorthogonalization computes factors U, S, V
of a low-rank approximation of a rectangular matrix A from a start block of b columns and q
block steps. NLAlib provides one fixed Ops program written over an abstract orthogonalization
operation, its exact stored-output certificate, a rounded run with orthogonality, residual
and forward bounds, a first orthogonalization scheme (column-wise CGS2 with threshold
deflation), and the transfer of Gaussian accuracy bounds to the stored output of the same
counted run. In exact arithmetic the stored product `U Sᴴ Vᴴ` is `rbki A Ω q`, randomized
block Krylov iteration.

## Pseudocode

The driver does no arithmetic of its own. `extend(Q, W)` extends the stored basis Q by the
block W and returns the new block and the coefficients; `A · X` and `Aᴴ · X` are applied
column by column.

```text
W = draw an n-by-b start block
V[block 0], G = extend(empty basis, W)
for j = 0, ..., q-1:
    W = A · V[block j]
    U[block j], R[block column j] = extend(U[blocks < j], W)
    W = Aᴴ · U[block j]
    V[block j+1], S[block column j] = extend(V[blocks <= j], W)
return U, V, G, R, S
```

Full reorthogonalization is the fact that every extension is against all stored columns of
its side. The [driver](../../NLAlib/Krylov/GolubKahan/Band/Alg.lean) is
`Krylov.GolubKahan.Band.solve`; `Krylov.GolubKahan.Band.program` fixes its four dimensions
`[m, n, b, q]` and five output buffers.

The first scheme for `extend` is
[column-wise two-pass classical Gram–Schmidt](../../NLAlib/Krylov/Orthogonalization/CGS2/Extend.lean)
with a deflation threshold `tau`, a rational literal of the implementation
(`CGS2.cgs2ExtendImpl tau`). The stored basis and the new columns already written form one
contiguous block.

```text
for c = 0, ..., b-1:
    nu = norm(W[:, c])
    C[k..k+b-1, c] = 0
    first pass:  coefficients of W[:, c] against the k + c stored columns -> C[0..k+c-1, c];
                 W[:, c] reduced in place
    second pass: coefficients against the same columns -> scratch; W[:, c] reduced in place
    C[0..k+c-1, c] += scratch
    beta = norm(W[:, c])
    if beta <= tau * nu:
        Qnew[:, c] = 0                 # deflated column, zero diagonal coefficient
    else:
        Qnew[:, c] = W[:, c] / beta
        C[k+c, c] = beta
```

At `tau = 0` the test is the exact zero guard. A dropped column stays a zero column of the
basis; the rank decision belongs to the scheme, not to the driver.

## Operation and representation choices

The driver uses three groups of operations.

| Operation | Declaration | Contracts |
|---|---|---|
| Extension of a stored basis by a block | `Ops.OrthOp.extend` in the [orthogonalization catalog](../../NLAlib/Ops/Catalog/Orth.lean) | exact `Ops.exactExtendRel`, rounded `Ops.extendRel` with parameters `(eta0, mu, eps)`, in the [contract file](../../NLAlib/Matrix/Factorizations/BasisExtensionContract.lean) |
| Products with A and with its adjoint | `Ops.OperatorPairOp.matvec`, `Ops.OperatorPairOp.rmatvec` in the [operator-pair catalog](../../NLAlib/Ops/Catalog/OperatorPair.lean) | exact `Ops.IsExactMatvecPair`, normwise rounded `Ops.IsMatvecPair` |
| Scalar draws from a tape stream | the existing sampling operation | the drawn words are the words of the tape |

The exact extension contract is the predicate `IsBasisExtension Q W Q' H R` of the
[pure theory](../../NLAlib/Matrix/Perturbation/BasisExtension.lean): `W = Q H + Q' R` with R
upper triangular, the new columns lie in the span of Q and W, a zero column of W gives a zero
column of Q', and orthonormality of the nonzero columns is preserved. It is a relation, not a
function: the scheme chooses which columns are zero, and the basis Q is arbitrary. The
rounded contract is `IsBasisExtensionErr eta0 mu eps Q W Q' H R`, conditional on a window on
the loss of orthogonality of Q. Orthogonality is measured by `gramDefect Q`, the Gram matrix
minus the indicator of the nonzero columns, so that deflated columns are allowed.

The matrix is reached only through the two products. The operator pair is the declared
oracle of the certificate: the contracts of `matvec` and `rmatvec` name the matrix of the
input, which is semantic data and occupies no supplied buffer, and their work and workspace
are parameters of the model. A concrete orthogonalization scheme is
an implementation of `extend` certified against one of the two contracts and substituted by
[linking](../../NLAlib/Krylov/GolubKahan/Band/Linked.lean).

Storage is column-major, one word per entry.

| Buffer | Length | Contents |
|---|---|---|
| U | `q*b*m` | left basis; `extend` writes a new block directly after the stored columns |
| V | `(q+1)*b*n` | right basis, written the same way |
| G | `b*b` | coefficients of the start block |
| R | `b*b*(q*(q+1)/2)` | left coefficients packed by block column; block column j is `(j*b + b)`-by-`b` at offset `b*b*(j*(j+1)/2)` |
| S | `b*b*(q*(q+3)/2)` | right coefficients packed by block column; block column j is `((j+1)*b + b)`-by-`b` at offset `b*b*(j*(j+3)/2)` |

The start block is the window of `n*b` words of the stream at the current tape position, read
column by column. The [assembly](../../NLAlib/Krylov/GolubKahan/Band/Run.lean) rebuilds the
global coefficient matrices from the packed block columns and identifies a stored run with
the pure relations `IsBlockGolubKahan`
([exact process](../../NLAlib/Krylov/Processes/BandGolubKahan.lean)) and `IsBlockGolubKahanErr`
([rounded process](../../NLAlib/Krylov/FinitePrecision/BandGolubKahanRun.lean)).

## Total output and resources

The [canonical problem](../../NLAlib/Krylov/GolubKahan/Band/Certification.lean) has sizes
`(m, n, b, q)`, all admitted, a real m-by-n matrix as its datum and five uninitialized output
blocks. `Krylov.GolubKahan.Band.Certification.algorithm` certifies the fixed program for
every interpretation whose two products are exact and whose extension meets the exact
contract, and for every tape. There is no rank, nonbreakdown or successful-run premise:
dependent start columns, rank-deficient A and breakdown inside the run are included.

The primitive part of the static budget is

```text
samples                 n*b
products with A         q*b
products with Aᴴ        q*b
basis extensions        2*q + 1      (one at [n, 0, b]; for each j < q one at [m, j*b, b]
                                      and one at [n, (j+1)*b, b])
```

The full budget also counts the structural instructions (index arithmetic, addressing,
allocation and control); it is the instruction manifest `staticCost` of the program, not a
closed form. The scratch is stated in closed form
(`Krylov.GolubKahan.Band.solvePeak`, proved by
`Krylov.GolubKahan.Band.stmtPeak_solve_le_solvePeak`):

```text
scratch  = (m + (n - m))*b + w + query reserve
resident = output lengths + scratch
```

with truncated subtraction, so the scratch block has `max(m, n)*b` words; it holds the drawn
block and then the products, and is released at the end. Here w is the largest declared
workspace among the primitive calls of the run (`Krylov.GolubKahan.Band.primitivePeak`): a
draw, a product at `[m, n]`, a product at `[n, m]` and the `2*q + 1` extensions at their
dimensions. No common bound on the primitive workspaces is assumed. The run consumes exactly
`n*b` words of the tape.

The operation model `Krylov.GolubKahan.Band.Certification.model work workspace` has these
properties, as reported by `scripts/OpsPrograms.lean`.

| Property | Value | Reason |
|---|---|---|
| confined | yes | every contract is in operand form: a call reads its operand blocks and the tape window and writes its output blocks only (`Certification.confined_model`) |
| uniform | no | the operator pair is a declared oracle: the contracts of the two products depend on the matrix of the input |
| charged | no | `work` is a parameter of the model and may be zero |
| budget | manifest | the full static count of the program; its primitive part is the closed count above (`Certification.original_staticBudget`) |
| scratch | closed | `solvePeak` plus the query reserve |

The five output blocks decode to an exact run for A from the drawn start block Ω. For such a
run the [factored identity](../../NLAlib/LowRank/BlockKrylov/Factored.lean) gives

```text
U Sᴴ Vᴴ = rbki A Ω q
```

with S assembled from the packed block columns. The nonzero columns of U and of V are
orthonormal, the first blocks of V span the block Krylov spaces of `Aᴴ A` and Ω, `A V = U R`
on the first q blocks of V, `Aᴴ U = V S`, and R and Sᴴ are banded with bandwidth b.

`Krylov.GolubKahan.Band.linked_certifies` certifies the driver linked with any scheme E that
is certified against the exact extension contract over a lower model; the only further
hypothesis is that the linked tree is well typed. In the counted-run form
(`Krylov.GolubKahan.Band.runs_linkedSolve`) each of the `2*q + 1` extension calls is replaced
by a supplied bound on the cost of E at its dimensions.

The exact CGS2 scheme meets the exact contract:
[`CGS2.cgs2Extend_exact_spec`](../../NLAlib/Krylov/Orthogonalization/CGS2/ExtendExact.lean)
proves it for `CGS2.cgs2ExtendImpl 0` under exact scalar arithmetic, exact level-one
operations and exact comparisons, for an arbitrary stored basis.

## The rounded run

Under the rounded contracts (products within normwise allowances, extension within
`(eta0, mu, eps)` at the admitted dimensions) the same program runs in total mode and its
stored blocks decode to a rounded run, the executed history
(`Krylov.GolubKahan.Band.Rounded.solve_spec`; after linking,
`Krylov.GolubKahan.Band.Rounded.runs_linkedSolve` with counts and scratch). No orthogonality,
rank or nonbreakdown hypothesis is made.

For a rounded run with product parameter `emv` (product errors at most `emv * ||A||2` times
the norm of the input column), `mu, eps, emv ≥ 0` and the window
`sqrt(3*(q+1)*b) * mu ≤ eta0`, the
[pure bounds](../../NLAlib/Krylov/FinitePrecision/BandGolubKahanRun.lean) are

```text
||gramDefect U||F ≤ sqrt(3*q*b) * mu
||gramDefect V||F ≤ sqrt(3*(q+1)*b) * mu
||A V[blocks < q] - U R||F ≤ (emv + eps*(1 + emv)) * sqrt(q*b*(1 + eta0)) * ||A||2
||Aᵀ U - V S||F           ≤ (emv + eps*(1 + emv)) * sqrt(q*b*(1 + eta0)) * ||A||2
||A - U Sᵀ Vᵀ|| ≤ ||(I - P_U) A||
                  + (sqrt(3*q*b)*mu + sqrt(1 + eta0)*(emv + eps*(1 + emv))*sqrt(q*b*(1 + eta0))) * ||A||2
```

The last line holds in the spectral and in the Frobenius norm, with `P_U` the orthogonal
projector onto the range of the computed U: the returned factors are as accurate as the
projection of A onto the computed left range, up to the loss of orthogonality and the second
residual. `Krylov.GolubKahan.Band.Rounded.storedBounds_of_storedOut` states the orthogonality
and forward bounds for the decoded output words.

For the CGS2 scheme with threshold `tau > 0`,
[`CGS2.cgs2Extend_spec`](../../NLAlib/Krylov/Orthogonalization/CGS2/ExtendRounded.lean) proves
the rounded contract under the standard model of rounded arithmetic, level-one error
contracts and exact comparisons. With c the budget of one classical pass against all stored
columns and E the relative accuracy of the computed norms and of the scaling, its parameters
are

```text
mu  = 4*c + 8*(eta0 + c)^2/tau + 5*E
eps = 3*c + 2*E + 2*tau
```

under `0 ≤ eta0 ≤ 1/100`, `c ≤ 1/100`, `4*u ≤ c` for the unit roundoff u, and
`0 ≤ E ≤ 1/100`. The [pure lemma](../../NLAlib/Matrix/Factorizations/CGS2/BasisExtensionErr.lean)
`isBasisExtensionErr_of_columns` derives these parameters, as `cgs2ExtendMu` and
`cgs2ExtendEps`, from per-column guarantees. The bound on a kept column is absolute, so the
rounded guarantees cover every returned column.

## Gaussian accuracy on the same run

The [sample constructor](../../NLAlib/LowRank/BlockKrylov/Samples.lean) builds the tape that
carries a given n-by-b matrix X and proves that the start block read by the program is X.
Unused positions and streams contain default words; no infinite iid law is asserted.

The [transfer theorems](../../NLAlib/LowRank/BlockKrylov/Probability.lean) apply to every
certified program for the canonical problem whose postcondition implies the exact-run
postcondition, hence to the abstract certificate and to a linked one.

- `BlockKrylov.storedOutput_eq_rbki`: the stored product of the run on the tape of X equals
  `rbki A X q` for every X, not only almost surely.
- `BlockKrylov.measureReal_not_accepts_le`: a failure bound for any predicate of
  `rbki A X q` is a failure bound for the complete counted run with that predicate of the
  stored product; no law of X and no successful run is assumed.
- `BlockKrylov.integral_comp_storedOutput`: expectations of any real function of the stored
  product equal those of `rbki A X q`, with no measurability or integrability premise.

So every statement about `rbki` transfers. Two corollaries are stated for a standard real
Gaussian X:

- the small-block gapped tail bound, for every block size `b ≥ 1` and depth `q ≥ t`, under a
  relative gap among the top t singular values
  (`BlockKrylov.measureReal_not_accepts_le_of_hasLaw_gaussianMatrix`, from the
  [small-block theory](../../NLAlib/LowRank/Gaussian/SmallBlock.lean));
- the large-block gapped bound in expectation, for `t + 2 ≤ b`
  (`BlockKrylov.integral_specNorm_sub_storedOutput_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  from the [block Krylov bounds](../../NLAlib/LowRank/Gaussian/BlockKrylov.lean)).

The other bounds for `rbki`, including the gapless forms of
[the gapless file](../../NLAlib/LowRank/Gaussian/BlockKrylovGapless.lean) and the remaining
small-block forms, transfer through the three general theorems but are not restated for the
stored output. These are exact-arithmetic accuracy statements: they use the exact
certificate.

## Scope

The following are not stated in the library, so nothing here should be read as claiming them.

- The concrete linked certificates: `linkedAlgorithm` instantiated at `CGS2.cgs2ExtendImpl`
  over an exact or a rounded BLAS model. The generic linking theorem and both certificates of
  the scheme exist; the instantiation, with its well-typedness side condition and its
  recomputed costs, is not written.
- A rounded canonical `Ops.Algorithm`. The rounded run is stated as total execution of the
  implementation and as a counted run of the linked program, not as a packaged certificate.
- An end-to-end rounded accuracy theorem. The forward bound compares the returned factors
  with the projection onto the computed left range; it does not bound the distance of that
  range from the exact block Krylov range, and the Gaussian bounds are not transferred to a
  rounded run.
- Complex scalars for the program. The pure exact relation and the exact extension contract
  are over real or complex scalars; the stored-run predicates, the certificate, the rounded
  relation and the CGS2 rounded analysis are over the reals.
