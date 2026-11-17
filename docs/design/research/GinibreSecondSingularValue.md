# An elementary fourth-power tail for the second-smallest singular value

This records the mathematical derivation for the acceptable weaker gap route in
`Spec-RandomMatrix-GinibreGapKappaV.md`. The implementation is in
`RandomMatrix/Gaussian/Complex/LeastSingularValue.lean`. The actual final constants
and the area-based conditioning argument are described in
[the design](../RandomMatrix-GinibreShattering.md). Section 4 records the constants used in the implementation.

## The estimate

Let `G` have independent standard complex Gaussian entries, with
`E |G_ij|² = 1`. For every deterministic complex `n × n` matrix `M`, `n ≥ 2`,
and `x ≥ 0`, the following elementary estimate suffices:

\[
\Pr[\sigma_{n-1}(M+G)\le x]\le (n-1)^3x^4.
\]

Singular values in this note are indexed from one, in decreasing order.
With the spec's normalized perturbation, it becomes

\[
\Pr[\sigma_{n-1}(M+\gamma G_n)\le x]
\le n^2(n-1)^3(x/\gamma)^4
\le n^5(x/\gamma)^4.
\]

The exponent four exceeds the exponent two lost to a planar net. Neither
Szarek's exact singular-value law nor Śniady's coupling is needed for this
weaker bound.

## 1. Rank-two projected small ball

For any deterministic orthogonal projector `P` of complex rank at least two,
choose orthonormal `u,v` in its range. If `g` is standard complex Gaussian and
`a` is deterministic, then

\[
\|P(g+a)\|\le s
\quad\Longrightarrow\quad
|u^*(g+a)|\le s,\quad |v^*(g+a)|\le s.
\]

The two Gaussian coordinates `u*g` and `v*g` are independent standard complex
Gaussians by unitary invariance. Each translated disk has mass at most `s²`.
Consequently

\[
\Pr[\|P(g+a)\|\le s]\le s^4.
\]

This deliberately uses a product of two disks rather than the exact
four-dimensional ball volume. It fits the existing `HasOrthonormalCols`
invariance theorem and the newly proved shifted scalar small ball directly.

## 2. A rectangular least-singular-value bound

Let `Y` be an `n × (n-1)` shifted standard complex Gaussian matrix. If its
smallest singular value is at most `x`, take a unit vector `w` with
`||Yw|| ≤ x`. Some coordinate `j` has `|w_j| ≥ 1/√(n-1)`. Divide by `w_j`.
The distance of column `j` to the span of the other `n-2` columns is at most
`√(n-1) x`.

For each fixed `j`, condition on those other columns. Their span has complex
codimension at least two, regardless of any rank deficiency. The orthogonal
projection of column `j` onto its complement is a shifted projected standard
complex Gaussian, independent of the conditioned columns. Step 1 bounds this
probability by `(√(n-1) x)^4`. Union over the `n-1` choices of `j`:

\[
\Pr[\sigma_{n-1}(Y)\le x]\le (n-1)^3x^4.
\]

There is no need to choose a measurable maximizing coordinate or a measurable
basis of the random complement. Use a union of column-distance events, condition
on a fixed column index, and prove the rank-two bound for each fixed projector,
as the existing least-singular-value proof does in rank one.

## 3. Remove one fixed column

Fix one column index of `X = M+G`, and let `Y` be the matrix obtained by deleting
it. On the two-dimensional right singular subspace of `X` for its two smallest
singular values, `||Xw|| ≤ σ_(n-1)(X) ||w||`. The coordinate functional at the
deleted index has a nontrivial kernel on that subspace. A unit vector in the
kernel is supported on the retained columns. Therefore

\[
\sigma_{n-1}(Y)\le \sigma_{n-1}(X).
\]

Apply Step 2. This also follows from singular-value interlacing for a column
deletion. The deletion index is fixed in advance; there is no extra union over
the removed column.

## 4. Consequence for an acceptable gap bound

The conditioning proof now supplies, for the normalized perturbation,

\[
\mathbb P[\text{no diagonalizer with condition at most }1/t]
\le 128e n^3t^2(m+\log(1/t))^2,
\qquad m=\|M\|/\gamma\ge2,\quad 0<t\le1.
\]

Its deterministic local area bound loses a factor four relative to the exact
area formula; the final constant absorbs this. The argument compares the bad
diagonalizer event to a measurable area-liminf event, so it does not select
random eigenvectors measurably.

Put `τ = r/γ ∈ (0,1]`, `L = log(1/τ)`, `K = m+L`, and choose

\[
q=\sqrt{\sqrt\tau},\qquad B=q^{-1},\qquad
s=2\sqrt2+\sqrt{2L}/\sqrt n,\qquad R=\|M\|+\gamma s.
\]

The norm failure probability is at most `τ²`. The cutoff radius satisfies
`R ≤ 3γK`. Since `τ ≤ q ≤ 1`, the conditioning bound with parameter `q`
is at most `128e n³√τ K²`.

The implemented square-grid corollary supplies an `r/2`-net with cardinality
at most `36(R/r)²`. If two eigenvalues have distance at most `r`, some net disk
of radius `2r` contains both. On the event of a diagonalizer with condition
at most `B`, the deterministic two-eigenvalue singular-value estimate gives
`σ_(n-1)(y-X) ≤ 2rB`. The fourth-power tail and a union bound give

\[
36(R/r)^2 n^5(2rB/\gamma)^4
=576 n^5(R/\gamma)^2\tau
\le5184 n^5 K^2\tau.
\]

The three failure probabilities sum to at most

\[
128e n^3\sqrt\tau K^2+\tau^2+5184 n^5\tau K^2
\le10000e n^5\sqrt\tau K^2.
\]

Thus the delivered acceptable gap constants are
`(C,a,b,c) = (10000e,5,1/2,2)`. The delivered conditioning constants are
`(128e,3,2,2)`. Both existential statements have the exact events and
normalization in the spec. The empty and singleton gap events are handled
separately. All boundary events use closed small-ball estimates.

## Implementation

The rank-two projected small ball, rectangular column-distance argument,
fixed-column deletion and normalized fourth-power tail are in
`RandomMatrix/Gaussian/Complex/LeastSingularValue.lean`. Column-deletion
interlacing reuses `singularValues_submatrix_le`.
`Matrix/Perturbation/EigenvalueClustering.lean` contains the deterministic
cluster estimate and its net consequence; the finite disk net is a corollary
of `Matrix/QRIteration/SquareGrid.lean`.
`RandomMatrix/Gaussian/Complex/Shattering.lean` combines them with the
conditioning argument and proves both exact existential statements.

Primary sources for the deterministic/net argument:
[BGKS, arXiv:1912.08805](https://arxiv.org/abs/1912.08805), Lemma 3.5 and §3.1;
for R4–R6:
[BKMS, arXiv:1906.11819](https://arxiv.org/abs/1906.11819), §3.
Steps 1–3 here are a separate elementary derivation, not attributed to those papers.
