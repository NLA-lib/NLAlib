# Design note: Matrix stage M3a, majorization and trace inequalities

Status: written 2026-10-14 by the orchestrator while M3 and M4 were being proved; to be
implemented after M4 without a maintainer approval stop, by the standing instruction in
`docs/port/status.md`. Choices a maintainer would have been asked about are in §7. The skeleton
(six files) elaborates against the pinned Mathlib and the M1 to M3 files.

## 0. Scope

Majorization of real vectors and its classical characterisations; Ky Fan's maximum principles
for eigenvalue and singular value partial sums; Schur's theorem on the diagonal; the trace
inequalities of von Neumann type; Hoffman–Wielandt for Hermitian matrices and Mirsky's inequality
in the Frobenius norm; Lidskii's inequalities for eigenvalues and singular values; Horn's
product inequality.

This stage was split out of M3 (see `Matrix-Spectral.md` §0). It is what M3b needs to define
unitarily invariant norms and prove Fan dominance. The rest of the brief's M7 (Schur–Horn and its
converse, determinant inequalities, Hadamard products, block inequalities, Kantorovich) stays in
M7.

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| sum of the `k` largest entries | `sumLargest x k`, for `x : ι → ℝ` unsorted | `sumLargest_fin_eq_sum_range` for sorted sequences |
| majorization | `Majorized x y`, `WeaklyMajorized x y`, for `x y : ι → ℝ` on one finite index type | `majorized_iff_exists_doublyStochastic` to Mathlib's `doublyStochastic` |
| singular value partial sums | `kyFanNorm k A`, the Ky Fan `k`-norm | `kyFanNorm_eq_sum_range` (`rfl`) |
| eigenvalue partial sums | `∑ i ∈ Finset.range k, eigenvalue A i`; no definition | — |
| majorization between spectra | the family of partial-sum inequalities, stated directly | `weaklyMajorized_fin_iff_sum_range_le` |

Mathlib has `doublyStochastic` and Birkhoff's theorem and no majorization.

## 2. Interfaces

**One definition of majorization, on unsorted vectors.** `Majorized` and `WeaklyMajorized` are
defined for `x y : ι → ℝ` through `sumLargest`, which is a supremum over index sets: no sorting
equivalence appears in any statement. Lidskii's theorem (eigenvalue differences, not sorted) and
Schur's theorem (the diagonal, not sorted) need the unsorted notion.

**Spectra are compared by partial sums.** `eigenvalue A` and `singularValues A` are already
sorted and ℕ-indexed, so a majorization between spectra is stated as the inequalities
`∑ i ∈ Finset.range k, … ≤ ∑ i ∈ Finset.range k, …`, which is what a consumer rewrites with. The
predicate form is given as well where the literature states one (`majorized_eigenvalue_add`,
`majorized_eigenvalue_add_sub`), with the sorted sequences restricted to `Fin (card n)`. There is
no second majorization predicate on sequences.

**Schur's theorem compares two vectors on the index type `n`**, the diagonal and the eigenvalues
in some enumeration. It is stated for any unitary diagonalisation `A * U = U * diagonal d`, so no
chosen eigenbasis appears; the forms with Mathlib's `hA.eigenvalues` and with partial sums of
`eigenvalue` are corollaries.

**The Ky Fan norm is defined here**, in `KyFan.lean`, because its triangle inequality is Ky Fan's
maximum principle and Lidskii's inequality for singular values is stated with it. M3b adds the
rest of its API. Eigenvalue partial sums stay unnamed.

**Sets of indices, not ranges, in Lipschitz-type sums.** Hoffman–Wielandt and Mirsky are stated
over an arbitrary `S : Finset ℕ` (every term is nonnegative and vanishes beyond the dimensions),
so a consumer never has to match a particular `Finset.range`.

## 3. Statement shapes

```lean
noncomputable def sumLargest (x : ι → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.powersetCard (min k (Fintype.card ι))).sup' _ fun s => ∑ i ∈ s, x i
def WeaklyMajorized (x y : ι → ℝ) : Prop := ∀ k, sumLargest x k ≤ sumLargest y k
structure Majorized (x y : ι → ℝ) : Prop where
  weaklyMajorized : WeaklyMajorized x y
  sum_eq : ∑ i, x i = ∑ i, y i

theorem sumLargest_fin_eq_sum_range {f : ℕ → ℝ} {N : ℕ} (hf : AntitoneOn f (Set.Iio N)) (k : ℕ) :
    sumLargest (fun i : Fin N => f i) k = ∑ i ∈ Finset.range (min k N), f i
theorem weaklyMajorized_fin_of_forall_sum_le {N : ℕ} {x : Fin N → ℝ} {f : ℕ → ℝ}
    (hf : AntitoneOn f (Set.Iio N))
    (h : ∀ S : Finset (Fin N), ∑ i ∈ S, x i ≤ ∑ i ∈ Finset.range S.card, f i) :
    WeaklyMajorized x (fun i : Fin N => f i)
theorem majorized_iff_exists_doublyStochastic {x y : ι → ℝ} :
    Majorized x y ↔ ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x
theorem Majorized.le_of_convexOn_of_comp_perm {x y : ι → ℝ} (h : Majorized x y)
    {Φ : (ι → ℝ) → ℝ} (hΦ : ConvexOn ℝ Set.univ Φ)
    (hperm : ∀ (z : ι → ℝ) (σ : Equiv.Perm ι), Φ (z ∘ σ) = Φ z) : Φ x ≤ Φ y
theorem WeaklyMajorized.le_of_convexOn_of_monotone_of_comp_perm {x y : ι → ℝ}
    (h : WeaklyMajorized x y) {Φ : (ι → ℝ) → ℝ} (hΦ : ConvexOn ℝ Set.univ Φ) (hmono : Monotone Φ)
    (hperm : ∀ (z : ι → ℝ) (σ : Equiv.Perm ι), Φ (z ∘ σ) = Φ z) : Φ x ≤ Φ y
theorem WeaklyMajorized.exists_le_majorized {x y : ι → ℝ} (h : WeaklyMajorized x y) :
    ∃ z : ι → ℝ, x ≤ z ∧ Majorized z y

theorem Matrix.IsHermitian.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜} (hQ : HasOrthonormalCols Q) :
    RCLike.re (Qᴴ * A * Q).trace ≤ ∑ i ∈ Finset.range (Fintype.card p), eigenvalue A i
theorem Matrix.IsHermitian.sum_Ico_eigenvalue_le_re_trace_conjTranspose_mul_mul [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜} (hQ : HasOrthonormalCols Q)
    {d : ℕ} (hd : Fintype.card p + d = Fintype.card n) :
    ∑ i ∈ Finset.Ico d (Fintype.card n), eigenvalue A i ≤ RCLike.re (Qᴴ * A * Q).trace
theorem sum_range_eigenvalue_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : ℕ) :
    ∑ i ∈ Finset.range k, eigenvalue (A + B) i ≤
      ∑ i ∈ Finset.range k, eigenvalue A i + ∑ i ∈ Finset.range k, eigenvalue B i

noncomputable def kyFanNorm (k : ℕ) (A : Matrix m n 𝕜) : ℝ :=
  ∑ i ∈ Finset.range k, singularValues A i
theorem norm_trace_conjTranspose_mul_mul_le_kyFanNorm [DecidableEq p] (A : Matrix m n 𝕜)
    {U : Matrix m p 𝕜} {V : Matrix n p 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) : ‖(Uᴴ * A * V).trace‖ ≤ kyFanNorm (Fintype.card p) A
theorem kyFanNorm_add_le (k : ℕ) (A B : Matrix m n 𝕜) :
    kyFanNorm k (A + B) ≤ kyFanNorm k A + kyFanNorm k B

theorem majorized_re_diag_of_mul_eq_mul_diagonal [DecidableEq n] {A U : Matrix n n 𝕜}
    {d : n → ℝ} (hU : HasOrthonormalCols U)
    (h : A * U = U * Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) :
    Majorized (fun i => RCLike.re (A i i)) d

theorem norm_trace_conjTranspose_mul_le_sum_singularValues_mul (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i * singularValues B i
theorem sum_sq_eigenvalue_sub_le_frobNorm_sub_sq {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (S : Finset ℕ) :
    ∑ i ∈ S, (eigenvalue A i - eigenvalue B i) ^ 2 ≤ frobNorm (A - B) ^ 2
theorem sum_sq_singularValues_sub_le_frobNorm_sub_sq (A B : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, (singularValues A i - singularValues B i) ^ 2 ≤ frobNorm (A - B) ^ 2

theorem sum_eigenvalue_add_sub_le_sum_range {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {J : Finset ℕ} (hJ : ∀ j ∈ J, j < Fintype.card n) :
    ∑ j ∈ J, (eigenvalue (A + B) j - eigenvalue A j) ≤ ∑ i ∈ Finset.range J.card, eigenvalue B i
theorem sum_abs_singularValues_add_sub_le_kyFanNorm (A E : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, |singularValues (A + E) i - singularValues A i| ≤ kyFanNorm S.card E
theorem weaklyMajorized_abs_singularValues_add_sub (A E : Matrix m n 𝕜) (N : ℕ) :
    WeaklyMajorized (fun i : Fin N => |singularValues (A + E) i - singularValues A i|)
      (fun i : Fin N => singularValues E i)

theorem prod_range_singularValues_mul_le (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) (k : ℕ) :
    ∏ i ∈ Finset.range k, singularValues (A * B) i ≤
      ∏ i ∈ Finset.range k, singularValues A i * singularValues B i
theorem sum_range_rpow_le_of_forall_prod_range_le {x y : ℕ → ℝ} {N : ℕ} (hx0 : ∀ i, 0 ≤ x i)
    (hy0 : ∀ i, 0 ≤ y i) (hx : Antitone x) (hy : Antitone y)
    (h : ∀ k ≤ N, ∏ i ∈ Finset.range k, x i ≤ ∏ i ∈ Finset.range k, y i) {r : ℝ} (hr : 0 < r) :
    ∑ i ∈ Finset.range N, x i ^ r ≤ ∑ i ∈ Finset.range N, y i ^ r
```

Everything spectral is over `𝕜`; the prototype proved this whole chain over `ℝ` only.

## 4. Consumers

| Item | Consumed by |
|---|---|
| `Majorized`, the convex-function characterisations | M3b (symmetric gauges are Schur-convex; Fan dominance); M7 Schur–Horn |
| Ky Fan principles, partial-sum subadditivity | M3b (Ky Fan norms are norms); trace estimation and low-rank optimality in the layers above |
| Schur's theorem | M7 Schur–Horn, Hadamard's inequality; diagonal estimators |
| von Neumann's trace inequality | M3b duality of Schatten norms; Procrustes (M9); low-rank approximation with a rank constraint |
| Hoffman–Wielandt, Mirsky | M6; matching of eigenvalues in perturbation bounds; M3b Mirsky for every invariant norm |
| Lidskii, singular value form | M3b Mirsky's theorem in any unitarily invariant norm; M6 |
| Horn's product inequality | M3b Hölder for Schatten norms |

## 5. Files

Under `NLAlib/Matrix/Majorization/`:

1. `Basic.lean`: `sumLargest`, `WeaklyMajorized`, `Majorized`, order properties, permutations,
   the sorted-sequence bridges.
2. `DoublyStochastic.lean` (imports 1, Mathlib `Birkhoff`): Hardy–Littlewood–Pólya, Rado,
   Karamata, Tomić–Weyl, the hinge characterisation, the weighted-sum lemmas.
3. `KyFan.lean` (imports 1, M3): the maximum principles and partial-sum subadditivity.
4. `Schur.lean` (imports 2, 3): orthostochastic matrices, Schur's theorem.
5. `TraceInequalities.lean` (imports 4): the Hermitian trace inequalities, von Neumann,
   Hoffman–Wielandt, Mirsky.
6. `Lidskii.lean` (imports 3, M3 `SingularValueInequalities` and `Dilation`; amended
   2026-10-14: it does not need the trace inequalities): Lidskii for eigenvalues and singular
   values.
7. `Horn.lean` (imports 2, M3 `SingularValueInequalities`): Horn's product inequality, Weyl's
   log-majorization lemma, power sums of the singular values of a product.

Independent for proving: 2 and 3 after 1; 7 after 2.

## 6. Material

Read: prototype `Matrix/Inequalities/{Majorization*, KyFan*, Lidskii, VonNeumann, Schur,
SingularValueMajorization, TraceTail, Wielandt}`, `Matrix/Perturbation/{EigenvalueTrace,
HoffmanWielandtNormal}`, `Matrix/Spectral/ProductSingularValues`.

Reused: the majorization theory (already on arbitrary finite index types), the Ky Fan principles,
the trace inequality chain, Lidskii.

Not reproduced: `sortingEquiv` and `sortedVector` in statements; `eigenvaluePrefix`;
`diagonalSequence`; `spectralTraceTail` (it is `∑ i ∈ Finset.Ico r (card n), eigenvalue A i`);
`*_reindex` lemmas; the `Fin`-specialised statements. Hoffman–Wielandt for normal matrices
(`HoffmanWielandtNormal`, over `ℂ`, with characteristic polynomial factorisations) is deferred to
M10 with normal matrices; `Wielandt.lean` (a Kantorovich-type bound) to M7.

## 7. Decisions taken without approval

1. **Majorization is defined once, on unsorted vectors over one finite index type**, through a
   choice-free `sumLargest`. Spectra are compared by partial sums.
2. **`kyFanNorm k A` is defined in this stage; eigenvalue partial sums have no name.**
3. **Schur's theorem is stated for any unitary diagonalisation**, with the `hA.eigenvalues` and
   partial-sum forms as corollaries.
4. **Everything spectral is restated over `𝕜`.** The prototype's proofs are real; the complex
   case of von Neumann's inequality is the main new proof obligation of the stage and the most
   likely scaffold candidate.
5. **Hoffman–Wielandt for normal matrices moves to M10.**

## 8. Review (Fable, 2026-10-14) and what changed

The review confirmed the interface (one unsorted definition on a finite index type; no predicate
on sequences `ℕ → ℝ`) and the stage boundary. Folded in:

1. Added the non-separable Schur-convexity lemmas `Majorized.le_of_convexOn_of_comp_perm` and
   `WeaklyMajorized.le_of_convexOn_of_monotone_of_comp_perm`; Fan dominance in M3b consumes them.
   `WeaklyMajorized.exists_le_majorized` was already present, without sign hypotheses.
2. Added `weaklyMajorized_fin_of_forall_sum_le` (unsorted left side against a sorted sequence),
   the bridge Lidskii's singular value inequality needs, and its instance
   `weaklyMajorized_abs_singularValues_add_sub`.
3. Schur's theorem restated for an arbitrary unitary diagonalisation (decision 3 revised).
4. Hoffman–Wielandt and Mirsky over an arbitrary `Finset ℕ`.
5. von Neumann's inequality stated for the modulus of the trace, the `frobInner` form a corollary;
   the lower Hermitian trace inequality added.
6. Ky Fan's principle for singular values stated for the modulus; the minimum principle in tail
   form over `Finset.Ico d (card n)`; attainment kept.
7. `kyFanNorm` defined here (decision 2 revised), with positivity.
8. Weyl's log-majorization lemma and the power sums for products added, in a new `Horn.lean`.
9. `hk` dropped from `sum_range_eigenvalue_add_le`; `sumLargest` defined with `Finset.sup'`
   instead of `sSup`, with `sumLargest_le` added to the API.
10. Vocabulary rows proposed for CONTRIBUTING §5.3 (added with this note).

## 9. Stage report (2026-10-14)

**Outcome.** Seven files under `Matrix/Majorization/` (1993 lines) and
`ForMathlib/Algebra/BigOperators/AbelSummation.lean`, all proved; nothing in `NLAlibScaffold`.
With M1 to M4 and `Norms/SymmetricGauge.lean` the build has no warnings, the axiom audit covers
1232 declarations with no violation, the environment linters pass on 981 declarations, and
references check clean. Proofs by Opus agents, four to nine minutes per file; one follow-up pass.

**What changed from the design.** No statement was found false.

- The whole trace-inequality chain is new over `𝕜`: Abel summation against Ky Fan's principles
  applied to the leading `k` columns of a diagonalising frame. Decision 4 expected the complex von
  Neumann inequality to be the scaffold candidate; it was proved.
- Ky Fan's principle for singular values is proved through the Hermitian dilation, not through
  von Neumann's inequality, so `KyFan.lean` does not depend on the trace inequalities.
- The converse of Hardy–Littlewood–Pólya is proved by separation (Hahn–Banach against the hull of
  the permutations) after Abel summation, not by T-transforms.
- Lidskii's inequality for eigenvalues has a new algebraic proof (positive part of
  `B - λ_{|J|-1}(B) • 1`, Loewner monotonicity, trace); the prototype's proof by eigenvalue
  derivatives along a pencil is not reproduced. `Lidskii.lean` imports `KyFan.lean` only.
- Horn's product inequality goes through Gram determinants with a thin SVD of `B X`; the public
  identity `det_conjTranspose_mul_self_eq_prod_sq_singularValues` came out of it.
- `sumLargest` kept its `Finset.sup'` body; the sorted-sequence case rests on the general
  exchange lemma `sumLargest_eq_sum_of_forall_le`.
- Added at the follow-up pass: `WeaklyMajorized.comp_equiv_left/right`,
  `WeaklyMajorized.exists_perm_sum_mul_le`, `weaklyMajorized_iff_forall_sum_monotone_convex_le`,
  `kyFanNorm_min_card`, `sum_range_min_card_eigenvalue`, the real-part form of the singular value
  principle, `conjTranspose_submatrix_mul_mul_submatrix` (in `Basic/Selection.lean`),
  `eigenvalue_dilation_of_add_add_one_eq` (the negative half of the dilation's spectrum),
  `exists_submodule_singularValues_mul_norm_le` (M3's open item), and the Abel summation
  inequalities `Finset.sum_range_mul_le_sum_range_mul_of_antitoneOn_of_nonneg` and
  `…_of_sum_eq`.

**Mathlib overlap.** Mathlib has `doublyStochastic` and Birkhoff's theorem, used directly, and no
majorization; it has summation by parts as an identity and not the Abel inequality.

**Not ported, by decision.** Sorting equivalences and sorted vectors; `eigenvaluePrefix`;
`diagonalSequence`; `Fin` transports. Deferred with ledger entries: Schur–Horn and its converse,
trace-tail bounds, Wielandt's inequality (M7); Hoffman–Wielandt for normal matrices (M10).

**For the next stages.**

- M3b consumes `Majorized.le_of_convexOn_of_comp_perm`, `WeaklyMajorized.exists_le_majorized`,
  `weaklyMajorized_fin_of_forall_sum_le` and Lidskii's singular value inequality in its Ky Fan
  form; nothing else of the majorization theory is needed to build unitarily invariant norms.
- M6 gets Hoffman–Wielandt and Mirsky over arbitrary index sets.
