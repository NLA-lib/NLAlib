# Design note: Matrix stage M8, matrix functions

Status: written 2026-10-14 by the orchestrator while M6 was being proved, reviewed by a Fable
agent the same day (§8); to be implemented
without a maintainer approval stop, by the standing instruction in `docs/port/status.md`. Choices
a maintainer would have been asked about are in §7. The skeleton (twelve files and one
`ForMathlib` file) elaborates against the pinned Mathlib and the earlier stages.

## 0. Scope

Functions of a Hermitian matrix through Mathlib's continuous functional calculus; polynomials in a
matrix; the exponential and the logarithm; trace functions (monotonicity, convexity, Klein);
operator monotone and operator convex functions (Löwner–Heinz, operator Jensen); the
Golden–Thompson inequality; the matrix relative entropy and Lieb's concavity theorem; traces of
powers; the logarithm of the determinant and the trace of the inverse; the matrix absolute value;
derivatives of the determinant, the inverse and trace powers along a curve.

Owed to this stage by earlier ones, and paid here: the nuclear norm as the trace of the absolute
value (M3b); `log det (1 + A) ≤ tr A` and concavity of `log det` (M7); monotonicity of the square
root and the description of `B ≤ A` by `A^{-1/2} B A^{-1/2} ≤ 1` (M7); singular values of
`(A Aᴴ)^q A` (M3).

Not here: the polar decomposition (M9, with the factorizations); functions of non-normal matrices
(Jordan form, Cauchy integrals; nothing downstream asks for them); the matrix sign function and
matrix means; expectations of matrix functions and the matrix cumulant generating function (the
matrix concentration layer, outside `Matrix/`).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| `f(A)` for Hermitian `A` | Mathlib's `cfc f A`, `f : ℝ → ℝ` | `Matrix.IsHermitian.cfc_eq` |
| matrix exponential | Mathlib's `NormedSpace.exp A` | `Matrix.IsHermitian.exp_eq_cfc` (new) |
| matrix logarithm | `cfc Real.log A` | — (`CFC.log` needs a global `NormedRing` on matrices) |
| matrix square root | Mathlib's `CFC.sqrt A` (as in M7) | `CFC.sqrt_eq_real_sqrt` |
| matrix power, real exponent | Mathlib's `A ^ r` (`CFC.rpow`), for positive semidefinite `A` | `CFC.rpow_eq_cfc_real` |
| absolute value of `A : Matrix m n 𝕜` | `CFC.sqrt (Aᴴ * A)`; `CFC.abs A` for square `A` (equal by `rfl`) | `CFC.abs_eq_cfc_norm` |
| positive part | Mathlib's `A⁺` | `CFC.le_posPart` |
| inverse square root | `(CFC.sqrt A)⁻¹` | `Matrix.PosDef.inv_sqrt_eq_cfc` (new) |
| location of the spectrum | `spectrum ℝ A ⊆ s`; Loewner sandwich for an interval | `Matrix.IsHermitian.spectrum_subset_iff` (new) |
| trace function | `RCLike.re (cfc f A).trace` | — |
| trace exponential | `RCLike.re (NormedSpace.exp A).trace` | — |
| largest eigenvalue | `eigenvalue A 0` (M3) | — |
| polynomial in a matrix | `Polynomial.aeval A p`, `p : ℝ[X]` | — |
| operator convexity | `OperatorConvexOn s f` (new predicate) | — |
| relative entropy | `relativeEntropy A H` (new, real-valued) | — |
| matrix perspective | `matrixPerspective f A H` (new) | — |
| intrinsic dimension | `intrinsicDimension A = re (tr A) / specNorm A` (new) | — |
| complexification | `complexify A : Matrix m n ℂ` (new), `A.map RCLike.toComplex` | `complexify_eq_mapMatrix` |
| derivative of a matrix curve | entrywise `∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t` | — |

New definitions: `OperatorConvexOn`, `relativeEntropy`, `matrixPerspective`, `intrinsicDimension`,
`complexify`. The prototype's `matrixExp`, `matrixLog`, `traceExp`, `traceFunction`, `lambdaMax`,
`lambdaMin`, `symmetricMatrices`, `traceEvenPower` and the `tracePowerAlong` family are not ported
as names: each is a one-token abbreviation of the spelling in the table, and every lemma about it
would have to be restated for the underlying term to be found by `rw` or `simp`.

## 2. Interfaces

**`cfc f A` is the spelling of `f(A)`.** The stage adds the API that makes it usable with the
library's vocabulary: `cfc f A` through any unitary diagonalisation
(`cfc_eq_mul_diagonal_mul_conjTranspose`, for a frame `U : Matrix n r 𝕜` with
`HasOrthonormalCols U`, `card r = card n` and `A = U * diagonal d * Uᴴ`, the shape the spectral
theorem of M3 produces), its trace as a sum over `eigenvalue A i`, its sorted eigenvalues when
`f` is monotone or antitone on the spectrum, and comparison `cfc f A ≤ cfc g A` from `f ≤ g` on
the eigenvalues or on an interval `[a, b]` with `a • 1 ≤ A ≤ b • 1`.

**The location of the spectrum is `spectrum ℝ A ⊆ s` or a Loewner sandwich.** `spectrum ℝ A ⊆ s`
for a general set (it is what Mathlib's `cfc_mono`, `cfc_nonneg` and `StarAlgHom.map_cfc`
consume), `a • 1 ≤ A`, `A ≤ b • 1` for an interval, `A.PosSemidef` and `A.PosDef` for the
half-lines. `Matrix.IsHermitian.spectrum_subset_iff` translates to the sorted eigenvalues. (The
first draft spelled the condition through `eigenvalue A i`; the review reversed that, §8.)

**Everything is over `𝕜`.** The deep results (Löwner–Heinz for general exponents, operator Jensen,
Golden–Thompson, Lieb) are theorems about complex C⋆-algebras: Mathlib's `CFC.rpow_le_rpow`,
`CFC.log_le_log` and `CFC.sqrt_le_sqrt` need a `CStarAlgebra`, which Mathlib provides for
`Matrix n n ℂ` in the scope `Matrix.Norms.L2Operator`, and the prototype proves the trace
inequalities over `ℂ`. `complexify : Matrix m n 𝕜 → Matrix m n ℂ` (entrywise
`RCLike.toComplex`, a real star algebra homomorphism added in `ForMathlib`) is an injective
star-ring homomorphism compatible with traces, the Loewner
order, `eigenvalue`, `cfc` and `exp`; statements are proved over `ℂ` and pulled back. A consumer
with real symmetric matrices never sees `ℂ`.

**Operator convexity is a predicate quantified over all sizes.** `OperatorConvexOn s f` asks for
the convexity inequality `f(a A + b B) ≤ a f(A) + b f(B)`, `a + b = 1`, for complex Hermitian
matrices indexed by `Fin d`, every `d`. Convex combinations are written with two weights
throughout, as Mathlib's `ConvexOn` does. Its
consequences (`cfc_add_le`, operator Jensen) hold over any `𝕜` and any index type. The examples
proved are `x²`, `x⁻¹`, `-log x`, `x log x`. Operator monotonicity gets no predicate: the three
instances (powers `0 ≤ r ≤ 1`, square root, logarithm) are theorems.

**Trace inequalities in two matrices come from one overlap formula.** With
`A = U diag(a) Uᴴ`, `B = V diag(b) Vᴴ`, `tr (f(A) g(B)) = ∑ i j, |(Uᴴ V)_{ij}|² f(a_i) g(b_j)`.
The generalized Klein inequality, Klein's inequality, the mean value trace inequality and trace
Young are scalar inequalities summed against these weights.

**Derivatives are entrywise.** Matrices carry no global norm in Mathlib; `HasDerivAt` for a
matrix-valued curve needs only the product topology, and `Matrix.hasDerivAt_iff_forall_apply`
says it is the entrywise statement. Jacobi's formula and the
derivative of the inverse are stated with hypothesis `∀ i j, HasDerivAt (fun s => A s i j) …` and
scalar or entrywise conclusions, over a normed commutative ring; they go to
`ForMathlib/Analysis/Calculus/Deriv/Matrix.lean`.

## 3. Statement shapes

The skeleton is the authority; this is the map.

`HermitianCalculus.lean`: `cfc_eq_mul_diagonal_mul_conjTranspose`, `cfc_diagonal`,
`Matrix.IsHermitian.cfc_mulVec_of_mulVec_eq_smul`; `cfc_mul_mul_conjTranspose`,
`cfc_submatrix_equiv`, `cfc_fromBlocks_diagonal`; `Matrix.IsHermitian.spectrum_subset_iff`,
`spectrum_subset_Icc_of_le`, `Matrix.PosSemidef.spectrum_subset_Ici`,
`Matrix.PosDef.spectrum_subset_Ioi`; `Matrix.IsHermitian.re_trace_cfc`
(`= ∑ i ∈ range (card n), f (eigenvalue A i)`), `eigenvalue_cfc_of_monotoneOn`,
`eigenvalue_cfc_of_antitoneOn` (index `k + j + 1 = card n`), `re_quadForm_cfc_eq_sum`,
`apply_eigenvalue_zero_le_re_trace_cfc`; `cfc_le_cfc_of_forall_mem_Icc`,
`Matrix.IsHermitian.specNorm_cfc_le`, `abs_re_quadForm_cfc_le`, `mul_card_le_re_trace_cfc`;
`Matrix.PosDef.inv_sqrt_eq_cfc`, `Matrix.PosDef.isUnit_sqrt`.

`Polynomial.lean`: `aeval_diagonal`, `aeval_mul_mul_conjTranspose`,
`Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq`, `exists_cfc_eq_aeval` (degree below the
size), `Matrix.IsHermitian.aeval`, `specNorm_aeval_le`, `specNorm_aeval_le_of_forall_mem_Icc` (the
Chebyshev form), `specNorm_cfc_sub_aeval_le`, `re_trace_aeval`, `re_quadForm_aeval_mulVec_le`
(energy norm); `aeval_mul_eq_mul_aeval_of_mul_eq_mul`, `aeval_mul_conjTranspose_self_mul`
(`p(A Aᴴ) A = A p(Aᴴ A)`), `IsSVD.mul_aeval_conjTranspose_mul_self`,
`singularValues_pow_mul_conjTranspose_self_mul`, `rank_pow_mul_conjTranspose_self_mul`.

`Exponential.lean`: `Matrix.IsHermitian.exp_eq_cfc`, `exp_mul_diagonal_mul_conjTranspose`,
`exp_mul_mul_conjTranspose`, `exp_add_real_smul_one`, `exp_fromBlocks_diagonal`;
`Matrix.IsHermitian.posDef_exp`, `cfc_log_exp`, `Matrix.PosDef.exp_cfc_log`,
`Matrix.IsHermitian.eigenvalue_exp`; `Matrix.IsHermitian.one_add_le_exp`, the transfer rule
`exp_smul_le_one_add_smul_add_smul_sq`, `Matrix.PosSemidef.cfc_log_one_add_le`; the trace
exponential: `re_trace_exp`, `exp_eigenvalue_zero_le_re_trace_exp`,
`re_trace_exp_le_card_mul_exp`, invariance, shift, block sum, continuity.

`Complexification.lean`: `complexify` and its compatibility lemmas (§2).

`TraceFunctions.lean`: `re_trace_cfc_le_re_trace_cfc_of_le` (`MonotoneOn f s`),
`convexOn_re_trace_cfc` on `{A | A.IsHermitian ∧ spectrum ℝ A ⊆ s}`, Klein
`re_trace_mul_cfc_le_re_trace_cfc_sub`, generalized Klein `sum_re_trace_cfc_mul_cfc_nonneg`,
`apply_re_quadForm_le_re_quadForm_cfc`, `specNorm_conjTranspose_mul_mul_pow_le`, Berezin
`re_trace_cfc_conjTranspose_mul_mul_le`; `re_trace_exp_le_re_trace_exp_of_le`,
`convexOn_re_trace_exp`, `re_trace_exp_le_exp_specNorm_sub_mul`; `intrinsicDimension`, its bounds
and block bounds, `Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul`.

`OperatorMonotone.lean`: `Matrix.PosSemidef.rpow_le_rpow` (`r ∈ [0, 1]`),
`Matrix.PosSemidef.sqrt_le_sqrt`, `Matrix.PosDef.cfc_log_le_cfc_log`,
`Matrix.PosDef.posDef_of_le`, `concaveOn_rpow`,
`Matrix.PosDef.le_iff_inv_sqrt_mul_mul_inv_sqrt_le_one`; `OperatorConvexOn`, `.convexOn`,
`.cfc_smul_add_smul_le`, the four examples (`x²`, `x⁻¹`, `-log x`, `x log x`);
`OperatorConvexOn.cfc_conjTranspose_mul_mul_le` (isometry) and
`OperatorConvexOn.cfc_sum_conjTranspose_mul_mul_le` (finite family with
`∑ i, (K i)ᴴ * K i = 1`; the prototype has two terms).

`GoldenThompson.lean`: `Matrix.PosSemidef.re_trace_mul_nonneg`, `re_trace_exp_add_le`,
`Matrix.PosDef.re_trace_exp_add_cfc_log_le`.

`Perspective.lean`: `matrixPerspective`, homogeneity, joint operator convexity
`OperatorConvexOn.matrixPerspective_smul_add_smul_le`.

`Lieb.lean`: `relativeEntropy`, nonnegativity, joint convexity, the two variational formulas as
`IsGreatest` over the image of the positive definite matrices, and
`concaveOn_re_trace_exp_add_cfc_log : ConcaveOn ℝ {A | A.PosDef} fun A => re (exp (H + cfc log A)).trace`.

`TracePowers.lean`: the overlap formula `re_trace_cfc_mul_cfc_eq_sum` and its lifting principle;
`Matrix.IsHermitian.re_trace_pow`, `specNorm_pow_le_re_trace_pow` (`0 < q`);
`re_trace_mul_pow_mul_pow_le`; the mean value trace inequality `re_trace_cfc_sub_mul_cfc_sub_le`
and its power form; trace Young for powers (`re_trace_mul_pow_le_add`) and for conjugate exponents
(`re_trace_mul_le_re_trace_rpow_add`).

`LogDet.lean`: `Matrix.IsHermitian.re_det_cfc`, `Matrix.PosDef.log_re_det_eq_re_trace_cfc_log`,
`Matrix.IsHermitian.re_det_exp`, `Matrix.PosSemidef.log_re_det_one_add_le_re_trace`,
`one_add_re_trace_le_re_det_one_add`, the weighted geometric mean of determinants,
`strictConcaveOn_log_re_det` with its equality case, operator convexity of the inverse,
`strictConvexOn_re_trace_inv`; convexity of the sets of positive semidefinite and positive
definite matrices.

`AbsoluteValue.lean`: `eigenvalue_sqrt_conjTranspose_mul_self`, `nuclearNorm_eq_re_trace_sqrt`,
`schattenNorm_rpow_eq_re_trace_rpow`, `schattenNorm_pow_eq_re_trace_pow`,
`Matrix.IsHermitian.le_abs`, `neg_abs_le`, `abs_le_specNorm_smul_one`.

`ForMathlib/Analysis/Calculus/Deriv/Matrix.lean`: `Matrix.hasDerivAt_iff_forall_apply`,
`hasDerivAt_mul_apply`, `hasDerivAt_trace`, `hasDerivAt_pow_succ_apply`,
`hasDerivAt_trace_pow_succ`, `sum_det_updateRow`, `hasDerivAt_det`, `hasDerivAt_inv_apply`,
`hasDerivAt_log_det`.

`ForMathlib/Analysis/RCLike/ToComplex.lean`: `RCLike.toComplex` and its basic lemmas.

## 4. Consumers

- **Matrix concentration** (Laplace transform method): `exp_eigenvalue_zero_le_re_trace_exp`,
  monotonicity of the trace exponential, the transfer rule, `Matrix.PosDef.cfc_log_le_cfc_log`,
  `Matrix.PosSemidef.cfc_log_one_add_le`,
  Lieb's theorem (subadditivity of matrix cumulants is Lieb plus Jensen for the expectation, which
  is why the theorem is stated as `ConcaveOn` on a set), Golden–Thompson (Ahlswede–Winter), the
  intrinsic dimension lemma.
- **Moment method and exchangeable pairs**: `specNorm_pow_le_re_trace_pow`, the mean value trace
  inequality, trace Young, `re_trace_mul_pow_mul_pow_le`, convexity of trace powers
  (`convexOn_re_trace_cfc` with `f = x^{2q}`).
- **Krylov methods**: `specNorm_aeval_le_of_forall_mem_Icc`, `re_quadForm_aeval_mulVec_le`,
  `re_quadForm_cfc_eq_sum` (Gauss quadrature and Lanczos for `xᴴ f(A) x`),
  `exists_cfc_eq_aeval`.
- **Randomized SVD and subspace iteration**: `singularValues_pow_mul_conjTranspose_self_mul`,
  `IsSVD.mul_aeval_conjTranspose_mul_self`.
- **Experimental design, barrier arguments, volume sampling**: `LogDet.lean`,
  `Matrix.hasDerivAt_log_det`.
- **Trace estimation** (Hutchinson, Hutch++ for `tr f(A)`): `re_trace_cfc`, `specNorm_cfc_le`.

## 5. Files

Under `NLAlib/Matrix/Functions/`:

1. `HermitianCalculus.lean` (imports M3 `CourantFischer`, M2 `Loewner`).
2. `Polynomial.lean` (imports 1, M3 `SVD`).
3. `Exponential.lean` (imports 1).
4. `Complexification.lean` (imports 3).
5. `TraceFunctions.lean` (imports 3, M3a `Schur`).
6. `OperatorMonotone.lean` (imports 4, M7 `Order`).
7. `GoldenThompson.lean` (imports 4, 5).
8. `Perspective.lean` (imports 6).
9. `Lieb.lean` (imports 6, 7; will import 8).
10. `TracePowers.lean` (imports 5).
11. `LogDet.lean` (imports 6, M7 `Determinant`).
12. `AbsoluteValue.lean` (imports 6, M3b `Schatten`).

And `NLAlib/ForMathlib/Analysis/Calculus/Deriv/Matrix.lean`.

Order for proving: 1 and the `ForMathlib` file; then 2, 3; then 4, 5; then 6, 7, 10; then 8, 11,
12; then 9.

## 6. Material

Prototype `Matrix/Functions/*` (47 modules, all proved) and `Matrix/Calculus/*`. Directly usable:
`CFCTrace`, `CFCQuadratic`, `HermitianCalculus`, `PolynomialCalculus`, `PolynomialIntertwining`,
`ExpLog`, `TraceExpBounds`, `GoldenThompson`, `TraceExpMonotone`, `TraceExpConvex`,
`GeneralizedKlein`, `LoewnerHeinz` (real), `LogOperatorConcave`, the `Jensen*` files,
`PerspectiveConvex`, `EntropyNonnegative`, `EntropyJointConvex`, `VariationalTrace*`,
`LiebConcavity`, `TracePowers`, `TraceMeanValue`, `TraceYoung`, `LogDetConcavity`,
`TraceInverseConvexity`, `IntrinsicDimension`, `DeterminantDerivative`, `InverseCalculus`.

Proof machinery that stays private or is not ported: `CoordinatePinching` (coordinate
reflections, used inside one concentration proof), `JointTensor*` (the tensor representation
behind joint convexity), `JensenReflectionAlgebra`, `PolynomialSeries` (derivatives of trace
polynomials along coordinate updates, used by one Stein-method proof; it moves with that proof),
`TracePowerConvexity` (Hessian computation, superseded by `convexOn_re_trace_cfc`),
`UnitaryCalculus` (reflection and reindexing twins of the conjugation lemmas),
`ExtremeEigenvalues` (the `lambdaMax`/`lambdaMin` API, replaced by `eigenvalue A 0` and Loewner
bounds).

## 7. Decisions taken without approval

1. No `matrixExp`, `matrixLog`, `traceExp`, `traceFunction`, `lambdaMax`, `lambdaMin` names.
2. The logarithm is `cfc Real.log A`, not `CFC.log A` (which needs a global normed algebra
   structure on matrices); real powers, the square root, the absolute value and the positive part
   are Mathlib's `A ^ r`, `CFC.sqrt A`, `CFC.abs A`, `A⁺`, all available with `MatrixOrder`.
3. `complexify` is a new public definition, and the route by which results reach `𝕜`.
4. `OperatorConvexOn` quantifies over complex matrices indexed by `Fin d`.
5. Spectrum location by `spectrum ℝ A ⊆ s` or Loewner bounds.
6. Derivatives are stated entrywise and live in `ForMathlib`.
7. New statements with no prototype counterpart: monotone and convex trace functions for a
   general `f`, classical Klein, Berezin, the general mean value trace inequality, trace Young for
   conjugate exponents, `log det (1 + A) ≤ tr A`, the absolute value file, the transfer rule in
   interval form, the finite-family operator Jensen inequality, `x log x` operator convex.
8. Not ported: coordinate pinching, the tensor representation, the polynomial-series derivative
   lemmas, the Hessian route to trace-power convexity.

## 8. Review (Fable, 2026-10-14) and what changed

The review checked every statement, including degenerate cases, against the skeleton. Findings
and their resolution:

1. **False statement.** `Matrix.IsHermitian.specNorm_pow_le_re_trace_pow` at `q = 0` on an empty
   index type (`1 ≤ 0`). The prototype's `0 < q` was restored.
2. `exists_cfc_eq_aeval` had a degree bound one too large for its consumer (`f(A) b` in the Krylov
   space of dimension `n`). Now `p.degree < card n`.
3. The mean value trace inequality was stated in a form that is true but is not
   [MackeyEtAl2014, Lemma 3.4] and needed an integrability argument for nothing. Restated in the
   published form (`g` monotone, `h'` convex); the power version is its corollary.
4. Truncated subtraction removed from statements: `re_trace_mul_pow_mul_pow_le` takes `l`, `k`
   with `Even (l + k)`; trace Young is stated with `p = q + 1`; derivative of a power with
   `Finset.antidiagonal`.
5. One shape for convex combinations (`a • A + b • B`, `a + b = 1`).
6. Mathlib spellings adopted where the first draft used `cfc` with a lambda: `A ^ r`,
   `CFC.abs A`, `A⁺`, `(CFC.sqrt A)⁻¹`. The reason the draft gave for avoiding `CFC.rpow` was
   wrong: only its order lemmas need a C⋆-algebra.
7. `spectrum ℝ A ⊆ s` replaces eigenvalue membership (it had been re-spelled in twelve
   statements).
8. `complexify` is now `A.map RCLike.toComplex` for a new `RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ` in
   `ForMathlib/Analysis/RCLike/ToComplex.lean`, so its compatibility lemmas are `map_*` facts.
9. Deleted as Mathlib's: `cfc_pow`, `isHermitian_cfc`, `cfc_mul_comm`, `aeval_eq_cfc`,
   `cfc_le_cfc_of_forall_eigenvalue`, `posSemidef_cfc`, `Matrix.PosDef.cfc_inv`,
   `exp_add_of_mul_comm`, `exp_real_smul_one`, `convex_setOf_isHermitian`, the `cfc |·|` bridge.
   Deleted as dead weight: `trace_cfc`, `re_det_one_add_le_exp_re_trace`, `re_trace_cfc_add_le`,
   the continuity lemma for Lieb's function, `hasDerivAt_det_smul_one_sub`.
10. Added for the consumers of §4: `apply_eigenvalue_zero_le_re_trace_cfc` (the general first
    step of the Laplace transform and intrinsic dimension arguments),
    `Matrix.PosSemidef.cfc_log_one_add_le`, Jensen for quadratic forms and its corollary
    `specNorm_conjTranspose_mul_mul_pow_le` (the power scheme bound of randomized SVD),
    `specNorm_cfc_sub_aeval_le` (Krylov approximation of `f(A)`), the block bounds for the
    intrinsic dimension, `MonotoneOn` in the monotone trace function, the bridge
    `Matrix.hasDerivAt_iff_forall_apply`.
11. One proposal was not taken: dropping the Hermitian hypotheses of `cfc_fromBlocks_diagonal`.
    With `A` not Hermitian and `B` Hermitian the left side is the junk value `0` and the right
    side is not.
