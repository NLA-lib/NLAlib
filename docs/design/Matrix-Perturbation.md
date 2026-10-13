# Design note: Matrix stage M6, perturbation theory

Status: written 2026-10-14 by the orchestrator while M3b and M5 were being proved; to be
implemented without a maintainer approval stop, by the standing instruction in
`docs/port/status.md`. Choices a maintainer would have been asked about are in §7. The skeleton
(ten files) elaborates against the pinned Mathlib and the earlier stages.

## 0. Scope

Neumann series and perturbation of the inverse; linear systems; separation bounds for the
Sylvester operator; the Davis–Kahan `sin Θ` theorems; Wedin's theorem for singular subspaces;
residual bounds for eigenvalues (Kato–Temple, Bauer–Fike); perturbation of the pseudoinverse and
of least-squares problems; continuity of spectral quantities; first-order perturbation of a simple
eigenvalue.

Eigenvalue and singular value perturbation bounds themselves (Weyl, Hoffman–Wielandt, Mirsky,
Lidskii) are in M3 and M3a.

Not here: conditioning of a differentiable map (the prototype's `MapConditioning`, whose base
definitions live outside `Matrix/`); eigenvalue variation for normal matrices and Bauer–Fike in
other absolute norms (M10, with normal matrices); measurability of spectral quantities (with the
measurability files).

## 1. Objects

No new definitions. The stage states theorems about objects of earlier stages:

| Concept | Spelling | From |
|---|---|---|
| distance between subspaces | `(1 - Q) * P` or, for frames, `Vᴴ * U`, in a norm | M5 |
| every unitarily invariant norm | `(Φ : SymmetricGauge)`, `Φ.matrixNorm` | M3b |
| gaps | `eigengap A k`, `singularGap A k`; mixed gaps written out, `eigenvalue A j - eigenvalue (A + E) (j + 1)` | M3 |
| spectral separation of two blocks | Loewner bounds `a • 1 ≤ L`, `L ≤ b • 1` on one, eigenvalue conditions with valid indices on the other; or pairwise `δ ≤ |eigenvalue L i - eigenvalue M j|` | M2, M3 |
| invariant subspace | `A * U = U * L` | M3 |
| least squares | `IsLeastSquaresSolution A b x`, `pinv`, `rangeProjector`, `conditionNumber` | M4 |

## 2. Interfaces

**The Sylvester operator is the engine.** Every `sin Θ` statement is a lower bound
`δ ‖X‖ ≤ ‖L X - X M‖` applied to `X = Vᴴ U`. The bounds are stated once, in `Sylvester.lean`:

- disc separation (`‖M‖₂ ≤ r`, `L` bounded below by `r + δ`), every unitarily invariant norm, any
  matrices; the proof is three lines and gives the interval and one-sided Hermitian cases after a
  shift;
- arbitrary separation of two Hermitian spectra, Frobenius norm.

The constant `π / 2` bound for arbitrarily interleaved Hermitian spectra in unitarily invariant
norms (Bhatia–Davis–McIntosh) is not ported.

**Davis–Kahan is stated in residual form**, at three levels of the same theorem:

- the engine, with frames: `A * V = V * M` (an invariant subspace of a Hermitian `A`), any pair
  `(U, L)`, a separation of `L` from `M`, conclusion `δ ‖Vᴴ U‖ ≤ ‖Vᴴ (A U - U L)‖`;
- the projector form: `Q` an orthogonal projector commuting with `A` with `Q A Q ≤ μ • Q`, any
  `(U, L)` with `(μ + δ) • 1 ≤ L`, conclusion `δ ‖Q U‖ ≤ ‖Q (A U - U L)‖`;
- the leading-eigenspace form, which is what Rayleigh–Ritz, subspace iteration and randomized SVD
  have: `W` a frame of leading eigenvectors, a Ritz pair `(U, L)` with
  `(λ_{j+1}(A) + δ) • 1 ≤ L`, conclusion `δ ‖(1 - W Wᴴ) U‖ ≤ ‖A U - U L‖`. No frame of the
  complement appears.

No eigenvalue proof term appears, `U` need not be orthonormal or invariant, and the perturbation
theorems are the case `A U - U L = E U`.

**Leading subspaces: two hypotheses, for two roles.** The subspace whose *complement* must be
bounded (the "true" leading eigenspace) is given by a frame of eigenvectors,
`A * W = W * diagonal (fun i : Fin (j + 1) => eigenvalue A i)` with `HasOrthonormalCols W`. This
is robust under repeated eigenvalues: `one_sub_mul_mul_one_sub_le_of_mul_eq_mul_diagonal` gives
`(1 - W Wᴴ) A (1 - W Wᴴ) ≤ λ_{j+1}(A) • (1 - W Wᴴ)` with no gap assumption. The weaker spelling
`A * W = W * Λ`, `λ_j(A) • 1 ≤ Λ` does not determine the subspace when `λ_j = λ_{j+1}` (take
eigenvalues `3, 2, 2, 2` and `W` spanning two eigenvectors for `2`), so it gives the complement
bound only with a strict gap; that is a second constructor lemma. The subspace that is *compared*
(the Ritz or perturbed side) only needs `A * U = U * L` with a Loewner bound on `L`, any number
of columns, any basis. The number of columns of a leading frame is `j + 1` so that the gap
`eigenvalue A j - eigenvalue (A + E) (j + 1)` needs no subtraction.

**Two kinds of gap.** The classical theorem needs a gap between the two matrices,
`δ ≤ λ_j(A) - λ_{j+1}(A + E)`, and holds in every unitarily invariant norm. The statistical
variants need only `eigengap A (j + 1)` and hold in the spectral and Frobenius norms with
constants `2`, `√2` and `2 √(j + 1)`. The Frobenius ones come from the variational inequality
`eigengap · ‖(1 - U Uᴴ) Q‖_F² ≤ ∑ λ_i - re tr (Qᴴ A Q)`, stated on its own because PCA-type
consumers use it directly.

**Wedin** has the same shape: the coupled separation bound, then a residual form for frames
`U`, `V` of leading singular vectors of `A` against any triple `(U', V', S)`, then the
perturbation theorem; the conclusion bounds `max (‖(1 - U Uᴴ) U'‖, ‖(1 - V Vᴴ) V'‖)`.

**Relative perturbations.** The form the sketching layer needs is multiplicative on the Gram
matrix: from `a • Aᴴ A ≤ (S A)ᴴ (S A) ≤ b • Aᴴ A` to bounds on the singular values, the
pseudoinverse and the condition number of `S A` (`Relative.lean`). Relative `sin Θ` theorems and
componentwise relative bounds (`|E| ≤ ε |A|`) have no consumer and are not ported.

**Linear systems and least squares use the real `conditionNumber`** and the predicate
`IsLeastSquaresSolution`; relative bounds are written without divisions where a denominator could
vanish (`‖x - y‖ ‖b‖ ≤ κ ‖b - A y‖ ‖x‖`).

**The pseudoinverse** is perturbed through Wedin's three-term identity, which gives a bound in
every unitarily invariant norm at once; the sharper constants (golden ratio, `√2`) are stated for
the spectral and Frobenius norms.

## 3. Statement shapes

```lean
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul (Φ : SymmetricGauge)
    {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} {r δ : ℝ} (hM : specNorm M ≤ r)
    (hL : ((r + δ) ^ 2) • (1 : Matrix m m 𝕜) ≤ Lᴴ * L) (X : Matrix m n 𝕜) :
    δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M)
theorem mul_frobNorm_le_frobNorm_mul_sub_mul {L : Matrix m m 𝕜} {M : Matrix n n 𝕜}
    (hL : L.IsHermitian) (hM : M.IsHermitian) {δ : ℝ}
    (hsep : ∀ i, i < Fintype.card m → ∀ j, j < Fintype.card n →
      δ ≤ |eigenvalue L i - eigenvalue M j|)
    (X : Matrix m n 𝕜) : δ * frobNorm X ≤ frobNorm (L * X - X * M)

theorem SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_eigenvalue (Φ : SymmetricGauge)
    {A : Matrix n n 𝕜} {V : Matrix n q 𝕜} {M : Matrix q q 𝕜} (hA : A.IsHermitian)
    (hM : M.IsHermitian) (hAV : A * V = V * M) {U : Matrix n p 𝕜} {L : Matrix p p 𝕜}
    {a b δ : ℝ} (hL₁ : a • (1 : Matrix p p 𝕜) ≤ L) (hL₂ : L ≤ b • (1 : Matrix p p 𝕜))
    (hMsep : ∀ i, i < Fintype.card q → eigenvalue M i ≤ a - δ ∨ b + δ ≤ eigenvalue M i) :
    δ * Φ.matrixNorm (Vᴴ * U) ≤ Φ.matrixNorm (Vᴴ * (A * U - U * L))
theorem SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_eigenvalue_sub (Φ : SymmetricGauge)
    {A E : Matrix n n 𝕜} (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ}
    {U U' : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hU' : HasOrthonormalCols U')
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hAU' : (A + E) * U' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue (A + E) i : ℝ) : 𝕜))
    {δ : ℝ} (hδ : δ ≤ eigenvalue A j - eigenvalue (A + E) (j + 1)) :
    δ * Φ.matrixNorm ((1 - U' * U'ᴴ) * U) ≤ Φ.matrixNorm (E * U)
theorem specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap … (hgap : 0 < eigengap A (j + 1)) :
    specNorm ((1 - U' * U'ᴴ) * U) ≤ 2 * specNorm E / eigengap A (j + 1)
theorem eigengap_mul_frobNorm_one_sub_mul_sq_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {j : ℕ}
    {U Q : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜)) :
    eigengap A (j + 1) * frobNorm ((1 - U * Uᴴ) * Q) ^ 2 ≤
      ∑ i ∈ Finset.range (j + 1), eigenvalue A i - RCLike.re (Qᴴ * A * Q).trace

theorem SymmetricGauge.mul_max_matrixNorm_one_sub_mul_le_of_singularValues_sub (Φ : SymmetricGauge)
    … {δ : ℝ} (hδ : δ ≤ singularValues (A + E) j - singularValues A (j + 1)) :
    δ * max (Φ.matrixNorm ((1 - U * Uᴴ) * U')) (Φ.matrixNorm ((1 - V * Vᴴ) * V')) ≤
      max (Φ.matrixNorm (E * V')) (Φ.matrixNorm (Eᴴ * U'))

theorem specNorm_inv_add_sub_inv_le {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) :
    specNorm ((A + E)⁻¹ - A⁻¹) ≤ specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E))
theorem norm_sub_le_conditionNumber_mul_of_add_mulVec_eq {A E : Matrix n n 𝕜} (hA : IsUnit A)
    {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A) (hε : conditionNumber A * ε < 1)
    {x y b f : n → 𝕜} (hx : A *ᵥ x = b) (hy : (A + E) *ᵥ y = b + f)
    (hf : ‖WithLp.toLp 2 f‖ ≤ ε * ‖WithLp.toLp 2 b‖) :
    ‖WithLp.toLp 2 (y - x)‖ ≤
      2 * ε * conditionNumber A / (1 - conditionNumber A * ε) * ‖WithLp.toLp 2 x‖

theorem Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) (μ : ℝ) :
    ∃ i, i < Fintype.card n ∧
      |eigenvalue A i - μ| * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x - μ • x)‖
theorem exists_norm_sub_le_conditionNumber_mul_specNorm {A V E : Matrix n n 𝕜} {d : n → 𝕜}
    (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal d) {x : n → 𝕜} (hx : x ≠ 0) {μ : 𝕜}
    (hμ : (A + E) *ᵥ x = μ • x) : ∃ i, ‖d i - μ‖ ≤ conditionNumber V * specNorm E

theorem pinv_sub_pinv (A B : Matrix m n 𝕜) :
    pinv B - pinv A =
      -(pinv B * (B - A) * pinv A) + pinv B * (pinv B)ᴴ * (B - A)ᴴ * (1 - A * pinv A) +
        (1 - pinv B * B) * (B - A)ᴴ * (pinv A)ᴴ * pinv A
theorem SymmetricGauge.matrixNorm_pinv_sub_pinv_le (Φ : SymmetricGauge) (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (pinv B - pinv A) ≤
      (specNorm (pinv B) * specNorm (pinv A) + specNorm (pinv B) ^ 2 + specNorm (pinv A) ^ 2) *
        Φ.matrixNorm (B - A)
theorem IsLeastSquaresSolution.norm_sub_le {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (hE : specNorm (pinv A) * specNorm E < 1)
    {b f : m → 𝕜} {x y : n → 𝕜} (hx : IsLeastSquaresSolution A b x)
    (hy : IsLeastSquaresSolution (A + E) (b + f) y) :
    ‖WithLp.toLp 2 (y - x)‖ ≤ specNorm (pinv (A + E)) *
      (‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖ +
        specNorm (pinv A) * specNorm E * ‖WithLp.toLp 2 (b - A *ᵥ x)‖)

theorem Matrix.IsHermitian.hasDerivAt_eigenvalue_add_smul {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ} (hk : k < Fintype.card n)
    (hsimple : ∀ i, i < Fintype.card n → i ≠ k → eigenvalue A i ≠ eigenvalue A k)
    {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) (hAx : A *ᵥ x = eigenvalue A k • x) :
    HasDerivAt (fun t : ℝ => eigenvalue (A + t • E) k) (RCLike.re (star x ⬝ᵥ E *ᵥ x)) 0
theorem continuousOn_pinv_setOf_rank_eq (r : ℕ) :
    ContinuousOn (pinv : Matrix m n 𝕜 → Matrix n m 𝕜) {A | A.rank = r}
```

## 4. Consumers

| Item | Consumed by |
|---|---|
| Sylvester separation bounds | Davis–Kahan and Wedin here; block diagonalisation and error analysis of Rayleigh–Ritz in the Krylov layer |
| Davis–Kahan, residual form | Rayleigh–Ritz and Lanczos error bounds (Ritz pairs with residuals); subspace iteration; sketched eigensolvers |
| Davis–Kahan and Wedin with the unperturbed gap | PCA and spectral clustering consistency, matrix completion, any "plug-in" estimate where only the population gap is known |
| variational `sin Θ` inequality | excess-risk bounds for PCA and low-rank approximation; analysis of randomized subspace methods through the captured trace |
| residual bounds, Kato–Temple | a posteriori error estimates and stopping criteria for eigensolvers |
| Bauer–Fike | non-normal eigenvalue sensitivity; pseudospectral remarks; Arnoldi |
| inverse and linear system perturbation | backward-to-forward error conversion for direct and iterative solvers; preconditioning |
| pseudoinverse and least-squares perturbation | sketch-and-solve and sketch-and-precondition error analysis; LSQR stopping rules |
| continuity results | measurability of spectral quantities in the random-matrix layers; existence arguments |
| derivative of a simple eigenvalue | sensitivity analysis; Rayleigh quotient iteration |

## 5. Files

Under `NLAlib/Matrix/Perturbation/`:

1. `Inverse.lean` (imports M3b `UnitarilyInvariant`, M4 `ConditionNumber`).
2. `Sylvester.lean` (imports M3b, M2 `Loewner`, M3 `Weyl`).
3. `DavisKahan.lean` (imports 2, M1 `OrthonormalBasis`, M3a `KyFan`).
4. `Wedin.lean` (imports 2, M3 `LowRank`).
5. `Residual.lean` (imports M4 `ConditionNumber`, M3 `CourantFischer`).
6. `Pseudoinverse.lean` (imports M3b, M4 `NormBounds`).
7. `LeastSquares.lean` (imports 6, M4 `LeastSquares`, `ConditionNumber`).
8. `Continuity.lean` (imports 6, M3a `TraceInequalities`).
9. `SimpleEigenvalue.lean` (imports 5, M3 `Weyl`).
10. `Relative.lean` (imports M4 `ConditionNumber`, M3 `Weyl`).

Independent for proving: 1, 2, 5, 6, 10 at once; then 3, 4, 7, 8, 9.

## 6. Material

Read: prototype `Matrix/Perturbation/*` (56 modules).

Reused: the Neumann series and inverse bounds; the Sylvester and coupled separation arguments
(real, in the spectral and Frobenius norms, redone over `𝕜` and for every unitarily invariant norm
where the argument allows); Wedin's pseudoinverse identities; the least-squares chain; the
implicit-function argument for a simple eigenvalue of a complex matrix.

Not reproduced: `eigenvalueProjector`, `topEigenframe`, `headColumns`, `sinePrincipalAngles` and
every statement built on them; the least-squares angle functions `leastSquaresCos`,
`leastSquaresEta`, `leastSquaresTan` and the forward-error formulas written with them (the bound
with the residual norm carries the same information); bundled `*_bounds` theorems; the pencil
lemmas (instances of Weyl's inequality); scalar helper lemmas.

## 7. Decisions taken without approval

1. **Davis–Kahan in residual form with frames is the primary statement**; perturbation and
   leading-eigenspace forms are corollaries.
2. **Interval-type separations give every unitarily invariant norm; arbitrary separations give the
   Frobenius norm only.** The `π / 2` theorem is left out.
3. **Leading eigenvectors and singular vectors enter as hypotheses on frames with `j + 1`
   columns** where the complement has to be bounded; the compared side takes any invariant pair
   with a Loewner bound.
4. **Bounds with the unperturbed gap are stated separately** (spectral: constant `2`; Frobenius:
   `√2` and `2 √(j + 1)`), together with the variational inequality they come from.
5. **Least-squares perturbation is stated with `IsLeastSquaresSolution` and the residual norm**;
   the angle parametrisation of Golub–Van Loan is not reproduced.
6. **The derivative of a simple Hermitian eigenvalue is stated for `eigenvalue (A + t • E) k`
   itself**, proved from the quadratic residual bound; the implicit-function branch is kept only
   for general complex matrices.
7. **Map conditioning, normal-matrix variation and absolute-norm Bauer–Fike leave this stage.**
8. **The raw "no other eigenvalue near" conditions** (`hiso` in `Residual.lean`, `hsimple` and
   `hsep` in `SimpleEigenvalue.lean`) are written out each time; they are a candidate interface if
   a third file needs them.

## 8. Review (Fable, 2026-10-14) and what changed

The review confirmed the residual form with `Vᴴ * U` as the engine, the `Φ` statements flagged for
checking (the disc form needs no sign condition; the coupled bound; the inverse and pseudoinverse
bounds), and every degenerate case listed (large `E`, full-size frames, ties, `δ ≤ 0`, size and
rank zero, the constants of the second-order remainder). Folded in:

1. Added the leading-eigenspace residual form with no complement frame
   (`SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_add_smul_one_le`) and, underneath it, the
   projector form (`SymmetricGauge.mul_matrixNorm_mul_le_of_mul_mul_le`).
2. The review proposed spelling a leading frame as `A * U = U * L`, `λ_j(A) • 1 ≤ L` everywhere,
   as equal in strength to the frame of eigenvectors. It is not, under repeated eigenvalues (§2);
   the Loewner spelling is used for the compared side, the eigenvector frame for the side whose
   complement is bounded, and the Loewner-with-gap constructor lemma is provided.
3. Redundant twins removed: the primed disc form and the spectral-norm copy of the interval
   Sylvester bound; `hT₂` dropped from the coupled bound (for square `T` it follows from `hT₁`).
4. `Relative.lean` added (§2), answering the brief's question on relative forms.
5. The Lipschitz and continuity statements for the optimal rank-`k` error are stated for every
   unitarily invariant norm.
6. The bounds with the unperturbed gap are all stated in the direction `(1 - U Uᴴ) U'` (estimate
   against truth), with a pointer to the equal-rank symmetry of M5.
7. Docstrings: Kato–Temple and the quadratic bound do not need `ℓ` to be an eigenvalue; the branch
   theorem uses the bilinear pairing.
8. To be placed by subject when proved: `SymmetricGauge.isLeast_matrixNorm_sub_of_rank_le` in
   `Norms/UnitarilyInvariant.lean`, the golden-ratio block lemma in `Norms/Projector.lean`.
