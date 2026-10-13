# Design note: Matrix stage M4, pseudoinverse and least squares

Status: written 2026-10-14 by the orchestrator while M3 was being proved; implemented without a
maintainer approval stop, by the standing instruction in `docs/port/status.md`. Choices a
maintainer would have been asked about are in §7.

This stage is designed and built before M3a and M3b (majorization; Schatten and unitarily
invariant norms). It depends on neither, and the sketching and solver layers need it first.
The order after M3 is therefore **M4 → M3a → M3b → M5 → M6 → …**.

## 0. Scope

The Penrose conditions and uniqueness; the Moore–Penrose pseudoinverse of every matrix; its
projector identities, transformations and full-rank formulas; its singular values and norms;
least-squares solutions; the condition number and the distance to rank deficiency; the
generalized Schur complement that M1 deferred.

Not here: perturbation of inverses, linear systems and pseudoinverses (M6); conditioning of
nonlinear maps through Jacobians (the prototype's `MapConditioning`, which is calculus and has no
consumer in this layer; it is recorded in the ledger as deferred to M6).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| pseudoinverse (predicate) | `IsPinv A B`: the four Penrose identities | — |
| pseudoinverse | `pinv A : Matrix n m 𝕜`, every shape and rank | `pinv_of_isUnit : pinv A = A⁻¹`; Mathlib has no pseudoinverse |
| full-rank formulas | no definitions; `pinv_eq_inv_mul_conjTranspose` under `Function.Injective A.mulVec`, `pinv_eq_conjTranspose_mul_inv` under `Function.Injective Aᴴ.mulVec` | — |
| full row rank | `Function.Injective Aᴴ.mulVec` | — |
| least-squares solution | `IsLeastSquaresSolution A b x := ∀ y, ‖toLp 2 (b - A *ᵥ x)‖ ≤ ‖toLp 2 (b - A *ᵥ y)‖` | — |
| least-squares residual | `(1 - rangeProjector A) *ᵥ b`, no definition | M1's row |
| condition number | `conditionNumber A : ℝ := specNorm A * specNorm (pinv A)`, any shape | `conditionNumber_of_isUnit` |
| generalized Schur complement | `C - Bᴴ * pinv A * B`, no definition | — |

## 2. Interfaces

**One pseudoinverse.** The prototype had the general `moorePenroseInverse` and two more
definitions, `pinvL A = (AᴴA)⁻¹Aᴴ` and `pinvR A = Aᴴ(AAᴴ)⁻¹`, with bridges; sketching theorems
were stated with `pinvL` and a hypothesis `IsUnit (Aᴴ * A)`, range-finder theorems with `pinvR`.
Here `pinv A` is the only object. The formulas are lemmas under the library's full-rank
hypothesis `Function.Injective A.mulVec` (M1's row). A statement about `(S A)⁺` is a statement
about `pinv (S * A)`, and a proof that wants the formula rewrites with it.

**`IsPinv A B`** is how a pseudoinverse is recognised: `pinv_eq_iff : pinv A = B ↔ IsPinv A B`.
Every transformation rule (`pinv (Q * A) = pinv A * Qᴴ`, `pinv Aᴴ = (pinv A)ᴴ`, the SVD formula)
is proved by checking four identities.

**The pseudoinverse and the projector are tied by two equations**, `mul_pinv : A * pinv A =
rangeProjector A` and `pinv_mul : pinv A * A = rangeProjector Aᴴ`. They are not simp lemmas in
either direction: both sides are normal forms in their own contexts.

**`IsSVD.pinv_eq`** gives `pinv A = V * diagonal σ⁻¹ * Uᴴ` from any thin SVD, with `0⁻¹ = 0`
covering vanishing singular values, so the compact and the thin SVD need no separate statements.

**`IsLeastSquaresSolution A b x`** is the named interface for least squares, taken and concluded
by theorems. A sketch-and-solve theorem will read: if `x̂` satisfies
`IsLeastSquaresSolution (S * A) (S *ᵥ b) x̂` and `S` embeds the range of `[A b]`, then
`‖b - A x̂‖ ≤ (1 + ε) ‖(1 - rangeProjector A) *ᵥ b‖`.

**`conditionNumber` is real-valued and defined for every matrix.** The contract's §5.2 gave
"`conditionNumber` is `⊤`" as its example of a junk value, following the prototype, which had an
`ℝ≥0∞`-valued condition number for square matrices and a separate real-valued
`moorePenroseConditionNumber`. One real-valued function replaces both: every use multiplies the
condition number by a small quantity inside a `calc` chain, where `ℝ≥0∞` forces coercions and
loses `positivity` and `gcongr`. The price is that a singular square matrix has a finite
condition number (the ratio to its smallest nonzero singular value); a theorem that means
"invertible" says `IsUnit A`.

## 3. Statement shapes

```lean
structure IsPinv (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) : Prop where
  mul_mul_left : A * B * A = A
  mul_mul_right : B * A * B = B
  isHermitian_left : (A * B).IsHermitian
  isHermitian_right : (B * A).IsHermitian

theorem IsPinv.unique (hB : IsPinv A B) (hC : IsPinv A C) : B = C
theorem exists_isPinv (A : Matrix m n 𝕜) : ∃ B : Matrix n m 𝕜, IsPinv A B

noncomputable def pinv (A : Matrix m n 𝕜) : Matrix n m 𝕜      -- the one given by `exists_isPinv`
theorem pinv_eq_iff {A : Matrix m n 𝕜} {B : Matrix n m 𝕜} : pinv A = B ↔ IsPinv A B
theorem mul_pinv (A : Matrix m n 𝕜) : A * pinv A = rangeProjector A
theorem pinv_mul (A : Matrix m n 𝕜) : pinv A * A = rangeProjector Aᴴ

theorem IsSVD.pinv_eq [DecidableEq r] {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ}
    {V : Matrix n r 𝕜} (h : IsSVD A U σ V) :
    pinv A = V * Matrix.diagonal (fun i => (((σ i)⁻¹ : ℝ) : 𝕜)) * Uᴴ

theorem pinv_eq_inv_mul_conjTranspose [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : pinv A = (Aᴴ * A)⁻¹ * Aᴴ
theorem pinv_mul_rev {A : Matrix l m 𝕜} {B : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (hB : Function.Injective Bᴴ.mulVec) :
    pinv (A * B) = pinv B * pinv A

theorem pinv_conjTranspose (A : Matrix m n 𝕜) : pinv Aᴴ = (pinv A)ᴴ
theorem pinv_smul (c : 𝕜) (A : Matrix m n 𝕜) : pinv (c • A) = c⁻¹ • pinv A
theorem HasOrthonormalCols.pinv_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : pinv (Q * A) = pinv A * Qᴴ
theorem HasOrthonormalCols.pinv_mul_conjTranspose_right [DecidableEq n] {Q : Matrix l n 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : pinv (A * Qᴴ) = Q * pinv A
theorem pinv_eq_conjTranspose_mul_inv [DecidableEq m] {A : Matrix m n 𝕜}
    (hA : Function.Injective Aᴴ.mulVec) : pinv A = Aᴴ * (A * Aᴴ)⁻¹
theorem pinv_mul_self_of_injective [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : pinv A * A = 1
theorem mul_pinv_self_of_injective_conjTranspose [DecidableEq m] {A : Matrix m n 𝕜}
    (hA : Function.Injective Aᴴ.mulVec) : A * pinv A = 1
theorem mul_pinv_conjTranspose_mul_self_mul_conjTranspose (A : Matrix m n 𝕜) :
    A * pinv (Aᴴ * A) * Aᴴ = rangeProjector A
theorem pinv_eq_pinv_conjTranspose_mul_self_mul (A : Matrix m n 𝕜) : pinv A = pinv (Aᴴ * A) * Aᴴ

theorem specNorm_pinv (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = A.rank) :
    specNorm (pinv A) = (singularValues A k)⁻¹
theorem specNorm_pinv_sq_le_inv_of_smul_one_le [DecidableEq n] {A : Matrix m n 𝕜} {a : ℝ}
    (ha : 0 < a) (h : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A) : specNorm (pinv A) ^ 2 ≤ a⁻¹
theorem frobNorm_pinv_sq_eq_re_trace_inv [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : frobNorm (pinv A) ^ 2 = RCLike.re ((Aᴴ * A)⁻¹).trace
theorem frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose [DecidableEq m]
    {A : Matrix m n 𝕜} (hA : Function.Injective Aᴴ.mulVec) :
    frobNorm (pinv A) ^ 2 = RCLike.re ((A * Aᴴ)⁻¹).trace
theorem smul_one_le_conjTranspose_mul_self_iff_specNorm_pinv_sq_le [DecidableEq n]
    {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) {a : ℝ} (ha : 0 < a) :
    a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A ↔ specNorm (pinv A) ^ 2 ≤ a⁻¹

def IsLeastSquaresSolution (A : Matrix m n 𝕜) (b : m → 𝕜) (x : n → 𝕜) : Prop :=
  ∀ y : n → 𝕜, ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤ ‖WithLp.toLp 2 (b - A *ᵥ y)‖
theorem isLeastSquaresSolution_iff_normal_equations {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔ Aᴴ *ᵥ (A *ᵥ x) = Aᴴ *ᵥ b
theorem isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec {A : Matrix m n 𝕜}
    {b : m → 𝕜} {x : n → 𝕜} : IsLeastSquaresSolution A b x ↔ A *ᵥ x = rangeProjector A *ᵥ b
theorem isLeastSquaresSolution_pinv_mulVec (A : Matrix m n 𝕜) (b : m → 𝕜) :
    IsLeastSquaresSolution A b (pinv A *ᵥ b)
theorem IsLeastSquaresSolution.norm_pinv_mulVec_le (h : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 (pinv A *ᵥ b)‖ ≤ ‖WithLp.toLp 2 x‖
theorem existsUnique_isLeastSquaresSolution_iff (A : Matrix m n 𝕜) (b : m → 𝕜) :
    (∃! x, IsLeastSquaresSolution A b x) ↔ Function.Injective A.mulVec
theorem isLeastSquaresSolution_iff_isMinOn {A : Matrix m n 𝕜} {b : m → 𝕜} {x : n → 𝕜} :
    IsLeastSquaresSolution A b x ↔
      IsMinOn (fun y : n → 𝕜 => ‖WithLp.toLp 2 (b - A *ᵥ y)‖) Set.univ x
theorem norm_sub_mulVec_sq_eq_add_norm_mulVec_sub_pinv_sq [DecidableEq m] (A : Matrix m n 𝕜)
    (b : m → 𝕜) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (b - A *ᵥ y)‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖ ^ 2 +
        ‖WithLp.toLp 2 (A *ᵥ (y - pinv A *ᵥ b))‖ ^ 2

noncomputable def conditionNumber (A : Matrix m n 𝕜) : ℝ := specNorm A * specNorm (pinv A)
theorem conditionNumber_eq_singularValues_div (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = A.rank) :
    conditionNumber A = singularValues A 0 / singularValues A k
theorem conditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one [DecidableEq n]
    {A : Matrix m n 𝕜} {a b : ℝ} (ha : 0 < a) (h₁ : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A)
    (h₂ : Aᴴ * A ≤ b • (1 : Matrix n n 𝕜)) : conditionNumber A ^ 2 ≤ b / a
theorem isLeast_specNorm_not_injective_add (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    IsLeast (specNorm '' {E : Matrix m n 𝕜 | ¬ Function.Injective (A + E).mulVec})
      (singularValues A k)

theorem posSemidef_fromBlocks_iff_pinv {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      A.PosSemidef ∧ LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin ∧
        (C - Bᴴ * pinv A * B).PosSemidef
```

`conditionNumber` registers a `positivity` extension, as the norms do.

## 4. Consumers

| Item | Consumed by |
|---|---|
| `pinv`, projector identities | least squares; M5 (oblique projections, tangents); M6 pseudoinverse perturbation (Wedin); range finders (`Ω₁⁺`); sketch-and-solve; Nyström (`(Ωᴴ A Ω)⁺`); Kaczmarz |
| `IsSVD.pinv_eq`, `specNorm_pinv` | M6; conditioning of sketched bases |
| `specNorm_pinv_sq_le_inv_of_smul_one_le`, `conditionNumber_sq_le_div_…` | subspace embeddings: `‖(S U)⁺‖` and `κ(S U)`; preconditioned solvers (sketch-and-precondition) |
| `frobNorm_pinv_sq_eq_re_trace_inv` | expected `‖Ω⁺‖_F²` for Gaussian `Ω` (range finder in Frobenius norm) |
| `IsLeastSquaresSolution` | sketch-and-solve; LSQR and CGLS (Krylov); M6 least-squares perturbation; M9 QR solution |
| `conditionNumber` | M6 linear systems and inverse perturbation; convergence rates of CG and Chebyshev |
| distance to rank deficiency | M6; M9 rank-revealing factorizations |
| generalized Schur complement | M7 block inequalities; Nyström and partial Cholesky |

## 5. Files

Under `NLAlib/Matrix/Pseudoinverse/`:

1. `Penrose.lean` (imports M1 `Projector`): `IsPinv`, uniqueness, stability, projector form,
   examples including the two full-rank formulas.
2. `Pinv.lean` (imports 1, M3 `SVD`): existence, `pinv`, characterisation, projector identities,
   transformations, the SVD formula, full rank, the reverse-order law.
3. `NormBounds.lean` (imports 2): singular values, spectral and Frobenius norms of `pinv`.
4. `LeastSquares.lean` (imports 3): `IsLeastSquaresSolution` and its theory.
5. `ConditionNumber.lean` (imports 3, M3 `LowRank`): `conditionNumber`, distance to rank
   deficiency.
6. `GeneralizedSchur.lean` (imports 2, M1 `SchurComplement`): Albert's criterion with `pinv`, the
   partial minimum.

Independent for proving: 3 and 6 after 2; 4 and 5 after 3.

## 6. Material

Read: prototype `Matrix/Basic/{PenroseIdentities, MoorePenrose, MoorePenroseProjector,
MoorePenroseRank, MoorePenroseTransformations, Pseudoinverse, LeastSquares, SingletonInverse,
GeneralizedSchurComplement}`, `Matrix/Norms/RankNorm`,
`Matrix/Perturbation/{ConditionNumber, Conditioning, MapConditioning, DistanceToSingularity}`.

Reused: the Penrose algebra (already over `𝕜`), existence through the SVD, the transformation
rules, least squares (real-only in the prototype, restated over `𝕜`), the condition number API,
distance to singularity.

Not reproduced: `pinvL`, `pinvR` and their eighteen lemmas (they are `pinv` under a rank
hypothesis); the `ℝ≥0∞` condition number and its `toReal` bridges; `generalizedSchurComplement`
as a definition; `rangeProjector` defined as `B * moorePenroseInverse B` (now M1's definition
and the lemma `mul_pinv`); real-only dot-product statements of least squares; the QR forms of
least squares (M9).

## 7. Decisions taken without approval

1. **One pseudoinverse, named `pinv`**, with the predicate `IsPinv`. The contract's §4 used
   `moorePenroseInverse` as an example of a definition name; `pinv` is what the subject calls it
   and statements such as `specNorm (pinv (S * A))` are read constantly.
2. **No `pinvL`/`pinvR`.** Full-rank formulas are lemmas under `Function.Injective A.mulVec`.
3. **`conditionNumber` is real-valued, for every shape**, replacing both prototype notions. This
   contradicts the example in CONTRIBUTING §5.2, which is amended.
4. **`IsLeastSquaresSolution` is a named predicate** over `𝕜`, not Mathlib's `IsMinOn` spelled
   out at each use.
5. **The generalized Schur complement has no definition.**
6. **M4 is built before M3a and M3b.**

## 8. Design review (Fable, 2026-10-14)

Eleven comments; no decision in §7 was reversed. The condition number stays real-valued and
defined for every shape: no listed consumer needs `⊤`, and for a rank-deficient consistent system
the value `σ₀ / σ_{r-1}` is the effective condition number that randomized Kaczmarz uses.

Folded in:

- §3 now writes out the transformation rules, the full-row-rank formula and the one-sided inverse
  identities; the randomized range finder starts from `Ω₁ Ω₁⁺ = 1` for a full-row-rank block.
- `frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose`, the full-row-rank mirror.
- `mul_pinv_conjTranspose_mul_self_mul_conjTranspose : A * pinv (Aᴴ * A) * Aᴴ = rangeProjector A`,
  the identity behind Nyström.
- The least-squares Pythagoras equality through `pinv`, and
  `isLeastSquaresSolution_iff_isMinOn`, so that minimisation over a Krylov subspace is Mathlib's
  `IsMinOn` on that subspace with no second predicate. No matrix right-hand-side predicate: M2's
  best-approximation lemma with `mul_pinv` covers it.
- The equivalence `a • 1 ≤ Aᴴ * A ↔ specNorm (pinv A) ^ 2 ≤ a⁻¹` for full column rank.
- The reverse-order law is named `pinv_mul_rev` (Mathlib's `mul_inv_rev`), avoiding a clash with
  `pinv_mul : pinv A * A = …`.
- Albert's criterion states range containment in the §5.3 spelling.
- Files renamed to `NormBounds.lean` and `GeneralizedSchur.lean`, so that no basename repeats an
  existing file's.

Recorded for consumers: `pinv` is neither continuous nor monotone in the Loewner order (the rank
can jump), so M6 states Wedin's identity directly. There is no "scaled condition number"
definition; the Kaczmarz rate is `1 - singularValues A k ^ 2 / frobNorm A ^ 2` with
`k + 1 = card n`.
