# Design note: Matrix stage M3b, Schatten and unitarily invariant norms

Status: written 2026-10-14 by the orchestrator while M3a was being proved; to be implemented
after M3a without a maintainer approval stop, by the standing instruction in
`docs/port/status.md`. Choices a maintainer would have been asked about are in §7. The skeleton
(five files) elaborates against the pinned Mathlib and the earlier stages.

## 0. Scope

The Ky Fan norms (the rest of their API; the definition and triangle inequality are in M3a), the
nuclear norm, the Schatten family, Hölder's inequality and duality for Schatten norms, symmetric
gauge functions, the unitarily invariant norm of a gauge, Fan dominance, Mirsky's theorem and
Eckart–Young–Mirsky in every unitarily invariant norm.

This is the part of the brief's M2 that needs singular values (see `Matrix-Norms.md` §0).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| Ky Fan norm | `kyFanNorm k A` (M3a) | `kyFanNorm_one : kyFanNorm 1 A = specNorm A` |
| nuclear norm | `nuclearNorm A`, the sum of the singular values | `schattenNorm_one` |
| Schatten norm | `schattenNorm q A`, `q : ℝ≥0∞`, the `PiLp q` norm of the first `min (card m) (card n)` singular values | the definition; `schattenNorm_two`, `schattenNorm_top` |
| exponent relations | Mathlib's `ENNReal.HolderTriple q r s`, `ENNReal.HolderConjugate q r`; an explicit `hq : 1 ≤ q` for the triangle inequality | — |
| symmetric gauge function | `Φ : SymmetricGauge`, a norm on `ℕ →₀ ℝ` invariant under permutations and absolute values | carrier is the type of `LinearMap.singularValues` |
| unitarily invariant norm | `Φ.matrixNorm A := Φ (singularValuesFinsupp A)`, for every shape | `lpGauge_matrixNorm`, `kyFanGauge_matrixNorm` |
| singular values as a finitely supported sequence | `singularValuesFinsupp A : ℕ →₀ ℝ`, with `⇑(singularValuesFinsupp A) = singularValues A` by `rfl` | `singularValuesFinsupp_eq_linearMap` |

Mathlib has `PiLp`, `lp`, Hölder's inequality for sums and the Hölder exponent classes, and no
Schatten or unitarily invariant norms.

## 2. Interfaces

**One gauge, every shape.** A unitarily invariant norm is given by a symmetric gauge function on
finitely supported sequences, applied to the singular values. One `Φ` therefore gives a norm on
`Matrix m n 𝕜` for all `m`, `n`, and statements can relate matrices of different shapes:
`Φ.matrixNorm (A * B) ≤ specNorm A * Φ.matrixNorm B`, Fan dominance between `A : Matrix m n 𝕜`
and `B : Matrix l p 𝕜`, invariance under a non-square factor with orthonormal columns. The
prototype's `UnitarilyInvariantNorm 𝕜 m n`, a seminorm on one shape, could not state these.

**A structure, not a class.** `SymmetricGauge` is a bundled structure, passed explicitly. A
matrix has many norms; none is canonical.

**Named norms are plain definitions with bridges.** `schattenNorm q`, `nuclearNorm`,
`kyFanNorm k`, `specNorm`, `frobNorm` are real-valued functions with their own lemmas and
positivity extensions. The gauge is the uniform interface: `lpGauge_matrixNorm` and
`kyFanGauge_matrixNorm` are simp lemmas that turn a gauge norm into the named one, so a theorem
proved for `Φ.matrixNorm` specialises by `simpa using h (lpGauge q)`.

**Fan dominance is stated with `kyFanNorm`**, `(∀ k, kyFanNorm k A ≤ kyFanNorm k B) →
Φ.matrixNorm A ≤ Φ.matrixNorm B`, not with a majorization predicate. For sequences the hypothesis
is the shape Lidskii's inequality produces:
`∀ S : Finset ℕ, ∑ i ∈ S, |x i| ≤ ∑ i ∈ Finset.range S.card, y i` with `y` non-increasing.

**A norm given on one shape** has no interface here. The representation of a unitarily
invariant norm on `Matrix m n 𝕜` by a gauge on all sequences (von Neumann's theorem, converse
direction) is not stated: it would need an extension of a gauge from `Fin N` to all finitely
supported sequences and has no consumer.

**Exponents are `ℝ≥0∞`.** One definition covers `q = ⊤`; real exponents are written
`schattenNorm (ENNReal.ofReal q)` or through the power-sum formula `schattenNorm_eq_sum_rpow`.
Hypotheses: none where the statement is true for all `q` (invariance, definiteness), `q ≠ 0` for
homogeneity and comparisons, an explicit `hq : 1 ≤ q` for the triangle inequality, Mathlib's
exponent classes for Hölder. Natural exponents have `ℕ`-power forms
(`schattenNorm_natCast_pow`, `schattenNorm_two_mul_natCast_pow`) so that the moment method never
meets `toReal` or `rpow`.

## 3. Statement shapes

```lean
noncomputable def nuclearNorm (A : Matrix m n 𝕜) : ℝ :=
  ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), singularValues A i
noncomputable def schattenNorm (q : ℝ≥0∞) (A : Matrix m n 𝕜) : ℝ :=
  ‖(WithLp.toLp q fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i :
    PiLp q fun _ : Fin (min (Fintype.card m) (Fintype.card n)) => ℝ)‖

theorem schattenNorm_eq_sum_rpow {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ⊤) (A : Matrix m n 𝕜) {N : ℕ}
    (hN : A.rank ≤ N) :
    schattenNorm q A = (∑ i ∈ Finset.range N, singularValues A i ^ q.toReal) ^ q.toReal⁻¹
theorem schattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n 𝕜) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B
theorem schattenNorm_anti {q r : ℝ≥0∞} (hq : q ≠ 0) (h : q ≤ r) (A : Matrix m n 𝕜) :
    schattenNorm r A ≤ schattenNorm q A
theorem schattenNorm_mul_le {q r s : ℝ≥0∞} [ENNReal.HolderTriple q r s] (hq : q ≠ 0) (hr : r ≠ 0)
    (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    schattenNorm s (A * B) ≤ schattenNorm q A * schattenNorm r B
theorem norm_trace_conjTranspose_mul_le_schattenNorm_mul {q r : ℝ≥0∞}
    [ENNReal.HolderConjugate q r] (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤ schattenNorm q A * schattenNorm r B
theorem isGreatest_frobInner_schattenNorm {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A : Matrix m n 𝕜) :
    IsGreatest ((fun B : Matrix m n 𝕜 => frobInner A B) '' {B | schattenNorm r B ≤ 1})
      (schattenNorm q A)
theorem nuclearNorm_mul_le_frobNorm_mul_frobNorm (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    nuclearNorm (A * B) ≤ frobNorm A * frobNorm B

structure SymmetricGauge extends Seminorm ℝ (ℕ →₀ ℝ) where
  eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0
  map_equivMapDomain' : ∀ (σ : Equiv.Perm ℕ) x, toFun (x.equivMapDomain σ) = toFun x
  map_abs' : ∀ x, toFun (x.mapRange abs abs_zero) = toFun x
instance : FunLike SymmetricGauge (ℕ →₀ ℝ) ℝ
instance : SeminormClass SymmetricGauge ℝ (ℕ →₀ ℝ)

theorem SymmetricGauge.le_of_forall_sum_le (Φ : SymmetricGauge) {x y : ℕ →₀ ℝ} (hy : Antitone y)
    (h : ∀ S : Finset ℕ, ∑ i ∈ S, |x i| ≤ ∑ i ∈ Finset.range S.card, y i) : Φ x ≤ Φ y

noncomputable def SymmetricGauge.matrixNorm (Φ : SymmetricGauge) (A : Matrix m n 𝕜) : ℝ :=
  Φ (singularValuesFinsupp A)
theorem SymmetricGauge.matrixNorm_add_le (Φ : SymmetricGauge) (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (A + B) ≤ Φ.matrixNorm A + Φ.matrixNorm B
theorem SymmetricGauge.matrixNorm_le_of_forall_kyFanNorm_le (Φ : SymmetricGauge)
    {A : Matrix m n 𝕜} {B : Matrix l p 𝕜} (h : ∀ k, kyFanNorm k A ≤ kyFanNorm k B) :
    Φ.matrixNorm A ≤ Φ.matrixNorm B
theorem SymmetricGauge.matrixNorm_mul_le_specNorm_mul (Φ : SymmetricGauge) (A : Matrix m p 𝕜)
    (B : Matrix p n 𝕜) : Φ.matrixNorm (A * B) ≤ specNorm A * Φ.matrixNorm B
theorem SymmetricGauge.matrixNorm_mul_left_of_hasOrthonormalCols (Φ : SymmetricGauge)
    [DecidableEq m] {Q : Matrix l m 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (Q * A) = Φ.matrixNorm A
theorem SymmetricGauge.apply_singularValuesFinsupp_sub_le (Φ : SymmetricGauge)
    (A B : Matrix m n 𝕜) :
    Φ (singularValuesFinsupp A - singularValuesFinsupp B) ≤ Φ.matrixNorm (A - B)
theorem SymmetricGauge.matrixNorm_sub_truncatedSVD_le_of_rank_le (Φ : SymmetricGauge)
    (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) :
    Φ.matrixNorm (A - truncatedSVD A k) ≤ Φ.matrixNorm (A - B)

noncomputable def lpGauge (q : ℝ≥0∞) (hq : 1 ≤ q) : SymmetricGauge
noncomputable def kyFanGauge (k : ℕ) (hk : k ≠ 0) : SymmetricGauge
theorem lpGauge_matrixNorm {q : ℝ≥0∞} (hq : 1 ≤ q) (A : Matrix m n 𝕜) :
    (lpGauge q hq).matrixNorm A = schattenNorm q A
theorem schattenNorm_two_mul_natCast_pow [DecidableEq n] {p : ℕ} (hp : p ≠ 0)
    (A : Matrix m n 𝕜) : schattenNorm (2 * p) A ^ (2 * p) = RCLike.re ((Aᴴ * A) ^ p).trace
theorem kyFanGauge_matrixNorm {k : ℕ} (hk : k ≠ 0) (A : Matrix m n 𝕜) :
    (kyFanGauge k hk).matrixNorm A = kyFanNorm k A
```

## 4. Consumers

| Item | Consumed by |
|---|---|
| `nuclearNorm`, its duality and the factorisation bound | trace estimation (`‖A‖_*` as the target for PSD `A`), nuclear-norm error bounds for Nyström, low-rank recovery |
| `schattenNorm q`, Hölder, monotonicity in `q` | matrix concentration (Schatten-`2p` moment method, noncommutative Khintchine), stochastic Lanczos quadrature error in Schatten norms, randomized SVD bounds in Schatten norms |
| `SymmetricGauge.matrixNorm` API | M5 `sin Θ` distances in any unitarily invariant norm; M6 Davis–Kahan and Wedin in any unitarily invariant norm; the low-rank layer's Eckart–Young–Mirsky |
| Fan dominance | transferring a bound proved for Ky Fan norms to every unitarily invariant norm |
| Mirsky | M6 singular value perturbation in any norm |
| `kyFanNorm` API | top-`k` energy in PCA and low-rank approximation statements |

## 5. Files

Under `NLAlib/Matrix/Norms/`:

1. `Nuclear.lean` (imports M3a `Lidskii`, M3 `LowRank`): Ky Fan norm API, `nuclearNorm`, duality
   with the spectral norm, the factorisation bound, Hermitian and positive semidefinite cases.
2. `Schatten.lean` (imports 1, Mathlib `PiLp`): the Schatten family.
3. `SchattenHolder.lean` (imports 2, M3a `Horn`): Hölder and duality.
4. `SymmetricGauge.lean` (imports M3a `DoublyStochastic`): the structure, its order theory, the
   `ℓ^q` and Ky Fan gauges.
5. `UnitarilyInvariant.lean` (imports 2, 4): `singularValuesFinsupp`, `matrixNorm`, Fan dominance,
   Mirsky, Eckart–Young–Mirsky, the bridges.

Independent for proving: 4 at any time; 3 and 5 after 2.

## 6. Material

Read: prototype `Matrix/Norms/{SymmetricGauge, InvariantNorm, InvariantNormRepresentation,
FanDominance, KyFanNorm, Nuclear*, Schatten*, RectangularDiagonal*}`,
`Matrix/Inequalities/{KyFanNorms, SingularValueMajorization, HornPowerSums}`.

Reused: the chain of arguments for the Schatten triangle inequality (through weak majorization and
`rpow` convexity), Hölder through Horn's product inequality and Weyl's lemma, the duality
attainment through an SVD.

Not reproduced: `schattenNormReal` (one definition with `ℝ≥0∞` exponents); `UnitarilyInvariantNorm`
as a structure on one shape, its `transpose` and `reindex`; `rectangularDiagonal` and
`prefixPermutation` (the representation of a one-shape norm by a gauge); the bundled seminorms
`nuclearSeminorm`, `kyFanSeminorm`, `schattenSeminorm`; `*_reindex` and `Fin` forms. The
nuclear norm as `tr √(Aᴴ A)` needs the matrix square root and moves to M10.

## 7. Decisions taken without approval

1. **The unitarily invariant interface is `SymmetricGauge` on `ℕ →₀ ℝ` with
   `Φ.matrixNorm A := Φ (singularValuesFinsupp A)`**, a structure and not a class.
2. **`singularValuesFinsupp` is a second accessor for singular values**, needed as the argument
   of a gauge. It is `singularValues` as a function, by `rfl`, and appears only in the gauge
   interface.
3. **`schattenNorm` takes `q : ℝ≥0∞` and is defined as a `PiLp` norm.** `q = 0` gives the rank.
4. **No interface for a unitarily invariant norm given on one shape**, and no representation
   theorem.
5. **Gauges are definite** (norms, not seminorms), so `kyFanGauge` takes `k ≠ 0`.
6. **No bundled `Seminorm` values** for the named norms.

## 8. Review (Fable, 2026-10-14) and what changed

The review confirmed the gauge on `ℕ →₀ ℝ`, `singularValuesFinsupp` as a cast (not a change of
`singularValues` itself, which every consumer indexes), `∀ Φ : SymmetricGauge` as the shape for
"every unitarily invariant norm", no normalisation field, and decisions 4 and 6. It checked the
degenerate cases of the skeleton (`q = 0`, `q = ⊤`, rank zero, empty index types, `k = 0`) and
found no false statement. Folded in:

1. `SymmetricGauge` extends Mathlib's `Seminorm ℝ (ℕ →₀ ℝ)` with `FunLike` and `SeminormClass`
   instances, in place of a raw function with `CoeFun`; the generic seminorm lemmas replace six
   hand-stated ones.
2. Natural-exponent bridges for the moment method: `schattenNorm_natCast_pow`,
   `schattenNorm_two_mul_natCast_pow`, the Hermitian form, `specNorm_pow_le_re_trace_pow`.
3. `1 ≤ q` is an explicit hypothesis, not a `Fact` instance, on the triangle inequality and on
   `lpGauge`.
4. The one-shape Fan dominance theorem was dropped: nothing in the library could be fed to it.
5. One-step bridges `lpGauge_top_matrixNorm`, `lpGauge_two_matrixNorm`, `lpGauge_one_matrixNorm`;
   the index forms `sum_abs_singularValues_sub_le_kyFanNorm_sub` and
   `sum_abs_eigenvalue_sub_le_kyFanNorm_sub` for consumers of Mirsky's theorem.
6. `schattenNorm_zero_left` renamed `schattenNorm_zero_eq_rank`.
