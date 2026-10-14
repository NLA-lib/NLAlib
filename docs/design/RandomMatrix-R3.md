# Design note: RandomMatrix stage R3, extreme singular values and spectral norms

Status: drafted 2026-10-14 for the orchestrator, under `docs/PORT_PROBABILITY.md` (§2 decided;
§5: conclusions in the Loewner form on the Gram matrix, separate lower and upper parameters).
Builds on P6 (`docs/design/Probability-P6.md`), R1, R4. Real throughout (D4: the Gaussian matrix
law is real this round). No question of the brief's §2 kind; one decision flagged in §7.

## 0. Scope and consumers

For `X` with law `gaussianMatrix m n` (`N = card m` rows, `n = card n` columns): Gordon's
expectation bounds, Gaussian concentration of every singular value (R1, proxy `1`), the deviation
tails, and the same conclusions as Loewner bounds on `Xᴴ X`; Chevet's inequality for `S X T`,
also with factors independent of `X`, and the range finder's spectral block bound. For a matrix
with independent isotropic sub-Gaussian rows: the net argument, constant named per D5.

| Item | Consumers (prototype files; next round) |
|---|---|
| Chevet `E ‖S G T‖ ≤ ‖S‖ ‖T‖_F + ‖S‖_F ‖T‖`, independent-factor form | LowRank (spectral range finder, 1 file); the block bound below |
| `E ‖S (V₂ᴴ G) pinv (V₁ᴴ G)‖ ≤ …` (Halko, Martinsson and Tropp, Theorem 10.6) | LowRank (spectral range finder, subspace iteration) |
| `E ‖G‖ ≤ √N + √n`, `√N - √n ≤ E σ_min` | the tails below |
| tails of `‖G‖` and `σ_min`; Loewner sandwich on `Gᴴ G` | next round: Gaussian subspace embedding (`IsSubspaceEmbedding` is that sandwich, §5 of the brief) |
| sub-Gaussian rows: sandwich, singular values, fixed-vector sub-exponential bound | next round: sub-Gaussian sketches (embedding, JL) |

Not here (no consumer): `E ‖S G T‖²`, small-ball bounds for `σ_min`, the bilinear-marginal net
bound without independence, complex Gaussian matrices.

## 1. Objects

| Concept | Spelling | Bridge / API |
|---|---|---|
| constant of the sub-Gaussian rows theorem | `noncomputable irreducible_def subgaussianRowsConstant : ℝ := 24`, new (D5) | `subgaussianRowsConstant_pos`, `subgaussianRowsConstant_le : subgaussianRowsConstant ≤ 24` |

`subgaussianRowsConstant` is the `C` of `√N ± C c (√n + t)` outside `2 e^{-t²}` (`c` the rows'
proxy), unspecified in the source ([Vershynin2018, Theorem 4.6.1], `C K²`). The proof (P1's
Bernstein literals `32 c²`, `4 c`; a `1/4`-net of `9^n` points; `C² / 256 ≥ max 1 (log 9)`)
reaches `16 √(log 9) ≈ 23.7`, rounded to `24`; the proof agent sets body and comparison to what it
reaches. Prototype: `32 e K² √(log 9)` and `1024 e² K⁴` (P*), two constants (§7 D2). Smaller is
better, so the API is an upper bound.

Used directly: R1, R4, P1, P3, P6, and the Matrix layer's `singularValues` (smallest at `k` with
`k + 1 = card n`), `specNorm`, `frobNorm`, `pinv`, nets (`exists_finite_isCover_sphere`,
`specNorm_le_div_of_isCover_of_isCover`, `Matrix.IsHermitian.specNorm_le_div_of_isCover`) and
Gram lemmas (`sq_singularValues_last_smul_one_le`, `specNorm_sq_le_iff_conjTranspose_mul_self_le`).

## 2. Interfaces

None new. Taken: `IsSubgaussianVector` and `IsIsotropic` of each row, with `iIndepFun` of the
rows beside them (D6: independence is a parameter beside an interface, not bundled). Concluded:
Mathlib's `HasSubgaussianMGF` (concentration), P1's `HasSubexponentialMGF` (fixed vector), and
the Loewner sandwich `a • 1 ≤ Xᴴ * X`, `Xᴴ * X ≤ b • 1` with separate `a`, `b`.

## 3. Statement shapes

`namespace NLAlib`; `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`,
`{m n a b : Type*} [Fintype m] [Fintype n] [Fintype a] [Fintype b]`, `{X : Ω → Matrix m n ℝ}`,
`hX : HasLaw X (gaussianMatrix m n) μ`. Abbreviations in this note only (the Lean statements
spell them out): `√N := √(Fintype.card m : ℝ)`, `√n := √(Fintype.card n : ℝ)`.

### 3.1 `RandomMatrix/Gaussian/SpectralNorm.lean`

```lean
theorem integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix (hX …) (S : Matrix a m ℝ)
    (T : Matrix n b ℝ) : Integrable (fun ω => specNorm (S * X ω * T)) μ
/-- **Chevet's inequality**: `E ‖S G T‖ ≤ ‖S‖ ‖T‖_F + ‖S‖_F ‖T‖`.
[Vershynin2018, Theorem 8.7.1]; [HalkoMartinssonTropp2011, Proposition 10.1].
Result: chevet-inequality -/
theorem integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix (hX …) (S : Matrix a m ℝ)
    (T : Matrix n b ℝ) :
    ∫ ω, specNorm (S * X ω * T) ∂μ ≤ specNorm S * frobNorm T + frobNorm S * specNorm T

variable {α : Type*} [MeasurableSpace α] {Y : Ω → α} {S : α → Matrix a m ℝ} {T : α → Matrix n b ℝ}

theorem integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix_of_indepFun (hY : AEMeasurable Y μ)
    (hX …) (hXY : IndepFun Y X μ) (hS : Measurable S) (hT : Measurable T)
    (hST : Integrable (fun ω => specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
      frobNorm (S (Y ω)) * specNorm (T (Y ω))) μ) :
    Integrable (fun ω => specNorm (S (Y ω) * X ω * T (Y ω))) μ
/-- Chevet's inequality with random factors independent of the Gaussian matrix. -/
theorem integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun (hY …) (hX …) (hXY …)
    (hS …) (hT …) (hST …) :
    ∫ ω, specNorm (S (Y ω) * X ω * T (Y ω)) ∂μ ≤
      ∫ ω, (specNorm (S (Y ω)) * frobNorm (T (Y ω)) + frobNorm (S (Y ω)) * specNorm (T (Y ω))) ∂μ
theorem integrable_specNorm_of_hasLaw_gaussianMatrix (hX …) : Integrable (fun ω => specNorm (X ω)) μ
/-- **Gordon's upper bound**: `E ‖G‖ ≤ √N + √n`. [Vershynin2018, Theorem 7.3.1]. -/
theorem integral_specNorm_le_of_hasLaw_gaussianMatrix (hX …) :
    ∫ ω, specNorm (X ω) ∂μ ≤ √(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)
```

`E ‖G‖ ≤ √N + √n` is Chevet with `S = 1`, `T = 1` (`specNorm_one_le`, `frobNorm_one_sq`).
Proof of Chevet (corrected in §8.1): on finite symmetric nets of the unit spheres,
`⟨u, S G T v⟩` has increments at most those of `‖Sᴴ u‖ ⟨g, T v⟩ + ‖T v‖ ⟨h, Sᴴ u⟩` (`g`, `h`
independent standard Gaussian);
P6's Sudakov–Fernique, `IsIsotropic.integral_norm_mulVec_le`, `specNorm_le_div_of_isCover_of_isCover`,
`ε → 0`. Independent factors: Chevet pointwise under the joint law, through `∫⁻` and Fubini as in
R2 (private); `hST` is needed only in the Bochner form, where a non-integrable right side would be
the junk `0` (D3).

### 3.2 `RandomMatrix/Gaussian/ExtremeSingularValues.lean`

```lean
theorem integrable_singularValues_of_hasLaw_gaussianMatrix (hX …) (k : ℕ) :
    Integrable (fun ω => singularValues (X ω) k) μ
/-- **Gordon's lower bound**: `√N - √n ≤ E σ_min(G)`. [Vershynin2018, Exercise 7.3.4];
[DavidsonSzarek2001, Theorem II.13]. Result: gordon -/
theorem le_integral_singularValues_of_hasLaw_gaussianMatrix (hX …) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) ≤ ∫ ω, singularValues (X ω) k ∂μ
/-- Every singular value of a Gaussian matrix is sub-Gaussian about its mean with proxy `1`. -/
theorem hasSubgaussianMGF_singularValues_sub_integral_of_hasLaw_gaussianMatrix (hX …) (k : ℕ) :
    HasSubgaussianMGF (fun ω => singularValues (X ω) k - ∫ ω', singularValues (X ω') k ∂μ) 1 μ
/-- `P(√N + √n + t ≤ ‖G‖) ≤ e^{-t²/2}`. [Vershynin2018, Corollary 7.3.3]. -/
theorem measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix (hX …) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t ≤ specNorm (X ω)} ≤
      Real.exp (-t ^ 2 / 2)
/-- `P(σ_min(G) ≤ √N - √n - t) ≤ e^{-t²/2}`. -/
theorem measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix (hX …) {k : ℕ}
    (hk : k + 1 = Fintype.card n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | singularValues (X ω) k ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t} ≤
      Real.exp (-t ^ 2 / 2)

variable [DecidableEq n]

/-- The upper Gram bound: `Gᴴ G ≤ (√N + √n + t)² • 1` outside probability `e^{-t²/2}`. -/
theorem measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix (hX …)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ¬ (X ω)ᴴ * X ω ≤
      (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ^ 2 • (1 : Matrix n n ℝ)} ≤
      Real.exp (-t ^ 2 / 2)
/-- The lower Gram bound: `(√N - √n - t)² • 1 ≤ Gᴴ G` outside probability `e^{-t²/2}`. -/
theorem measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix (hX …)
    {t : ℝ} (ht : 0 ≤ t) (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t) ^ 2 •
      (1 : Matrix n n ℝ) ≤ (X ω)ᴴ * X ω} ≤ Real.exp (-t ^ 2 / 2)
/-- **The Gaussian Gram sandwich** outside probability `2 e^{-t²/2}`, the shape of the next
round's subspace-embedding predicate. -/
theorem measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_hasLaw_gaussianMatrix
    (hX …) {t : ℝ} (ht : 0 ≤ t) (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) :
    μ.real {ω | ¬ ((√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t) ^ 2 • (1 : Matrix n n ℝ) ≤
      (X ω)ᴴ * X ω ∧ (X ω)ᴴ * X ω ≤
      (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ^ 2 • (1 : Matrix n n ℝ))} ≤
      2 * Real.exp (-t ^ 2 / 2)
```

Proofs. Lower bound, `card n ≤ card m`: on nets, `⟨v, G u⟩` against `⟨g, u⟩ + ⟨h, v⟩` in P6's
Gordon inequality (`‖v uᴴ - v' u'ᴴ‖_F² ≤ ‖u - u'‖² + ‖v - v'‖²`, equality for `u = u'`), P6's
`E ‖h_N‖ - E ‖g_n‖ ≥ √N - √n`, `ε → 0`; `card n > card m`: `σ_k = 0`
(`singularValues_of_card_rows_le`). Concentration: R1's Frobenius-Lipschitz theorem with `L = 1`
(`abs_singularValues_sub_le_frobNorm`). Tails: the expectation bounds and P1's tails. Gram forms:
`specNorm_sq_le_iff_…`; `sq_singularValues_last_smul_one_le`, `smul_one_le_smul_one`; union bound.

### 3.3 `RandomMatrix/Gaussian/BlockMoments.lean` (R4's file, + 3)

`{n k r s a : Type*}`, `{X : Ω → Matrix n k ℝ}`, frames `V₁ : Matrix n r ℝ`, `V₂ : Matrix n s ℝ`
with `hV₁ hV₂ h₁₂` as in R4's block bound, `hrk : Fintype.card r + 2 ≤ Fintype.card k`,
`S : Matrix a s ℝ`:

```lean
theorem integrable_specNorm_mul_mul_pinv_of_hasLaw_gaussianMatrix … :
    Integrable (fun ω => specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω))) μ
/-- **The range finder's spectral block bound**: `E ‖S Ω₂ Ω₁†‖ ≤ ‖S‖ E ‖Ω₁†‖_F + ‖S‖_F E ‖Ω₁†‖`
with R4's moments. [HalkoMartinssonTropp2011, proof of Theorem 10.6], there with `e √k / (k - r)`. -/
theorem integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix … :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ∂μ ≤
      specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
        frobNorm S * (Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
          √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2))
/-- The form of Halko, Martinsson and Tropp, proved from the above (R4 §7 Q1). -/
theorem integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix … :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ∂μ ≤
      specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
        frobNorm S * (Real.exp 1 * √(Fintype.card k : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r))
```

Proof: R1's `indepFun_conjTranspose_mul_…` (blocks independent), `hasLaw_const_mul_…` (`V₂ᴴ X`
Gaussian), §3.1's independent-factor Chevet with `Y := V₁ᴴ X`, `T := pinv`
(`measurable_pinv`), R4's `integral_frobNorm_pinv_le_…` and `integral_specNorm_pinv_le_…`.

### 3.4 `RandomMatrix/SubGaussian/ExtremeSingularValues.lean`

`[DecidableEq n] {c : ℝ≥0}`; the row hypotheses, written once here:
`(hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
(hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ)`; `w := subgaussianRowsConstant * c * (√n + t)`.

```lean
noncomputable irreducible_def subgaussianRowsConstant : ℝ := 24
theorem subgaussianRowsConstant_pos : 0 < subgaussianRowsConstant
theorem subgaussianRowsConstant_le : subgaussianRowsConstant ≤ 24
/-- For a unit `x`, `‖X x‖² - N` is sub-exponential with parameters `32 c² N`, `4 c`. -/
theorem hasSubexponentialMGF_norm_mulVec_sq_sub_of_isSubgaussianVector hind hsub hiso
    {x : n → ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    HasSubexponentialMGF (fun ω => ‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - Fintype.card m)
      (32 * c ^ 2 * Fintype.card m) (4 * c) μ
/-- **Independent isotropic sub-Gaussian rows** (Gram sandwich): outside probability `2 e^{-t²}`,
`(√N - w)² • 1 ≤ Xᴴ X ≤ (√N + w)² • 1`. [Vershynin2018, Theorem 4.6.1], with a named constant.
Result: subgaussian-matrix-norm -/
theorem measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_isSubgaussianVector
    hind hsub hiso {t : ℝ} (ht : 0 ≤ t) (hw : w ≤ √N) :
    μ.real {ω | ¬ ((√N - w) ^ 2 • (1 : Matrix n n ℝ) ≤ (X ω)ᴴ * X ω ∧
      (X ω)ᴴ * X ω ≤ (√N + w) ^ 2 • (1 : Matrix n n ℝ))} ≤ 2 * Real.exp (-t ^ 2)
theorem measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_isSubgaussianVector
    hind hsub hiso (ht : 0 ≤ t) (hw : w ≤ √N) :
    μ.real {ω | ¬ (√N - w) ^ 2 • (1 : Matrix n n ℝ) ≤ (X ω)ᴴ * X ω} ≤ 2 * Real.exp (-t ^ 2)
theorem measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_isSubgaussianVector
    hind hsub hiso (ht : 0 ≤ t) :
    μ.real {ω | ¬ (X ω)ᴴ * X ω ≤ (√N + w) ^ 2 • (1 : Matrix n n ℝ)} ≤ 2 * Real.exp (-t ^ 2)
theorem measureReal_singularValues_le_le_of_isSubgaussianVector [Nonempty m] hind hsub hiso
    {k : ℕ} (hk : k + 1 = Fintype.card n) (ht : 0 ≤ t) :
    μ.real {ω | singularValues (X ω) k ≤ √N - w} ≤ 2 * Real.exp (-t ^ 2)
theorem measureReal_specNorm_ge_le_of_isSubgaussianVector [Nonempty m] hind hsub hiso (ht : 0 ≤ t) :
    μ.real {ω | √N + w ≤ specNorm (X ω)} ≤ 2 * Real.exp (-t ^ 2)
```

The two-sided statement is primary (the net bounds `‖Xᴴ X - N 1‖`, both sides at once); the
one-sided forms are corollaries. The fixed-vector statement is public (the next round's
sub-Gaussian JL takes it; P1's literal constants, so no named constant). Proof: isotropy gives
`E ⟨X_i, x⟩² = 1`, then P1's `hasSubexponentialMGF_sq_sub_integral` and `sum_of_iIndepFun`, the
net (§1), and `‖Aᴴ A / N - 1‖ ≤ max δ δ² ⇒` singular values in `√N (1 ± δ)` (private). A Gaussian
matrix satisfies the hypotheses with `c = 1`, but §3.2 dominates there (`√N ± (√n + √2 t)` outside
`2 e^{-t²}`): the docstrings say so (D5 rule 3).

### 3.5 Degenerate cases

- **`n` empty** (no columns): no `k` with `k + 1 = 0`, so the `σ_min` statements are vacuous;
  `Xᴴ X` is `0 × 0` and every Loewner statement holds (the event is empty); `specNorm` is `0`.
- **`m` empty** (no rows), Gaussian: `specNorm = 0` and `√N = 0`; the upper tail's event is
  `{√n + t ≤ 0}`, empty unless `n` empty and `t = 0`, where the bound is `1`. Sub-Gaussian:
  `hsub`, `hiso` are vacuous, so `c` is unconstrained; with `c = 0` and `t > 0` the singular-value
  events `{σ ≤ 0}` and `{0 ≤ specNorm}` are everything and `2 e^{-t²} < 1`: false. Hence
  `[Nonempty m]` on those two. The Loewner forms need nothing: `hw` forces `w = 0` and the
  sandwich `0 ≤ 0 ≤ (√0 + 0)² • 1` holds. With `m`, `n` nonempty, isotropy and
  `HasSubgaussianMGF.integral_sq_le` give `1 ≤ c`, which the proof uses (so no `1 ≤ c`
  hypothesis; the prototype's `hK : 1 ≤ K` is redundant).
- **`n > N`**: `σ_k = 0` (padding) and `√N - √n < 0`: Gordon's lower bound and the `σ_min` tail
  hold trivially, and no tallness hypothesis is stated. The lower Gram forms are vacuous
  (`0 ≤ t ≤ √N - √n < 0` impossible).
- **`n = N`**: Gordon's lower bound is `0 ≤ E σ_min`; the lower Gram form forces `t = 0` and
  `0 • 1 ≤ Xᴴ X`, always true.
- **`t = 0`**: the tails are true (bound `1`, or `2`); `t < 0` is excluded (`ht`).
- **The Loewner lower base** `√N - √n - t` (resp. `√N - w`) must be nonnegative, or squaring
  makes `a` large and the statement false: hence `htn` (`hw`). The upper forms need nothing.
- **`c = 0`** with `m`, `n` nonempty contradicts isotropy: vacuous, not false.
- **Chevet**: empty `a`, `b`, `m` or `n` make `S X T = 0`; right side `≥ 0`. Block bound: `r`
  empty makes `pinv (V₁ᴴ X)` a `k × 0` matrix and the product `0`; `s` empty likewise.
- **Probability** is implied by `HasLaw` and by `iIndepFun` (also for an empty row set); no
  measurability hypothesis on events (`μ.real` is outer).

## 4. Consumers of the headline statements

§0. The next round proves `IsSubspaceEmbedding` from the Gram sandwiches after the `1/√N` scaling
and restriction to `U` (rows `Uᴴ X_i` stay isotropic and sub-Gaussian: `IsIsotropic.mulVec`,
`IsSubgaussianVector.mulVec`).

## 5. Files

1. `RandomMatrix/Gaussian/SpectralNorm.lean`: §3.1 (6); imports R1, P6's `GaussianComparison`,
   P0's `Isotropic`.
2. `RandomMatrix/Gaussian/ExtremeSingularValues.lean`: §3.2 (8); imports 1, R1's
   `Concentration`, P6, `ChiSquareMoments`.
3. `RandomMatrix/Gaussian/BlockMoments.lean`: + §3.3 (3); now also imports 1.
4. `RandomMatrix/SubGaussian/ExtremeSingularValues.lean`: §3.4 (8); imports P1, P3, the Matrix
   nets; independent of 1 to 3.

Bibliography: `DavidsonSzarek2001` (P6 adds it). Labels in `Vershynin2018` and HMT to be checked.

## 6. Material

Read: the prototype's `RandomMatrix/Gaussian/Spectral/{Gordon,Deviation,Chevet,
SpectralSecondMoment,SmallBall,SketchRank}.lean`, `RandomMatrix/SubGaussian/{SubGaussianRows,
SubGaussianJL}.lean`. Reused as proof material: the nets and comparison processes of `Gordon.lean`
(`gu_coeff_ineq`, `gl_matrix_side`), the net and Bernstein steps of `SubGaussianRows.lean`. Not
reproduced: measure forms and `_of_hasLaw` twins (D2); `Fin` types and `card (Fin n) - 1`
indices; the five-part conjunction `gordon_extreme_singular_values` (split; `E σ_min ≤ E ‖G‖` is
`singularValues_le_specNorm` under `integral_mono`); the success form
`one_sub_le_measure_sigmaMin_and_specNorm_…` (D3); `sigmaMin`; the raw row hypotheses with
`⟨K ^ 2, _⟩` and `u ⬝ᵥ u = 1` (D2, D6); `ENNReal.ofReal` bounds and strict events; the Gram tail
`measure_lt_specNorm_gram_sub_card_le_…` (proof-internal); `SpectralSecondMoment`, `SmallBall`
(no consumer); `SketchRank` (R1).

## 7. Open questions

### 7.1 Of the brief's §2 kind

None.

### 7.2 Decisions taken (recorded for review)

**D1. Loewner forms are the primary conclusions, beside the singular-value tails**, with separate
lower and upper statements and a sandwich by the union bound (the next round's predicate is the
conjunction). The lower forms carry the nonnegative-base hypothesis; they need no `[Nonempty m]`,
the singular-value forms of §3.4 do.

**D2. One named constant, Vershynin 2018's shape** `√N ± C c (√n + t)` outside `2 e^{-t²}`,
not the prototype's (Vershynin 2012, Theorem 5.39) `√N ± (C √n + t)` outside `2 e^{-c' t²}`: one
constant to invert, the same bound up to rescaling `t`. *Flagged:* the next round's sub-Gaussian
sample sizes will be written in this shape; another shape would coexist (D5 rule 3).

**D3. Real rows.** The rows theorem generalises to `𝕜` (`IsSubgaussianVector`, `IsIsotropic`
are over `𝕜`), but over `ℂ` the net has `9^{2n}` points and `|z|² - 1` has doubled
sub-exponential parameters, so one statement over `𝕜` would carry a constant worse for `ℝ`. The
complex form comes later with a constant depending on `Module.finrank ℝ 𝕜`. Chevet's and the Gram forms' shapes are field-generic; the Gaussian
statements wait for a complex Gaussian matrix law (R1, D4).

**D4. Chevet first, `E ‖G‖ ≤ √N + √n` as its corollary** (one Sudakov–Fernique argument).

**D5. Two block bounds** (sharp and HMT's), mirroring R4 §7 Q1: the HMT form is dominated and
proved from the other, kept because LowRank cites it; neither is `_sharp`.

**D6. No `1 ≤ c` or tallness hypothesis**: both are implied or unnecessary (§3.5).

## 8. Amendments from the review (2026-10-14)

The skeletons (`RandomMatrix/Gaussian/{SpectralNorm,ExtremeSingularValues}.lean`, the additions
to `RandomMatrix/Gaussian/BlockMoments.lean`, `RandomMatrix/SubGaussian/ExtremeSingularValues.lean`)
are the statements where they differ from §3.

1. **Chevet's comparison process (§3.1) corrected.** The process must carry the norms of the
   vectors, not of the factors: with `x = Sᴴu`, `y = T v`,
   `X_{uv} = ⟨u, S G T v⟩ = ⟨x, G y⟩` is compared with
   `Y_{uv} = ‖Sᴴu‖ ⟨g, T v⟩ + ‖T v‖ ⟨h, Sᴴu⟩` (`g`, `h` independent standard Gaussian). The
   inequality stated in §3.1 with `specNorm S`, `specNorm T` in place of `‖Sᴴu‖`, `‖T v‖` is
   false for non-unit `x`, `y`: for `x = e₁, x' = e₁/2, y = e₁, y' = e₁/2` and `‖S‖ = ‖T‖ = 1`,
   `E (X - X')² = ‖x yᵀ - x' y'ᵀ‖_F² = 9/16` but the increments of
   `⟨g, T v⟩ + ⟨h, Sᴴu⟩` are `‖y - y'‖² + ‖x - x'‖² = 1/2`. Increment check for the corrected
   process: `E (Y - Y')² - E (X - X')² ≥ (‖x‖ ‖y‖ - ‖x'‖ ‖y'‖)² ≥ 0`. The proof runs over finite
   symmetric nets; the supremum of `Y` is at most `‖S‖ ‖Tᴴ g‖ + ‖T‖ ‖S h‖`, whose mean is bounded by
   `IsIsotropic.integral_norm_mulVec_le` (P6 §3.3). The case of empty `m` or `n` (`S G T = 0`, no
   unit vectors) is split off before the net. No statement changes.
   In §3.2: `⟨g, u⟩ + ⟨h, v⟩` is the `X` side of P6's Gordon inequality and `⟨v, G u⟩` its `Y`
   side (`E min max X ≤ E min max Y`, `u` the outer index); see P6 §8.3.
2. **`subgaussianRowsConstant := 24` is verified, with a thin margin** (`16 √(log 9) ≈ 23.72` is
   needed). The proof must use `(√n + t)² ≥ n + t²` and a `1/4`-net exactly. Derivation, with
   `δ = C c (√n + t) / √N`: per row `⟨Xᵢ, x⟩² - 1` is sub-exponential with P1's `(32 c², 4 c)`,
   so `‖X x‖² - N` has `(32 c² N, 4 c)`; Bernstein at `s = εN` with `ε = max(δ, δ²)/2` bounds
   `P(|‖X x‖² - N| ≥ εN)` by `2 exp (-N min(ε², ε) / (64 c²))`, using `1 ≤ c` (isotropy and
   `HasSubgaussianMGF.integral_sq_le`; with rows and columns present) to compare the two
   Bernstein regimes; `min(ε², ε) ≥ δ²/4`, so the exponent is at least
   `C² (√n + t)² / 256 ≥ C² (n + t²) / 256`. The `1/4`-net of `9ⁿ` points loses a factor `2` in
   `‖Xᴴ X / N - 1‖ ≤ 2 max_x |‖X x‖² / N - 1| ≤ max(δ, δ²)`, and the union bound needs
   `C² / 256 ≥ max 1 (log 9) = log 9`. Then `‖Xᴴ X / N - 1‖ ≤ max(δ, δ²)` puts the singular values
   in `√N (1 ± δ) = √N ± w`. The constant's docstring records the margin.
3. **Corollary 7.3.3 is one-sided here.** The docstrings of the Gaussian tails and one-sided Gram
   bounds say so: the source's two-sided form has the factor `2`, which only the sandwich keeps.
4. (P6's: no bare `∃ C`; see P6 §8.1.)
5. (P6's: §7.1 Q1 of P6 decided; `HasGaussianLaw` of the finite family.)
6. **Names.** The module docstring of `RandomMatrix/SubGaussian/ExtremeSingularValues.lean` says
   that `_of_isSubgaussianVector` stands for the three row hypotheses `hind`, `hsub`, `hiso`. The
   dominated spectral block bound keeps the name
   `integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`, for
   consistency with R4's `integral_specNorm_pinv_le_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`;
   its docstring cites R4 §7 Q1.
7. **A public tail for `specNorm (S * X * T)`** in §3.1, for the next round's probabilistic range
   finder (R1's Frobenius-Lipschitz concentration with `L = ‖S‖ ‖T‖`, then Chevet):
   ```lean
   theorem measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix
       (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) {t : ℝ}
       (ht : 0 ≤ t) :
       μ.real {ω | specNorm S * frobNorm T + frobNorm S * specNorm T + t ≤
         specNorm (S * X ω * T)} ≤ Real.exp (-t ^ 2 / (2 * (specNorm S * specNorm T) ^ 2))
   ```
   (`S = 0` or `T = 0`: the bound is `exp 0 = 1`). §5 file 1 now holds 7 statements.
8. **Bibliography**: `DavidsonSzarek2001` is in `docs/references.bib` (with `Gordon1985`,
   `Kahane1986`; P6 §8.4).

Skeleton notes. Result ids: `chevet-inequality`; `gaussian-matrix-extreme-singular-values` on
both `E ‖G‖ ≤ √N + √n` and `√N - √n ≤ E σ_min(G)` (§3.2 had `gordon`; [DavidsonSzarek2001,
Theorem II.13] states the two together); `subgaussian-matrix-norm`. The two Gram-sandwich names
are longer than 92 characters, so `theorem` and the name are on separate lines (the 100-character
limit). No statement of §3 was changed in meaning.
