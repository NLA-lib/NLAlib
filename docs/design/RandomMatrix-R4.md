# Design note: RandomMatrix stage R4, inverse moments of Gaussian matrices

Status: written 2026-10-14 by the orchestrator. No question of the brief's §2 kind.

## 0. Scope and consumers

The moments of the pseudoinverse of a wide standard Gaussian matrix `G : r × k` (`r < k`), which
the randomized range finder's error bounds consume (Halko, Martinsson and Tropp 2011,
Propositions 10.1 to 10.4 and the proof of Theorem 10.5), with the negative moments of `χ²` that
they rest on.

| Item | Consumers (prototype files) |
|---|---|
| `E (G Gᴴ)⁻¹ = (k - r - 1)⁻¹ • 1` | LowRank (Nyström, range finder) |
| `E ‖pinv G‖_F² = r / (k - r - 1)` | LowRank (3 files: the range finder, randomized SVD, Nyström) |
| `E ‖pinv G‖ ≤ e √((k + r - 1)/2) / (k - r)`, and the source's `e √k / (k - r)` as its corollary | LowRank (spectral-norm bounds; 1 file) |
| the block bound `E ‖S Ω₂ (pinv Ω₁)‖_F² = ‖S‖_F² r / (k - r - 1)` for orthogonal blocks `Ω₁ = V₁ᴴ Ω`, `Ω₂ = V₂ᴴ Ω` | LowRank (3 files: the range finder's main step) |
| negative moments of `χ²` | the above |

Not here (no consumer outside the layer, inventory §5): `E ‖pinv G‖_F⁴`, the tails of `‖pinv G‖`
and `‖pinv G‖_F²`, the `λ_min (G Gᴴ)` tail and the hard edge, Wishart densities (D9). Range
frames (`gaussianRangeFrame`, an orthonormal basis of `range (A G)` chosen measurably) are the
next round's, with the range finder.

## 1. Objects

`gaussianMatrix` (R1), the Matrix layer's `pinv` (`pinv_eq_conjTranspose_mul_inv`: for full row
rank, `pinv G = Gᴴ (G Gᴴ)⁻¹`), `frobNorm`, `specNorm`, matrix integrals under
`Matrix.Norms.L2Operator` (P0). No new object.

## 2. Interfaces

None.

## 3. Statement shapes

`namespace NLAlib`; `{r k : Type*} [Fintype r] [Fintype k] [DecidableEq r] [DecidableEq k]`,
`{X : Ω → Matrix r k ℝ}`, `hX : HasLaw X (gaussianMatrix r k) μ`. Dimension hypotheses on the
cardinals, written `Fintype.card r + 2 ≤ Fintype.card k` (no `Fin`).

### 3.1 `Probability/Distributions/ChiSquareInverse.lean`

```lean
/-- Negative moments of `χ²_d`: `E ‖X‖^{-2q} = Γ(d/2 - q) / (2^q Γ(d/2))` for `0 ≤ q < d/2`. -/
theorem integral_rpow_neg_norm_sq_of_hasLaw_gaussianVector {n : Type*} [Fintype n]
    {X : Ω → n → ℝ} (hX : HasLaw X (gaussianVector n) μ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < Fintype.card n / 2) :
    ∫ ω, (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ (-q) ∂μ =
      Real.Gamma (Fintype.card n / 2 - q) / (2 ^ q * Real.Gamma (Fintype.card n / 2))
theorem integrable_rpow_neg_norm_sq_of_hasLaw_gaussianVector … (hq : q < Fintype.card n / 2) :
    Integrable (fun ω => (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ (-q)) μ
/-- `E 1 / χ²_d = 1 / (d - 2)` for `d ≥ 3`. -/
theorem integral_inv_norm_sq_of_hasLaw_gaussianVector … (hn : 3 ≤ Fintype.card n) :
    ∫ ω, (‖WithLp.toLp 2 (X ω)‖ ^ 2)⁻¹ ∂μ = 1 / (Fintype.card n - 2)
```

At `X ω = 0` (probability zero) `0 ^ (-q)` is Lean's junk; the integral is unaffected. `q < d/2`
is the integrability threshold, so the hypothesis is sharp.

### 3.2 `RandomMatrix/Gaussian/InverseMoments.lean`

```lean
/-- `E (G Gᴴ)⁻¹ = (k - r - 1)⁻¹ • 1` for a standard Gaussian `G : r × k` with `r + 2 ≤ k`. -/
theorem integral_inv_mul_conjTranspose_of_hasLaw_gaussianMatrix
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, (X ω * (X ω)ᴴ)⁻¹ ∂μ = ((Fintype.card k - Fintype.card r - 1 : ℝ))⁻¹ • 1
theorem integrable_inv_mul_conjTranspose_of_hasLaw_gaussianMatrix (hrk …) :
    Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹) μ
/-- **`E ‖G†‖_F² = r / (k - r - 1)`** (Halko, Martinsson and Tropp, Proposition 10.2). -/
theorem integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix (hrk …) :
    ∫ ω, frobNorm (pinv (X ω)) ^ 2 ∂μ = Fintype.card r / (Fintype.card k - Fintype.card r - 1)
theorem integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix (hrk …) :
    Integrable (fun ω => frobNorm (pinv (X ω)) ^ 2) μ
/-- `E ‖G†‖ ≤ e √((k + r - 1)/2) / (k - r)` for `1 ≤ r < k`. -/
theorem integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix (hr : 0 < Fintype.card r)
    (hrk : Fintype.card r < Fintype.card k) :
    ∫ ω, specNorm (pinv (X ω)) ∂μ ≤
      Real.exp 1 / (Fintype.card k - Fintype.card r) *
        √((Fintype.card k + Fintype.card r - 1) / 2)
/-- The form of Halko, Martinsson and Tropp (Proposition 10.2), `E ‖G†‖ ≤ e √k / (k - r)`,
weaker in every regime and proved from `integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix`. -/
theorem integral_specNorm_pinv_le_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix (hr …) (hrk …) :
    ∫ ω, specNorm (pinv (X ω)) ∂μ ≤
      Real.exp 1 * √(Fintype.card k) / (Fintype.card k - Fintype.card r)
theorem integrable_specNorm_pinv_of_hasLaw_gaussianMatrix (hrk : Fintype.card r < Fintype.card k) :
    Integrable (fun ω => specNorm (pinv (X ω))) μ
```

### 3.3 `RandomMatrix/Gaussian/BlockMoments.lean`

For `Ω : Ω' → Matrix n k ℝ` with law `gaussianMatrix n k`, frames `V₁ : Matrix n r ℝ`,
`V₂ : Matrix n s ℝ` with `HasOrthonormalCols`, `V₁ᴴ V₂ = 0`, and a fixed `S : Matrix a s ℝ`:

```lean
/-- **The range finder's block bound** (Halko, Martinsson and Tropp, proof of Theorem 10.5):
`E ‖S (V₂ᴴ Ω) pinv (V₁ᴴ Ω)‖_F² = ‖S‖_F² r / (k - r - 1)`. -/
theorem integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix (hΩ …) (hV₁ …) (hV₂ …)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, frobNorm (S * (V₂ᴴ * Ω ω) * pinv (V₁ᴴ * Ω ω)) ^ 2 ∂μ =
      frobNorm S ^ 2 * Fintype.card r / (Fintype.card k - Fintype.card r - 1)
theorem integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix … :
    Integrable (fun ω => frobNorm (S * (V₂ᴴ * Ω ω) * pinv (V₁ᴴ * Ω ω)) ^ 2) μ
```

Proof: R1's block independence and laws, R2's independent second moment with `T := pinv`, and
§3.2.

## 4. Consumers of the headline statements

§0's table.

## 5. Files

1. `Probability/Distributions/ChiSquareInverse.lean`: §3.1 (3).
2. `RandomMatrix/Gaussian/InverseMoments.lean`: §3.2 (7); imports 1, R1.
3. `RandomMatrix/Gaussian/BlockMoments.lean`: §3.3 (2); imports 2, R2.

## 6. Material

The prototype's `RandomMatrix/Gaussian/InverseMoments/{Mean,DiagonalLaw,OffDiagonal,SchurComplement,
Probe,SpectralProbe,FrobeniusMoments}.lean`, `Probability/ChiSquare/ChiSquare.lean` (negative
moments), `RandomMatrix/Gaussian/Moments/Conditioning.lean` (the block bound). Route for the mean:
by rotation invariance the diagonal entries of `(G Gᴴ)⁻¹` are `1 / χ²_{k-r+1}` (Schur complement:
the distance of a row to the span of the others), off-diagonal means vanish by sign symmetry;
`E ‖pinv G‖_F² = tr E (G Gᴴ)⁻¹`. Spectral bound: probes `u ⬝ (G Gᴴ)⁻¹ u` have the law of
`1/χ²_{k-r+1}`, moments up to `(k - r)/2`, and the operator norm by a net-free trace argument
(prototype `SpectralProbe`). Not reproduced: `pinvR`, `pinvL` (the Matrix layer's `pinv`), `frobSq`,
the hard edge and Wishart (D9), tails without a consumer, `Fin` index types, `_of_hasLaw` twins.

## 7. Open questions (orchestrator decisions, recorded for review)

**Q1. Two bounds for `E ‖G†‖`.** The prototype's `_sharp` bound
`e √((k + r - 1)/2) / (k - r)` is at most the source's `e √k / (k - r)` whenever `r ≤ k + 1`, so the
source's form is dominated (D5 rule 5): it is proved from the first and kept because LowRank cites
it, under a name that spells its right side; neither is named `_sharp`.

## 8. Amendments from the review (2026-10-14)

The skeletons (`Probability/Distributions/ChiSquareMoments.lean`,
`RandomMatrix/Gaussian/{InverseMoments,BlockMoments}.lean`) are the statements where they differ
from §3.
1. Tails first (CONTRIBUTING §5.2): the range finder's tail theorems (Halko, Martinsson and Tropp
   10.7, 10.8) consume the higher moments, so R4 states the general spectral moments
   `E ‖G†‖^q ≤ (e √((k + r - 1)/2) / (k - r))^q` for `0 < q ≤ k - r` (with `E ‖G†‖` as `q = 1`, and
   the source's `e √k / (k - r)` as a corollary) and the Frobenius fourth moment
   (`r + 4 ≤ k`). The constant `√((k + r - 1)/2)` has no source; the docstring says it is what the
   probe proof reaches. The extension to `p ≥ 1` (HMT state `p ≥ 2`) is recorded in the docstring.
2. χ²: the general real moments `E (‖X‖²)^s = 2^s Γ(d/2 + s)/Γ(d/2)` for `s > -d/2` (file renamed
   `ChiSquareMoments.lean`), with `E 1/χ²_d = 1/(d - 2)` as the case used.
3. `E ‖G†‖_F ≤ √(r/(k - r - 1))` (Jensen) with its integrability companion, for the spectral block
   bound (R3).
4. Names: `integral_mul_conjTranspose_inv_…` (the inverse of `X Xᴴ`), `integral_norm_sq_inv_…`,
   `integral_norm_sq_rpow_…`; `hr : 0 < card r` dropped (`r = 0` gives `0 = 0`); instances per
   statement; casts written `(Fintype.card r : ℝ)`; the block file keeps `X` for the matrix.
5. Junk values: `(G Gᴴ)⁻¹` is `0` off the a.s. full-rank set and `pinv` is total; the integrals are
   unaffected (module docstrings).
6. The spectral block bound (HMT Theorem 10.6: `E ‖S G₂ G₁†‖ ≤ ‖S‖ √(r/(k-r-1)) + ‖S‖_F e√k/(k-r)`)
   needs Chevet with independent factors and is R3's.
