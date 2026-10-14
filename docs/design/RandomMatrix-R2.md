# Design note: RandomMatrix stage R2, moments of Gaussian sketches

Status: written 2026-10-14 by the orchestrator. No question of the brief's §2 kind.

## 0. Scope and consumers

Second moments of `S G T` for a standard Gaussian matrix `G` and fixed `S`, `T`, and the same
with `S`, `T` random but independent of `G` (the conditioning step every randomized range-finder
bound uses).

| Item | Consumers (prototype files) |
|---|---|
| `E ‖S G T‖_F² = ‖S‖_F² ‖T‖_F²` (Halko, Martinsson and Tropp, Proposition 10.1) | LowRank (range finder, randomized SVD, Nyström), Estimation |
| the same with `(S, T)` independent of `G` | LowRank (`integral_frobSq_mul_gaussian_mul_of_indepFun`: 3 files, through R4's block bound) |

Not here (no consumer outside its own layer, inventory §5): the fourth moment of `‖S G T‖_F`,
approximate matrix multiplication by a Gaussian sketch, the fourth-moment sandwich. They are
standard and can join a later stage with their consumer. `E ‖S G T‖` (spectral) is R3 (Gordon,
Chevet).

## 1. Objects

`gaussianMatrix` (R1), `frobNorm` (Matrix layer), Mathlib's `IndepFun`. No new object.

## 2. Interfaces

None. The second-moment identity uses only isotropy of the entries (`E G_ab G_cd = δ_ac δ_bd`),
so it is stated for a Gaussian matrix and proved from P0's `IsIsotropic` of `Function.uncurry G`
(R1 §8.2); a sketch with isotropic entries (Rademacher) gets the same identity from the same
lemma, stated once for `IsIsotropic`.

## 3. Statement shapes

`namespace NLAlib`; variables as in R1, `{a b : Type*} [Fintype a] [Fintype b]`.

### `RandomMatrix/Gaussian/Moments.lean`

```lean
/-- The second moment of a sketch with isotropic entries: if `Function.uncurry X` is isotropic,
`E ‖S X T‖_F² = ‖S‖_F² ‖T‖_F²`. -/
theorem integral_frobNorm_mul_mul_sq_of_isIsotropic [DecidableEq m] [DecidableEq n]
    (hX : IsIsotropic (fun ω => Function.uncurry (X ω)) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, frobNorm (S * X ω * T) ^ 2 ∂μ = frobNorm S ^ 2 * frobNorm T ^ 2
theorem integrable_frobNorm_mul_mul_sq_of_isIsotropic … :
    Integrable (fun ω => frobNorm (S * X ω * T) ^ 2) μ
/-- **The second moment of a Gaussian sketch** (Halko, Martinsson and Tropp 2011,
Proposition 10.1). -/
theorem integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, frobNorm (S * X ω * T) ^ 2 ∂μ = frobNorm S ^ 2 * frobNorm T ^ 2
/-- The second moment with random factors independent of the Gaussian matrix:
`E ‖S(Y) X T(Y)‖_F² = E [‖S(Y)‖_F² ‖T(Y)‖_F²]` for `Y` independent of `X`. -/
theorem integral_frobNorm_mul_mul_sq_of_indepFun {α : Type*} [MeasurableSpace α] {Y : Ω → α}
    (hY : AEMeasurable Y μ) (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ)
    {S : α → Matrix a m ℝ} {T : α → Matrix n b ℝ} (hS : Measurable S) (hT : Measurable T) :
    ∫ ω, frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2 ∂μ =
      ∫ ω, frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2 ∂μ
```

Degenerate cases: empty index types give `0 = 0`. The independent form needs no integrability:
both sides are integrals of nonnegative functions and the identity holds in `ℝ≥0∞` (the proof
goes through `lintegral` and Fubini on the joint law, then back; if the right side is not
integrable both sides are junk `0`, and the identity still holds because the left side is
integrable exactly when the right side is: the docstring says so). The proof agent states the
`∫⁻` form as a public lemma if it is the natural intermediate.

## 4. Files

`RandomMatrix/Gaussian/Moments.lean` (4 statements); imports R1 and P0's `Isotropic.lean`.

## 5. Material

The prototype's `RandomMatrix/Gaussian/Moments/{SecondMoment,Conditioning}.lean`. Not
reproduced: `frobSq` (the Matrix layer writes `frobNorm A ^ 2`), measure-form twins,
`integrable_const_mul_gaussianMatrix_entry_mul` and the entrywise moment lemmas (P2 and P0 through
the `uncurry` law), `Fin` index types.
