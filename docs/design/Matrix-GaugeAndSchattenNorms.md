# Symmetric gauges and Schatten norm inequalities

The three source cards are `unitarily-invariant-norm-def`, `ordered-schatten-trace-deficit`,
and `schatten-even-moment-smoothness` in the [matrix majorization subsection](https://research.chen.pw/NLAlib/#matrix-majorization).
Their statements use the existing `SymmetricGauge.matrixNorm` and `schattenNorm` on
finite matrices over `RCLike`. The [original formalization](https://github.com/tchen-research/NLAlib/tree/77514ce42a0e437d837797a063ac161f41022730)
guides the comparison of hypotheses, endpoint cases and constants.

The explorer uses `trace-power-superadditivity` for the positive trace-power inequality
applied to two PSD summands. Its application to an ordered pair gives
`ordered-schatten-trace-deficit`, which also covers the nuclear-norm equality at
exponent one. The two directions of the symmetric-gauge correspondence share
`unitarily-invariant-norm`.

## Representation of a fixed-shape norm

A matrix norm on one rectangular shape can be restricted to its thin diagonal.
The SVD transfers it back to the matrix when the norm is unchanged by left and
right unitary factors. The public `IsUnitarilyInvariant` predicate expresses this
condition on a supplied function. The norm axioms and definiteness come from a
Mathlib seminorm and its zero criterion. The matrix representation and converse
use the existing orthonormal-frame interface.

The library's symmetric gauges take finitely supported sequences of arbitrary length.
To extend a definite symmetric seminorm on `Fin d → ℝ` when `0 < d`, take the supremum
over restrictions to ordered selections of `d` coordinates. There are finitely many
values at each finitely supported input. Sign invariance makes deleting coordinates
a contraction, so the extension agrees on the original coordinates. In the empty
matrix shape the only input is zero and an existing gauge supplies the representation.

The restriction and frame argument live in `Norms/GaugeRepresentation`. The finite
extension lives in `Norms/SymmetricGauge` and relies on Mathlib’s bounded supremum
of seminorms. Existing cross-shape Fan dominance applies to a representing gauge.
Only values on the prescribed shape are specified by the representation theorem.

```lean
theorem IsUnitarilyInvariant.exists_forall_matrixNorm_eq {p : Seminorm 𝕜 (Matrix m n 𝕜)}
    (hp : IsUnitarilyInvariant (p : Matrix m n 𝕜 → ℝ)) (hdef : ∀ A, p A = 0 → A = 0) :
    ∃ Φ : SymmetricGauge, ∀ A : Matrix m n 𝕜, Φ.matrixNorm A = p A
```

## Ordered trace deficits

For positive semidefinite matrices with `B ≤ A`, the power of the Schatten norm of
`A - B` is bounded by the difference of the corresponding powers for every finite
real exponent at least one. At exponent one this becomes trace additivity. For McCarthy’s trace superadditivity, stack the two positive
square roots in the rows of a matrix. Trace Jensen applied to the two principal
blocks gives the sum of the individual trace powers. The opposite Gram matrix is
the sum of the two inputs, and the Gram matrices have the same positive spectrum.

The additive trace inequality belongs in `Functions/TracePowers`. It gives the
ordered estimate in `Norms/SchattenPowers` using the positive-matrix identity
`schattenNorm_rpow_eq_re_trace_rpow`. The equality at exponent one belongs with
the nuclear norm and its trace formula in `Norms/Nuclear`.

```lean
theorem Matrix.PosSemidef.re_trace_rpow_add_le {X Y : Matrix n n 𝕜}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {p : ℝ} (hp : 1 ≤ p) :
    RCLike.re (X ^ p).trace + RCLike.re (Y ^ p).trace ≤ RCLike.re ((X + Y) ^ p).trace

theorem Matrix.PosSemidef.schattenNorm_sub_rpow_le {A B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (h : B ≤ A) {p : ℝ} (hp : 1 ≤ p) :
    schattenNorm (ENNReal.ofReal p) (A - B) ^ p ≤
      schattenNorm (ENNReal.ofReal p) A ^ p - schattenNorm (ENNReal.ofReal p) B ^ p

theorem Matrix.PosSemidef.nuclearNorm_sub_of_le {A B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (h : B ≤ A) : nuclearNorm (A - B) = nuclearNorm A - nuclearNorm B
```

## Even-moment smoothness

For real or complex rectangular matrices, compare the even and odd parts of the
Gram powers of `A + B` and `A - B`. Matrix products are controlled by the existing
Schatten Hölder inequality. The scalar estimate for the average of the two even
powers supplies the coefficient `2 * r - 1` for each positive integer `r`. The
scalar inequality belongs with the other finite mean inequalities in ForMathlib.
Matrix moment calculations then use the established relation between Gram traces
and `schattenNorm`. Neither part needs a rank condition.

The binomial expansion cancels odd coefficients in the scalar sign average. The
upper bound for each remaining coefficient gives the scalar inequality for all
real inputs, including either sign. In `Norms/SchattenSmoothness`, the matrix
proof uses Hölder twice per Gram factor to bound the sum and difference of the two
partial products. The exponent in the conclusion is `r⁻¹ = 2/p` for `p = 2r`.
The result applies directly to rectangular matrices without doubling the dimension.

```lean
theorem Real.add_pow_add_sub_pow_le (a b : ℝ) (r : ℕ) :
    ((a + b) ^ (2 * r) + (a - b) ^ (2 * r)) / 2 ≤
      (a ^ 2 + (2 * (r : ℝ) - 1) * b ^ 2) ^ r

theorem schattenNorm_add_pow_add_schattenNorm_sub_pow_div_rpow_le {r : ℕ} (hr : 0 < r)
    (A B : Matrix m n 𝕜) :
    ((schattenNorm (2 * r) (A + B) ^ (2 * r) + schattenNorm (2 * r) (A - B) ^ (2 * r)) / 2) ^
      (r : ℝ)⁻¹ ≤ schattenNorm (2 * r) A ^ 2 + (2 * (r : ℝ) - 1) * schattenNorm (2 * r) B ^ 2
```

The fixed-shape norm representation is Bhatia’s Theorem IV.2.1 with arbitrary
rectangular dimensions over either scalar field. The deficit is Lemma 2.3 of
[Persson, Meyer and Musco](https://doi.org/10.1137/23M1619435). The smoothness
statement is the even-integer case of Theorem 8.2 in
[Tropp’s matrix analysis lectures](https://doi.org/10.7907/nwsv-df59).

## Fixed-shape invariance and even moments

Use `q : ℝ≥0∞` at the norm interface, as in `schattenNorm q A`. Finite real
powers enter through `ENNReal.ofReal`; even moment theorems quantify over the
positive natural half-exponent so both powers and their induction are natural.
The fixed-shape predicate belongs beside the other unitarily invariant norms.
Its witnesses are obtained from the existing left and right isometry identities:

```lean
isUnitarilyInvariant_schattenNorm (q : ℝ≥0∞) :
    IsUnitarilyInvariant (schattenNorm q : Matrix m n 𝕜 → ℝ)
isUnitarilyInvariant_specNorm : IsUnitarilyInvariant (specNorm : Matrix m n 𝕜 → ℝ)
isUnitarilyInvariant_frobNorm : IsUnitarilyInvariant (frobNorm : Matrix m n 𝕜 → ℝ)
```

The witnesses can be supplied to invariant frame transport or the gauge
representation. The identities with the spectral and Frobenius norms specialize
the Schatten witness at infinity and two. The sharp two-point bound in
`SchattenSmoothness` takes `0 < r` and matrices of the same rectangular shape.
For `p = 2*r` it bounds the sum of their sum and difference moments by
`(‖A‖ + ‖B‖)^p + (‖A‖ - ‖B‖)^p`, with each norm the same Schatten p-norm.
The uniform smoothness theorem uses that estimate directly.
