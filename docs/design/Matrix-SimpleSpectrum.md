# A complete list of simple spectral values

This note records the design after PR #96 merged.

A finite matrix pencil can supply one spectral value per index before it has
a diagonalization. Over an arbitrary field an injective list of that length
already supplies an eigenbasis and exhausts the spectrum. The empty list also
works in dimension zero. These statements in `Matrix/Spectral/SimpleSpectrum.lean`
use Mathlib's spectrum and basis directly.

```lean
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem exists_mulVec_eq_smul_of_injective
    (M : Matrix n n K) (ev : n → K) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum K M) :
    ∃ b : Module.Basis n K (n → K), ∀ i, M *ᵥ b i = ev i • b i

theorem spectrum_eq_range_of_injective_mem_spectrum
    (M : Matrix n n K) (ev : n → K) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum K M) : spectrum K M = Set.range ev
```

`TraceExponentialContour` uses the eigenbasis to compute a trace as a sum.
`ExteriorEigenvalueBranches` and `InversePencilBranches` use the set equality
to locate a root in a labelled branch. The proof composes Mathlib's
`Module.End.eigenvectors_linearIndependent'` with
`basisOfLinearIndependentOfCardEqFinrank'`.

In the opposite direction, a supplied unitary diagonalization gives real
spectral nodes even when the nodes repeat.

```lean
theorem mem_spectrum_of_eq_mul_diagonal_mul_conjTranspose
    {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] (ev : n → ℝ)
    (U : unitary (Matrix n n 𝕜)) {A : Matrix n n 𝕜}
    (hA : A = (U : Matrix n n 𝕜) * Matrix.diagonal (fun i => (ev i : 𝕜)) *
      (U : Matrix n n 𝕜)ᴴ) (i : n) : ev i ∈ spectrum ℝ A
```

`HermitianDerivative` uses this implication to specialize differentiability
on the spectrum to a node. `TraceExponentialApproximation` uses it to bound
a diagonal slope by the spectral endpoints. Mathlib supplies spectral invariance
under an algebra equivalence and the spectrum of a diagonal matrix. This note
records the interfaces already in use following PR #96.
