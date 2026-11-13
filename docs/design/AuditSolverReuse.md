# Solver interfaces and shared proof lemmas: audit correction

2026-11-04. This amends the linear-system lower-bound and iterative-sketching designs.
No new algorithm, hypothesis structure, or target is introduced.

## Right-hand side and success

The query lower bounds fix `b : n → ℝ` and `hb : b ≠ 0` before the seeded
algorithm. The algorithm may therefore depend on this known input, while its seed law
is independent of the unknown matrix. Success quantifies over admissible matrices only:

```lean
{b : n → ℝ} (hb : b ≠ 0)
{alg : S → QueryAlgorithm (n → ℝ) (n → ℝ) q (n → ℝ)}
(halg : QueryAlgorithm.IsMeasurableFamily alg) (ρ : Measure S)
[IsProbabilityMeasure ρ]
(hsucc : ∀ A : Matrix n n ℝ, A.IsHermitian →
  spectrum ℝ A ⊆ Set.Icc (-κ) (-1) ∪ Set.Icc 1 κ →
  2 / 3 ≤ ρ.real {s | ‖WithLp.toLp 2 (b - A *ᵥ (alg s).run A.mulVec)‖ ≤
    ε * ‖WithLp.toLp 2 b‖})
```

The hidden-rotation theorem has the same fixed right-hand side and quantifies only
over orthogonal rotations. The proof reuses the existing worst-case theorem, which
already holds for every fixed nonzero right-hand side. The constants, spectral scope,
and dimension requirement are unchanged. The three changed signatures are recorded
in the rename map. Consumers with a solver family indexed by `b` specialize that family
to the given `b` before applying the theorem.

## Iterative sketching

The existing theorem bounds the energy error by a geometric expression for all positive
steps. This is an error-propagation bound, not convergence unless its factor is below one.
The documentation explicitly distinguishes these cases and the stable-step sufficient
condition. The added corollary is:

```lean
theorem IsSubspaceEmbedding.tendsto_norm_mulVec_sub_iterativeSketching_sq
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hA : Function.Injective A.mulVec)
    {ω : ℝ} (hω : 0 < ω) (hr : max |1 - ω / b| |1 - ω / a| < 1)
    (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) :
    Filter.Tendsto (fun q : ℕ =>
      ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S ω y x₀ q))‖ ^ 2)
      Filter.atTop (nhds 0)
```

Here `𝕜` is `RCLike`, and all three matrix index types are arbitrary finite types.
It reuses Mathlib's geometric-series limit and `squeeze_zero`; no new convergence theory
is introduced. Downstream convergence proofs can consume the limit directly.

## Reuse and placement

- `ForMathlib/Analysis/InnerProductSpace/PiL2.lean`: coordinate forms of `norm_add_le`
  and `norm_sub_le`, over arbitrary finite coordinates and `RCLike`.
  These replace the independent private copies in CGRun, CGRunModel, and LocalErrors.
  Scaling uses `WithLp.toLp_smul`, `norm_smul`, and `Real.norm_eq_abs` directly.
  Existing `EuclideanSpace.abs_dotProduct_le_norm` and
  `EuclideanSpace.norm_toLp_sq_eq_dotProduct_self` replace the other four duplicate helpers.
  No new norm or inner-product object is introduced.
- `ForMathlib/Algebra/Polynomial/Expand.lean`: the squared-norm bound for the even part
  `Polynomial.contract 2`. It follows the existing evaluation identity here and is used
  by both TwoInterval and WorstCase. Mathlib searched: no matching bound.
- LanczosFunctions and SchurHorn use Mathlib `PiLp.norm_single` directly; the private
  unit-coordinate wrappers are deleted. WorstCase uses `EuclideanSpace.norm_sq_eq` directly
  instead of its private copy.
- EarlyTruncation and CGTridiagonal retain proof-local lemmas, with conclusion-based names
  and powers after their arguments. No private declaration receives explorer metadata.

All additions use existing Mathlib vocabulary and are upstream candidates in their
existing ForMathlib homes. There is no new deviation or vocabulary row. Sources and
mathematical statements otherwise remain as documented in their owning modules.


## Interval bounds for residual polynomials

CG, MINRES, PCG and preconditioned MINRES use the same normalized polynomial on a positive
spectral interval. The Polynomial layer should expose the empty-outlier specialization with its
degree, value at zero and uniform bound together. Each solver can then apply its own residual
estimate directly. The specialization keeps the existing conventions for a singleton interval,
a reversed interval and degree zero.


The residual minimax value takes the infimum of feasible nonnegative uniform bounds. The
constant polynomial one makes this set nonempty on any domain. Its order API gives upper bounds
from one feasible polynomial and lower bounds from all feasible polynomials. CG and MINRES
then use these two statements without unfolding real suprema. This agrees with the usual
supremum norm on finite spectra and avoids the real supremum convention on unbounded sets.
