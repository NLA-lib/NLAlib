# Capacity, scaling and rank of Kraus maps

A finite family of complex square matrices defines the positive map
T(X) = ∑ᵢ Aᵢ X Aᵢᴴ. Operator scaling needs both the infimum of the determinant
of T(X) for positive definite X with det X = 1 and certificates which remain
valid when the infimum is zero or unattained. Use Mathlib determinants, Loewner
order, Kronecker products and the library's squared Frobenius norm.

The main statements give the multiplier ‖det B‖² ‖det C‖² under an invertible
input/output congruence; for families of orders n and m the tensor capacity is
cap(T)^m cap(S)^n. For a unital or trace-preserving tuple with squared imbalance
at most ε ≤ 1/(n+1), rank cannot decrease on PSD inputs and capacity lies
between (1-√(nε))^n and 1. Conversely capacity at least exp(-δ), 0 ≤ δ ≤ 1/6,
bounds the squared imbalance by 6δ. No attainment by a chosen optimizer is assumed.

The determinant normalization and determinant/trace variational formulas belong
with matrix inequalities. The scalar convexity and weighted matching arguments
use the pinned Mathlib Birkhoff and Hall APIs. The remaining matrix proofs are
organized into the capacity definition and transformation, the near-balanced
certificates, and tensor multiplicativity. The real-linear map on complex
matrices is used to match the source's optimization domain. The two atlas cards
cite Garg, Gurvits, Oliveira and Wigderson, *Operator scaling: theory and
applications*, Definition 2.6, Proposition 2.7, Theorems 2.12 and 3.11.

## Public statements and provenance

The scaling and tensor laws appear as `operatorCapacity_congruence_scaling` and
`operatorCapacity_krausMap_kronecker`. The rank and two capacity bounds are available
separately for each normalization. The two converse estimates bound the sum of the squared
Frobenius defects even in the presence of an exactly normalized marginal.
`NLAlib.determinantTraceObjectiveSet` states the trace variational formula over
real or complex matrices. The Hall argument and the scalar entropy inequality use Mathlib
finite sums and positive real inputs, respectively. The support-count argument also works
over linearly ordered fields. The original proofs were adapted from
[atlas commit 77514ce](https://github.com/tchen-research/NLAlib/tree/77514ce42a0e437d837797a063ac161f41022730).
