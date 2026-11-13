# Numerical mathematics independent of program execution

The numerical analysis and tape laws used by Ops depend on scalar functions, matrix maps,
and probability measures. They do not depend on a program evaluator. This separation moves
the existing mathematics out of mixed execution modules and makes that fact visible in imports.

## Objects and interfaces

No mathematical object or hypothesis interface is introduced. Existing `RelErr`, `AbsRelErr`,
binary representability and quantization, `FloatMachine`, matrix error contracts, and sample
laws retain their definitions and theorem statements. Mathlib's `Float.Model.Format`, matrices,
`HasLaw`, and independent sequences remain the underlying objects. Existing mathematical names
are preserved during relocation; no compatibility aliases or forwarding modules are added.

The execution adapters `ScalarSem`, old `Interp`, old buffer stores and old access models stay
in legacy modules until their owners retire those modules. They import the separated mathematics,
never the reverse. Ops keeps its existing independent machine and counted evaluator.

## Files and consumers

* `Matrix/FinitePrecision/Rounding`: accumulated and relative rounding errors, moved intact.
* `Matrix/FinitePrecision/Underflow`: mixed absolute-relative errors, excluding old semantic adapters.
* `Matrix/FinitePrecision/Float`: finite binary word representation and decoding, excluding
  `ScalarSem` definitions and their execution theorems.
* `Matrix/FinitePrecision/BinaryFloat`: the mathematical quantizer, moved intact.
* `Matrix/FinitePrecision/ResidualGap` and `VectorErrors`: pure update-defect and vector-error
  results, preserving their existing matrix and mixed-error hypotheses.
* `Matrix/FinitePrecision/Machine`, `EntrywiseRounding`, and Ops arithmetic/matrix/sampling
  adapters: existing pure matrix machine mathematics and its Ops connection.
* Pure Newton–Schulz, deflation and spectral bisection analysis leaves `Matrix/Computation`
  for corresponding numerical matrix topics. Its definitions and proofs are reused.
* `RandomMatrix/TapeLaw` and `RandomMatrix/Gaussian/Tape`: probability measures, iid windows,
  and real/complex Gaussian matrices, separated from old matrix-free access models.
* Pure ideal bisection sample definitions live beside `SpectralBisectionSamples`; old
  interpretation and storage adapters remain separate.

The concrete tape layout module is `Matrix/FinitePrecision/Samples`; the ideal recursive tree
is `Matrix/FinitePrecision/SpectralBisection/IdealSamples`. The mixed
`SpectralBisectionSamples` file keeps pure sample congruence and measurability. Its old
`ScalarSem` coupling proofs move to `SpectralBisectionSamples/LegacySemantics`, which is consumed
only by the old program certificates until retirement. This module contains the original
adapter proofs rather than forwarding definitions.

All consumers import the mathematical topic directly. Other agents own Krylov programs,
Hutch++, and new Gram–Schmidt, so import edits in those paths are coordinated with their owners.
Root owns generated imports and deletion of obsolete programs.

## Statement preservation and validation

This is a move/split of checked declarations, not a new numerical proof. Headline statements
remain the existing word-output specifications and numerical probability theorems; no assumption
is weakened, no execution success premise is added, and no output is preprocessed. In particular,
the pure quantizer remains distinct from a physical IEEE execution guarantee.

Validation builds the separated modules and actual `WorkCertification`, `ProbabilityTransfer`,
and `Sign.Math` consumers through the shared gate. Their transitive import closures must contain
no old computation execution modules. Source checks and declaration/axiom audits accompany the
build. The shared proof machinery is unchanged: existing error lemmas, sample maps, tape position
identities and Ops total execution rules are reused, with no parallel evaluator or duplicate proofs.

## Placement decisions

Scalar numerical models use the existing layer-zero Matrix topic so existing Matrix consumers
can import them without a new layer or changes to rule data. Probability laws stay in RandomMatrix.
Pure mathematical declarations keep their existing namespace even where its historical name is
`NLAlib.Computation`; module dependency separation is independent of namespace spelling.

## Finite binary64 operations

`NativeFloat` and `NativeFloatSqrt` retain the existing logical `Float` accuracy, finite-range
and square-root proofs independently of the old optional interpreter. `WordRepresentation`
bridges bounded binary representability to an actual finite logical `Float` word, using core's
normalization and packing and the existing nearest-float uniqueness lemma.

`OpsFloat` uses these actual native arithmetic functions on the finite-word carrier. Operations
are total, with an explicit finite fallback outside their accuracy range. The model asserts
mixed relative/absolute error only for exact results of magnitude at most the largest finite
binary64 value, and excludes a zero divisor in the division accuracy clause. Negation remains
exact. This is an instance of the existing `Ops.MixedModel`, not a new arithmetic interface.

Rational literals have a separately documented rounded-word policy. Converting numerator and
denominator independently through native `Float` is not a correct all-rational literal model:
an in-range quotient can have an overflowing numerator or denominator. The finite-word literal
constructor instead uses the existing mathematical binary quantizer and its representability
bridge. No physical implementation cost or runtime replacement guarantee follows from this
logical word model. Existing scalar/BLAS/CG mixed-error theorems consume its pointwise model;
there is no algorithm accuracy callback or execution-success assumption.

The final preservation pass also keeps pure ordered dot/substitution traces and their operation
labels (`ArithmeticOperation`, `Traces`), relative normalization inequalities and their named
factor (`Normalization`), the full entrywise-to-norm classical Gram–Schmidt analysis
(`ClassicalGramSchmidtRoundingError`), and the finite represented-value carrier and optional
quantizer (`BinaryFloatCarrier`). These modules live under `Matrix/FinitePrecision`; the
nearest-grid relative-error theorem lives in `GridMachine`. Their mathematical statements and
proofs remain independent of either evaluator. Two normalization helper lemmas are public so
that temporary legacy adapters can use the preserved proof without duplication.

The same separation applies to pure mathematics embedded in former program files outside the
core folders. `Krylov/FinitePrecision/{CGPrecision,LanczosPrecision,LanczosReorthPrecision}`
retain the three registered precision budgets and their scalar comparisons, including the
reorthogonalization regime and coefficient tridiagonal. `Krylov/LinearSystems/CGGuards` retains
positive curvature and guarded mathematical status transitions. Registered constant names and
bodies remain unchanged; only their file paths change. A generic square-root helper belongs to
the existing upstream-candidate `ForMathlib/Analysis/Real/Sqrt` topic.
