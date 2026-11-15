# Polynomial majorants for fixed Ops programs

The shared analysis bounds weighted work of the actual instrumented statement tree. It
introduces no evaluator, and the total QR adapter retains the existing numerical certificate.
Every operation, query, index/address instruction, control step, allocation and release stays
in the full canonical count.

## Index contexts and work measures

`IExp.degreeAt degrees e` bounds an evaluated natural index by a power of a common base, with
an individual exponent for every current index slot. Frames map each dimension and operand
offset separately. Loops and bounded queries append only their new index exponent; existing
slot exponents remain unchanged. Constants zero and one have exponent zero.

The statement analysis keeps four separate quantities:

- `Stmt.workCoefficient`: a syntax-computed coefficient, adding sequential and alternative
  instruction bodies and query charges.
- `Stmt.workDegreeAt`: the loop degree for the current index context; sequential composition
  takes the larger degree, while a loop adds its iteration-count degree.
- `Stmt.callDegreeAt`: an independent exponent controlling primitive dimension values.
- `Stmt.callArity`: the actual largest operation/query dimension-list length.

A base `b ≥ 2` and aligned `List.Forall₂ (fun v e => v ≤ b^e) idx degrees` admit the initial
indices. The generic conclusion is

```
stmtWeightedCost op query s idx ≤ s.workCoefficient * b^(s.workDegreeAt degrees) * weight.
```

`WorkEnvelope` bounds supplied operation/query weights on dimension lists of length at most
the actual call arity and entries at most `b^(s.callDegreeAt degrees)`. The finite envelope
is separately enumerable; it is not the program's static cost manifest. Shape growth is not
inferred from the total work degree.

## Exact shifted QR specialization

Write `b = (N-1) + m + k + F + M + 2`. The first five initial index slots have exponent one;
the three raw operand offsets are zero and have exponent zero. The entire fixed instrumented
program supplies a computable coefficient `C`, work degree `D`, call degree `E`, and arity `A`.
Let `K(A,b^E)` be the finite maximum of the two supplied spectral cost functions on natural
dimension lists of length at most `A` and entries at most `b^E`. Every admitted raw input,
every interpretation meeting the existing exact model and every tape have a total canonical run:

```
full modeled work ≤ C * b^D * (1 + K(A,b^E))
modeled sequential span ≤ C * b^D * (1 + K(A,b^E)).
```

Only the overhead factor is asserted polynomial; arbitrary supplied kernel growth remains
explicit. The admitted count satisfies `k = 2^m`. Fuel `F` and grid bound `M` remain natural
inputs. This is not a bit-complexity or accuracy-complexity statement and makes no tightness
claim. No kernel is silently assigned zero work.

`exactAlgorithm_runs_with_work_le` returns the total run and the original stored backward
output. `exactAlgorithmWithPolynomialWork` inherits `deflationForwardSpecification` and
`exactForwardAlgorithm`, retaining both backward and HD9 directed forward-error guarantees.
Its program, model, admission, full count budget, scratch and memory fields are unchanged.
Functional uniqueness identifies its resource-bound run with the existing certificate's run.

## Files and shared machinery

- `Ops/IndexDegrees.lean`: aligned per-slot expression and dimension-list bounds.
- `Ops/ContextWork.lean`: computable coefficient, work degree, call degree and arity.
- `Ops/WeightEnvelope.lean`: finite-domain weight hypotheses and enumerable maximum.
- `Ops/PolynomialWork.lean`: context-sensitive weighted bound and canonical execution bridge.
- `Eigensolvers/ShiftedQR/Cost.lean`: actual QR measures, finite spectral envelope and total adapter.

Existing APIs reused: `IExp.evalList`, `stmtWeightedCost`, `evalCounted_weight_le`,
`ResourceModel.work`, `ResourceModel.span_le_work`, and the exact backward/forward certificate.
Searched Mathlib/Ops: power monotonicity and aligned-list operations are reused; no existing
context-sensitive full-program polynomial majorant was found. The abandoned uniform-base
prototype is replaced, rather than retained as a parallel cost analysis.

The final actual profile is `C=17109`, `D=14`, `E=5`, `A=2`. The public equalities
`exactWorkCoefficient_eq`, `exactWorkDegree_eq`, `exactCallDegree_eq`, and
`exactCallArity_eq` use kernel reduction (`rfl`), and `exactPolynomialWork_eq` rewrites the
named expression into `17109 * b^14 * (1 + K(2,b^5))`. No unchecked evaluator supplies a proof.
