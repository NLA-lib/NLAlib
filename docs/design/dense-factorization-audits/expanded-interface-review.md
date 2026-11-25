# Independent factorization interface review

Integration note: all eight placement findings below were subsequently corrected. The four
scalar facts were moved/generalized into existing ForMathlib field/sqrt topics, redundant
nonnegativity arguments were dropped, and consumers updated. The four standalone Nat facts
were replaced by existing Mathlib ceil-division APIs inside matrix-specific execution proofs.
The findings are retained as review history; no allowlist exemption was added.

Read-only review of canonical relative/finite Cholesky and frozen blocked LU/trailing sources
under /tmp/nlalib-next-blocked and /tmp/nlalib-next-trailing. No checked source or artifacts were
changed and no shared/canonical builds were launched. Mutable blocked Cholesky was excluded.

## Concrete repository-rule blockers

P9 requires general facts with no NLAlib/matrix/measure vocabulary to live in ForMathlib.
These are genuine placement issues, not helper-name collisions:

- BlockedLUExecution.lean: private block_start_lt, block_end_eq_min, block_terminal,
  block_count_zero (the original lines 32–54): pure Nat/ceilDiv arithmetic. LU worker has
  acknowledged and is replacing these with existing Mathlib facts inline in matrix-specific
  execution proofs, preserving actual builders and headline interfaces.
- Canonical Matrix/Perturbation/CholeskySchurError.lean: private
  abs_mul_div_sub_mul_div_le: pure real rational perturbation inequality. Root acknowledged
  ownership of its proper placement/reuse correction.
- Canonical Matrix/Perturbation/CholeskyColumnError.lean: public
  abs_sqrt_sub_sqrt_le_div, private abs_div_sub_div_le, public
  abs_div_sqrt_sub_div_sqrt_le: pure real inequalities without NLAlib vocabulary. Use an
  appropriate ForMathlib sqrt/division topic after checking existing Mathlib API.

A scan of exposed signatures across all new Cholesky mixed/relative scalar and finite-range
files found no further scalar P9 item. In particular, mixed-column helpers mentioning
AbsRelErr and helpers mentioning roundingFactor have actual NLAlib vocabulary; they are not
the same P9 issue. The tiny matrixView shorthand has explicit Matrix vocabulary and is not a
true P9 violation, although directly using Matrix.submatrix is a sensible simplification.

No material T9/exposed-type defect was found. Fin.castLE/natAdd in public types use named
bound hypotheses rather than embedded proof scripts. The generic word/storage helpers retain
proper arbitrary carriers where claimed.

## Cholesky semantic assessment

No material soundness or unsupported headline claim found in the reviewed code.

- Relative full success takes a source spectral band, u<=1/10, and an explicit input Schur
  error recurrence below mu/2. These are functions of original input/numerical parameters,
  not assumptions of an actual run or rounded stored pivot trace. Every actual active pivot
  and positive diagonal is derived during execution.
- Finite-range success uses CholeskyRangeConditions: scalar inequalities involving only
  N,u,tau,B,mu,Omega, plus the original spectral band. Root/divisor margins and exact-result
  range are established before instructions execute. Its residual invariant covers all
  entries, including retired rows/columns, which is necessary for the actual full Schur update.
- The arithmetic-only interface correctly has separate minus-one-literal and square-root
  backend laws. BinaryCholesky proves both for the actual bounded binaryFloatSem quantizer;
  it does not leave these as unexplained assumptions in its concrete theorem.
- The factor budget is absolute IsCholeskyErr, not a relative input-scaled budget. Uniform
  entry error e gives spectral factor distance <=N*e; the residual estimate is exactly
  (N*e)(2*sqrt(B)+N*e), including the necessary quadratic term. The dimensions/scale and
  structural requirements (exact lower zeros, positive diagonal) are consistent.
- The source is copied to residual scratch before any factor writes, so original source and
  output may share or overlap words. Final footprint is one original output block write.
  N=0 branches execute empty bodies before reading handles; capacity/storage conditions are
  vacuous and no phantom source-handle validity is introduced.

Limits to preserve in user-facing claims:

- These bounds are conservative and conditioning-dependent; they do not establish classical
  condition-independent Cholesky backward stability or a sharp Higham-style constant.
- binaryFloatSem is a noncomputable mathematical quantizer on represented real values with
  gradual underflow, explicit nearest tie policy and rejection when the EXACT result exceeds
  maxFinite. It excludes signed zeros/nonfinite sentinels and is not linked to native IEEE
  machine operations. Actual Float regression examples do not supply that missing linkage.
- The finite theorem requires its explicit numerical inequalities; no ready-made theorem
  automatically establishes them for every SPD binary64 matrix.

## Blocked LU/trailing semantic assessment

No material soundness or unsupported exposed theorem claim found.

- blockedLuFactor uses clipped panel widths and a supplied symbolic count satisfying the
  exact ceiling formula. Its no-pivot nonbreakdown premise is on canonical gaussState of the
  ORIGINAL input, not a supplied actual execution trace. It is an input-only exact domain
  condition, not a theorem of success for every nonsingular matrix.
- The actual panel kernel materializes lower columns/upper rows and updates only two panel
  rectangles with saved pivot operands and GER. The bottom-right square is deferred until
  a packed GEMM product of the completed panel is subtracted. This is genuine panel deferral,
  not grouping repeated full residual Schur calls inside a block counter.
- The rectangle copies carry the parent leading dimension explicitly. The trailing operator
  gathers both panel factors and the trailing residual before any residual scatter; its
  alias claims and unchanged-exterior statement agree with that actual instruction order.
- The existing library gemm builder is really called on packed m-by-width and width-by-m
  operands. It is nevertheless a scalar reference IR (one gemv per column), not an optimized
  native BLAS binding. No cache-efficiency or native BLAS acceleration has been proved.
- Input is copied before clearing either factor, so source/output overlap in the full blocked
  driver is genuine. Retention of the source is only promised under the stated source/output
  buffer separation. Lower/upper outputs are distinct in the main theorem; the separate
  empty-store helper supports coincident invalid handles without a scalar-model assumption.
- Empty trailing blocks and zero-width panel updates have their stated degenerate behavior;
  gathering/scattering may still copy initialized residual words at width zero. The docs
  correctly promise no arithmetic there, not absence of all word copies.

Limits: current reviewed full blocked LU is real, exact-semantics, unpivoted LU with nonzero
canonical pivots. It is not rounded blocked LU or a blocked PLU/PLUQ driver. Blocked Cholesky
is another worker's mutable lane and was not included in this review.

## Predicate / Mathlib reuse assessment

IsCholeskyErr is a substantive absolute-residual extension with an existing exact-zero bridge.
The blocked panel states are actual deferred-elimination reference states and stored invariants,
not duplicate factorization predicates. IsLDL extends to real diagonal signs/indefinite inputs;
the newly delivered LDLMathlib bridge identifies Mathlib's actual factors and canonical SPD
factors, filling the explicit reuse obligation. Existing Matrix.submatrix/finite embeddings,
canonical LU/Cholesky factors and standard GEMM/GER interfaces are reused.
