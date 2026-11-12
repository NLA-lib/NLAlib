# Spectral consequences for the actual reorthogonalized prefix

The total rounded output has an executed history and a longest leading prefix satisfying the
chosen strict test `tau * savedRawNorm < beta`. That prefix may be shorter than the executed
history. Its first excluded step satisfies the opposite non-strict inequality, so an empty
prefix is an informative numerical boundary, not an arbitrary escape alternative.

`Reorth/RoundedSpectral.lean` composes this checked prefix theorem with the existing pure
LanczosReorthRun spectral theorem. Its input assumptions are symmetry, the common primitive
precision envelope, the dimension-only actual-CGS2 error budget, `0 < tau <= 1`, eta/c in
[0,.01], and the size-only fixed-point and recurrence windows. Write
`mu = 2 * (2*c + 2*(eta+c)^2/tau + E)`. The windows are
`sqrt(3*(cap+1))*mu <= eta` and `mu + E + 3*c <= .01`.

The conclusion retains complete physical history/readback and the selected prefix's strict
and first-failed tests. A nonempty prefix exhibits the existing run with every parameter and
sequence tied to the actual archive. Its decoded basis/tridiagonal match that same run. The
largest-to-smallest eigenvalues of the stored prefix satisfy interlacing from above with
explicit perturbation radius `100*(r+1)*(mu+E+3*c)*specNorm A`. The existing pure backward,
quadrature and spectral results remain available on the returned run with the same proved
parameter identities; their execution is not reproved here. The program does not run an
eigensolver and is not modified to stop at the analysis threshold.

No new model, constant, operation or mathematical interface is introduced. Generalized packed
matrix readback lives in ordinary RoundedRitz and consumes LanczosData, so ordinary and reorth
runs share it. Mathlib was searched; NLAlib's existing LanczosReorthSpectral theorem is reused.
Canonical postcondition composition uses Algorithm.mapPost; full resource bounds stay fixed.
