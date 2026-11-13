# Same-run probability for standalone deflation

The fixed deflation program draws stored complex sample words, multiplies by the supplied
matrix, computes QR and copies the requested leading columns. Its total word certificate fixes
that result and all resource claims before any numerical probability bound is applied.

`Deflation.Probability` uses the existing pure randomized-deflation theorem, with its original
arithmetic, matrix multiplication, QR and normal-sampler accuracy assumptions. The input is a
stored perturbation of a rank-r matrix U S Vᴴ, with orthonormal U and V and invertible S. Its
conditioning, precision, range and Gaussian tail hypotheses remain explicit.

The new stored-output predicate records an actual packed basis block and the existing
mathematical conclusion: some unitary W makes the returned decoded basis close to U W. It does
not introduce a second numerical subspace interface or weaken the pure theorem.

The sample coupling is explicit:

```
sampleMatrix n 0 (tape omega) = (G omega).map normal
```

Here G has the standard complex Gaussian matrix law, and normal is precisely the normal
sampler used in the numerical machine. A concrete tape constructor packs those sampler outputs
on the Gaussian stream. Its exact-window proof uses the shared `Tape.ofStream` roundtrip and
the existing matrix codec roundtrip; it performs no algorithmic computation and writes no
input buffers. Remaining streams and unused positions contain the default word, so no full
iid tape law is claimed for that finite construction.

The generic total-certificate transfer may accept an independent reference-event bound. The
headline canonical-program theorem discharges that bound with the concrete Gaussian deflation
theorem, rather than asking for an unknown numerical failure estimate. Its failure event is
`Specification.Accepts` negated, retaining total execution, all resource bounds, the exact word
specification, sample advance, cleanup and the stored numerical conclusion on the same run.

Existing materials: `RandomizedDeflation`, pure `Matrix.FinitePrecision.Deflation`, the new
standalone `Deflation.Certification`, and `Ops.Probability`. Existing algebra and probability
proofs are reused. No execution-success hypothesis or algorithm hidden in an operation contract
is introduced.
