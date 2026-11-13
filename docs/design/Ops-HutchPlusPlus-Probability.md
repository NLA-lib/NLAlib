# Hutch++ samples and same-run Gaussian probability

The exact word program computes the existing mathematical `hutchpp` estimator, including
rank-deficient sketches through rank-revealing modified Gram–Schmidt. Distribution theory
is separate from that execution proof.

`HutchPlusPlus/Samples` exposes the two actual scalar-codec matrix windows: the sketch at
position zero, followed by the residual probes at position n*k on the same stream. Its finite
tape constructor packs S followed by G. Exact coupling uses shared adjacent-window lemmas and
codec roundtrips, including empty matrices. Other streams and unused positions are defaults;
the constructor claims no full infinite iid tape law.

`HutchPlusPlus/Probability` uses ordinary real Gaussian matrix `HasLaw` hypotheses for S and G
and their `IndepFun` hypothesis. It reuses
`measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix`, with the existing explicit
embedding dimension, positive sketch size, positive failure parameter and nonnegative absolute
error threshold. The underlying theorem applies to any real square input matrix; positive
semidefiniteness is needed only for its separate relative-trace corollaries.

The actual output postcondition reads the stored scalar and compares it to the input matrix's
trace. `Ops.Algorithm.measureReal_failure_le` transfers the Gaussian bound to the negation of
`Specification.Accepts`, preserving the exact word output, complete counters, work, span,
scratch, resident payload, sample advance and cleanup on that same canonical execution.

No execution-success hypothesis, numerical-output callback, hidden input preprocessing or
algorithm inside an operation contract is introduced. The stored operator model supplies the
actual input matrix: raw dense words, an explicit COO representation with its existing
duplicate-entry meaning, or a declared matrix-free oracle. Sampling is specified only through
the windows actually consumed by the program.
