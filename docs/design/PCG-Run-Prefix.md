# PCG run prefixes

The guarded rounded PCG solver consumes an initialized prefix at each loop iteration.
`Krylov/FinitePrecision/PCGRunPrefix.lean` extends the existing `PCGRun`; it does not
introduce another mathematical trajectory model. `PCGRun.exists_extend` takes local
normwise defects, current pairing and curvature positivity, the exact next oracle action,
and final pairing nonnegativity. Its conclusion preserves the system, reference
preconditioner, identical oracle, right-hand side and allowance, and specifies every
sequence through point updates. Consequently every previous state and pairing is retained.
The proof reuses the point-update organization of `CGRunConstruction`, with PCG's fourth
vector and additive pairing error; Mathlib's `Function.update` is used directly.

`Krylov/CG/HSPCG/FinitePrecision/Prefix.lean` supplies the execution-facing proposition

```lean
RunPrefix A P O b e k s rho : Prop
```

Its zero case states the exact initializer state, the initial computed dot-product error
and nonnegativity. Its positive case is an existing `PCGRun n k` with fixed problem,
oracle, allowance, endpoint state and terminal pairing. `RunPrefix.exists_run` exposes
that witness whenever `0 < k`. This is support for loop invariants, not a second run model
or an additional algorithm definition.

The append bridge has conclusion

```lean
RoundBounds.append_prefix ... : RunPrefix A P O b e (k + 1) next rho'
```

It consumes a prefix and actual `RoundBounds em u ed ea A O s next rho rho'`, together
with a Hermitian system, SPD reference preconditioner, nonnegative local allowances below
the common allowance, the common upper bound of one percent, and final pairing
nonnegativity. The local bounds already contain the current divisor positivity proved
by step execution. The zero case uses `PCGRun.ofOneStep`; the positive case uses the pure
extension constructor and `RoundBounds.exists_run_errors`.

The numerical continuation theorem derives nonzero next directions from the extracted
existing run. The runtime derives final pairing nonnegativity from its spectral precision
window and identifies a recomputed incoming pairing with the preceding outgoing pairing
using the functional scalar dot kernel on the unchanged word operands. This identity must
be established by execution; a relational BLAS error bound alone does not identify dots.
No execution-success hypothesis is introduced. No new memory or primitive contract is
needed. Searched Mathlib and the existing PCG run API: no PCG append constructor exists.
There is no separate Mathlib notion being replaced and no numerical bound is defined here.

## Functional dot evidence

`HSPCG/FinitePrecision/Pairing.lean` defines `pairingValue F r z` using the existing
`sumSeqF` kernel on `List.ofFn` operands, and `dotEvidenceRel ε Q` preserves an additional
predicate of the two decoded finite vectors and the actual output word. The public
`dot_function_meets hB.dot hDot` combines the numerical BLAS law and the backend's
functional law. It uses the shared `Interp.Meets.and_rel` in `Ops/Logic/Writes.lean`;
that rule reads back apart output blocks from the same actual operation result before
identifying the two relational witnesses. It does not assume independent runs coincide.

The existing thirteen-call step proof is generalized once as `step_spec_with_pairings`.
The ordinary `step_spec` specializes its extra evidence to `True`; the functional
`step_writes_function` exposes the original `RoundBounds` together with
`rho = pairingValue F s.r s.z` and `rho' = pairingValue F next.r next.z`.
Unchanged residual and preconditioned-residual words therefore force the old outgoing dot
and new incoming dot to agree. Shared `Ops.ofFn_decv` is the canonical decoding round trip.
