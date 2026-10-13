# NLAlib

A Lean 4 / Mathlib library of the foundations of numerical linear algebra: matrix analysis and
perturbation theory, random matrices and concentration, sketching, low-rank approximation,
Krylov methods and randomized solvers. The aim is reusable statements that other people's
proofs can cite, stated once, generally, in Mathlib's style.

Website: https://nla-lib.org. The library is being rebuilt from an internal prototype, one
layer at a time, starting with `NLAlib/Matrix/`.

## Using

```
lake exe cache get
lake build -j 4 NLAlib
```

Pinned: Lean `v4.33.1`, Mathlib `v4.33.1`.

## Contributing

[CONTRIBUTING.md](CONTRIBUTING.md) is the contract: layout, file template, names, statement
conventions and vocabulary, docstrings and citations, the no-`sorry` rule and the scaffold library,
the PR checks, and how to build without exhausting memory. Agents start at
[AGENTS.md](AGENTS.md).

## License

Apache License 2.0, see [LICENSE](LICENSE). Ported material keeps its original attribution in the
file header.
