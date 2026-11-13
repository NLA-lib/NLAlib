# Polar Horner program and cost proposal

> **Archived execution proposal.** This source targets the retired `Computation` executor
> and target registry. It is preserved as research material outside the built libraries;
> the reproduction commands below describe that historical environment and do not apply
> to the current Ops library. The numerical results in `Matrix/Functions/PolarMinimax.lean`
> remain part of the current library.

The atlas card [polar-minimax-polynomial-iteration](https://research.chen.pw/NLAlib/#polar-minimax-polynomial-iteration)
bounds the number of matrix products once the scalar coefficients are supplied.
This proposal evaluates the library's `oddMatrixIterate` on a rectangular matrix
over any `RCLike` field. For Gram degree $q \ge 1$ and $k$ stages, its fixed
tree calls the matrix multiplication kernel exactly $(q+1)k$ times. This includes
zero stages, repeated or zero coefficients, empty dimensions, and deficient rank.
The scalar minimax claims are in `NLAlib/Matrix/Functions/PolarMinimax.lean`.
[The Polar Express, §2 and Appendix E](https://arxiv.org/abs/2505.16932v5)

## Input and cost

`Proposal.Polar.horner.compiled` takes the row count $m$ and the three sizes
`![n, d, k]`, with $d=q-1$. The program reads $mn$ column-major entries of
$A$ from read-only storage. Its two declared buffers hold the writable output
and the $k(d+2)$ supplied real coefficients, packed stage by stage in ascending
powers. Every `RCLike` entry occupies one exact scalar word. Each stage forms
$G=X^*X$, starts with $c_{q-1}I+c_qG$, performs $q-1$ square products,
then computes the rectangular product with $X$. The adjoint, diagonal shifts,
entrywise scaling and copies are charged as scalar operations.

The program allocates $mn+3n^2$ scratch words. The total bound, including the
input ROM, output, coefficients, and scratch, is $3mn+3n^2+k(d+2)$ words.
Matrix multiplication uses the library's exact black-box `liftMM realLayout exactMM`
and `mmShape` contract. Workspace accounting measures interpreter-visible words.

## Lean statements

All identifiers below are in `Proposal.Polar`.

- `horner.kernelWeight_cnt_of_exec_eq_some` proves the exact increment in the
  standard kernel-weighted count for every successful run of the actual tree.
  `horner.kernelWeight_staticCost` derives the same count from the tree's
  static semantics. The proof uses the library's standard operation counter.
- `spec_stage` proves successful execution and the exact output of one complete
  rectangular Horner update, with an explicit mutation footprint. It calls
  `routineSpec_adjoint`, `spec_addDiagonal`, `spec_inner` and the library's
  matrix multiplication contract.
- `storedEntriesHornerWithExactMM` is the full success, value and resource theorem.
  `storedEntriesHorner` proves its registry-shaped presentation
  `StoredEntriesHorner`. The numerical postcondition reads the final output
  buffer and compares it to `oddMatrixIterate` for every input.
- `StoredEntriesExactMatMul` and its `NonVacuous` companion give the candidate
  exact access model. `storedEntriesHorner_nonVacuous` supplies a witness at
  arbitrarily large row counts.

## Reproducing the checks

From the repository root, build the native dependencies. The commands below
use the repository's pinned toolchain and compile these review modules into
Lake's existing module search path. Each invocation treats warnings as errors.

~~~sh
set -eu
lake build --wfail NLAlib.Matrix.Functions.PolarMinimax NLAlibTools.Float
out=.lake/build/lib/lean/proposals/polar
mkdir -p "$out"
for part in Adjoint Diagonal Packed Horner Access Memory Initial Inner Stage Final; do
  lake env lean -DwarningAsError=true -o "$out/$part.olean" "proposals/polar/$part.lean"
done
lake env lean -DwarningAsError=true proposals/polar/Smoke.lean
~~~

The six run checks exercise a nonsquare matrix with a nondiagonal Gram matrix,
a negative middle coefficient, a vanishing leading coefficient, zero stages,
Gram degrees one through three, and both empty rectangular shapes. They compare
the returned words and the matrix-product count to independent expected values.

## Maintainer review

The existing `Computation.StoredEntries` interpreter supplies no black-box
kernel. This proposal gives it exactly one specified multiplication kernel with
`Interp.withKernel`. The existing registry recognizes four models in
`scripts/Targets.lean`. Admission requires a maintainer decision on the exact
stored-entry product model, its nonvacuity companion, the symbolic tree, and
the target's printed statement and resource convention. Promotion also requires
the registry generator to recognize the approved model and the maintainer to
approve the regenerated closure and tree hashes under the
[program rules](../../docs/contributing/programs.md). The standalone proposal has
no registered result ID.
