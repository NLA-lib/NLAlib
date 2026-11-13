/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.List.Range
public import NLAlib.Computation.Exact
public import NLAlib.ForMathlib.Data.Option.Basic
public import NLAlib.ForMathlib.Order.Basic

/-!
# BLAS kernels as programs

The BLAS kernels used by the library's programs, as derived programs inside `named` nodes (so
that the NumPy emitter may print them as calls into its prelude). Vectors are a buffer, an offset
and a length, with stride one; matrices are column-major from an offset. Offsets and lengths are
index expressions.

Each kernel has one specification under exact arithmetic, in six parts: the value (the final
store is the store with the result written, which also gives the frame), the tape positions
(unchanged), the memory in cells (current memory unchanged, the peak raised by the scratch at
most), the memory in bits (likewise), and the counts (exact). Kernels that are not elementwise
carry disjointness hypotheses; in-place kernels allow exact aliasing and forbid partial overlap.
The specifications of the level-2 and level-3 kernels are in
`NLAlib/Computation/BLAS/MatrixKernels.lean`, that of `trsvLower` and the rounding-error analyses
in `NLAlib/Computation/BLAS/Triangular.lean` and `NLAlib/Computation/BLAS/RoundingErrors.lean`.
Design: `docs/design/Computation.md` (D13, D17, §4).

## Main definitions

* Level 1: `NLAlib.Computation.dot`, `NLAlib.Computation.axpy`, `NLAlib.Computation.scal`,
  `NLAlib.Computation.rscl`, `NLAlib.Computation.copyv`, `NLAlib.Computation.nrm2`.
* Levels 2 and 3: `NLAlib.Computation.gemv`, `NLAlib.Computation.ger`,
  `NLAlib.Computation.gemm`, and the triangular solve `NLAlib.Computation.trsvLower`.
* Complex kernels on interleaved pairs (index `NLAlib.Computation.zidx`):
  `NLAlib.Computation.zcopy`, `NLAlib.Computation.zzero`, `NLAlib.Computation.zidentity`,
  `NLAlib.Computation.zneg`, `NLAlib.Computation.zadd`, `NLAlib.Computation.zsub`,
  `NLAlib.Computation.zscal`, `NLAlib.Computation.zconjTranspose`,
  `NLAlib.Computation.zmirror`, `NLAlib.Computation.zhermShift`,
  `NLAlib.Computation.zhermScale`, `NLAlib.Computation.zhermAvg`,
  `NLAlib.Computation.ztraceRe`, `NLAlib.Computation.zboxTest`. Their specifications against a
  floating-point machine are in the design note `docs/design/Computation-SignDeflatePrograms.md`
  (stage COMPDYN S1c).

## Main results

* `NLAlib.Computation.exec_dot`, `NLAlib.Computation.exec_axpy`, `NLAlib.Computation.exec_scal`,
  `NLAlib.Computation.exec_rscl`, `NLAlib.Computation.exec_copyv`, `NLAlib.Computation.exec_nrm2`:
  the specifications of the level-1 kernels.
* `NLAlib.Computation.run_dot`, `NLAlib.Computation.run_axpy`, `NLAlib.Computation.run_gemv`,
  `NLAlib.Computation.run_ger`, `NLAlib.Computation.run_gemm`,
  `NLAlib.Computation.run_trsvLower`: the kernels unfolded.
* `NLAlib.Computation.exec_forRange_dot_add`: a loop of `dot` calls accumulated into one cell.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib.Computation

open Builder

section Kernels

variable {P ι VB VI : Type}

/-- `dot`: $\mathit{dst} \leftarrow \mathbf{x}^{\mathsf{H}}\mathbf{y}$, accumulated in order.
One scratch cell. -/
def dot (p : P) (dst : Cell VB VI) (x : VB) (xo : IExp VI) (y : VB) (yo : IExp VI)
    (n : IExp VI) : Builder P ι VB VI Unit :=
  named "dot" [.cell dst, .buf x, .idx xo, .buf y, .idx yo, .idx n] do
    ins (.lit p dst 0)
    let t ← alloc p 1
    forRange n fun i => do
      ins (.un p .conj ⟨t, 0⟩ ⟨x, xo + .var i⟩)
      ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨y, yo + .var i⟩)
      ins (.bin p .add dst dst ⟨t, 0⟩)

/-- `axpy`: $\mathbf{y} \leftarrow a\mathbf{x} + \mathbf{y}$, in place. One scratch cell. -/
def axpy (p : P) (a : Cell VB VI) (x : VB) (xo : IExp VI) (y : VB) (yo : IExp VI)
    (n : IExp VI) : Builder P ι VB VI Unit :=
  named "axpy" [.cell a, .buf x, .idx xo, .buf y, .idx yo, .idx n] do
    let t ← alloc p 1
    forRange n fun i => do
      ins (.bin p .mul ⟨t, 0⟩ a ⟨x, xo + .var i⟩)
      ins (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)

/-- `scal`: $\mathbf{x} \leftarrow a\mathbf{x}$, in place. -/
def scal (p : P) (a : Cell VB VI) (x : VB) (xo : IExp VI) (n : IExp VI) :
    Builder P ι VB VI Unit :=
  named "scal" [.cell a, .buf x, .idx xo, .idx n] do
    forRange n fun i => ins (.bin p .mul ⟨x, xo + .var i⟩ a ⟨x, xo + .var i⟩)

/-- `rscl`: $\mathbf{x} \leftarrow \mathbf{x}/a$, in place (LAPACK's `rscl`). -/
def rscl (p : P) (a : Cell VB VI) (x : VB) (xo : IExp VI) (n : IExp VI) :
    Builder P ι VB VI Unit :=
  named "rscl" [.cell a, .buf x, .idx xo, .idx n] do
    forRange n fun i => ins (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ a)

/-- `copy`: $\mathbf{y} \leftarrow \mathbf{x}$. -/
def copyv (p : P) (x : VB) (xo : IExp VI) (y : VB) (yo : IExp VI) (n : IExp VI) :
    Builder P ι VB VI Unit :=
  named "copy" [.buf x, .idx xo, .buf y, .idx yo, .idx n] do
    forRange n fun i => ins (.copy p ⟨y, yo + .var i⟩ ⟨x, xo + .var i⟩)

/-- `nrm2`: $\mathit{dst} \leftarrow \|\mathbf{x}\|$, as the square root of `dot`. -/
def nrm2 (p : P) (dst : Cell VB VI) (x : VB) (xo : IExp VI) (n : IExp VI) :
    Builder P ι VB VI Unit :=
  named "nrm2" [.cell dst, .buf x, .idx xo, .idx n] do
    dot p dst x xo x xo n
    ins (.un p .sqrt dst dst)

/-- `gemv`: $\mathbf{y} \leftarrow \mathbf{A}\mathbf{x}$ for a stored $m \times n$ matrix
$\mathbf{A}$, column by column. One scratch cell. -/
def gemv (p : P) (m n : IExp VI) (A : VB) (ao : IExp VI) (x : VB) (xo : IExp VI) (y : VB)
    (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "gemv" [.idx m, .idx n, .buf A, .idx ao, .buf x, .idx xo, .buf y, .idx yo] do
    forRange m fun i => ins (.lit p ⟨y, yo + .var i⟩ 0)
    let t ← alloc p 1
    forRange n fun j => forRange m fun i => do
      ins (.bin p .mul ⟨t, 0⟩ ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)
      ins (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)

/-- `ger`: $\mathbf{A} \leftarrow \mathbf{A} + a\mathbf{x}\mathbf{y}^{\mathsf{H}}$ for a stored
$m \times n$ matrix $\mathbf{A}$, in place, column by column. Two scratch cells. -/
def ger (p : P) (m n : IExp VI) (a : Cell VB VI) (x : VB) (xo : IExp VI) (y : VB)
    (yo : IExp VI) (A : VB) (ao : IExp VI) : Builder P ι VB VI Unit :=
  named "ger" [.idx m, .idx n, .cell a, .buf x, .idx xo, .buf y, .idx yo, .buf A, .idx ao] do
    let t ← alloc p 2
    forRange n fun j => do
      ins (.un p .conj ⟨t, 0⟩ ⟨y, yo + .var j⟩)
      ins (.bin p .mul ⟨t, 0⟩ a ⟨t, 0⟩)
      forRange m fun i => do
        ins (.bin p .mul ⟨t, 1⟩ ⟨x, xo + .var i⟩ ⟨t, 0⟩)
        ins (.bin p .add ⟨A, ao + .var i + m * .var j⟩ ⟨A, ao + .var i + m * .var j⟩ ⟨t, 1⟩)

/-- `gemm`: $\mathbf{C} \leftarrow \mathbf{A}\mathbf{B}$, $\mathbf{A}$ of size $m \times n$ and
$\mathbf{B}$ of size $n \times l$, one `gemv` per column. -/
def gemm (p : P) (m n l : IExp VI) (A : VB) (ao : IExp VI) (B : VB) (bo : IExp VI) (C : VB)
    (co : IExp VI) : Builder P ι VB VI Unit :=
  named "gemm" [.idx m, .idx n, .idx l, .buf A, .idx ao, .buf B, .idx bo, .buf C, .idx co] do
    forRange l fun c => gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)

/-- `trsv` (lower, no transpose, non-unit diagonal): $\mathbf{x} \leftarrow \mathbf{T}^{-1}
\mathbf{x}$ in place, for a stored lower triangular $n \times n$ matrix $\mathbf{T}$
(column-major from $\mathit{tOff}$; the entries above the diagonal are not read), row by row:
$x_i \leftarrow (x_i - \sum_{j<i} t_{ij}x_j)/t_{ii}$, subtracting in the order $j = 0, 1, \ldots$.
One scratch cell. -/
def trsvLower (p : P) (n : IExp VI) (T : VB) (tOff : IExp VI) (x : VB) (xo : IExp VI) :
    Builder P ι VB VI Unit :=
  named "trsvLower" [.idx n, .buf T, .idx tOff, .buf x, .idx xo] do
    let t ← alloc p 1
    forRange n fun i => do
      forRange (.var i) fun j => do
        ins (.bin p .mul ⟨t, 0⟩ ⟨T, tOff + .var i + n * .var j⟩ ⟨x, xo + .var j⟩)
        ins (.bin p .sub ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ ⟨t, 0⟩)
      ins (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ ⟨T, tOff + .var i + n * .var i⟩)

/-! ### Complex kernels on interleaved pairs

A complex $m \times n$ matrix is stored as interleaved pairs of real words, column-major and
packed: the real part of entry $(i, j)$ at word $2(i + mj)$ from the offset and the imaginary
part at the next word (`NLAlib.Computation.zidx`), as in BLAS, LAPACK and NumPy `complex128`.
Every complex kernel is written over real instructions, so its rounding is componentwise, one
rounding per real operation. The Hermitian kernels compute the strict upper triangle and the
real diagonal, write a zero imaginary part on the diagonal, and complete the lower triangle from
the stored upper triangle by a copy and a negation (`NLAlib.Computation.zmirror`). -/

/-- The word offset $2(i + mj)$ of the real part of entry $(i, j)$ of a complex matrix with $m$
rows stored as interleaved pairs; the imaginary part is the next word. -/
def zidx (m i j : IExp VI) : IExp VI := 2 * (i + m * j)

/-- `zcopy`: $\mathbf{Y} \leftarrow \mathbf{X}$ for complex $m \times n$ matrices, word by word. -/
def zcopy (p : P) (m n : IExp VI) (X : VB) (xo : IExp VI) (Y : VB) (yo : IExp VI) :
    Builder P ι VB VI Unit :=
  named "zcopy" [.idx m, .idx n, .buf X, .idx xo, .buf Y, .idx yo] do
    forRange (2 * (m * n)) fun w => ins (.copy p ⟨Y, yo + .var w⟩ ⟨X, xo + .var w⟩)

/-- `zzero`: $\mathbf{Y} \leftarrow \mathbf{0}$ for a complex $m \times n$ matrix (the literal
$0$ in every word). -/
def zzero (p : P) (m n : IExp VI) (Y : VB) (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "zzero" [.idx m, .idx n, .buf Y, .idx yo] do
    forRange (2 * (m * n)) fun w => ins (.lit p ⟨Y, yo + .var w⟩ 0)

/-- `zidentity`: $\mathbf{Y} \leftarrow \mathbf{I}$ for a complex $n \times n$ matrix: the literal
$0$ in every word, then the literal $1$ in the real part of each diagonal entry. -/
def zidentity (p : P) (n : IExp VI) (Y : VB) (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "zidentity" [.idx n, .buf Y, .idx yo] do
    forRange (2 * (n * n)) fun w => ins (.lit p ⟨Y, yo + .var w⟩ 0)
    forRange n fun i => ins (.lit p ⟨Y, yo + zidx n (.var i) (.var i)⟩ 1)

/-- `zneg`: $\mathbf{Y} \leftarrow -\mathbf{X}$ for complex $m \times n$ matrices, word by word
(both parts negated). In place allowed. -/
def zneg (p : P) (m n : IExp VI) (X : VB) (xo : IExp VI) (Y : VB) (yo : IExp VI) :
    Builder P ι VB VI Unit :=
  named "zneg" [.idx m, .idx n, .buf X, .idx xo, .buf Y, .idx yo] do
    forRange (2 * (m * n)) fun w => ins (.un p .neg ⟨Y, yo + .var w⟩ ⟨X, xo + .var w⟩)

/-- `zadd`: $\mathbf{Z} \leftarrow \mathbf{X} + \mathbf{Y}$ for complex $m \times n$ matrices,
word by word (real and imaginary parts added separately). In place allowed. -/
def zadd (p : P) (m n : IExp VI) (X : VB) (xo : IExp VI) (Y : VB) (yo : IExp VI) (Z : VB)
    (zo : IExp VI) : Builder P ι VB VI Unit :=
  named "zadd" [.idx m, .idx n, .buf X, .idx xo, .buf Y, .idx yo, .buf Z, .idx zo] do
    forRange (2 * (m * n)) fun w =>
      ins (.bin p .add ⟨Z, zo + .var w⟩ ⟨X, xo + .var w⟩ ⟨Y, yo + .var w⟩)

/-- `zsub`: $\mathbf{Z} \leftarrow \mathbf{X} - \mathbf{Y}$ for complex $m \times n$ matrices,
word by word. In place allowed. -/
def zsub (p : P) (m n : IExp VI) (X : VB) (xo : IExp VI) (Y : VB) (yo : IExp VI) (Z : VB)
    (zo : IExp VI) : Builder P ι VB VI Unit :=
  named "zsub" [.idx m, .idx n, .buf X, .idx xo, .buf Y, .idx yo, .buf Z, .idx zo] do
    forRange (2 * (m * n)) fun w =>
      ins (.bin p .sub ⟨Z, zo + .var w⟩ ⟨X, xo + .var w⟩ ⟨Y, yo + .var w⟩)

/-- `zscal`: $\mathbf{Y} \leftarrow a\mathbf{X}$ for a stored real $a$ and complex $m \times n$
matrices, word by word ($a$ times each part). In place allowed. -/
def zscal (p : P) (m n : IExp VI) (a : Cell VB VI) (X : VB) (xo : IExp VI) (Y : VB)
    (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "zscal" [.idx m, .idx n, .cell a, .buf X, .idx xo, .buf Y, .idx yo] do
    forRange (2 * (m * n)) fun w => ins (.bin p .mul ⟨Y, yo + .var w⟩ a ⟨X, xo + .var w⟩)

/-- `zconjTranspose`: $\mathbf{Y} \leftarrow \mathbf{X}^{\mathsf{H}}$ for a complex $m \times n$
matrix $\mathbf{X}$ and the $n \times m$ matrix $\mathbf{Y}$: the real part copied, the
imaginary part negated. Out of place. -/
def zconjTranspose (p : P) (m n : IExp VI) (X : VB) (xo : IExp VI) (Y : VB) (yo : IExp VI) :
    Builder P ι VB VI Unit :=
  named "zconjTranspose" [.idx m, .idx n, .buf X, .idx xo, .buf Y, .idx yo] do
    forRange m fun j => forRange n fun i => do
      ins (.copy p ⟨Y, yo + zidx n (.var i) (.var j)⟩ ⟨X, xo + zidx m (.var j) (.var i)⟩)
      ins (.un p .neg ⟨Y, yo + zidx n (.var i) (.var j) + 1⟩
        ⟨X, xo + zidx m (.var j) (.var i) + 1⟩)

/-- `zmirror`: the lower triangle of a complex $n \times n$ matrix $\mathbf{Y}$ from its strict
upper triangle, $y_{ji} \leftarrow \bar y_{ij}$ for $i < j$ (the real part copied, the imaginary
part negated), in place. -/
def zmirror (p : P) (n : IExp VI) (Y : VB) (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "zmirror" [.idx n, .buf Y, .idx yo] do
    forRange n fun j => forRange (.var j) fun i => do
      ins (.copy p ⟨Y, yo + zidx n (.var j) (.var i)⟩ ⟨Y, yo + zidx n (.var i) (.var j)⟩)
      ins (.un p .neg ⟨Y, yo + zidx n (.var j) (.var i) + 1⟩
        ⟨Y, yo + zidx n (.var i) (.var j) + 1⟩)

/-- `zhermShift`: $\mathbf{Y} \leftarrow \mathbf{X} - c\mathbf{I}$ stored Hermitian, for complex
$n \times n$ matrices and a stored real $c$: the strict upper triangle copied, the diagonal real
parts $\mathrm{fl}(\operatorname{Re} x_{ii} - c)$, the diagonal imaginary parts the literal $0$,
the lower triangle mirrored (`NLAlib.Computation.zmirror`). Out of place. -/
def zhermShift (p : P) (n : IExp VI) (X : VB) (xo : IExp VI) (c : Cell VB VI) (Y : VB)
    (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "zhermShift" [.idx n, .buf X, .idx xo, .cell c, .buf Y, .idx yo] do
    forRange n fun j => forRange (.var j) fun i => do
      ins (.copy p ⟨Y, yo + zidx n (.var i) (.var j)⟩ ⟨X, xo + zidx n (.var i) (.var j)⟩)
      ins (.copy p ⟨Y, yo + zidx n (.var i) (.var j) + 1⟩
        ⟨X, xo + zidx n (.var i) (.var j) + 1⟩)
    forRange n fun i => do
      ins (.bin p .sub ⟨Y, yo + zidx n (.var i) (.var i)⟩ ⟨X, xo + zidx n (.var i) (.var i)⟩ c)
      ins (.lit p ⟨Y, yo + zidx n (.var i) (.var i) + 1⟩ 0)
    zmirror p n Y yo

/-- `zhermScale`: $\mathbf{Y} \leftarrow \mathbf{X}/c$ stored Hermitian, for complex $n \times n$
matrices and a stored real $c$: both parts of the strict upper triangle and the diagonal real
parts divided by $c$, the diagonal imaginary parts the literal $0$, the lower triangle mirrored.
Out of place. -/
def zhermScale (p : P) (n : IExp VI) (X : VB) (xo : IExp VI) (c : Cell VB VI) (Y : VB)
    (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "zhermScale" [.idx n, .buf X, .idx xo, .cell c, .buf Y, .idx yo] do
    forRange n fun j => forRange (.var j) fun i => do
      ins (.bin p .div ⟨Y, yo + zidx n (.var i) (.var j)⟩ ⟨X, xo + zidx n (.var i) (.var j)⟩ c)
      ins (.bin p .div ⟨Y, yo + zidx n (.var i) (.var j) + 1⟩
        ⟨X, xo + zidx n (.var i) (.var j) + 1⟩ c)
    forRange n fun i => do
      ins (.bin p .div ⟨Y, yo + zidx n (.var i) (.var i)⟩ ⟨X, xo + zidx n (.var i) (.var i)⟩ c)
      ins (.lit p ⟨Y, yo + zidx n (.var i) (.var i) + 1⟩ 0)
    zmirror p n Y yo

/-- `zhermAvg`: $\mathbf{Y} \leftarrow (\mathbf{X} + \mathbf{X}^{\mathsf{H}})/c$ stored
Hermitian, for complex $n \times n$ matrices and a stored real $c$: on the strict upper triangle
$\mathrm{fl}(\mathrm{fl}(\operatorname{Re} x_{ij} + \operatorname{Re} x_{ji})/c)$ and
$\mathrm{fl}(\mathrm{fl}(\operatorname{Im} x_{ij} - \operatorname{Im} x_{ji})/c)$, on the
diagonal $\mathrm{fl}(\mathrm{fl}(\operatorname{Re} x_{ii} + \operatorname{Re} x_{ii})/c)$ and the
literal $0$, the lower triangle mirrored. Out of place. -/
def zhermAvg (p : P) (n : IExp VI) (X : VB) (xo : IExp VI) (c : Cell VB VI) (Y : VB)
    (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "zhermAvg" [.idx n, .buf X, .idx xo, .cell c, .buf Y, .idx yo] do
    forRange n fun j => forRange (.var j) fun i => do
      ins (.bin p .add ⟨Y, yo + zidx n (.var i) (.var j)⟩ ⟨X, xo + zidx n (.var i) (.var j)⟩
        ⟨X, xo + zidx n (.var j) (.var i)⟩)
      ins (.bin p .div ⟨Y, yo + zidx n (.var i) (.var j)⟩ ⟨Y, yo + zidx n (.var i) (.var j)⟩ c)
      ins (.bin p .sub ⟨Y, yo + zidx n (.var i) (.var j) + 1⟩
        ⟨X, xo + zidx n (.var i) (.var j) + 1⟩ ⟨X, xo + zidx n (.var j) (.var i) + 1⟩)
      ins (.bin p .div ⟨Y, yo + zidx n (.var i) (.var j) + 1⟩
        ⟨Y, yo + zidx n (.var i) (.var j) + 1⟩ c)
    forRange n fun i => do
      ins (.bin p .add ⟨Y, yo + zidx n (.var i) (.var i)⟩ ⟨X, xo + zidx n (.var i) (.var i)⟩
        ⟨X, xo + zidx n (.var i) (.var i)⟩)
      ins (.bin p .div ⟨Y, yo + zidx n (.var i) (.var i)⟩ ⟨Y, yo + zidx n (.var i) (.var i)⟩ c)
      ins (.lit p ⟨Y, yo + zidx n (.var i) (.var i) + 1⟩ 0)
    zmirror p n Y yo

/-- `ztraceRe`: $\mathit{dst} \leftarrow \sum_i \operatorname{Re} x_{ii}$ for a complex
$n \times n$ matrix, rounded from the left: the literal $0$, then
$\mathit{dst} \leftarrow \mathrm{fl}(\mathit{dst} + \operatorname{Re} x_{ii})$ for
$i = 0, \ldots, n - 1$. -/
def ztraceRe (p : P) (n : IExp VI) (X : VB) (xo : IExp VI) (dst : Cell VB VI) :
    Builder P ι VB VI Unit :=
  named "ztraceRe" [.idx n, .buf X, .idx xo, .cell dst] do
    ins (.lit p dst 0)
    forRange n fun i => ins (.bin p .add dst dst ⟨X, xo + zidx n (.var i) (.var i)⟩)

/-- `zboxTest`: the max-modulus test of the parts of a complex $m \times n$ matrix,
$\mathit{flag} \leftarrow 0$ if every real and imaginary part $t$ satisfies
$\mathit{lo} \le t \le \mathit{hi}$
(two comparisons per word) and $1$ otherwise, the flag a literal. -/
def zboxTest (p : P) (m n : IExp VI) (X : VB) (xo : IExp VI) (lo hi flag : Cell VB VI) :
    Builder P ι VB VI Unit :=
  named "zboxTest" [.idx m, .idx n, .buf X, .idx xo, .cell lo, .cell hi, .cell flag] do
    ins (.lit p flag 0)
    forRange (2 * (m * n)) fun w =>
      ifThenElse p .le lo ⟨X, xo + .var w⟩
        (ifThenElse p .le ⟨X, xo + .var w⟩ hi (pure ()) (ins (.lit p flag 1)))
        (ins (.lit p flag 1))

end Kernels

/-! ### Run lemmas: the kernels unfolded -/

section Runs

variable {P ι : Type}

/-- The program of `dot`: zero $\mathit{dst}$, then add $\bar{x}_i y_i$ for each $i$, through one
scratch cell. -/
theorem run_dot (p : P) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    (dot (ι := ι) p dst x xo y yo n).run = .seq (.named "dot"
      [.cell dst, .buf x, .idx xo, .buf y, .idx yo, .idx n]
      (.seq (.instr (.lit p dst 0)) (.alloc p 1 fun t => .seq (.loop n fun i =>
        .seq (.instr (.un p .conj ⟨t, 0⟩ ⟨x, xo + .var i⟩))
          (.seq (.instr (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨y, yo + .var i⟩))
            (.seq (.instr (.bin p .add dst dst ⟨t, 0⟩)) .skip))) .skip))) .skip := rfl

/-- The program of `axpy`: add $a x_i$ to $y_i$ for each $i$, through one scratch cell. -/
theorem run_axpy (p : P) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    (axpy (ι := ι) p a x xo y yo n).run = .seq (.named "axpy"
      [.cell a, .buf x, .idx xo, .buf y, .idx yo, .idx n]
      (.alloc p 1 fun t => .seq (.loop n fun i =>
        .seq (.instr (.bin p .mul ⟨t, 0⟩ a ⟨x, xo + .var i⟩))
          (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)) .skip))
        .skip)) .skip := rfl

private theorem scal_run (p : P) (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) :
    (scal (ι := ι) p a x xo n).run = .seq (.named "scal" [.cell a, .buf x, .idx xo, .idx n]
      (.seq (.loop n fun i =>
        .seq (.instr (.bin p .mul ⟨x, xo + .var i⟩ a ⟨x, xo + .var i⟩)) .skip) .skip)) .skip :=
  rfl

/-- The program of `rscl`: divide $x_i$ by $a$ in place for each $i$. -/
theorem run_rscl (p : P) (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) :
    (rscl (ι := ι) p a x xo n).run = .seq (.named "rscl" [.cell a, .buf x, .idx xo, .idx n]
      (.seq (.loop n fun i =>
        .seq (.instr (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ a)) .skip) .skip)) .skip :=
  rfl

private theorem copyv_run (p : P) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    (copyv (ι := ι) p x xo y yo n).run = .seq (.named "copy"
      [.buf x, .idx xo, .buf y, .idx yo, .idx n]
      (.seq (.loop n fun i =>
        .seq (.instr (.copy p ⟨y, yo + .var i⟩ ⟨x, xo + .var i⟩)) .skip) .skip)) .skip := rfl

/-- The norm kernel executes the ordered dot product, then one square root in the same cell. -/
theorem run_nrm2 (p : P) (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) :
    (nrm2 (ι := ι) p dst x xo n).run = .seq (.named "nrm2" [.cell dst, .buf x, .idx xo, .idx n]
      (dot p dst x xo x xo n >>= fun _ => ins (.un p .sqrt dst dst)).run) .skip := rfl

/-- The program of `gemv`: zero $\mathbf{y}$, then add column $j$ of $\mathbf{A}$ times $x_j$
for each $j$, through one scratch cell. -/
theorem run_gemv (p : P) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) :
    (gemv (ι := ι) p m n A ao x xo y yo).run = .seq (.named "gemv"
      [.idx m, .idx n, .buf A, .idx ao, .buf x, .idx xo, .buf y, .idx yo]
      (.seq (.loop m fun i => .seq (.instr (.lit p ⟨y, yo + .var i⟩ 0)) .skip)
        (.alloc p 1 fun t => .seq (.loop n fun j => .seq (.loop m fun i =>
          .seq (.instr (.bin p .mul ⟨t, 0⟩ ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩))
            (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)) .skip))
          .skip) .skip))) .skip := rfl

/-- The program of `ger`: for each column $j$, multiply $\bar{y}_j$ by $a$, then add
$\mathbf{x}$ times it into column $j$ of $\mathbf{A}$, through two scratch cells. -/
theorem run_ger (p : P) (m n : IExp ℕ) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo : IExp ℕ) (A : ℕ) (ao : IExp ℕ) :
    (ger (ι := ι) p m n a x xo y yo A ao).run = .seq (.named "ger"
      [.idx m, .idx n, .cell a, .buf x, .idx xo, .buf y, .idx yo, .buf A, .idx ao]
      (.alloc p 2 fun t => .seq (.loop n fun j =>
        .seq (.instr (.un p .conj ⟨t, 0⟩ ⟨y, yo + .var j⟩))
        (.seq (.instr (.bin p .mul ⟨t, 0⟩ a ⟨t, 0⟩))
        (.seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨t, 1⟩ ⟨x, xo + .var i⟩ ⟨t, 0⟩))
          (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩
            ⟨A, ao + .var i + m * .var j⟩ ⟨t, 1⟩)) .skip)) .skip))) .skip)) .skip := rfl

/-- The program of `gemm`: one `gemv` call per column of $\mathbf{B}$ and $\mathbf{C}$. -/
theorem run_gemm (p : P) (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ) (bo : IExp ℕ)
    (C : ℕ) (co : IExp ℕ) :
    (gemm (ι := ι) p m n l A ao B bo C co).run = .seq (.named "gemm"
      [.idx m, .idx n, .idx l, .buf A, .idx ao, .buf B, .idx bo, .buf C, .idx co]
      (.seq (.loop l fun c => (gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)).run)
        .skip)) .skip := rfl

/-- The program of `trsvLower`: for each row $i$, subtract $t_{ij} x_j$ from $x_i$ for $j < i$
through one scratch cell, then divide by $t_{ii}$. -/
theorem run_trsvLower (p : P) (n : IExp ℕ) (T : ℕ) (tOff : IExp ℕ) (x : ℕ) (xo : IExp ℕ) :
    (trsvLower (ι := ι) p n T tOff x xo).run = .seq (.named "trsvLower"
      [.idx n, .buf T, .idx tOff, .buf x, .idx xo]
      (.alloc p 1 fun t => .seq (.loop n fun i => .seq (.loop (.var i) fun j =>
        .seq (.instr (.bin p .mul ⟨t, 0⟩ ⟨T, tOff + .var i + n * .var j⟩ ⟨x, xo + .var j⟩))
          (.seq (.instr (.bin p .sub ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ ⟨t, 0⟩)) .skip))
        (.seq (.instr (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩
          ⟨T, tOff + .var i + n * .var i⟩)) .skip)) .skip)) .skip := rfl

private theorem exists_foldlM_range_eq_some_of_le {α : Type} {g : α → ℕ → Option α} {a b : α}
    {n i : ℕ} (h : (List.range n).foldlM g a = some b) (hi : i ≤ n) :
    ∃ c, (List.range i).foldlM g a = some c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [List.range_add, List.foldlM_append] at h
  obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨c, hc⟩

end Runs

section Steps

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- One step of `dot`, from a store `s` with `v` written into `dst`. -/
private theorem exec_dot_step (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem) (p : P)
    {s : Store P 𝕜} {dst : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo : IExp ℕ} {t i : ℕ}
    {xi yi v : 𝕜} {si si' : Store P 𝕜} {st' : St P 𝕜 (OpCount P ι)} {arr : Array (Option 𝕜)}
    (hx : s.read p x (xo.eval + i) = some xi) (hy : s.read p y (yo.eval + i) = some yi)
    (hdx : dst.buf = x → dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → dst.idx.eval ≠ yo.eval + i) (ht : s.size = t)
    (hsi : s.write p dst.buf dst.idx.eval v = some si)
    (hsi' : s.write p dst.buf dst.idx.eval (v + star xi * yi) = some si')
    (harr : arr.size = 1) (hst : st'.store = si.push (p, arr)) :
    ∃ arr' : Array (Option 𝕜), arr'.size = 1 ∧
      exec I (.seq (.instr (.un p .conj ⟨t, 0⟩ ⟨x, xo + .var i⟩))
        (.seq (.instr (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨y, yo + .var i⟩))
          (.seq (.instr (.bin p .add dst dst ⟨t, 0⟩)) .skip))) st' =
      some { st' with
        store := si'.push (p, arr')
        cnt := st'.cnt + I.charge (.un p .conj) + I.charge (.bin p .mul) +
          I.charge (.bin p .add) } := by
  have hsz : si.size = t := by rw [← ht, Store.size_of_write_eq_some hsi]
  have hlt : ∀ {b j : ℕ} {w : 𝕜}, s.read p b j = some w → b < si.size := fun h => by
    rw [Store.size_of_write_eq_some hsi]; exact Store.lt_size_of_read_eq_some h
  have hdlt : dst.buf < si.size := by
    rw [Store.size_of_write_eq_some hsi]; exact Store.lt_size_of_write_eq_some hsi
  have r1 : ∀ arr' : Array (Option 𝕜), Store.read (si.push (p, arr')) p x (xo.eval + i) =
      some xi := by
    intro arr'
    rw [Store.read_push_of_lt (hlt hx), Store.read_of_write_eq_some_of_ne hsi, hx]
    by_cases h : x = dst.buf
    · exact Or.inr fun he => hdx h.symm he.symm
    · exact Or.inl h
  have r3 : ∀ arr' : Array (Option 𝕜), Store.read (si.push (p, arr')) p y (yo.eval + i) =
      some yi := by
    intro arr'
    rw [Store.read_push_of_lt (hlt hy), Store.read_of_write_eq_some_of_ne hsi, hy]
    by_cases h : y = dst.buf
    · exact Or.inr fun he => hdy h.symm he.symm
    · exact Or.inl h
  set a₁ := arr.set! 0 (some (star xi))
  set a₂ := a₁.set! 0 (some (star xi * yi))
  have h₁ : 0 < a₁.size := by simp [a₁, harr]
  have w3 : Store.write (si.push (p, a₂)) p dst.buf dst.idx.eval (v + star xi * yi) =
      some (si'.push (p, a₂)) := by
    rw [Store.write_push_of_lt hdlt, Store.write_of_write_eq_some hsi, hsi', Option.map_some]
  refine ⟨a₂, by simp [a₂, a₁, harr], (exec_seq_instr_un I (s := si.push (p, a₁))
      (by rw [hst]; exact r1 arr) (by rw [hI]; rfl)
      (by dsimp only [IExp.eval_zero]; rw [hst, ← hsz, Store.write_push_size (by omega)])).trans
    ((exec_seq_instr_bin I (s := si.push (p, a₂))
      (by dsimp only [IExp.eval_zero]; rw [← hsz];
          exact Store.read_push_size_set!_zero (by omega)) (r3 _)
      (by rw [hI]; rfl)
      (by dsimp only [IExp.eval_zero]; rw [← hsz, Store.write_push_size h₁])).trans
    ((exec_seq_instr_bin I
      (by rw [Store.read_push_of_lt hdlt]; exact Store.read_of_write_eq_some hsi)
      (by dsimp only [IExp.eval_zero]; rw [← hsz]; exact Store.read_push_size_set!_zero h₁)
      (by rw [hI]; rfl) w3).trans (exec_skip I _)))⟩

private theorem exec_axpy_step (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (p : P) {si si' : Store P 𝕜} {a : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo : IExp ℕ}
    {t i : ℕ} {av xi yi : 𝕜} {st' : St P 𝕜 (OpCount P ι)} {arr : Array (Option 𝕜)}
    (ha : si.read p a.buf a.idx.eval = some av) (hx : si.read p x (xo.eval + i) = some xi)
    (hy : si.read p y (yo.eval + i) = some yi) (ht : si.size = t)
    (hsi' : si.write p y (yo.eval + i) (av * xi + yi) = some si') (harr : arr.size = 1)
    (hst : st'.store = si.push (p, arr)) :
    ∃ arr' : Array (Option 𝕜), arr'.size = 1 ∧
      exec I (.seq (.instr (.bin p .mul ⟨t, 0⟩ a ⟨x, xo + .var i⟩))
        (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)) .skip)) st' =
      some { st' with
        store := si'.push (p, arr')
        cnt := st'.cnt + I.charge (.bin p .mul) + I.charge (.bin p .add) } := by
  set a₁ := arr.set! 0 (some (av * xi))
  have h₁ : 0 < a₁.size := by simp [a₁, harr]
  have hylt : y < si.size := Store.lt_size_of_read_eq_some hy
  refine ⟨a₁, by simp [a₁, harr], (exec_seq_instr_bin I (s := si.push (p, a₁))
      (by rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some ha)]; exact ha)
      (by rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some hx)]; exact hx)
      (by rw [hI]; rfl)
      (by dsimp only [IExp.eval_zero]; rw [hst, ← ht, Store.write_push_size (by omega)])).trans
    ((exec_seq_instr_bin I
      (by rw [Store.read_push_of_lt hylt]; exact hy)
      (by dsimp only [IExp.eval_zero]; rw [← ht]; exact Store.read_push_size_set!_zero (by omega))
      (by rw [hI]; exact congrArg some (add_comm _ _))
      (by rw [Store.write_push_of_lt hylt]; dsimp only [IExp.eval_add, IExp.eval_var];
          rw [hsi', Option.map_some])).trans (exec_skip I _))⟩

end Steps

/-! ### Specifications under exact arithmetic -/

section Specs

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]
  (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
  (hc : IsUnitCharge I) (p : P) (st : St P 𝕜 (OpCount P ι))

include hI hc

/-- **`dot` computes $\mathbf{x}^{\mathsf{H}}\mathbf{y}$** for every index expression of the
offsets and the length: if the cells of $\mathbf{x}$ and $\mathbf{y}$ hold $x_i$, $y_i$ for
$i < n$ and $\mathit{dst}$ is in neither, the run writes $\sum_{i<n} \bar{x}_i y_i$ into
$\mathit{dst}$ and nothing else, keeps the tape and the current memory, raises the peak by one
cell at tag $p$, and counts $n$ conjugations, multiplications and additions and one literal.
The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_dot (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ)
    (xs ys : ℕ → 𝕜) (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read p y (yo.eval + i) = some (ys i))
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i) (s₁ : Store P 𝕜)
    (h₁ : st.store.write p dst.buf dst.idx.eval
      (∑ i ∈ Finset.range n.eval, star (xs i) * ys i) = some s₁) :
    ∃ st', exec I (dot p dst x xo y yo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + (n.eval • (Finsupp.single (.un p .conj) 1 +
        Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1) +
        Finsupp.single (.lit p) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  set S : ℕ → 𝕜 := fun i => ∑ j ∈ Finset.range i, star (xs j) * ys j with hS
  have hw := Store.exists_write_eq_some_of_write_eq_some h₁
  obtain ⟨s0, hs0⟩ := hw ((0 : ℚ) : 𝕜)
  have hv0 : I.sem.lit p (0 : ℚ) = some ((0 : ℚ) : 𝕜) := by rw [hI]; rfl
  rw [run_dot, exec_seq_skip, exec_named, exec_seq_instr_lit I hv0 hs0, exec_alloc,
    exec_seq_skip]
  refine Option.exists_map_eq_some_of_exists (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜, ∃ arr : Array (Option 𝕜),
      st.store.write p dst.buf dst.idx.eval (S i) = some si ∧ arr.size = 1 ∧
      st'.store = si.push (p, arr) ∧ st'.cnt = st.cnt + I.charge (.lit p) +
        i • (I.charge (.un p .conj) + I.charge (.bin p .mul) + I.charge (.bin p .add)) ∧
      st'.pos = st.pos ∧ st'.cur = Function.update st.cur p (st.cur p + 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.curW = st.curW + 1 * I.width p ∧ st'.peakW = max st.peakW (st.curW + 1 * I.width p))
    ?_ ?_) ?_
  · exact ⟨s0, Array.replicate 1 none, by simpa [S] using hs0, by simp, rfl, by simp, rfl,
      by simp, by simp, by simp, by simp⟩
  · intro i hi st' ⟨si, arr, hsi, harr, hst, hcnt, hpos, hcur, hpeak, hcurW, hpeakW⟩
    obtain ⟨si', hsi'⟩ := hw (S (i + 1))
    have hsi'' := hsi'
    rw [show S (i + 1) = S i + star (xs i) * ys i from Finset.sum_range_succ _ _] at hsi''
    obtain ⟨arr', harr', hrun⟩ := exec_dot_step I hI p (hx i hi) (hy i hi)
      (fun h => hdx h i hi) (fun h => hdy h i hi) (Store.size_of_write_eq_some hs0).symm hsi
      hsi'' harr hst
    refine ⟨_, hrun, si', arr', hsi', harr', rfl, ?_, hpos, hcur, hpeak, hcurW, hpeakW⟩
    simp only [hcnt, succ_nsmul, add_assoc]
  · intro stL ⟨si, arr, hsi, harr, hst, hcnt, hpos, hcur, hpeak, hcurW, hpeakW⟩
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨by simp [hst, hsi₁], hpos, by simp [hcur], by simp [hcurW], ?_, hpeak,
      by simp [hpeakW]⟩
    simp only [hcnt, hc.charge_eq]
    abel

/-- **`axpy` computes $\mathbf{y} \leftarrow a\mathbf{x} + \mathbf{y}$ in place**: if $a$, the
$x_i$ and the $y_i$ ($i < n$) are stored, $a$ is not in $\mathbf{y}$, and $\mathbf{x}$ and
$\mathbf{y}$ are the same vector or do not overlap, the run writes $a x_i + y_i$ into the cells
of $\mathbf{y}$ and nothing else, keeps the tape and the current memory, raises the peak by one
cell, and counts $n$ multiplications and additions. The operation is in
[GolubVanLoan2013, §1.1]. -/
theorem exec_axpy (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (av : 𝕜)
    (xs ys : ℕ → 𝕜) (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read p y (yo.eval + i) = some (ys i))
    (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j)
    (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p y yo.eval
      ((List.range n.eval).toArray.map fun i => av * xs i + ys i) = some s₁) :
    ∃ st', exec I (axpy p a x xo y yo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • (Finsupp.single (.bin p .mul) 1 +
        Finsupp.single (.bin p .add) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  rw [Store.writeBlock_map_range] at h₁
  rw [run_axpy, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  refine Option.exists_map_eq_some_of_exists (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜, ∃ arr : Array (Option 𝕜),
      (List.range i).foldlM (fun s j => s.write p y (yo.eval + j) (av * xs j + ys j)) st.store =
        some si ∧ arr.size = 1 ∧
      st'.store = si.push (p, arr) ∧
      st'.cnt = st.cnt + i • (I.charge (.bin p .mul) + I.charge (.bin p .add)) ∧
      st'.pos = st.pos ∧ st'.cur = Function.update st.cur p (st.cur p + 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.curW = st.curW + 1 * I.width p ∧ st'.peakW = max st.peakW (st.curW + 1 * I.width p))
    ?_ ?_) ?_
  · exact ⟨st.store, Array.replicate 1 none, rfl, by simp, rfl, by simp, rfl, by simp, by simp,
      by simp, by simp⟩
  · intro i hi st' ⟨si, arr, hsi, harr, hst, hcnt, hpos, hcur, hpeak, hcurW, hpeakW⟩
    obtain ⟨si', hsi'⟩ := exists_foldlM_range_eq_some_of_le h₁ hi
    have hstep := hsi'
    rw [List.foldlM_range_succ, Option.bind_eq_bind, hsi, Option.bind_some] at hstep
    have hrd : ∀ {b j : ℕ}, (∀ k < i, b ≠ y ∨ j ≠ yo.eval + k) →
        si.read p b j = st.store.read p b j := fun h =>
      Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk =>
        h k (List.mem_range.mp hk)
    have ha' : si.read p a.buf a.idx.eval = some av := by
      rw [hrd fun k hk => ?_, ha]
      by_cases h : a.buf = y
      · exact Or.inr (hay h k (hk.trans hi))
      · exact Or.inl h
    have hx' : si.read p x (xo.eval + i) = some (xs i) := by
      rw [hrd fun k hk => ?_, hx i hi]
      by_cases h : x = y
      · exact Or.inr fun he => absurd (hxy h i hi k (hk.trans hi) he) (by omega)
      · exact Or.inl h
    have hy' : si.read p y (yo.eval + i) = some (ys i) := by
      rw [hrd fun k hk => Or.inr (by omega), hy i hi]
    obtain ⟨arr', harr', hrun⟩ := exec_axpy_step I hI p ha' hx' hy'
      (Store.size_of_foldlM_write_eq_some _ _ _ hsi) hstep harr hst
    refine ⟨_, hrun, si', arr', hsi', harr', rfl, ?_, hpos, hcur, hpeak, hcurW, hpeakW⟩
    simp only [hcnt, succ_nsmul, add_assoc]
  · intro stL ⟨si, arr, hsi, harr, hst, hcnt, hpos, hcur, hpeak, hcurW, hpeakW⟩
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨by simp [hst, hsi₁], hpos, by simp [hcur], by simp [hcurW], ?_, hpeak,
      by simp [hpeakW]⟩
    simp only [hcnt, hc.charge_eq]

/-- **`scal` computes $\mathbf{x} \leftarrow a\mathbf{x}$ in place**: if $a$ and the $x_i$
($i < n$) are stored and $a$ is not in $\mathbf{x}$, the run writes $a x_i$ into the cells of
$\mathbf{x}$ and nothing else, keeps the tape and the memory, and counts $n$ multiplications.
The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_scal (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (av : 𝕜) (xs : ℕ → 𝕜)
    (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hax : a.buf = x → ∀ i < n.eval, a.idx.eval ≠ xo.eval + i) (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p x xo.eval
      ((List.range n.eval).toArray.map fun i => av * xs i) = some s₁) :
    ∃ st', exec I (scal p a x xo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • Finsupp.single (.bin p .mul) 1 ∧
      st'.peak = st.peak ∧ st'.peakW = st.peakW := by
  rw [Store.writeBlock_map_range] at h₁
  rw [scal_run, exec_seq_skip, exec_named, exec_seq_skip]
  refine Exists.imp (fun stL h => ⟨h.1, ?_⟩) (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜,
      (List.range i).foldlM (fun s j => s.write p x (xo.eval + j) (av * xs j)) st.store =
        some si ∧ st' = { st with store := si, cnt := st.cnt + i • I.charge (.bin p .mul) })
    ⟨st.store, rfl, by simp⟩ ?_)
  · obtain ⟨-, si, hsi, rfl⟩ := h
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨hsi₁, rfl, rfl, rfl, by simp [hc.charge_eq], rfl, rfl⟩
  · rintro i hi _ ⟨si, hsi, rfl⟩
    obtain ⟨si', hsi'⟩ := exists_foldlM_range_eq_some_of_le h₁ hi
    have hstep := hsi'
    rw [List.foldlM_range_succ, Option.bind_eq_bind, hsi, Option.bind_some] at hstep
    have hrd : ∀ {b j : ℕ}, (∀ k < i, b ≠ x ∨ j ≠ xo.eval + k) →
        si.read p b j = st.store.read p b j := fun h =>
      Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk =>
        h k (List.mem_range.mp hk)
    have ha' : si.read p a.buf a.idx.eval = some av := by
      rw [hrd fun k hk => ?_, ha]
      by_cases h : a.buf = x
      · exact Or.inr (hax h k (hk.trans hi))
      · exact Or.inl h
    have hx' : si.read p x (xo.eval + i) = some (xs i) := by
      rw [hrd fun k hk => Or.inr (by omega), hx i hi]
    refine ⟨_, (exec_seq_instr_bin I ha' hx' (by rw [hI]; rfl) hstep).trans (exec_skip I _),
      si', hsi', ?_⟩
    rw [succ_nsmul, ← add_assoc]

/-- **`rscl` computes $\mathbf{x} \leftarrow \mathbf{x}/a$ in place**: if $a \ne 0$ and the
$x_i$ ($i < n$) are stored and $a$ is not in $\mathbf{x}$, the run writes $x_i/a$ into the cells
of $\mathbf{x}$ and nothing else, keeps the tape and the memory, and counts $n$ divisions.
The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_rscl (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (av : 𝕜) (xs : ℕ → 𝕜) (hav : av ≠ 0)
    (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hax : a.buf = x → ∀ i < n.eval, a.idx.eval ≠ xo.eval + i) (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p x xo.eval
      ((List.range n.eval).toArray.map fun i => xs i / av) = some s₁) :
    ∃ st', exec I (rscl p a x xo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • Finsupp.single (.bin p .div) 1 ∧
      st'.peak = st.peak ∧ st'.peakW = st.peakW := by
  rw [Store.writeBlock_map_range] at h₁
  rw [run_rscl, exec_seq_skip, exec_named, exec_seq_skip]
  refine Exists.imp (fun stL h => ⟨h.1, ?_⟩) (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜,
      (List.range i).foldlM (fun s j => s.write p x (xo.eval + j) (xs j / av)) st.store =
        some si ∧ st' = { st with store := si, cnt := st.cnt + i • I.charge (.bin p .div) })
    ⟨st.store, rfl, by simp⟩ ?_)
  · obtain ⟨-, si, hsi, rfl⟩ := h
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨hsi₁, rfl, rfl, rfl, by simp [hc.charge_eq], rfl, rfl⟩
  · rintro i hi _ ⟨si, hsi, rfl⟩
    obtain ⟨si', hsi'⟩ := exists_foldlM_range_eq_some_of_le h₁ hi
    have hstep := hsi'
    rw [List.foldlM_range_succ, Option.bind_eq_bind, hsi, Option.bind_some] at hstep
    have hrd : ∀ {b j : ℕ}, (∀ k < i, b ≠ x ∨ j ≠ xo.eval + k) →
        si.read p b j = st.store.read p b j := fun h =>
      Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk =>
        h k (List.mem_range.mp hk)
    have ha' : si.read p a.buf a.idx.eval = some av := by
      rw [hrd fun k hk => ?_, ha]
      by_cases h : a.buf = x
      · exact Or.inr (hax h k (hk.trans hi))
      · exact Or.inl h
    have hx' : si.read p x (xo.eval + i) = some (xs i) := by
      rw [hrd fun k hk => Or.inr (by omega), hx i hi]
    refine ⟨_, (exec_seq_instr_bin I hx' ha' (by rw [hI]; simp [exactSem, hav]) hstep).trans
      (exec_skip I _), si', hsi', ?_⟩
    rw [succ_nsmul, ← add_assoc]

omit [RCLike 𝕜] hI in
/-- **`copy` copies $\mathbf{x}$ into $\mathbf{y}$**: if the $x_i$ ($i < n$) are stored and the
two vectors are the same or do not overlap, the run writes $x_i$ into the cells of $\mathbf{y}$
and nothing else, keeps the tape and the memory, and counts $n$ copies. The operation is in
[GolubVanLoan2013, §1.1]. -/
theorem exec_copyv (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (xs : ℕ → 𝕜)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j)
    (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map xs) = some s₁) :
    ∃ st', exec I (copyv p x xo y yo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • Finsupp.single (.copy p) 1 ∧
      st'.peak = st.peak ∧ st'.peakW = st.peakW := by
  rw [Store.writeBlock_map_range] at h₁
  rw [copyv_run, exec_seq_skip, exec_named, exec_seq_skip]
  refine Exists.imp (fun stL h => ⟨h.1, ?_⟩) (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜,
      (List.range i).foldlM (fun s j => s.write p y (yo.eval + j) (xs j)) st.store =
        some si ∧ st' = { st with store := si, cnt := st.cnt + i • I.charge (.copy p) })
    ⟨st.store, rfl, by simp⟩ ?_)
  · obtain ⟨-, si, hsi, rfl⟩ := h
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨hsi₁, rfl, rfl, rfl, by simp [hc.charge_eq], rfl, rfl⟩
  · rintro i hi _ ⟨si, hsi, rfl⟩
    obtain ⟨si', hsi'⟩ := exists_foldlM_range_eq_some_of_le h₁ hi
    have hstep := hsi'
    rw [List.foldlM_range_succ, Option.bind_eq_bind, hsi, Option.bind_some] at hstep
    have hx' : si.read p x (xo.eval + i) = some (xs i) := by
      rw [Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk => ?_, hx i hi]
      by_cases h : x = y
      · exact Or.inr fun he =>
          absurd (hxy h i hi k ((List.mem_range.mp hk).trans hi) he)
            (by have := List.mem_range.mp hk; omega)
      · exact Or.inl h
    refine ⟨_, (exec_seq_instr_copy I hx' hstep).trans (exec_skip I _), si', hsi', ?_⟩
    rw [succ_nsmul, ← add_assoc]

/-- **`nrm2` computes $\|\mathbf{x}\|$**: if the $x_i$ ($i < n$) are stored and $\mathit{dst}$ is
not in $\mathbf{x}$, the run writes $\bigl(\sum_{i<n} \bar{x}_i x_i\bigr)^{1/2}$ into
$\mathit{dst}$ and nothing else, keeps the tape and the current memory, raises the peak by one
cell, and counts $n$ conjugations, multiplications and additions, one literal and one square
root. The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_nrm2 (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (xs : ℕ → 𝕜)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i) (s₁ : Store P 𝕜)
    (h₁ : st.store.write p dst.buf dst.idx.eval
      ((√(RCLike.re (∑ i ∈ Finset.range n.eval, star (xs i) * xs i)) : ℝ) : 𝕜) = some s₁) :
    ∃ st', exec I (nrm2 p dst x xo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + (n.eval • (Finsupp.single (.un p .conj) 1 +
        Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1) +
        Finsupp.single (.lit p) 1 + Finsupp.single (.un p .sqrt) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  obtain ⟨s₀, hs₀⟩ := Store.exists_write_eq_some_of_write_eq_some h₁
    (∑ i ∈ Finset.range n.eval, star (xs i) * xs i)
  obtain ⟨st₁, h1, hs1, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_dot I hI hc p st dst x xo x xo n xs xs hx hx hdx hdx s₀ hs₀
  have hnn : (0 : 𝕜) ≤ ∑ i ∈ Finset.range n.eval, star (xs i) * xs i :=
    Finset.sum_nonneg fun i _ => star_mul_self_nonneg (xs i)
  have hv : I.sem.un p .sqrt (∑ i ∈ Finset.range n.eval, star (xs i) * xs i) =
      some ((√(RCLike.re (∑ i ∈ Finset.range n.eval, star (xs i) * xs i)) : ℝ) : 𝕜) := by
    rw [hI]; exact if_pos hnn
  rw [run_nrm2, exec_seq_skip, exec_named, exec_run_bind I (b := dot p dst x xo x xo n)
    (fun _ => rfl), h1, Option.bind_some]
  refine ⟨_, (exec_seq_instr_un I (by rw [hs1]; exact Store.read_of_write_eq_some hs₀) hv
    (by rw [hs1, Store.write_of_write_eq_some hs₀]; exact h₁)).trans (exec_skip I _), rfl, hpos,
    hcur, hcurW, ?_, hpeak, hpeakW⟩
  simp only [hcnt, hc.charge_eq, add_assoc]

end Specs

/-! ### Loops of kernels -/

section Loops

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- A loop of `dot` calls accumulated into one cell: for $j < n$, the program computes the dot
product of column $c_0 + j$ of the $N$-row buffers `B` and `C` (the cells from $N(c_0 + j)$)
into the scratch cell `t[0]` and adds it into `acc`. If these columns hold $\mathbf{u}_j$ and
$\mathbf{v}_j$ and `acc` holds $a_0$, the run leaves
$a_0 + \sum_{j<n} \mathbf{u}_j^{\mathsf{H}}\mathbf{v}_j$ in `acc`, changes no other cell outside
the scratch buffer, keeps the shape, the tape and the current memory, raises the peaks by at
most one cell at tag $p$, and counts $n$ dot products of length $N$ and $n$ additions. With
$\mathbf{v}_j = \mathbf{A}\mathbf{u}_j$ it accumulates a trace
$\operatorname{tr}(\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U})$. -/
theorem exec_forRange_dot_add (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) {N : ℕ} (B C t : ℕ) (acc : Cell ℕ ℕ)
    (n : IExp ℕ) (colE : ℕ → IExp ℕ) (c0 : ℕ) (hcol : ∀ j, (colE j).eval = N * (c0 + j))
    (u v : ℕ → Fin N → 𝕜) (st : St P 𝕜 (OpCount P ι)) (a0 : 𝕜)
    (hB : ∀ j < n.eval, ∀ a : Fin N, st.store.read p B (N * (c0 + j) + a) = some (u j a))
    (hC : ∀ j < n.eval, ∀ a : Fin N, st.store.read p C (N * (c0 + j) + a) = some (v j a))
    (hacc : st.store.read p acc.buf acc.idx.eval = some a0) (htB : t ≠ B) (htC : t ≠ C)
    (haB : acc.buf ≠ B) (haC : acc.buf ≠ C) (hat : acc.buf = t → acc.idx.eval ≠ 0)
    (ht : ∃ s, st.store.write p t 0 0 = some s) :
    ∃ st', exec I (forRange n fun j => dot p ⟨t, 0⟩ B (colE j) C (colE j) (.const N) >>=
        fun _ => ins (.bin p .add acc acc ⟨t, 0⟩)).run st = some st' ∧
      st'.store.read p acc.buf acc.idx.eval =
        some (a0 + ∑ j ∈ Finset.range n.eval, star (u j) ⬝ᵥ v j) ∧
      (∀ q b i, b ≠ t → (b = acc.buf → i ≠ acc.idx.eval) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.bin p .add) 1) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p) := by
  rw [show (forRange (ι := ι) n fun j => dot p ⟨t, 0⟩ B (colE j) C (colE j) (.const N) >>=
      fun _ => ins (.bin p .add acc acc ⟨t, 0⟩)).run = .seq (.loop n fun j =>
        (dot p ⟨t, 0⟩ B (colE j) C (colE j) (.const N) >>=
          fun _ => ins (.bin p .add acc acc ⟨t, 0⟩)).run) .skip from rfl, exec_seq_skip]
  obtain ⟨s₀, hs₀⟩ := ht
  refine exists_exec_loop_eq_some_of_forall I (fun j st' =>
      st'.store.read p acc.buf acc.idx.eval =
        some (a0 + ∑ j' ∈ Finset.range j, star (u j') ⬝ᵥ v j') ∧
      (∀ q b i, b ≠ t → (b = acc.buf → i ≠ acc.idx.eval) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧ st'.cur = st.cur ∧
      st'.curW = st.curW ∧
      st'.cnt = st.cnt + j • (N • (Finsupp.single (OpKind.un p .conj) 1 +
        Finsupp.single (OpKind.bin p .mul) 1 + Finsupp.single (OpKind.bin p .add) 1) +
        Finsupp.single (OpKind.lit p) 1 + Finsupp.single (OpKind.bin p .add) 1) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p))
    ⟨by simpa using hacc, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl, by simp, fun q => by
      by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq], le_max_left _ _⟩ ?_
  intro j hj st' ⟨hacc', hfr, hsh, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  set xs : ℕ → 𝕜 := fun a => if h : a < N then u j ⟨a, h⟩ else 0
  set ys : ℕ → 𝕜 := fun a => if h : a < N then v j ⟨a, h⟩ else 0
  have hsum : ∑ a ∈ Finset.range N, star (xs a) * ys a = star (u j) ⬝ᵥ v j := by
    rw [← Fin.sum_univ_eq_sum_range (fun a => star (xs a) * ys a)]
    simp [xs, ys, dotProduct]
  obtain ⟨s1, hs1⟩ := Store.exists_write_eq_some_of_shape_eq hsh hs₀
    (∑ a ∈ Finset.range N, star (xs a) * ys a)
  obtain ⟨st1, h1, hst1, hpos1, hcur1, hcurW1, hcnt1, hpeak1, hpeakW1⟩ :=
    exec_dot I hI hc p st' ⟨t, 0⟩ B (colE j) C (colE j) (.const N) xs ys
      (fun a (ha : a < N) => by
        rw [hcol, hfr p B _ (Ne.symm htB) (fun h => absurd h.symm haB), hB j hj ⟨a, ha⟩]
        simp [xs, ha])
      (fun a (ha : a < N) => by
        rw [hcol, hfr p C _ (Ne.symm htC) (fun h => absurd h.symm haC), hC j hj ⟨a, ha⟩]
        simp [ys, ha])
      (fun h => absurd h htB) (fun h => absurd h htC) s1 hs1
  have hacc1 : s1.read p acc.buf acc.idx.eval =
      some (a0 + ∑ j' ∈ Finset.range j, star (u j') ⬝ᵥ v j') := by
    rw [Store.read_of_write_eq_some_of_ne hs1 (by
      by_cases h : acc.buf = t
      · exact Or.inr (hat h)
      · exact Or.inl h), hacc']
  obtain ⟨s2, hs2⟩ := Store.exists_write_eq_some_of_read_eq_some
    (v := a0 + ∑ j' ∈ Finset.range (j + 1), star (u j') ⬝ᵥ v j') hacc1
  have hv : I.sem.bin p .add (a0 + ∑ j' ∈ Finset.range j, star (u j') ⬝ᵥ v j')
      (∑ a ∈ Finset.range N, star (xs a) * ys a) =
      some (a0 + ∑ j' ∈ Finset.range (j + 1), star (u j') ⬝ᵥ v j') := by
    rw [hI, Finset.sum_range_succ, ← add_assoc, hsum]; rfl
  rw [exec_run_bind I (b := dot p ⟨t, 0⟩ B (colE j) C (colE j) (.const N)) (fun _ => rfl), h1,
    Option.bind_some]
  refine ⟨_, (exec_seq_instr_bin I (by rw [hst1]; exact hacc1)
    (by rw [hst1]; exact Store.read_of_write_eq_some hs1) hv
    (by rw [hst1]; exact hs2)).trans (exec_skip I _), Store.read_of_write_eq_some hs2,
    fun q b i hbt hba => ?_, ?_, hpos1.trans hpos, hcur1.trans hcur, hcurW1.trans hcurW, ?_,
    ?_, ?_⟩
  · change s2.read q b i = _
    rw [Store.read_of_write_eq_some_of_ne hs2 (by
        by_cases h : b = acc.buf
        · exact Or.inr (hba h)
        · exact Or.inl h),
      Store.read_of_write_eq_some_of_ne hs1 (Or.inl hbt), hfr q b i hbt hba]
  · change s2.shape = _
    rw [Store.shape_of_write_eq_some hs2, Store.shape_of_write_eq_some hs1, hsh]
  · change st1.cnt + I.charge (.bin p .add) = _
    simp only [hcnt1, hcnt, hc.charge_eq, IExp.eval_const, succ_nsmul, add_assoc]
  · change st1.peak ≤ _
    rw [hpeak1, hcur]
    exact Function.update_max_le_update_max hpeak
  · change st1.peakW ≤ _
    rw [hpeakW1, hcurW]
    exact max_le hpeakW (le_max_right _ _)

end Loops

end NLAlib.Computation
