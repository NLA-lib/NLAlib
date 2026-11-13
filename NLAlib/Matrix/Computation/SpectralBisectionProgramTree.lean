/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.NewtonSchulzSignProgramTree

/-!
# Randomized spectral bisection as a program: the builder and the registered tree

Randomized spectral bisection ([Shah2024, Algorithm 3]), as the shallow `NLAlib.eigh` computes it
on a floating-point machine, written as a builder over memory buffers (`NLAlib.eighProg`) and
compiled once at symbolic sizes into one first-order tree (`NLAlib.eighProg.compiled`). Every
operation on data is an instruction of the model, a counted comparison, a call of the black-box
kernels `mm` and `qr` (`NLAlib.Computation.Stmt.kcall`) or a conversion of a stored value to an
index (`NLAlib.Computation.Stmt.bindIdx`); complex matrices are interleaved pairs of real words and
the entrywise steps are the complex kernels of `NLAlib/Computation/BLAS.lean`; the sign step is
inlined at each node from the test and step blocks of the Newton–Schulz program
(`NLAlib.newtonSchulzTestBlock`, `NLAlib.newtonSchulzStepBlock`) with the step limit of the
shallow loop (`NLAlib.eighSignBlock`), so the run never fails for want of sign steps.

The recursion runs **level by level** (design note `docs/design/Computation-EighProgram.md`):
the nodes at one depth $d$ partition $[0, n)$ into contiguous ranges $[lo, lo + k)$, and a node of
size $k$ at $lo$ keeps its $k \times k$ matrix packed at word offset $2n^2 d + 2nlo$ of the level
arenas (so the blocks of the nodes of one level are disjoint, $k^2 \le kn$). A downward loop over
the depths $d < D = \ell_0 + 1$ draws the samples of the level, reads each slot's stored size
with an index binder, and runs the node step on every node: a leaf writes its output, a node with
one child writes the shifted matrix at the same slot of level $d + 1$, a split writes the two
bases and the two compressions at the slots $lo$ and $lo + k_+$ of level $d + 1$, with its kind
and $k_+$ stored for the way back. The nodes left at depth $D$ get the junk output
$(\mathbf{I}, \mathbf{0})$ of the spent budget. An upward loop over the depths assembles each
node's output from its children's: $[\mathrm{mm}(\mathbf{Q}_+, \mathbf{U}_+)\
\mathrm{mm}(\mathbf{Q}_-, \mathbf{U}_-)]$ and the rounded shifted eigenvalues.

Sizes, kinds and $k_+$ are stored as integer literals and read back by index binders; tests on
sizes are loops whose trip count is $0$ or $1$ by index arithmetic (`NLAlib.eighWhen`), so no
comparison of stored sizes is needed. **The samples are static**: every level $d$ draws exactly
$n$ uniform and $4n^2$ Gaussian values, so the node at $(d, lo)$ reads its seed at uniform tape
position $nd + lo$ and its two Gaussian test matrices at fixed positions
(`NLAlib.eighTapeSample`), whatever the data.

## Main definitions

* `NLAlib.eighWhen`, `NLAlib.eighEqInd`: control by index arithmetic.
* `NLAlib.eighSignBlock`: the Newton–Schulz sign with the shallow step limit.
* `NLAlib.eighLeafBlock`, `NLAlib.eighChildBlock`, `NLAlib.eighDeflateBlock`,
  `NLAlib.eighCompressBlock`, `NLAlib.eighSplitBlock`, `NLAlib.eighClampBlock`,
  `NLAlib.eighNodeBlock`: the node step.
* `NLAlib.eighDownLevel`, `NLAlib.eighBottomLevel`, `NLAlib.eighUpLevel`: one level of each pass,
  and the nodes whose budget is spent.
* `NLAlib.eighProg`: randomized spectral bisection as a program.
* `NLAlib.eighProg.compiled`: its registered tree.
* `NLAlib.eighScalarKinds`, `NLAlib.eighCount`: an upper bound on its counts.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

variable {P ι VB VI : Type}

/-! ### Control by index arithmetic -/

/-- **Run a block when an index expression is positive**: a loop over the indices below
$1 - (1 - e)$ (truncated subtraction), which is $1$ when $e \ge 1$ and $0$ otherwise; no
comparison of stored values. -/
def eighWhen (e : IExp VI) (b : Builder P ι VB VI Unit) : Builder P ι VB VI Unit :=
  forRange (1 - (1 - e)) fun _ => b

/-- The indicator of $c = m$ by index arithmetic: $(1 - (c - m))(1 - (m - c))$, truncated
subtraction, which is $1$ if $c = m$ and $0$ otherwise. -/
def eighEqInd (c m : IExp VI) : IExp VI := (1 - (c - m)) * (1 - (m - c))

/-! ### The layout -/

/-- The word offset of the node block at depth $d$ and slot $lo$ in an arena of complex
$n \times n$ blocks, one per level: $2n^2 d + 2n\,lo$. -/
def eighBlockOff (n d lo : IExp VI) : IExp VI := 2 * (n * n) * d + 2 * n * lo

/-- The cell of slot $lo$ at depth $d$ in an arena of $n$ cells per level: $nd + lo$. -/
def eighSlotOff (n d lo : IExp VI) : IExp VI := n * d + lo

/-- The evaluated matrix-arena offset is the level stride $2n^2$ plus the slot stride
$2n$, using the values of the three index expressions. No printed source. -/
theorem eval_eighBlockOff (n d lo : IExp ℕ) :
    (eighBlockOff n d lo).eval = 2 * (n.eval * n.eval) * d.eval + 2 * n.eval * lo.eval := rfl

/-- The evaluated scalar-arena offset is the level stride $n$ plus the slot, using the values
of the three index expressions. No printed source. -/
theorem eval_eighSlotOff (n d lo : IExp ℕ) :
    (eighSlotOff n d lo).eval = n.eval * d.eval + lo.eval := rfl

/-! ### The sign step with the shallow step limit -/

/-- **The Newton–Schulz sign algorithm with the step limit of the shallow loop**: the set-up and
the test of `NLAlib.newtonSchulzSignProg` ($\eta = \mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$
from the stored $\varepsilon$, $b$ in the cells `po`, `po + 1` of `par`, $\mathbf{X}_0 =
\mathbf{A}/b$ stored Hermitian at `X` from `xo`, `NLAlib.newtonSchulzTestBlock`), then $F$ times:
if the flag says the test failed (one counted comparison), the rounded step
(`NLAlib.newtonSchulzStepBlock`) and the test of the new iterate. It never fails for want of steps:
it ends with the first iterate that passes among the first $F$, or the $F$-th, as
`NLAlib.newtonSchulzLoop` does, where `NLAlib.newtonSchulzSignProg`'s `whileFuel` fails. Scratch:
five cells and two $n \times n$ complex matrices (`scope`). [Shah2024, Algorithm 1], as
`NLAlib.newtonSchulzSign` with step limit $F$. -/
def eighSignBlock (p : P) (mm : ι) (n F : IExp VI) (A : VB) (ao : IExp VI) (par : VB)
    (po : IExp VI) (X : VB) (xo : IExp VI) : Builder P ι VB VI Unit := scope do
  -- t: 0 the threshold η, 1 the flag, 2 a literal, 3 the stored one, 4 the negated threshold
  let t ← alloc p 5
  let W ← alloc p (2 * (n * n))
  let V ← alloc p (2 * (n * n))
  ins (.litIdx p ⟨t, 2⟩ (4 * n))
  ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
  ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
  ins (.lit p ⟨t, 3⟩ 1)
  zhermScale p n A ao ⟨par, po + 1⟩ X xo
  newtonSchulzTestBlock p mm n X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
  forRange F fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
    (do
      newtonSchulzStepBlock p mm n X xo W V ⟨t, 2⟩
      newtonSchulzTestBlock p mm n X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
    (pure ())

/-! ### The node step -/

/-- **A leaf**: the stored identity as the node's $\mathbf{U}$ (`zidentity`) in the block at `uo`
of `Ua`, the eigenvalues at `eo` of `Ea` either the real parts of the diagonal of the node matrix
at `mo` of `Ma` (`diag`, a leaf of size at most $1$) or the literal $0$ (a leaf by the window
test), and the kind $1$ in the cell `kd`. -/
def eighLeafBlock (p : P) (diag : Bool) (k : IExp VI) (Ma : VB) (mo : IExp VI) (Ua : VB)
    (uo : IExp VI) (Ea : VB) (eo : IExp VI) (kd : Cell VB VI) : Builder P ι VB VI Unit := do
  zidentity p k Ua uo
  forRange k fun i =>
    if diag then ins (.copy p ⟨Ea, eo + .var i⟩ ⟨Ma, mo + zidx k (.var i) (.var i)⟩)
    else ins (.lit p ⟨Ea, eo + .var i⟩ 0)
  ins (.litIdx p kd 1)

/-- **One child on the same slot**: the node matrix at `mo` of `Ma` shifted by the stored
$\sigma$ in the cell `sg` (`zhermShift`) into the block at `mo'`, its size $k$ in the cell `sz'`
of the next level and the kind `code` ($2$ for the positive side, $3$ for the negative) in `kd`. -/
def eighChildBlock (p : P) (k : IExp VI) (Ma : VB) (mo mo' : IExp VI) (sg sz' kd : Cell VB VI)
    (code : ℕ) : Builder P ι VB VI Unit := do
  zhermShift p k Ma mo sg Ma mo'
  ins (.litIdx p sz' k)
  ins (.litIdx p kd (.const code))

/-- **Randomized deflation on stored samples**: the complex $k \times k$ test matrix
$\widetilde{\mathbf{G}}$ in `G` from the Gaussian words of the level in `Sg` (entry $(i, j)$ from
the words $2(n(2(lo + j) + s) + i)$ and the next, each times the stored $\sqrt{1/2}$ in `sq`),
$\mathbf{Y} = \mathrm{mm}(\mathbf{P}, \widetilde{\mathbf{G}})$ and $(\mathbf{Q}, \mathbf{R}) =
\mathrm{qr}(\mathbf{Y})$ by kernel calls, and the first $r$ columns of $\mathbf{Q}$ at `qo` of `Qa`:
`NLAlib.deflate` on the samples of side $s$ ($0$ positive, $1$ negative). -/
def eighDeflateBlock (p : P) (mm qr : ι) (n k r lo : IExp VI) (side : ℕ) (Sg : VB)
    (sq : Cell VB VI) (Pm G Y Qf Rf Qa : VB) (qo : IExp VI) : Builder P ι VB VI Unit := do
  forRange k fun j => forRange k fun i => do
    ins (.bin p .mul ⟨G, zidx k (.var i) (.var j)⟩
      ⟨Sg, 2 * (n * (2 * (lo + .var j) + .const side) + .var i)⟩ sq)
    ins (.bin p .mul ⟨G, zidx k (.var i) (.var j) + 1⟩
      ⟨Sg, 2 * (n * (2 * (lo + .var j) + .const side) + .var i) + 1⟩ sq)
  stmt (.kcall mm p [k, k, k] [(Pm, 0), (G, 0)] [(Y, 0)])
  stmt (.kcall qr p [k, k] [(Y, 0)] [(Qf, 0), (Rf, 0)])
  zcopy p k r Qf 0 Qa qo

/-- **A compression**: for the stored $k \times r$ basis $\mathbf{Q}$ at `qo` of `Qa` and the node
matrix $\mathbf{A}$ at `mo` of `Ma`, the stored Hermitian
$(\mathbf{C} + \mathbf{C}^{\mathsf{H}})/\mathrm{fl}(2) - \sigma\mathbf{I}$ with
$\mathbf{C} = \mathrm{mm}(\mathrm{mm}(\mathbf{Q}^{\mathsf{H}}, \mathbf{A}), \mathbf{Q})$, written
at `co` of `Ma`; $\mathbf{Q}^{\mathsf{H}}$ by `zconjTranspose`, the products by kernel calls,
`two` and `sg` the cells of $\mathrm{fl}(2)$ and $\sigma$. -/
def eighCompressBlock (p : P) (mm : ι) (k r : IExp VI) (Qa : VB) (qo : IExp VI) (Ma : VB)
    (mo co : IExp VI) (two sg : Cell VB VI) (Qh C1 C2 C3 : VB) : Builder P ι VB VI Unit := do
  zconjTranspose p k r Qa qo Qh 0
  stmt (.kcall mm p [r, k, k] [(Qh, 0), (Ma, mo)] [(C1, 0)])
  stmt (.kcall mm p [r, k, r] [(C1, 0), (Qa, qo)] [(C2, 0)])
  zhermAvg p r C2 0 two C3 0
  zhermShift p r C3 0 sg Ma co

/-- **A split** at the slot $lo$ of depth $d$ into $k_+$ and $k - k_+$: with the stored
$\sqrt{1/2}$ read from the cell `sq` (computed once by `NLAlib.eighProg`, never written here), the
bases
$\mathbf{Q}_\pm$ (`NLAlib.eighDeflateBlock`, sides $0$ and $1$) packed at the node's block `qo` of
`Qa` ($\mathbf{Q}_-$ after the $2k k_+$ words of $\mathbf{Q}_+$), the compressions
(`NLAlib.eighCompressBlock`, shifts $\sigma$ and $-\sigma$) at the blocks of the slots $lo$ and
$lo + k_+$ of depth $d + 1$, their sizes, the kind $4$ and $k_+$. -/
def eighSplitBlock (p : P) (mm qr : ι) (n d lo k kp : IExp VI) (Sg : VB) (Pp Pm : VB)
    (Ma Qa Sz Kd Kp : VB) (two sg nsg sq : Cell VB VI) : Builder P ι VB VI Unit := scope do
  let G ← alloc p (2 * (n * n))
  let Y ← alloc p (2 * (n * n))
  let Qf ← alloc p (2 * (n * n))
  let Rf ← alloc p (2 * (n * n))
  let Qh ← alloc p (2 * (n * n))
  let C1 ← alloc p (2 * (n * n))
  let C2 ← alloc p (2 * (n * n))
  let C3 ← alloc p (2 * (n * n))
  let qo := eighBlockOff n d lo
  eighDeflateBlock p mm qr n k kp lo 0 Sg sq Pp G Y Qf Rf Qa qo
  eighDeflateBlock p mm qr n k (k - kp) lo 1 Sg sq Pm G Y Qf Rf Qa (qo + 2 * (k * kp))
  eighCompressBlock p mm k kp Qa qo Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) two sg
    Qh C1 C2 C3
  eighCompressBlock p mm k (k - kp) Qa (qo + 2 * (k * kp)) Ma (eighBlockOff n d lo)
    (eighBlockOff n (d + 1) (lo + kp)) two nsg Qh C1 C2 C3
  ins (.litIdx p ⟨Sz, eighSlotOff n (d + 1) lo⟩ kp)
  ins (.litIdx p ⟨Sz, eighSlotOff n (d + 1) (lo + kp)⟩ (k - kp))
  ins (.litIdx p ⟨Kd, eighSlotOff n d lo⟩ 4)
  ins (.litIdx p ⟨Kp, eighSlotOff n d lo⟩ kp)

/-- **The clamp of a split index to $[0, k]$** by counted instructions: the literals $0$ and $k$
into the cells `z` and `kc`, then two comparisons: if $x < 0$ the cell `x` gets the stored $0$,
if $k \le x$ it gets the stored $k$, and otherwise it is kept. With exact comparisons, literals and
conversion, the conversion of the clamped cell is $\min(k, \lfloor x\rfloor_+)$, and it never
fails nor exceeds $k$: the index binder that reads it (`NLAlib.Computation.Stmt.bindIdx`, which
fails on a negative value or one above its bound) always receives a value in range. -/
def eighClampBlock (p : P) (k : IExp VI) (x z kc : Cell VB VI) : Builder P ι VB VI Unit := do
  ins (.lit p z 0)
  ins (.litIdx p kc k)
  ifThenElse p .le z x
    (ifThenElse p .le kc x (ins (.copy p x kc)) (pure ()))
    (ins (.copy p x z))

/-- **The node step** at the slot $lo$ of depth $d$ for a node of size $k \ge 2$ whose window
test fails ([Shah2024, Algorithm 3], one node, as `NLAlib.eighStep`): the stored $\sigma =
\mathrm{fl}(R/\mathrm{fl}(2))$ and $-\sigma$; the shift $c = \mathrm{fl}(\mathrm{fl}(R/\ell)v)$
from the node's uniform draw $v$ (cell $lo$ of `Su`), $\ell = \ell_0 + d$; $\mathbf{W} =
\mathbf{A} - c\mathbf{I}$ stored Hermitian; its Newton–Schulz sign $\mathbf{B}$ at the stored
accuracy $\beta$ (cell $2$ of `par`) and scale $\mathrm{fl}(\mathrm{fl}(2)R)$
(`NLAlib.eighSignBlock`, step limit $F$); the projectors
$\mathbf{P}_+ = (\mathbf{B} - (-1)\mathbf{I})/\mathrm{fl}(2)$ and
$\mathbf{P}_- = -(\mathbf{B} - \mathbf{I})/\mathrm{fl}(2)$ stored Hermitian; the rounded trace
$t$ of $\mathbf{P}_+$, $\mathrm{fl}(t + \mathrm{fl}(1/2))$ clamped to $[0, k]$ by two comparisons
(`NLAlib.eighClampBlock`, in the dead cells $2$ and $3$) and
$k_+ = \min(\lfloor\mathrm{fl}(t + \mathrm{fl}(1/2))\rfloor_+, k)$ read by an index binder;
then one child on the positive side if $k_+ = k$, on the negative side if $k_+ = 0$, and a split
otherwise (`NLAlib.eighChildBlock`, `NLAlib.eighSplitBlock`, with the stored $\sqrt{1/2}$ of the
cell `sqh`). -/
def eighNodeBlock (p : P) (mm qr : ι) (n L F d lo k : IExp VI) (par Lv Su Sg Ma Qa Sz Kd Kp : VB)
    (one two half negone sqh : Cell VB VI) : Builder P ι VB VI Unit := scope do
  -- t: 0 σ, 1 −σ, 2 ℓ, 3 R/ℓ, 4 c, 5 the trace, 6 t + 1/2; then 2 the literal 0, 3 the literal k
  -- and 6 the clamped t + 1/2
  let t ← alloc p 7
  -- sp: 0 β, 1 fl(2R), the parameters of the sign program
  let sp ← alloc p 2
  let W ← alloc p (2 * (n * n))
  let B ← alloc p (2 * (n * n))
  let T ← alloc p (2 * (n * n))
  let Pp ← alloc p (2 * (n * n))
  let Pm ← alloc p (2 * (n * n))
  let R : Cell VB VI := ⟨Lv, 2 * d⟩
  ins (.bin p .div ⟨t, 0⟩ R two)
  ins (.un p .neg ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.litIdx p ⟨t, 2⟩ (L + d))
  ins (.bin p .div ⟨t, 3⟩ R ⟨t, 2⟩)
  ins (.bin p .mul ⟨t, 4⟩ ⟨t, 3⟩ ⟨Su, lo⟩)
  zhermShift p k Ma (eighBlockOff n d lo) ⟨t, 4⟩ W 0
  ins (.copy p ⟨sp, 0⟩ ⟨par, 2⟩)
  ins (.bin p .mul ⟨sp, 1⟩ two R)
  eighSignBlock p mm k F W 0 sp 0 B 0
  zhermShift p k B 0 negone T 0
  zhermScale p k T 0 two Pp 0
  zhermShift p k B 0 one T 0
  zneg p k k T 0 T 0
  zhermScale p k T 0 two Pm 0
  ztraceRe p k Pp 0 ⟨t, 5⟩
  ins (.bin p .add ⟨t, 6⟩ ⟨t, 5⟩ half)
  eighClampBlock p k ⟨t, 6⟩ ⟨t, 2⟩ ⟨t, 3⟩
  Builder.bindIdx p ⟨t, 6⟩ k fun kp => do
    eighWhen (1 - (k - .var kp))
      (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) ⟨t, 0⟩
        ⟨Sz, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 2)
    eighWhen (1 - .var kp)
      (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) ⟨t, 1⟩
        ⟨Sz, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 3)
    eighWhen (.var kp * (k - .var kp))
      (eighSplitBlock p mm qr n d lo k (.var kp) Sg Pp Pm Ma Qa Sz Kd Kp two ⟨t, 0⟩ ⟨t, 1⟩ sqh)

/-! ### The two passes -/

/-- **One level of the downward pass** at depth $d < D$: the next window
$\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(1/2) + \mathrm{fl}(2/\ell))R)$ and tolerance
$\mathrm{fl}(\mathrm{fl}(1 - \mathrm{fl}(1/\ell))\varepsilon)$ (`NLAlib.eighNextParams`,
$\ell = \ell_0 + d$) into the cells $2(d + 1)$ and $2(d + 1) + 1$ of `Lv`; the $n$ uniform and
$4n^2$ Gaussian draws of the level into `Su` and `Sg`; and for each slot $lo$, its stored size
$k$ (an index binder bounded by $n - lo$) and, for $k \ge 1$, a leaf (size at most $1$, or
$R \le \mathrm{fl}(\varepsilon R_0)$, one comparison) or the node step
(`NLAlib.eighNodeBlock`, with the stored $\sqrt{1/2}$ of the cell `sqh`). -/
def eighDownLevel (p : P) (mm qr : ι) (n L F d : IExp VI) (par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp : VB)
    (one two half negone sqh : Cell VB VI) : Builder P ι VB VI Unit := scope do
  -- t: 0 ℓ, 1 1/ℓ, 2 2/ℓ, 3 a sum or difference, 4 ε R₀
  let t ← alloc p 5
  ins (.litIdx p ⟨t, 0⟩ (L + d))
  ins (.bin p .div ⟨t, 2⟩ two ⟨t, 0⟩)
  ins (.bin p .add ⟨t, 3⟩ half ⟨t, 2⟩)
  ins (.bin p .mul ⟨Lv, 2 * (d + 1)⟩ ⟨t, 3⟩ ⟨Lv, 2 * d⟩)
  ins (.bin p .div ⟨t, 1⟩ one ⟨t, 0⟩)
  ins (.bin p .sub ⟨t, 3⟩ one ⟨t, 1⟩)
  ins (.bin p .mul ⟨Lv, 2 * (d + 1) + 1⟩ ⟨t, 3⟩ ⟨Lv, 2 * d + 1⟩)
  forRange n fun i => ins (.draw p .uniform ⟨Su, .var i⟩)
  forRange (4 * (n * n)) fun w => ins (.draw p .gaussian ⟨Sg, .var w⟩)
  forRange n fun lo => Builder.bindIdx p ⟨Sz, eighSlotOff n d (.var lo)⟩ (n - .var lo) fun k =>
    eighWhen (.var k) do
      eighWhen (1 - (.var k - 1))
        (eighLeafBlock p true (.var k) Ma (eighBlockOff n d (.var lo)) Ua
          (eighBlockOff n d (.var lo)) Ea (eighSlotOff n d (.var lo))
          ⟨Kd, eighSlotOff n d (.var lo)⟩)
      eighWhen (.var k - 1) do
        ins (.bin p .mul ⟨t, 4⟩ ⟨Lv, 2 * d + 1⟩ ⟨par, 0⟩)
        ifThenElse p .le ⟨Lv, 2 * d⟩ ⟨t, 4⟩
          (eighLeafBlock p false (.var k) Ma (eighBlockOff n d (.var lo)) Ua
            (eighBlockOff n d (.var lo)) Ea (eighSlotOff n d (.var lo))
            ⟨Kd, eighSlotOff n d (.var lo)⟩)
          (eighNodeBlock p mm qr n L F d (.var lo) (.var k) par Lv Su Sg Ma Qa Sz Kd Kp one two
            half negone sqh)

/-- **The nodes whose budget is spent**: at depth $D$, for each slot $lo$ with stored size
$k \ge 1$, the junk output of `NLAlib.eighAux` at budget $0$: the stored identity and zero
eigenvalues. -/
def eighBottomLevel (p : P) (n D : IExp VI) (Ua Ea Sz : VB) : Builder P ι VB VI Unit :=
  forRange n fun lo => Builder.bindIdx p ⟨Sz, eighSlotOff n D (.var lo)⟩ (n - .var lo) fun k =>
    eighWhen (.var k) do
      zidentity p (.var k) Ua (eighBlockOff n D (.var lo))
      forRange (.var k) fun i => ins (.lit p ⟨Ea, eighSlotOff n D (.var lo) + .var i⟩ 0)

/-- **One level of the upward pass** at depth $d < D$: for each slot $lo$ with stored size
$k \ge 1$, its stored kind (an index binder bounded by $4$); a leaf is done; a node with one child
copies the child's $\mathbf{U}$ (same slot, depth $d + 1$) and adds $\pm\sigma$,
$\sigma = \mathrm{fl}(R/\mathrm{fl}(2))$, to its eigenvalues; a split reads $k_+$ and writes
$[\mathrm{mm}(\mathbf{Q}_+, \mathbf{U}_+)\ \mathrm{mm}(\mathbf{Q}_-, \mathbf{U}_-)]$ (two kernel
calls into the two column blocks) and the eigenvalues $\mathrm{fl}(d_+ + \sigma)$,
$\mathrm{fl}(d_- - \sigma)$. -/
def eighUpLevel (p : P) (mm : ι) (n d : IExp VI) (Lv Ua Qa Ea Sz Kd Kp : VB) (two : Cell VB VI) :
    Builder P ι VB VI Unit := scope do
  -- t: 0 σ, 1 −σ
  let t ← alloc p 2
  ins (.bin p .div ⟨t, 0⟩ ⟨Lv, 2 * d⟩ two)
  ins (.un p .neg ⟨t, 1⟩ ⟨t, 0⟩)
  forRange n fun lo => Builder.bindIdx p ⟨Sz, eighSlotOff n d (.var lo)⟩ (n - .var lo) fun k =>
    eighWhen (.var k) <| Builder.bindIdx p ⟨Kd, eighSlotOff n d (.var lo)⟩ 4 fun c => do
      eighWhen (eighEqInd (.var c) 2) do
        zcopy p (.var k) (.var k) Ua (eighBlockOff n (d + 1) (.var lo)) Ua
          (eighBlockOff n d (.var lo))
        forRange (.var k) fun i => ins (.bin p .add ⟨Ea, eighSlotOff n d (.var lo) + .var i⟩
          ⟨Ea, eighSlotOff n (d + 1) (.var lo) + .var i⟩ ⟨t, 0⟩)
      eighWhen (eighEqInd (.var c) 3) do
        zcopy p (.var k) (.var k) Ua (eighBlockOff n (d + 1) (.var lo)) Ua
          (eighBlockOff n d (.var lo))
        forRange (.var k) fun i => ins (.bin p .add ⟨Ea, eighSlotOff n d (.var lo) + .var i⟩
          ⟨Ea, eighSlotOff n (d + 1) (.var lo) + .var i⟩ ⟨t, 1⟩)
      eighWhen (eighEqInd (.var c) 4) <|
        Builder.bindIdx p ⟨Kp, eighSlotOff n d (.var lo)⟩ (.var k) fun kp => do
          let qo := eighBlockOff n d (.var lo)
          stmt (.kcall mm p [.var k, .var kp, .var kp]
            [(Qa, qo), (Ua, eighBlockOff n (d + 1) (.var lo))] [(Ua, eighBlockOff n d (.var lo))])
          stmt (.kcall mm p [.var k, .var k - .var kp, .var k - .var kp]
            [(Qa, qo + 2 * (.var k * .var kp)), (Ua, eighBlockOff n (d + 1) (.var lo + .var kp))]
            [(Ua, eighBlockOff n d (.var lo) + 2 * (.var k * .var kp))])
          forRange (.var kp) fun j => ins (.bin p .add
            ⟨Ea, eighSlotOff n d (.var lo) + .var j⟩
            ⟨Ea, eighSlotOff n (d + 1) (.var lo) + .var j⟩ ⟨t, 0⟩)
          forRange (.var k - .var kp) fun j => ins (.bin p .sub
            ⟨Ea, eighSlotOff n d (.var lo) + .var kp + .var j⟩
            ⟨Ea, eighSlotOff n (d + 1) (.var lo) + .var kp + .var j⟩ ⟨t, 0⟩)

/-! ### The program -/

/-- **Randomized spectral bisection as a program** ([Shah2024, Algorithm 3], as `NLAlib.eigh` with
depth counter $\ell_0$ and sign step limit $F$): from the stored Hermitian $n \times n$ matrix
$\mathbf{A}$ (interleaved pairs in `A`) and the stored $R_0$, $\varepsilon$, $\beta$ (cells $0$,
$1$, $2$ of `par`) it writes the stored $\mathbf{U}$ ($2n^2$ words of `U`) and eigenvalues ($n$
cells of `dv`). Level arenas for the $D + 1$ depths, $D = \ell_0 + 1$: the node matrices, outputs
and bases (complex $n \times n$ blocks), the eigenvalues, sizes, kinds and $k_+$ ($n$ cells each)
and the windows and tolerances; the constants $1$, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2) =
\mathrm{fl}(1/\mathrm{fl}(2))$, $-1$ and the stored $\sqrt{1/2} =
\mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$ (`NLAlib.Computation.ScalarSem.sqrtHalf`, computed once and
read by every split); every size cell the literal $0$ but the root's ($n$ at slot
$0$); $\mathbf{A}$, $R_0$, $\varepsilon$ at depth $0$. Then the downward pass
(`NLAlib.eighDownLevel` at $d = 0, \ldots, D - 1$), the junk output $(\mathbf{I}, \mathbf{0})$ of
every node at depth $D$ (`NLAlib.eighBottomLevel`), the upward pass (`NLAlib.eighUpLevel` at
$d = D - 1, \ldots, 0$), and the root's output copied out. Every buffer is freed at the end
(`scope`).
Algorithm: spectral-bisection -/
def eighProg (p : P) (mm qr : ι) (n L F : IExp VI) (A par U dv : VB) :
    Builder P ι VB VI Unit := scope do
  let D : IExp VI := L + 1
  -- c: 0 one, 1 fl(2), 2 fl(1/2), 3 −1, 4 fl(√fl(1/2))
  let c ← alloc p 5
  let Ma ← alloc p (2 * (n * n) * (D + 1))
  let Ua ← alloc p (2 * (n * n) * (D + 1))
  let Qa ← alloc p (2 * (n * n) * D)
  let Ea ← alloc p (n * (D + 1))
  let Sz ← alloc p (n * (D + 1) + 1)
  let Kd ← alloc p (n * D)
  let Kp ← alloc p (n * D)
  let Lv ← alloc p (2 * (D + 1))
  let Su ← alloc p n
  let Sg ← alloc p (4 * (n * n))
  ins (.lit p ⟨c, 0⟩ 1)
  ins (.litIdx p ⟨c, 1⟩ 2)
  ins (.bin p .div ⟨c, 2⟩ ⟨c, 0⟩ ⟨c, 1⟩)
  ins (.un p .neg ⟨c, 3⟩ ⟨c, 0⟩)
  ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)
  forRange (n * (D + 1) + 1) fun w => ins (.litIdx p ⟨Sz, .var w⟩ 0)
  ins (.litIdx p ⟨Sz, 0⟩ n)
  zcopy p n n A 0 Ma 0
  ins (.copy p ⟨Lv, 0⟩ ⟨par, 0⟩)
  ins (.copy p ⟨Lv, 1⟩ ⟨par, 1⟩)
  forRange D fun d =>
    eighDownLevel p mm qr n L F (.var d) par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩
      ⟨c, 3⟩ ⟨c, 4⟩
  eighBottomLevel p n D Ua Ea Sz
  forRange D fun d' => eighUpLevel p mm n (L - .var d') Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩
  zcopy p n n Ua 0 U 0
  forRange n fun i => ins (.copy p ⟨dv, .var i⟩ ⟨Ea, .var i⟩)

-- Compilation is checked by evaluation, which on this tree needs a deeper recursion than the
-- default.
set_option maxRecDepth 100000 in
/-- **The registered tree of randomized spectral bisection**: `NLAlib.eighProg` with the stored
matrix in declared buffer $0$, the stored $R_0$, $\varepsilon$, $\beta$ in cells $0$ to $2$ of
declared buffer $1$, and the outputs $\mathbf{U}$ and $\mathbf{d}$ in declared buffers $2$ and
$3$, compiled once at symbolic sizes ($n = N$, the depth counter $\ell_0$ and the sign step limit
$F$) into one first-order program for all sizes; compilation succeeds by evaluation. -/
def eighProg.compiled (p : P) (mm qr : ι) : Prog P ι 2 4 :=
  (ProgFamily.compile fun _ _ N n h =>
    (eighProg p mm qr N (n 0) (n 1) (h 0) (h 1) (h 2) (h 3)).run).get rfl

/-! ### Counts -/

/-- The scalar operation kinds of `NLAlib.eighProg` at the tag `p`: the four arithmetic
operations, negation, square root, literals, copies, comparisons, the two kinds of draws and the
conversions to indices. -/
def eighScalarKinds {ι : Type} (p : P) : List (OpKind P ι) :=
  [.bin p .add, .bin p .sub, .bin p .mul, .bin p .div, .un p .neg, .un p .sqrt, .lit p, .copy p,
    .cmp p, .draw p .uniform, .draw p .gaussian, .toNat p]

/-- **An upper bound on the counts** of `NLAlib.eighProg` at size $n$, depth counter $\ell_0$ and
step limit $F$: at most $1024(F + 2)(\ell_0 + 2)(n + 1)^3$ operations of each scalar kind
(`NLAlib.eighScalarKinds`), and, for each of the $2(\ell_0 + 1)n$ slot visits of the two passes, the
kernel calls of a node of every size $k \le n$ with every split $k_+ \le k$: $2F + 8$ products at
$[k, k, k]$ (the sign set-up, steps and tests, and the two deflations), two factorizations at $[k,
k]$, the four products of the compressions and the two of the assembly. This is the static bound: an
index binder is bounded by the supremum over its range, so every size is charged at every slot
(design note `docs/design/Computation-EighProgram.md`, §5; the tight count is the weighted bound
there). -/
noncomputable def eighCount {ι : Type} (p : P) (mm qr : ι) (n L F : ℕ) : OpCount P ι :=
  ((eighScalarKinds (ι := ι) p).map fun κ =>
      Finsupp.single κ (1024 * (F + 2) * (L + 2) * (n + 1) ^ 3)).sum +
    (2 * (L + 1) * n) • ∑ k ∈ Finset.range (n + 1), ∑ kp ∈ Finset.range (k + 1),
      ((2 * F + 8) • Finsupp.single (.kcall p mm [k, k, k]) 1 +
        Finsupp.single (.kcall p qr [k, k]) 2 +
        Finsupp.single (.kcall p mm [kp, k, k]) 1 + Finsupp.single (.kcall p mm [kp, k, kp]) 1 +
        Finsupp.single (.kcall p mm [k - kp, k, k]) 1 +
        Finsupp.single (.kcall p mm [k - kp, k, k - kp]) 1 +
        Finsupp.single (.kcall p mm [k, kp, kp]) 1 +
        Finsupp.single (.kcall p mm [k, k - kp, k - kp]) 1)

end NLAlib
