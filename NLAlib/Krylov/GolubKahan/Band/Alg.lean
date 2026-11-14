/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.BasisExtensionContract
public import NLAlib.Ops.Blas.Sampling
public import NLAlib.Ops.Catalog.OperatorPair
public import NLAlib.Ops.Cert

/-!
# Block Golub–Kahan bidiagonalization with full reorthogonalization as one fixed program

The driver is written against three groups of operations and does no arithmetic of its own:
the extension of a stored basis by a block (`NLAlib.Ops.OrthOp.extend`), the products with a
matrix $\mathbf{A}$ and with $\mathbf{A}^{\mathsf{H}}$ (`NLAlib.Ops.OperatorPairOp`), and scalar
draws from a tape stream. With $N = qb$:

```
draw Ω (n × b);  V block 0, G := extend(∅, Ω)
for j < q:  U block j,   block column j of R := extend(U blocks < j, A · (V block j))
            V block j+1, block column j of S := extend(V blocks ≤ j, Aᴴ · (U block j))
```

Full reorthogonalization is the fact that every extension is against all stored columns of its
side. A concrete orthogonalization scheme is an implementation of `extend` proved against the
contract (`NLAlib.Ops.extendRel`, `NLAlib.Ops.exactExtendRel`) and substituted by linking. The
stored-run predicates of this file are related to the pure relations
`NLAlib.IsBlockGolubKahan` and `NLAlib.IsBlockGolubKahanErr` in
`NLAlib/Krylov/GolubKahan/Band/Run.lean`. Design: `docs/design/LowRank-BlockLanczos.md` §3.

**Storage.** All blocks are column-major, one word per entry. `U` has `q * b * m` words and `V`
has `(q + 1) * b * n`; a new block is written by `extend` directly after the stored columns of
its side. `G` holds the `b * b` coefficients of the start block. `R` and `S` are packed by block
column: block column `j` of `R` is the `(j * b + b) × b` coefficient block of the extension of
the `j * b` stored columns of `U`, at the offset `b * b * (j * (j + 1) / 2)`, and block column
`j` of `S` is the `((j + 1) * b + b) × b` block of the extension of the `(j + 1) * b` stored
columns of `V`, at the offset `b * b * (j * (j + 3) / 2)`. The scratch block of
`max m n * b` words holds the drawn block and then the products; it is released at the end.

## Main definitions

* `NLAlib.Krylov.GolubKahan.Band.applyColumns`, `NLAlib.Krylov.GolubKahan.Band.step`,
  `NLAlib.Krylov.GolubKahan.Band.solve`, `NLAlib.Krylov.GolubKahan.Band.program`: the program.
* `NLAlib.Krylov.GolubKahan.Band.coefOffsetR`, `NLAlib.Krylov.GolubKahan.Band.coefOffsetS`,
  `NLAlib.Krylov.GolubKahan.Band.outLens`: the packed layout.
* `NLAlib.Krylov.GolubKahan.Band.IsStoredRun`, `NLAlib.Krylov.GolubKahan.Band.IsExactStoredRun`,
  `NLAlib.Krylov.GolubKahan.Band.IsRoundedStoredRun`, `NLAlib.Krylov.GolubKahan.Band.StoredOut`:
  the relation between the stored blocks of a run, block by block.
* `NLAlib.Krylov.GolubKahan.Band.solveRel`, `NLAlib.Krylov.GolubKahan.Band.Rounded.solveRel`:
  the contracts of the program.

## Main results

* `NLAlib.Krylov.GolubKahan.Band.extendPred_of_eq_zero`: an extension of the empty basis does not
  depend on the name of the empty column type.
* `NLAlib.Krylov.GolubKahan.Band.coefOffsetR_succ`,
  `NLAlib.Krylov.GolubKahan.Band.coefOffsetS_succ`: consecutive block columns are adjacent.
* `NLAlib.Krylov.GolubKahan.Band.writes_applyColumns`,
  `NLAlib.Krylov.GolubKahan.Band.writes_applyColumns_error`: a block of products.
* `NLAlib.Krylov.GolubKahan.Band.solve_writes`, `NLAlib.Krylov.GolubKahan.Band.solve_spec`:
  total execution under the exact contracts; the stored blocks are exact extensions.
* `NLAlib.Krylov.GolubKahan.Band.Rounded.solve_writes`,
  `NLAlib.Krylov.GolubKahan.Band.Rounded.solve_spec`: total execution under the rounded
  contracts, with the executed history.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.GolubKahan.Band

open Ops

variable {K Op Tst : Type}

/-! ### The program -/

/-- Apply the operation `o` (a product with a fixed `m × n` matrix) to each of the `b` columns
of the column-major block `X`, writing the `b` products as the column-major block `Y`. Input
and output are in different buffers. -/
def applyColumns (o : Op) : Impl Op Tst := opsImpl% [m, n, b] (X) → (Y) {
  for c < b {
    call o [m, n] (X[c * n]) → (Y[c * m])
  }
}

variable [Has OrthOp Op] [Has OperatorPairOp Op]

/-- Block step `j`: the products of $\mathbf{A}$ with block `j` of `V` are extended against the
`j * b` stored columns of `U`, giving block `j` of `U` and block column `j` of `R`; then the
products of $\mathbf{A}^{\mathsf{H}}$ with block `j` of `U` are extended against the
`(j + 1) * b` stored columns of `V`, giving block `j + 1` of `V` and block column `j` of `S`.
The scratch block `W` holds the products. -/
def step : Impl Op Tst := opsImpl% [m, n, b, j] (U, V, R, S, W) → () {
  run (applyColumns (Has.inj OperatorPairOp.matvec)).body [m, n, b] (V[j * b * n], W);
  call (Has.inj OrthOp.extend) [m, j * b, b] (U, W) →
    (U[j * b * m], W, R[b * b * (j * (j + 1) / 2)]);
  run (applyColumns (Has.inj OperatorPairOp.rmatvec)).body [n, m, b] (U[j * b * m], W);
  call (Has.inj OrthOp.extend) [n, (j + 1) * b, b] (V, W) →
    (V[(j + 1) * b * n], W, S[b * b * (j * (j + 3) / 2)])
}

variable [Has SampleOp Op]

/-- Block Golub–Kahan bidiagonalization with full reorthogonalization, at the dimensions
`[m, n, b, q]`: draw the `n × b` start block from the stream into the scratch block, extend the
empty basis by it (block `0` of `V` and the start coefficients `G`), and run `q` block steps.
The outputs are `U` (`q * b * m` words), `V` (`(q + 1) * b * n`), `G` (`b * b`) and the packed
coefficients `R` and `S`. The scratch block has `max m n * b` words. -/
def solve (stream : ℕ) : Impl Op Tst := opsImpl% [m, n, b, q] () → (U, V, G, R, S) {
  let W ← alloc ((m + (n - m)) * b);
  run (sampleVector stream).body [n * b] (W);
  call (Has.inj OrthOp.extend) [n, 0, b] (V, W) → (V, W, G);
  for j < q {
    run step.body [m, n, b, j] (U, V, R, S, W)
  }
}

/-- The fixed program: four dimensions `[m, n, b, q]` and the five output buffers `U`, `V`,
`G`, `R`, `S`. -/
def program (stream : ℕ) : Program Op Tst 4 5 :=
  (solve stream).program 5 []
    [⟨0, .const 0⟩, ⟨1, .const 0⟩, ⟨2, .const 0⟩, ⟨3, .const 0⟩, ⟨4, .const 0⟩]

/-! ### The packed layout -/

/-- The offset of block column $j$ of the packed coefficients of the left basis: block column
$i$ has $(ib + b)b$ words, so the offset is $b^2 j(j+1)/2$. -/
def coefOffsetR (b j : ℕ) : ℕ := b * b * (j * (j + 1) / 2)

/-- The offset of block column $j$ of the packed coefficients of the right basis: block column
$i$ has $((i+1)b + b)b$ words, so the offset is $b^2 j(j+3)/2$. -/
def coefOffsetS (b j : ℕ) : ℕ := b * b * (j * (j + 3) / 2)

/-- Block column $j + 1$ of the packed coefficients of the left basis starts where block column
$j$, of $(jb + b)b$ words, ends. -/
theorem coefOffsetR_succ (b j : ℕ) :
    coefOffsetR b (j + 1) = coefOffsetR b j + (j * b + b) * b := by
  have h : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by ring
  rw [coefOffsetR, coefOffsetR, h, Nat.add_mul_div_left _ _ (by norm_num)]
  ring

/-- Block column $j + 1$ of the packed coefficients of the right basis starts where block
column $j$, of $((j+1)b + b)b$ words, ends. -/
theorem coefOffsetS_succ (b j : ℕ) :
    coefOffsetS b (j + 1) = coefOffsetS b j + ((j + 1) * b + b) * b := by
  have h : (j + 1) * (j + 1 + 3) = j * (j + 3) + 2 * (j + 2) := by ring
  rw [coefOffsetS, coefOffsetS, h, Nat.add_mul_div_left _ _ (by norm_num)]
  ring

/-- The lengths of the five output blocks `U`, `V`, `G`, `R`, `S` at the dimensions
`[m, n, b, q]`. -/
def outLens (m n b q : ℕ) : List ℕ :=
  [q * b * m, (q + 1) * b * n, b * b, coefOffsetR b q, coefOffsetS b q]

/-! ### The relation between the stored blocks -/

/-- A predicate on the matrices of a run at the dimensions $(m, n, b, q)$: the start block
$\mathbf{\Omega}$, the bases $\mathbf{U}$ ($m \times qb$) and $\mathbf{V}$
($n \times (q+1)b$), the start coefficients $\mathbf{G}$ and the block columns of the
coefficients of the left and of the right basis. -/
abbrev RunPred (m n b q : ℕ) : Type :=
  Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin (q * b)) ℝ →
    Matrix (Fin n) (Fin ((q + 1) * b)) ℝ → Matrix (Fin b) (Fin b) ℝ →
    ((j : ℕ) → Matrix (Fin (j * b + b)) (Fin b) ℝ) →
    ((j : ℕ) → Matrix (Fin ((j + 1) * b + b)) (Fin b) ℝ) → Prop

/-- **The stored blocks of a run are related block by block**, for an extension predicate `Ext`
and relations `Mv`, `Rmv` between a block and the block of its computed products with
$\mathbf{A}$ and with $\mathbf{A}^{\mathsf{H}}$. Block $0$ of $\mathbf{V}$ and $\mathbf{G}$
extend the empty basis by $\mathbf{\Omega}$; the empty basis is the prefix of zero blocks of
$\mathbf{V}$, with column type `Fin (0 * b)`, as in `NLAlib.IsBlockGolubKahan`. For every
$j < q$: block $j$ of $\mathbf{U}$ and
block column $j$ of the left coefficients extend the first $j$ blocks of $\mathbf{U}$ by a
product block of block $j$ of $\mathbf{V}$; block $j + 1$ of $\mathbf{V}$ and block column $j$
of the right coefficients extend the first $j + 1$ blocks of $\mathbf{V}$ by a product block of
block $j$ of $\mathbf{U}$. The upper part of a coefficient block column is the coefficient block
against the old columns and its lower $b$ rows the block against the new ones. -/
structure IsStoredRun {m n b q : ℕ} (Ext : ExtendPred ℝ)
    (Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop)
    (Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop)
    (Ω : Matrix (Fin n) (Fin b) ℝ) (U : Matrix (Fin m) (Fin (q * b)) ℝ)
    (V : Matrix (Fin n) (Fin ((q + 1) * b)) ℝ) (G : Matrix (Fin b) (Fin b) ℝ)
    (R : (j : ℕ) → Matrix (Fin (j * b + b)) (Fin b) ℝ)
    (S : (j : ℕ) → Matrix (Fin ((j + 1) * b + b)) (Fin b) ℝ) : Prop where
  /-- The start block: block $0$ of $\mathbf{V}$ extends the empty basis, the prefix of zero
  blocks of $\mathbf{V}$, by $\mathbf{\Omega}$. -/
  start : Ext n (0 * b) b (blockPrefix b V 0) Ω (blockCols b V 0) 0 G
  /-- Block $j$ of $\mathbf{U}$ extends the first $j$ blocks of $\mathbf{U}$ by the products of
  $\mathbf{A}$ with block $j$ of $\mathbf{V}$. -/
  left : ∀ j < q, ∃ W, Mv (blockCols b V j) W ∧
    Ext m (j * b) b (blockPrefix b U j) W (blockCols b U j) (coefTop (R j)) (coefBot (R j))
  /-- Block $j + 1$ of $\mathbf{V}$ extends the first $j + 1$ blocks of $\mathbf{V}$ by the
  products of $\mathbf{A}^{\mathsf{H}}$ with block $j$ of $\mathbf{U}$. -/
  right : ∀ j < q, ∃ W, Rmv (blockCols b U j) W ∧
    Ext n ((j + 1) * b) b (blockPrefix b V (j + 1)) W (blockCols b V (j + 1))
      (coefTop (S j)) (coefBot (S j))

/-- An extension of the empty basis is an extension of every basis with no columns: a predicate
`Ext` on the matrices of a basis extension that holds at the basis with column type `Fin 0`, as
returned by a call at the dimensions `[n, 0, b]`, holds at every basis $\mathbf{Q}$ and
coefficient block $\mathbf{H}$ with column and row type `Fin k`, $k = 0$; in particular at
`Fin (0 * b)`, the form of the start block in
`NLAlib.Krylov.GolubKahan.Band.IsStoredRun`. -/
theorem extendPred_of_eq_zero (Ext : ExtendPred ℝ) {n k b : ℕ} (hk : k = 0)
    (Q : Matrix (Fin n) (Fin k) ℝ) (H : Matrix (Fin k) (Fin b) ℝ)
    {W Q' : Matrix (Fin n) (Fin b) ℝ} {R : Matrix (Fin b) (Fin b) ℝ}
    (h : Ext n 0 b 0 W Q' 0 R) : Ext n k b Q W Q' H R := by
  subst hk
  have hQ : Q = 0 := by
    ext i j
    exact j.elim0
  have hH : H = 0 := by
    ext i j
    exact i.elim0
  rw [hQ, hH]
  exact h

/-- The stored blocks of an exact run: every extension is exact (`NLAlib.IsBasisExtension`) and
the extended blocks are the products $\mathbf{A}\mathbf{V}_j$ and
$\mathbf{A}^{\mathsf{H}}\mathbf{U}_j$ of the stored blocks. -/
def IsExactStoredRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b q : ℕ) : RunPred m n b q :=
  IsStoredRun (fun _ _ _ Q W Q' H R => IsBasisExtension Q W Q' H R)
    (fun X W => W = A * X) (fun X W => W = Aᴴ * X)

/-- The stored blocks of a rounded run, the executed history: every extension is a rounded
extension with parameters $(\eta_0, \mu, \varepsilon)$ (`NLAlib.IsBasisExtensionErr`) of a
computed product block $\mathbf{W}$, whose column $c$ satisfies
$\|\mathbf{A}\mathbf{x}_c - \mathbf{w}_c\| \le \delta\|\mathbf{x}_c\|$ for the products with
$\mathbf{A}$ and $\|\mathbf{A}^{\mathsf{H}}\mathbf{x}_c - \mathbf{w}_c\| \le
\delta'\|\mathbf{x}_c\|$ for the products with $\mathbf{A}^{\mathsf{H}}$, $\mathbf{x}_c$ the
column of the stored block and the norm the Euclidean norm. -/
def IsRoundedStoredRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (δ δ' η₀ μ ε : ℝ) (b q : ℕ) :
    RunPred m n b q :=
  IsStoredRun (fun _ _ _ Q W Q' H R => IsBasisExtensionErr η₀ μ ε Q W Q' H R)
    (fun X W => ∀ c, ‖WithLp.toLp 2 (A *ᵥ X.col c - W.col c)‖ ≤ δ * ‖WithLp.toLp 2 (X.col c)‖)
    (fun X W => ∀ c, ‖WithLp.toLp 2 (Aᴴ *ᵥ X.col c - W.col c)‖ ≤ δ' * ‖WithLp.toLp 2 (X.col c)‖)

variable [Inhabited K]

/-- The run predicate `Run` holds of the decoded words: the window `ω` of the tape (the start
block), the words `us`, `vs`, `gs` of the bases and of the start coefficients, and the packed
coefficient words `rs`, `ss`, whose block column `j` starts at the offset
`NLAlib.Krylov.GolubKahan.Band.coefOffsetR` resp.
`NLAlib.Krylov.GolubKahan.Band.coefOffsetS`. -/
def StoredOut (dec : K → ℝ) (m n b q : ℕ) (Run : RunPred m n b q)
    (ω us vs gs rs ss : List K) : Prop :=
  Run (decodeMatrix dec n b ω) (decodeMatrix dec m (q * b) us)
    (decodeMatrix dec n ((q + 1) * b) vs) (decodeMatrix dec b b gs)
    (fun j => decodeMatrix dec (j * b + b) b (rs.drop (coefOffsetR b j)))
    (fun j => decodeMatrix dec ((j + 1) * b + b) b (ss.drop (coefOffsetS b j)))

/-- The dimensions are `[m, n, b, q]` with the row and column numbers of the matrix, there is no
input operand, and the five outputs are in distinct buffers. -/
@[admNF] def SolveOperands (m n : ℕ) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d.headD 0 = m ∧ d.getD 1 0 = n ∧ ins = [] ∧ ∃ U V G R S,
    outs = [U, V, G, R, S] ∧ [U.1, V.1, G.1, R.1, S.1].Nodup

/-- The contract of the program for a run predicate: at the dimensions `[m, n, b, q]` the call
reads the window of `n * b` words of the stream and writes the five output blocks, whose decoded
matrices satisfy the run predicate with the decoded window as start block. -/
@[simps (attr := storeNF)]
def solveRelOf (stream : ℕ) (dec : K → ℝ) (m n : ℕ) (Run : (b q : ℕ) → RunPred m n b q) :
    BlockRel K where
  nd := 4
  stream := stream
  win d := d.getD 1 0 * d.getD 2 0
  inLens _ := []
  outLens d := outLens (d.headD 0) (d.getD 1 0) (d.getD 2 0) (d.getD 3 0)
  rel d _ ω Y := match Y with
    | [us, vs, gs, rs, ss] =>
        StoredOut dec m n (d.getD 2 0) (d.getD 3 0) (Run _ _) ω us vs gs rs ss
    | _ => False

/-- The exact contract of the program: the stored blocks are an exact run for $\mathbf{A}$ from
the drawn start block. -/
def solveRel (stream : ℕ) (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BlockRel K :=
  solveRelOf stream dec m n (IsExactStoredRun A)

/-! ### Products of a block -/

/-- A block of exact products: if the operation `o` meets the exact contract of the product with
$\mathbf{A}$, the loop over the `b` columns of the readable block `xs` writes a block that
decodes to $\mathbf{A}\mathbf{X}$, $\mathbf{X}$ the decoded input block. The output is in
another buffer; the position of the tape does not move. Zero dimensions are included. -/
theorem writes_applyColumns {dec : K → ℝ} {m n b : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} {o : Op}
    (hA : I.Meets .total o ((matvecRel dec A).spec (MatvecOperands m n)))
    {τ : Tape K} {μ : Mem K} {x y : ℕ × ℕ} {xs : List K} (hxy : x.1 ≠ y.1)
    (hl : μ.Live [x, y]) (hx : μ.store.readBlock x.1 x.2 (b * n) = some xs)
    (hy : y.2 + b * m ≤ μ.store.len y.1) :
    Writes .total I τ (applyColumns o).body (Env.frame [m, n, b] [x, y])
      (Store.inBlock y.1 y.2 (b * m))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock y.1 y.2 (b * m) = some ys ∧
        decodeMatrix dec m b ys = A * decodeMatrix dec n b xs) μ := by
  -- Outline: `writes_loop_disjoint_prefix` with the regions `Store.inBlock y.1 (y.2 + c * m) m`
  -- (pairwise disjoint, inside the output block) and the result "column `c` of the output is
  -- the product of column `c` of the input"; each round is `writes_call1` with `hA`, the
  -- admission `MatvecOperands` from `hxy`, and the column read from `hx` by
  -- `Store.readBlock` of a sub-block. Then `decodeMatrix_apply` column by column.
  sorry

/-- A block of rounded products: if the operation `o` meets the normwise contract of the product
with $\mathbf{A}$ at the allowance $\delta$, the loop over the `b` columns of the readable block
`xs` writes a block whose decoded column $c$ satisfies
$\|\mathbf{A}\mathbf{x}_c - \mathbf{w}_c\| \le \delta\|\mathbf{x}_c\|$ in the Euclidean norm,
$\mathbf{x}_c$ the decoded column of the input. The output is in another buffer; the position
of the tape does not move. -/
theorem writes_applyColumns_error {dec : K → ℝ} {m n b : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {δ : ℝ} {I : Interp Op Tst K} {o : Op}
    (hA : I.Meets .total o ((matvecErrorRel dec A δ).spec (MatvecOperands m n)))
    {τ : Tape K} {μ : Mem K} {x y : ℕ × ℕ} {xs : List K} (hxy : x.1 ≠ y.1)
    (hl : μ.Live [x, y]) (hx : μ.store.readBlock x.1 x.2 (b * n) = some xs)
    (hy : y.2 + b * m ≤ μ.store.len y.1) :
    Writes .total I τ (applyColumns o).body (Env.frame [m, n, b] [x, y])
      (Store.inBlock y.1 y.2 (b * m))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock y.1 y.2 (b * m) = some ys ∧
        ∀ c, ‖WithLp.toLp 2 (A *ᵥ (decodeMatrix dec n b xs).col c -
          (decodeMatrix dec m b ys).col c)‖ ≤
            δ * ‖WithLp.toLp 2 ((decodeMatrix dec n b xs).col c)‖) μ := by
  -- Outline: as `writes_applyColumns`, with `matvecErrorRel` in place of `matvecRel`.
  sorry

/-! ### Exact execution -/

/-- Total execution under the exact contracts. If `matvec` and `rmatvec` are the exact
products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$, `extend` meets the exact contract of a
basis extension and the draws return the words of the tape, then for all dimensions
$(m, n, b, q)$, on five live output blocks in distinct buffers with room for the output lengths,
the program terminates, writes only the output blocks, consumes exactly $nb$ samples and
releases its scratch; the stored blocks decode to matrices that are an exact run for
$\mathbf{A}$ from the start block $\mathbf{\Omega}$ decoded from the window of the tape: every
stored block is an exact extension of the stored columns before it by the products of the
previous block. No rank or nonbreakdown hypothesis is needed. -/
theorem solve_writes {dec : K → ℝ} {m n b q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} (hA : IsExactMatvecPair dec A I)
    (hO : I.Meets .total (Has.inj OrthOp.extend) ((exactExtendRel dec).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) {τ : Tape K} {μ : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : μ.Live [U, V, G, R, S])
    (hz : μ.Room [U, V, G, R, S] (outLens m n b q)) :
    Writes .total I τ (solve stream).body (Env.frame [m, n, b, q] [U, V, G, R, S])
      (Fp.blocks [U, V, G, R, S] (outLens m n b q))
      (fun μ' => μ'.pos = μ.pos + n * b ∧ ∃ us vs gs rs ss,
        μ'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m n b q (IsExactStoredRun A b q) (τ.window stream μ.pos (n * b))
          us vs gs rs ss) μ := by
  -- Outline (storage bookkeeping only; the driver does no arithmetic).
  -- 1. `writes_alloc` for the scratch `W` of `(m + (n - m)) * b ≥ max (n * b) (m * b)` words;
  --    the postcondition reads only the five output blocks, so cleanup preserves it.
  -- 2. `writes_sampleVector hSample` in the frame: `W` holds `τ.window stream μ.pos (n * b)`.
  -- 3. `writes_call` with `hO` at `[n, 0, b]`: the admission `ExtendOperands` holds with
  --    `Q = V`, `Q' = (V.1, V.2 + 0 * n)`, `C = G` (distinct buffers from `hbuf` and from the
  --    freshness of `W`); the basis block of length `0 * n` reads as `[]`. This gives `start`
  --    after identifying the `(0 + b) × b` decoded block with the `b × b` matrix `G` and moving
  --    from the column type `Fin 0` to `Fin (0 * b)` by `extendPred_of_eq_zero`.
  -- 4. `writes_loop` over `j < q` with the invariant: the position is `μ.pos + n * b`; the
  --    first `j * b * m` words of `U`, `(j + 1) * b * n` words of `V`, `coefOffsetR b j` words
  --    of `R` and `coefOffsetS b j` words of `S` are readable and satisfy `left` and `right`
  --    for all `i < j` and `start`; footprint: these prefixes and the scratch. A round is
  --    `writes_frame` of `step`: `writes_applyColumns hA.matvec`, `writes_call` with `hO` at
  --    `[m, j * b, b]` (adjacent output `U[j * b * m]`), `writes_applyColumns hA.rmatvec` at
  --    `[n, m, b]`, `writes_call` with `hO` at `[n, (j + 1) * b, b]`. Earlier blocks are kept
  --    because each call writes only its three output blocks (`BlockRel.Post`), and
  --    `coefOffsetR_succ`, `coefOffsetS_succ` advance the packed prefixes.
  -- 5. Readback: the prefix of `j * b` columns of the decoded `U` is `blockPrefix b U j` and
  --    its block `j` is `blockCols b U j` (entrywise, `decodeMatrix_apply`), likewise for `V`
  --    and for the dropped coefficient words.
  sorry

/-- The program meets its exact contract in total mode: under the exact contracts of the
two products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$, of the basis extension and of the
draws, on five output blocks in distinct buffers the program writes blocks that decode to an
exact run for $\mathbf{A}$ from the drawn start block, and advances the tape by the $nb$ words
of that block. -/
theorem solve_spec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} (hA : IsExactMatvecPair dec A I)
    (hO : I.Meets .total (Has.inj OrthOp.extend) ((exactExtendRel dec).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) :
    (solve (Op := Op) (Tst := Tst) stream).Triple I .total
      ((solveRel stream dec A).spec (SolveOperands m n)) := by
  -- Outline: `cert_intro [m', n', b, q] () → (U, V, G, R, S)`, substitute the two dimensions
  -- from the admission, and conclude from `solve_writes` by `Writes.mono`, as
  -- `NLAlib.Krylov.Lanczos.Reorth.solve_spec` does.
  sorry

/-! ### Rounded execution -/

namespace Rounded

/-- The rounded contract of the program: the stored blocks are a rounded run for $\mathbf{A}$
with product allowances $\delta$, $\delta'$ and extension parameters
$(\eta_0, \mu, \varepsilon)$, from the drawn start block. -/
def solveRel (stream : ℕ) (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (δ δ' η₀ μ ε : ℝ) : BlockRel K :=
  solveRelOf stream dec m n (IsRoundedStoredRun A δ δ' η₀ μ ε)

/-- Total execution under the rounded contracts, with the executed history. If `matvec` and
`rmatvec` meet the normwise contracts of the products with $\mathbf{A}$ and
$\mathbf{A}^{\mathsf{H}}$ at the allowances $\delta$, $\delta'$, `extend` meets the rounded
contract of a basis extension with parameters $(\eta_0, \mu, \varepsilon)$ at the dimensions of
the run, and the draws return the words of the tape, then on five live output blocks in distinct
buffers with room for the output lengths the program terminates, writes only the output blocks,
consumes exactly $nb$ samples and releases its scratch; the stored blocks decode to a rounded
run: every stored block is a rounded extension of the stored columns before it by a computed
product block within the product allowance. There is no orthogonality, rank or nonbreakdown
hypothesis. -/
theorem solve_writes {dec : K → ℝ} {m n b q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {δ δ' η₀ μ ε : ℝ} {ok : ℕ → ℕ → ℕ → Prop} {I : Interp Op Tst K}
    (hA : IsMatvecPair dec A δ δ' I)
    (hO : I.Meets .total (Has.inj OrthOp.extend)
      ((extendRel dec η₀ μ ε ok).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) (hok₀ : ok n 0 b)
    (hokU : ∀ j < q, ok m (j * b) b) (hokV : ∀ j < q, ok n ((j + 1) * b) b)
    {τ : Tape K} {ν : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : ν.Live [U, V, G, R, S])
    (hz : ν.Room [U, V, G, R, S] (outLens m n b q)) :
    Writes .total I τ (solve stream).body (Env.frame [m, n, b, q] [U, V, G, R, S])
      (Fp.blocks [U, V, G, R, S] (outLens m n b q))
      (fun ν' => ν'.pos = ν.pos + n * b ∧ ∃ us vs gs rs ss,
        ν'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m n b q (IsRoundedStoredRun A δ δ' η₀ μ ε b q)
          (τ.window stream ν.pos (n * b)) us vs gs rs ss) ν := by
  -- Outline: the proof of the exact `solve_writes` with `writes_applyColumns_error` for the
  -- products and `extendRel` for the extensions; the domain of each `extend` call is `hok₀`,
  -- `hokU j` or `hokV j`. The product block `W` of the history is the decoded scratch block
  -- read by the `extend` call.
  sorry

/-- The program meets its rounded contract in total mode, at the dimensions `[m, n, b, q]`
at which the basis extension is admitted for every block of the run. -/
theorem solve_spec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {δ δ' η₀ μ ε : ℝ} {ok : ℕ → ℕ → ℕ → Prop} {I : Interp Op Tst K}
    (hA : IsMatvecPair dec A δ δ' I)
    (hO : I.Meets .total (Has.inj OrthOp.extend)
      ((extendRel dec η₀ μ ε ok).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) (hok : ∀ k b, ok m k b ∧ ok n k b) :
    (solve (Op := Op) (Tst := Tst) stream).Triple I .total
      ((solveRel stream dec A δ δ' η₀ μ ε).spec (SolveOperands m n)) := by
  -- Outline: as the exact `solve_spec`, from `Rounded.solve_writes`.
  sorry

end Rounded

end NLAlib.Krylov.GolubKahan.Band
